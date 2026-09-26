/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Coloring

/-!
# Kempe closure of ring traces  (port of `kempe.v`)

The proof of the Kempe closure property of the set of trace colorings of the border ring of a
planar plain quasicubic hypermap.  This is the main link between the reflected combinatorial
reducibility proofs and the mathematical theory of planar graphs developed in the rest of the
proof.  The result is also reused to validate the reduction to internally 5-connected
triangulations.

We start by defining three small functions on chromograms that modify chromograms by flipping
brackets in various ways:

* `gramNeg w`  : negate (invert) the parity bit of the first `Gpop` of `w` not matching an
  earlier `Gpush` (Coq `gram_neg`).
* `gramFlip w` : change the first unmatched `Gpop` of `w` into a `Gpush`, setting the parity bit
  of the next unmatched `Gpop` so that the overall parity of the resulting chromogram is
  inverted (Coq `gram_flip`).  This operation turns a chromogram with exactly two unbalanced
  `Gpop`s into a balanced one.
* `gramRot w`  : if `w` is balanced (all `Gpush` and `Gpop` are matched), the chromogram that
  matches the left rotation of the edge colorings matched by `w`: `gramRot w` matches
  `rot 1 et` exactly when `w` matches `et` (Coq `gram_rot`, `match_gram_rot`).

These functions are used to match changes in the perimeter as edges are removed in the main
theorem `kempe_map` (Coq `Kempe_map`), which proceeds by induction on the size of the map, much
as the proof of the Euler formula planarity property; indeed, the proof uses the `euler_tree`
lemma from that proof to select edges.

## The proof of `kempe_map`

As in Coq, the theorem is proved by induction in a single piece rather than through the face to
edge coloring equivalence, 23-path ring dart outerplanar pairings and bracket encoding chain of
equivalences sketched in paper proofs.  We prove Kempe closure by induction on the size of a
planar remainder map, using a double Walkup-N transform to contract one of the edges incident
to the perimeter N-cycle `r` (`r` need not be simple).  We assume `k` is a coloring of `G`, and
need to find a chromogram matching `k` on `r`, whose matching colorings all extend to colorings
of `G`.  This is trivial if `r = []`; otherwise `r` is an E-cycle in `permN G`, so `euler_tree`
gives us a dart `z` in `r` whose edge either
 (a) loops back to the perimeter, enclosing a single face: `face z = z`, or
 (b) is incident to an inner (hence cubic) node: `face z` is not in `r`.
Using `gramRot`, we can assume without loss that `z` is the second dart of `r`, more precisely,
that `rot 1 r = z :: p`.  As `k` is a coloring, `k z ≠ k (node z)`, so `p ≠ []`, say
`p = nz :: p1`.  Contracting `[z; edge z]` yields a remainder map `H` with a projection `h` onto
`G \ [z; edge z]`, and a perimeter N-cycle `s` which `h` maps to either `p1` in case (a), or
`node (edge z) :: face z :: p` in case (b).  Provided its trace on `rotr 1 s` starts with
distinct colors in case (b), a coloring `k1` of `H` lifts to a coloring `k0` of `G`; in case (a)
we can also set the head of the trace of `k0` on `r`.  Applying induction to the coloring
`k ∘ h` of `H` yields a chromogram `w`.  In case (a) the required chromogram is
`Gskip :: Gskip :: w` if the trace of `k` on `r` starts with `Color1`, otherwise it is
`Gpush :: Gpop0 :: w`.  In case (b) we first show `w = s1 :: s2 :: w1` where either
`{s1, s2} = {Gskip, Gpush}`, `s1 = s2 = Gpush`, or `w = Gpush :: Gpop1 :: w1`.  The required
chromogram is then `Gpush :: gramNeg w1`, `Gskip :: gramFlip w1`, or `Gskip :: w1` in each of
these three cases, respectively.

## Porting notes

* `gramNegRec`, `gramFlipRec` and `gramRot` are computable and structurally recursive, with the
  same case structure as the Coq fixpoints; math-comp `rcons w s` is `w ++ [s]`, and the
  boolean `[exists b, gram_balanced 0 b w]` of `gram_rot` is computed as
  `gramBalanced 0 true w || gramBalanced 0 false w`.
* `kempe_map` only assumes `[Fintype D]`: the decidable equality of darts used by the Walkup
  construction is obtained classically inside the proof.
* The single Coq proof of `Kempe_map` is split into private lemmas.  After Coq's
  `clearbody h H`, the proof only uses the properties `Ih`, `z'h`, `ez'h`, `invh`, `hE`, `hN` of
  the contraction `h : H → G`; these are the fields of the private structure `KContract`, and
  the induction step (`KContract.kempe_step`) is proved for any `H`, `h` with these properties,
  then instantiated with the double Walkup transform `kH` (Coq `H`) and its projection `kh`
  (Coq `h`).
* The Coq induction is on a bound of `#|G|`, for all hypermaps; here it quantifies over all
  dart types in the universe of `D` (the darts `{u : {x // x ≠ z} // u ≠ ez'}` of the contracted
  map live in the same universe).
* Coq's second "without loss" (rotating `r` so that `rot 1 r = z :: p`) iterates `gram_rot`
  along `rot 1`; here it is replaced by the equivalent statement that the Kempe property of a
  coloring is invariant under all rotations of the ring (`kempeProp_rot1`, `kempeProp_rot`,
  `kempeProp_of_rot`).
* The Coq header comment of the proof lists the third subcase of case (b) as
  `w = Gpush :: Gpop0 :: w1`; as the Coq proof (`Ds12`) shows, it is `Gpush :: Gpop1 :: w1`.
-/

namespace FourColor

open Function

universe u

/-! ### Chromogram operations -/

/-- Coq `gram_neg_rec n w`: negate the parity bit of the first `Gpop` of `w` that is matched
neither by an earlier `Gpush` of `w` nor by one of the `n` chords opened before `w`. -/
def gramNegRec (n : ℕ) (w : Chromogram) : Chromogram :=
  match w, n with
  | Gpush :: w', _ => Gpush :: gramNegRec (n + 1) w'
  | Gskip :: w', _ => Gskip :: gramNegRec n w'
  | s :: w', n' + 1 => s :: gramNegRec n' w'
  | Gpop0 :: w', 0 => Gpop1 :: w'
  | Gpop1 :: w', 0 => Gpop0 :: w'
  | [], _ => w

/-- Coq `gram_neg w`: negate (invert) the parity bit of the first `Gpop` of `w` not matching
an earlier `Gpush`. -/
def gramNeg : Chromogram → Chromogram := gramNegRec 0

/-- `matchg` with a nonempty context never matches the empty chromogram. -/
private theorem matchg_nil_of_ne_nil {lb : List Bool} (h : lb ≠ []) (et : Colseq) :
    matchg lb et [] = false := by
  cases et <;> cases lb <;> first | rfl | exact absurd rfl h

/-- The generalized statement proved by induction in Coq `match_gram_neg`: in the context
`lb ++ [b0]`, negating the `Gpop` that closes the bottom chord amounts to negating `b0`. -/
private theorem match_gramNegRec (b0 : Bool) (w : Chromogram) :
    ∀ (et : Colseq) (lb : List Bool),
      matchg (lb ++ [b0]) et (gramNegRec lb.length w) = matchg (lb ++ [!b0]) et w := by
  induction w with
  | nil =>
    intro et lb
    rw [show gramNegRec lb.length [] = [] by cases lb <;> rfl,
      matchg_nil_of_ne_nil (by simp), matchg_nil_of_ne_nil (by simp)]
  | cons s w ih =>
    intro et lb
    cases et with
    | nil => cases s <;> cases lb <;> rfl
    | cons e et =>
      cases s with
      | Gpush =>
        cases e
        all_goals first
          | rfl
          | exact ih et (false :: lb)
          | exact ih et (true :: lb)
      | Gskip =>
        cases e
        all_goals first
          | rfl
          | exact ih et lb
      | Gpop0 =>
        rcases lb with _ | ⟨_ | _, lb⟩ <;> cases e <;> cases b0
        all_goals first
          | rfl
          | exact ih et lb
      | Gpop1 =>
        rcases lb with _ | ⟨_ | _, lb⟩ <;> cases e <;> cases b0
        all_goals first
          | rfl
          | exact ih et lb

/-- Coq `match_gram_neg`. -/
theorem match_gram_neg (b0 : Bool) (et : Colseq) (w : Chromogram) :
    matchg [b0] et (gramNeg w) = matchg [!b0] et w :=
  match_gramNegRec b0 w et []

/-- Coq `gram_flip_rec n w`: change into a `Gpush` the first `Gpop` of `w` that is matched
neither by an earlier `Gpush` of `w` nor by one of the `n` chords opened before `w`, and adjust
the bit of the next unmatched `Gpop` so that the total parity is inverted. -/
def gramFlipRec (n : ℕ) (w : Chromogram) : Chromogram :=
  match w, n with
  | Gpush :: w', _ => Gpush :: gramFlipRec (n + 1) w'
  | Gskip :: w', _ => Gskip :: gramFlipRec n w'
  | s :: w', n' + 1 => s :: gramFlipRec n' w'
  | Gpop0 :: w', 0 => Gpush :: gramNeg w'
  | Gpop1 :: w', 0 => Gpush :: w'
  | [], _ => Gpush :: w

/-- Coq `gram_flip w`: change the first unmatched `Gpop` of `w` into a `Gpush`, setting the
parity bit of the next unmatched `Gpop` so that the overall parity of the resulting chromogram
is inverted.  This turns a chromogram with exactly two unbalanced `Gpop`s into a balanced
one. -/
def gramFlip : Chromogram → Chromogram := gramFlipRec 0

/-- The generalized statement proved by induction in Coq `match_gram_flip`, in the context
`lb`. -/
private theorem match_gramFlipRec (w : Chromogram) :
    ∀ (et : Colseq) (lb : List Bool),
      matchg lb et (gramFlipRec lb.length w) =
        (matchg (lb ++ [true, false]) et w || matchg (lb ++ [false, true]) et w) := by
  induction w with
  | nil =>
    intro et lb
    rw [show gramFlipRec lb.length [] = [Gpush] by cases lb <;> rfl,
      matchg_nil_of_ne_nil (by simp), matchg_nil_of_ne_nil (by simp)]
    cases et with
    | nil => rfl
    | cons e et => cases e <;> cases et <;> rfl
  | cons s w ih =>
    intro et lb
    cases et with
    | nil => cases s <;> cases lb <;> rfl
    | cons e et =>
      cases s with
      | Gpush =>
        cases e
        all_goals first
          | rfl
          | exact ih et (false :: lb)
          | exact ih et (true :: lb)
      | Gskip =>
        cases e
        all_goals first
          | rfl
          | exact ih et lb
      | Gpop0 =>
        rcases lb with _ | ⟨_ | _, lb⟩
        · cases e
          · rfl
          · rfl
          · show matchg [false] et (gramNeg w) = (false || matchg [true] et w)
            rw [match_gram_neg, Bool.false_or]
            rfl
          · show matchg [true] et (gramNeg w) = (matchg [false] et w || false)
            rw [match_gram_neg, Bool.or_false]
            rfl
        all_goals cases e
        all_goals first
          | rfl
          | exact ih et lb
      | Gpop1 =>
        rcases lb with _ | ⟨_ | _, lb⟩ <;> cases e
        all_goals first
          | rfl
          | exact ih et lb
          | exact (Bool.or_false _).symm

/-- Coq `match_gram_flip`. -/
theorem match_gram_flip (et : Colseq) (w : Chromogram) :
    matchg [] et (gramFlip w) = (matchg [true, false] et w || matchg [false, true] et w) :=
  match_gramFlipRec w et []

/-- Coq `gram_rot w`: if `w` is balanced (all `Gpush` and `Gpop` are matched), the chromogram
that matches the left rotation of the edge colorings matched by `w` (obtained by moving the
first symbol to the end, changing it to a `Gpop` if it is a `Gpush`, and flipping the matching
`Gpop`); otherwise `w` itself.  Coq's `[exists b, gram_balanced 0 b w]` is computed as
`gramBalanced 0 true w || gramBalanced 0 false w`. -/
def gramRot (w : Chromogram) : Chromogram :=
  if gramBalanced 0 true w || gramBalanced 0 false w then
    match w with
    | Gpush :: w' => gramFlip (w' ++ [Gpop1])
    | Gskip :: w' => w' ++ [Gskip]
    | _ => w
  else w

/-- `matchg` never matches a nonempty trace with the empty chromogram. -/
private theorem matchg_cons_nil (lb : List Bool) (e : Color) (et : Colseq) :
    matchg lb (e :: et) [] = false := by
  cases lb <;> rfl

/-- `matchg` never matches the empty trace with a nonempty chromogram. -/
private theorem matchg_nil_cons (lb : List Bool) (s : GramSymbol) (w : Chromogram) :
    matchg lb [] (s :: w) = false := by
  cases lb <;> rfl

/-- `matchg` never matches a nonempty trace with the empty chromogram. -/
private theorem matchg_append_nil (lb : List Bool) (et : Colseq) (e : Color) :
    matchg lb (et ++ [e]) [] = false := by
  cases et <;> exact matchg_cons_nil _ _ _

/-- `matchg` never matches the empty trace with a nonempty chromogram. -/
private theorem matchg_nil_append (lb : List Bool) (w : Chromogram) (s : GramSymbol) :
    matchg lb [] (w ++ [s]) = false := by
  cases w <;> exact matchg_nil_cons _ _ _

/-- Appending a `Gpop1` (the `Gpush` case of Coq `match_gram_rot`): the final `Gpop1` closes
the bottom chord of the context. -/
private theorem matchg_append_Gpop1 (e : Color) (w : Chromogram) :
    ∀ (b0 : Bool) (et : Colseq) (lb : List Bool) (b : Bool),
      gramBalanced lb.length b0 w = true →
      matchg (b :: lb) (et ++ [e]) (w ++ [Gpop1]) =
        (matchg (belast b lb) et w && decide (e = ccons true (!last b lb))) := by
  induction w with
  | nil =>
    intro b0 et lb b hbal
    cases lb with
    | cons b' lb => exact absurd hbal (by cases b0 <;> simp [gramBalanced])
    | nil =>
      cases et with
      | nil => cases e <;> cases b <;> rfl
      | cons e' et =>
        rw [belast_nil, matchg_cons_nil, Bool.false_and]
        cases e' <;> cases b <;> first | rfl | exact matchg_append_nil _ _ _
  | cons s w ih =>
    intro b0 et lb b hbal
    cases et with
    | nil =>
      rw [matchg_nil_cons, Bool.false_and]
      cases e <;> cases s <;> rcases lb with _ | ⟨_ | _, lb⟩ <;> cases b <;>
        first | rfl | exact matchg_nil_append _ _ _
    | cons e' et =>
      cases s with
      | Gpush =>
        cases e' with
        | Color2 => exact ih b0 et (b :: lb) false hbal
        | Color3 => exact ih b0 et (b :: lb) true hbal
        | Color0 => exact (Bool.false_and _).symm
        | Color1 => exact (Bool.false_and _).symm
      | Gskip =>
        cases e' with
        | Color1 => exact ih (!b0) et lb b hbal
        | Color0 => exact (Bool.false_and _).symm
        | Color2 => exact (Bool.false_and _).symm
        | Color3 => exact (Bool.false_and _).symm
      | Gpop0 =>
        cases lb with
        | nil => exact absurd hbal (by simp [gramBalanced])
        | cons b' lb =>
          cases e' <;> cases b
          all_goals first
            | exact (Bool.false_and _).symm
            | exact ih b0 et lb b' hbal
      | Gpop1 =>
        cases lb with
        | nil => exact absurd hbal (by simp [gramBalanced])
        | cons b' lb =>
          cases e' <;> cases b
          all_goals first
            | exact (Bool.false_and _).symm
            | exact ih (!b0) et lb b' hbal

/-- Appending a `Gskip` (the `Gskip` case of Coq `match_gram_rot`). -/
private theorem matchg_append_Gskip (e : Color) (w : Chromogram) :
    ∀ (et : Colseq) (lb : List Bool),
      matchg lb (et ++ [e]) (w ++ [Gskip]) = (matchg lb et w && decide (e = Color1)) := by
  induction w with
  | nil =>
    intro et lb
    cases et with
    | nil =>
      cases e
      all_goals first
        | exact (Bool.and_false _).symm
        | exact (Bool.and_true _).symm
    | cons e' et =>
      rw [matchg_cons_nil, Bool.false_and]
      cases e' <;> first | rfl | exact matchg_append_nil _ _ _
  | cons s w ih =>
    intro et lb
    cases et with
    | nil =>
      rw [matchg_nil_cons, Bool.false_and]
      cases e <;> cases s <;> rcases lb with _ | ⟨_ | _, lb⟩ <;>
        first | rfl | exact matchg_nil_append _ _ _
    | cons e' et =>
      cases s with
      | Gpush =>
        cases e' with
        | Color2 => exact ih et (false :: lb)
        | Color3 => exact ih et (true :: lb)
        | Color0 => exact (Bool.false_and _).symm
        | Color1 => exact (Bool.false_and _).symm
      | Gskip =>
        cases e' with
        | Color1 => exact ih et lb
        | Color0 => exact (Bool.false_and _).symm
        | Color2 => exact (Bool.false_and _).symm
        | Color3 => exact (Bool.false_and _).symm
      | Gpop0 =>
        rcases lb with _ | ⟨_ | _, lb⟩ <;> cases e'
        all_goals first
          | exact (Bool.false_and _).symm
          | exact ih et lb
      | Gpop1 =>
        rcases lb with _ | ⟨_ | _, lb⟩ <;> cases e'
        all_goals first
          | exact (Bool.false_and _).symm
          | exact ih et lb

/-- `gramFlipRec` never returns the empty chromogram. -/
private theorem gramFlipRec_cons (n : ℕ) (w : Chromogram) :
    ∃ s w', gramFlipRec n w = s :: w' := by
  rcases w with _ | ⟨_ | _ | _ | _, w⟩ <;> rcases n with _ | n <;> exact ⟨_, _, rfl⟩

/-- Coq `match_gram_rot`: `gramRot w` matches `rot 1 et` exactly when `w` matches `et`. -/
theorem match_gram_rot (et : Colseq) (w : Chromogram) :
    matchg [] (rot 1 et) (gramRot w) = matchg [] et w := by
  unfold gramRot
  by_cases hbal : (gramBalanced 0 true w || gramBalanced 0 false w) = true
  · rw [ite_eq_left hbal]
    obtain ⟨b0, hb0⟩ : ∃ b0, gramBalanced 0 b0 w = true := by
      cases h : gramBalanced 0 true w
      · rw [h, Bool.false_or] at hbal
        exact ⟨false, hbal⟩
      · exact ⟨true, h⟩
    cases et with
    | nil =>
      rcases w with _ | ⟨_ | _ | _ | _, w⟩
      · rfl
      · show matchg [] [] (gramFlip (w ++ [Gpop1])) = false
        obtain ⟨s, w', h⟩ := gramFlipRec_cons 0 (w ++ [Gpop1])
        rw [gramFlip, h]
        exact matchg_nil_cons _ _ _
      · show matchg [] [] (w ++ [Gskip]) = false
        exact matchg_nil_append _ _ _
      · rfl
      · rfl
    | cons e et =>
      rw [rot1_cons]
      rcases w with _ | ⟨_ | _ | _ | _, w⟩
      · exact matchg_append_nil _ _ _
      · show matchg [] (et ++ [e]) (gramFlip (w ++ [Gpop1])) = matchg [] (e :: et) (Gpush :: w)
        rw [match_gram_flip, matchg_append_Gpop1 e w b0 et [false] true hb0,
          matchg_append_Gpop1 e w b0 et [true] false hb0]
        cases e
        · show (matchg [true] et w && false || matchg [false] et w && false) = false
          rw [Bool.and_false, Bool.and_false, Bool.or_false]
        · show (matchg [true] et w && false || matchg [false] et w && false) = false
          rw [Bool.and_false, Bool.and_false, Bool.or_false]
        · show (matchg [true] et w && false || matchg [false] et w && true) = matchg [false] et w
          rw [Bool.and_false, Bool.false_or, Bool.and_true]
        · show (matchg [true] et w && true || matchg [false] et w && false) = matchg [true] et w
          rw [Bool.and_false, Bool.or_false, Bool.and_true]
      · show matchg [] (et ++ [e]) (w ++ [Gskip]) = matchg [] (e :: et) (Gskip :: w)
        rw [matchg_append_Gskip]
        cases e
        · exact Bool.and_false _
        · exact Bool.and_true _
        · exact Bool.and_false _
        · exact Bool.and_false _
      · exact absurd hb0 (by cases b0 <;> simp [gramBalanced])
      · exact absurd hb0 (by cases b0 <;> simp [gramBalanced])
  · rw [ite_eq_right hbal]
    have hnb : ∀ b, gramBalanced 0 b w = false := by
      intro b
      rw [Bool.not_eq_true, Bool.or_eq_false_iff] at hbal
      cases b
      · exact hbal.2
      · exact hbal.1
    have key : ∀ et', matchg [] et' w = false := by
      intro et'
      rw [Bool.eq_false_iff]
      intro h
      have := (matchg_balanced h).2
      rw [hnb] at this
      exact Bool.false_ne_true this
    rw [key, key]


/-! ### Chromogram lemmas for the two cases of the main induction step -/

/-- The chromogram of case (a) of Coq `Kempe_map` (`w2`) matches the traces
`e1 :: e1 :: et` with `et` matching `w`. -/
private theorem matchg_w2 {e1 : Color} (he1 : e1 ≠ Color0) (et : Colseq) (w : Chromogram) :
    matchg [] (e1 :: e1 :: et)
      (if e1 = Color1 then Gskip :: Gskip :: w else Gpush :: Gpop0 :: w) = matchg [] et w := by
  cases e1
  · exact absurd rfl he1
  all_goals rfl

/-- Conversely, the traces matching the chromogram `w2` of case (a) have the form
`e2 :: e2 :: et2`, with `e2 ≠ Color0` and `et2` matching `w`. -/
private theorem matchg_w2_inv (c : Prop) [Decidable c] (w : Chromogram) {et : Colseq}
    (h : matchg [] et (if c then Gskip :: Gskip :: w else Gpush :: Gpop0 :: w) = true) :
    ∃ e2 et2, e2 ≠ Color0 ∧ matchg [] et2 w = true ∧ et = e2 :: e2 :: et2 := by
  by_cases hc : c
  · rw [ite_eq_left hc] at h
    rcases et with _ | ⟨e, _ | ⟨e', et⟩⟩
    · exact absurd h Bool.false_ne_true
    · cases e <;> exact absurd h Bool.false_ne_true
    · cases e <;> cases e'
      all_goals first
        | exact absurd h Bool.false_ne_true
        | exact ⟨_, et, by decide, h, rfl⟩
  · rw [ite_eq_right hc] at h
    rcases et with _ | ⟨e, _ | ⟨e', et⟩⟩
    · exact absurd h Bool.false_ne_true
    · cases e <;> exact absurd h Bool.false_ne_true
    · cases e <;> cases e'
      all_goals first
        | exact absurd h Bool.false_ne_true
        | exact ⟨_, et, by decide, h, rfl⟩

/-- The chromogram of case (b) of Coq `Kempe_map`, built from the first two symbols `s1`, `s2`
and the rest `w` of the chromogram of the contracted map. -/
private def kempeGramB (s1 s2 : GramSymbol) (w : Chromogram) : Chromogram :=
  if Gskip ∈ [s1, s2] then Gpush :: gramNeg w
  else Gskip :: (if s2 = Gpush then gramFlip w else w)

/-- Coq `Ds12` and the first half of case (b) of Coq `Kempe_map`: if the trace
`e2 :: e2 +c e1 :: et` of the contracted map matches `w`, with `e1 ≠ Color0`, then `w` starts
with two symbols `s1`, `s2` satisfying `Ds12`, and `e1 :: et` matches `kempeGramB s1 s2 w'`. -/
private theorem kempe_gram_b1 {e1 e2 : Color} {et : Colseq} {w : Chromogram} (he1 : e1 ≠ Color0)
    (h : matchg [] (e2 :: addc e2 e1 :: et) w = true) :
    ∃ s1 s2 w', w = s1 :: s2 :: w' ∧
      (if s1 = Gpush then s2 ≠ Gpop0 else s1 = Gskip ∧ s2 = Gpush) ∧
      matchg [] (e1 :: et) (kempeGramB s1 s2 w') = true := by
  obtain ⟨s1, s2, w', rfl⟩ : ∃ s1 s2 w', w = s1 :: s2 :: w' := by
    have := matchg_size h
    rcases w with _ | ⟨s1, _ | ⟨s2, w'⟩⟩
    · simp at this
    · simp at this
    · exact ⟨s1, s2, w', rfl⟩
  refine ⟨s1, s2, w', rfl, ?_⟩
  unfold kempeGramB
  cases e1
  · exact absurd rfl he1
  all_goals cases s1 <;> cases s2 <;> cases e2
  all_goals first
    | exact absurd h Bool.false_ne_true
    | refine ⟨by decide, ?_⟩
  -- the remaining cases: rewrite with the chromogram operation lemmas
  all_goals first
    | exact h
    | (show matchg [false] et (gramNeg w') = true; rw [match_gram_neg]; exact h)
    | (show matchg [true] et (gramNeg w') = true; rw [match_gram_neg]; exact h)
    | (change matchg [true, false] et w' = true at h
       show matchg [] et (gramFlip w') = true
       rw [match_gram_flip, h]
       rfl)
    | (change matchg [false, true] et w' = true at h
       show matchg [] et (gramFlip w') = true
       rw [match_gram_flip, h, Bool.or_true])

/-- The second half of case (b) of Coq `Kempe_map`: a trace `e :: et` matching
`kempeGramB s1 s2 w` has `e ≠ Color0`, and it lifts to the trace `e0 :: e0 +c e :: et` of the
contracted map, which matches `s1 :: s2 :: w`. -/
private theorem kempe_gram_b2 {s1 s2 : GramSymbol} {w : Chromogram} {e : Color} {et : Colseq}
    (hs12 : if s1 = Gpush then s2 ≠ Gpop0 else s1 = Gskip ∧ s2 = Gpush)
    (h : matchg [] (e :: et) (kempeGramB s1 s2 w) = true) :
    e ≠ Color0 ∧
      matchg []
        ((if s1 = Gskip then Color1 else if s2 = Gskip then addc Color1 e
          else ccons true (decide (s2 = Gpush) && matchg [false, true] et w)) ::
          addc (if s1 = Gskip then Color1 else if s2 = Gskip then addc Color1 e
            else ccons true (decide (s2 = Gpush) && matchg [false, true] et w)) e :: et)
        (s1 :: s2 :: w) = true := by
  unfold kempeGramB at h
  cases s1 <;> cases s2
  all_goals first
    | exact absurd hs12 (by decide)
    | skip
  all_goals cases e
  all_goals first
    | exact absurd h Bool.false_ne_true
    | skip
  all_goals refine ⟨by decide, ?_⟩
  -- (Gpush, Gpush) : e = Color1 and `et` matches `gramFlip w`
  · change matchg [] et (gramFlip w) = true at h
    rw [match_gram_flip] at h
    cases hb : matchg [false, true] et w
    · rw [hb, Bool.or_false] at h
      exact h
    · exact hb
  -- (Gpush, Gskip)
  · change matchg [false] et (gramNeg w) = true at h
    rw [match_gram_neg] at h
    exact h
  · change matchg [true] et (gramNeg w) = true at h
    rw [match_gram_neg] at h
    exact h
  -- (Gpush, Gpop1)
  · exact h
  -- (Gskip, Gpush)
  · change matchg [false] et (gramNeg w) = true at h
    rw [match_gram_neg] at h
    exact h
  · change matchg [true] et (gramNeg w) = true at h
    rw [match_gram_neg] at h
    exact h

namespace Hypermap

variable {D : Type u}

/-! ### The contracted map (Coq `ez'`, `H`, `h`) -/

section Contract

variable [Fintype D] [DecidableEq D] (G : Hypermap D) (z : D) (hez : G.edge z ≠ z)

/-- Coq `ez'`: the dart `edge z`, as a dart of `WalkupN z`. -/
private def kez : WDart z := ⟨G.edge z, hez⟩

/-- Coq `H`: the map obtained from `G` by contracting the edge `[z; edge z]`, i.e. the
`WalkupE` transform of `WalkupN z` at `edge z`. -/
private abbrev kH : Hypermap (WDart (G.kez z hez)) := (G.WalkupN z).WalkupE (G.kez z hez)

/-- Coq `h`: the projection of the darts of `H` onto the darts of `G`. -/
private def kh (u : WDart (G.kez z hez)) : D := u.1.1

omit [Fintype D] [DecidableEq D] in
/-- The value of `kez`. -/
private theorem kez_val : (G.kez z hez).1 = G.edge z := rfl

/-- The contracted map has two darts less than `G` (Coq `#|H| < n`, from `card_S_Walkup`). -/
private theorem card_kH : Fintype.card D = Fintype.card (WDart (G.kez z hez)) + 2 := by
  rw [card_S_Walkup z, card_S_Walkup (G.kez z hez)]

/-- Coq `planH`: the contracted map of a planar map is planar. -/
private theorem planar_kH (hG : G.Planar) : (G.kH z hez).Planar :=
  planar_WalkupE _ _ (planar_WalkupN G z hG)

variable {G z hez}

omit [Fintype D] [DecidableEq D] in
/-- Coq `Ih`: the projection `h` is injective. -/
private theorem kh_inj : Injective (G.kh z hez) := fun _ _ huv => Subtype.ext (Subtype.ext huv)

omit [Fintype D] [DecidableEq D] in
/-- Coq `z'h`: the projection `h` avoids `z`. -/
private theorem kh_ne (u : WDart (G.kez z hez)) : G.kh z hez u ≠ z := u.1.2

omit [Fintype D] [DecidableEq D] in
/-- Coq `ez'h`: the projection `h` avoids `edge z`. -/
private theorem kh_ne_edge (u : WDart (G.kez z hez)) : G.kh z hez u ≠ G.edge z := fun h =>
  u.2 (Subtype.ext h)

omit [Fintype D] [DecidableEq D] in
/-- Coq `invh`: every dart other than `z` and `edge z` is in the image of `h`. -/
private theorem kh_surj {x : D} (hx : x ≠ z) (hx' : x ≠ G.edge z) : ∃ u, G.kh z hez u = x :=
  ⟨⟨⟨x, hx⟩, fun h => hx' (congrArg Subtype.val h)⟩, rfl⟩

/-- Coq `hE`: `h` commutes with `edge`. -/
private theorem kh_edge (hpl : G.Plain) (u : WDart (G.kez z hez)) :
    G.kh z hez ((G.kH z hez).edge u) = G.edge (G.kh z hez u) := by
  have ee := G.plain_eq hpl
  have hfix : (G.WalkupN z).glink (G.kez z hez) (G.kez z hez) := by
    left
    apply Subtype.ext
    simp only [WalkupN_edge_val, kez, skip1, ee, ite_true]
  have hu1 : u.1.1 ≠ z := u.1.2
  have hu2 : u.1.1 ≠ G.edge z := fun h => u.2 (Subtype.ext h)
  have h1 : G.edge u.1.1 ≠ z := fun h => hu2 ((ee _).symm.trans (congrArg G.edge h))
  have h2 : (G.WalkupN z).edge u.1 ≠ G.kez z hez := by
    intro h
    have := congrArg Subtype.val h
    simp only [WalkupN_edge_val, kez, skip1, ite_eq_right h1] at this
    exact hu1 (G.edgeI this)
  show ((G.WalkupN z).skipEdge (G.kez z hez) u).1.1 = G.edge u.1.1
  rw [glink_fp_skip_edge _ _ hfix u]
  simp only [skip_val, skip1, ite_eq_right h2, WalkupN_edge_val, ite_eq_right h1]

/-- Coq `hN`: `h (node u)` is `node (h u)`, except that `node` is short-circuited around `z`
and `edge z` (`[eta id with z |-> node (edge z), edge z |-> node z] (node (h u))`). -/
private theorem kh_node (hpl : G.Plain) (hn : ∀ x, G.node x ≠ x) (u : WDart (G.kez z hez)) :
    G.kh z hez ((G.kH z hez).node u) =
      if G.node (G.kh z hez u) = z then G.node (G.edge z)
      else if G.node (G.kh z hez u) = G.edge z then G.node z else G.node (G.kh z hez u) := by
  have ee := G.plain_eq hpl
  have key : ∀ v : WDart z, ((G.WalkupN z).node v).1 =
      if G.node v.1 = G.edge z then G.node z else if G.node v.1 = z then G.edge z
      else G.node v.1 := by
    intro v
    rw [WalkupN_node_val]
    simp only [skipEdge1, permN_edge, permN_face, permN_node, ite_eq_right (hn z),
      G.plain_eq' hpl z]
    have e1 : G.edge (G.node v.1) = z ↔ G.node v.1 = G.edge z :=
      ⟨fun h => (ee _).symm.trans (congrArg G.edge h), fun h => by rw [h, ee]⟩
    by_cases h1 : G.node v.1 = G.edge z
    · rw [ite_eq_left (e1.2 h1), ite_eq_left h1]
    · rw [ite_eq_right (mt e1.1 h1), ite_eq_right h1]
  have hx1 : u.1.1 ≠ z := u.1.2
  have hx2 : u.1.1 ≠ G.edge z := fun h => u.2 (Subtype.ext h)
  have hc : (G.WalkupN z).node u.1 = G.kez z hez ↔ ((G.WalkupN z).node u.1).1 = G.edge z :=
    Subtype.ext_iff
  show (skip1 (G.kez z hez) (G.WalkupN z).node u.1).1 = _
  unfold skip1
  unfold kh
  by_cases h1 : G.node u.1.1 = z
  · have h2 : G.node u.1.1 ≠ G.edge z := fun h => hez (h.symm.trans h1)
    have hc' : (G.WalkupN z).node u.1 = G.kez z hez :=
      hc.2 (by rw [key, ite_eq_right h2, ite_eq_left h1])
    have h3 : G.node (G.edge z) ≠ z := fun h => hx2 (G.nodeI (h1.trans h.symm))
    rw [ite_eq_left hc', key, kez_val, ite_eq_left h1, ite_eq_right (hn _), ite_eq_right h3]
  · by_cases h2 : G.node u.1.1 = G.edge z
    · have h3 : G.node z ≠ G.edge z := fun h => hx1 (G.nodeI (h2.trans h.symm))
      have hc' : (G.WalkupN z).node u.1 ≠ G.kez z hez := fun h =>
        h3 (by rw [← hc.1 h, key, ite_eq_left h2])
      rw [ite_eq_right hc', key, ite_eq_left h2, ite_eq_right h1, ite_eq_left h2]
    · have hc' : (G.WalkupN z).node u.1 ≠ G.kez z hez := fun h =>
        h2 (by rw [← hc.1 h, key, ite_eq_right h2, ite_eq_right h1])
      rw [ite_eq_right hc', key, ite_eq_right h2, ite_eq_right h1, ite_eq_right h1,
        ite_eq_right h2]

end Contract

/-! ### The induction step, for an abstract contraction -/

section Step

variable {D' : Type u}

/-- The properties of the projection `h` of the contracted map `H` onto `G` used in the proof
of Coq `Kempe_map`, after `clearbody h H`: Coq's local facts `Ih`, `z'h`, `ez'h`, `invh`, `hE`
and `hN`. -/
private structure KContract [DecidableEq D] (G : Hypermap D) (H : Hypermap D') (h : D' → D)
    (z : D) : Prop where
  inj : Injective h
  ne : ∀ u, h u ≠ z
  ne_edge : ∀ u, h u ≠ G.edge z
  surj : ∀ x, x ≠ z → x ≠ G.edge z → ∃ u, h u = x
  edge : ∀ u, h (H.edge u) = G.edge (h u)
  node : ∀ u, h (H.node u) = if G.node (h u) = z then G.node (G.edge z)
    else if G.node (h u) = G.edge z then G.node z else G.node (h u)

namespace KContract

variable [DecidableEq D] {G : Hypermap D} {H : Hypermap D'} {h : D' → D} {z : D}

/-- `hN` away from `z` and `edge z`. -/
private theorem node_of (hK : KContract G H h z) (u : D') (h1 : G.node (h u) ≠ z)
    (h2 : G.node (h u) ≠ G.edge z) : h (H.node u) = G.node (h u) := by
  rw [hK.node, ite_eq_right h1, ite_eq_right h2]

/-- `hN` at `z`. -/
private theorem node_z (hK : KContract G H h z) (u : D') (h1 : G.node (h u) = z) :
    h (H.node u) = G.node (G.edge z) := by
  rw [hK.node, ite_eq_left h1]

/-- `hN` at `edge z`. -/
private theorem node_ez (hK : KContract G H h z) (hez : G.edge z ≠ z) (u : D')
    (h1 : G.node (h u) = G.edge z) : h (H.node u) = G.node z := by
  rw [hK.node, ite_eq_right (fun h' => hez (h1.symm.trans h')), ite_eq_left h1]

/-- Coq `invh_p`: a sequence avoiding `z` and `edge z` lifts to `H`. -/
private theorem lift_list (hK : KContract G H h z) :
    ∀ q : List D, (∀ x ∈ q, x ≠ z ∧ x ≠ G.edge z) → ∃ s : List D', s.map h = q
  | [], _ => ⟨[], rfl⟩
  | x :: q, hq => by
    obtain ⟨u, rfl⟩ := hK.surj x (hq x List.mem_cons_self).1 (hq x List.mem_cons_self).2
    obtain ⟨s, hs⟩ := hK.lift_list q fun y hy => hq y (List.mem_cons_of_mem _ hy)
    exact ⟨u :: s, by rw [List.map_cons, hs]⟩

/-- Coq `invhNp`: node paths of `G` lift to node paths of `H`. -/
private theorem lift_path (hK : KContract G H h z) :
    ∀ (u : D') (s : List D'), fpath G.node (h u) (s.map h) → fpath H.node u s
  | _, [], _ => trivial
  | u, v :: s, hp => by
    obtain ⟨hv, hp⟩ := hp
    refine ⟨hK.inj ?_, hK.lift_path v s hp⟩
    have hv : G.node (h u) = h v := hv
    rw [hK.node_of u (hv ▸ hK.ne v) (hv ▸ hK.ne_edge v), hv]

variable [Finite D']

/-- Coq `plainH`. -/
private theorem plain [Finite D] (hK : KContract G H h z) (hpl : G.Plain) : H.Plain := by
  refine (plainP _).2 fun u _ => ⟨hK.inj ?_, fun h' => ?_⟩
  · rw [hK.edge, hK.edge, G.plain_eq hpl]
  · have := congrArg h h'
    rw [hK.edge] at this
    exact G.plain_neq hpl _ this

/-- The face of `h u`, computed from `h (face u)` (Coq `rewrite -[in h u](faceK u) hE hN`). -/
private theorem edge_face (hK : KContract G H h z) (u : D') :
    h u = G.edge (if G.node (h (H.face u)) = z then G.node (G.edge z)
      else if G.node (h (H.face u)) = G.edge z then G.node z else G.node (h (H.face u))) := by
  conv_lhs => rw [← H.faceK u]
  rw [hK.edge, hK.node]

end KContract

/-- Membership in a node cycle is closed under `node`. -/
private theorem mem_ncycle_node [Finite D] {G : Hypermap D} {q : List D}
    (hq : fcycle G.node q) {x : D} (hx : x ∈ q) (y : D) : y ∈ q ↔ G.node y ∈ q := by
  rw [← fconnect_cycle hq hx, ← fconnect_cycle hq hx]
  exact G.cnode1r x y

/-- Coq's construction of the ring `s` of `H`: an N-cycle whose projection is `p1` if
`face z = z` (case (a)), and `node (edge z) :: face z :: nz :: p1` otherwise (case (b)). -/
private theorem KContract.exists_s [Finite D] [DecidableEq D] [Finite D'] {G : Hypermap D}
    {H : Hypermap D'} {h : D' → D} {z nz : D} {p1 : List D}
    (hK : KContract G H h z) (hpl : G.Plain) (hn : ∀ x, G.node x ≠ x)
    (hcyc : fcycle G.node (z :: nz :: p1)) (hU : (z :: nz :: p1).Nodup)
    (hcub : G.Quasicubic (z :: nz :: p1)) (hDfz : G.face z = z ∨ G.face z ∉ z :: nz :: p1) :
    ∃ s, fcycle H.node s ∧
      s.map h = if G.face z = z then p1 else G.node (G.edge z) :: G.face z :: nz :: p1 := by
  have ee := G.plain_eq hpl
  have nf_e := G.plain_eq' hpl
  have hez : G.edge z ≠ z := G.plain_neq hpl z
  have hc : path (frel G.node) z (nz :: p1 ++ [z]) := hcyc
  rw [List.cons_append, path_cons, path_concat] at hc
  obtain ⟨hDnz, hp, hL⟩ := hc
  change G.node z = nz at hDnz
  change G.node (last nz p1) = z at hL
  have memN := mem_ncycle_node hcyc List.mem_cons_self
  rw [List.nodup_cons, List.nodup_cons] at hU
  obtain ⟨hz, hnzp1, -⟩ := hU
  by_cases hfz : G.face z = z
  · rw [ite_eq_left hfz]
    have ez_nz : G.edge z = nz := by rw [← nf_e z, hfz, hDnz]
    obtain ⟨s, hs⟩ := hK.lift_list p1 fun x hx =>
      ⟨fun h' => hz (List.mem_cons_of_mem _ (h' ▸ hx)),
        fun h' => hnzp1 (by rw [← ez_nz, ← h']; exact hx)⟩
    refine ⟨s, ?_, hs⟩
    cases s with
    | nil => trivial
    | cons u s1 =>
      rw [List.map_cons] at hs
      subst hs
      obtain ⟨hu, hp1⟩ := hp
      change G.node nz = h u at hu
      show path (frel H.node) u (s1 ++ [u])
      rw [path_concat]
      refine ⟨hK.lift_path u s1 hp1, hK.inj ?_⟩
      have hl : G.node (h (last u s1)) = z := by rw [← last_map h u s1]; exact hL
      rw [hK.node_z _ hl, ez_nz, hu]
  · rw [ite_eq_right hfz]
    have hfzq : G.face z ∉ z :: nz :: p1 := hDfz.resolve_left hfz
    obtain ⟨Dn3fz, -⟩ := (G.cubicP).1 hcub _ hfzq
    -- `node (edge z)` is not on the node cycle of `z`
    have hnez : G.node (G.edge z) ∉ z :: nz :: p1 := by
      intro hm
      rw [← nf_e z, memN, Dn3fz] at hm
      exact hfzq hm
    have hfez : G.face z ≠ G.edge z := fun h' => hn (G.edge z) (by rw [← h', nf_e, h'])
    have hq : ∀ x ∈ G.node (G.edge z) :: G.face z :: nz :: p1, x ≠ z ∧ x ≠ G.edge z := by
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨fun h' => hnez (by rw [h']; exact List.mem_cons_self), hn _⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨hfz, hfez⟩
      exact ⟨fun h' => hz (h' ▸ hx),
        fun h' => hnez ((memN _).1 (List.mem_cons_of_mem z (h' ▸ hx)))⟩
    obtain ⟨s, hs⟩ := hK.lift_list _ hq
    refine ⟨s, ?_, hs⟩
    rcases s with _ | ⟨u, _ | ⟨v, _ | ⟨w, s1⟩⟩⟩
    · exact absurd hs (by simp)
    · exact absurd hs (by simp)
    · exact absurd hs (by simp)
    simp only [List.map_cons, List.cons.injEq] at hs
    obtain ⟨hu, hv, hw, hs1⟩ := hs
    subst hs1
    show path (frel H.node) u (v :: w :: (s1 ++ [u]))
    rw [path_cons, path_cons, path_concat]
    refine ⟨hK.inj ?_, hK.inj ?_, ⟨?_, hK.inj ?_⟩⟩
    · have hnu : G.node (h u) = G.face z := by rw [hu, ← nf_e z, Dn3fz]
      rw [hK.node_of u (by rw [hnu]; exact hfz) (by rw [hnu]; exact hfez), hnu, hv]
    · rw [hK.node_ez hez v (by rw [hv, nf_e]), hw, hDnz]
    · rw [← hw] at hp; exact hK.lift_path w s1 hp
    · have hl : G.node (h (last w s1)) = z := by rw [← last_map h w s1, hw]; exact hL
      rw [hK.node_z _ hl, hu]

/-- Coq `cubHs` (before rotation): `H` is quasicubic with respect to `s`. -/
private theorem KContract.quasicubic_s [Finite D] [DecidableEq D] [Finite D'] {G : Hypermap D}
    {H : Hypermap D'} {h : D' → D} {z nz : D} {p1 : List D} {s : List D'}
    (hK : KContract G H h z) (hpl : G.Plain) (hn : ∀ x, G.node x ≠ x)
    (hcyc : fcycle G.node (z :: nz :: p1)) (hcub : G.Quasicubic (z :: nz :: p1))
    (hs : s.map h = if G.face z = z then p1 else G.node (G.edge z) :: G.face z :: nz :: p1) :
    H.Quasicubic s := by
  have ee := G.plain_eq hpl
  have nf_e := G.plain_eq' hpl
  have hc : path (frel G.node) z (nz :: p1 ++ [z]) := hcyc
  rw [List.cons_append, path_cons] at hc
  have hDnz : G.node z = nz := hc.1
  have memN := mem_ncycle_node hcyc List.mem_cons_self
  refine (H.cubicP).2 fun u hu => ?_
  change u ∉ s at hu
  have s'x : h u ∉ s.map h := fun hm => hu ((List.mem_map_of_injective hK.inj).1 hm)
  rw [hs] at s'x
  have zN'x : h u ∉ z :: nz :: p1 := by
    intro hm
    rcases List.mem_cons.1 hm with h' | hm
    · exact hK.ne u h'
    by_cases hfz : G.face z = z
    · rw [ite_eq_left hfz] at s'x
      rcases List.mem_cons.1 hm with h' | hm
      · have ez_nz : G.edge z = nz := by rw [← nf_e z, hfz, hDnz]
        exact hK.ne_edge u (h'.trans ez_nz.symm)
      · exact s'x hm
    · rw [ite_eq_right hfz] at s'x
      exact s'x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
  obtain ⟨Dn3x, -⟩ := (G.cubicP).1 hcub (h u) zN'x
  have z'nx : G.node (h u) ≠ z := fun h' =>
    zN'x ((memN (h u)).2 (by rw [h']; exact List.mem_cons_self))
  have hfzx : h u ≠ G.face z := by
    intro h'
    by_cases hfz : G.face z = z
    · exact hK.ne u (h'.trans hfz)
    · rw [ite_eq_right hfz] at s'x
      exact s'x (by rw [h']; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have ez'nx : G.node (h u) ≠ G.edge z := by
    intro h'
    have := G.nodeK (h u)
    rw [h', ee] at this
    exact hfzx this.symm
  have h_nu : h (H.node u) = G.node (h u) := hK.node_of u z'nx ez'nx
  refine ⟨hK.inj ?_, fun h' => hn (h u) (by rw [← h_nu, h'])⟩
  have z'n2x : G.node (G.node (h u)) ≠ z := fun h' =>
    zN'x (by rw [memN, memN, h']; exact List.mem_cons_self)
  have ez'n2x : G.node (G.node (h u)) ≠ G.edge z := by
    intro h'
    have hfz : G.face z = G.node (h u) := by
      have := G.nodeK (G.node (h u))
      rw [h', ee] at this
      exact this
    have hfz' : G.face z ≠ z := by rw [hfz]; exact z'nx
    rw [ite_eq_right hfz'] at s'x
    apply s'x
    have : h u = G.node (G.edge z) := by rw [← h', Dn3x]
    rw [this]
    exact List.mem_cons_self
  have h_n2u : h (H.node (H.node u)) = G.node (G.node (h u)) := by
    rw [hK.node_of _ (by rw [h_nu]; exact z'n2x) (by rw [h_nu]; exact ez'n2x), h_nu]
  rw [hK.node_of _ (by rw [h_n2u, Dn3x]; exact hK.ne u)
    (by rw [h_n2u, Dn3x]; exact hK.ne_edge u), h_n2u, Dn3x]

/-- Coq `geoH` (duplicate-freeness part, before rotation). -/
private theorem KContract.nodup_s [Finite D] [DecidableEq D] {G : Hypermap D}
    {H : Hypermap D'} {h : D' → D} {z nz : D} {p1 : List D} {s : List D'}
    (hK : KContract G H h z) (hpl : G.Plain) (hn : ∀ x, G.node x ≠ x)
    (hcyc : fcycle G.node (z :: nz :: p1)) (hU : (z :: nz :: p1).Nodup)
    (hcub : G.Quasicubic (z :: nz :: p1)) (hDfz : G.face z = z ∨ G.face z ∉ z :: nz :: p1)
    (hs : s.map h = if G.face z = z then p1 else G.node (G.edge z) :: G.face z :: nz :: p1) :
    s.Nodup := by
  have nf_e := G.plain_eq' hpl
  have memN := mem_ncycle_node hcyc List.mem_cons_self
  rw [← List.nodup_map_iff hK.inj, hs]
  rw [List.nodup_cons, List.nodup_cons] at hU
  by_cases hfz : G.face z = z
  · rw [ite_eq_left hfz]
    exact hU.2.2
  · rw [ite_eq_right hfz]
    have hfzq : G.face z ∉ z :: nz :: p1 := hDfz.resolve_left hfz
    obtain ⟨Dn3fz, -⟩ := (G.cubicP).1 hcub _ hfzq
    have hnez : G.node (G.edge z) ∉ z :: nz :: p1 := by
      intro hm
      rw [← nf_e z, memN, Dn3fz] at hm
      exact hfzq hm
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨fun hm => hfzq (List.mem_cons_of_mem _ hm),
      List.nodup_cons.2 hU.2⟩⟩
    rw [List.mem_cons, not_or]
    refine ⟨fun h' => hn (G.face z) ?_, fun hm => hnez (List.mem_cons_of_mem _ hm)⟩
    rw [← nf_e z] at h'
    have := congrArg G.node h'
    rw [Dn3fz] at this
    exact this.symm

/-- The right-rotated trace of a coloring of a nonempty sequence. -/
private theorem urtrace_map_cons {α : Type*} (k : α → Color) (x : α) (l : List α) :
    urtrace ((x :: l).map k) = pairmap addc (k (last x l)) (k x :: l.map k) := by
  rw [urtrace, List.map_cons, last_cons, last_map]

/-- Coq `khE`, `khF`: the coloring `k` of `G` induces the coloring `k ∘ h` of `H`. -/
private theorem KContract.coloring_comp [Finite D] [DecidableEq D] [Finite D'] {G : Hypermap D}
    {H : Hypermap D'} {h : D' → D} {z : D} {k : D → Color}
    (hK : KContract G H h z) (hpl : G.Plain) (hk : G.Coloring k) : H.Coloring (k ∘ h) := by
  obtain ⟨kE, kF⟩ := hk
  refine ⟨fun u => ?_, fun u => ?_⟩
  · show k (h (H.edge u)) ≠ k (h u)
    rw [hK.edge]
    exact kE _
  · show k (h (H.face u)) = k (h u)
    rw [hK.edge_face u]
    generalize h (H.face u) = y
    have hy : k y = k (G.edge (G.node y)) := by
      have := kF (G.edge (G.node y))
      rw [G.nodeK] at this
      exact this
    rw [hy]
    by_cases h1 : G.node y = z
    · rw [ite_eq_left h1, h1]
      have := kF (G.edge (G.node (G.edge z)))
      rw [G.nodeK] at this
      exact this
    · rw [ite_eq_right h1]
      by_cases h2 : G.node y = G.edge z
      · rw [ite_eq_left h2, h2, G.plain_eq hpl]
        have := kF (G.edge (G.node z))
        rw [G.nodeK] at this
        exact this
      · rw [ite_eq_right h2]

/-- Coq `invh_col_s`: a coloring `k1` of `H` whose trace on `s` starts with two distinct colors
(in case (b)) lifts to a coloring `k0` of `G`; in case (a), `k0 z +c k0 nz` can be any given
nonzero color `e1`. -/
private theorem KContract.lift_coloring [Finite D] [DecidableEq D] [Finite D'] {G : Hypermap D}
    {H : Hypermap D'} {h : D' → D} {z nz : D} {p1 : List D} {s : List D'}
    (hK : KContract G H h z) (hpl : G.Plain) (hn : ∀ x, G.node x ≠ x)
    (hcyc : fcycle G.node (z :: nz :: p1))
    (hs : s.map h = if G.face z = z then p1 else G.node (G.edge z) :: G.face z :: nz :: p1)
    {k1 : D' → Color} (hk1 : H.Coloring k1) (e1 : Color)
    (hU : (if G.face z = z then [e1, Color0] else (urtrace (s.map k1)).take 2).Nodup) :
    ∃ k0, G.Coloring k0 ∧ (∀ u, k1 u = k0 (h u)) ∧
      (G.face z = z → addc (k0 z) (k0 nz) = e1) := by
  classical
  have ee := G.plain_eq hpl
  have nf_e := G.plain_eq' hpl
  have hez := G.plain_neq hpl z
  have hc : path (frel G.node) z (nz :: p1 ++ [z]) := hcyc
  rw [List.cons_append, path_cons, path_concat] at hc
  obtain ⟨hDnz, -, hL⟩ := hc
  change G.node z = nz at hDnz
  change G.node (last nz p1) = z at hL
  have hLp1 : last nz p1 = G.face (G.edge z) := by
    have := G.nodeK (last nz p1)
    rw [hL] at this
    exact this.symm
  obtain ⟨k1E, k1F⟩ := hk1
  -- an extension `k0` of `k1`
  let k0 : D → Color := fun x => if hx : ∃ u, h u = x then k1 hx.choose else e1
  have Dk0 : ∀ u, k1 u = k0 (h u) := by
    intro u
    have hx : ∃ v, h v = h u := ⟨u, rfl⟩
    simp only [k0, dite_eq_left hx]
    rw [hK.inj hx.choose_spec]
  have hfez : G.face z ≠ G.edge z := fun h' => hn (G.edge z) (by rw [← h', nf_e, h'])
  have hfezz : G.face (G.edge z) ≠ z := fun h' => hn z (by
    have := G.faceK (G.edge z)
    rw [h'] at this
    exact G.edgeI this)
  set e2 := k0 (G.face (G.edge z)) with he2
  set e3 := if G.face z = z then addc e1 e2 else k0 (G.face z) with he3
  have e2'3 : e3 ≠ e2 := by
    by_cases hfz : G.face z = z
    · rw [he3, ite_eq_left hfz]
      rw [ite_eq_left hfz] at hU
      intro h'
      have h0 : e1 = Color0 := by rw [← addcK e1 e2, h', addcc]
      exact (List.nodup_cons.1 hU).1 (by rw [h0]; exact List.mem_singleton_self _)
    · rw [he3, ite_eq_right hfz]
      rw [ite_eq_right hfz] at hU
      have hmap : s.map k1 = (s.map h).map k0 := by
        rw [List.map_map]
        exact List.map_congr_left fun u _ => Dk0 u
      rw [hmap, hs, ite_eq_right hfz, urtrace_map_cons, last_cons, last_cons, hLp1] at hU
      intro h'
      rw [List.map_cons, List.map_cons, pairmap_cons, pairmap_cons] at hU
      simp only [List.take_succ_cons, List.take_zero] at hU
      rw [h', addcC (k0 (G.node (G.edge z)))] at hU
      exact (List.nodup_cons.1 hU).1 (List.mem_singleton_self _)
  let k0' : D → Color := fun x => if x = z then e3 else if x = G.edge z then e2 else k0 x
  have k0'z : k0' z = e3 := by simp only [k0', ite_true]
  have k0'ez : k0' (G.edge z) = e2 := by simp only [k0', ite_eq_right hez, ite_true]
  have k0'h : ∀ x, x ≠ z → x ≠ G.edge z → k0' x = k0 x := fun x h1 h2 => by
    simp only [k0', ite_eq_right h1, ite_eq_right h2]
  refine ⟨k0', ⟨fun x => ?_, fun x => ?_⟩, fun u => ?_, fun hfz => ?_⟩
  · -- edges are properly colored
    by_cases hx1 : x = G.edge z
    · rw [hx1, ee, k0'z, k0'ez]
      exact e2'3
    by_cases hx2 : x = z
    · rw [hx2, k0'z, k0'ez]
      exact e2'3.symm
    obtain ⟨u, rfl⟩ := hK.surj x hx2 hx1
    have h1 : G.edge (h u) ≠ z := fun h' => hx1 (by rw [← h', ee])
    have h2 : G.edge (h u) ≠ G.edge z := fun h' => hx2 (G.edgeI h')
    rw [k0'h _ h1 h2, k0'h _ hx2 hx1, ← hK.edge, ← Dk0, ← Dk0]
    exact k1E u
  · -- faces are uniformly colored
    by_cases hx2 : x = z
    · subst hx2
      by_cases hfz : G.face x = x
      · rw [hfz]
      · rw [k0'h _ hfz hfez, k0'z, he3, ite_eq_right hfz]
    by_cases hx1 : x = G.edge z
    · subst hx1
      rw [k0'ez]
      by_cases h' : G.face (G.edge z) = G.edge z
      · rw [h', k0'ez]
      · rw [k0'h _ hfezz h']
    obtain ⟨u, rfl⟩ := hK.surj x hx2 hx1
    have hxy : k0 (h u) = k0 (h (H.face u)) := by rw [← Dk0, ← Dk0, k1F]
    rw [k0'h _ hx2 hx1, hxy, hK.edge_face u]
    have hne1 := hK.ne (H.face u)
    have hne2 := hK.ne_edge (H.face u)
    generalize h (H.face u) = y at hne1 hne2 ⊢
    by_cases h1 : G.node y = z
    · rw [ite_eq_left h1, G.nodeK, k0'ez, he2]
      have := G.nodeK y
      rw [h1] at this
      rw [this]
    · rw [ite_eq_right h1]
      by_cases h2 : G.node y = G.edge z
      · rw [ite_eq_left h2, G.nodeK, k0'z]
        have hy : y = G.face z := by
          have := G.nodeK y
          rw [h2, ee] at this
          exact this.symm
        have hfz : G.face z ≠ z := hy ▸ hne1
        rw [he3, ite_eq_right hfz, hy]
      · rw [ite_eq_right h2, G.nodeK, k0'h _ hne1 hne2]
  · rw [k0'h _ (hK.ne u) (hK.ne_edge u)]
    exact Dk0 u
  · have ez_nz : G.edge z = nz := by rw [← nf_e z, hfz, hDnz]
    rw [k0'z, ← ez_nz, k0'ez, he3, ite_eq_left hfz, addcK]

/-- A coloring has no node fixed points (Coq `n'id`). -/
private theorem coloring_node_ne [Finite D] {G : Hypermap D} {k : D → Color} (hk : G.Coloring k)
    (x : D) : G.node x ≠ x := by
  intro h
  apply hk.1 (G.node x)
  have := hk.2 (G.edge (G.node x))
  rw [G.nodeK] at this
  rw [← this, h]

/-- math-comp `rot_cycle`, for math-comp's `rot`. -/
private theorem cycle_rot {α : Type*} {e : α → α → Prop} (n : ℕ) (s : List α) :
    cycle e (rot n s) ↔ cycle e s := by
  rcases le_or_gt n s.length with h | h
  · rw [rot_eq_rotate h, cycle_rotate]
  · rw [rot_oversize h.le]

/-- The conclusion of Coq `Kempe_map` for a ring `r` and a coloring `k` (the statement proved
by induction): some chromogram matches the trace of `k` on `r`, and all the traces matching it
are ring traces of `r`. -/
private def KempeProp (G : Hypermap D) (r : List D) (k : D → Color) : Prop :=
  ∃ w, matchg [] (trace (r.map k)) w = true ∧ ∀ et, matchg [] et w = true → G.RingTrace r et

/-- The induction step of Coq `Kempe_map`, for the contraction `h : H → G` of the edge
`[z; edge z]`, where the rotated ring is `z :: nz :: p1`: the Kempe property of `H` (for its
ring `rotr 1 s`) implies the Kempe property of `G`, stated with right-rotated traces. -/
private theorem KContract.kempe_step [Fintype D] [DecidableEq D] [Fintype D'] {G : Hypermap D}
    {H : Hypermap D'} {h : D' → D} {z nz : D} {p1 : List D} {k : D → Color}
    (hK : KContract G H h z) (hpl : G.Plain) (hk : G.Coloring k) (hplH : H.Planar)
    (IH : ∀ r', H.UCyclePlanarPlainQuasicubic r' → ∀ k', H.Coloring k' → KempeProp H r' k')
    (hcyc : fcycle G.node (z :: nz :: p1)) (hU : (z :: nz :: p1).Nodup)
    (hcub : G.Quasicubic (z :: nz :: p1)) (hDfz : G.face z = z ∨ G.face z ∉ z :: nz :: p1) :
    ∃ w, matchg [] (urtrace ((z :: nz :: p1).map k)) w = true ∧
      ∀ et, matchg [] et w = true →
        ∃ k0, G.Coloring k0 ∧ et = urtrace ((z :: nz :: p1).map k0) := by
  have nf_e := G.plain_eq' hpl
  have hn := coloring_node_ne hk
  have hc : path (frel G.node) z (nz :: p1 ++ [z]) := hcyc
  rw [List.cons_append, path_cons, path_concat] at hc
  obtain ⟨hDnz, -, hL⟩ := hc
  change G.node z = nz at hDnz
  change G.node (last nz p1) = z at hL
  have hLp1 : last nz p1 = G.face (G.edge z) := by
    have := G.nodeK (last nz p1)
    rw [hL] at this
    exact this.symm
  obtain ⟨s, hcycs, hs⟩ := hK.exists_s hpl hn hcyc hU hcub hDfz
  have geoH : H.UCyclePlanarPlainQuasicubic (rotr 1 s) := by
    refine ⟨⟨⟨hK.plain hpl, ?_⟩, ?_, ?_⟩, hplH⟩
    · have hq := hK.quasicubic_s hpl hn hcyc hcub hs
      intro x hx
      exact hq (fun h' => hx (mem_rotr.2 h'))
    · show cycle _ (rot _ s)
      exact (cycle_rot _ _).2 hcycs
    · exact nodup_rotr.2 (hK.nodup_s hpl hn hcyc hU hcub hDfz hs)
  obtain ⟨w, kMw, sMw⟩ := IH _ geoH (k ∘ h) (hK.coloring_comp hpl hk)
  have htr : ∀ k1 : D' → Color, trace ((rotr 1 s).map k1) = urtrace (s.map k1) := by
    intro k1
    rw [← urtrace_trace, ← map_rot, rotrK]
  have hk0map : ∀ (k1 : D' → Color) (k0 : D → Color), (∀ u, k1 u = k0 (h u)) →
      s.map k1 = (s.map h).map k0 := by
    intro k1 k0 Dk0
    rw [List.map_map]
    exact List.map_congr_left fun u _ => Dk0 u
  rw [htr, hk0map (k ∘ h) k fun _ => rfl] at kMw
  have sMw' : ∀ et, matchg [] et w = true →
      ∃ k1, H.Coloring k1 ∧ et = urtrace (s.map k1) := by
    intro et het
    obtain ⟨k1, hk1, hdef⟩ := sMw et het
    exact ⟨k1, hk1, by rw [hdef, htr]⟩
  by_cases hfz : G.face z = z
  · -- case (a): the edge of `z` loops back to the ring, enclosing the face of `z`
    have hs' : s.map h = p1 := by rw [hs, ite_eq_left hfz]
    have ez_nz : G.edge z = nz := by rw [← nf_e z, hfz, hDnz]
    have trace_r : ∀ k0, G.Coloring k0 → addc (k0 z) (k0 nz) ≠ Color0 ∧
        urtrace ((z :: nz :: p1).map k0) =
          addc (k0 z) (k0 nz) :: addc (k0 z) (k0 nz) :: urtrace (p1.map k0) := by
      intro k0 hk0
      obtain ⟨k0E, k0F⟩ := hk0
      have hkL : k0 (last nz p1) = k0 nz := by rw [hLp1, k0F, ez_nz]
      constructor
      · rw [Ne, addc_eq0]
        intro h'
        apply k0E nz
        have := G.faceK z
        rw [hfz, hDnz] at this
        rw [this, h']
      · have hurt : pairmap addc (k0 nz) (p1.map k0) = urtrace (p1.map k0) := by
          cases p1 with
          | nil => rfl
          | cons x p2 =>
            rw [urtrace_map_cons, ← hkL]
            rfl
        rw [urtrace_map_cons, last_cons, hkL, List.map_cons, pairmap_cons, pairmap_cons,
          addcC (k0 nz), hurt]
    obtain ⟨hne, htr1⟩ := trace_r k hk
    rw [hs'] at kMw
    refine ⟨if addc (k z) (k nz) = Color1 then Gskip :: Gskip :: w else Gpush :: Gpop0 :: w,
      ?_, ?_⟩
    · rw [htr1, matchg_w2 hne]
      exact kMw
    · intro et het
      obtain ⟨e2, et2, hne2, het2, rfl⟩ := matchg_w2_inv _ w het
      obtain ⟨k1, hk1, Det2⟩ := sMw' et2 het2
      obtain ⟨k0, hk0, Dk0, De2⟩ := hK.lift_coloring hpl hn hcyc hs hk1 e2 (by
        rw [ite_eq_left hfz]
        exact List.nodup_cons.2 ⟨fun h' => hne2 (List.mem_singleton.1 h'),
          List.nodup_singleton _⟩)
      refine ⟨k0, hk0, ?_⟩
      rw [(trace_r k0 hk0).2, De2 hfz, Det2, hk0map k1 k0 Dk0, hs']
  · -- case (b): the edge of `z` leads to an inner (cubic) node
    have hs' : s.map h = G.node (G.edge z) :: G.face z :: nz :: p1 := by
      rw [hs, ite_eq_right hfz]
    have hT : ∀ k0 : D → Color, (∀ x, k0 (G.face x) = k0 x) →
        urtrace ((z :: nz :: p1).map k0) =
          addc (k0 (G.edge z)) (k0 z) :: addc (k0 z) (k0 nz) ::
            pairmap addc (k0 nz) (p1.map k0) ∧
        urtrace ((G.node (G.edge z) :: G.face z :: nz :: p1).map k0) =
          addc (k0 (G.edge z)) (k0 (G.node (G.edge z))) :: addc (k0 (G.node (G.edge z))) (k0 z) ::
            addc (k0 z) (k0 nz) :: pairmap addc (k0 nz) (p1.map k0) := by
      intro k0 k0F
      have hkL : k0 (last nz p1) = k0 (G.edge z) := by rw [hLp1, k0F]
      constructor
      · rw [urtrace_map_cons, last_cons, hkL, List.map_cons, pairmap_cons, pairmap_cons]
      · rw [urtrace_map_cons, last_cons, last_cons, hkL, List.map_cons, List.map_cons,
          pairmap_cons, pairmap_cons, pairmap_cons, k0F]
    have hne1 : addc (k (G.edge z)) (k z) ≠ Color0 := by
      rw [Ne, addc_eq0]
      exact hk.1 z
    have De21 : addc (addc (k (G.edge z)) (k (G.node (G.edge z)))) (addc (k (G.edge z)) (k z)) =
        addc (k (G.node (G.edge z))) (k z) := by
      rw [addcC (k (G.edge z)) (k (G.node (G.edge z))), ← addcA, addKc]
    rw [hs', (hT k hk.2).2, ← De21] at kMw
    obtain ⟨s1, s2, w', rfl, hs12, hmatch⟩ := kempe_gram_b1 hne1 kMw
    refine ⟨kempeGramB s1 s2 w', ?_, ?_⟩
    · rw [(hT k hk.2).1]
      exact hmatch
    · intro et' het'
      rcases et' with _ | ⟨e, et⟩
      · exfalso
        have := matchg_size het'
        unfold kempeGramB at this
        split_ifs at this
      obtain ⟨hne, hmw⟩ := kempe_gram_b2 hs12 het'
      generalize (if s1 = Gskip then Color1 else if s2 = Gskip then addc Color1 e
          else ccons true (decide (s2 = Gpush) && matchg [false, true] et w')) = e0 at hmw
      obtain ⟨k1, hk1, Det⟩ := sMw' _ hmw
      obtain ⟨k0, hk0, Dk0, -⟩ := hK.lift_coloring hpl hn hcyc hs hk1 Color0 (by
        rw [ite_eq_right hfz, ← Det]
        simp only [List.take_succ_cons, List.take_zero]
        refine List.nodup_cons.2 ⟨fun h' => hne ?_, List.nodup_singleton _⟩
        have := congrArg (addc e0) (List.mem_singleton.1 h')
        rw [addcc, addKc] at this
        exact this.symm)
      refine ⟨k0, hk0, ?_⟩
      rw [hk0map k1 k0 Dk0, hs', (hT k0 hk0.2).2] at Det
      rw [(hT k0 hk0.2).1]
      simp only [List.cons.injEq] at Det
      obtain ⟨h0, h1, h2⟩ := Det
      rw [h2, ← addKc e0 e, h1, h0, ← addcA, addKc]

end Step

/-! ### Rotation invariance, the main induction, and the main theorem -/

section Main

/-- Rotating the ring by one dart preserves `KempeProp` (the inner induction of Coq's second
"without loss", using `gramRot`). -/
private theorem kempeProp_rot1 {G : Hypermap D} {r : List D} {k : D → Color}
    (h : KempeProp G r k) : KempeProp G (rot 1 r) k := by
  obtain ⟨w, hw, hwr⟩ := h
  refine ⟨gramRot w, ?_, fun et het => ?_⟩
  · rw [map_rot, trace_rot, match_gram_rot]
    exact hw
  · rw [← rotrK 1 et, match_gram_rot] at het
    obtain ⟨k', hk', hdef⟩ := hwr _ het
    exact ⟨k', hk', by rw [map_rot, trace_rot, ← hdef, rotrK]⟩

/-- `KempeProp` is invariant under all rotations of the ring. -/
private theorem kempeProp_rot {G : Hypermap D} {r : List D} {k : D → Color} (h : KempeProp G r k)
    (n : ℕ) : KempeProp G (rot n r) k := by
  induction n with
  | zero => rwa [rot0]
  | succ n ih =>
    rcases lt_or_ge n r.length with hn | hn
    · rw [rotS hn]
      exact kempeProp_rot1 ih
    · rwa [rot_oversize (by omega : r.length ≤ n + 1)]

/-- `KempeProp` for a rotation of the ring implies `KempeProp` for the ring. -/
private theorem kempeProp_of_rot {G : Hypermap D} {r : List D} {k : D → Color} (n : ℕ)
    (h : KempeProp G (rot n r) k) : KempeProp G r k := by
  have : KempeProp G (rotr n (rot n r)) k := kempeProp_rot h _
  rwa [rotK] at this

/-- The main induction of Coq `Kempe_map`, on a bound `n` of the number of darts. -/
private theorem kempe_map_ind (n : ℕ) :
    ∀ {D : Type u} [Fintype D] [DecidableEq D] (G : Hypermap D) (r : List D),
      Fintype.card D < n → G.UCyclePlanarPlainQuasicubic r →
      ∀ k, G.Coloring k → KempeProp G r k := by
  induction n with
  | zero => intro D _ _ G r h; exact absurd h (Nat.not_lt_zero _)
  | succ n IHn =>
    intro D _ _ G r hcard hG k hk
    have hpl := hG.plain
    have hn := coloring_node_ne hk
    have hcycr : fcycle G.node r := hG.ucycle.1
    by_cases hr : r = []
    · subst hr
      refine ⟨[], rfl, fun et het => ⟨k, hk, ?_⟩⟩
      have := matchg_size het
      cases et with
      | nil => rfl
      | cons e et => simp at this
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil r hr
    -- the first "without loss": a dart `z` of `r` given by the Euler tree lemma
    have hJ : G.permN.Jordan := (planar_iff_jordan _).1 ((G.planar_permN).2 hG.planar)
    obtain ⟨z, hxz, hz⟩ := euler_tree G.permN x hJ
    have r_z : z ∈ r := (fconnect_cycle hcycr hx).1 hxz
    have hDfz : G.face z = z ∨ G.face z ∉ r := by
      rcases hz with (hz | hz) | hz
      · exact Or.inl hz.symm
      · exact absurd hz (G.plain_neq hpl z)
      · exact Or.inr fun hm => hz ((fconnect_cycle hcycr r_z).2 hm)
    -- the second "without loss": rotate `r` so that it starts with `z`
    obtain ⟨i, p', hi⟩ := rot_to r_z
    apply kempeProp_of_rot i
    rw [hi]
    have hq : G.UCyclePlanarPlainQuasicubic (z :: p') := by
      rw [← hi]
      exact ⟨⟨⟨hpl, fun y hy => hG.quasicubic fun h' => hy (mem_rot.2 h')⟩,
        (cycle_rot i r).2 hG.ucycle.1, nodup_rot.2 hG.ucycle.2⟩, hG.planar⟩
    have hDfz' : G.face z = z ∨ G.face z ∉ z :: p' := by
      rw [← hi]
      exact hDfz.imp_right fun h' hm => h' (mem_rot.1 hm)
    obtain ⟨nz, p1, rfl⟩ : ∃ nz p1, p' = nz :: p1 := by
      cases p' with
      | nil => exact absurd hq.ucycle.1.1 (hn z)
      | cons nz p1 => exact ⟨nz, p1, rfl⟩
    -- contract the edge `[z; edge z]`, and apply the induction hypothesis
    have hez : G.edge z ≠ z := G.plain_neq hpl z
    have hK : KContract G (G.kH z hez) (G.kh z hez) z :=
      ⟨kh_inj, kh_ne, kh_ne_edge, fun _ h1 h2 => kh_surj h1 h2, kh_edge hpl, kh_node hpl hn⟩
    have IH_H : ∀ r', (G.kH z hez).UCyclePlanarPlainQuasicubic r' →
        ∀ k', (G.kH z hez).Coloring k' → KempeProp (G.kH z hez) r' k' := fun r' hr' k' hk' =>
      IHn (G.kH z hez) r' (by have := card_kH G z hez; omega) hr' k' hk'
    obtain ⟨w, hw, hwr⟩ := hK.kempe_step hpl hk (planar_kH G z hez hG.planar) IH_H
      hq.ucycle.1 hq.ucycle.2 hq.quasicubic hDfz'
    have key : KempeProp G (rotr 1 (z :: nz :: p1)) k := by
      refine ⟨w, ?_, fun et het => ?_⟩
      · rw [← urtrace_trace, ← map_rot, rotrK]
        exact hw
      · obtain ⟨k0, hk0, hdef⟩ := hwr et het
        exact ⟨k0, hk0, by rw [← urtrace_trace, ← map_rot, rotrK]; exact hdef⟩
    have := kempeProp_rot1 key
    rwa [rotrK] at this

/-- Coq `Kempe_map`: the ring traces of a planar plain quasicubic map with a duplicate-free
N-cycle ring `r` are Kempe closed. -/
theorem kempe_map [Fintype D] (G : Hypermap D) (r : List D)
    (hG : G.UCyclePlanarPlainQuasicubic r) : KempeClosed (G.RingTrace r) := by
  classical
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨fun g => ⟨permc g ∘ k, G.coloring_inj (permc_inj g) hk, ?_⟩,
    kempe_map_ind _ G r (Nat.lt_succ_self _) hG k hk⟩
  rw [← List.map_map, ← trace_permt]
  rfl

end Main

end Hypermap

end FourColor
