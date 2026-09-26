/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Layout
import FourColor.Chromogram

/-!
# Reducibility engine: chromograms, non-crossing matchings and Kempe chord flips

A chromogram `w` (for the skip color `Color1`) matched by a trace `t` pairs the non-`Color1`
entries of `t` by a *non-crossing perfect matching* `M` of their ranks (the bracket structure
of `w`), and the traces matching `w` are exactly those obtained from `t` by *flipping*
(`Color2 ↔ Color3` at both ends) any set of chords of `M`.  The engine needs two facts
(`exists_ncm_of_matchg`):

1. the matching of any chromogram matched by `t` is one of the matchings enumerated by
   `ncm (nonOne t) 0 (nonOne t)` (enumeration completeness), and
2. flipping any sub-list of its chords yields a trace that still matches `w` (the orbit of
   the chord flips is contained in the matchers of `w`).

Together with the bit-level description of chord flips (`KempeStep.lean`) this proves that
the bit-parallel Kempe step computes a subset of `Kempe1`.

Definitions:
* `flipNth l t`      : swap `Color2`/`Color3` at the rank-`l` non-`Color1` entry of `t`;
* `flipChord (a, b)` : flip the ranks `a` and `b`; `flipChords S` : flip all chords of `S`;
* `ncm fuel lo n`    : the non-crossing perfect matchings of the ranks `lo … lo+n-1`, each
  as a list of chords `(a, b)`, `a < b`: the first chord `(lo, lo+2j+1)`, then a matching of
  the ranks strictly inside it, then a matching of the ranks after it (`fuel ≥ n`).
  The enumeration order is the one of the continuation-passing fold `ncmFold` of the Kempe
  step, which shares chord prefixes.
-/

namespace FourColor.Engine

open FourColor

/-- Swap `Color2`/`Color3` at the rank-`l` non-`Color1` entry of `t` (ranks from `0`, counted
from the head; no change if `t` has at most `l` non-`Color1` entries). -/
def flipNth : Nat → Colseq → Colseq
  | _, [] => []
  | l, c :: t =>
    match c with
    | Color1 => Color1 :: flipNth l t
    | _ => if l == 0 then permc Eperm132 c :: t else c :: flipNth (l - 1) t

/-- A chord: a pair of ranks `(a, b)` with `a < b`. -/
abbrev Chord := Nat × Nat

/-- Flip both ends of a chord. -/
def flipChord (ab : Chord) (t : Colseq) : Colseq := flipNth ab.1 (flipNth ab.2 t)

/-- Flip all the chords of a list, first chord first. -/
def flipChords (S : List Chord) (t : Colseq) : Colseq := S.foldl (fun t ab => flipChord ab t) t

/-- The non-crossing perfect matchings of the ranks `lo … lo+n-1` (for `fuel ≥ n`): the chord
of the first rank `(lo, lo+2j+1)`, a matching of the ranks inside it, a matching of the ranks
after it.  (For odd `n` there is none.) -/
def ncm : Nat → Nat → Nat → List (List Chord)
  | 0, _, _ => [[]]
  | fuel + 1, lo, n =>
    if n == 0 then [[]] else
    (List.range (n / 2)).flatMap fun j =>
      (ncm fuel (lo + 1) (2 * j)).flatMap fun mi =>
        (ncm fuel (lo + 2 * j + 2) (n - 2 * j - 2)).map fun mo =>
          (lo, lo + 2 * j + 1) :: (mi ++ mo)

/-! ### Specification -/

/-- The chords of an enumerated matching are pairs of ranks `lo ≤ a < b < lo + n`. -/
theorem mem_ncm_chord {fuel lo n : Nat} {M : List Chord} (hM : M ∈ ncm fuel lo n)
    {ab : Chord} (hab : ab ∈ M) : lo ≤ ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < lo + n := by
  induction fuel generalizing lo n M with
  | zero => simp [ncm] at hM; subst hM; simp at hab
  | succ fuel ih =>
    by_cases hn : n = 0
    · subst hn; simp [ncm] at hM; subst hM; simp at hab
    · have hn' : (n == 0) = false := by simpa using hn
      simp only [ncm, hn', Bool.false_eq_true, ite_false, List.mem_flatMap, List.mem_range,
        List.mem_map] at hM
      obtain ⟨j, hj, mi, hmi, mo, hmo, rfl⟩ := hM
      simp only [List.mem_cons, List.mem_append] at hab
      rcases hab with rfl | hab | hab
      · simp; omega
      · have := ih hmi hab; omega
      · have := ih hmo hab; omega

/-- There are non-crossing perfect matchings of an even number of ranks. -/
theorem ncm_ne_nil (fuel lo n : Nat) (hn : n % 2 = 0) : ncm fuel lo n ≠ [] := by
  induction fuel generalizing lo n with
  | zero => simp [ncm]
  | succ fuel ih =>
    by_cases h0 : n = 0
    · subst h0; simp [ncm]
    · have hn' : (n == 0) = false := by simpa using h0
      simp only [ncm, hn', Bool.false_eq_true, ite_false, ne_eq, List.flatMap_eq_nil_iff,
        List.mem_range, not_forall]
      refine ⟨0, by omega, ?_⟩
      simp only [Nat.mul_zero, List.map_eq_nil_iff]
      obtain ⟨mi, hmi⟩ := List.exists_mem_of_ne_nil _ (ih (lo + 1) 0 rfl)
      exact ⟨mi, hmi, ih _ _ (by omega)⟩

/-! ### Helpers: flips of ranks -/

private theorem mt_nonOne_cons (c : Color) (t : Colseq) :
    nonOne (c :: t) = nonOne t + (if c = Color1 then 0 else 1) := by
  simp only [nonOne, List.countP_cons]
  cases c <;> simp

private theorem mt_nonOne_append (t1 t2 : Colseq) :
    nonOne (t1 ++ t2) = nonOne t1 + nonOne t2 := by
  simp [nonOne, List.countP_append]

private theorem mt_flipNth_ne {c : Color} (hc : c ≠ Color1) (l : Nat) (t : Colseq) :
    flipNth l (c :: t) = if l = 0 then permc Eperm132 c :: t else c :: flipNth (l - 1) t := by
  cases c <;> first | exact absurd rfl hc | simp [flipNth]

private theorem mt_length_flipNth (l : Nat) (t : Colseq) : (flipNth l t).length = t.length := by
  induction t generalizing l with
  | nil => rfl
  | cons c t ih => cases c <;> cases l <;> simp [flipNth, ih]

private theorem mt_nonOne_flipNth (l : Nat) (t : Colseq) : nonOne (flipNth l t) = nonOne t := by
  induction t generalizing l with
  | nil => rfl
  | cons c t ih => cases c <;> cases l <;> simp [flipNth, mt_nonOne_cons, ih, permc]

private theorem mt_flipNth_append_lt (t1 t2 : Colseq) (l : Nat) (hl : l < nonOne t1) :
    flipNth l (t1 ++ t2) = flipNth l t1 ++ t2 := by
  induction t1 generalizing l with
  | nil => simp [nonOne] at hl
  | cons c t ih =>
    rw [mt_nonOne_cons] at hl
    cases c <;> rcases l with _ | l <;> simp [flipNth] at hl ⊢ <;> apply ih <;> omega

private theorem mt_flipNth_append_add (t1 t2 : Colseq) (l : Nat) :
    flipNth (l + nonOne t1) (t1 ++ t2) = t1 ++ flipNth l t2 := by
  induction t1 with
  | nil => simp [nonOne]
  | cons c t ih => cases c <;> simp [flipNth, mt_nonOne_cons, ih, ← Nat.add_assoc]

private theorem mt_length_flipChord (ab : Chord) (t : Colseq) :
    (flipChord ab t).length = t.length := by
  simp [flipChord, mt_length_flipNth]

private theorem mt_flipChord_append_lt {t1 t2 : Colseq} {ab : Chord} (h1 : ab.1 < nonOne t1)
    (h2 : ab.2 < nonOne t1) : flipChord ab (t1 ++ t2) = flipChord ab t1 ++ t2 := by
  unfold flipChord
  rw [mt_flipNth_append_lt _ _ _ h2,
    mt_flipNth_append_lt _ _ _ (by rwa [mt_nonOne_flipNth])]

private theorem mt_flipChord_append_add (t1 t2 : Colseq) (a b : Nat) :
    flipChord (a + nonOne t1, b + nonOne t1) (t1 ++ t2) = t1 ++ flipChord (a, b) t2 := by
  unfold flipChord
  rw [mt_flipNth_append_add, mt_flipNth_append_add]

/-! ### Helpers: matching as a stack machine -/

/-- The number of non-`Gskip` symbols of a chromogram. -/
private def nsk : Chromogram → Nat
  | [] => 0
  | Gskip :: w => nsk w
  | _ :: w => nsk w + 1

private theorem nsk_append (w1 w2 : Chromogram) : nsk (w1 ++ w2) = nsk w1 + nsk w2 := by
  induction w1 with
  | nil => simp [nsk]
  | cons s w ih => cases s <;> simp [nsk, ih] <;> omega

/-- One step of `matchg`. -/
private def mstep : List Bool → Color → GramSymbol → Option (List Bool)
  | lb, Color1, Gskip => some lb
  | lb, Color2, Gpush => some (false :: lb)
  | lb, Color3, Gpush => some (true :: lb)
  | false :: lb, Color2, Gpop0 => some lb
  | true :: lb, Color2, Gpop1 => some lb
  | true :: lb, Color3, Gpop0 => some lb
  | false :: lb, Color3, Gpop1 => some lb
  | _, _, _ => none

/-- Run `matchg` on a segment, returning the final stack. -/
private def mrun : List Bool → Colseq → Chromogram → Option (List Bool)
  | lb, [], [] => some lb
  | lb, e :: t, s :: w => (mstep lb e s).bind (fun l => mrun l t w)
  | _, _, _ => none

private theorem matchg_iff_mrun (t : Colseq) :
    ∀ (lb : List Bool) (w : Chromogram), matchg lb t w = true ↔ mrun lb t w = some [] := by
  induction t with
  | nil =>
    intro lb w
    cases w <;> cases lb <;> simp [matchg, mrun]
  | cons e t ih =>
    intro lb w
    cases w with
    | nil => simp [matchg, mrun]
    | cons s w =>
      cases e <;> cases s <;> rcases lb with _ | ⟨_ | _, lb⟩ <;> simp [matchg, mrun, mstep, ih]

private theorem mrun_append (lb : List Bool) (t1 t2 : Colseq) (w1 w2 : Chromogram)
    (h : t1.length = w1.length) :
    mrun lb (t1 ++ t2) (w1 ++ w2) = (mrun lb t1 w1).bind (fun l => mrun l t2 w2) := by
  induction t1 generalizing lb w1 with
  | nil =>
    cases w1 with
    | nil => simp [mrun]
    | cons s w => simp at h
  | cons e t ih =>
    cases w1 with
    | nil => simp at h
    | cons s w =>
      simp only [List.cons_append, mrun]
      cases mstep lb e s with
      | none => rfl
      | some l => exact ih l w (by simpa using h)

private theorem mrun_some (t : Colseq) : ∀ (lb : List Bool) (w : Chromogram) (l : List Bool),
    mrun lb t w = some l → t.length = w.length ∧ nonOne t = nsk w := by
  induction t with
  | nil =>
    intro lb w l h
    cases w with
    | nil => simp [nonOne, nsk]
    | cons s w => simp [mrun] at h
  | cons e t ih =>
    intro lb w l h
    cases w with
    | nil => simp [mrun] at h
    | cons s w =>
      cases e <;> cases s <;> rcases lb with _ | ⟨_ | _, lb⟩ <;>
        simp only [mrun, mstep, Option.bind_some, Option.bind_none, reduceCtorEq] at h <;>
        obtain ⟨h1, h2⟩ := ih _ _ _ h <;> simp [mt_nonOne_cons, nsk, h1, h2]

private theorem mrun_split {lb lb' : List Bool} {t : Colseq} {w1 w2 : Chromogram}
    (h : mrun lb t (w1 ++ w2) = some lb') :
    ∃ t1 t2 l, t = t1 ++ t2 ∧ t1.length = w1.length ∧ mrun lb t1 w1 = some l ∧
      mrun l t2 w2 = some lb' := by
  have hl := (mrun_some _ _ _ _ h).1
  rw [List.length_append] at hl
  rw [← List.take_append_drop w1.length t,
    mrun_append _ _ _ _ _ (by simp; omega), Option.bind_eq_some_iff] at h
  obtain ⟨l, h1, h2⟩ := h
  exact ⟨_, _, l, (List.take_append_drop _ _).symm, by simp; omega, h1, h2⟩

/-- Bracket balance of a chromogram in a context of `d` open chords (parities ignored). -/
private def bal : Nat → Chromogram → Bool
  | d, [] => d == 0
  | d, Gpush :: w => bal (d + 1) w
  | d, Gskip :: w => bal d w
  | 0, Gpop0 :: _ => false
  | d + 1, Gpop0 :: w => bal d w
  | 0, Gpop1 :: _ => false
  | d + 1, Gpop1 :: w => bal d w

private theorem bal_parity (w : Chromogram) : ∀ d, bal d w = true → (nsk w + d) % 2 = 0 := by
  induction w with
  | nil => intro d h; simp [bal] at h; simp [nsk, h]
  | cons s w ih =>
    intro d h
    cases s with
    | Gpush => have := ih _ h; simp [nsk]; omega
    | Gskip => simpa [nsk] using ih _ h
    | Gpop0 =>
      cases d with
      | zero => simp [bal] at h
      | succ d => have := ih _ h; simp [nsk]; omega
    | Gpop1 =>
      cases d with
      | zero => simp [bal] at h
      | succ d => have := ih _ h; simp [nsk]; omega

/-- A balanced segment is run independently of the stack below it. -/
private theorem mrun_bal (w : Chromogram) : ∀ (l1 lb : List Bool) (t : Colseq),
    bal l1.length w = true → mrun (l1 ++ lb) t w = if matchg l1 t w then some lb else none := by
  induction w with
  | nil =>
    intro l1 lb t hb
    have : l1 = [] := by simpa [bal] using hb
    subst this
    cases t <;> simp [mrun, matchg]
  | cons s w ih =>
    intro l1 lb t hb
    cases t with
    | nil => simp [mrun, matchg]
    | cons e t =>
      cases s with
      | Gskip =>
        cases e <;> first | exact ih l1 lb t hb | simp [mrun, mstep, matchg]
      | Gpush =>
        cases e <;>
          first
            | exact ih (false :: l1) lb t hb
            | exact ih (true :: l1) lb t hb
            | simp [mrun, mstep, matchg]
      | Gpop0 =>
        rcases l1 with _ | ⟨_ | _, l1⟩
        · simp [bal] at hb
        all_goals
          cases e <;> first | exact ih l1 lb t hb | simp [mrun, mstep, matchg]
      | Gpop1 =>
        rcases l1 with _ | ⟨_ | _, l1⟩
        · simp [bal] at hb
        all_goals
          cases e <;> first | exact ih l1 lb t hb | simp [mrun, mstep, matchg]

/-- First-return decomposition: the chord open below the context `l1` closes at `p`. -/
private theorem first_return (w : Chromogram) : ∀ (t : Colseq) (l1 : List Bool) (x : Bool)
    (lb : List Bool), matchg (l1 ++ x :: lb) t w = true →
    ∃ w1 p w2 t1 d t2, w = w1 ++ p :: w2 ∧ t = t1 ++ d :: t2 ∧ t1.length = w1.length ∧
      bal l1.length w1 = true ∧ matchg l1 t1 w1 = true ∧
      matchg (x :: lb) (d :: t2) (p :: w2) = true ∧ (p = Gpop0 ∨ p = Gpop1) := by
  induction w with
  | nil =>
    intro t l1 x lb h
    cases t <;> simp [matchg] at h
  | cons s w ih =>
    intro t l1 x lb h
    cases t with
    | nil => simp [matchg] at h
    | cons e t =>
      have ext : ∀ (l1' : List Bool), matchg (l1' ++ x :: lb) t w = true →
          (∀ w1, bal l1.length (s :: w1) = bal l1'.length w1) →
          (∀ t1 w1, matchg l1 (e :: t1) (s :: w1) = matchg l1' t1 w1) →
          ∃ w1 p w2 t1 d t2, s :: w = w1 ++ p :: w2 ∧ e :: t = t1 ++ d :: t2 ∧
            t1.length = w1.length ∧ bal l1.length w1 = true ∧ matchg l1 t1 w1 = true ∧
            matchg (x :: lb) (d :: t2) (p :: w2) = true ∧ (p = Gpop0 ∨ p = Gpop1) := by
        intro l1' h' hb hm
        obtain ⟨w1, p, w2, t1, d, t2, rfl, rfl, hlen, hbal, hm1, hm2, hp⟩ := ih t l1' x lb h'
        exact ⟨s :: w1, p, w2, e :: t1, d, t2, rfl, rfl, by simp [hlen], by rw [hb]; exact hbal,
          by rw [hm]; exact hm1, hm2, hp⟩
      cases s with
      | Gskip =>
        cases e <;> simp only [matchg, Bool.false_eq_true] at h
        exact ext l1 h (fun _ => by simp [bal]) (fun _ _ => by simp [matchg])
      | Gpush =>
        cases e <;> simp only [matchg, Bool.false_eq_true] at h
        · exact ext (false :: l1) h (fun _ => by simp [bal]) (fun _ _ => by simp [matchg])
        · exact ext (true :: l1) h (fun _ => by simp [bal]) (fun _ _ => by simp [matchg])
      | Gpop0 =>
        rcases l1 with _ | ⟨_ | _, l1⟩
        · exact ⟨[], Gpop0, w, [], e, t, rfl, rfl, rfl, rfl, by simp [matchg],
            by simpa using h, Or.inl rfl⟩
        all_goals
          cases e <;> simp only [List.cons_append, matchg, Bool.false_eq_true] at h
          exact ext l1 h (fun _ => by simp [bal]) (fun _ _ => by simp [matchg])
      | Gpop1 =>
        rcases l1 with _ | ⟨_ | _, l1⟩
        · exact ⟨[], Gpop1, w, [], e, t, rfl, rfl, rfl, rfl, by simp [matchg],
            by simpa using h, Or.inr rfl⟩
        all_goals
          cases e <;> simp only [List.cons_append, matchg, Bool.false_eq_true] at h
          exact ext l1 h (fun _ => by simp [bal]) (fun _ _ => by simp [matchg])

/-! ### Helpers: chords whose flip preserves matching -/

/-- Flipping the chord `ab` preserves every run of the segment `w`. -/
private def FlipOK (w : Chromogram) (ab : Chord) : Prop :=
  ab.1 < nsk w ∧ ab.2 < nsk w ∧
    ∀ lb t lb', mrun lb t w = some lb' → mrun lb (flipChord ab t) w = some lb'

private theorem FlipOK_prefix {w1 : Chromogram} {ab : Chord} (w2 : Chromogram)
    (hF : FlipOK w1 ab) : FlipOK (w1 ++ w2) ab := by
  obtain ⟨ha, hb, hF⟩ := hF
  refine ⟨by rw [nsk_append]; omega, by rw [nsk_append]; omega, fun lb t lb' h => ?_⟩
  obtain ⟨t1, t2, l, rfl, hl, h1, h2⟩ := mrun_split h
  have hn := (mrun_some _ _ _ _ h1).2
  rw [mt_flipChord_append_lt (by omega) (by omega),
    mrun_append _ _ _ _ _ (by rw [mt_length_flipChord]; exact hl), hF _ _ _ h1]
  simpa using h2

private theorem FlipOK_suffix (w1 : Chromogram) {w2 : Chromogram} {a b : Nat}
    (hF : FlipOK w2 (a, b)) : FlipOK (w1 ++ w2) (a + nsk w1, b + nsk w1) := by
  obtain ⟨ha, hb, hF⟩ := hF
  refine ⟨by simp only [nsk_append]; omega, by simp only [nsk_append]; omega,
    fun lb t lb' h => ?_⟩
  obtain ⟨t1, t2, l, rfl, hl, h1, h2⟩ := mrun_split h
  have hn := (mrun_some _ _ _ _ h1).2
  rw [← hn, mt_flipChord_append_add, mrun_append _ _ _ _ _ hl, h1]
  simpa using hF _ _ _ h2

private theorem flipChord_first {c d : Color} (hc : c ≠ Color1) (hd : d ≠ Color1)
    (t1 t2 : Colseq) :
    flipChord (0, nonOne t1 + 1) (c :: (t1 ++ d :: t2)) =
      permc Eperm132 c :: (t1 ++ permc Eperm132 d :: t2) := by
  unfold flipChord
  simp only
  rw [mt_flipNth_ne hc]
  simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel]
  rw [show nonOne t1 = 0 + nonOne t1 by simp, mt_flipNth_append_add, mt_flipNth_ne hd,
    mt_flipNth_ne hc]
  simp

private theorem FlipOK_base {w1 w2 : Chromogram} {p : GramSymbol} (hb : bal 0 w1 = true)
    (hp : p = Gpop0 ∨ p = Gpop1) : FlipOK (Gpush :: (w1 ++ p :: w2)) (0, nsk w1 + 1) := by
  have hn : nsk (Gpush :: (w1 ++ p :: w2)) = nsk w1 + nsk w2 + 2 := by
    rcases hp with rfl | rfl <;> simp [nsk, nsk_append] <;> omega
  refine ⟨by simp only [hn]; omega, by simp only [hn]; omega, fun lb t lb' h => ?_⟩
  rcases t with _ | ⟨c, t⟩
  · simp [mrun] at h
  obtain ⟨x, hx, hx', hc⟩ : ∃ x, mstep lb c Gpush = some (x :: lb) ∧
      mstep lb (permc Eperm132 c) Gpush = some ((!x) :: lb) ∧ c ≠ Color1 := by
    cases c
    · simp [mrun, mstep] at h
    · simp [mrun, mstep] at h
    · exact ⟨false, rfl, rfl, by decide⟩
    · exact ⟨true, rfl, rfl, by decide⟩
  simp only [mrun, hx, Option.bind_some] at h
  obtain ⟨t1, t2, l, rfl, hl, h1, h2⟩ := mrun_split h
  have hm := mrun_bal w1 [] (x :: lb) t1 hb
  have hm' := mrun_bal w1 [] ((!x) :: lb) t1 hb
  simp only [List.nil_append] at hm hm'
  have hmt : matchg [] t1 w1 = true := by
    cases hmg : matchg [] t1 w1
    · rw [hm, hmg] at h1; simp at h1
    · rfl
  simp only [hm, hmt, ite_true, Option.some.injEq] at h1
  subst h1
  simp only [hmt, ite_true] at hm'
  have hn1 : nonOne t1 = nsk w1 := (mrun_some _ _ _ _ hm').2
  rcases t2 with _ | ⟨d, t3⟩
  · simp [mrun] at h2
  simp only [mrun, Option.bind_eq_some_iff] at h2
  obtain ⟨l2, hs, h3⟩ := h2
  have hd : d ≠ Color1 := by
    rintro rfl; rcases hp with rfl | rfl <;> simp [mstep] at hs
  have hs' : mstep ((!x) :: lb) (permc Eperm132 d) p = some l2 := by
    rcases hp with rfl | rfl <;> cases x <;> cases d <;> exact hs
  rw [← hn1, flipChord_first hc hd]
  simp only [mrun, hx', Option.bind_some]
  rw [mrun_append _ _ _ _ _ hl, hm']
  simp only [Option.bind_some, mrun, hs']
  exact h3

private theorem nil_mem_ncm (fuel lo : Nat) : [] ∈ ncm fuel lo 0 := by
  cases fuel <;> simp [ncm]

private theorem exists_aux (N : Nat) : ∀ (w : Chromogram) (t : Colseq), w.length < N →
    matchg [] t w = true → ∀ fuel lo, nonOne t ≤ fuel →
    ∃ M ∈ ncm fuel lo (nonOne t), ∀ ab ∈ M, FlipOK w (ab.1 - lo, ab.2 - lo) := by
  induction N with
  | zero => intro w t hw; simp at hw
  | succ N ih =>
    intro w t hw h fuel lo hf
    rcases w with _ | ⟨s, w⟩
    · rcases t with _ | ⟨e, t⟩
      · exact ⟨[], nil_mem_ncm _ _, by simp⟩
      · simp [matchg] at h
    rcases t with _ | ⟨e, t⟩
    · simp [matchg] at h
    simp only [List.length_cons] at hw
    cases s with
    | Gskip =>
      cases e <;> simp only [matchg, Bool.false_eq_true] at h
      simp only [mt_nonOne_cons, ite_true, Nat.add_zero] at hf ⊢
      obtain ⟨M, hM, hF⟩ := ih w t (by omega) h fuel lo hf
      refine ⟨M, hM, fun ab hab => ?_⟩
      simpa [nsk] using FlipOK_suffix [Gskip] (hF ab hab)
    | Gpop0 => cases e <;> simp [matchg] at h
    | Gpop1 => cases e <;> simp [matchg] at h
    | Gpush =>
      obtain ⟨x, hx, hc⟩ : ∃ x, matchg [x] t w = true ∧ e ≠ Color1 := by
        cases e <;> simp only [matchg, Bool.false_eq_true] at h
        · exact ⟨false, h, by decide⟩
        · exact ⟨true, h, by decide⟩
      obtain ⟨w1, p, w2, t1, d, t2, rfl, rfl, hlen, hbal, hm1, hm2, hp⟩ :=
        first_return w t [] x [] hx
      simp only [List.length_nil] at hbal
      have hm2' : matchg [] t2 w2 = true ∧ d ≠ Color1 := by
        rcases hp with rfl | rfl <;> cases x <;> cases d <;>
          simp only [matchg, Bool.false_eq_true] at hm2 <;> exact ⟨hm2, by decide⟩
      obtain ⟨hm2, hd⟩ := hm2'
      have hn1 : nonOne t1 = nsk w1 := (mrun_some _ _ _ _ ((matchg_iff_mrun _ _ _).1 hm1)).2
      have hpar := bal_parity w1 0 hbal
      obtain ⟨j, hj⟩ : ∃ j, nsk w1 = 2 * j := ⟨nsk w1 / 2, by omega⟩
      have hn : nonOne (e :: (t1 ++ d :: t2)) = 2 * j + nonOne t2 + 2 := by
        simp only [mt_nonOne_cons, mt_nonOne_append, hc, hd, ite_false]; omega
      rw [hn] at hf ⊢
      obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [List.length_append, List.length_cons] at hw
      obtain ⟨mi, hmi, hFi⟩ := ih w1 t1 (by omega) hm1 fuel (lo + 1) (by omega)
      obtain ⟨mo, hmo, hFo⟩ := ih w2 t2 (by omega) hm2 fuel (lo + 2 * j + 2) (by omega)
      rw [hn1, hj] at hmi
      refine ⟨(lo, lo + 2 * j + 1) :: (mi ++ mo), ?_, ?_⟩
      · have hne : (2 * j + nonOne t2 + 2 == 0) = false := by simp
        simp only [ncm, hne, Bool.false_eq_true, ite_false, List.mem_flatMap, List.mem_range,
          List.mem_map]
        refine ⟨j, by omega, mi, hmi, mo, ?_, rfl⟩
        rwa [show 2 * j + nonOne t2 + 2 - 2 * j - 2 = nonOne t2 by omega]
      · rintro ⟨a, b⟩ hab
        simp only [List.mem_cons, List.mem_append] at hab
        rcases hab with hab | hab | hab
        · simp only [Prod.mk.injEq] at hab
          obtain ⟨rfl, rfl⟩ := hab
          have e : ((a, a + 2 * j + 1) : Chord).1 - a = 0 ∧
              ((a, a + 2 * j + 1) : Chord).2 - a = nsk w1 + 1 := by simp; omega
          rw [e.1, e.2]
          exact FlipOK_base hbal hp
        · have hr := mem_ncm_chord hmi hab
          have := FlipOK_suffix [Gpush] (FlipOK_prefix (p :: w2) (hFi _ hab))
          simp only [nsk] at this
          rwa [show a - (lo + 1) + 1 = a - lo by omega,
            show b - (lo + 1) + 1 = b - lo by omega] at this
        · have hr := mem_ncm_chord hmo hab
          have := FlipOK_suffix (Gpush :: (w1 ++ [p])) (hFo _ hab)
          have hk : nsk (Gpush :: (w1 ++ [p])) = 2 * j + 2 := by
            rcases hp with rfl | rfl <;> simp [nsk, nsk_append, hj]
          rw [hk, show a - (lo + 2 * j + 2) + (2 * j + 2) = a - lo by omega,
            show b - (lo + 2 * j + 2) + (2 * j + 2) = b - lo by omega] at this
          simpa using this

/-! ### Helpers: codes and sums of flipped traces -/

private theorem mt_div2 (a : Nat) (b : Bool) : (2 * a + b.toNat) / 2 = a := by
  cases b <;> simp; omega

private theorem mt_mod2 (a : Nat) (b : Bool) : ((2 * a + b.toNat) % 2 = 1) = (b = true) := by
  cases b <;> simp

private theorem mt_xor_bits (a c : Nat) (b e : Bool) :
    (2 * a + b.toNat) ^^^ (2 * c + e.toNat) = 2 * (a ^^^ c) + (b ^^ e).toNat := by
  apply Nat.eq_of_testBit_eq; intro i
  rcases i with _ | i
  · rw [Nat.testBit_xor]; simp only [Nat.testBit_zero, mt_mod2]; cases b <;> cases e <;> rfl
  · rw [Nat.testBit_xor, Nat.testBit_succ, Nat.testBit_succ, Nat.testBit_succ, mt_div2, mt_div2,
      mt_div2, Nat.testBit_xor]

private theorem mt_color0_flipNth (l : Nat) {t : Colseq} (h0 : Color0 ∉ t) :
    Color0 ∉ flipNth l t := by
  induction t generalizing l with
  | nil => simp [flipNth]
  | cons c t ih =>
    have h0' : Color0 ∉ t := fun h => h0 (List.mem_cons_of_mem _ h)
    have hc : c ≠ Color0 := fun h => h0 (h ▸ List.mem_cons_self)
    cases c <;> rcases l with _ | l <;> simp_all [flipNth, permc]

private theorem mt_sumt_flipNth {l : Nat} {t : Colseq} (hl : l < nonOne t) (h0 : Color0 ∉ t) :
    sumt (flipNth l t) = addc Color1 (sumt t) := by
  induction t generalizing l with
  | nil => simp [nonOne] at hl
  | cons c t ih =>
    have h0' : Color0 ∉ t := fun h => h0 (List.mem_cons_of_mem _ h)
    have hc : c ≠ Color0 := fun h => h0 (h ▸ List.mem_cons_self)
    rw [mt_nonOne_cons] at hl
    have e : ∀ c', sumt (c' :: t) = addc c' (sumt t) := fun _ => rfl
    cases c with
    | Color0 => exact absurd rfl hc
    | Color1 =>
      simp only [ite_true, Nat.add_zero] at hl
      show addc Color1 (sumt (flipNth l t)) = _
      rw [ih hl h0', e]
    | Color2 =>
      rcases l with _ | l
      · show addc Color3 (sumt t) = _
        rw [e]; generalize sumt t = x; cases x <;> rfl
      · show addc Color2 (sumt (flipNth l t)) = _
        rw [ih (by simp at hl; omega) h0', e]; generalize sumt t = x; cases x <;> rfl
    | Color3 =>
      rcases l with _ | l
      · show addc Color2 (sumt t) = _
        rw [e]; generalize sumt t = x; cases x <;> rfl
      · show addc Color3 (sumt (flipNth l t)) = _
        rw [ih (by simp at hl; omega) h0', e]; generalize sumt t = x; cases x <;> rfl

/-- **Kempe orbits of chromograms.**  If `t` matches the chromogram `w`, the bracket matching
of `w` is enumerated by `ncm`, and flipping any sub-list of its chords gives a trace that
still matches `w`. -/
theorem exists_ncm_of_matchg {t : Colseq} {w : Chromogram} (h : matchg [] t w = true) :
    ∃ M ∈ ncm (nonOne t) 0 (nonOne t),
      ∀ S : List Chord, S.Sublist M → matchg [] (flipChords S t) w = true := by
  obtain ⟨M, hM, hF⟩ := exists_aux (w.length + 1) w t (by omega) h (nonOne t) 0 le_rfl
  refine ⟨M, hM, fun S hS => ?_⟩
  have key : ∀ S : List Chord, (∀ ab ∈ S, FlipOK w ab) →
      ∀ t', matchg [] t' w = true → matchg [] (flipChords S t') w = true := by
    intro S
    induction S with
    | nil => intro _ t' h'; exact h'
    | cons ab S ih =>
      intro hS t' h'
      refine ih (fun ab' h'' => hS ab' (List.mem_cons_of_mem _ h'')) _ ?_
      rw [matchg_iff_mrun] at h' ⊢
      exact (hS ab List.mem_cons_self).2.2 _ _ _ h'
  exact key S (fun ab hab => by simpa using hF ab (hS.subset hab)) t h

/-- Flipping a rank does not change the block of a trace. -/
theorem nonOne_flipNth (l : Nat) (t : Colseq) : nonOne (flipNth l t) = nonOne t :=
  mt_nonOne_flipNth l t

/-- Flipping a rank does not change the block of a trace. -/
theorem blockRank_flipNth (l m : Nat) (t : Colseq) :
    blockRank (flipNth l t) m = blockRank t m := by
  induction t generalizing l m with
  | nil => rfl
  | cons c t ih =>
    cases c <;> rcases l with _ | l <;> simp [flipNth, blockRank, permc, ih, mt_length_flipNth]

/-- Flipping an existing rank toggles its bit in the unpacked code. -/
theorem xcode_flipNth {l : Nat} {t : Colseq} (hl : l < nonOne t) (h0 : Color0 ∉ t) :
    xcode (flipNth l t) = xcode t ^^^ 2 ^ l := by
  induction t generalizing l with
  | nil => simp [nonOne] at hl
  | cons c t ih =>
    have h0' : Color0 ∉ t := fun h => h0 (List.mem_cons_of_mem _ h)
    have hc : c ≠ Color0 := fun h => h0 (h ▸ List.mem_cons_self)
    rw [mt_nonOne_cons] at hl
    have p0 : (2 : Nat) ^ 0 = 2 * 0 + true.toNat := rfl
    have ps : ∀ l : Nat, (2 : Nat) ^ (l + 1) = 2 * 2 ^ l + false.toNat := fun l => by
      simp [Nat.pow_succ, Nat.mul_comm]
    cases c with
    | Color0 => exact absurd rfl hc
    | Color1 =>
      simp only [ite_true, Nat.add_zero] at hl
      exact ih hl h0'
    | Color2 =>
      rcases l with _ | l
      · show 2 * xcode t + 1 = 2 * xcode t ^^^ 2 ^ 0
        rw [p0, show 2 * xcode t = 2 * xcode t + false.toNat from rfl, mt_xor_bits]; simp
      · show 2 * xcode (flipNth l t) = 2 * xcode t ^^^ 2 ^ (l + 1)
        rw [ih (by simp at hl; omega) h0', ps,
          show 2 * xcode t = 2 * xcode t + false.toNat from rfl, mt_xor_bits]; rfl
    | Color3 =>
      rcases l with _ | l
      · show 2 * xcode t = (2 * xcode t + 1) ^^^ 2 ^ 0
        rw [p0, show 2 * xcode t + 1 = 2 * xcode t + true.toNat from rfl, mt_xor_bits]; simp
      · show 2 * xcode (flipNth l t) + 1 = (2 * xcode t + 1) ^^^ 2 ^ (l + 1)
        rw [ih (by simp at hl; omega) h0', ps,
          show 2 * xcode t + 1 = 2 * xcode t + true.toNat from rfl, mt_xor_bits]; rfl

/-- Flipping both ends of a chord of distinct existing ranks preserves validity. -/
theorem validTrace_flipChord {r a b : Nat} {t : Colseq} (h : ValidTrace r t) (hab : a < b)
    (hb : b < nonOne t) : ValidTrace r (flipChord (a, b) t) := by
  obtain ⟨hlen, h0, hs⟩ := h
  unfold flipChord
  have h0' := mt_color0_flipNth b h0
  refine ⟨by simp [mt_length_flipNth, hlen], mt_color0_flipNth a h0', ?_⟩
  rw [mt_sumt_flipNth (by rw [mt_nonOne_flipNth]; omega) h0', mt_sumt_flipNth hb h0, hs]
  rfl

end FourColor.Engine
