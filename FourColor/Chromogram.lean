/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Color

/-!
# Chromograms  (port of `chromogram.v`)

Chromograms are words representing congruence classes of regions with respect to Kempe
inversions for a single edge color and color permutation.  The relevant topological
information for each class consists of a set of non-intersecting chords linking perimeter
edges, and the parity of the number of links for each chord.  The word representation of these
chords is a Dyck word augmented with spaces (for perimeter edges that are not linked because
they are colored with the inversion color) and parities (on closing brackets), each chord being
represented with a matching bracket pair.

* `Chromogram` : `List GramSymbol` (Coq `chromogram`), with each `GramSymbol` one of
  - `Gskip` : no chord (edge has `Color1`);
  - `Gpush` : chord start (edge has `Color2` or `Color3`);
  - `Gpop0` : odd chord end (end edge has the same color as start);
  - `Gpop1` : even chord end (start and end have different colors).

For `w : Chromogram`, `lb : List Bool`, `b : Bool` and `et : Colseq`, we define

* `matchg lb et w`       : `et` is a valid edge coloring trace that matches `w` in a context
  where there are `length lb` open chords (started but not ended) whose corresponding edge
  color parities are `lb.reverse` (i.e., if `lb` is `false :: _`, then the start of the last
  open chord had edge `Color2`).
* `gramBalanced d b w`   : `w` is balanced in a context with `d` open chords and has parity
  `b` (i.e., matches colorings with parity `b`) (Coq `gram_balanced`).
* `KempeClosed P`        : `P : Colseq → Prop` is closed under permutations and Kempe flips:
  if `P et` then `et` matches some chromogram `w` in the empty context, such that `P` holds
  for all edge colorings that are permutations of `et` or that match `w` (Coq
  `Kempe_closed`).
* `KempeCoclosure P et`  : `P` meets all `KempeClosed` predicates that hold for `et` (Coq
  `Kempe_coclosure`).

Being a ring trace in a planar plain cubic map is `KempeClosed`; the relation between
chromograms and graphs is developed in `kempe.v`.

As for edge color traces, we also use partial chromograms, with the last (redundant) symbol
removed, in addition to complete ones.  This is the form actually used for the correctness
proof of the reducibility check.

* `cgram d b w`          : the complete chromogram corresponding to `w`, i.e., `w` with its
  last symbol restored, in the context of a chromogram prefix with `d` open chords and parity
  `b`.
* `BitStack`             : a simple datatype equivalent to `List Bool`, with constructors
  `Bstack0`, `Bpush0` and `Bpush1` (Coq `bit_stack`); `bitseqOfStack` and `stackOfBitseq`
  convert between the two representations.
* `matchpg bs et w`      : the chromogram completion of `w` matches the trace completion of
  `et`, in the context of a prefix where the colors matching the start of open chords have
  parities `(bitseqOfStack bs).reverse`, respectively.

## Porting notes

* The computational predicates `gramBalanced`, `matchg` and `matchpg` are `Bool`-valued and
  structurally recursive, with the same case structure as the Coq fixpoints; `KempeClosed`
  and `KempeCoclosure` are `Prop`s.
* The Coq section-local `sumb` (the sum of a bit sequence) is a private definition.
-/

namespace FourColor

/-- Coq `gram_symbol`: the symbols of chromograms. -/
inductive GramSymbol : Type where
  /-- Chord start: the edge has `Color2` or `Color3` (Coq `Gpush`). -/
  | Gpush
  /-- No chord: the edge has `Color1` (Coq `Gskip`). -/
  | Gskip
  /-- Odd chord end: the end edge has the same color as the start (Coq `Gpop0`). -/
  | Gpop0
  /-- Even chord end: the start and end edges have different colors (Coq `Gpop1`). -/
  | Gpop1
  deriving Repr, Inhabited

export GramSymbol (Gpush Gskip Gpop0 Gpop1)

/-- Coq `eqgs`: comparison of chromogram symbols. -/
def eqgs (s1 s2 : GramSymbol) : Bool :=
  match s1, s2 with
  | Gpush, Gpush => true
  | Gskip, Gskip => true
  | Gpop0, Gpop0 => true
  | Gpop1, Gpop1 => true
  | _, _ => false

/-- Coq `eqgsP`: `eqgs` reflects equality. -/
theorem eqgsP {s1 s2 : GramSymbol} : eqgs s1 s2 = true ↔ s1 = s2 := by
  cases s1 <;> cases s2 <;> simp [eqgs]

/-- The decidable equality of chromogram symbols, computed with `eqgs` (Coq
`hasDecEq.Build gram_symbol eqgsP`). -/
instance : DecidableEq GramSymbol := fun _ _ => decidable_of_iff _ eqgsP

/-- Coq `chromogram`: sequences of chromogram symbols. -/
abbrev Chromogram := List GramSymbol

/-- Coq `gram_balanced d b0 w`: `w` is balanced in a context with `d` open chords, and has
parity `b0`. -/
def gramBalanced (d : ℕ) (b0 : Bool) (w : Chromogram) : Bool :=
  match w, d with
  | [], 0 => !b0
  | Gpush :: w', _ => gramBalanced (d + 1) b0 w'
  | Gskip :: w', _ => gramBalanced d (!b0) w'
  | Gpop0 :: w', d' + 1 => gramBalanced d' b0 w'
  | Gpop1 :: w', d' + 1 => gramBalanced d' (!b0) w'
  | _, _ => false

/-- Coq `matchg lb et w`: the trace `et` matches the chromogram `w`, in a context with
`length lb` open chords whose starting edge colors have parities `lb.reverse`. -/
def matchg (lb : List Bool) (et : Colseq) (w : Chromogram) : Bool :=
  match w, et, lb with
  | [], [], [] => true
  | s :: w', e :: et', _ =>
    match e, s, lb with
    | Color1, Gskip, _ => matchg lb et' w'
    | Color2, Gpush, _ => matchg (false :: lb) et' w'
    | Color2, Gpop0, false :: lb' => matchg lb' et' w'
    | Color2, Gpop1, true :: lb' => matchg lb' et' w'
    | Color3, Gpush, _ => matchg (true :: lb) et' w'
    | Color3, Gpop0, true :: lb' => matchg lb' et' w'
    | Color3, Gpop1, false :: lb' => matchg lb' et' w'
    | _, _, _ => false
  | _, _, _ => false

/-- Coq `Kempe_closed P`: `P` is closed under edge color permutations and Kempe flips. -/
def KempeClosed (P : Colseq → Prop) : Prop :=
  ∀ et, P et →
    (∀ g : EdgePerm, P (permt g et)) ∧
      ∃ w, matchg [] et w = true ∧ ∀ et', matchg [] et' w = true → P et'

/-- Coq `Kempe_coclosure P et`: `P` meets every Kempe-closed predicate that holds for `et`. -/
def KempeCoclosure (P : Colseq → Prop) (et : Colseq) : Prop :=
  ∀ P' : Colseq → Prop, KempeClosed P' → P' et → ∃ et', P et' ∧ P' et'

/-- Coq `matchg_size`. -/
theorem matchg_size {et : Colseq} {lb : List Bool} {w : Chromogram}
    (h : matchg lb et w = true) : w.length = et.length := by
  induction et generalizing lb w with
  | nil =>
    cases w with
    | nil => rfl
    | cons s w => exact absurd h (by simp [matchg])
  | cons e et ih =>
    cases w with
    | nil => exact absurd h (by simp [matchg])
    | cons s w =>
      rw [List.length_cons, List.length_cons, Nat.add_right_cancel_iff]
      cases e <;> cases s <;> rcases lb with _ | ⟨_ | _, lb⟩ <;>
        simp only [matchg, Bool.false_eq_true] at h <;> exact ih h

/-- Coq `matchg_memc0`. -/
theorem matchg_memc0 {et : Colseq} {lb : List Bool} {w : Chromogram}
    (h : matchg lb et w = true) : Color0 ∉ et := by
  induction et generalizing lb w with
  | nil => exact List.not_mem_nil
  | cons e et ih =>
    cases w with
    | nil => exact absurd h (by simp [matchg])
    | cons s w =>
      rw [List.mem_cons, not_or]
      cases e <;> cases s <;> rcases lb with _ | ⟨_ | _, lb⟩ <;>
        simp only [matchg, Bool.false_eq_true] at h <;> exact ⟨by decide, ih h⟩

section BalanceLemmas

/-- Coq section-local `sumb`: the sum (xor) of a bit sequence. -/
private def sumb : List Bool → Bool := List.foldr xor false

private theorem sumb_nil : sumb [] = false := rfl

private theorem sumb_cons (b : Bool) (lb : List Bool) : sumb (b :: lb) = (b ^^ sumb lb) := rfl

/-- The parity of a natural number, as a boolean (math-comp `odd`). -/
private def oddb : ℕ → Bool
  | 0 => false
  | n + 1 => !oddb n

private theorem oddb_succ (n : ℕ) : oddb (n + 1) = !oddb n := rfl

set_option hygiene false in
/-- The final step of the balance lemmas: normalise the bits and decide the boolean identity
between the induction hypothesis (`h1`, `h2`) and the goal. -/
local macro "bal_tac" : tactic => `(tactic| (
  simp only [List.length_cons, oddb_succ, sumb_cons, sumt_cons, cbit1_addc, cbit0_addc,
    gramBalanced, cbit0_Color1, cbit0_Color2, cbit0_Color3, cbit1_Color1, cbit1_Color2,
    cbit1_Color3] at h1 h2 ⊢
  revert h1 h2
  generalize oddb lb.length = o
  generalize cbit1 (sumt et) = x1
  generalize sumb lb = sb
  generalize cbit0 (sumt et) = x0
  cases o <;> cases x1 <;> cases sb <;> cases x0 <;> simp))

private theorem matchg_balanced_aux (et : Colseq) : ∀ (lb : List Bool) (w : Chromogram),
    matchg lb et w = true →
      (oddb lb.length ^^ cbit1 (sumt et)) = false ∧
        gramBalanced lb.length (sumb lb ^^ cbit0 (sumt et)) w = true := by
  induction et with
  | nil =>
    intro lb w h
    cases w with
    | nil =>
      cases lb with
      | nil => exact ⟨rfl, rfl⟩
      | cons b lb => exact absurd h (by simp [matchg])
    | cons s w => exact absurd h (by simp [matchg])
  | cons e et ih =>
    intro lb w h
    cases w with
    | nil => exact absurd h (by simp [matchg])
    | cons s w =>
      cases s with
      | Gpush =>
        cases e with
        | Color2 =>
          obtain ⟨h1, h2⟩ := ih (false :: lb) w h
          bal_tac
        | Color3 =>
          obtain ⟨h1, h2⟩ := ih (true :: lb) w h
          bal_tac
        | _ => simp [matchg] at h
      | Gskip =>
        cases e with
        | Color1 =>
          obtain ⟨h1, h2⟩ := ih lb w h
          bal_tac
        | _ => simp [matchg] at h
      | Gpop0 =>
        rcases lb with _ | ⟨_ | _, lb⟩ <;> cases e <;> simp only [matchg, Bool.false_eq_true] at h
        all_goals
          obtain ⟨h1, h2⟩ := ih lb w h
          bal_tac
      | Gpop1 =>
        rcases lb with _ | ⟨_ | _, lb⟩ <;> cases e <;> simp only [matchg, Bool.false_eq_true] at h
        all_goals
          obtain ⟨h1, h2⟩ := ih lb w h
          bal_tac

/-- Coq `matchg_balanced`: a trace matching a chromogram in the empty context has a sum with
`cbit1` unset, and the chromogram is balanced with the parity of `cbit0` of the sum. -/
theorem matchg_balanced {et : Colseq} {w : Chromogram} (h : matchg [] et w = true) :
    cbit1 (sumt et) = false ∧ gramBalanced 0 (cbit0 (sumt et)) w = true := by
  obtain ⟨h1, h2⟩ := matchg_balanced_aux et [] w h
  exact ⟨by simpa [oddb] using h1, by simpa [sumb] using h2⟩

/-- Coq `balanced_inj`: the context and the parity of a balanced chromogram are unique. -/
theorem balanced_inj {w : Chromogram} {n1 n2 : ℕ} {b1 b2 : Bool}
    (h1 : gramBalanced n1 b1 w = true) (h2 : gramBalanced n2 b2 w = true) :
    n1 = n2 ∧ b1 = b2 := by
  induction w generalizing n1 n2 b1 b2 with
  | nil =>
    cases n1 <;> cases n2 <;> cases b1 <;> cases b2 <;>
      first
        | exact ⟨rfl, rfl⟩
        | exact absurd h1 Bool.false_ne_true
        | exact absurd h2 Bool.false_ne_true
  | cons s w ih =>
    cases s with
    | Gpush =>
      obtain ⟨h, h'⟩ := ih (n1 := n1 + 1) (n2 := n2 + 1) h1 h2
      exact ⟨by omega, h'⟩
    | Gskip =>
      obtain ⟨h, h'⟩ := ih (b1 := !b1) (b2 := !b2) h1 h2
      exact ⟨h, by simpa using h'⟩
    | Gpop0 =>
      cases n1 with
      | zero => exact absurd h1 Bool.false_ne_true
      | succ n1 =>
        cases n2 with
        | zero => exact absurd h2 Bool.false_ne_true
        | succ n2 =>
          obtain ⟨h, h'⟩ := ih (n1 := n1) (n2 := n2) h1 h2
          exact ⟨by omega, h'⟩
    | Gpop1 =>
      cases n1 with
      | zero => exact absurd h1 Bool.false_ne_true
      | succ n1 =>
        cases n2 with
        | zero => exact absurd h2 Bool.false_ne_true
        | succ n2 =>
          obtain ⟨h, h'⟩ := ih (n1 := n1) (n2 := n2) (b1 := !b1) (b2 := !b2) h1 h2
          exact ⟨by omega, by simpa using h'⟩

/-- Coq `balanced_sumt0`. -/
theorem balanced_sumt0 {w : Chromogram} {et : Colseq} (hb : gramBalanced 0 false w = true)
    (hm : matchg [] et w = true) : sumt et = Color0 := by
  obtain ⟨h1, h0⟩ := matchg_balanced hm
  obtain ⟨-, h2⟩ := balanced_inj h0 hb
  rw [← ccons_cbits (sumt et), h1, h2]
  rfl

private theorem matchg_permt132 (et : Colseq) : ∀ (lb : List Bool) (w : Chromogram),
    matchg (lb.map not) (permt Eperm132 et) w = matchg lb et w := by
  induction et with
  | nil => intro lb w; cases w <;> cases lb <;> rfl
  | cons e et ih =>
    intro lb w
    cases w with
    | nil => rfl
    | cons s w =>
      cases s with
      | Gpush => cases e <;> first | rfl | exact ih (false :: lb) w | exact ih (true :: lb) w
      | Gskip => cases e <;> first | rfl | exact ih lb w
      | Gpop0 => rcases lb with _ | ⟨_ | _, lb⟩ <;> cases e <;> first | rfl | exact ih lb w
      | Gpop1 => rcases lb with _ | ⟨_ | _, lb⟩ <;> cases e <;> first | rfl | exact ih lb w

/-- Coq `match_etrace`: matching is invariant under the even normalization of traces. -/
theorem match_etrace (et : Colseq) (w : Chromogram) :
    matchg [] (etrace et) w = matchg [] et w := by
  unfold etrace etracePerm
  cases evenTrace et
  · exact matchg_permt132 et [] w
  · rw [ite_eq_left rfl, permt_id]

/-! Algorithmic predicates, for chromogram paths. -/

/-- Coq `bit_stack`: a datatype equivalent to `List Bool` (stacks of open chord parities). -/
inductive BitStack : Type where
  /-- The empty stack (Coq `Bstack0`). -/
  | Bstack0
  /-- Push a `false` bit (Coq `Bpush0`). -/
  | Bpush0 (bs : BitStack)
  /-- Push a `true` bit (Coq `Bpush1`). -/
  | Bpush1 (bs : BitStack)
  deriving DecidableEq, Repr, Inhabited

export BitStack (Bstack0 Bpush0 Bpush1)

/-- Coq `bitseq_of_stack`: the bit sequence of a bit stack. -/
def bitseqOfStack : BitStack → List Bool
  | Bstack0 => []
  | Bpush0 bs' => false :: bitseqOfStack bs'
  | Bpush1 bs' => true :: bitseqOfStack bs'

/-- Coq `stack_of_bitseq`: the bit stack of a bit sequence. -/
def stackOfBitseq : List Bool → BitStack :=
  List.foldr (fun b => if b then Bpush1 else Bpush0) Bstack0

/-- `bitseqOfStack` cancels `stackOfBitseq` (not in the Coq file). -/
theorem bitseqOfStack_stackOfBitseq (lb : List Bool) : bitseqOfStack (stackOfBitseq lb) = lb := by
  induction lb with
  | nil => rfl
  | cons b lb ih => cases b <;> exact congrArg _ ih

/-- `stackOfBitseq` cancels `bitseqOfStack` (not in the Coq file). -/
theorem stackOfBitseq_bitseqOfStack (bs : BitStack) : stackOfBitseq (bitseqOfStack bs) = bs := by
  induction bs with
  | Bstack0 => rfl
  | Bpush0 bs ih => exact congrArg Bpush0 ih
  | Bpush1 bs ih => exact congrArg Bpush1 ih

/-- Coq `cgram d b0 w`: the completion of the partial chromogram `w` with its last symbol, in
the context of a prefix with `d` open chords and parity `b0`. -/
def cgram (d : ℕ) (b0 : Bool) (w : Chromogram) : Chromogram :=
  match w with
  | [] =>
    [match d with
      | 0 => Gskip
      | _ + 1 => if b0 then Gpop1 else Gpop0]
  | s :: w' =>
    s :: match s with
      | Gpush => cgram (d + 1) b0 w'
      | Gskip => cgram d (!b0) w'
      | Gpop0 => cgram (d - 1) b0 w'
      | Gpop1 => cgram (d - 1) (!b0) w'

/-- Coq `matchpg bs et w`: the chromogram completion of `w` matches the trace completion of
`et`, in the context of open chords whose starting edge colors have parities
`(bitseqOfStack bs).reverse`. -/
def matchpg (bs : BitStack) (et : Colseq) (w : Chromogram) : Bool :=
  match w, et with
  | [], [] => true
  | s :: w', e :: et' =>
    match e, s, bs with
    | Color1, Gskip, _ => matchpg bs et' w'
    | Color2, Gpush, _ => matchpg (Bpush0 bs) et' w'
    | Color2, Gpop0, Bpush0 bs' => matchpg bs' et' w'
    | Color2, Gpop1, Bpush1 bs' => matchpg bs' et' w'
    | Color3, Gpop0, Bpush1 bs' => matchpg bs' et' w'
    | Color3, Gpush, _ => matchpg (Bpush1 bs) et' w'
    | Color3, Gpop1, Bpush0 bs' => matchpg bs' et' w'
    | _, _, _ => false
  | _, _ => false

private theorem length_cgram (d : ℕ) (b0 : Bool) (w : Chromogram) :
    (cgram d b0 w).length = w.length + 1 := by
  induction w generalizing d b0 with
  | nil => rfl
  | cons s w ih => cases s <;> simp [cgram, ih]

private theorem balanced_cgram (w : Chromogram) : ∀ (s : GramSymbol) (d : ℕ) (b0 : Bool),
    gramBalanced d b0 (s :: w) = true → s :: w = cgram d b0 ((s :: w).take w.length) := by
  induction w with
  | nil =>
    intro s d b0 h
    cases s <;> rcases d with _ | _ | d <;> cases b0 <;>
      first
        | rfl
        | exact absurd h Bool.false_ne_true
  | cons s' w ih =>
    intro s d b0 h
    rw [List.length_cons, List.take_succ_cons]
    cases s with
    | Gpush => exact congrArg (Gpush :: ·) (ih s' (d + 1) b0 h)
    | Gskip => exact congrArg (Gskip :: ·) (ih s' d (!b0) h)
    | Gpop0 =>
      cases d with
      | zero => exact absurd h Bool.false_ne_true
      | succ d => exact congrArg (Gpop0 :: ·) (ih s' d b0 h)
    | Gpop1 =>
      cases d with
      | zero => exact absurd h Bool.false_ne_true
      | succ d => exact congrArg (Gpop1 :: ·) (ih s' d (!b0) h)

/-- Coq `matchg_cgram`: a chromogram matching a completed trace is the completion of its
prefix. -/
theorem matchg_cgram {cw : Chromogram} {et : Colseq} (h : matchg [] (ctrace et) cw = true) :
    cw = cgram 0 false (cw.take (cw.length - 1)) := by
  have hb := (matchg_balanced h).2
  rw [sumt_ctrace] at hb
  cases cw with
  | nil =>
    have := matchg_size h
    simp [ctrace] at this
  | cons s w =>
    rw [List.length_cons, Nat.add_sub_cancel]
    exact balanced_cgram w s 0 false hb

set_option hygiene false in
/-- The color bookkeeping step of `matchg_pg_aux`. -/
local macro "pg_color_tac" : tactic => `(tactic| (
  rw [hc, sumt_cons, addcA]
  congr 1
  try simp only [List.length_cons, oddb_succ, sumb_cons]
  generalize oddb lb.length = o
  generalize sumb lb = sb
  cases o <;> cases b <;> cases sb <;> rfl))

private theorem matchg_pg_aux (et : Colseq) :
    ∀ (lb : List Bool) (b : Bool) (w : Chromogram) (c : Color),
      c = addc (ccons (oddb lb.length) (b ^^ sumb lb)) (sumt et) →
      gramBalanced lb.length b (cgram lb.length b w) = true →
      matchg lb (et ++ [c]) (cgram lb.length b w) = matchpg (stackOfBitseq lb) et w := by
  induction et with
  | nil =>
    intro lb b w c hc hb
    cases w with
    | nil =>
      subst hc
      rcases lb with _ | ⟨x, _ | ⟨y, lb⟩⟩
      · cases b
        · exact absurd hb Bool.false_ne_true
        · rfl
      · cases x <;> cases b <;> rfl
      · cases b <;> exact absurd hb Bool.false_ne_true
    | cons s w =>
      rw [show matchpg (stackOfBitseq lb) [] (s :: w) = false from rfl]
      apply Bool.eq_false_iff.2
      intro h
      have := matchg_size h
      simp [length_cgram] at this
  | cons e et ih =>
    intro lb b w c hc hb
    cases w with
    | nil =>
      rw [show matchpg (stackOfBitseq lb) (e :: et) [] = false from rfl]
      apply Bool.eq_false_iff.2
      intro h
      have := matchg_size h
      simp [length_cgram] at this
    | cons s w =>
      cases s with
      | Gpush =>
        cases e with
        | Color2 => exact ih (false :: lb) b w c (by pg_color_tac) hb
        | Color3 => exact ih (true :: lb) b w c (by pg_color_tac) hb
        | _ => rfl
      | Gskip =>
        cases e with
        | Color1 => exact ih lb (!b) w c (by pg_color_tac) hb
        | _ => rfl
      | Gpop0 =>
        rcases lb with _ | ⟨_ | _, lb⟩ <;> cases e <;>
          first
            | rfl
            | exact ih lb b w c (by pg_color_tac) hb
      | Gpop1 =>
        rcases lb with _ | ⟨_ | _, lb⟩ <;> cases e <;>
          first
            | rfl
            | exact ih lb (!b) w c (by pg_color_tac) hb

/-- Coq `matchg_pg`: for a balanced completed chromogram, matching the completed trace is
decided by `matchpg` on the partial trace and partial chromogram. -/
theorem matchg_pg (et : Colseq) {w : Chromogram}
    (hb : gramBalanced 0 false (cgram 0 false w) = true) :
    matchg [] (ctrace et) (cgram 0 false w) = matchpg Bstack0 et w :=
  matchg_pg_aux et [] false w (sumt et) rfl hb

private theorem matchpg_permt132 (et : Colseq) : ∀ (lb : List Bool) (w : Chromogram),
    matchpg (stackOfBitseq (lb.map not)) (permt Eperm132 et) w =
      matchpg (stackOfBitseq lb) et w := by
  induction et with
  | nil => intro lb w; cases w <;> rfl
  | cons e et ih =>
    intro lb w
    cases w with
    | nil => rfl
    | cons s w =>
      cases s with
      | Gpush => cases e <;> first | rfl | exact ih (false :: lb) w | exact ih (true :: lb) w
      | Gskip => cases e <;> first | rfl | exact ih lb w
      | Gpop0 => rcases lb with _ | ⟨_ | _, lb⟩ <;> cases e <;> first | rfl | exact ih lb w
      | Gpop1 => rcases lb with _ | ⟨_ | _, lb⟩ <;> cases e <;> first | rfl | exact ih lb w

/-- Coq `matchpg_etrace`. -/
theorem matchpg_etrace (et : Colseq) (w : Chromogram) :
    matchpg Bstack0 (etrace et) w = matchpg Bstack0 et w := by
  unfold etrace etracePerm
  cases evenTrace et
  · exact matchpg_permt132 et [] w
  · rw [ite_eq_left rfl, permt_id]

/-- Coq `matchpg_size`. -/
theorem matchpg_size {et : Colseq} {bs : BitStack} {w : Chromogram}
    (h : matchpg bs et w = true) : w.length = et.length := by
  induction et generalizing bs w with
  | nil =>
    cases w with
    | nil => rfl
    | cons s w => exact absurd h (by simp [matchpg])
  | cons e et ih =>
    cases w with
    | nil => exact absurd h (by simp [matchpg])
    | cons s w =>
      rw [List.length_cons, List.length_cons, Nat.add_right_cancel_iff]
      cases e <;> cases s <;> rcases bs with _ | bs | bs <;>
        simp only [matchpg, Bool.false_eq_true] at h <;> exact ih h

/-- Coq `matchpg_flip`: `matchpg Bstack0` is invariant under swapping `Color2` and
`Color3`. -/
theorem matchpg_flip (et : Colseq) (w : Chromogram) :
    matchpg Bstack0 (permt Eperm132 et) w = matchpg Bstack0 et w :=
  matchpg_permt132 et [] w

end BalanceLemmas

end FourColor
