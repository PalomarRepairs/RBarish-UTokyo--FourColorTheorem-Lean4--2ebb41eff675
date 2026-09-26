/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Round

/-!
# Reducibility engine: the Birkhoff check (replacement of `birkhoff.v`'s `Birkhoff_check2`)

`birkhoff.v` proves that a minimal counter-example has no nontrivial rings of size `≤ 5`
with a small computation, `Birkhoff_check2`, run on `ctree`/`gtree` pairs through
`Kempe_tree_closure`.  The new engine replaces it by the same game on trace sets in the packed
layout, reusing the engine's sound operations (`roundsN`), so that no `ctree`/`gtree` code has
to be ported.

Two sides (the inside and the outside of a ring of size `r`) keep sound sets `X1`, `X2`: the
traces known to be in the Kempe co-closure of `P1` (resp. `P2`), where `Pi t` means "`t` is not
a ring trace of side `i`".  The reversal `rv` maps the traces of one side to those of the other
(a network with `NetSpec r rv rvf`, `rvf` an involution).  A step picks the first trace `t`
with `t ∉ X1` and `rv t ∉ X2`; since the map is not colorable, `P1 t` or `P2 (rv t)` holds
(`hglue`), and both cases are explored:
* case 1 adds `t` to `X1` and closes it by `fuel` rounds; it succeeds if some basis coloring
  set is covered by the new `X1`, or recursively with the sides exchanged;
* case 2 adds `rv t` to `X2`, and continues in the same way.
The check fails when no trace can be picked or after `n` levels.  Soundness (`bk2_false`): if
both sides' sets are sound, each side has a Kempe-closed set of ring traces (`hR1`, `hR2`)
meeting every basis coloring set (`hb1`, `hb2`), and `hglue` holds, the check is `false`;
hence a successful check refutes the existence of the ring.
-/

namespace FourColor.Engine

open FourColor

/-- The lowest set bit of `x` (as a singleton set), `0` if `x = 0`. -/
def lowBit (x : Nat) : Nat := x ^^^ (x &&& (x - 1))

/-- Some basis coloring set is covered by `X`. -/
def coveredAny (basis : List (List Nat)) (X : List Nat) : Bool := basis.any fun B => covered B X

/-- The Birkhoff game (see the module documentation): ring size `r`, `τ12` network `tau`,
reversal network `rv`, basis coloring sets `basis`, `fuel` rounds per closure, `n` levels. -/
def bk2 (r : Nat) (tau rv : Net) (basis : List (List Nat)) (fuel : Nat) :
    Nat → List Nat → List Nat → Bool
  | 0, _, _ => false
  | n + 1, X1, X2 =>
    let full := fullMask r
    let S := (full ^^^ catG r X1) &&& applyNet rv (full ^^^ catG r X2)
    if Nat.beq S 0 then false else
    let e := lowBit S
    let X1' := roundsN r tau fuel (splitG r (catG r X1 ||| e))
    let X2' := roundsN r tau fuel (splitG r (catG r X2 ||| (applyNet rv e &&& full)))
    (coveredAny basis X1' || bk2 r tau rv basis fuel n X2 X1') &&
      (coveredAny basis X2' || bk2 r tau rv basis fuel n X1 X2')

/-- The empty trace set. -/
def emptySet (r : Nat) : List Nat := List.replicate (ngrades r) 0

/-- The Birkhoff check for ring size `r`: the game from empty sets. -/
def birkhoffCheck (r : Nat) (tau rv : Net) (basis : List (List Nat)) (fuel n : Nat) : Bool :=
  bk2 r tau rv basis fuel n (emptySet r) (emptySet r)

/-! ### Specification -/

/-! ### Proof helpers -/

private theorem exists_two_pow_mul_odd (x : Nat) (hx : x ≠ 0) :
    ∃ i c, x = 2 ^ i * (2 * c + 1) := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · obtain ⟨i, c, hc⟩ := ih (x / 2) (by omega) (by omega)
      refine ⟨i + 1, c, ?_⟩
      have e : x = 2 * (x / 2) := by omega
      rw [e, hc, Nat.pow_succ]
      ring
    · exact ⟨0, x / 2, by omega⟩

/-- `lowBit x` is the singleton of a set bit of `x`. -/
private theorem lowBit_spec {x : Nat} (hx : x ≠ 0) :
    ∃ i, lowBit x = 2 ^ i ∧ x.testBit i = true := by
  obtain ⟨i, c, rfl⟩ := exists_two_pow_mul_odd x hx
  have hx1 : 2 ^ i * (2 * c + 1) = 2 ^ (i + 1) * c + 2 ^ i := by rw [Nat.pow_succ]; ring
  have hp : 0 < 2 ^ i := Nat.two_pow_pos i
  have hx2 : 2 ^ i * (2 * c + 1) - 1 = 2 ^ (i + 1) * c + (2 ^ i - 1) := by rw [hx1]; omega
  have hlt1 : 2 ^ i < 2 ^ (i + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hlt2 : 2 ^ i - 1 < 2 ^ (i + 1) := by omega
  have hlt0 : 0 < 2 ^ (i + 1) := Nat.two_pow_pos _
  have hand : 2 ^ i * (2 * c + 1) &&& (2 ^ i * (2 * c + 1) - 1) = 2 ^ (i + 1) * c + 0 := by
    rw [hx2, hx1]
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_land, Nat.testBit_two_pow_mul_add _ hlt1, Nat.testBit_two_pow_mul_add _ hlt2,
      Nat.testBit_two_pow_mul_add _ hlt0]
    by_cases hj : j < i + 1
    · simp only [hj, ite_true, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one, Nat.zero_testBit]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    · simp [hj]
  refine ⟨i, ?_, ?_⟩
  · unfold lowBit
    rw [hand, hx1]
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ hlt1, Nat.testBit_two_pow_mul_add _ hlt0]
    by_cases hj : j < i + 1
    · simp [hj]
    · have : ¬ i = j := by omega
      simp [hj, this]
  · rw [hx1, Nat.testBit_two_pow_mul_add _ hlt1]
    simp

private theorem gsize_eq_zero {r k : Nat} (hk : ngrades r ≤ k) : gsize r k = 0 := by
  unfold gsize ngrades at *
  rw [ite_eq_right (by simp; omega), chooseAux_eq, Nat.choose_eq_zero_of_lt (by omega)]
  simp

private theorem goff_le_gtotal (r : Nat) : ∀ n, goff r n ≤ gtotal r := by
  have mono : ∀ a b, goff r a ≤ goff r (a + b) := by
    intro a b
    induction b with
    | zero => exact Nat.le_refl _
    | succ b ih => show goff r a ≤ goff r (a + b) + gsize r (a + b); omega
  have stable : ∀ j, goff r (ngrades r + j) = gtotal r := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      show goff r (ngrades r + j) + gsize r (ngrades r + j) = gtotal r
      rw [ih, gsize_eq_zero (by omega)]; rfl
  intro n
  by_cases h : n ≤ ngrades r
  · obtain ⟨b, hb⟩ := Nat.exists_eq_add_of_le h
    have := mono n b
    rw [← hb] at this; exact this
  · obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_le h)
    rw [stable]

private theorem testBit_catGAux_lt (r : Nat) : ∀ (X : List Nat) (k i : Nat),
    (catGAux r k (goff r k) X).testBit i = true → i < gtotal r := by
  intro X
  induction X with
  | nil => intro k i h; simp [catGAux] at h
  | cons q qs ih =>
    intro k i h
    simp only [catGAux, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_land,
      testBit_ones, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨h1, _, h2⟩ | h
    · have := goff_le_gtotal r (k + 1)
      have e : goff r (k + 1) = goff r k + gsize r k := rfl
      omega
    · exact ih (k + 1) i h

/-- The concatenated layout has no bit above `gtotal r`. -/
private theorem testBit_catG_lt {r : Nat} {X : List Nat} {i : Nat}
    (h : (catG r X).testBit i = true) : i < gtotal r :=
  testBit_catGAux_lt r X 0 i h

private theorem den_splitG_iff {r x : Nat} {t : Colseq} (ht : ValidTrace r t) :
    den r (splitG r x) t ↔ x.testBit (cpos r t) = true := by
  unfold den; rw [testBit_splitG ht]; exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩

private theorem testBit_catG_iff {r : Nat} {X : List Nat} {t : Colseq} (ht : ValidTrace r t) :
    (catG r X).testBit (cpos r t) = true ↔ den r X t := by
  unfold den; rw [testBit_catG ht]; exact ⟨fun h => ⟨ht, h⟩, fun h => h.2⟩

/-- A sound set extended by a trace of `P` is sound. -/
private theorem soundFor_add {r : Nat} {P : Colseq → Prop} {X : List Nat} {t : Colseq}
    (ht : ValidTrace r t) (hP : P t) (hX : SoundFor P (den r X)) :
    SoundFor P (den r (splitG r (catG r X ||| 2 ^ cpos r t))) := by
  intro s hs
  have hsv := hs.1
  rw [den_splitG_iff hsv, Nat.testBit_or, Bool.or_eq_true, testBit_catG_iff hsv,
    Nat.testBit_two_pow] at hs
  rcases hs with hs | hs
  · exact hX s hs
  · have := cpos_inj ht hsv (of_decide_eq_true hs)
    subst this
    exact kempeCoclosure_of_mem hP

/-- A sound set extended by the reversal of a trace is sound. -/
private theorem soundFor_add_rv {r : Nat} {rv : Net} {rvf : Colseq → Colseq}
    (hrv : NetSpec r rv rvf) (hrvv : ∀ t, ValidTrace r t → ValidTrace r (rvf t))
    (hrvi : ∀ t, ValidTrace r t → rvf (rvf t) = t) {P : Colseq → Prop} {X : List Nat}
    {t : Colseq} (ht : ValidTrace r t) (hP : P (rvf t)) (hX : SoundFor P (den r X)) :
    SoundFor P (den r (splitG r (catG r X ||| (applyNet rv (2 ^ cpos r t) &&& fullMask r)))) := by
  intro s hs
  have hsv := hs.1
  rw [den_splitG_iff hsv, Nat.testBit_or, Bool.or_eq_true, testBit_catG_iff hsv,
    Nat.testBit_land, hrv s hsv, Nat.testBit_two_pow, Bool.and_eq_true] at hs
  rcases hs with hs | hs
  · exact hX s hs
  · have e := cpos_inj ht (hrvv s hsv) (of_decide_eq_true hs.1)
    have : s = rvf t := by rw [e, hrvi s hsv]
    subst this
    exact kempeCoclosure_of_mem hP

/-- A sound set covers no basis coloring set when the basis colorings are not in `P`. -/
private theorem coveredAny_false {r : Nat} {basis : List (List Nat)} {P : Colseq → Prop}
    {X : List Nat} (hR : KempeClosed fun t => ¬ P t) (hb : ∀ B ∈ basis, ∃ t, den r B t ∧ ¬ P t)
    (hX : SoundFor P (den r X)) : coveredAny basis X = false := by
  unfold coveredAny
  rw [List.any_eq_false]
  intro B hB hc
  obtain ⟨t, htB, hnP⟩ := hb B hB
  exact hnP (hX.sub_of_closed hR (den_of_covered hc htB))

/-- **Soundness of the Birkhoff game.** -/
theorem bk2_false {r : Nat} {tau rv : Net} (htau : TauSpec r tau) {rvf : Colseq → Colseq}
    (hrv : NetSpec r rv rvf) (hrvv : ∀ t, ValidTrace r t → ValidTrace r (rvf t))
    (hrvi : ∀ t, ValidTrace r t → rvf (rvf t) = t)
    {basis : List (List Nat)} {fuel : Nat} (P1 P2 : Colseq → Prop)
    (hR1 : KempeClosed fun t => ¬ P1 t) (hR2 : KempeClosed fun t => ¬ P2 t)
    (hglue : ∀ t, ValidTrace r t → P1 t ∨ P2 (rvf t))
    (hb1 : ∀ B ∈ basis, ∃ t, den r B t ∧ ¬ P1 t) (hb2 : ∀ B ∈ basis, ∃ t, den r B t ∧ ¬ P2 t)
    (n : Nat) (X1 X2 : List Nat) (hX1 : SoundFor P1 (den r X1)) (hX2 : SoundFor P2 (den r X2)) :
    bk2 r tau rv basis fuel n X1 X2 = false := by
  induction n generalizing P1 P2 X1 X2 with
  | zero => rfl
  | succ n ih =>
    simp only [bk2]
    split
    · rfl
    · rename_i hS
      simp only [Nat.beq_eq] at hS
      obtain ⟨i, he, hi⟩ := lowBit_spec hS
      rw [he]
      rw [Nat.testBit_land, Bool.and_eq_true, Nat.testBit_xor] at hi
      have hig : i < gtotal r := by
        by_contra hig
        have h1 : (fullMask r).testBit i = false := by
          unfold fullMask; rw [testBit_ones]; simpa using hig
        have h2 : (catG r X1).testBit i = false := by
          cases hc : (catG r X1).testBit i
          · rfl
          · exact absurd (testBit_catG_lt hc) hig
        rw [h1, h2] at hi
        simp at hi
      obtain ⟨t, ht, rfl⟩ := exists_cpos hig
      have hglue' : ∀ t, ValidTrace r t → P2 t ∨ P1 (rvf t) := by
        intro t ht
        rcases hglue (rvf t) (hrvv t ht) with h | h
        · exact Or.inr h
        · rw [hrvi t ht] at h; exact Or.inl h
      rcases hglue t ht with h1 | h2
      · have hX1' := roundsN_sound htau fuel (soundFor_add ht h1 hX1)
        rw [coveredAny_false hR1 hb1 hX1', ih P2 P1 hR2 hR1 hglue' hb2 hb1 X2 _ hX2 hX1']
        rfl
      · have hX2' := roundsN_sound htau fuel (soundFor_add_rv hrv hrvv hrvi ht h2 hX2)
        rw [coveredAny_false hR2 hb2 hX2', ih P1 P2 hR1 hR2 hglue hb1 hb2 X1 _ hX1 hX2']
        simp

/-- The empty set is sound. -/
theorem soundFor_emptySet (r : Nat) (P : Colseq → Prop) : SoundFor P (den r (emptySet r)) := by
  intro t ht
  exfalso
  have := ht.2
  simp [emptySet] at this

end FourColor.Engine
