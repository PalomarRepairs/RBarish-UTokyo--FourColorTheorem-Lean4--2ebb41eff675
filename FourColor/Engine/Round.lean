/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.KempeStep
import FourColor.Engine.Network

/-!
# Reducibility engine: rounds, checkpoints and coverage

One *round* of the engine maps a trace set `X` (packed layout, list of grades) to the
permutation closure of its Kempe step:

`round X = K ∪ τ12 (K ∪ τ23 (τ12 K))` with `K = kempeStep X`,

which is the closure of `K` under the six color permutations when `K` is `τ23`-closed (as the
Kempe step always is).  Every round is sound (`round_sound`); no fixpoint is ever computed:
the engine iterates rounds from the coloring traces `P` until the contract traces `C` are
covered.

## Checkpoints

The kernel's memory grows with the work done in a declaration, so long computations are cut
into declarations `roundsN r τ n (expand r Hᵢ) = expand r Hᵢ₊₁` between *checkpoints* `Hᵢ`,
big-number literals computed at elaboration time.  A checkpoint stores only the low half
(rows `xp < 2^(2k-2)`) of each grade `k ≥ 1`: the high half is its `Color2 ↔ Color3` image
(`expand`).  `ReachN` chains the checkpoint equations; its soundness is `ReachN.sound`.
-/

namespace FourColor.Engine

open FourColor

/-- The closure of a `τ23`-closed trace set under the color permutations:
`K ∪ τ12 (K ∪ τ23 (τ12 K))` (with `τ12 = net`). -/
def permCloseK (r : Nat) (tau : Net) (K : List Nat) : List Nat :=
  let x := catG r K
  let a := applyNet tau x
  let a23 := catG r (tau23 r (splitG r a))
  let b := applyNet tau (x ||| a23)
  splitG r (x ||| b)

/-- One round of the engine: Kempe step, then permutation closure. -/
def round (r : Nat) (tau : Net) (X : List Nat) : List Nat := permCloseK r tau (kempeStep r X)

/-- `n` rounds. -/
def roundsN (r : Nat) (tau : Net) : Nat → List Nat → List Nat
  | 0, X => X
  | n + 1, X => roundsN r tau n (round r tau X)

/-- Expansion of a checkpoint: each grade is completed with its `Color2 ↔ Color3` image. -/
def expand (r : Nat) (H : List Nat) : List Nat :=
  mapGrades (fun k h => h ||| tau23Grade r k h) H

/-- `covered C X`: every grade of `C` is contained in the corresponding grade of `X`
(missing grades are empty). -/
def covered : List Nat → List Nat → Bool
  | [], _ => true
  | c :: cs, [] => Nat.beq c 0 && covered cs []
  | c :: cs, g :: gs => Nat.beq (c &&& g) c && covered cs gs

/-- A chain of rounds between two trace sets, proved piecewise (one declaration per piece). -/
inductive ReachN (r : Nat) (tau : Net) : List Nat → List Nat → Prop
  /-- No round. -/
  | refl (X : List Nat) : ReachN r tau X X
  /-- `n` rounds, then a chain. -/
  | step {X Z : List Nat} (n : Nat) (h : ReachN r tau (roundsN r tau n X) Z) : ReachN r tau X Z

/-! ### Specification -/

/-! ### Proof helpers -/

private theorem validTrace_permt {r : Nat} (g : EdgePerm) {t : Colseq} (h : ValidTrace r t) :
    ValidTrace r (permt g t) :=
  ⟨by simp [permt, h.1], by rw [memc0_permt]; exact h.2.1, by rw [sumt_permt, h.2.2, permc0]⟩

private theorem permt_213_132_213 (t : Colseq) :
    permt Eperm213 (permt Eperm132 (permt Eperm213 t)) = permt Eperm321 t := by
  simp only [permt, List.map_map]
  apply List.map_congr_left
  intro c _
  cases c <;> rfl

/-- Reading a trace in a split layout. -/
private theorem den_splitG_iff {r x : Nat} {t : Colseq} (ht : ValidTrace r t) :
    den r (splitG r x) t ↔ x.testBit (cpos r t) = true := by
  unfold den; rw [testBit_splitG ht]; exact ⟨fun h => h.2, fun h => ⟨ht, h⟩⟩

/-- Reading a trace in a concatenated layout. -/
private theorem testBit_catG_iff {r : Nat} {X : List Nat} {t : Colseq} (ht : ValidTrace r t) :
    (catG r X).testBit (cpos r t) = true ↔ den r X t := by
  unfold den; rw [testBit_catG ht]; exact ⟨fun h => ⟨ht, h⟩, fun h => h.2⟩

/-- The permutation closure only adds color permutations of its argument. -/
theorem permCloseK_den {r : Nat} {tau : Net} (htau : TauSpec r tau) {K : List Nat}
    {t : Colseq} (h : den r (permCloseK r tau K) t) : ∃ g : EdgePerm, den r K (permt g t) := by
  have ht := h.1
  unfold permCloseK at h
  simp only at h
  rw [den_splitG_iff ht, Nat.testBit_or, Bool.or_eq_true] at h
  rcases h with h | h
  · exact ⟨Eperm123, by rw [permt_id]; exact (testBit_catG_iff ht).1 h⟩
  · have ht1 := validTrace_permt Eperm213 ht
    rw [htau t ht, Nat.testBit_or, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨Eperm213, (testBit_catG_iff ht1).1 h⟩
    · rw [testBit_catG_iff ht1, den_tau23, den_splitG_iff (validTrace_permt Eperm132 ht1),
        htau _ (validTrace_permt Eperm132 ht1), permt_213_132_213] at h
      exact ⟨Eperm321, (testBit_catG_iff (validTrace_permt Eperm321 ht)).1 h⟩

/-- **Soundness of a round**, for any `P`. -/
theorem round_sound {r : Nat} {tau : Net} (htau : TauSpec r tau) {P : Colseq → Prop}
    {X : List Nat} (hX : SoundFor P (den r X)) : SoundFor P (den r (round r tau X)) := by
  apply hX.step
  intro t ht
  obtain ⟨g, hg⟩ := permCloseK_den htau ht
  exact ⟨g, kempeStep_sound hg⟩

/-- Soundness of `n` rounds. -/
theorem roundsN_sound {r : Nat} {tau : Net} (htau : TauSpec r tau) {P : Colseq → Prop}
    (n : Nat) {X : List Nat} (hX : SoundFor P (den r X)) :
    SoundFor P (den r (roundsN r tau n X)) := by
  induction n generalizing X with
  | zero => exact hX
  | succ n ih => exact ih (round_sound htau hX)

/-- Soundness of a chain of rounds. -/
theorem ReachN.sound {r : Nat} {tau : Net} (htau : TauSpec r tau) {P : Colseq → Prop}
    {X Y : List Nat} (h : ReachN r tau X Y) (hX : SoundFor P (den r X)) :
    SoundFor P (den r Y) := by
  induction h with
  | refl => exact hX
  | step n _ ih => exact ih (roundsN_sound htau n hX)

/-- A checkpoint equation gives a chain. -/
theorem reachN_of_eq {r : Nat} {tau : Net} {n : Nat} {X Y : List Nat}
    (h : roundsN r tau n X = Y) : ReachN r tau X Y := by
  subst h
  exact ReachN.step n (ReachN.refl _)

/-- Chains compose. -/
theorem ReachN.trans {r : Nat} {tau : Net} {X Y Z : List Nat} (h1 : ReachN r tau X Y)
    (h2 : ReachN r tau Y Z) : ReachN r tau X Z := by
  induction h1 with
  | refl => exact h2
  | step n _ ih => exact ReachN.step n (ih h2)

/-- The expansion of a checkpoint only adds `Color2 ↔ Color3` images. -/
theorem den_expand {r : Nat} {H : List Nat} {t : Colseq} (h : den r (expand r H) t) :
    den r H t ∨ den r H (permt Eperm132 t) := by
  obtain ⟨ht, hb⟩ := h
  unfold expand at hb
  rw [getD_mapGrades _ (fun k => by rw [tau23Grade_zero]; rfl) H, Nat.testBit_or,
    Bool.or_eq_true] at hb
  rcases hb with hb | hb
  · exact Or.inl ⟨ht, hb⟩
  · refine Or.inr (den_tau23.1 ⟨ht, ?_⟩)
    unfold tau23
    rw [getD_mapGrades _ (tau23Grade_zero r) H]
    exact hb

/-- Soundness of the expansion of a checkpoint. -/
theorem expand_sound {r : Nat} {P : Colseq → Prop} {H : List Nat}
    (hH : SoundFor P (den r H)) : SoundFor P (den r (expand r H)) := by
  intro t ht
  rcases den_expand ht with h | h
  · exact hH t h
  · exact kempeCoclosure_of_permt Eperm132 (hH _ h)

/-- Coverage, grade by grade. -/
theorem covered_getD {C X : List Nat} (h : covered C X = true) (k i : Nat)
    (hc : (C.getD k 0).testBit i = true) : (X.getD k 0).testBit i = true := by
  induction C generalizing X k with
  | nil => simp at hc
  | cons c cs ih =>
    cases X with
    | nil =>
      simp only [covered, Bool.and_eq_true, Nat.beq_eq] at h
      cases k with
      | zero => simp [h.1] at hc
      | succ k => exact ih h.2 k (by simpa using hc)
    | cons g gs =>
      simp only [covered, Bool.and_eq_true, Nat.beq_eq] at h
      cases k with
      | zero =>
        simp only [List.getD_cons_zero] at hc ⊢
        have := congrArg (fun n => n.testBit i) h.1
        simp only [Nat.testBit_land, hc, Bool.true_and] at this
        exact this
      | succ k => simpa using ih h.2 k (by simpa using hc)

/-- Coverage. -/
theorem den_of_covered {r : Nat} {C X : List Nat} (h : covered C X = true) {t : Colseq}
    (ht : den r C t) : den r X t :=
  ⟨ht.1, covered_getD h _ _ ht.2⟩

end FourColor.Engine
