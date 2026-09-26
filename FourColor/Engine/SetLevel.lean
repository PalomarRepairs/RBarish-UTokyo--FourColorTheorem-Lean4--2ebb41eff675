/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Chromogram

/-!
# Reducibility engine, set level: Kempe steps and the Kempe co-closure

The reducibility engine (overview in `FourColor/Engine.lean`) computes, for a configuration with
coloring
traces `Col`, an increasing sequence of trace sets `X₀ ⊆ X₁ ⊆ …`, starting from `X₀ = Col`,
each step taking the permutation closure of a *Kempe step* `Kempe1 Xᵢ`:

* `Kempe1 X t`   : every chromogram (for the skip color `Color1`) matched by `t` is also
  matched by some trace of `X`.  Since `t` matches `w` exactly when `t` is in the orbit of
  the chord flips of `w`, this is the one-step closure of `X` under Kempe switches of the
  colors `Color2`/`Color3`.
* `SoundFor P X` : every trace of `X` is in the Kempe co-closure of `P` (Coq
  `Kempe_coclosure`).

The engine only needs *soundness*: every set it computes satisfies `SoundFor P`, where `P` is
the set of ring traces of the configuration.  Soundness is preserved by all the operations:
membership in `P` (`soundFor_of_sub`), color permutations (`kempeCoclosure_permt`), unions,
and `Kempe1` (`kempeCoclosure_kempe1`).  No completeness (fixpoint) property is ever needed;
in particular the engine stops as soon as the contract traces are covered.

Nothing here is a port of a Coq lemma; the notions are those of `chromogram.v`.
-/

namespace FourColor.Engine

open FourColor

/-- One Kempe step for the skip color `Color1`: `t` is in `Kempe1 X` when every chromogram `w`
matched by `t` (in the empty context) is matched by some trace of `X`. -/
def Kempe1 (X : Colseq → Prop) (t : Colseq) : Prop :=
  ∀ w, matchg [] t w = true → ∃ s, X s ∧ matchg [] s w = true

/-- `SoundFor P X`: every trace of `X` is in the Kempe co-closure of `P`. -/
def SoundFor (P X : Colseq → Prop) : Prop := ∀ t, X t → KempeCoclosure P t

/-- `Kempe1` contains its argument. -/
theorem kempe1_self {X : Colseq → Prop} {t : Colseq} (h : X t) : Kempe1 X t :=
  fun _ hw => ⟨t, h, hw⟩

/-- `Kempe1` is monotone. -/
theorem kempe1_mono {X Y : Colseq → Prop} (hXY : ∀ t, X t → Y t) {t : Colseq}
    (h : Kempe1 X t) : Kempe1 Y t := fun w hw =>
  let ⟨s, hs, hsw⟩ := h w hw
  ⟨s, hXY s hs, hsw⟩

/-- The traces of `P` are in the Kempe co-closure of `P`. -/
theorem kempeCoclosure_of_mem {P : Colseq → Prop} {t : Colseq} (h : P t) :
    KempeCoclosure P t := fun _ _ hP' => ⟨t, h, hP'⟩

/-- The Kempe co-closure is monotone in `P`. -/
theorem kempeCoclosure_mono {P Q : Colseq → Prop} (hPQ : ∀ t, P t → Q t) {t : Colseq}
    (h : KempeCoclosure P t) : KempeCoclosure Q t := fun P' hP' ht =>
  let ⟨s, hs, hs'⟩ := h P' hP' ht
  ⟨s, hPQ s hs, hs'⟩

/-- The Kempe co-closure is closed under color permutations (one direction). -/
theorem kempeCoclosure_of_permt {P : Colseq → Prop} (g : EdgePerm) {t : Colseq}
    (h : KempeCoclosure P (permt g t)) : KempeCoclosure P t := fun P' hP' ht =>
  h P' hP' ((hP' t ht).1 g)

/-- The Kempe co-closure is closed under color permutations. -/
theorem kempeCoclosure_permt {P : Colseq → Prop} (g : EdgePerm) {t : Colseq} :
    KempeCoclosure P (permt g t) ↔ KempeCoclosure P t := by
  refine ⟨kempeCoclosure_of_permt g, fun h => ?_⟩
  apply kempeCoclosure_of_permt (invEperm g)
  rwa [permt_inv]

/-- The Kempe co-closure absorbs one Kempe step: if all the traces of `X` are in the
co-closure of `P`, so are those of `Kempe1 X`. -/
theorem kempeCoclosure_kempe1 {P X : Colseq → Prop} (hX : SoundFor P X) {t : Colseq}
    (h : Kempe1 X t) : KempeCoclosure P t := by
  intro P' hP' ht
  obtain ⟨_, w, htw, hw⟩ := hP' t ht
  obtain ⟨s, hs, hsw⟩ := h w htw
  exact hX s hs P' hP' (hw s hsw)

/-- Subsets of `P` are sound. -/
theorem soundFor_of_sub {P X : Colseq → Prop} (h : ∀ t, X t → P t) : SoundFor P X :=
  fun t ht => kempeCoclosure_of_mem (h t ht)

/-- Soundness is inherited by subsets. -/
theorem SoundFor.mono {P X Y : Colseq → Prop} (hX : SoundFor P X) (hYX : ∀ t, Y t → X t) :
    SoundFor P Y := fun t ht => hX t (hYX t ht)

/-- Soundness of a union. -/
theorem SoundFor.union {P X Y : Colseq → Prop} (hX : SoundFor P X) (hY : SoundFor P Y) :
    SoundFor P (fun t => X t ∨ Y t) := fun t ht => ht.elim (hX t) (hY t)

/-- Soundness of a Kempe step. -/
theorem SoundFor.kempe1 {P X : Colseq → Prop} (hX : SoundFor P X) : SoundFor P (Kempe1 X) :=
  fun _ ht => kempeCoclosure_kempe1 hX ht

/-- Soundness of a permuted set. -/
theorem SoundFor.perm {P X : Colseq → Prop} (hX : SoundFor P X) (g : EdgePerm) :
    SoundFor P (fun t => X (FourColor.permt g t)) := fun _ ht =>
  kempeCoclosure_of_permt g (hX _ ht)

/-- The one-round soundness rule used by the engine: if every trace of `Y` has a color
permutation in `Kempe1 X`, then `Y` is sound when `X` is. -/
theorem SoundFor.step {P X Y : Colseq → Prop} (hX : SoundFor P X)
    (hY : ∀ t, Y t → ∃ g : EdgePerm, Kempe1 X (permt g t)) : SoundFor P Y := by
  intro t ht
  obtain ⟨g, hg⟩ := hY t ht
  exact kempeCoclosure_of_permt g (kempeCoclosure_kempe1 hX hg)

/-- The use of a sound set: a trace of a sound set cannot be separated from `P` by a Kempe
closed predicate.  In particular, if the complement of `P` is Kempe closed, a sound set is
contained in `P` (`SoundFor.sub_of_closed`). -/
theorem SoundFor.sub_of_closed {P X : Colseq → Prop} (hX : SoundFor P X)
    (hclosed : KempeClosed fun t => ¬ P t) {t : Colseq} (ht : X t) : P t := by
  by_contra hPt
  obtain ⟨s, hs, hns⟩ := hX t ht (fun t => ¬ P t) hclosed hPt
  exact hns hs

end FourColor.Engine
