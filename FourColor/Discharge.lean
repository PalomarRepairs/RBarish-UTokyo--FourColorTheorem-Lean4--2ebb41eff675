/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Part
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Discharging  (port of `discharge.v`)

Discharging arities to neighbouring faces. We specify how to compute the discharge "score" of a
face, using the 32 rules given by Robertson et al. to move charges across edges, and prove that
some face has a positive score (called "charge" by Robertson et al.). Each rule specifies a
score adjustment between neighbouring faces, and is represented here by one or two part
objects.

## Main definitions (Coq name → Lean name)

* `drules` → `Drules` (`List Part`).
* `drule1`, `drule2`, `drule2'`, ..., `drule32` → same names: the part encodings of the
  discharge rules, written with the part literals of `FourColor.PartSyntax`.
* `base_drules` → `baseDrules`: the list of all discharge rules, with multiplicity. This list
  has 38 items, as `drule1` is duplicated (it transfers 2 points), `drule2` and `drule3` are
  specialized by hub arity (we use `exactFitp`), `drule10` and `drule31` are specialized
  according to symmetry, and `drule3` is specialized to let the `mirrorPart` operation return an
  exact result.
* `symmetrize_drules rs` → `symmetrizeDrules rs`: complete the drule sequence by adding all the
  symmetrics of non-symmetrical parts, where the symmetry is reflection across the third spoke.
* `the_drules` → `theDrules`: the exact list of parts used to adjust the initial scores. Each
  part fitting at a dart `x` transfers one unit from the face of `x` to that of
  `edge (face² x)`; the two-face shift facilitates the use of the `conversePart` operation.
* `dscore1 x` → `G.dscore1 x`: the score transferred from the face of `x` to that of `edge x`
  (the number of parts in `theDrules` that fit `face⁻² x`).
* `dscore2 x` → `G.dscore2 x`: the total adjustment across the `(edge x, x)` edge, i.e.,
  `dscore1 (edge x) - dscore1 x`.
* `dscore x` → `G.dscore x`: the discharge score of the face `F` of `x`: `10 * (6 - #|F|)`,
  plus the adjustments from `theDrules`.
* `pick_source_drules n rs` → `pickSourceDrules n rs`: the parts in `rs` with size `n`, that
  is, the rules for taking score units from the hub face.
* `pick_target_drules n rs` → `pickTargetDrules n rs`: the converse of parts in `rs` compatible
  with hub size `n`; these are the drules for adding score units to the hub face.
* `drule_fork_values` (constructor `DruleForkValues`) → `DruleForkValues` (constructor
  `DruleForkValues.mk`), `drule_fork` (constructor `DruleFork`, fields `source_drules`,
  `target_drules`) → `DruleFork` (constructor `DruleFork.mk`, fields `sourceDrules`,
  `targetDrules`, `values`): the specializations of `theDrules` to hub size `n`.
* `sort_drules_result` (constructor `SortDrules`, fields `nb_forced_drules`,
  `straddling_drules`) → `SortDrulesResult` (constructor `SortDrulesResult.mk`, fields
  `nbForcedDrules`, `straddlingDrules`); `sort_drules_rec`, `sort_drules` → `sortDrulesRec`,
  `sortDrules`: `sortDrules p rs` returns the number of rules in `rs` implied by `p` (whose part
  representation contains `p`) and the rules in `rs` that are neither implied nor excluded by
  `p`.
* `dbound1 rs x` → `G.dbound1 rs x`: the number of part sectors in `rs` that fit at `x`.
* `dbound2 tr sr x` → `G.dbound2 tr sr x`: `dbound1 tr x - dbound1 sr x`.
* `dboundK n` → `dboundK n`: `10 * (6 - n)`.
* `sort_drules_spec` (constructor `SortDrulesSpec`) → `G.SortDrulesSpec` (constructor
  `SortDrulesSpec.mk`).

The rule data, `symmetrizeDrules`, `pickSourceDrules`, `pickTargetDrules`, `sortDrules` and
`dboundK` are structurally recursive first-order functions, evaluated by the Lean kernel in the
hubcap checks of the unavoidability proof. The scores (math-comp `int`) are integers (`ℤ`).

## Main results

* `dscore_cface`: the score only depends on the face.
* `dscore_roots`: in a planar plain cubic connected map the scores of the faces sum to `120`;
  hence `posz_dscore`: some face has a positive score.
* `dscore_mirror`: the scores of a map and of its mirror image coincide.
* `dbound1_eq`, `sort_dbound1_eq`, `sort_drulesP`, `dbound2_leq`, `dboundK_eq`, `dscore_cap1`,
  `source_drules_range`, `dscore_cap2`: the bounds on scores used to prune the combinatorial
  enumeration of parts in the hubcap checks.

## Deviations from the Coq statements

* Sums over a face `\sum_(y in cface x) F y` are `∑ y ∈ Finset.univ.filter (G.cface x ·), F y`
  and sums over face roots `\sum_(x in froots face)` are
  `∑ x ∈ Finset.univ.filter (fun x => froot G.face x = x), ...`, with classical decidability
  (`open Classical in`), since `cface` is a `Prop` here. `dscore` needs `[Fintype D]`.
* Hypermaps are finite by definition in Coq; here the lemmas assume `[Finite D]` (or
  `[Fintype D]` when a sum over darts is involved). The Coq section hypotheses become explicit
  arguments: `hG : G.PlanarPlainCubicConnected` (Coq `geoG` of section `DischargePlanar`) for
  `dscore_roots`, `posz_dscore`, `dscore_mirror`, and `hG : G.PlainCubicPentagonal` (Coq `geoG`
  of section `ScoreBound`) for `dbound2_leq`, `dboundK_eq`, `dscore_cap2`.
* `sumz_connect` is stated for a `Prop`-valued relation (Coq: a `rel` on a `finType`), with
  `roots e` written `{x | root e x = x}`.
* The coercions of `sort_drules_result` to `nat` and `drules` are the explicit projections
  `nbForcedDrules` and `straddlingDrules`; the `let rup := ...` of `sort_dbound1_eq` is
  unfolded.
* `sort_drules_spec` is a `Prop`-valued inductive family (a `Set` in Coq); see `sort_drulesP`
  for how to use it as a view.
* `~~ Pr58 nhub` is `¬ memRange .pr58 nhub`.
* Added (not in Coq): `DruleFork.sourceDrules_eq` and `DruleFork.targetDrules_eq`, the Lean
  form of the Coq idiom `case: rf => _ _ []`.
-/

namespace FourColor

open Function

universe u

/-! ### Discharge rules -/

/-- Coq `drules`: sequences of parts (discharge rules). -/
abbrev Drules : Type := List Part

section DischargeRules

open PartSyntax

/-- Coq `drule1`. -/
def drule1 : Part := Part $ * $ * $ 6+ $ * $ * $

/-- Coq `drule2`. -/
def drule2 : Part := Part $ * $ 5 $ 7+ $ * $ * $
/-- Coq `drule2'`. -/
def drule2' : Part := Part $ * $ 5 $ 7+ $ * $ * $ * $

/-- Coq `drule3`. -/
def drule3 : Part := Part $ 5 $ 6- $ 6+ $ * $ * $
/-- Coq `drule3'`. -/
def drule3' : Part := Part $ 5 $ 6- $ 6+ $ * $ * $ * $

/-- Coq `drule4`. -/
def drule4 : Part := Part $ 6- $[5] 5 $ 6+ $ * $ * $ * $
/-- Coq `drule4'`. -/
def drule4' : Part := Part $ 6- $[5] 6 $ 6+ $ * $ * $ * $

/-- Coq `drule5`. -/
def drule5 : Part := Part $ 6 $[6- 5] 6 $ 6+ $ * $ * $ * $

/-- Coq `drule6`. -/
def drule6 : Part := Part $ 6 $[6-] 5 $[5] 7+ $ * $ * $ * $

/-- Coq `drule7`. -/
def drule7 : Part := Part $ 6 $[6 6-] 6 $[5] 7+ $ * $ * $ * $

/-- Coq `drule8`. -/
def drule8 : Part := Part $ 5 $ 6- $ 7+ $ * $ * $ * $ * $

/-- Coq `drule9`. -/
def drule9 : Part := Part $ 6- $ 6- $ 7+ $ * $ * $ * $ 5 $

/-- Coq `drule10`. -/
def drule10 : Part := Part $ 5 $ 5 $ 7+ $ 5 $ 6+ $ * $ * $
/-- Coq `drule10'`. -/
def drule10' : Part := Part $ 5 $ 5 $ 7+ $ 5 $ 5 $ * $ * $

/-- Coq `drule11`. -/
def drule11 : Part := Part $ 6 $[5] 5 $ 7+ $ 5 $ 6+ $ * $ * $

/-- Coq `drule12`. -/
def drule12 : Part := Part $ 5 $[5] 5 $ 7+ $ 5 $[5] 5 $ * $ * $

/-- Coq `drule13`. -/
def drule13 : Part := Part $ 6 $[5] 5 $[5] 8+ $ 5 $ 5 $ * $ * $

/-- Coq `drule14`. -/
def drule14 : Part := Part $ 5 $[5] 6 $ 7+ $ 5 $ * $ * $ * $

/-- Coq `drule15`. -/
def drule15 : Part := Part $ 5 $ 6 $ 7+ $ 5 $ 7+ $ 5 $ 6 $

/-- Coq `drule16`. -/
def drule16 : Part := Part $ 6 $ 6 $ 7+ $ 5 $ 5 $ 5 $ 6 $

/-- Coq `drule17`. -/
def drule17 : Part := Part $ 5 $[6] 6 $ 7+ $ 5 $ 5 $ 7+ $ 5 $

/-- Coq `drule18`. -/
def drule18 : Part := Part $ 6 $[5] 5 $[5] 7 $ 6+ $ * $ * $ 5 $

/-- Coq `drule19`. -/
def drule19 : Part := Part $ 6 $ 6+ $ 8+ $[5] 5 $[5] 6 $ 5 $ 6 $

/-- Coq `drule20`. -/
def drule20 : Part := Part $ 5 $ 6 $ 7+ $ 6 $ 6 $ 5 $ 5 $

/-- Coq `drule21`. -/
def drule21 : Part := Part $ 6- $ 6 $[5] 7 $ 6+ $ * $ 5 $ 5 $

/-- Coq `drule22`. -/
def drule22 : Part := Part $ 5 $ 6 $[5] 7 $ 6+ $ * $ 5 $ 6 $

/-- Coq `drule23`. -/
def drule23 : Part := Part $ 5 $[5] 7 $ 7+ $ 5 $ * $ * $ * $

/-- Coq `drule24`. -/
def drule24 : Part := Part $ 5 $ 5 $[5] 7 $ 7+ $ 6 $ 6 $ 5 $

/-- Coq `drule25`. -/
def drule25 : Part := Part $ 5 $ 5 $ 7+ $[* * 5] 7 $[6] 5 $ 5 $ * $

/-- Coq `drule26`. -/
def drule26 : Part := Part $ 6 $ 6 $[5] 7 $ 7+ $ 5 $ 5 $ 6 $

/-- Coq `drule27`. -/
def drule27 : Part := Part $ 7+ $ 6 $[6 5 6+] 7 $ 7 $[5] 6- $ * $ * $

/-- Coq `drule28`. -/
def drule28 : Part := Part $ 5 $ 5 $ 7+ $ 5 $ 5 $ * $ * $ 5 $

/-- Coq `drule29`. -/
def drule29 : Part := Part $ 5 $[5] 5 $ 7+ $ 5 $ * $ * $ 5 $ 5 $

/-- Coq `drule30`. -/
def drule30 : Part := Part $ 5 $ 5 $ 7+ $ 5 $[5] 6 $ 5 $ * $ * $

/-- Coq `drule31`. -/
def drule31 : Part := Part $ 5 $[5] 5 $ 7+ $ 5 $[6+] 5 $ 6+ $ * $ 6+ $
/-- Coq `drule31'`. -/
def drule31' : Part := Part $ 5 $[5] 5 $ 7+ $ 5 $[5] 5 $ 6+ $ * $ 6+ $

/-- Coq `drule32`. -/
def drule32 : Part := Part $ 5 $ 6 $[5] 7 $ 7+ $ 6 $ 5 $ 5 $ 5 $

end DischargeRules

/-- Coq `base_drules`: the list of all discharge rules, with multiplicity (38 items). -/
def baseDrules : Drules :=
  [drule1, drule1, drule2, drule2', drule3, drule3', drule4, drule4', drule5,
   drule6, drule7, drule8, drule9, drule10, drule10',
   drule11, drule12, drule13, drule14, drule15, drule16, drule17, drule18, drule19,
   drule20, drule21, drule22, drule23, drule24, drule25, drule26, drule27, drule28, drule29,
   drule30, drule31, drule31', drule32]

/-- Coq `symmetrize_drules r`: complete the drule sequence `r` by adding the symmetric image
`p'` of every part `p` that is not contained in `p'`, where the symmetry is the reflection across
the third spoke (`p'` is `mirrorPart p` rotated five times by `sizePart p - 1`). -/
def symmetrizeDrules : Drules → Drules
  | [] => []
  | p :: r' =>
    let p' := (rotPart (sizePart p - 1))^[5] (mirrorPart p)
    let psr := p :: symmetrizeDrules r'
    match cmpPart p p' with
    | .subset => psr
    | _ => p' :: psr
termination_by structural r => r

/-- Coq `the_drules`: the exact list of parts used to adjust the initial scores. -/
def theDrules : Drules := symmetrizeDrules baseDrules

/-! ### The discharge score (Coq section `Discharge`) -/

namespace Hypermap

variable {D : Type u} (G : Hypermap D)

/-- Coq `dscore1 x`: the score transferred from the face of `x` to that of `edge x`, i.e., the
number of parts in `theDrules` that fit `face⁻² x` exactly. -/
noncomputable def dscore1 (x : D) : ℤ :=
  ((theDrules.countP (G.exactFitp (G.invFace2 x)) : ℕ) : ℤ)

/-- Coq `dscore2 x`: the total adjustment across the `(edge x, x)` edge. -/
noncomputable def dscore2 (x : D) : ℤ := G.dscore1 (G.edge x) - G.dscore1 x

open Classical in
/-- Coq `dscore x`: the discharge score of the face `F` of `x`, `10 * (6 - #|F|)` plus the
adjustments `dscore2` across the edges of `F`. -/
noncomputable def dscore [Fintype D] (x : D) : ℤ :=
  60 - ((10 * G.arity x : ℕ) : ℤ) +
    ∑ y ∈ Finset.univ.filter (fun y => G.cface x y), G.dscore2 y

open Classical in
/-- Coq `dscore_cface`. -/
theorem dscore_cface [Fintype D] {x y : D} (h : G.cface x y) : G.dscore x = G.dscore y := by
  unfold dscore
  rw [G.arity_cface h, Finset.filter_congr (fun z _ => G.same_cface h z)]

/-! #### Sums over a face -/

open Classical in
/-- The number of darts in the face of `x` is its arity. -/
private theorem card_cface [Fintype D] (x : D) :
    (Finset.univ.filter (fun y => G.cface x y)).card = G.arity x := by
  rw [← Set.ncard_coe_finset, Finset.coe_filter]
  simp only [Finset.mem_univ, true_and]
  rfl

open Classical in
/-- Reindexing a sum over a face by `face` (Coq `reindex_inj faceI` and `cface1r`). -/
private theorem sum_cface_face [Fintype D] (x : D) (F : D → ℤ) :
    ∑ y ∈ Finset.univ.filter (fun y => G.cface x y), F (G.face y) =
      ∑ y ∈ Finset.univ.filter (fun y => G.cface x y), F y := by
  refine Finset.sum_nbij' G.face (fun y => G.edge (G.node y)) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact (G.cface1r x y).1 hy
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    rw [G.cface1r x, G.nodeK]
    exact hy
  · intro y _
    exact G.faceK y
  · intro y _
    exact G.nodeK y

end Hypermap

/-! ### Scores of planar maps (Coq section `DischargePlanar`) -/

open Classical in
/-- Coq `sumz_connect`: summing over the components of a connect-symmetric relation. -/
theorem sumz_connect {I : Type*} [Fintype I] (e : I → I → Prop) (F : I → ℤ)
    (hs : ConnectSym e) :
    ∑ x ∈ Finset.univ.filter (fun x => root e x = x),
      ∑ y ∈ Finset.univ.filter (fun y => connect e x y), F y = ∑ y, F y := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (g := root e)
    (t := Finset.univ.filter (fun x => root e x = x))
    (fun y _ => by simp only [Finset.mem_filter, Finset.mem_univ, true_and, root_root hs]) F]
  refine Finset.sum_congr rfl fun x hx => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
  refine Finset.sum_congr (Finset.filter_congr fun y _ => ?_) fun _ _ => rfl
  constructor
  · intro hxy
    rw [← hx]
    exact (root_eq_iff hs).2 (hs _ _ hxy)
  · intro hyx
    have : root e y = root e x := by rw [hyx, hx]
    exact hs _ _ ((root_eq_iff hs).1 this)

open Classical in
/-- The number of components of a connect-symmetric relation is the number of roots. -/
private theorem nComp_univ_eq_card_roots {α : Type*} [Fintype α] {e : α → α → Prop}
    (hs : ConnectSym e) :
    nComp e Set.univ = (Finset.univ.filter (fun x => root e x = x)).card := by
  unfold nComp
  have himg : comp e '' Set.univ = comp e '' ↑(Finset.univ.filter (fun x => root e x = x)) := by
    ext c
    constructor
    · rintro ⟨x, -, rfl⟩
      refine ⟨root e x, ?_, ?_⟩
      · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq, root_root hs]
      · exact (comp_eq_iff hs).2 (hs _ _ (connect_root e x))
    · rintro ⟨x, -, rfl⟩
      exact ⟨x, Set.mem_univ _, rfl⟩
  rw [himg, Set.InjOn.ncard_image, Set.ncard_coe_finset]
  intro x hx y hy hxy
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
  rw [← hx, ← hy]
  exact (root_eq_iff hs).2 ((comp_eq_iff hs).1 hxy)

namespace Hypermap

variable {D : Type u} (G : Hypermap D)

/-- The sum of the `dscore2` adjustments over all darts vanishes. -/
private theorem sum_dscore2 [Fintype D] : ∑ y, G.dscore2 y = 0 := by
  simp only [dscore2, Finset.sum_sub_distrib]
  rw [Fintype.sum_bijective G.edge G.edgeI.bijective_of_finite (fun y => G.dscore1 (G.edge y))
    G.dscore1 (fun _ => rfl), sub_self]

open Classical in
/-- Coq `dscore_roots`. -/
theorem dscore_roots [Fintype D] (hG : G.PlanarPlainCubicConnected) :
    ∑ x ∈ Finset.univ.filter (fun x => froot G.face x = x), G.dscore x = 120 := by
  have h1 : ∀ x, G.dscore x =
      60 + ∑ y ∈ Finset.univ.filter (fun y => G.cface x y), (G.dscore2 y - 10) := by
    intro x
    rw [dscore, Finset.sum_sub_distrib, Finset.sum_const, G.card_cface, nsmul_eq_mul]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_add_distrib,
    sumz_connect (frel G.face) _ G.cface_sym, Finset.sum_sub_distrib, G.sum_dscore2,
    Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul]
  have hE := (G.cubic_euler hG.toPlainCubicConnected).1 hG.planar
  have hc : fcard G.face Set.univ = (Finset.univ.filter (fun x => froot G.face x = x)).card :=
    nComp_univ_eq_card_roots G.cface_sym
  rw [hc] at hE
  have hE' : (6 : ℤ) * ((Finset.univ.filter (fun x => froot G.face x = x)).card : ℤ) =
      (Fintype.card D : ℤ) + 12 := by exact_mod_cast hE
  linarith

/-- Coq `posz_dscore`. -/
theorem posz_dscore [Fintype D] (hG : G.PlanarPlainCubicConnected) : ∃ x, 0 < G.dscore x := by
  classical
  by_contra h
  simp only [not_exists, not_lt] at h
  have h1 := G.dscore_roots hG
  have h2 : ∑ x ∈ Finset.univ.filter (fun x => froot G.face x = x), G.dscore x ≤ 0 :=
    Finset.sum_nonpos fun x _ => h x
  linarith

/-! #### Mirror image -/

/-- `face⁻²` in the mirror map, at `face x`, is `face³ x`. -/
private theorem mirror_invFace2_face [Finite D] (x : D) :
    G.mirror.invFace2 (G.face x) = G.face (G.face (G.face x)) := by
  simp only [invFace2, mirror_edge, mirror_node, G.edgeK]

/-- `face⁵ (face⁻² x) = face³ x`. -/
private theorem iter_face_invFace2 [Finite D] (x : D) :
    G.face^[5] (G.invFace2 x) = G.face (G.face (G.face x)) := by
  simp only [invFace2, Function.iterate_succ_apply', Function.iterate_zero_apply, G.nodeK]

/-- The mirror face permutation is the inverse of `face`. -/
private theorem mirror_face_iter [Finite D] (k : ℕ) (w : D) :
    G.mirror.face^[k] (G.face^[k] w) = w := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply (f := G.mirror.face),
      Function.iterate_succ_apply' (f := G.face)]
    show G.mirror.face^[k] (G.edge (G.node (G.face (G.face^[k] w)))) = w
    rw [G.faceK, ih]

end Hypermap

/-- Rotations preserve the size of parts. -/
private theorem size_iter_rotPart (k i : ℕ) (q : Part) :
    sizePart ((rotPart k)^[i] q) = sizePart q := by
  induction i generalizing q with
  | zero => rfl
  | succ i ih => rw [Function.iterate_succ_apply, ih, size_rot_part]

namespace Hypermap

variable {D : Type u}

/-- Rotating a part of size `n` by `n - 1` amounts to moving its anchor one step along the
face (Coq `fit_rp`, one step). -/
private theorem exactFitp_rot_pred [Finite D] (G1 : Hypermap D) (Q : Part) (x1 : D) :
    G1.exactFitp x1 (rotPart (sizePart Q - 1) Q) = G1.exactFitp (G1.face x1) Q := by
  by_cases hx : G1.arity x1 = sizePart Q
  · have hpos : 0 < G1.arity x1 := order_pos G1.faceI x1
    rw [G1.fitp_rot (sizePart Q - 1) Q (Nat.sub_le _ _) (G1.face x1),
      ← Function.iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel (by omega), ← hx,
      G1.iter_face_arity]
  · have h1 : (G1.arity x1 == sizePart (rotPart (sizePart Q - 1) Q)) = false := by
      rw [size_rot_part]; simpa using hx
    have h2 : (G1.arity (G1.face x1) == sizePart Q) = false := by
      rw [G1.arity_face]; simpa using hx
    simp only [exactFitp, h1, h2, Bool.false_and]

/-- Coq `fit_rp`: iterated rotations by `size - 1` move the anchor along the face. -/
private theorem exactFitp_iter_rot [Finite D] (G1 : Hypermap D) (q : Part) (i : ℕ) (x1 : D) :
    G1.exactFitp x1 ((rotPart (sizePart q - 1))^[i] q) = G1.exactFitp (G1.face^[i] x1) q := by
  induction i generalizing x1 with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply, ← ih (G1.face x1)]
    have hs := size_iter_rotPart (sizePart q - 1) i q
    have := exactFitp_rot_pred G1 ((rotPart (sizePart q - 1))^[i] q) x1
    rwa [hs] at this

/-- Exact fitting is inherited by containing parts of the same size. -/
private theorem exactFitp_of_subset (G1 : Hypermap D) {x : D} {p q : Part}
    (hpq : cmpPart p q = .subset) (hsz : sizePart q = sizePart p) (h : G1.exactFitp x p) :
    G1.exactFitp x q := by
  simp only [exactFitp, Bool.and_eq_true, beq_iff_eq] at h ⊢
  refine ⟨by rw [hsz]; exact h.1, ?_⟩
  rw [G1.fitp_cmp p x h.2 q, hpq]
  rfl

variable (G : Hypermap D)

/-- Coq `dscore_mirror`, the key step `score1F`: `dscore1` of the mirror map at `face x` is
`dscore1` at `x`. -/
private theorem dscore1_mirror_face [Finite D] (hG : G.PlainCubic) (x : D) :
    G.mirror.dscore1 (G.face x) = G.dscore1 x := by
  unfold dscore1
  congr 1
  rw [G.mirror_invFace2_face, ← G.iter_face_invFace2]
  generalize G.invFace2 x = y
  unfold theDrules
  induction baseDrules with
  | nil => rfl
  | cons p r ih =>
    set p1 := (rotPart (sizePart p - 1))^[5] (mirrorPart p) with hp1
    have Ep1 : sizePart p1 = sizePart p := by
      rw [hp1, size_iter_rotPart, size_mirror_part]
    have fit_p1 : ∀ (G1 : Hypermap D) (x1 : D),
        G1.exactFitp x1 p1 = G1.exactFitp (G1.face^[5] x1) (mirrorPart p) := by
      intro G1 x1
      have := exactFitp_iter_rot G1 (mirrorPart p) 5 x1
      rwa [size_mirror_part] at this
    -- the mirror of `p1` at `face⁵ y` is `p` at `y`, and conversely
    have hA : G.mirror.exactFitp (G.face^[5] y) p1 = G.exactFitp y p := by
      rw [fit_p1, G.mirror_face_iter, ← G.fitp_mirror hG, mirror_mirror_part]
    have hB : G.exactFitp y p1 = G.mirror.exactFitp (G.face^[5] y) p := by
      rw [fit_p1, G.fitp_mirror hG]
    simp only [symmetrizeDrules]
    rw [← hp1]
    rcases hc : cmpPart p p1
    · simp only [List.countP_cons, hA, hB, ih]
      omega
    · simp only [List.countP_cons, hA, hB, ih]
      omega
    · simp only [List.countP_cons, ih]
      have hAB : G.mirror.exactFitp (G.face^[5] y) p = G.exactFitp y p := by
        apply Bool.eq_iff_iff.2
        constructor
        · intro h
          rw [← hA]
          exact exactFitp_of_subset G.mirror hc Ep1 h
        · intro h
          rw [← hB]
          exact exactFitp_of_subset G hc Ep1 h
      rw [hAB]

open Classical in
/-- Coq `dscore_mirror`. -/
theorem dscore_mirror [Fintype D] (hG : G.PlanarPlainCubicConnected) (x : D) :
    G.mirror.dscore x = G.dscore x := by
  have hPC : G.PlainCubic := hG.toPlainCubic
  unfold dscore
  rw [G.arity_mirror, Finset.filter_congr (fun y _ => G.cface_mirror x y),
    ← G.sum_cface_face x G.mirror.dscore2]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [dscore2, mirror_edge, G.plain_eq' hPC.plain, G.dscore1_mirror_face hPC]

end Hypermap

/-! ### Score bounds (Coq section `ScoreBound`)

Rule selectors, by source or target arity, or by matching a part. The "target arity" returns a
list of converse rules. The "matching" selector returns a pair of the number of rules that are
forced by the part, plus the list of rules that straddle the part, discarding the rules that
are disjoint from or forced by the part. The matching selector is part of the inner loop of the
unavoidability computation. -/

/-- Coq `pick_source_drules nhub`: the parts with size `nhub`, i.e., the rules for taking score
units from a hub face of arity `nhub`. -/
def pickSourceDrules (nhub : ℕ) : Drules → Drules :=
  List.filter (fun p => sizePart p == nhub)

/-- Coq `pick_target_drules nhub`: the converse of the parts compatible with hub size `nhub`,
i.e., the rules for adding score units to a hub face of arity `nhub`. -/
def pickTargetDrules (nhub : ℕ) : Drules → Drules
  | [] => []
  | p :: r' =>
    match conversePart p with
    | (u, p') =>
      let tr := pickTargetDrules nhub r'
      if memRange u nhub then p' :: tr else tr
termination_by structural r => r

/-- Coq `sort_drules_result` (constructor `SortDrules`): the result of `sortDrules`. -/
structure SortDrulesResult where
  /-- Coq `nb_forced_drules` (a coercion to `nat` in Coq): the number of rules forced by the
  part. -/
  nbForcedDrules : ℕ
  /-- Coq `straddling_drules` (a coercion to `drules` in Coq): the rules that straddle the
  part. -/
  straddlingDrules : Drules

/-- Coq `sort_drules_rec p n rs r`: add to `n` the number of rules of `r` implied by `p`, and
prepend to `rs` the rules of `r` that are neither implied nor excluded by `p`. -/
def sortDrulesRec (p : Part) : ℕ → Drules → Drules → SortDrulesResult
  | n, rs, [] => ⟨n, rs⟩
  | n, rs, p' :: r' =>
    match cmpPart p p' with
    | .subset => sortDrulesRec p (n + 1) rs r'
    | .straddle => sortDrulesRec p n (p' :: rs) r'
    | .disjoint => sortDrulesRec p n rs r'
termination_by structural _ _ r => r

/-- Coq `sort_drules p r`: the number of rules in `r` implied by `p`, and the rules in `r`
that are neither implied nor excluded by `p`. -/
def sortDrules (p : Part) (r : Drules) : SortDrulesResult := sortDrulesRec p 0 [] r

/-- Coq `drule_fork_values` (constructor `DruleForkValues`): the specification of the fields of
a `DruleFork`. -/
inductive DruleForkValues (nhub : ℕ) : Drules → Drules → Prop
  /-- Coq `DruleForkValues`. -/
  | mk : DruleForkValues nhub (pickSourceDrules nhub theDrules) (pickTargetDrules nhub theDrules)

/-- Coq `drule_fork nhub` (constructor `DruleFork`): a rule fork specializes the full set of
discharge rules for a specific hub size, so that the source/target arity selection is only
performed once. -/
structure DruleFork (nhub : ℕ) where
  /-- Coq `source_drules`: `pickSourceDrules nhub theDrules`. -/
  sourceDrules : Drules
  /-- Coq `target_drules`: `pickTargetDrules nhub theDrules`. -/
  targetDrules : Drules
  /-- The (anonymous) Coq field: `sourceDrules` and `targetDrules` have the specified
  values. -/
  values : DruleForkValues nhub sourceDrules targetDrules

variable {nhub : ℕ} in
/-- The source rules of a drule fork are `pickSourceDrules nhub theDrules` (the Lean form of the
Coq idiom `case: rf => _ _ []`). -/
theorem DruleFork.sourceDrules_eq (rf : DruleFork nhub) :
    rf.sourceDrules = pickSourceDrules nhub theDrules := by
  obtain ⟨_, _, ⟨⟩⟩ := rf
  rfl

variable {nhub : ℕ} in
/-- The target rules of a drule fork are `pickTargetDrules nhub theDrules` (the Lean form of the
Coq idiom `case: rf => _ _ []`). -/
theorem DruleFork.targetDrules_eq (rf : DruleFork nhub) :
    rf.targetDrules = pickTargetDrules nhub theDrules := by
  obtain ⟨_, _, ⟨⟩⟩ := rf
  rfl

/-- Coq `dboundK nhub`: `10 * (6 - nhub)`, the initial score of a hub of arity `nhub ≥ 5`. -/
def dboundK (nhub : ℕ) : ℤ :=
  match nhub - 5 with
  | n + 1 => -((n * 10 : ℕ) : ℤ)
  | 0 => 10

namespace Hypermap

variable {D : Type u} (G : Hypermap D)

/-- Coq `dbound1 r x`: the number of part sectors in `r` that fit at `x`. -/
noncomputable def dbound1 (r : Drules) (x : D) : ℕ := r.countP (G.fitp x)

/-- Coq `dbound2 r r' x`: the number of part sectors in `r` that fit at `x`, minus the number of
those in `r'` that fit at `x`. -/
noncomputable def dbound2 (r r' : Drules) (x : D) : ℤ :=
  (G.dbound1 r x : ℤ) - (G.dbound1 r' x : ℤ)

/-- Coq `sort_drules_spec x r` (constructor `SortDrulesSpec`): `G.SortDrulesSpec x r s m` holds
when, for some `n` and `r'`, `s = ⟨n, r'⟩` and `m = n + G.dbound1 r' x`. -/
inductive SortDrulesSpec (x : D) (r : Drules) : SortDrulesResult → ℕ → Prop
  /-- Coq `SortDrulesSpec`. -/
  | mk (n : ℕ) (r' : Drules) : SortDrulesSpec x r ⟨n, r'⟩ (n + G.dbound1 r' x)

variable {nhub : ℕ}

/-- `face⁻² (face² x) = x`. -/
private theorem invFace2_face_face [Finite D] (x : D) : G.invFace2 (G.face (G.face x)) = x := by
  simp only [invFace2, G.faceK]

/-- Coq `dbound1_eq`. -/
theorem dbound1_eq [Finite D] (rf : DruleFork nhub) {x : D} (nFx : G.arity x = nhub) :
    G.dscore1 (G.face (G.face x)) = (G.dbound1 rf.sourceDrules x : ℤ) := by
  obtain ⟨rs, rt, hv⟩ := rf
  cases hv
  unfold dscore1 dbound1
  rw [G.invFace2_face_face]
  congr 1
  unfold pickSourceDrules exactFitp
  rw [List.countP_filter, nFx]
  congr 1
  funext p
  rw [Bool.and_comm, Bool.beq_comm]

/-- Coq `sort_dbound1_eq`. -/
theorem sort_dbound1_eq {x : D} {p : Part} (fit_xp : G.fitp x p) (ru : Drules) :
    G.dbound1 ru x =
      (sortDrules p ru).nbForcedDrules + G.dbound1 (sortDrules p ru).straddlingDrules x := by
  have key : ∀ (m : ℕ) (rs : Drules), m + G.dbound1 rs x + G.dbound1 ru x =
      (sortDrulesRec p m rs ru).nbForcedDrules +
        G.dbound1 (sortDrulesRec p m rs ru).straddlingDrules x := by
    induction ru with
    | nil => intro m rs; simp [sortDrulesRec, dbound1]
    | cons r ru ih =>
      intro m rs
      have hr := G.fitp_cmp p x fit_xp r
      simp only [sortDrulesRec]
      rcases hc : cmpPart p r
      · -- disjoint
        rw [hc] at hr
        have hr' : G.fitp x r = false := hr
        rw [← ih m rs]
        simp only [dbound1, List.countP_cons, hr', Bool.false_eq_true, ite_false]
        omega
      · -- straddle
        rw [← ih m (r :: rs)]
        simp only [dbound1, List.countP_cons]
        omega
      · -- subset
        rw [hc] at hr
        have hr' : G.fitp x r = true := hr
        rw [← ih (m + 1) rs]
        simp only [dbound1, List.countP_cons, hr', ite_true]
        omega
  have := key 0 []
  simp only [dbound1, List.countP_nil, Nat.zero_add] at this
  exact this

/-- Coq `sort_drulesP`. As in Coq, this is meant to be used as a view; since Lean's `cases`
does not abstract the goal over the indices, generalize them first, e.g.
`have hs := G.sort_drulesP fit_xp r`,
`generalize sortDrules p r = s, G.dbound1 r x = m at hs ⊢`, then `obtain ⟨n, r'⟩ := hs`. -/
theorem sort_drulesP {x : D} {p : Part} (fit_xp : G.fitp x p) (r : Drules) :
    G.SortDrulesSpec x r (sortDrules p r) (G.dbound1 r x) := by
  rw [G.sort_dbound1_eq fit_xp r]
  generalize sortDrules p r = res
  obtain ⟨n, r'⟩ := res
  exact .mk n r'

/-- Coq `dbound2_leq`. -/
theorem dbound2_leq [Finite D] (rf : DruleFork nhub) (hG : G.PlainCubicPentagonal) {x : D}
    (nFx : G.arity x = nhub) :
    G.dscore2 (G.face (G.face x)) ≤ G.dbound2 rf.targetDrules rf.sourceDrules x := by
  unfold dbound2 dscore2
  rw [← G.dbound1_eq rf nFx]
  suffices h : G.dscore1 (G.edge (G.face (G.face x))) ≤ (G.dbound1 rf.targetDrules x : ℤ) by
    linarith
  unfold dscore1
  norm_cast
  obtain ⟨rs, rt, hv⟩ := rf
  cases hv
  -- the converse of a rule fitting `y` fits `x`
  have key : ∀ r, G.exactFitp (G.invFace2 (G.edge (G.face (G.face x)))) r →
      memRange (conversePart r).1 nhub ∧ G.fitp x (conversePart r).2 := by
    intro r hr
    have hc := G.fitp_converse hG r _ hr
    have hx : G.invFace2 (G.edge (G.face (G.face
        (G.invFace2 (G.edge (G.face (G.face x))))))) = x := by
      simp only [invFace2, G.nodeK, G.plain_eq hG.plain, G.faceK]
    rw [hx] at hc
    rcases hcr : conversePart r with ⟨u, r'⟩
    rw [hcr] at hc
    simp only [tightFitp, Bool.and_eq_true, nFx] at hc
    exact hc
  show List.countP _ theDrules ≤ G.dbound1 (pickTargetDrules nhub theDrules) x
  induction theDrules with
  | nil => simp [pickTargetDrules, dbound1]
  | cons r dr ih =>
    rw [List.countP_cons]
    have kr := key r
    simp only [pickTargetDrules]
    rcases hcr : conversePart r with ⟨u, r'⟩
    rw [hcr] at kr
    simp only at kr ⊢
    by_cases hyr : G.exactFitp (G.invFace2 (G.edge (G.face (G.face x)))) r = true
    · obtain ⟨hu, hfit⟩ := kr hyr
      simp only [hyr, hu, ite_true, dbound1, List.countP_cons, hfit]
      simp only [dbound1] at ih
      omega
    · have hyr' : G.exactFitp (G.invFace2 (G.edge (G.face (G.face x)))) r = false := by
        simpa using hyr
      simp only [hyr', Bool.false_eq_true, ite_false, Nat.add_zero]
      refine le_trans ih ?_
      split
      · simp only [dbound1, List.countP_cons]
        omega
      · exact le_rfl

/-- Coq `dboundK_eq`. -/
theorem dboundK_eq (hG : G.PlainCubicPentagonal) {x : D} (nFx : G.arity x = nhub) :
    dboundK nhub = 60 - ((10 * G.arity x : ℕ) : ℤ) := by
  have h5 := hG.pentagonal x
  unfold dboundK
  split
  · rename_i n hn
    push_cast
    omega
  · rename_i hn
    push_cast
    omega

open Classical in
/-- Coq `dscore_cap1`. -/
theorem dscore_cap1 [Fintype D] (m : ℕ) (ub_m : ∀ y, G.dscore1 y ≤ m) (x : D)
    (pos_x : 0 < G.dscore x) (d : ℕ) (max_m : 59 < (10 - m) * d) : G.arity x < d := by
  by_contra hd
  have hdx : d ≤ G.arity x := not_lt.1 hd
  have ltm10 : m < 10 := by
    by_contra h
    have : 10 - m = 0 := by omega
    rw [this, Nat.zero_mul] at max_m
    omega
  have h60 : 60 ≤ (10 - m) * G.arity x := le_trans max_m (Nat.mul_le_mul_left _ hdx)
  have h60' : (60 : ℤ) ≤ (10 - (m : ℤ)) * (G.arity x : ℤ) := by
    have : ((60 : ℕ) : ℤ) ≤ (((10 - m) * G.arity x : ℕ) : ℤ) := by exact_mod_cast h60
    push_cast [Nat.cast_sub ltm10.le] at this
    exact this
  have hsum : ∑ y ∈ Finset.univ.filter (fun y => G.cface x y), G.dscore2 y ≤
      ∑ y ∈ Finset.univ.filter (fun y => G.cface x y), (m : ℤ) := by
    refine Finset.sum_le_sum fun y _ => ?_
    have h1 := ub_m (G.edge y)
    have h2 : 0 ≤ G.dscore1 y := by unfold dscore1; positivity
    unfold dscore2
    linarith
  rw [Finset.sum_const, G.card_cface, nsmul_eq_mul] at hsum
  unfold dscore at pos_x
  push_cast at pos_x
  nlinarith

/-- Coq `source_drules_range`. -/
theorem source_drules_range (rf : DruleFork nhub) (h : ¬ memRange .pr58 nhub) :
    rf.sourceDrules = [] := by
  obtain ⟨rs, rt, hv⟩ := rf
  cases hv
  have key : ∀ p ∈ theDrules, memRange .pr58 (sizePart p) = true := by decide
  show pickSourceDrules nhub theDrules = []
  unfold pickSourceDrules
  rw [List.filter_eq_nil_iff]
  intro p hp heq
  rw [beq_iff_eq] at heq
  exact h (heq ▸ key p hp)

open Classical in
/-- Coq `dscore_cap2`. -/
theorem dscore_cap2 [Fintype D] (rf : DruleFork nhub) (hG : G.PlainCubicPentagonal) {x : D}
    (nFx : G.arity x = nhub) (pos_x : 0 < G.dscore x) :
    0 < dboundK nhub + ∑ y ∈ Finset.univ.filter (fun y => G.cface x y),
      G.dbound2 rf.targetDrules rf.sourceDrules y := by
  have hsum : ∑ y ∈ Finset.univ.filter (fun y => G.cface x y), G.dscore2 y ≤
      ∑ y ∈ Finset.univ.filter (fun y => G.cface x y),
        G.dbound2 rf.targetDrules rf.sourceDrules y := by
    rw [← G.sum_cface_face x G.dscore2, ← G.sum_cface_face x (fun y => G.dscore2 (G.face y))]
    refine Finset.sum_le_sum fun y hy => ?_
    have hy' : G.cface x y := (Finset.mem_filter.1 hy).2
    exact G.dbound2_leq rf hG (by rw [← G.arity_cface hy', nFx])
  unfold dscore at pos_x
  rw [← G.dboundK_eq hG nFx] at pos_x
  linarith

end Hypermap

end FourColor
