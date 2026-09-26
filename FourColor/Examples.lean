/-
Copyright (c) 2026. Lean 4 port of the planarity part of the Coq/Rocq formal proof
of the Four Color Theorem by Georges Gonthier (math-comp/fourcolor).
-/
import FourColor.Jordan
import Mathlib.Tactic.FinCases

/-!
# Sanity checks: planarity is neither vacuous nor trivial

Two small examples that exercise the definitions end to end:

* `unitMap` — the one-dart hypermap (all permutations trivial) has genus `0`, so it is
  `Planar` (and hence `Jordan`).
* `torus` — the one-vertex, one-face map of the torus: 4 darts, two edges (`x ↦ x + 2`),
  node and face rotations `x ↦ x + 1`.  We compute its genus directly from the Euler formula
  (`genus = (2·1 + 4 − (2 + 1 + 1)) / 2 = 1`) and also exhibit an explicit Moebius path, so it
  is neither `Planar` nor `Jordan` — consistently with `planar_iff_jordan`.
-/

namespace FourColor

namespace Hypermap

namespace Examples

/-! ### The one-dart map -/

/-- The hypermap with a single dart and trivial permutations. -/
def unitMap : Hypermap Unit where
  edge := id
  node := id
  face := id
  edgeK _ := rfl

theorem nComp_unit (e : Unit → Unit → Prop) : nComp e Set.univ = 1 := by
  rw [nComp, Set.univ_unique, Set.image_singleton, Set.ncard_singleton]

theorem unitMap_genus : unitMap.genus = 0 := by
  simp [genus, eulerLhs, eulerRhs, fcard, nComp_unit]

theorem unitMap_planar : unitMap.Planar := unitMap_genus

theorem unitMap_jordan : unitMap.Jordan := (planar_iff_jordan _).1 unitMap_planar

/-! ### The torus with one vertex, two edges and one face -/

/-- A genus-one hypermap: darts `0 = a⁺, 1 = b⁺, 2 = a⁻, 3 = b⁻`, the edge involution pairs
`a⁺ a⁻` and `b⁺ b⁻`, and the single vertex and single face both rotate `0 → 1 → 2 → 3`. -/
def torus : Hypermap (Fin 4) where
  edge x := x + 2
  node x := x + 1
  face x := x + 1
  edgeK := by decide

/-- An explicit Moebius path: the contour `0 → 1 → 2` (two F-links), with the cross N-links
`0 → node 0 = 1` and `1 → node 1 = 2`. -/
theorem torus_moebius : torus.MoebiusPath [0, 1, 2] := by
  refine ⟨by decide, ⟨Or.inr (by decide), Or.inr (by decide), trivial⟩, ?_⟩
  show mem2 [1, 2] ((2 + 2) + 1) (0 + 1)
  exact Or.inl ⟨by decide, by decide⟩

theorem torus_not_jordan : ¬ torus.Jordan := fun h => h _ torus_moebius

theorem torus_not_planar : ¬ torus.Planar := fun h =>
  torus_not_jordan ((planar_iff_jordan _).1 h)

/-- A connect-symmetric relation all of whose points are connected to `0` has one component. -/
theorem nComp_univ_eq_one {e : Fin 4 → Fin 4 → Prop} (hs : ConnectSym e)
    (h : ∀ x, connect e 0 x) : nComp e Set.univ = 1 := by
  have : (Set.univ : Set (Fin 4)) = comp e 0 := by
    ext x; exact ⟨fun _ => h x, fun _ => trivial⟩
  rw [this, nComp_comp hs]

theorem torus_node_conn (x : Fin 4) : fconnect torus.node 0 x := by
  refine fconnect_iff_iterate.2 ⟨x.val, ?_⟩
  fin_cases x <;> decide

theorem torus_face_conn (x : Fin 4) : fconnect torus.face 0 x := by
  refine fconnect_iff_iterate.2 ⟨x.val, ?_⟩
  fin_cases x <;> decide

/-- The edge orbit of `0` is `{0, 2}`. -/
theorem torus_edge_orbit {x : Fin 4} (h : fconnect torus.edge 0 x) : x = 0 ∨ x = 2 := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hbc ih =>
    subst hbc
    rcases ih with rfl | rfl
    · exact Or.inr (by decide)
    · exact Or.inl (by decide)

theorem torus_fcard_edge : fcard torus.edge Set.univ = 2 := by
  have hs : ConnectSym (frel torus.edge) := fconnect_sym torus.edgeI
  have huniv : (Set.univ : Set (Fin 4)) = fclosure torus.edge {0, 1} := by
    ext x
    refine ⟨fun _ => ?_, fun _ => trivial⟩
    fin_cases x
    · exact ⟨0, by simp, connect_refl _⟩
    · exact ⟨1, by simp, connect_refl _⟩
    · exact ⟨0, by simp, connect_of_rel (by decide)⟩
    · exact ⟨1, by simp, connect_of_rel (by decide)⟩
  rw [huniv]
  refine nComp_closure2_of_not_connect hs fun h => ?_
  rcases torus_edge_orbit h with h | h <;> exact absurd h (by decide)

theorem torus_nComp_glink : nComp torus.glink Set.univ = 1 :=
  nComp_univ_eq_one torus.glinkC fun x => torus.gcomp_of_cnode (torus_node_conn x)

/-- The Euler formula gives genus `1` for the torus map. -/
theorem torus_genus : torus.genus = 1 := by
  have hN : fcard torus.node Set.univ = 1 :=
    nComp_univ_eq_one (fconnect_sym torus.nodeI) torus_node_conn
  have hF : fcard torus.face Set.univ = 1 :=
    nComp_univ_eq_one (fconnect_sym torus.faceI) torus_face_conn
  simp only [genus, eulerLhs, eulerRhs, torus_nComp_glink, torus_fcard_edge, hN, hF,
    Fintype.card_fin]

end Examples

end Hypermap

end FourColor
