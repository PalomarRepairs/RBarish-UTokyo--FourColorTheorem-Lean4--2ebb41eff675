/-
Copyright (c) 2026. Lean 4 port of the planarity part of the Coq/Rocq formal proof
of the Four Color Theorem by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Walkup.Edge
import FourColor.Walkup.Comp

/-!
# The Walkup construction: genus  (port of `walkup.v`, part 4)

Both sides of the Euler formula change in a controlled way under `WalkupE`
(`euler_lhs_WalkupE`, `euler_rhs_WalkupE`), so the genus can only decrease, and is invariant
when `z` is degenerate or `z` and `node z` lie on different edge cycles.
-/

namespace FourColor

open Function

universe u

namespace Hypermap

variable {D : Type u} [Fintype D] [DecidableEq D] (G : Hypermap D) (z : D)

/-- math-comp `genus_WalkupE_eq`. -/
theorem genus_WalkupE_eq (h : G.glink z z ∨ ¬ G.crossEdge z) :
    (G.WalkupE z).genus = G.genus := by
  have hL := G.euler_lhs_WalkupE z
  have hR := G.euler_rhs_WalkupE z
  have hab : G.nCompZ z (G.Disconnected z) = G.nCompZ z (G.crossEdge z) := by
    rcases h with h | h
    · simp only [nCompZ, h, ite_true]
    · have hd := G.not_cross_connected z h
      simp [nCompZ, hd, h]
  rw [hab] at hL
  unfold genus
  omega

/-- math-comp `le_genus_WalkupE`. -/
theorem le_genus_WalkupE : (G.WalkupE z).genus ≤ G.genus := by
  by_cases h : G.glink z z ∨ ¬ G.crossEdge z
  · exact (G.genus_WalkupE_eq z h).le
  · rw [not_or, not_not] at h
    obtain ⟨hg, hc⟩ := h
    have hL := G.euler_lhs_WalkupE z
    have hR := G.euler_rhs_WalkupE z
    have hb : G.nCompZ z (G.crossEdge z) = 0 := by simp [nCompZ, hg, hc]
    have ha : G.nCompZ z (G.Disconnected z) ≤ 1 := by
      unfold nCompZ
      rw [ite_eq_right hg]
      split_ifs <;> omega
    unfold genus
    omega

/-- math-comp `planar_WalkupE`. -/
theorem planar_WalkupE (hG : G.Planar) : (G.WalkupE z).Planar := by
  unfold Planar at *
  have := G.le_genus_WalkupE z
  omega

/-- math-comp `even_genus_WalkupE`. -/
theorem even_genus_WalkupE (h : (G.WalkupE z).EvenGenus) : G.EvenGenus := by
  have hL := G.euler_lhs_WalkupE z
  have hR := G.euler_rhs_WalkupE z
  have hab : G.nCompZ z (G.crossEdge z) ≤ G.nCompZ z (G.Disconnected z) := by
    by_cases hg : G.glink z z
    · simp only [nCompZ, hg, ite_true, le_refl]
    · by_cases hc : G.crossEdge z
      · simp [nCompZ, hg, hc]
      · have hd := G.not_cross_connected z hc
        simp [nCompZ, hg, hc, hd]
  unfold EvenGenus genus at *
  omega

/-- math-comp `planar_WalkupN`. -/
theorem planar_WalkupN (hG : G.Planar) : (G.WalkupN z).Planar := by
  unfold WalkupN
  rw [planar_permF]
  exact planar_WalkupE G.permN z ((G.planar_permN).2 hG)

/-- math-comp `planar_WalkupF`. -/
theorem planar_WalkupF (hG : G.Planar) : (G.WalkupF z).Planar := by
  unfold WalkupF
  rw [planar_permN]
  exact planar_WalkupE G.permF z ((G.planar_permF).2 hG)

end Hypermap

end FourColor
