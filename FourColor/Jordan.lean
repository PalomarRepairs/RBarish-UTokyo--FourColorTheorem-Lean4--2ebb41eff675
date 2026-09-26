/-
Copyright (c) 2026. Lean 4 port of the planarity part of the Coq/Rocq formal proof
of the Four Color Theorem by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Jordan.EvenGenus
import FourColor.Jordan.PlanarJordan
import FourColor.Jordan.EulerTree
import FourColor.Walkup.Jordan

/-!
# The Jordan characterization of planarity  (port of `jordan.v`)

This file proves the validity of our Jordan curve theorem inspired combinatorial
characterization of planarity: a hypermap is planar (satisfies the Euler formula, i.e. has
genus `0`) if and only if it has no Moebius paths.

* `Hypermap.evenGenus`       : math-comp `even_genusP`
* `Hypermap.euler_le`        : math-comp `Euler_le`
* `Hypermap.jordan_of_planar`: math-comp `planar_Jordan`
* `Hypermap.euler_tree`      : math-comp `Euler_tree`
* `Hypermap.planar_of_jordan`: math-comp `Jordan_planar`
* `Hypermap.planar_iff_jordan`: math-comp `planarP`
-/

namespace FourColor

open Function

universe u

namespace Hypermap

variable {D : Type u}

/-- math-comp `Jordan_planar`. -/
theorem planar_of_jordan [Fintype D] (G : Hypermap D) (hG : G.Jordan) : G.Planar := by
  classical
  suffices h : ∀ (n : ℕ) (D : Type u) [Fintype D] [DecidableEq D] (G : Hypermap D),
      Fintype.card D ≤ n → G.Jordan → G.Planar from h _ D G le_rfl hG
  intro n
  induction n with
  | zero =>
    intro D _ _ G hn _
    have : IsEmpty D := Fintype.card_eq_zero_iff.1 (Nat.le_zero.1 hn)
    exact genus_of_isEmpty G
  | succ n ih =>
    intro D _ _ G hn hJ
    by_cases hD : IsEmpty D
    · exact genus_of_isEmpty G
    · obtain ⟨x⟩ := not_isEmpty_iff.1 hD
      obtain ⟨z, -, hz⟩ := euler_tree G x hJ
      have hg : G.glink z z ∨ ¬ G.crossEdge z := by
        rcases hz with (h | h) | h
        · exact Or.inl (Or.inr (Or.inl h.symm))
        · exact Or.inl (Or.inr (Or.inr h))
        · exact Or.inr h
      unfold Planar
      rw [← G.genus_WalkupE_eq z hg]
      exact ih _ (G.WalkupE z) (by have := card_S_Walkup z; omega) (G.jordan_WalkupE z hJ)

/-- math-comp `planarP`: the Euler-formula and Jordan-property characterizations of planarity
coincide. -/
theorem planar_iff_jordan [Fintype D] (G : Hypermap D) : G.Planar ↔ G.Jordan :=
  ⟨G.jordan_of_planar, G.planar_of_jordan⟩

end Hypermap

end FourColor
