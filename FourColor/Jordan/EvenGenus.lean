/-
Copyright (c) 2026. Lean 4 port of the planarity part of the Coq/Rocq formal proof
of the Four Color Theorem by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Walkup.Genus

/-!
# The genus formula has no truncation  (port of `jordan.v`, `even_genusP` and `Euler_le`)
-/

namespace FourColor

open Function

universe u

namespace Hypermap

variable {D : Type u}

theorem nComp_univ_of_isEmpty [IsEmpty D] (e : D → D → Prop) : nComp e Set.univ = 0 := by
  rw [nComp_eq_zero]
  exact Set.univ_eq_empty_iff.2 inferInstance

theorem eulerLhs_of_isEmpty [Fintype D] [IsEmpty D] (G : Hypermap D) : G.eulerLhs = 0 := by
  simp [eulerLhs, nComp_univ_of_isEmpty, Fintype.card_eq_zero]

theorem eulerRhs_of_isEmpty [Fintype D] [IsEmpty D] (G : Hypermap D) : G.eulerRhs = 0 := by
  simp [eulerRhs, fcard, nComp_univ_of_isEmpty]

theorem genus_of_isEmpty [Fintype D] [IsEmpty D] (G : Hypermap D) : G.genus = 0 := by
  simp [genus, eulerLhs_of_isEmpty, eulerRhs_of_isEmpty]

/-- math-comp `even_genusP`: there is never any truncation in the genus formula. -/
theorem evenGenus [Fintype D] (G : Hypermap D) : G.EvenGenus := by
  classical
  suffices h : ∀ (n : ℕ) (D : Type u) [Fintype D] [DecidableEq D] (G : Hypermap D),
      Fintype.card D ≤ n → G.EvenGenus from h _ D G le_rfl
  intro n
  induction n with
  | zero =>
    intro D _ _ G hn
    have : IsEmpty D := Fintype.card_eq_zero_iff.1 (Nat.le_zero.1 hn)
    unfold EvenGenus
    rw [eulerLhs_of_isEmpty, eulerRhs_of_isEmpty, genus_of_isEmpty]
  | succ n ih =>
    intro D _ _ G hn
    by_cases hD : IsEmpty D
    · unfold EvenGenus
      rw [eulerLhs_of_isEmpty, eulerRhs_of_isEmpty, genus_of_isEmpty]
    · obtain ⟨z⟩ := not_isEmpty_iff.1 hD
      apply even_genus_WalkupE G z
      apply ih
      have := card_S_Walkup z
      omega

/-- math-comp `Euler_le`: the Euler inequality. -/
theorem euler_le [Fintype D] (G : Hypermap D) : G.eulerRhs ≤ G.eulerLhs := by
  have := G.evenGenus
  unfold EvenGenus at this
  omega

end Hypermap

end FourColor
