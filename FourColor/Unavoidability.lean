/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Present.P5.Exclude
import FourColor.Present.P6.Exclude
import FourColor.Present.P7.Exclude
import FourColor.Present.P8.Exclude
import FourColor.Present.P9.Exclude
import FourColor.Present.P10.Exclude
import FourColor.Present.P11.Exclude

/-!
# The unavoidability theorem (port of `unavoidability.v`)

Reducibility implies that there is no minimal counter-example, collating the results of the
seven presentations `exclude5` … `exclude11` (`FourColor/Present/P5` … `P11`).

A minimal counter-example `G` has a dart `x` of positive discharge score (`posz_dscore`), whose
face has at least five sides (`G` is pentagonal).  Every dart receives at most five units of
charge from each of its neighbouring faces (`dscore1 y ≤ 5`): for a neighbouring face of size
`n` the charge is the `dbound1` of the drule fork of hub size `n` (`dbound1_eq`), which is `0`
when `n` is outside `5 … 8` (`source_drules_range`) and is bounded by `check_dbound1P` otherwise
(the checks `checkDbound1 theRedpart (theDruleFork n) (pcons_ n) 5` for `n = 5 … 8` are
evaluated by the kernel).  So the face of `x` has fewer than twelve sides (`dscore_cap1`),
and the presentations exclude the arities `5 … 11`.

| Coq | Lean |
|---|---|
| `unavoidability` | `FourColor.unavoidability` |
| (the four `check_dbound1` computations, by conversion) | `check_dbound1_five` … `check_dbound1_eight` |
-/

namespace FourColor

universe u

/-! ### The charge bound for hub sizes 5 to 8 (kernel evaluation) -/

/-- Coq (by conversion in `unavoidability`): the charge bound for hub size 5. -/
theorem check_dbound1_five : checkDbound1 theRedpart (theDruleFork 5) (pcons_ 5) 5 = true := by
  decide +kernel

/-- Coq (by conversion in `unavoidability`): the charge bound for hub size 6. -/
theorem check_dbound1_six : checkDbound1 theRedpart (theDruleFork 6) (pcons_ 6) 5 = true := by
  decide +kernel

/-- Coq (by conversion in `unavoidability`): the charge bound for hub size 7. -/
theorem check_dbound1_seven : checkDbound1 theRedpart (theDruleFork 7) (pcons_ 7) 5 = true := by
  decide +kernel

/-- Coq (by conversion in `unavoidability`): the charge bound for hub size 8. -/
theorem check_dbound1_eight : checkDbound1 theRedpart (theDruleFork 8) (pcons_ 8) 5 = true := by
  decide +kernel

/-- The charge bound for the hub sizes of the range `5 … 8`. -/
theorem check_dbound1_range {n : ℕ} (hn : memRange .pr58 n = true) :
    checkDbound1 theRedpart (theDruleFork n) (pcons_ n) 5 = true := by
  have h : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by
    simp only [memRange, Bool.or_eq_true, beq_iff_eq] at hn
    omega
  rcases h with rfl | rfl | rfl | rfl
  · exact check_dbound1_five
  · exact check_dbound1_six
  · exact check_dbound1_seven
  · exact check_dbound1_eight

/-! ### Unavoidability -/

/-- Every dart of a minimal counter-example receives at most five units of charge from the face
of its `face ∘ face` predecessor (the bound `ub_m` of `dscore_cap1` in Coq's proof). -/
theorem dscore1_le_five (red_check : Reducibility) {D : Type u} [Fintype D]
    {G : Hypermap D} (cexG : G.MinimalCounterExample) (y : D) : G.dscore1 y ≤ 5 := by
  classical
  have pcp := Hypermap.minimal_counter_example_is_plain_cubic_pentagonal cexG
  -- `y = face (face x)` for `x = face⁻² y`
  have hy : G.face (G.face (G.invFace2 y)) = y := by
    simp only [Hypermap.invFace2, G.nodeK]
  rw [← hy]
  set x := G.invFace2 y
  set n := G.arity x
  rw [G.dbound1_eq (theDruleFork n) rfl]
  by_cases Dn : memRange .pr58 n = true
  · have fit_x : G.exactFitp x (pcons_ n) = true := G.exact_fitp_pcons_ pcp.pentagonal x
    have := G.check_dbound1P (no_fit_the_redpart red_check cexG) (rfl : G.arity x = n) fit_x
      (check_dbound1_range Dn)
    exact_mod_cast this
  · rw [Hypermap.source_drules_range (theDruleFork n) Dn]
    simp [Hypermap.dbound1]

/-- Coq `unavoidability`: reducibility implies that there is no minimal counter-example. -/
theorem unavoidability (red_check : Reducibility) {D : Type u} [Fintype D] (G : Hypermap D) :
    ¬ G.MinimalCounterExample := by
  intro cexG
  classical
  have pcp := Hypermap.minimal_counter_example_is_plain_cubic_pentagonal cexG
  obtain ⟨x, pos_x⟩ := G.posz_dscore cexG.toPlanarPlainCubicConnected
  have x_ok : G.ValidHub x := ⟨cexG, pos_x⟩
  have h5 : 5 ≤ G.arity x := pcp.pentagonal x
  have h12 : G.arity x < 12 :=
    G.dscore_cap1 5 (dscore1_le_five red_check cexG) x pos_x 12 (by norm_num)
  have e5 := exclude5 red_check G x x_ok
  have e6 := exclude6 red_check G x x_ok
  have e7 := exclude7 red_check G x x_ok
  have e8 := exclude8 red_check G x x_ok
  have e9 := exclude9 red_check G x x_ok
  have e10 := exclude10 red_check G x x_ok
  have e11 := exclude11 red_check G x x_ok
  omega

end FourColor
