/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.QuizData.Lit

/-!
# The precomputed drule forks (Coq `the_drule_fork`)

Coq's `present.v` defines `the_drule_fork_template n : drule_fork n`, the fork
`DruleFork (DruleForkValues _)` whose rule lists are `pick_source_drules n the_drules` and
`pick_target_drules n the_drules` (computed on demand), and
`the_drule_fork := Eval vm_compute in the_drule_fork_template`, where these lists are
precomputed for the hub sizes below 12. Here:

* `theDruleForkTemplate n` is the template, and `theDruleFork n` is the precomputed fork: for
  `5 ≤ n ≤ 11` its rule lists are the literals `sourceDrulesN` and `targetDrulesN` (added by
  `#quizdata_drules`); for the other hub sizes it is the template (the hub sizes below 5 do not
  occur, and their rule lists are empty).
* `pickSourceDrules_N : pickSourceDrules N theDrules = sourceDrulesN` and
  `pickTargetDrules_N : pickTargetDrules N theDrules = targetDrulesN` are checked by the kernel,
  one declaration each; they give the `values` field of the literal forks `theDruleForkN`.
* `theDruleFork_eq n : theDruleFork n = theDruleForkTemplate n`, and the rule lists of
  `theDruleFork n` are `pickSourceDrules n theDrules` and `pickTargetDrules n theDrules`
  (`theDruleFork_sourceDrules`, `theDruleFork_targetDrules`), as for any `DruleFork n`.

The rule lists have 6/0, 14/12, 40/67, 11/57, 0/57, 0/57 and 0/57 parts for the hub sizes 5 to 11.
-/

namespace FourColor

/-- Coq `the_drule_fork_template n`: the drule fork for hub size `n`, with its rule lists
`pickSourceDrules n theDrules` and `pickTargetDrules n theDrules` not precomputed. -/
def theDruleForkTemplate (n : ℕ) : DruleFork n := ⟨_, _, .mk⟩

/-- A drule fork is determined by its hub size: every `rf : DruleFork n` is
`theDruleForkTemplate n`. -/
theorem DruleFork.eq_template {n : ℕ} (rf : DruleFork n) : rf = theDruleForkTemplate n := by
  obtain ⟨_, _, ⟨⟩⟩ := rf
  rfl

namespace QuizData

#quizdata_drules sourceDrules5 5 source
#quizdata_drules targetDrules5 5 target
#quizdata_drules sourceDrules6 6 source
#quizdata_drules targetDrules6 6 target
#quizdata_drules sourceDrules7 7 source
#quizdata_drules targetDrules7 7 target
#quizdata_drules sourceDrules8 8 source
#quizdata_drules targetDrules8 8 target
#quizdata_drules sourceDrules9 9 source
#quizdata_drules targetDrules9 9 target
#quizdata_drules sourceDrules10 10 source
#quizdata_drules targetDrules10 10 target
#quizdata_drules sourceDrules11 11 source
#quizdata_drules targetDrules11 11 target

theorem pickSourceDrules_5 : pickSourceDrules 5 theDrules = sourceDrules5 := by decide +kernel
theorem pickTargetDrules_5 : pickTargetDrules 5 theDrules = targetDrules5 := by decide +kernel
theorem pickSourceDrules_6 : pickSourceDrules 6 theDrules = sourceDrules6 := by decide +kernel
theorem pickTargetDrules_6 : pickTargetDrules 6 theDrules = targetDrules6 := by decide +kernel
theorem pickSourceDrules_7 : pickSourceDrules 7 theDrules = sourceDrules7 := by decide +kernel
theorem pickTargetDrules_7 : pickTargetDrules 7 theDrules = targetDrules7 := by decide +kernel
theorem pickSourceDrules_8 : pickSourceDrules 8 theDrules = sourceDrules8 := by decide +kernel
theorem pickTargetDrules_8 : pickTargetDrules 8 theDrules = targetDrules8 := by decide +kernel
theorem pickSourceDrules_9 : pickSourceDrules 9 theDrules = sourceDrules9 := by decide +kernel
theorem pickTargetDrules_9 : pickTargetDrules 9 theDrules = targetDrules9 := by decide +kernel
theorem pickSourceDrules_10 : pickSourceDrules 10 theDrules = sourceDrules10 := by
  decide +kernel
theorem pickTargetDrules_10 : pickTargetDrules 10 theDrules = targetDrules10 := by
  decide +kernel
theorem pickSourceDrules_11 : pickSourceDrules 11 theDrules = sourceDrules11 := by
  decide +kernel
theorem pickTargetDrules_11 : pickTargetDrules 11 theDrules = targetDrules11 := by
  decide +kernel

/-- The drule fork for hub size 5, with literal rule lists. -/
def theDruleFork5 : DruleFork 5 :=
  ⟨sourceDrules5, targetDrules5, pickSourceDrules_5 ▸ pickTargetDrules_5 ▸ .mk⟩

/-- The drule fork for hub size 6, with literal rule lists. -/
def theDruleFork6 : DruleFork 6 :=
  ⟨sourceDrules6, targetDrules6, pickSourceDrules_6 ▸ pickTargetDrules_6 ▸ .mk⟩

/-- The drule fork for hub size 7, with literal rule lists. -/
def theDruleFork7 : DruleFork 7 :=
  ⟨sourceDrules7, targetDrules7, pickSourceDrules_7 ▸ pickTargetDrules_7 ▸ .mk⟩

/-- The drule fork for hub size 8, with literal rule lists. -/
def theDruleFork8 : DruleFork 8 :=
  ⟨sourceDrules8, targetDrules8, pickSourceDrules_8 ▸ pickTargetDrules_8 ▸ .mk⟩

/-- The drule fork for hub size 9, with literal rule lists. -/
def theDruleFork9 : DruleFork 9 :=
  ⟨sourceDrules9, targetDrules9, pickSourceDrules_9 ▸ pickTargetDrules_9 ▸ .mk⟩

/-- The drule fork for hub size 10, with literal rule lists. -/
def theDruleFork10 : DruleFork 10 :=
  ⟨sourceDrules10, targetDrules10, pickSourceDrules_10 ▸ pickTargetDrules_10 ▸ .mk⟩

/-- The drule fork for hub size 11, with literal rule lists. -/
def theDruleFork11 : DruleFork 11 :=
  ⟨sourceDrules11, targetDrules11, pickSourceDrules_11 ▸ pickTargetDrules_11 ▸ .mk⟩

end QuizData

/-- Coq `the_drule_fork` (`Eval vm_compute in the_drule_fork_template`): the drule forks, with
literal rule lists for the hub sizes 5 to 11 (`QuizData.theDruleFork5`, ...,
`QuizData.theDruleFork11`), and `theDruleForkTemplate n` for the other hub sizes. -/
def theDruleFork : (n : ℕ) → DruleFork n
  | 5 => QuizData.theDruleFork5
  | 6 => QuizData.theDruleFork6
  | 7 => QuizData.theDruleFork7
  | 8 => QuizData.theDruleFork8
  | 9 => QuizData.theDruleFork9
  | 10 => QuizData.theDruleFork10
  | 11 => QuizData.theDruleFork11
  | n => theDruleForkTemplate n

/-- The precomputed drule forks are the forks of the template (Coq: by conversion). -/
theorem theDruleFork_eq (n : ℕ) : theDruleFork n = theDruleForkTemplate n :=
  DruleFork.eq_template _

theorem theDruleFork_sourceDrules (n : ℕ) :
    (theDruleFork n).sourceDrules = pickSourceDrules n theDrules :=
  DruleFork.sourceDrules_eq _

theorem theDruleFork_targetDrules (n : ℕ) :
    (theDruleFork n).targetDrules = pickTargetDrules n theDrules :=
  DruleFork.targetDrules_eq _

theorem theDruleFork_five : theDruleFork 5 = QuizData.theDruleFork5 := rfl
theorem theDruleFork_six : theDruleFork 6 = QuizData.theDruleFork6 := rfl
theorem theDruleFork_seven : theDruleFork 7 = QuizData.theDruleFork7 := rfl
theorem theDruleFork_eight : theDruleFork 8 = QuizData.theDruleFork8 := rfl
theorem theDruleFork_nine : theDruleFork 9 = QuizData.theDruleFork9 := rfl
theorem theDruleFork_ten : theDruleFork 10 = QuizData.theDruleFork10 := rfl
theorem theDruleFork_eleven : theDruleFork 11 = QuizData.theDruleFork11 := rfl

end FourColor
