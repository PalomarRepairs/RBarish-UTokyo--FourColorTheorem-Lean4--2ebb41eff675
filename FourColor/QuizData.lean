/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.QuizData.Tree
import FourColor.QuizData.Forks

/-!
# The precomputed quiz tree and drule forks (from Coq's `present.v`)

Coq's `present.v` uses two values computed with `Eval vm_compute`: `the_quiz_tree`, the fully
evaluated quiz tree of the 633 configurations, and `the_drule_fork n`, the drule forks for the hub
sizes below 12. Here they are literals, added by meta code (`FourColor.QuizData.Lit`: the value is
computed at elaboration time, turned into an `Expr` and added with `addDecl`), and proved equal to
the computed values by the kernel:

* `theQuizTree : QuizTree` (Coq `the_quiz_tree`), with
  `theQuizTree_eq : theQuizTree = cfquizTree theConfigs` (`FourColor.QuizData.Tree`);
* `theDruleFork : (n : ℕ) → DruleFork n` (Coq `the_drule_fork`), with literal rule lists for the
  hub sizes 5 to 11, and `theDruleFork_eq : theDruleFork n = theDruleForkTemplate n`
  (`FourColor.QuizData.Forks`; Coq `the_drule_fork_template`).

## How the quiz tree is checked

The kernel cannot evaluate `cfquizTree theConfigs` in one declaration within Palomar's limits
(about 1 GB and 30 s per declaration), and its cost is
superlinear in the size of a declaration. So:

1. For each configuration, `cfquiz_cfNNN : cfquiz cfNNN = qzNNN` compares its quiz with a literal
   (`FourColor.QuizData.Quizzes1` to `Quizzes4`, 633 declarations). The radius test of `cfquiz`,
   which dominates its cost, is given the successful kernel face as a certificate
   (`FourColor.QuizData.cfquizCheck`), which removes its failed tries (547 of the 1180 tries
   over the 633 configurations; this cut the kernel time of the quiz checks from 97 s to 55 s).
2. `theQuizTree_check` builds the tree from the 633 literal quizzes with strict, recursor-style
   versions of the store functions (`FourColor.QuizData.qztBuild`) and compares it with the
   literal tree, in one declaration.
3. `theQuizTree_eq` combines them with `cfquizTreeRec_eq_qztBuild`.

The modules, in dependency order: `QuizData.Basic` (functions and lemmas, no data),
`QuizData.Lit` (meta code), `QuizData.Quizzes1` to `QuizData.Quizzes4`, `QuizData.Tree`,
`QuizData.Forks`.

## Costs (Lean v4.35.0-rc2)

* Kernel time at build time: 50.6 s for the 633 quiz checks (at most 0.25 s and a few tens of MB
  per declaration), 2.1 s for `theQuizTree_check` (about 220 MB), 3.8 s for the 14 fork checks
  (at most 0.4 s each).
* Palomar's checkers on `theQuizTree_eq` and `theDruleFork_eq` (with all their dependencies):
  `leanchecker` 57 s (357 MB), nanoda 46 s (320 MB), con-ron 100 s wall and 130 s CPU (562 MB).
-/
