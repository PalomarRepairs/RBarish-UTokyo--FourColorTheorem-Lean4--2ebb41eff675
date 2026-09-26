/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.QuizData.Quizzes1
import FourColor.QuizData.Quizzes2
import FourColor.QuizData.Quizzes3
import FourColor.QuizData.Quizzes4

/-!
# The precomputed quiz tree (Coq `the_quiz_tree`)

Coq's `present.v` defines `the_quiz_tree := Eval vm_compute in cfquiz_tree the_configs`. Here
`theQuizTree` is the same value as a literal, added by `#quizdata_tree`, and `theQuizTree_eq`
proves `theQuizTree = cfquizTree theConfigs` by kernel computation, in two parts:

1. `cfquiz_cfNNN : cfquiz cfNNN = qzNNN` for each configuration (`FourColor.QuizData.Quizzes1`
   to `Quizzes4`, one declaration per configuration), assembled here into
   `map_cfquiz_theConfigs : theConfigs.map cfquiz = theQuizBlocks.flatten`, where
   `theQuizBlocks` lists the literal quizzes `qzNNN` in blocks of 32 (`#quizdata_blocks`; the
   blocks keep the terms and the proofs shallow);
2. `theQuizTree_check`: the tree built from the literal quizzes by `qztBuild` (the strict version
   of `cfquizTreeRec`) is `theQuizTree`, one declaration.

The literal is a term of about 44,000 nodes (3361 question triples in 69 leaf lists, the longest
of which has 239 triples), at most about 250 levels deep.
-/

namespace FourColor

#quizdata_tree theQuizTree

namespace QuizData

#quizdata_blocks theConfigBlocks theQuizBlocks 32

set_option maxRecDepth 8192 in
theorem theConfigs_eq_flatten : theConfigs = theConfigBlocks.flatten := by
  rfl

theorem map_cfquiz_theConfigBlocks :
    theConfigBlocks.map (List.map cfquiz) = theQuizBlocks := by
  simp only [theConfigBlocks, theQuizBlocks, List.map_cons, List.map_nil, quizdata_cfquiz]

theorem map_cfquiz_theConfigs : theConfigs.map cfquiz = theQuizBlocks.flatten := by
  rw [theConfigs_eq_flatten, List.map_flatten, map_cfquiz_theConfigBlocks]

/-- The kernel check of the quiz tree: storing the literal quizzes of the configurations gives
the literal tree. -/
theorem theQuizTree_check :
    quizTreeBeq (qztBuild qztEmpty theConfigs theQuizBlocks.flatten) theQuizTree = true := by
  decide +kernel

end QuizData

/-- The precomputed quiz tree is the quiz tree of the 633 configurations (Coq defines
`the_quiz_tree` as `Eval vm_compute in cfquiz_tree the_configs`, so this holds by conversion
there). -/
theorem theQuizTree_eq : theQuizTree = cfquizTree theConfigs := by
  rw [cfquizTree, QuizData.cfquizTreeRec_eq_qztBuild, QuizData.map_cfquiz_theConfigs]
  exact (QuizData.eq_of_quizTreeBeq QuizData.theQuizTree_check).symm

end FourColor
