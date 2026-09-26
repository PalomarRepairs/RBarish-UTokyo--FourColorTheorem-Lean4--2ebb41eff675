/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Fast.Part
import FourColor.Fast.RedPart
import FourColor.Fast.Prune
import FourColor.Fast.Hubcap
import FourColor.Fast.PruneGen
import FourColor.Fast.Sound

/-!
# Kernel-fast leaf checks of the presentations

Umbrella module for the kernel-fast versions of the checks that the presentation scripts
(Coq `present.v`, `presentN.v`) evaluate, each proved equal to its faithful definition (or, for
the certificate-guided check, proved sound):

* `FourColor.Fast.Part`: the part operations (`cmpPartFast`, `meetPartFast`, `rotPartFast`,
  `splitPartFast`, `goodSplitFast`, ..., each with `_eq`).
* `FourColor.Fast.RedPart`: `redpartFast` with `redpartFast_eq : redpartFast qt p = redpart qt p`,
  and fast versions of every function of the search (zipper moves, popping, quiz matching,
  quiz-tree lookups), each with `_eq`.
* `FourColor.Fast.Prune`: certificate-guided `redpart`: pruning masks `QztMask`, pruned quiz trees
  `qztPrune`, and the soundness theorem `Hypermap.no_fit_redpartFast_prune`: if
  `redpartFast (qztPrune qt m) p` then no dart fits `p` exactly, when no quiz of `qt` fits.
* `FourColor.Fast.Hubcap`: the hubcap checks `checkDbound1Fast`, `checkDbound2Fast`,
  `check2Dbound2Fast`, `checkUnfitFast`, `hubcapFitFast`, `hubcapCoverFast` (and their loops), and
  the similarity test `similarCheckFast`, each with `_eq`.
* `FourColor.Fast.PruneGen`: native (computable) functions computing the pruning masks of the
  checks (`PruneGen.redpartMask`, `PruneGen.hubcapMask`); not used in proofs.

## How a presentation leaf is checked

With `qt = theQuizTree`, `n = sizePart p`, `rs`, `rt` the literal rule lists of
`theDruleFork n` (`QuizData.sourceDrulesN`, `QuizData.targetDrulesN`), and `m` the leaf's mask
(`PruneGen.redpartMask qt p`, resp. `PruneGen.hubcapMask qt (theDruleFork n) p hc`):

* Reducible: `redpartFast (qztPruneFast qt m) p = true` by `decide +kernel`, then
  `Hypermap.no_fit_redpartFast_pruneFast` (instead of Coq's `no_fit_the_redpart`).
* Hubcap: `(hubcapCoverFast n hc && hubcapFitFast n (redpartFast (qztPruneFast qt m)) rs rt p hc)
  = true` by `decide +kernel`, then `Hypermap.hubcapFast_prune_sound` (Coq `hubcap_fit_bound`).
  A heavy check can be split over several declarations with the unfolding lemmas
  `checkDbound2Fast_of_rec`, `check2Dbound2Fast_of_rec`, `checkDbound2RecFast_succ_cons`,
  `check2Dbound2RecFast_succ_cons` and `check2Dbound2RecFast_succ_nil_cons` (all `rfl` or
  closed-equation lemmas).
* Similar: `similarCheckFast ps p j mir = true`, then `similarCheckFast_eq` and
  `similarCheck_iff` give the side condition of Coq's `succeed_by_similarity`.
* Pcase: `goodSplitFast`, `splitPartFast` (`FourColor.Fast.Part`).
* The source bound of Coq `unavoidability.v`: `checkDbound1Fast` with
  `Hypermap.checkDbound1Fast_prune_sound` (Coq `check_dbound1P`).

## Measured costs (Lean v4.35.0-rc2, kernel time at build)

On leaves of the real presentations, faithful → fast → fast with the pruned quiz tree:

* Reducible leaves (three leaves, the last one the most expensive): 5.4 / 69.8 / 230 ms →
  0.9 / 5.5 / 20.7 ms → 1.6 / 4.0 / 6.0 ms (`qztPrune`; with `qztPruneFast` about 40% less);
* Hubcap leaves at the 10th, 50th, 75th and 95th percentiles of cost: 514 / 1,490 / 3,160 /
  10,900 ms → 44 / 175 / 355 / 1,090 ms → 42 / 123 / 114 / 395 ms (`qztPrune`; `qztPruneFast` is
  about 7–13% faster); the heaviest leaf (one dual constraint) 30.4 s fast, 22 s pruned;
* Similar: 3.2 → 0.5 ms; `check_dbound1` for the hub sizes 5 to 8: 1.54 s → 0.16 s → 0.13 s.

On sample Hubcap leaves of 6.6k, 21k, 46k and 92k native operations: faithful 461 / 1,550 /
2,510 / 6,460 ms, fast 57 / 164 / 354 / 751 ms, pruned 44 / 73 / 83 / 257 ms.

Extrapolated over all the leaves (stratified sample of 62 of the 5,274 Hubcap leaves, ratio
estimator on their native cost, three runs): Hubcap leaves ≈ 1,450 s ± 10% with the pruned tree
(≈ 2,700 s without pruning, ≈ 950 s for the hubcap computations alone), Reducible ≈ 3–5 s, Similar
≈ 0.3 s: about 0.4 h (the faithful checks are about 10 times slower than the fast ones on the
sampled leaves, about 7.5 h in all). These are for one leaf per declaration: 12 leaves in one
declaration cost 1.1–1.8 times the sum of their separate costs
(2 to 4 leaves: no measurable difference), so declarations should stay around a second.

Palomar's checkers (`scripts/palomar_check.sh --jobs 1`), on 19 such checks (14.0 s of kernel
time at build): `leanchecker` 12.5 s, nanoda 4.7 s, con-ron 25.2 s (its fixed start is about 7 s),
all accepting; on a heavy Hubcap leaf (11 s at build): 12.1 s (1.55 GB), 5.2 s, 18.4 s.
-/
