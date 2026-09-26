/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Fast.Hubcap
import FourColor.Fast.Prune

/-!
# Soundness of the fast leaf checks

The fast checks of `FourColor.Fast.Hubcap` with the certificate-guided reducibility check
`redpartFast (qztPruneFast qt m)` of `FourColor.Fast.Prune`, in the form that the presentation
checks use (Coq `present.v`: `succeed_by_reducibility`, `succeed_by_hubcap`; Coq
`unavoidability.v`: `check_dbound1P`):

* `Hypermap.no_fit_redpartFast_pruneFast` (in `FourColor.Fast.Prune`): the Reducible check;
* `Hypermap.hubcapFast_prune_sound`: the Hubcap check (Coq `hubcap_fit_bound` with
  `the_redpart`);
* `Hypermap.checkDbound1Fast_prune_sound`: the source bound check (Coq `check_dbound1P` with
  `the_redpart`).

Each hypothesis `h` is a closed boolean equation, meant to be proved by `decide +kernel`; `qt`
is the quiz tree of the configurations (`theQuizTree`), of which no quiz fits a minimal
counterexample (Coq `no_fit_the_redpart`), and `m` is any mask
(`FourColor.PruneGen.hubcapMask` computes a good one).
-/

namespace FourColor.Hypermap

universe u

variable {D : Type u} {G : Hypermap D}

/-- The fast Hubcap check is sound: Coq `hubcap_fit_bound` for the reducibility check
`redpartFast (qztPruneFast qt m)` (the conclusion `~~ exact_fitp x p`). -/
theorem hubcapFast_prune_sound [Fintype D] (hG : G.PlainCubicPentagonal) {qt : QuizTree}
    (fit'qt : ∀ y : D, ¬ G.QztFit y qt) (m : QztMask) {nhub : ℕ} (rf : DruleFork nhub) {x : D}
    {p : Part} {hc : Hubcap} (Ep : sizePart p = nhub) (pos_x : 0 < G.dscore x)
    (h : (hubcapCoverFast nhub hc && hubcapFitFast nhub (redpartFast (qztPruneFast qt m))
      rf.sourceDrules rf.targetDrules p hc) = true) :
    G.exactFitp x p = false := by
  rw [hubcapCoverFast_eq, hubcapFitFast_eq] at h
  exact G.hubcap_fit_bound hG (fun y q hq => no_fit_redpartFast_pruneFast hG fit'qt m q hq y) Ep
    pos_x h

/-- The fast source bound check is sound: Coq `check_dbound1P` for the reducibility check
`redpartFast (qztPruneFast qt m)`. -/
theorem checkDbound1Fast_prune_sound [Finite D] (hG : G.PlainCubicPentagonal) {qt : QuizTree}
    (fit'qt : ∀ y : D, ¬ G.QztFit y qt) (m : QztMask) {nhub : ℕ} (rf : DruleFork nhub) {x : D}
    {p : Part} {ns : ℕ} (nFx : G.arity x = nhub) (fit_xp : G.exactFitp x p = true)
    (h : checkDbound1Fast (redpartFast (qztPruneFast qt m)) rf.sourceDrules p ns = true) :
    G.dbound1 rf.sourceDrules x ≤ ns := by
  rw [checkDbound1Fast_eq] at h
  exact G.check_dbound1P (fun y q hq => no_fit_redpartFast_pruneFast hG fit'qt m q hq y) nFx
    fit_xp h

end FourColor.Hypermap
