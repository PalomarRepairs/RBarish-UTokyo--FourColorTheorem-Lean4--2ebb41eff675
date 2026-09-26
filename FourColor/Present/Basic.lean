/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Embed
import FourColor.CfReducible
import FourColor.QuizData
import FourColor.Fast
import FourColor.Birkhoff

/-!
# Presentations: the properties and the steps (port of `present.v`, first part)

The definitions and lemmas of Coq's `present.v`, which the presentation scripts `presentN.v`
apply through its tactic notations (`Presentation`, `Pcase`, `Reducible`, `Hubcap`, `Similar`):

* `Reducibility` (Coq `reducibility`): the 633 configurations of `theConfigs` are C-reducible,
  i.e. `ReducibleInRange 0 theConfigs.length theConfigs` (`FourColor.CfReducible`).
* `Hypermap.ValidHub G x` (Coq `valid_hub`): `G` is a minimal counter-example and the score of
  the face of `x` is positive.
* `ExcludedArity n` (Coq `excluded_arity`), `Successful p` (Coq `successful`),
  `ForcedPart p0 p` (Coq `forced_part`), `SucceedsIn p0 p` (Coq `succeeds_in`, the goals
  `Check p in p0` of the scripts).
* `exclude_arity` (the tactic `Presentation`), `succeed_by_split` (`Pcase`),
  `succeed_by_similarity` (`Similar`), `no_fit_the_redpart`, `succeed_by_reducibility`
  (`Reducible`) and `succeed_by_hubcap` (`Hubcap`), with `theRedpart` (Coq `the_redpart`,
  `redpart the_quiz_tree`), `theQuizTree` and `theDruleFork` (`FourColor.QuizData`).

Added here (not in Coq), for the kernel checks of `FourColor.Present.Tree`:

* `not_qztFit_theQuizTree`: no quiz of `theQuizTree` fits a minimal counter-example, assuming
  `Reducibility` (the core of the proof of Coq's `no_fit_the_redpart`);
* `successful_nil`: no valid hub fits the empty part;
* `succeed_by_reducibility_fast` and `succeed_by_hubcap_fast`: `succeed_by_reducibility` and
  `succeed_by_hubcap` with the fast checks of `FourColor.Fast` and a pruned quiz tree
  `qztPruneFast theQuizTree m` (any mask `m`), and, for the hubcaps, any drule fork
  `rf : DruleFork n` with `n = sizePart p`.

## Porting notes

* The Coq hypermap `G` bundles its finite dart type; here the quantifiers `forall G x` of
  `excluded_arity`, `successful` and `forced_part` are over a dart type `D : Type u` with a
  `Fintype` instance, a hypermap `G : Hypermap D` and a dart `x : D`, so these properties are
  universe-polymorphic (they take the universe `u` of the dart types). No `DecidableEq D`
  instance is required; the proofs use classical decidability where the Birkhoff theorem
  (`minimal_counter_example_is_plain_cubic_pentagonal`) needs it.
* `~~ exact_fitp x p` is `G.exactFitp x p = false`, as in `FourColor.Hubcap`, and
  `(arity x == n) = false` is `G.arity x ≠ n`.
* The statement-level `let`s of `succeed_by_split` and `succeed_by_similarity` are unfolded;
  the section hypotheses `ps_ok` and `red_check` are explicit arguments, in the order of Coq's
  `Arguments` declarations.
* Coq's `the_quiz_tree`, `the_drule_fork_template` and `the_drule_fork` are
  `theQuizTree`, `theDruleForkTemplate` and `theDruleFork` of `FourColor.QuizData`.
-/

namespace FourColor

open Hypermap

universe u

/-! ### The properties -/

/-- Coq `reducibility`: all the configurations of `theConfigs` are C-reducible. -/
def Reducibility : Prop := ReducibleInRange 0 theConfigs.length theConfigs

namespace Hypermap

/-- Coq `valid_hub G x`: `x` is a dart of a minimal counter-example `G`, and the face of `x`
has a positive discharge score. -/
def ValidHub {D : Type u} [Fintype D] (G : Hypermap D) (x : D) : Prop :=
  G.MinimalCounterExample ∧ 0 < G.dscore x

end Hypermap

/-- Coq `excluded_arity n`: assuming reducibility, no valid hub has arity `n`. -/
def ExcludedArity (n : ℕ) : Prop :=
  Reducibility → ∀ {D : Type u} [Fintype D] (G : Hypermap D) (x : D), G.ValidHub x →
    G.arity x ≠ n

/-- Coq `successful p`: no valid hub fits `p` exactly. -/
def Successful (p : Part) : Prop :=
  ∀ {D : Type u} [Fintype D] (G : Hypermap D) (x : D), G.ValidHub x → G.exactFitp x p = false

/-- Coq `forced_part p0 p`: every valid hub that fits `p0` exactly also fits `p` exactly. -/
def ForcedPart (p0 p : Part) : Prop :=
  ∀ {D : Type u} [Fintype D] (G : Hypermap D) (x : D), G.ValidHub x →
    G.exactFitp x p0 = true → G.exactFitp x p = true

/-- Coq `succeeds_in p0 p` (the goal `Check p in p0` of the presentation scripts): if `p0`
forces `p`, then `p` is successful. -/
def SucceedsIn (p0 p : Part) : Prop := ForcedPart.{u} p0 p → Successful.{u} p

/-- A valid hub is a dart of a plain cubic pentagonal map (Coq: the coercion
`minimal_counter_example_is_plain_cubic_pentagonal`). -/
theorem Hypermap.ValidHub.plainCubicPentagonal {D : Type u} [Fintype D] {G : Hypermap D} {x : D}
    (x_ok : G.ValidHub x) : G.PlainCubicPentagonal := by
  classical
  exact minimal_counter_example_is_plain_cubic_pentagonal x_ok.1

/-- Not in Coq: no valid hub fits the empty part (its arity is at least 5). -/
theorem successful_nil : Successful.{u} .nil := by
  intro D _ G x x_ok
  have h5 := x_ok.plainCubicPentagonal.pentagonal x
  simp only [exactFitp, sizePart, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
  exact Or.inl (by omega)

/-! ### Presentation -/

/-- Coq `exclude_arity` (the tactic `Presentation`): a presentation for hub size `n`, the goal
`Check pcons_ n in pcons_ n`, proves `ExcludedArity n`. -/
theorem exclude_arity (n : ℕ)
    (succ_p0_n : Reducibility → SucceedsIn.{u} (pcons_ n) (pcons_ n)) :
    ExcludedArity.{u} n := by
  intro red D _ G x x_ok hxn
  have h1 := G.exact_fitp_pcons_ x_ok.plainCubicPentagonal.pentagonal x
  rw [hxn] at h1
  have h2 := succ_p0_n red (fun _ _ _ h => h) G x x_ok
  rw [h1] at h2
  exact Bool.noConfusion h2

/-! ### Splitting and symmetry -/

/-- `fitp_split` for a valid hub. -/
private theorem validHub_fitp_split {D : Type u} [Fintype D] {G : Hypermap D} {x : D}
    (x_ok : G.ValidHub x) (i : SubpartLoc) (j k : ℕ) {q : Part} (hq : goodSplit i j k q = true)
    (lo : Bool) :
    G.exactFitp x (splitPart i j k lo q) = ((lo ^^ G.fitc i j k x) && G.exactFitp x q) :=
  G.fitp_split x_ok.plainCubicPentagonal.pentagonal i j k q hq lo x

/-- Coq `succeed_by_split` (the tactic `Pcase`, with `lo = true` for `i[j+1] <= k` and
`lo = false` for `i[j+1] > k`): with `pl`, `pr` the parts `p` refined by the assumption and by
its complement, and `p0l` the part `p0` refined by the assumption (or `pl` if that is not a good
split of `p0`), the goal `Check p in p0` follows from `Check pl in p0l` and, assuming
`successful p0l`, `Check pr in p0`. -/
theorem succeed_by_split (i : SubpartLoc) (j k : ℕ) (lo : Bool) {p0 p : Part}
    (p_ijk : goodSplit i j k p = true)
    (pl_ok : SucceedsIn.{u}
      (if goodSplit i j k p0 then splitPart i j k lo p0 else splitPart i j k lo p)
      (splitPart i j k lo p))
    (pr_ok : Successful.{u}
        (if goodSplit i j k p0 then splitPart i j k lo p0 else splitPart i j k lo p) →
      SucceedsIn.{u} p0 (splitPart i j k (!lo) p)) :
    SucceedsIn.{u} p0 p := by
  intro p0p
  have p0lpl : ForcedPart.{u}
      (if goodSplit i j k p0 then splitPart i j k lo p0 else splitPart i j k lo p)
      (splitPart i j k lo p) := by
    intro D _ G x x_ok h
    by_cases hg : goodSplit i j k p0 = true
    · rw [ite_eq_left hg, validHub_fitp_split x_ok i j k hg, Bool.and_eq_true] at h
      rw [validHub_fitp_split x_ok i j k p_ijk, Bool.and_eq_true]
      exact ⟨h.1, p0p G x x_ok h.2⟩
    · rwa [ite_eq_right hg] at h
  have pl_ok' : Successful.{u} (splitPart i j k lo p) := pl_ok p0lpl
  have pr_ok' : Successful.{u} (splitPart i j k (!lo) p) := by
    refine pr_ok ?_ ?_
    · intro D _ G x x_ok
      have hl := pl_ok' G x x_ok
      cases h : G.exactFitp x
          (if goodSplit i j k p0 then splitPart i j k lo p0 else splitPart i j k lo p)
      · rfl
      · rw [p0lpl G x x_ok h] at hl
        exact hl
    · intro D _ G x x_ok h0
      have hp := p0p G x x_ok h0
      have hl := pl_ok' G x x_ok
      rw [validHub_fitp_split x_ok i j k p_ijk, hp] at hl ⊢
      generalize G.fitc i j k x = c at hl ⊢
      cases lo <;> cases c <;> simp_all
  intro D _ G x x_ok
  have hl := pl_ok' G x x_ok
  have hr := pr_ok' G x x_ok
  rw [validHub_fitp_split x_ok i j k p_ijk] at hl hr
  generalize G.fitc i j k x = c at hl hr
  generalize G.exactFitp x p = b at hl hr ⊢
  cases lo <;> cases c <;> cases b <;> simp_all

/-- A part of size 0 is empty. -/
private theorem eq_nil_of_sizePart_eq_zero {q : Part} (h : sizePart q = 0) : q = .nil := by
  cases q <;> simp_all [sizePart]

/-- Rotating a part by more than its size does not change the fit. -/
private theorem fitp_rotPart_of_lt {D : Type u} (G : Hypermap D) {j : ℕ} {q : Part}
    (h : sizePart q < j) (x : D) : G.fitp x (rotPart j q) = G.fitp x q := by
  have hd : dropPart j q = .nil := by
    apply eq_nil_of_sizePart_eq_zero
    rw [size_drop_part]
    omega
  conv_rhs => rw [← cat_take_drop_part j q]
  rw [rotPart, G.fitp_cat, G.fitp_cat, hd]
  simp [fitp, sizePart]

/-- Coq `succeed_by_similarity` (the tactic `Similar to [*]L[j]`, `mir = true` for the mirror
form `*`): if `ps` is successful (the hypothesis `L`), and `p` (mirrored if `mir`) rotated by
`j` has the size of `ps` and is a subset of `ps`, then `Check p in p0` holds for any `p0`. -/
theorem succeed_by_similarity (j : ℕ) (mir : Bool) {ps : Part} (ps_ok : Successful.{u} ps)
    {p0 p : Part}
    (h : sizePart ps = sizePart (rotPart j (if mir then mirrorPart p else p)) ∧
      cmpPart (rotPart j (if mir then mirrorPart p else p)) ps = .subset) :
    SucceedsIn.{u} p0 p := by
  obtain ⟨Eps2, eq_p2ps⟩ := h
  intro _ D _ G x x_ok
  cases fit_p : G.exactFitp x p
  · rfl
  exfalso
  obtain ⟨cexG, pos_x⟩ := x_ok
  have hPCC := minimal_counter_example_is_planar_plain_cubic_connected cexG
  have hPC : G.PlainCubic := (ValidHub.plainCubicPentagonal ⟨cexG, pos_x⟩).toPlainCubic
  -- the map `G1` and the part `p1`, possibly mirrored
  obtain ⟨G1, x1, x1ok, Exp1⟩ : ∃ (G1 : Hypermap D) (x1 : D), G1.ValidHub x1 ∧
      G1.exactFitp x1 (if mir then mirrorPart p else p) = true := by
    cases mir
    · exact ⟨G, x, ⟨cexG, pos_x⟩, fit_p⟩
    · refine ⟨G.mirror, x, ⟨minimal_counter_example_mirror cexG, ?_⟩, ?_⟩
      · rw [G.dscore_mirror hPCC]
        exact pos_x
      · rw [ite_eq_left rfl, ← G.fitp_mirror hPC, mirror_mirror_part]
        exact fit_p
  generalize (if mir then mirrorPart p else p) = p1 at Exp1 Eps2 eq_p2ps
  -- a valid hub of `G1` that fits `p2 = rotPart j p1`
  obtain ⟨x2, x2ok, Exp2⟩ :
      ∃ x2, G1.ValidHub x2 ∧ G1.exactFitp x2 (rotPart j p1) = true := by
    rcases Nat.lt_or_ge (sizePart p1) j with ltnj | lejn
    · refine ⟨x1, x1ok, ?_⟩
      simp only [exactFitp, size_rot_part, fitp_rotPart_of_lt G1 ltnj] at Exp1 ⊢
      exact Exp1
    · refine ⟨G1.face^[j] x1, ⟨x1ok.1, ?_⟩, ?_⟩
      · rw [← G1.dscore_cface (fconnect_iterate _ _ _)]
        exact x1ok.2
      · rw [← G1.fitp_rot j p1 lejn]
        exact Exp1
  have hps := ps_ok G1 x2 x2ok
  simp only [exactFitp, Bool.and_eq_true, beq_iff_eq] at Exp2
  have hfit : G1.fitp x2 ps = true := by
    rw [G1.fitp_cmp _ x2 Exp2.2 ps, eq_p2ps]
    rfl
  simp only [exactFitp, Eps2, Exp2.1, beq_self_eq_true, hfit, Bool.and_self] at hps
  exact Bool.noConfusion hps

/-! ### Reducibility -/

/-- Not in Coq as a separate lemma (the core of the proof of Coq `no_fit_the_redpart`):
assuming reducibility, no quiz of `theQuizTree` fits a minimal counter-example. -/
theorem not_qztFit_theQuizTree (red_check : Reducibility) {D : Type u} [Fintype D]
    {G : Hypermap D} (cexG : G.MinimalCounterExample) (y : D) : ¬ G.QztFit y theQuizTree := by
  classical
  rw [theQuizTree_eq]
  intro hfit
  obtain ⟨cf, ltcf, qz, fit_qz, cf_ok, u, qz_u⟩ :=
    G.qzt_fit_cfquiz (minimal_counter_example_is_plain_cubic_pentagonal cexG).toPlainCubic
      theConfigs hfit
  have red_cf : CfReducible (theConfigs.getD cf cf000) := red_check cf (Nat.zero_le _) ltcf
  have key : ∀ {G' : Hypermap D}, G'.MinimalCounterExample → (∃ y, G'.fitqz y qz) →
      False := by
    rintro G' cexG' ⟨y', fit'⟩
    exact not_embed_reducible cexG' cf_ok
      (quiz_preembedding (minimal_counter_example_is_plain_cubic_pentagonal cexG').toPlainCubic
        cf_ok.toPlainQuasicubic qz_u fit') red_cf
  rcases fit_qz with h | h
  · exact key cexG h
  · exact key (minimal_counter_example_mirror cexG) h

/-- Coq `the_redpart` (a section `Let` of `present.v`): the reducibility check `redpart` with
the precomputed quiz tree of the configurations. -/
def theRedpart : Part → Bool := redpart theQuizTree

/-- Coq `no_fit_the_redpart`: assuming reducibility, no dart of a minimal counter-example fits a
part accepted by `theRedpart`. -/
theorem no_fit_the_redpart (red_check : Reducibility) {D : Type u} [Fintype D] {G : Hypermap D}
    (cexG : G.MinimalCounterExample) (x : D) (p' : Part) (hp : theRedpart p' = true) :
    G.exactFitp x p' = false := by
  classical
  exact no_fit_redpart (minimal_counter_example_is_plain_cubic_pentagonal cexG)
    (not_qztFit_theQuizTree red_check cexG) p' hp x

/-- Coq `succeed_by_reducibility` (the tactic `Reducible`). -/
theorem succeed_by_reducibility {p0 p : Part} (red_check : Reducibility)
    (hp : theRedpart p = true) : SucceedsIn.{u} p0 p :=
  fun _ _ _ _ x x_ok => no_fit_the_redpart red_check x_ok.1 x p hp

/-- `succeed_by_reducibility` with the fast check `redpartFast` on the quiz tree pruned by any
mask `m` (`FourColor.Fast.Prune`). -/
theorem succeed_by_reducibility_fast {p0 p : Part} (red_check : Reducibility) (m : QztMask)
    (hp : redpartFast (qztPruneFast theQuizTree m) p = true) : SucceedsIn.{u} p0 p :=
  fun _ _ _ _ x x_ok => no_fit_redpartFast_pruneFast x_ok.plainCubicPentagonal
    (not_qztFit_theQuizTree red_check x_ok.1) m p hp x

/-! ### Hubcaps -/

/-- Coq `succeed_by_hubcap` (the tactic `Hubcap`): with `n = sizePart p`, if `hc` covers the
hub and `p` fits `hc` (for the rule fork `theDruleFork n` and the reducibility check
`theRedpart`), then `Check p in p0` holds for any `p0`. -/
theorem succeed_by_hubcap (hc : Hubcap) {p0 p : Part} (red_check : Reducibility)
    (h : (hubcapCover (sizePart p) hc &&
      hubcapFit theRedpart (theDruleFork (sizePart p)) p hc) = true) :
    SucceedsIn.{u} p0 p :=
  fun _ _ _ G _ x_ok => G.hubcap_fit_bound x_ok.plainCubicPentagonal
    (fun y q hq => no_fit_the_redpart red_check x_ok.1 y q hq) rfl x_ok.2 h

/-- `succeed_by_hubcap` with the fast checks (`hubcapCoverFast`, `hubcapFitFast`), the fast
reducibility check `redpartFast` on the quiz tree pruned by any mask `m`, and any drule fork
`rf : DruleFork n` with `n = sizePart p`. -/
theorem succeed_by_hubcap_fast {n : ℕ} (rf : DruleFork n) (m : QztMask) (hc : Hubcap)
    {p0 p : Part} (red_check : Reducibility) (Ep : sizePart p = n)
    (h : (hubcapCoverFast n hc && hubcapFitFast n (redpartFast (qztPruneFast theQuizTree m))
      rf.sourceDrules rf.targetDrules p hc) = true) :
    SucceedsIn.{u} p0 p :=
  fun _ _ _ _ _ x_ok => hubcapFast_prune_sound x_ok.plainCubicPentagonal
    (not_qztFit_theQuizTree red_check x_ok.1) m rf Ep x_ok.2 h

end FourColor
