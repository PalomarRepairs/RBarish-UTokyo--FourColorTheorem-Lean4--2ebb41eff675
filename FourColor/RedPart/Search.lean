/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.RedPart.Pop

/-!
# Reducibility check for parts: the search and its soundness
  (port of `redpart.v`, part 3 of 3)

The end of the Coq section `RedpartRec` and the section `Redpart`:

* `red_zpart_rec zp d` → `redZpartRec qt ahub redRec p0l p0r zp d`: for one of the `d` first
  right shifts of the zipper part `zp`, one of the quizzes of `qt` matches the range upper bounds
  at a node covered by the locations of `zp`, and `redRec` succeeds on all the parts obtained by
  popping one of the matched ranges.
* `red_zpart` → `redZpart qt ahub redRec p0l p0r`: `redZpartRec` from the first subpart of
  `p0r`, for `ahub` shifts.
* `not_red_zpart`: in a plain cubic pentagonal map where no quiz of `qt` fits, if `x0` exactly
  fits `p0r`, `p0l = rev_part p0r`, and `redRec` fails on the parts of size `ahub` that fit a
  dart of arity `ahub`, then `redZpart` fails.
* `redpart qt p` → `redpart qt p`: the check itself, iterating `redZpart` (at most
  `12 * size_part p` times) with the recursive check as `redRec`; the Coq local fixpoint `loop` is
  `redpart.loop`.
* `no_fit_redpart`: the soundness of the check, `redpart qt p → ∀ x, ~~ exact_fitp x p`.

## Porting notes

* `redZpartRec`, `redZpart`, `redpart` and `redpart.loop` are structurally recursive (on the
  fuel `d`), first-order apart from the `redRec` argument (as in Coq), and faithful to the Coq
  definitions, so that the kernel can evaluate `redpart` (`decide +kernel`).
* The section variables are explicit arguments: `qt ahub redRec p0l p0r` for the definitions;
  the section hypotheses `geoG`, `fit'qt : ∀ y, ¬ G.QztFit y qt` (Coq `forall y, ~~ qzt_fit y qt`),
  `notRedRec`, `Dp0l`, `fitP0r`, `nFx0` for `not_red_zpart`; `geoG` and `fit'qt` for
  `no_fit_redpart`. `~~ b` is stated as `b = false`.
* The proof of `not_red_zpart` follows the Coq case analysis (the hub triangle, the spoke
  triangle, and the fan triangles of the right spoke of arity 5 to 8); the shared contradiction
  argument of the cases is the private lemma `leaf_absurd`.
-/

namespace FourColor

universe u

/-- Coq `red_zpart_rec zp d`: for one of the `d` first right shifts of zipper part `zp`, one of
the quizzes in `qt` matches the range upper bounds at a node covered by the locations of `zp`,
and `red_rec` succeeds on all the parts obtained by popping one of the matched ranges. -/
def redZpartRec (qt : QuizTree) (ahub : Qarity) (redRec : Part → Bool) (p0l p0r : Part) :
    Zpart → ℕ → Bool
  | _, 0 => false
  | zp, d' + 1 =>
    let zp' := zshiftr p0l p0r Zhub zp
    match zp with
    | ⟨_, pl, pr⟩ =>
    let s := getSpoke pr
    let sqt := qztGetr s (qztTruncate qt)
    if (if qztProper sqt then
          match zp' with
          | ⟨_, pl', pr'⟩ =>
          let sl := getSpoke pl
          if redQztLeaf ahub redRec p0l p0r ⟨Zhubr, pl', pr'⟩ (zshiftl p0l p0r Zhubl zp)
              ⟨Zhat, pl, pr⟩ (qztGetr s (qztGetr sl (qztGet1 ahub qt))) then
            redPoprSpoke ahub redRec p0r pr && redPoplSpoke ahub redRec p0r pl pr
          else
          if redQztLeaf ahub redRec p0l p0r ⟨zfanLt pr, pl', pr'⟩ zp ⟨zfanRt pl, pl, pr⟩
              (qztGetr (getHat pr) (qztGetr sl sqt)) then
            redPoprHat ahub redRec p0r pr &&
              (redPoplSpoke ahub redRec p0r pl pr && redPoprSpoke ahub redRec p0r pr)
          else
          let zpnil : Zpart := ⟨Znil, pl', pr'⟩
          match pr with
          | .cons .pr55 h _ =>
            if redQztLeaf ahub redRec p0l p0r ⟨Zhatr, pl', pr'⟩ ⟨Zhatl, pl, pr⟩ zpnil
                (qztGetr (getHat pr') (qztGetr h sqt)) then
              redPoprHat ahub redRec p0r pr' && redPoprHat ahub redRec p0r pr
            else false
          | .cons6 h f1 _ =>
            if redQztLeaf ahub redRec p0l p0r ⟨Zfan0l, pl', pr'⟩ ⟨Zhatl, pl, pr⟩ zpnil
                (qztGetr f1 (qztGetr h sqt)) then
              redPoplFan1r ahub redRec p0r pl' pr' && redPoprHat ahub redRec p0r pr
            else
            if redQztLeaf ahub redRec p0l p0r ⟨Zhatr, pl', pr'⟩ ⟨Zfan0r, pl', pr'⟩ zpnil
                (qztGetr (getHat pr') (qztGetr f1 sqt)) then
              redPoprHat ahub redRec p0r pr' && redPoplFan1r ahub redRec p0r pl' pr'
            else false
          | .cons7 h f1 f2 _ =>
            if redQztLeaf ahub redRec p0l p0r ⟨Zfan1l, pl', pr'⟩ ⟨Zhatl, pl, pr⟩ zpnil
                (qztGetr f1 (qztGetr h sqt)) then
              redPoplFan1r ahub redRec p0r pl' pr' && redPoprHat ahub redRec p0r pr
            else
            if redQztLeaf ahub redRec p0l p0r ⟨Zfan0l, pl', pr'⟩ ⟨Zfan0r, pl', pr'⟩ zpnil
                (qztGetr f2 (qztGetr f1 sqt)) then
              redPoplFan2r ahub redRec p0r pl' pr' && redPoplFan1r ahub redRec p0r pl' pr'
            else
            if redQztLeaf ahub redRec p0l p0r ⟨Zhatr, pl', pr'⟩ ⟨Zfan1r, pl', pr'⟩ zpnil
                (qztGetr (getHat pr') (qztGetr f2 sqt)) then
              redPoprHat ahub redRec p0r pr' && redPoplFan2r ahub redRec p0r pl' pr'
            else false
          | .cons8 h f1 f2 f3 _ =>
            if redQztLeaf ahub redRec p0l p0r ⟨Zfan2l, pl', pr'⟩ ⟨Zhatl, pl, pr⟩ zpnil
                (qztGetr f1 (qztGetr h sqt)) then
              redPoplFan1r ahub redRec p0r pl' pr' && redPoprHat ahub redRec p0r pr
            else
            if redQztLeaf ahub redRec p0l p0r ⟨Zfan1l, pl', pr'⟩ ⟨Zfan0r, pl', pr'⟩ zpnil
                (qztGetr f2 (qztGetr f1 sqt)) then
              redPoplFan2r ahub redRec p0r pl' pr' && redPoplFan1r ahub redRec p0r pl' pr'
            else
            if redQztLeaf ahub redRec p0l p0r ⟨Zfan0l, pl', pr'⟩ ⟨Zfan1r, pl', pr'⟩ zpnil
                (qztGetr f3 (qztGetr f2 sqt)) then
              redPoplFan3r ahub redRec p0r pl' pr' && redPoplFan2r ahub redRec p0r pl' pr'
            else
            if redQztLeaf ahub redRec p0l p0r ⟨Zhatr, pl', pr'⟩ ⟨Zfan2r, pl', pr'⟩ zpnil
                (qztGetr (getHat pr') (qztGetr f3 sqt)) then
              redPoprHat ahub redRec p0r pr' && redPoplFan3r ahub redRec p0r pl' pr'
            else false
          | _ => false
        else false) then true
    else redZpartRec qt ahub redRec p0l p0r zp' d'

/-- Coq `red_zpart`: one of the quizzes in `qt` matches the range upper bounds at some node in
`p0r`, and `red_rec` succeeds on all the parts obtained by popping one of the matched ranges. -/
def redZpart (qt : QuizTree) (ahub : Qarity) (redRec : Part → Bool) (p0l p0r : Part) : Bool :=
  redZpartRec qt ahub redRec p0l p0r ⟨Zhub, dropPart 1 p0l, shiftPart p0l p0r⟩ ahub

namespace Hypermap

open Redpart

variable {D : Type u} [Finite D] {G : Hypermap D}

section RedpartRec

variable (geoG : G.PlainCubicPentagonal) {qt : QuizTree} (fit'qt : ∀ y : D, ¬ G.QztFit y qt)
  {ahub : Qarity} {redRec : Part → Bool}
  (notRedRec : ∀ (x : D) (p : Part), G.arity x = ahub → G.exactFitp x p = true → redRec p = false)
  {p0l p0r : Part} {x0 : D} (Dp0l : p0l = revPart p0r) (fitP0r : G.exactFitp x0 p0r = true)
  (nFx0 : G.arity x0 = ahub)

omit [Finite D] in
/-- `if b then true else false` is `b`. -/
private theorem ite_true_false_eq {b : Bool} :
    ((if b = true then true else false) = true) = (b = true) := by
  cases b <;> rfl

include geoG fit'qt notRedRec Dp0l fitP0r nFx0 in
/-- The contradiction argument shared by the cases of `not_red_zpart`: if a leaf check succeeds
for three zipper parts that fit the right steps of the node of `y`, and the arities of that node
are the indices of the leaf list in the quiz tree, then the quiz tree fits at `y`. -/
private theorem leaf_absurd {zp1 zp2 zp3 : Zpart} {r2 r3 : Prange} {qa1 : Qarity} (y : D)
    (hleaf : redQztLeaf ahub redRec p0l p0r zp1 zp2 zp3
      (qztGetr r3 (qztGetr r2 (qztGet1 qa1 qt))) = true)
    (H : fitqa r2 (topqa r2) = true → fitqa r3 (topqa r3) = true →
      (G.Zpfit x0 (G.qstepR y) zp1 ∧ Zpvalid p0r zp1) ∧
      (G.Zpfit x0 (G.qstepR (G.node y)) zp2 ∧ Zpvalid p0r zp2) ∧
      (G.Zpfit x0 (G.qstepR (G.node (G.node y))) zp3 ∧ Zpvalid p0r zp3) ∧
      G.arity y = qa1 ∧ G.arity (G.node y) = topqa r2 ∧
      G.arity (G.node (G.node y)) = topqa r3) : False := by
  obtain ⟨hprop, hfit⟩ := red_qzt_leaf_fit geoG notRedRec Dp0l fitP0r nFx0 zp1 zp2 zp3 _ hleaf
  obtain ⟨E3, D3, P3⟩ := qzt_getr_fit r3 _ hprop
  obtain ⟨E2, D2, -⟩ := qzt_getr_fit r2 _ P3
  obtain ⟨⟨f1, v1⟩, ⟨f2, v2⟩, ⟨f3, v3⟩, a1, a2, a3⟩ := H E2 E3
  have hq := hfit y f1 v1 f2 v2 f3 v3
  rw [← D3, ← D2] at hq
  exact redpart_no_qzt_fitl fit'qt y qa1 (topqa r2) (topqa r3) a1 a2 a3 hq

include geoG fit'qt notRedRec Dp0l fitP0r nFx0 in
/-- Coq `not_red_zpart`. -/
theorem not_red_zpart : redZpart qt ahub redRec p0l p0r = false := by
  have hp0r := Ep0r fitP0r nFx0
  have h0 := size_p0r_pos fitP0r
  have h0l := size_p0l_pos Dp0l fitP0r
  have sz0l := size_p0l Dp0l fitP0r
  have nt_p0l : 1 < sizePart p0l := by have := geoG.pentagonal x0; omega
  have nt_pl : 0 < sizePart (dropPart 1 p0l) := by rw [size_drop_part]; omega
  have nt_pr : (ahub : ℕ) < sizePart (shiftPart p0l p0r) := by
    rw [size_shift_part _ h0l]; omega
  have zp_ok := zvalid_initl Dp0l h0l
  unfold redZpart
  suffices H : ∀ (d : ℕ) (pl pr : Part), 0 < sizePart pl → d < sizePart pr → Zvalid p0r pl pr →
      redZpartRec qt ahub redRec p0l p0r ⟨Zhub, pl, pr⟩ d = false from
    H _ _ _ nt_pl nt_pr zp_ok
  intro d
  induction d with
  | zero => intros; rfl
  | succ d IHd =>
  intro pl pr nt_pl nt_pr zp_ok
  have nt_pr2 : 1 < sizePart pr := by omega
  have Dzp1 : ∀ zi zi1, zshiftr p0l p0r zi1 ⟨zi, pl, pr⟩ =
      ⟨zi1, shiftPart pr pl, dropPart 1 pr⟩ := fun zi zi1 => zshiftr_eq p0l p0r zi zi1 pl pr nt_pr2
  have zp1ok : Zvalid p0r (shiftPart pr pl) (dropPart 1 pr) := by
    have e := zpvalid_shiftr Dp0l h0 Zhub ⟨Zhub, pl, pr⟩ zp_ok
    rw [Dzp1] at e
    exact e
  have Ex1 : G.zorg x0 (shiftPart pr pl) = G.face (G.zorg x0 pl) := by
    rw [zorg, zorg, size_shift_part _ (by omega), Function.iterate_succ_apply']
  have IH1 := IHd (shiftPart pr pl) (dropPart 1 pr)
    (by rw [size_shift_part _ (by omega)]; omega) (by rw [size_drop_part]; omega) zp1ok
  have hr := fitp_head geoG (zvalid_fit_r fitP0r zp_ok)
  rw [Bool.eq_false_iff]
  intro h
  rw [redZpartRec] at h
  simp only [Dzp1] at h
  rw [IH1, ite_true_false_eq] at h
  split at h
  swap
  · exact absurd h Bool.false_ne_true
  rename_i sqt_ok
  obtain ⟨Es, Ds, -⟩ := qzt_getr_fit _ _ sqt_ok
  have Dsqt : qztGetr (getSpoke pr) (qztTruncate qt) = qztGet1 (topqa (getSpoke pr)) qt := by
    rw [← Ds]; exact qzt_get1_truncate _ _ (by rw [Ds]; exact sqt_ok)
  rw [Dsqt] at h
  have Espoke : ∀ qa, fitqa (getSpoke pr) qa = true → redPoprSpoke ahub redRec p0r pr = true →
      G.arity (G.edge (G.zorg x0 pl)) = qa := fun qa hqa hred =>
    red_popr_spoke_fit geoG notRedRec fitP0r nFx0 zp_ok qa hqa hred
  split at h
  · -- the hub triangle
    rename_i hL
    rw [Bool.and_eq_true] at h
    refine leaf_absurd geoG fit'qt notRedRec Dp0l fitP0r nFx0 (G.zorg x0 pl) hL
      fun E2 E3 => ⟨⟨fun _ => ?_, zp1ok⟩, ⟨fun _ => ?_, ?_⟩, ⟨fun _ => ?_, zp_ok⟩, ?_, ?_, ?_⟩
    · simp only [zdart_mk, Ex1, zmove]; hnorm
    · rw [zdart_shiftl Dp0l fitP0r]; simp only [zporg_mk, zmove]; hnorm
    · exact zpvalid_shiftl Dp0l h0l _ _ zp_ok
    · simp only [zdart_mk, zmove, qstepR]
    · rw [zorg, G.arity_iter_face, nFx0]
    · exact red_popl_spoke_fit geoG notRedRec fitP0r nFx0 zp_ok _ E2 h.2
    · rw [← Espoke _ E3 h.1]; arity_tac
  split at h
  · -- the spoke triangle
    rename_i _ hL
    simp only [Bool.and_eq_true] at h
    have Es' := Espoke _ Es h.2.2
    refine leaf_absurd geoG fit'qt notRedRec Dp0l fitP0r nFx0
      (G.face^[2] (G.edge (G.zorg x0 pl))) hL
      fun E2 E3 => ⟨⟨?_, zp1ok⟩, ⟨fun _ => ?_, zp_ok⟩, ⟨?_, zp_ok⟩, ?_, ?_, ?_⟩
    · have htop : G.ZpfitTop ahub x0 ⟨Zhatr, pl, pr⟩ := by
        show G.arity (G.zmove Zhatr (G.zorg x0 pl)) = (topqa (getSpoke pr) : ℕ)
        rw [← Es']; simp only [zmove]; arity_tac
      have e := zdart_stepRt geoG Dp0l fitP0r ⟨Zhatr, pl, pr⟩ htop zp_ok
      have e2 : zstepRt p0l p0r ⟨Zhatr, pl, pr⟩ = ⟨zfanLt pr, shiftPart pr pl, dropPart 1 pr⟩ :=
        Dzp1 _ _
      have e3 : G.face^[2] (G.edge (G.zorg x0 pl)) = G.zdart x0 ⟨Zhatr, pl, pr⟩ := by
        simp only [zdart_mk, zmove]; hnorm
      rw [e2] at e
      rw [e3]; exact e
    · simp only [zdart_mk, zmove]; hnorm
    · have htop : G.ZpfitTop ahub x0 ⟨Zhatl, pl, pr⟩ := by
        show G.arity (G.zmove Zhatl (G.zorg x0 pl)) = (topqa (getSpoke pl) : ℕ)
        rw [← red_popl_spoke_fit geoG notRedRec fitP0r nFx0 zp_ok _ E2 h.2.1]
        simp only [zmove]; arity_tac
      have e := zdart_stepLt geoG Dp0l fitP0r ⟨Zhatl, pl, pr⟩ htop zp_ok
      have e3 : G.qstepR (G.node (G.node (G.face^[2] (G.edge (G.zorg x0 pl))))) =
          G.qstepL (G.zdart x0 ⟨Zhatl, pl, pr⟩) := by
        simp only [zdart_mk, zmove]; hnorm
      rw [e3]; exact e
    · rw [G.arity_iter_face]; exact Es'
    · rw [← red_popl_spoke_fit geoG notRedRec fitP0r nFx0 zp_ok _ E2 h.2.1]; arity_tac
    · rw [← red_popr_hat_fit notRedRec fitP0r nFx0 zp_ok _ E3 h.1]; arity_tac
  -- the fan triangles of the right spoke
  rcases pr with _ | ⟨s, hh, p⟩ | ⟨hh, f1, p⟩ | ⟨hh, f1, f2, p⟩ | ⟨hh, f1, f2, f3, p⟩ <;>
    try dsimp only at h
  · exact absurd h Bool.false_ne_true
  · -- a pentagonal right spoke
    cases s <;> dsimp only at h <;> try exact absurd h Bool.false_ne_true
    have hk := iter_face_of_arity (mem55 hr.1)
    split at h
    swap
    · exact absurd h Bool.false_ne_true
    rename_i hL
    rw [Bool.and_eq_true] at h
    refine leaf_absurd geoG fit'qt notRedRec Dp0l fitP0r nFx0
      (G.face^[3] (G.edge (G.zorg x0 pl))) hL
      fun E2 E3 => ⟨⟨fun _ => ?_, zp1ok⟩, ⟨fun _ => ?_, zp_ok⟩, ⟨fun hp => ?_, zp1ok⟩, ?_, ?_, ?_⟩
    · simp only [zdart_mk, Ex1, zmove]; wrap_tac hk
    · simp only [zdart_mk, zmove]; hnorm
    · exact absurd hp Bool.false_ne_true
    · rw [G.arity_iter_face]; exact mem55 hr.1
    · rw [← red_popr_hat_fit notRedRec fitP0r nFx0 zp_ok _ E2 h.2]; arity_tac
    · rw [← red_popr_hat_fit notRedRec fitP0r nFx0 zp1ok _ E3 h.1, Ex1]; arity_wrap_tac hk
  · -- a hexagonal right spoke
    have hk := iter_face_of_arity (mem66 hr.1)
    split at h
    · rename_i hL
      rw [Bool.and_eq_true] at h
      refine leaf_absurd geoG fit'qt notRedRec Dp0l fitP0r nFx0
        (G.face^[3] (G.edge (G.zorg x0 pl))) hL
        fun E2 E3 => ⟨⟨fun _ => ?_, zp1ok⟩, ⟨fun _ => ?_, zp_ok⟩, ⟨fun hp => ?_, zp1ok⟩,
          ?_, ?_, ?_⟩
      · simp only [zdart_mk, Ex1, zmove]; wrap_tac hk
      · simp only [zdart_mk, zmove]; hnorm
      · exact absurd hp Bool.false_ne_true
      · rw [G.arity_iter_face]; exact mem66 hr.1
      · rw [← red_popr_hat_fit notRedRec fitP0r nFx0 zp_ok _ E2 h.2]; arity_tac
      · rw [← red_popl_fan1r_fit geoG notRedRec fitP0r nFx0 zp1ok _ E3 h.1]
        simp only [zdart_mk, Ex1, zmove]; arity_tac
    split at h
    swap
    · exact absurd h Bool.false_ne_true
    rename_i _ hL
    rw [Bool.and_eq_true] at h
    refine leaf_absurd geoG fit'qt notRedRec Dp0l fitP0r nFx0
      (G.face^[4] (G.edge (G.zorg x0 pl))) hL
      fun E2 E3 => ⟨⟨fun _ => ?_, zp1ok⟩, ⟨fun _ => ?_, zp1ok⟩, ⟨fun hp => ?_, zp1ok⟩, ?_, ?_, ?_⟩
    · simp only [zdart_mk, Ex1, zmove]; wrap_tac hk
    · simp only [zdart_mk, Ex1, zmove]; hnorm
    · exact absurd hp Bool.false_ne_true
    · rw [G.arity_iter_face]; exact mem66 hr.1
    · rw [← red_popl_fan1r_fit geoG notRedRec fitP0r nFx0 zp1ok _ E2 h.2]
      simp only [zdart_mk, Ex1, zmove]; arity_tac
    · rw [← red_popr_hat_fit notRedRec fitP0r nFx0 zp1ok _ E3 h.1, Ex1]; arity_wrap_tac hk
  · -- a heptagonal right spoke
    have hk := iter_face_of_arity (mem77 hr.1)
    split at h
    · rename_i hL
      rw [Bool.and_eq_true] at h
      refine leaf_absurd geoG fit'qt notRedRec Dp0l fitP0r nFx0
        (G.face^[3] (G.edge (G.zorg x0 pl))) hL
        fun E2 E3 => ⟨⟨fun _ => ?_, zp1ok⟩, ⟨fun _ => ?_, zp_ok⟩, ⟨fun hp => ?_, zp1ok⟩,
          ?_, ?_, ?_⟩
      · simp only [zdart_mk, Ex1, zmove]; wrap_tac hk
      · simp only [zdart_mk, zmove]; hnorm
      · exact absurd hp Bool.false_ne_true
      · rw [G.arity_iter_face]; exact mem77 hr.1
      · rw [← red_popr_hat_fit notRedRec fitP0r nFx0 zp_ok _ E2 h.2]; arity_tac
      · rw [← red_popl_fan1r_fit geoG notRedRec fitP0r nFx0 zp1ok _ E3 h.1]
        simp only [zdart_mk, Ex1, zmove]; arity_tac
    split at h
    · rename_i _ hL
      rw [Bool.and_eq_true] at h
      refine leaf_absurd geoG fit'qt notRedRec Dp0l fitP0r nFx0
        (G.face^[4] (G.edge (G.zorg x0 pl))) hL
        fun E2 E3 => ⟨⟨fun _ => ?_, zp1ok⟩, ⟨fun _ => ?_, zp1ok⟩, ⟨fun hp => ?_, zp1ok⟩,
          ?_, ?_, ?_⟩
      · simp only [zdart_mk, Ex1, zmove]; wrap_tac hk
      · simp only [zdart_mk, Ex1, zmove]; hnorm
      · exact absurd hp Bool.false_ne_true
      · rw [G.arity_iter_face]; exact mem77 hr.1
      · rw [← red_popl_fan1r_fit geoG notRedRec fitP0r nFx0 zp1ok _ E2 h.2]
        simp only [zdart_mk, Ex1, zmove]; arity_tac
      · rw [← red_popl_fan2r_fit geoG notRedRec fitP0r nFx0 zp1ok _ E3 h.1]
        simp only [zdart_mk, Ex1, zmove]; arity_tac
    split at h
    swap
    · exact absurd h Bool.false_ne_true
    rename_i _ _ hL
    rw [Bool.and_eq_true] at h
    refine leaf_absurd geoG fit'qt notRedRec Dp0l fitP0r nFx0
      (G.face^[5] (G.edge (G.zorg x0 pl))) hL
      fun E2 E3 => ⟨⟨fun _ => ?_, zp1ok⟩, ⟨fun _ => ?_, zp1ok⟩, ⟨fun hp => ?_, zp1ok⟩, ?_, ?_, ?_⟩
    · simp only [zdart_mk, Ex1, zmove]; wrap_tac hk
    · simp only [zdart_mk, Ex1, zmove]; hnorm
    · exact absurd hp Bool.false_ne_true
    · rw [G.arity_iter_face]; exact mem77 hr.1
    · rw [← red_popl_fan2r_fit geoG notRedRec fitP0r nFx0 zp1ok _ E2 h.2]
      simp only [zdart_mk, Ex1, zmove]; arity_tac
    · rw [← red_popr_hat_fit notRedRec fitP0r nFx0 zp1ok _ E3 h.1, Ex1]; arity_wrap_tac hk
  · -- an octagonal right spoke
    have hk := iter_face_of_arity (mem88 hr.1)
    split at h
    · rename_i hL
      rw [Bool.and_eq_true] at h
      refine leaf_absurd geoG fit'qt notRedRec Dp0l fitP0r nFx0
        (G.face^[3] (G.edge (G.zorg x0 pl))) hL
        fun E2 E3 => ⟨⟨fun _ => ?_, zp1ok⟩, ⟨fun _ => ?_, zp_ok⟩, ⟨fun hp => ?_, zp1ok⟩,
          ?_, ?_, ?_⟩
      · simp only [zdart_mk, Ex1, zmove]; wrap_tac hk
      · simp only [zdart_mk, zmove]; hnorm
      · exact absurd hp Bool.false_ne_true
      · rw [G.arity_iter_face]; exact mem88 hr.1
      · rw [← red_popr_hat_fit notRedRec fitP0r nFx0 zp_ok _ E2 h.2]; arity_tac
      · rw [← red_popl_fan1r_fit geoG notRedRec fitP0r nFx0 zp1ok _ E3 h.1]
        simp only [zdart_mk, Ex1, zmove]; arity_tac
    split at h
    · rename_i _ hL
      rw [Bool.and_eq_true] at h
      refine leaf_absurd geoG fit'qt notRedRec Dp0l fitP0r nFx0
        (G.face^[4] (G.edge (G.zorg x0 pl))) hL
        fun E2 E3 => ⟨⟨fun _ => ?_, zp1ok⟩, ⟨fun _ => ?_, zp1ok⟩, ⟨fun hp => ?_, zp1ok⟩,
          ?_, ?_, ?_⟩
      · simp only [zdart_mk, Ex1, zmove]; wrap_tac hk
      · simp only [zdart_mk, Ex1, zmove]; hnorm
      · exact absurd hp Bool.false_ne_true
      · rw [G.arity_iter_face]; exact mem88 hr.1
      · rw [← red_popl_fan1r_fit geoG notRedRec fitP0r nFx0 zp1ok _ E2 h.2]
        simp only [zdart_mk, Ex1, zmove]; arity_tac
      · rw [← red_popl_fan2r_fit geoG notRedRec fitP0r nFx0 zp1ok _ E3 h.1]
        simp only [zdart_mk, Ex1, zmove]; arity_tac
    split at h
    · rename_i _ _ hL
      rw [Bool.and_eq_true] at h
      refine leaf_absurd geoG fit'qt notRedRec Dp0l fitP0r nFx0
        (G.face^[5] (G.edge (G.zorg x0 pl))) hL
        fun E2 E3 => ⟨⟨fun _ => ?_, zp1ok⟩, ⟨fun _ => ?_, zp1ok⟩, ⟨fun hp => ?_, zp1ok⟩,
          ?_, ?_, ?_⟩
      · simp only [zdart_mk, Ex1, zmove]; wrap_tac hk
      · simp only [zdart_mk, Ex1, zmove]; hnorm
      · exact absurd hp Bool.false_ne_true
      · rw [G.arity_iter_face]; exact mem88 hr.1
      · rw [← red_popl_fan2r_fit geoG notRedRec fitP0r nFx0 zp1ok _ E2 h.2]
        simp only [zdart_mk, Ex1, zmove]; arity_tac
      · rw [← red_popl_fan3r_fit geoG notRedRec fitP0r nFx0 zp1ok _ E3 h.1]
        simp only [zdart_mk, Ex1, zmove]; arity_tac
    split at h
    swap
    · exact absurd h Bool.false_ne_true
    rename_i _ _ _ hL
    rw [Bool.and_eq_true] at h
    refine leaf_absurd geoG fit'qt notRedRec Dp0l fitP0r nFx0
      (G.face^[6] (G.edge (G.zorg x0 pl))) hL
      fun E2 E3 => ⟨⟨fun _ => ?_, zp1ok⟩, ⟨fun _ => ?_, zp1ok⟩, ⟨fun hp => ?_, zp1ok⟩, ?_, ?_, ?_⟩
    · simp only [zdart_mk, Ex1, zmove]; wrap_tac hk
    · simp only [zdart_mk, Ex1, zmove]; hnorm
    · exact absurd hp Bool.false_ne_true
    · rw [G.arity_iter_face]; exact mem88 hr.1
    · rw [← red_popl_fan3r_fit geoG notRedRec fitP0r nFx0 zp1ok _ E2 h.2]
      simp only [zdart_mk, Ex1, zmove]; arity_tac
    · rw [← red_popr_hat_fit notRedRec fitP0r nFx0 zp1ok _ E3 h.1, Ex1]; arity_wrap_tac hk

end RedpartRec

end Hypermap

/-- Coq `redpart qt p`: if a map fits (exactly) part `p` at dart `x0`, then the quiz tree `qt`
fits at some dart `x` adjacent to `x0`. The recursion depth `12 * size_part p` keeps the
recursion bounded (each recursive call pops one range; there are at most 4 open ranges per
subpart). The Coq local fixpoint `loop` is `redpart.loop`. -/
def redpart (qt : QuizTree) (p : Part) : Bool :=
  let nhub := sizePart p
  let ahub := qarityOfNat nhub
  (nhub == (ahub : ℕ)) && redpart.loop qt ahub (nhub * 12) p
where
  /-- Coq `loop` (local to `redpart`): `loop d p'` runs `red_zpart` on `p'` with `loop d'` as
  the recursive check. -/
  loop (qt : QuizTree) (ahub : Qarity) : ℕ → Part → Bool
    | 0, _ => false
    | d' + 1, p' => redZpart qt ahub (loop qt ahub d') (revPart p') p'

namespace Hypermap

variable {D : Type u} [Finite D] {G : Hypermap D}

/-- Coq `no_fit_redpart`: the soundness of `redpart` (section `Redpart`, with the section
variable `qt` and the hypotheses `geoG` and `fit'qt`). -/
theorem no_fit_redpart (geoG : G.PlainCubicPentagonal) {qt : QuizTree}
    (fit'qt : ∀ y : D, ¬ G.QztFit y qt) (p : Part) (hp : redpart qt p = true) (x : D) :
    G.exactFitp x p = false := by
  simp only [redpart, Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨Ep, red_p⟩ := hp
  have key : ∀ (d : ℕ) (x : D) (p' : Part), G.arity x = qarityOfNat (sizePart p) →
      G.exactFitp x p' = true → redpart.loop qt (qarityOfNat (sizePart p)) d p' = false := by
    intro d
    induction d with
    | zero => intros; rfl
    | succ d IHd =>
      intro x p' hx fit_p'
      exact not_red_zpart geoG fit'qt IHd rfl fit_p' hx
  rw [Bool.eq_false_iff]
  intro fit_p
  have hx : G.arity x = qarityOfNat (sizePart p) := by
    rw [← Ep, ← Redpart.size_p0r fit_p]
  rw [key _ x p hx fit_p] at red_p
  exact Bool.false_ne_true red_p

end Hypermap

end FourColor
