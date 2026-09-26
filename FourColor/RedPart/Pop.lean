/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.RedPart.Zipper

/-!
# Reducibility check for parts: popping ranges and matching questions
  (port of `redpart.v`, part 2 of 3)

The second half of the Coq section `RedpartRec`, up to `redpart_no_qzt_fitl`: updating a part
by "popping" one of its ranges (replacing `[M, N]` with `[M, N-1]`), and matching the questions of
the quiz tree against the top values of the ranges of a zipper part.

## Definitions (Coq name → Lean name)

* `red_pcons pc r pr` → `redPcons ahub redRec p0r pc r pr`: `r` is unbounded or a singleton, or
  `redRec` succeeds for the part of size `ahub` obtained by padding the sector
  `pc (popqa r) pr` with a prefix of `p0r`.
* `red_popr_spoke`, `red_popr_hat`, `red_popl_spoke`, `red_popl_hat`, `red_popl_fan[123][lr]`
  → `redPoprSpoke`, `redPoprHat`, `redPoplSpoke`, `redPoplHat`, `redPoplFan[123][lr]`:
  `redRec` succeeds on the part obtained by popping the corresponding range, or this range is
  unbounded or a singleton.
* `red_pop zp` → `redPop ahub redRec p0r zp`: `redRec` succeeds on the part obtained by popping
  `zrange zp`.
* `fitqzp zp q` → `fitqzp ahub p0l p0r zp q`: the arities specified by `q` for a traversal
  starting at `zdart zp` are the tops of the corresponding ranges of `zp`.
* `red_popqzp zp q` → `redPopqzp ahub redRec p0l p0r zp q`: `redPop` succeeds on all the zipper
  parts tested for arity during the traversal of question `q`.
* `red_qzt_leaf zp1 zp2 zp3 qt0` (section `RedQztLeaf`) →
  `redQztLeaf ahub redRec p0l p0r zp1 zp2 zp3 qt0`: in the leaf list `qt0`, both `fitqzp` and
  `redPopqzp` succeed for all the `zpi qi` pairs, for one of the leaves `QztLeaf q1 q2 q3 _`.
* `qzt_getr r qt` → `qztGetr r qt`: `qztGet1 (topqa r) qt` for a `QztNode`.

All the lemmas are ported with their Coq names.

## Porting notes

* As in part 1, the section variables are explicit leading arguments of the computational
  definitions (Coq order `ahub red_rec p0l p0r`), and the section hypotheses `geoG`, `not_red_rec`
  (here `notRedRec`, with `~~ red_rec p` as `redRec p = false`), `Dp0l`, `fit_p0r` and `nFx0`
  are explicit hypotheses of the lemmas that use them. The section `RedQztLeaf` variables `zp1`,
  `zp2`, `zp3` are explicit arguments too.
* `fitq` is a `Prop` in `FourColor.Quiz`, so `fitqzp_fit` concludes `G.fitq (G.zdart x0 zp) q`,
  and `qzt_fitl` is the `Prop` `QztFitl`: the conclusion `~ ~~ qzt_fitl x qtl` of
  `red_qzt_leaf_fit` (a boolean double negation) is stated as `G.QztFitl x qtl`, and
  `redpart_no_qzt_fitl` concludes `¬ G.QztFitl y (qztGet3 qa1 qa2 qa3 qt)`.
* The statement-level `let qa := topqa r` of `qzt_getr_fit` is unfolded, and its
  `[/\ _, _ & _]` is a conjunction.
-/

namespace FourColor

universe u

open Hypermap

/-! ### Popping ranges -/

/-- Coq `red_pcons pc r pr`: `r` is unbounded or a singleton, or `red_rec` succeeds for the part
of size `ahub` obtained by padding the part sector `pc (popqa r) pr` with a prefix of `p0r`. -/
def redPcons (ahub : Qarity) (redRec : Part → Bool) (p0r : Part) (pc : Prange → Part → Part)
    (r : Prange) (pr : Part) : Bool :=
  let rpc (r' : Prange) := redRec (takePart (ahub : ℕ) (catPart (pc r' pr) p0r))
  match r with
  | .pr56 => rpc .pr55
  | .pr57 => rpc .pr56
  | .pr58 => rpc .pr57
  | .pr67 => rpc .pr66
  | .pr68 => rpc .pr67
  | .pr78 => rpc .pr77
  | _ => true

/-- `redPcons` for a range that can be popped. -/
theorem redPcons_eq {ahub : Qarity} {redRec : Part → Bool} {p0r : Part}
    {pc : Prange → Part → Part} {r : Prange} {pr : Part} (h : memRange (popqa r) 9 = false) :
    redPcons ahub redRec p0r pc r pr = redRec (takePart ahub (catPart (pc (popqa r) pr) p0r)) := by
  cases r <;> first | rfl | exact absurd h (by decide)

/-- Taking a prefix of a part of known size. -/
private theorem size_take_part (n : ℕ) (p : Part) (h : n ≤ sizePart p) :
    sizePart (takePart n p) = n := by
  have e1 := size_drop_part n p
  have e2 : sizePart (takePart n p) + sizePart (dropPart n p) = sizePart p := by
    conv_rhs => rw [← cat_take_drop_part n p]
    rw [size_cat_part]
  omega

namespace Hypermap

open Redpart

variable {D : Type u} [Finite D] {G : Hypermap D}

omit [Finite D] in
/-- A prefix of a fitting part fits. -/
private theorem fitp_take {x : D} {p : Part} (n : ℕ) (h : G.fitp x p = true) :
    G.fitp x (takePart n p) = true := by
  have e := G.fitp_cat x (takePart n p) (dropPart n p)
  rw [cat_take_drop_part, h, eq_comm, Bool.and_eq_true] at e
  exact e.1

section RedpartRec

variable (geoG : G.PlainCubicPentagonal) {ahub : Qarity} {redRec : Part → Bool}
  (notRedRec : ∀ (x : D) (p : Part), G.arity x = ahub → G.exactFitp x p = true → redRec p = false)
  {p0l p0r : Part} {x0 : D} (Dp0l : p0l = revPart p0r) (fitP0r : G.exactFitp x0 p0r = true)
  (nFx0 : G.arity x0 = ahub)

include notRedRec fitP0r nFx0 in
/-- Coq `red_pcons_fit`. -/
theorem red_pcons_fit {pc : Prange → Part → Part} {j : SubpartLoc} (hpc : PartUpdate.{u} pc j)
    (r : Prange) (pl pr : Part) (hzp : Zvalid p0r pl (pc r pr)) (qa : Qarity)
    (hqa : fitqa r qa = true) (hred : redPcons ahub redRec p0r pc r pr = true) :
    G.arity (j.move G (G.zorg x0 pl)) = qa := by
  apply fitqa_popqa hqa
  have hfit := zvalid_fit_r fitP0r hzp
  have Ey : G.arity (G.zorg x0 pl) = ahub := by rw [zorg, G.arity_iter_face, nFx0]
  obtain ⟨Epr, hpcr⟩ := hpc r pr
  obtain ⟨hr, fit_pc⟩ := hpcr D G (G.zorg x0 pl) hfit
  rw [hr, Bool.true_and]
  cases hpop : memRange (popqa r) 9
  · rw [Bool.false_or]
    cases Ery : memRange (popqa r) (G.arity (j.move G (G.zorg x0 pl)))
    · rfl
    · exfalso
      have hsz := size_zvalid hzp
      have Epr' := (hpc (popqa r) pr).1
      have hp0r := Ep0r fitP0r nFx0
      have fit1 : G.fitp (G.zorg x0 pl) (catPart (pc (popqa r) pr) p0r) = true := by
        have e2 : G.face^[sizePart (pc (popqa r) pr)] (G.zorg x0 pl) = x0 := by
          rw [zorg, ← Function.iterate_add_apply, Epr',
            show sizePart pr + 1 + sizePart pl = sizePart p0r + sizePart p0r by omega,
            size_p0r fitP0r, Function.iterate_add_apply, G.iter_face_arity, G.iter_face_arity]
        rw [G.fitp_cat, fit_pc _ Ery, e2, Bool.true_and]
        have e3 := fitP0r
        rw [exactFitp, Bool.and_eq_true] at e3
        exact e3.2
      have fit_p0r1 : G.exactFitp (G.zorg x0 pl)
          (takePart ahub (catPart (pc (popqa r) pr) p0r)) = true := by
        simp only [exactFitp, Bool.and_eq_true, beq_iff_eq]
        refine ⟨?_, fitp_take _ fit1⟩
        rw [size_take_part _ _ (by rw [size_cat_part, Epr', hp0r]; omega), Ey]
      have h1 := notRedRec _ _ Ey fit_p0r1
      rw [redPcons_eq hpop, h1] at hred
      exact absurd hred (by decide)
  · rfl

/-- Coq `red_popr_spoke pr`: pop the first spoke range of `pr`. -/
def _root_.FourColor.redPoprSpoke (ahub : Qarity) (redRec : Part → Bool) (p0r : Part)
    (pr : Part) : Bool :=
  match pr with
  | .cons s h p => redPcons ahub redRec p0r (fun r => .cons r h) s p
  | _ => true

include geoG notRedRec fitP0r nFx0 in
/-- Coq `red_popr_spoke_fit`. -/
theorem red_popr_spoke_fit {pl pr : Part} (hzp : Zvalid p0r pl pr) (qa : Qarity)
    (hqa : fitqa (getSpoke pr) qa = true) (hred : redPoprSpoke ahub redRec p0r pr = true) :
    G.arity (G.edge (G.zorg x0 pl)) = qa := by
  have hr := (fitp_head geoG (zvalid_fit_r fitP0r hzp)).1
  cases pr with
  | nil => cases qa <;> simp [getSpoke, fitqa] at hqa
  | cons s h p => exact red_pcons_fit notRedRec fitP0r nFx0 (updatePs h) s pl p hzp qa hqa hred
  | _ => exact fitqa_popqa hqa _ (by rw [hr]; rfl)

/-- Coq `red_popr_hat pr`: pop the first hat range of `pr`. -/
def _root_.FourColor.redPoprHat (ahub : Qarity) (redRec : Part → Bool) (p0r : Part)
    (pr : Part) : Bool :=
  match pr with
  | .cons s h p => redPcons ahub redRec p0r (Part.cons s) h p
  | .cons6 h f1 p => redPcons ahub redRec p0r (fun r => .cons6 r f1) h p
  | .cons7 h f1 f2 p => redPcons ahub redRec p0r (fun h' => .cons7 h' f1 f2) h p
  | .cons8 h f1 f2 f3 p => redPcons ahub redRec p0r (fun h' => .cons8 h' f1 f2 f3) h p
  | _ => true

include notRedRec fitP0r nFx0 in
/-- Coq `red_popr_hat_fit`. -/
theorem red_popr_hat_fit {pl pr : Part} (hzp : Zvalid p0r pl pr) (qa : Qarity)
    (hqa : fitqa (getHat pr) qa = true) (hred : redPoprHat ahub redRec p0r pr = true) :
    G.arity (SubpartLoc.hat.move G (G.zorg x0 pl)) = qa := by
  cases pr with
  | nil => cases qa <;> simp [getHat, nextHat, fitqa] at hqa
  | cons s h p => exact red_pcons_fit notRedRec fitP0r nFx0 (updatePh s) h pl p hzp qa hqa hred
  | cons6 h f1 p =>
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP6h f1) h pl p hzp qa hqa hred
  | cons7 h f1 f2 p =>
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP7h f1 f2) h pl p hzp qa hqa hred
  | cons8 h f1 f2 f3 p =>
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP8h f1 f2 f3) h pl p hzp qa hqa hred

/-- Coq `red_popl_spoke pl pr`: pop the first spoke range of `pl` (a reversed sector). -/
def _root_.FourColor.redPoplSpoke (ahub : Qarity) (redRec : Part → Bool) (p0r : Part)
    (pl pr : Part) : Bool :=
  match pl with
  | .cons s h _ => redPcons ahub redRec p0r (fun r => .cons r h) s pr
  | _ => true

include geoG notRedRec fitP0r nFx0 in
/-- Coq `red_popl_spoke_fit`. -/
theorem red_popl_spoke_fit {pl pr : Part} (hzp : Zvalid p0r pl pr) (qa : Qarity)
    (hqa : fitqa (getSpoke pl) qa = true) (hred : redPoplSpoke ahub redRec p0r pl pr = true) :
    G.arity (G.node (G.zorg x0 pl)) = qa := by
  have hl := (fitp_head_l geoG fitP0r hzp).1
  cases pl with
  | nil => cases qa <;> simp [getSpoke, fitqa] at hqa
  | cons s h pl =>
    rw [zorg_cons, Dnf geoG]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updatePs h) s pl pr hzp qa hqa hred
  | _ => exact fitqa_popqa hqa _ (by rw [hl]; rfl)

/-- Coq `red_popl_hat pl pr`: pop the first hat range of `pl`. -/
def _root_.FourColor.redPoplHat (ahub : Qarity) (redRec : Part → Bool) (p0r : Part)
    (pl pr : Part) : Bool :=
  match pl with
  | .cons s h _ => redPcons ahub redRec p0r (fun r => .cons s r) h pr
  | .cons6 h f1 _ => redPcons ahub redRec p0r (fun r => .cons6 r f1) h pr
  | .cons7 h f1 f2 _ => redPcons ahub redRec p0r (fun r => .cons7 r f1 f2) h pr
  | .cons8 h f1 f2 f3 _ => redPcons ahub redRec p0r (fun r => .cons8 r f1 f2 f3) h pr
  | _ => true

include geoG notRedRec fitP0r nFx0 in
/-- Coq `red_popl_hat_fit`. -/
theorem red_popl_hat_fit {pl pr : Part} (hzp : Zvalid p0r pl pr) (qa : Qarity)
    (hqa : fitqa (getHat pl) qa = true) (hred : redPoplHat ahub redRec p0r pl pr = true) :
    G.arity (G.edge (G.face^[2] (G.node (G.zorg x0 pl)))) = qa := by
  cases pl with
  | nil => cases qa <;> simp [getHat, nextHat, fitqa] at hqa
  | cons s h pl =>
    rw [zorg_cons, Dnf geoG]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updatePh s) h pl pr hzp qa hqa hred
  | cons6 h f1 pl =>
    rw [zorg_cons6, Dnf geoG]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP6h f1) h pl pr hzp qa hqa hred
  | cons7 h f1 f2 pl =>
    rw [zorg_cons7, Dnf geoG]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP7h f1 f2) h pl pr hzp qa hqa hred
  | cons8 h f1 f2 f3 pl =>
    rw [zorg_cons8, Dnf geoG]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP8h f1 f2 f3) h pl pr hzp qa hqa hred

/-- Coq `red_popl_fan1l pl pr`: pop the first (clockwise) fan range of `pl`. -/
def _root_.FourColor.redPoplFan1l (ahub : Qarity) (redRec : Part → Bool) (p0r : Part)
    (pl pr : Part) : Bool :=
  match pl with
  | .cons6 h f1 _ => redPcons ahub redRec p0r (fun r => .cons6 h r) f1 pr
  | .cons7 h f1 f2 _ => redPcons ahub redRec p0r (fun r => .cons7 h f1 r) f2 pr
  | .cons8 h f1 f2 f3 _ => redPcons ahub redRec p0r (fun r => .cons8 h f1 f2 r) f3 pr
  | _ => true

/-- Coq `red_popl_fan2l pl pr`: pop the second (clockwise) fan range of `pl`. -/
def _root_.FourColor.redPoplFan2l (ahub : Qarity) (redRec : Part → Bool) (p0r : Part)
    (pl pr : Part) : Bool :=
  match pl with
  | .cons7 h f1 f2 _ => redPcons ahub redRec p0r (fun r => .cons7 h r f2) f1 pr
  | .cons8 h f1 f2 f3 _ => redPcons ahub redRec p0r (fun r => .cons8 h f1 r f3) f2 pr
  | _ => true

/-- Coq `red_popl_fan3l pl pr`: pop the third (clockwise) fan range of `pl`. -/
def _root_.FourColor.redPoplFan3l (ahub : Qarity) (redRec : Part → Bool) (p0r : Part)
    (pl pr : Part) : Bool :=
  match pl with
  | .cons8 h f1 f2 f3 _ => redPcons ahub redRec p0r (fun r => .cons8 h r f2 f3) f1 pr
  | _ => true

/-- Coq `red_popl_fan1r pl pr`: pop the first (counterclockwise) fan range of `pl`. -/
def _root_.FourColor.redPoplFan1r (ahub : Qarity) (redRec : Part → Bool) (p0r : Part)
    (pl pr : Part) : Bool :=
  match pl with
  | .cons6 h f1 _ => redPcons ahub redRec p0r (fun r => .cons6 h r) f1 pr
  | .cons7 h f1 f2 _ => redPcons ahub redRec p0r (fun r => .cons7 h r f2) f1 pr
  | .cons8 h f1 f2 f3 _ => redPcons ahub redRec p0r (fun r => .cons8 h r f2 f3) f1 pr
  | _ => true

/-- Coq `red_popl_fan2r pl pr`: pop the second (counterclockwise) fan range of `pl`. -/
def _root_.FourColor.redPoplFan2r (ahub : Qarity) (redRec : Part → Bool) (p0r : Part)
    (pl pr : Part) : Bool :=
  match pl with
  | .cons7 h f1 f2 _ => redPcons ahub redRec p0r (fun r => .cons7 h f1 r) f2 pr
  | .cons8 h f1 f2 f3 _ => redPcons ahub redRec p0r (fun r => .cons8 h f1 r f3) f2 pr
  | _ => true

/-- Coq `red_popl_fan3r pl pr`: pop the third (counterclockwise) fan range of `pl`. -/
def _root_.FourColor.redPoplFan3r (ahub : Qarity) (redRec : Part → Bool) (p0r : Part)
    (pl pr : Part) : Bool :=
  match pl with
  | .cons8 h f1 f2 f3 _ => redPcons ahub redRec p0r (fun r => .cons8 h f1 f2 r) f3 pr
  | _ => true

include geoG notRedRec fitP0r nFx0 in
/-- Coq `red_popl_fan1l_fit`. -/
theorem red_popl_fan1l_fit {pl pr : Part} (hzp : Zvalid p0r pl pr) (qa : Qarity)
    (hqa : fitqa (getFan1l pl) qa = true) (hred : redPoplFan1l ahub redRec p0r pl pr = true) :
    G.arity (G.zdart x0 ⟨Zfan1l, pl, pr⟩) = qa := by
  cases pl with
  | cons6 h f1 pl =>
    have hf := zvalid_fit_r fitP0r (pl := pl) (pr := .cons6 h f1 pr) hzp
    simp only [fitp, Bool.and_eq_true] at hf
    rw [zdart_mk, zorg_cons6, (arity_zfanl geoG (mem66 hf.1)).1 rfl]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP6f1 h) f1 pl pr hzp qa hqa hred
  | cons7 h f1 f2 pl =>
    have hf := zvalid_fit_r fitP0r (pl := pl) (pr := .cons7 h f1 f2 pr) hzp
    simp only [fitp, Bool.and_eq_true] at hf
    rw [zdart_mk, zorg_cons7, ((arity_zfanl geoG (mem77 hf.1)).2.1 rfl).1]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP7f2 h f1) f2 pl pr hzp qa hqa hred
  | cons8 h f1 f2 f3 pl =>
    have hf := zvalid_fit_r fitP0r (pl := pl) (pr := .cons8 h f1 f2 f3 pr) hzp
    simp only [fitp, Bool.and_eq_true] at hf
    rw [zdart_mk, zorg_cons8, ((arity_zfanl geoG (mem88 hf.1)).2.2 rfl).1]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP8f3 h f1 f2) f3 pl pr hzp qa hqa hred
  | _ => cases qa <;> simp [getFan1l, fitqa] at hqa

include geoG notRedRec fitP0r nFx0 in
/-- Coq `red_popl_fan2l_fit`. -/
theorem red_popl_fan2l_fit {pl pr : Part} (hzp : Zvalid p0r pl pr) (qa : Qarity)
    (hqa : fitqa (getFan2l pl) qa = true) (hred : redPoplFan2l ahub redRec p0r pl pr = true) :
    G.arity (G.zdart x0 ⟨Zfan2l, pl, pr⟩) = qa := by
  cases pl with
  | cons7 h f1 f2 pl =>
    have hf := zvalid_fit_r fitP0r (pl := pl) (pr := .cons7 h f1 f2 pr) hzp
    simp only [fitp, Bool.and_eq_true] at hf
    rw [zdart_mk, zorg_cons7, ((arity_zfanl geoG (mem77 hf.1)).2.1 rfl).2]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP7f1 h f2) f1 pl pr hzp qa hqa hred
  | cons8 h f1 f2 f3 pl =>
    have hf := zvalid_fit_r fitP0r (pl := pl) (pr := .cons8 h f1 f2 f3 pr) hzp
    simp only [fitp, Bool.and_eq_true] at hf
    rw [zdart_mk, zorg_cons8, ((arity_zfanl geoG (mem88 hf.1)).2.2 rfl).2.1]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP8f2 h f1 f3) f2 pl pr hzp qa hqa hred
  | _ => cases qa <;> simp [getFan2l, fitqa] at hqa

include geoG notRedRec fitP0r nFx0 in
/-- Coq `red_popl_fan3l_fit`. -/
theorem red_popl_fan3l_fit {pl pr : Part} (hzp : Zvalid p0r pl pr) (qa : Qarity)
    (hqa : fitqa (getFan3l pl) qa = true) (hred : redPoplFan3l ahub redRec p0r pl pr = true) :
    G.arity (G.zdart x0 ⟨Zfan3l, pl, pr⟩) = qa := by
  cases pl with
  | cons8 h f1 f2 f3 pl =>
    have hf := zvalid_fit_r fitP0r (pl := pl) (pr := .cons8 h f1 f2 f3 pr) hzp
    simp only [fitp, Bool.and_eq_true] at hf
    rw [zdart_mk, zorg_cons8, ((arity_zfanl geoG (mem88 hf.1)).2.2 rfl).2.2]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP8f1 h f2 f3) f1 pl pr hzp qa hqa hred
  | _ => cases qa <;> simp [getFan3l, fitqa] at hqa

include geoG notRedRec fitP0r nFx0 in
/-- Coq `red_popl_fan1r_fit`. -/
theorem red_popl_fan1r_fit {pl pr : Part} (hzp : Zvalid p0r pl pr) (qa : Qarity)
    (hqa : fitqa (getFan1r pl) qa = true) (hred : redPoplFan1r ahub redRec p0r pl pr = true) :
    G.arity (G.zdart x0 ⟨Zfan1r, pl, pr⟩) = qa := by
  cases pl with
  | cons6 h f1 pl =>
    rw [zdart_mk, zorg_cons6, zmove, Dnf geoG]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP6f1 h) f1 pl pr hzp qa hqa hred
  | cons7 h f1 f2 pl =>
    rw [zdart_mk, zorg_cons7, zmove, Dnf geoG]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP7f1 h f2) f1 pl pr hzp qa hqa hred
  | cons8 h f1 f2 f3 pl =>
    rw [zdart_mk, zorg_cons8, zmove, Dnf geoG]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP8f1 h f2 f3) f1 pl pr hzp qa hqa hred
  | _ => cases qa <;> simp [getFan1r, fitqa] at hqa

include geoG notRedRec fitP0r nFx0 in
/-- Coq `red_popl_fan2r_fit`. -/
theorem red_popl_fan2r_fit {pl pr : Part} (hzp : Zvalid p0r pl pr) (qa : Qarity)
    (hqa : fitqa (getFan2r pl) qa = true) (hred : redPoplFan2r ahub redRec p0r pl pr = true) :
    G.arity (G.zdart x0 ⟨Zfan2r, pl, pr⟩) = qa := by
  cases pl with
  | cons7 h f1 f2 pl =>
    rw [zdart_mk, zorg_cons7, zmove, Dnf geoG]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP7f2 h f1) f2 pl pr hzp qa hqa hred
  | cons8 h f1 f2 f3 pl =>
    rw [zdart_mk, zorg_cons8, zmove, Dnf geoG]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP8f2 h f1 f3) f2 pl pr hzp qa hqa hred
  | _ => cases qa <;> simp [getFan2r, fitqa] at hqa

include geoG notRedRec fitP0r nFx0 in
/-- Coq `red_popl_fan3r_fit`. -/
theorem red_popl_fan3r_fit {pl pr : Part} (hzp : Zvalid p0r pl pr) (qa : Qarity)
    (hqa : fitqa (getFan3r pl) qa = true) (hred : redPoplFan3r ahub redRec p0r pl pr = true) :
    G.arity (G.zdart x0 ⟨Zfan3r, pl, pr⟩) = qa := by
  cases pl with
  | cons8 h f1 f2 f3 pl =>
    rw [zdart_mk, zorg_cons8, zmove, Dnf geoG]
    exact red_pcons_fit notRedRec fitP0r nFx0 (updateP8f3 h f1 f2) f3 pl pr hzp qa hqa hred
  | _ => cases qa <;> simp [getFan3r, fitqa] at hqa

/-- Coq `red_pop zp`: `red_rec` succeeds on the part obtained by popping `zrange zp`. -/
def _root_.FourColor.redPop (ahub : Qarity) (redRec : Part → Bool) (p0r : Part) (zp : Zpart) :
    Bool :=
  match zp with
  | ⟨Zhubl, pl, pr⟩ => redPoplSpoke ahub redRec p0r pl pr
  | ⟨Zhubr, _, pr⟩ => redPoprSpoke ahub redRec p0r pr
  | ⟨Zhatl, pl, pr⟩ => redPoplSpoke ahub redRec p0r pl pr
  | ⟨Zhat, _, pr⟩ => redPoprHat ahub redRec p0r pr
  | ⟨Zhatr, _, pr⟩ => redPoprSpoke ahub redRec p0r pr
  | ⟨Zfan0l, _, pr⟩ => redPoprHat ahub redRec p0r pr
  | ⟨Zfan1l, pl, pr⟩ => redPoplFan1l ahub redRec p0r pl pr
  | ⟨Zfan2l, pl, pr⟩ => redPoplFan2l ahub redRec p0r pl pr
  | ⟨Zfan3l, pl, pr⟩ => redPoplFan3l ahub redRec p0r pl pr
  | ⟨Zfan0r, pl, pr⟩ => redPoplHat ahub redRec p0r pl pr
  | ⟨Zfan1r, pl, pr⟩ => redPoplFan1r ahub redRec p0r pl pr
  | ⟨Zfan2r, pl, pr⟩ => redPoplFan2r ahub redRec p0r pl pr
  | ⟨Zfan3r, pl, pr⟩ => redPoplFan3r ahub redRec p0r pl pr
  | _ => true

include geoG notRedRec fitP0r nFx0 in
/-- Coq `red_pop_fit`. -/
theorem red_pop_fit (zp : Zpart) (hzp : Zpvalid p0r zp) (qa : Qarity)
    (hqa : fitqa (zrange ahub zp) qa = true) (hred : redPop ahub redRec p0r zp = true) :
    G.arity (G.zdart x0 zp) = qa := by
  obtain ⟨zi, pl, pr⟩ := zp
  change Zvalid p0r pl pr at hzp
  cases zi with
  | Znil => cases qa <;> simp [zrange, fitqa] at hqa
  | Zhub =>
    rw [zdart_mk, zmove, zorg, G.arity_iter_face, nFx0]
    cases ahub <;> cases qa <;> simp [zrange, hubRange, fitqa] at hqa <;> rfl
  | Zhubl => exact red_popl_spoke_fit geoG notRedRec fitP0r nFx0 hzp qa hqa hred
  | Zhubr =>
    rw [← red_popr_spoke_fit geoG notRedRec fitP0r nFx0 hzp qa hqa hred]
    simp only [zdart_mk, zmove]; arity_tac
  | Zhat =>
    rw [← red_popr_hat_fit notRedRec fitP0r nFx0 hzp qa hqa hred]
    simp only [zdart_mk, zmove]; arity_tac
  | Zhatl =>
    rw [← red_popl_spoke_fit geoG notRedRec fitP0r nFx0 hzp qa hqa hred]
    simp only [zdart_mk, zmove]; arity_tac
  | Zhatr =>
    rw [← red_popr_spoke_fit geoG notRedRec fitP0r nFx0 hzp qa hqa hred]
    simp only [zdart_mk, zmove]; arity_tac
  | Zfan0l =>
    rw [← red_popr_hat_fit notRedRec fitP0r nFx0 hzp qa hqa hred]
    simp only [zdart_mk, zmove]; arity_tac
  | Zfan1l => exact red_popl_fan1l_fit geoG notRedRec fitP0r nFx0 hzp qa hqa hred
  | Zfan2l => exact red_popl_fan2l_fit geoG notRedRec fitP0r nFx0 hzp qa hqa hred
  | Zfan3l => exact red_popl_fan3l_fit geoG notRedRec fitP0r nFx0 hzp qa hqa hred
  | Zfan0r => exact red_popl_hat_fit geoG notRedRec fitP0r nFx0 hzp qa hqa hred
  | Zfan1r => exact red_popl_fan1r_fit geoG notRedRec fitP0r nFx0 hzp qa hqa hred
  | Zfan2r => exact red_popl_fan2r_fit geoG notRedRec fitP0r nFx0 hzp qa hqa hred
  | Zfan3r => exact red_popl_fan3r_fit geoG notRedRec fitP0r nFx0 hzp qa hqa hred

end RedpartRec

end Hypermap

/-! ### Matching questions against zipper parts -/

/-- Coq `fitqzp zp q`: the arities specified by `q`, for a traversal starting at `zdart zp`, are
the tops of the corresponding ranges in `zp`. -/
def fitqzp (ahub : Qarity) (p0l p0r : Part) (zp : Zpart) : Question → Bool
  | Qask0 => true
  | Qask1 qa => fitqa (zrange ahub zp) qa
  | QaskL qa ql =>
    if fitqa (zrange ahub zp) qa then fitqzp ahub p0l p0r (zstepLt p0l p0r zp) ql else false
  | QaskR qa qr =>
    if fitqa (zrange ahub zp) qa then fitqzp ahub p0l p0r (zstepRt p0l p0r zp) qr else false
  | QaskLR qa ql qr =>
    if fitqa (zrange ahub zp) qa then
      if fitqzp ahub p0l p0r (zstepL p0l p0r zp) ql then
        fitqzp ahub p0l p0r (zstepR p0l p0r zp) qr
      else false
    else false
  | QaskLL qa ql =>
    let zpl := zstepL p0l p0r zp
    if fitqa (zrange ahub zpl) qa then fitqzp ahub p0l p0r (zstepL p0l p0r zpl) ql else false
  | QaskRR qa qr =>
    let zpr := zstepR p0l p0r zp
    if fitqa (zrange ahub zpr) qa then fitqzp ahub p0l p0r (zstepR p0l p0r zpr) qr else false

/-- Coq `red_popqzp zp q`: assuming `fitqzp zp q`, `red_pop` succeeds on all the zipper parts
tested for arity during the traversal of question `q`. -/
def redPopqzp (ahub : Qarity) (redRec : Part → Bool) (p0l p0r : Part) (zp : Zpart) :
    Question → Bool
  | Qask0 => true
  | Qask1 _ => redPop ahub redRec p0r zp
  | QaskL _ ql =>
    redPop ahub redRec p0r zp && redPopqzp ahub redRec p0l p0r (zstepLt p0l p0r zp) ql
  | QaskR _ qr =>
    redPop ahub redRec p0r zp && redPopqzp ahub redRec p0l p0r (zstepRt p0l p0r zp) qr
  | QaskLR _ ql qr =>
    redPop ahub redRec p0r zp &&
      (redPopqzp ahub redRec p0l p0r (zstepL p0l p0r zp) ql &&
        redPopqzp ahub redRec p0l p0r (zstepR p0l p0r zp) qr)
  | QaskLL _ ql =>
    let zpl := zstepL p0l p0r zp
    redPop ahub redRec p0r zpl && redPopqzp ahub redRec p0l p0r (zstepL p0l p0r zpl) ql
  | QaskRR _ qr =>
    let zpr := zstepR p0l p0r zp
    redPop ahub redRec p0r zpr && redPopqzp ahub redRec p0l p0r (zstepR p0l p0r zpr) qr

/-- `fitqa` fails on the free range. -/
private theorem fitqa_pr59 (qa : Qarity) : fitqa .pr59 qa = false := by cases qa <;> rfl

/-- Coq `fitqzp_proper`. -/
theorem fitqzp_proper {ahub : Qarity} {p0l p0r : Part} {zp : Zpart} {q : Question}
    (h : fitqzp ahub p0l p0r zp q = true) : Qask0 = q ∨ zproper zp = true := by
  cases q with
  | Qask0 => exact Or.inl rfl
  | _ =>
    right
    obtain ⟨zi, pl, pr⟩ := zp
    cases zi <;> first
      | rfl
      | simp [fitqzp, zrange, zstepL, zstepR, fitqa_pr59] at h

namespace Hypermap

open Redpart

variable {D : Type u} {G : Hypermap D}

/-! Unfolding `fitq` (helpers). -/

/-- `fitq` on a `Qask0` question. -/
private theorem fitq_Qask0 (x : D) : G.fitq x Qask0 := rfl

/-- `fitq` on a `Qask1` question. -/
private theorem fitq_Qask1 (x : D) (qa : Qarity) :
    G.fitq x (Qask1 qa) ↔ (qa : ℕ) = G.arity x := by
  simp [fitq, flatq, walkq]

/-- `fitq` on a `QaskL` question. -/
private theorem fitq_QaskL (x : D) (qa : Qarity) (ql : Question) :
    G.fitq x (QaskL qa ql) ↔ (qa : ℕ) = G.arity x ∧ G.fitq (G.qstepL x) ql := by
  simp only [fitq, flatq, walkq, List.map_cons, List.cons.injEq]

/-- `fitq` on a `QaskR` question. -/
private theorem fitq_QaskR (x : D) (qa : Qarity) (qr : Question) :
    G.fitq x (QaskR qa qr) ↔ (qa : ℕ) = G.arity x ∧ G.fitq (G.qstepR x) qr := by
  simp only [fitq, flatq, walkq, List.map_cons, List.cons.injEq]

/-- `fitq` on a `QaskLR` question. -/
private theorem fitq_QaskLR (x : D) (qa : Qarity) (ql qr : Question) :
    G.fitq x (QaskLR qa ql qr) ↔
      (qa : ℕ) = G.arity x ∧ G.fitq (G.qstepL x) ql ∧ G.fitq (G.qstepR x) qr := by
  rw [fitq, flatq, walkq, List.map_cons, List.cons.injEq, fitq_cat]
  exact Iff.rfl

/-- `fitq` on a `QaskLL` question. -/
private theorem fitq_QaskLL (x : D) (qa : Qarity) (qll : Question) :
    G.fitq x (QaskLL qa qll) ↔
      (qa : ℕ) = G.arity (G.edge (G.node (G.qstepL x))) ∧
        G.fitq (G.qstepL (G.qstepL x)) qll := by
  simp only [fitq, flatq, walkq, List.map_cons, List.cons.injEq]

/-- `fitq` on a `QaskRR` question. -/
private theorem fitq_QaskRR (x : D) (qa : Qarity) (qrr : Question) :
    G.fitq x (QaskRR qa qrr) ↔
      (qa : ℕ) = G.arity (G.qstepR x) ∧ G.fitq (G.qstepR (G.qstepR x)) qrr := by
  simp only [fitq, flatq, walkq, List.map_cons, List.cons.injEq]

variable [Finite D]

section RedpartRec

variable (geoG : G.PlainCubicPentagonal) {ahub : Qarity} {redRec : Part → Bool}
  (notRedRec : ∀ (x : D) (p : Part), G.arity x = ahub → G.exactFitp x p = true → redRec p = false)
  {p0l p0r : Part} {x0 : D} (Dp0l : p0l = revPart p0r) (fitP0r : G.exactFitp x0 p0r = true)
  (nFx0 : G.arity x0 = ahub)

omit [Finite D] in
/-- The top of a range fitted by a question arity. -/
private theorem top_of_fitqa {r : Prange} {qa : Qarity} (h : fitqa r qa = true) :
    (qa : ℕ) = topqa r := by
  rw [fitqa_topqa, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

include geoG notRedRec Dp0l fitP0r nFx0 in
/-- Coq `fitqzp_fit`. -/
theorem fitqzp_fit (zp : Zpart) (q : Question) (hfit : fitqzp ahub p0l p0r zp q = true)
    (hred : redPopqzp ahub redRec p0l p0r zp q = true) (hzp : Zpvalid p0r zp) :
    G.fitq (G.zdart x0 zp) q := by
  have h0 := size_p0r_pos fitP0r
  induction q generalizing zp with
  | Qask0 => exact fitq_Qask0 _
  | Qask1 qa =>
    rw [fitq_Qask1]
    exact (red_pop_fit geoG notRedRec fitP0r nFx0 zp hzp qa hfit hred).symm
  | QaskL qa ql ih =>
    simp only [fitqzp] at hfit
    simp only [redPopqzp, Bool.and_eq_true] at hred
    split_ifs at hfit with Eqa
    have Dqa := red_pop_fit geoG notRedRec fitP0r nFx0 zp hzp qa Eqa hred.1
    rw [fitq_QaskL]
    refine ⟨Dqa.symm, ?_⟩
    rcases fitqzp_proper hfit with hq | hprop
    · subst hq; exact fitq_Qask0 _
    · have htop : G.ZpfitTop ahub x0 zp := by rw [ZpfitTop, Dqa, top_of_fitqa Eqa]
      rw [← zdart_stepLt geoG Dp0l fitP0r zp htop hzp hprop]
      exact ih _ hfit hred.2 (zpvalid_stepLt Dp0l h0 zp hzp)
  | QaskR qa qr ih =>
    simp only [fitqzp] at hfit
    simp only [redPopqzp, Bool.and_eq_true] at hred
    split_ifs at hfit with Eqa
    have Dqa := red_pop_fit geoG notRedRec fitP0r nFx0 zp hzp qa Eqa hred.1
    rw [fitq_QaskR]
    refine ⟨Dqa.symm, ?_⟩
    rcases fitqzp_proper hfit with hq | hprop
    · subst hq; exact fitq_Qask0 _
    · have htop : G.ZpfitTop ahub x0 zp := by rw [ZpfitTop, Dqa, top_of_fitqa Eqa]
      rw [← zdart_stepRt geoG Dp0l fitP0r zp htop hzp hprop]
      exact ih _ hfit hred.2 (zpvalid_stepRt Dp0l h0 zp hzp)
  | QaskLR qa ql qr ihl ihr =>
    simp only [fitqzp] at hfit
    simp only [redPopqzp, Bool.and_eq_true] at hred
    split_ifs at hfit with Eqa fit_ql
    have Dqa := red_pop_fit geoG notRedRec fitP0r nFx0 zp hzp qa Eqa hred.1
    rw [fitq_QaskLR]
    refine ⟨Dqa.symm, ?_, ?_⟩
    · rcases fitqzp_proper fit_ql with hq | hprop
      · subst hq; exact fitq_Qask0 _
      · rw [← zdart_stepL geoG Dp0l fitP0r zp hzp hprop]
        exact ihl _ fit_ql hred.2.1 (zpvalid_stepL Dp0l h0 zp hzp)
    · rcases fitqzp_proper hfit with hq | hprop
      · subst hq; exact fitq_Qask0 _
      · rw [← zdart_stepR geoG Dp0l fitP0r zp hzp hprop]
        exact ihr _ hfit hred.2.2 (zpvalid_stepR Dp0l h0 zp hzp)
  | QaskLL qa ql ih =>
    simp only [fitqzp] at hfit
    simp only [redPopqzp, Bool.and_eq_true] at hred
    split_ifs at hfit with Eqa
    have hpl := fitqa_proper ahub _ _ Eqa
    have hzpl := zpvalid_stepL Dp0l h0 zp hzp
    have e1 := zdart_stepL geoG Dp0l fitP0r zp hzp hpl
    have Dqa := red_pop_fit geoG notRedRec fitP0r nFx0 _ hzpl qa Eqa hred.1
    rw [fitq_QaskLL, ← e1]
    refine ⟨?_, ?_⟩
    · have e2 : G.arity (G.edge (G.node (G.zdart x0 (zstepL p0l p0r zp)))) =
          G.arity (G.zdart x0 (zstepL p0l p0r zp)) := by
        rw [← G.arity_face (G.edge (G.node _)), G.nodeK]
      rw [e2, Dqa]
    · rcases fitqzp_proper hfit with hq | hprop
      · subst hq; exact fitq_Qask0 _
      · rw [← zdart_stepL geoG Dp0l fitP0r _ hzpl hprop]
        exact ih _ hfit hred.2 (zpvalid_stepL Dp0l h0 _ hzpl)
  | QaskRR qa qr ih =>
    simp only [fitqzp] at hfit
    simp only [redPopqzp, Bool.and_eq_true] at hred
    split_ifs at hfit with Eqa
    have hpr := fitqa_proper ahub _ _ Eqa
    have hzpr := zpvalid_stepR Dp0l h0 zp hzp
    have e1 := zdart_stepR geoG Dp0l fitP0r zp hzp hpr
    have Dqa := red_pop_fit geoG notRedRec fitP0r nFx0 _ hzpr qa Eqa hred.1
    rw [fitq_QaskRR, ← e1]
    refine ⟨Dqa.symm, ?_⟩
    rcases fitqzp_proper hfit with hq | hprop
    · subst hq; exact fitq_Qask0 _
    · rw [← zdart_stepR geoG Dp0l fitP0r _ hzpr hprop]
      exact ih _ hfit hred.2 (zpvalid_stepR Dp0l h0 _ hzpr)

end RedpartRec

end Hypermap

/-! ### Matching leaves of the quiz tree (Coq section `RedQztLeaf`) -/

/-- Coq `red_qzt_leaf qtl` (section `RedQztLeaf`, with variables `zp1 zp2 zp3`): in the leaf
list `qtl`, both `fitqzp` and `red_popqzp` succeed for all the `zpi qi` pairs, for one of the
leaves `QztLeaf q1 q2 q3 _`. -/
def redQztLeaf (ahub : Qarity) (redRec : Part → Bool) (p0l p0r : Part) (zp1 zp2 zp3 : Zpart) :
    QuizTree → Bool
  | QztLeaf q1 q2 q3 qtl' =>
    if fitqzp ahub p0l p0r zp3 q3 then
      if fitqzp ahub p0l p0r zp2 q2 then
        if fitqzp ahub p0l p0r zp1 q1 then
          redPopqzp ahub redRec p0l p0r zp1 q1 &&
            (redPopqzp ahub redRec p0l p0r zp2 q2 && redPopqzp ahub redRec p0l p0r zp3 q3)
        else redQztLeaf ahub redRec p0l p0r zp1 zp2 zp3 qtl'
      else redQztLeaf ahub redRec p0l p0r zp1 zp2 zp3 qtl'
    else redQztLeaf ahub redRec p0l p0r zp1 zp2 zp3 qtl'
  | _ => false

namespace Hypermap

variable {D : Type u} [Finite D] {G : Hypermap D}

section RedpartRec

variable (geoG : G.PlainCubicPentagonal) {ahub : Qarity} {redRec : Part → Bool}
  (notRedRec : ∀ (x : D) (p : Part), G.arity x = ahub → G.exactFitp x p = true → redRec p = false)
  {p0l p0r : Part} {x0 : D} (Dp0l : p0l = revPart p0r) (fitP0r : G.exactFitp x0 p0r = true)
  (nFx0 : G.arity x0 = ahub)

omit [Finite D] in
/-- A question fitted by a proper zipper part fits at its dart. -/
private theorem fitq_of_fitqzp {zp : Zpart} {q : Question} {x : D}
    (hfit : fitqzp ahub p0l p0r zp q = true) (hzpf : G.Zpfit x0 x zp)
    (H : zproper zp = true → G.fitq (G.zdart x0 zp) q) : G.fitq x q := by
  rcases fitqzp_proper hfit with hq | hprop
  · subst hq; rfl
  · rw [← hzpf hprop]; exact H hprop

include geoG notRedRec Dp0l fitP0r nFx0 in
/-- Coq `red_qzt_leaf_fit` (the Coq conclusion `~ ~~ qzt_fitl x qtl` is `G.QztFitl x qtl`). -/
theorem red_qzt_leaf_fit (zp1 zp2 zp3 : Zpart) (qtl : QuizTree)
    (h : redQztLeaf ahub redRec p0l p0r zp1 zp2 zp3 qtl = true) :
    qztProper qtl = true ∧
      ∀ x : D,
        G.Zpfit x0 (G.qstepR x) zp1 → Zpvalid p0r zp1 →
        G.Zpfit x0 (G.qstepR (G.node x)) zp2 → Zpvalid p0r zp2 →
        G.Zpfit x0 (G.qstepR (G.node (G.node x))) zp3 → Zpvalid p0r zp3 →
        G.QztFitl x qtl := by
  refine ⟨by cases qtl <;> simp_all [redQztLeaf, qztProper], ?_⟩
  intro x fit1 ok1 fit2 ok2 fit3 ok3
  induction qtl with
  | QztLeaf q1 q2 q3 qtl ih =>
    simp only [redQztLeaf] at h
    simp only [QztFitl]
    split_ifs at h with c3 c2 c1
    · simp only [Bool.and_eq_true] at h
      left
      exact ⟨fitq_of_fitqzp c1 fit1 fun _ =>
          fitqzp_fit geoG notRedRec Dp0l fitP0r nFx0 zp1 q1 c1 h.1 ok1,
        fitq_of_fitqzp c2 fit2 fun _ =>
          fitqzp_fit geoG notRedRec Dp0l fitP0r nFx0 zp2 q2 c2 h.2.1 ok2,
        fitq_of_fitqzp c3 fit3 fun _ =>
          fitqzp_fit geoG notRedRec Dp0l fitP0r nFx0 zp3 q3 c3 h.2.2 ok3⟩
    all_goals exact Or.inr (ih h)
  | _ => simp [redQztLeaf] at h

end RedpartRec

end Hypermap

/-! ### Quiz tree lookup by range -/

/-- Coq `qzt_getr r qt`: the subtree of the quiz tree node `qt` for the top value of `r`. -/
def qztGetr (r : Prange) (qt : QuizTree) : QuizTree :=
  match qt with
  | QztNode qt5 qt6 qt7 qt8 =>
    match r with
    | .pr55 => qt5
    | .pr56 => qt6
    | .pr66 => qt6
    | .pr57 => qt7
    | .pr67 => qt7
    | .pr77 => qt7
    | .pr58 => qt8
    | .pr68 => qt8
    | .pr78 => qt8
    | .pr88 => qt8
    | _ => QztNil
  | _ => QztNil

/-- Coq `qzt_getr_fit` (the Coq statement names `qa := topqa r` with a `let`). -/
theorem qzt_getr_fit (r : Prange) (qt1 : QuizTree) (h : qztProper (qztGetr r qt1) = true) :
    fitqa r (topqa r) = true ∧ qztGet1 (topqa r) qt1 = qztGetr r qt1 ∧ qztProper qt1 = true := by
  cases qt1 with
  | QztNode qt5 qt6 qt7 qt8 =>
    cases r <;> first | exact ⟨rfl, rfl, rfl⟩ | simp [qztGetr, qztProper] at h
  | _ => simp [qztGetr, qztProper] at h

namespace Hypermap

variable {D : Type u} {G : Hypermap D}

/-- Coq `redpart_no_qzt_fitl` (section `Redpart`, with the section variable `qt` and hypothesis
`fit'qt : forall y, ~~ qzt_fit y qt`). -/
theorem redpart_no_qzt_fitl {qt : QuizTree} (fit'qt : ∀ y : D, ¬ G.QztFit y qt) (y : D)
    (qa1 qa2 qa3 : Qarity) (Dqa1 : G.arity y = qa1) (Dqa2 : G.arity (G.node y) = qa2)
    (Dqa3 : G.arity (G.node (G.node y)) = qa3) : ¬ G.QztFitl y (qztGet3 qa1 qa2 qa3 qt) := by
  intro hfit
  apply fit'qt y
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · rw [Dqa1, qarity_of_qarity]
  · rw [Dqa2, qarity_of_qarity]
  · rw [Dqa3, qarity_of_qarity]
  · rw [Dqa1, Dqa2, Dqa3, qarity_of_qarity, qarity_of_qarity, qarity_of_qarity]
    exact hfit

end Hypermap

end FourColor
