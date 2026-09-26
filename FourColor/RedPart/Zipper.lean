/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Part
import FourColor.QuizTree

/-!
# Reducibility check for parts: zipper parts  (port of `redpart.v`, part 1 of 3)

`redpart.v` checks that every 2-neighbourhood that matches a part contains the kernel of one of
the 633 reducible configurations: no dart of a plain cubic pentagonal map in which no quiz of the
quiz tree fits can fit the part. This file ports the first half of the Coq section `RedpartRec`:
the zipper parts used to navigate a part `p0r` (with `p0l = rev_part p0r`), and the moves along
them.

A zipper part (`Zpart`) is a pair of a left and a right part sector, the left one reversed (not
mirrored!), whose concatenation is twice `p0r`, together with an index (`ZpartLoc`) that
identifies the dart represented by the zipper part:
* the two node orbits that fall between the left and right sectors, that is, that contain a dart
  from both the left spoke and right spoke faces (`Zhub`, `Zhubl`, `Zhubr` and `Zhat`, `Zhatl`,
  `Zhatr`); the third dart is either the hub dart or a hat dart in the right sector;
* the (disjoint) `qstepL` and `qstepR` trajectories that run around the left spoke face,
  counter-clockwise and clockwise, respectively, and end with hat darts (`ZfanNl`, `ZfanNr`,
  numbered in decreasing order: the last (hat) dart is number `0`);
* `Znil`, an "out of bounds" value.

## Definitions (Coq name → Lean name)

* `zpart_loc` → `ZpartLoc` (constructors with Coq's names); `zpart` → `Zpart` (constructor
  `Zpart.mk`, Coq `Zpart`).
* `zproper` → `zproper`; `zvalid`, `zpvalid` → `Zvalid`, `Zpvalid` (their section variable
  `p0r` is their first argument).
* `zmove`, `zorg`, `zporg`, `zdart` → `G.zmove`, `G.zorg`, `G.zporg`, `G.zdart`; `zpfit` →
  `G.Zpfit`; `zpfit_top` → `G.ZpfitTop`.
* `hub_range`, `zrange` → `hubRange`, `zrange`.
* `shift_part` → `shiftPart`; the Coq local notations `p0ll`, `p0lr`, `p0rr`, `p0rl` are
  unfolded (`dropPart 1 p0l`, `shiftPart p0l p0r`, `dropPart 1 p0r`, `shiftPart p0r p0l`).
* `zshiftl`, `zshiftr`, `zfanL`, `zfanR`, `zstepL`, `zstepR`, `topqa`, `fitqa`, `popqa`,
  `zfanLt`, `zfanRt`, `zstepLt`, `zstepRt` → same names.

All the lemmas of this part of `redpart.v` are ported with their Coq names.

## Porting notes

* The Coq section variables become explicit leading arguments of the computational definitions,
  in the Coq order `qt ahub red_rec p0l p0r` (only the ones used), as in Coq after the sections
  are closed: e.g. `zshiftl p0l p0r zi zp`, `zrange ahub zp`. The computational definitions are
  first-order and non-recursive (or structurally recursive), so that they reduce in the kernel.
* The section hypotheses `geoG : plain_cubic_pentagonal G`, `Dp0l : p0l = rev_part p0r`,
  `fit_p0r : exact_fitp x0 p0r` and `nFx0 : arity x0 = nhub` are explicit hypotheses (`geoG`,
  `Dp0l`, `fitP0r`, `nFx0`) of the lemmas that use them; `nhub` is `(ahub : ℕ)`. The section
  `Let`s `De2`, `Dnf`, `Dn3`, `Dn2` are `Redpart.De2`, `Redpart.Dnf`, `Redpart.Dn3`,
  `Redpart.Dn2`, and `Dne`, `Dfn`, `Dfnn`, `Ep0r` are `Redpart.Dne`, `Redpart.Dfn`,
  `Redpart.Dfnn`, `Redpart.Ep0r` (namespace `FourColor.Hypermap.Redpart`, which also holds the
  proof tools of the three files).
* Dart identities are proved by normalizing both sides as words in `node` and `edge`, using
  `face = node ∘ node ∘ edge`, `edge ∘ edge = id` and `node ∘ node ∘ node = id` in a plain cubic
  map (tactic `hnorm`), after using `face^[arity y] y = y` when needed (tactic `wrap_tac`), and
  arity identities by exhibiting a face offset (tactics `arity_tac`, `arity_wrap_tac`). These
  replace the Coq rewrite chains.
* `zproper_shiftl` and `zproper_shiftr` state `if zi is Znil then false else true` as a `match`.
* `zvalid_initl`, `zvalid_initr`, `zpvalid_shiftl`, `zpvalid_shiftr` and the `zpvalid_step*`
  lemmas take the positivity of `size_part p0l` (or `p0r`) as a hypothesis, which Coq derives
  from the section hypotheses (`Ep0r`, `nFx0`, `orderSpred`); `Redpart.size_p0l_pos` and
  `Redpart.size_p0r_pos` derive it from `fitP0r`. The section `Let pentaG` is
  `geoG.pentagonal`.
* Additional helper lemmas (not in Coq): `zdart_mk`, `zporg_mk`, `zorg_cons*`, `zvalid_fit_r`,
  `fitp_head_l`, `arity_zfanl`, `mem_hubRange`, `catrev_shift`, `size_shift_part`,
  `zshift[lr]_nil`, `zshift[lr]_one`, `zshift[lr]_cases`, `zproper_mk`, `zorg_size2`,
  `size_zvalid`, `zfanL_dart`, `zfanR_dart`, `zfanR_dart'`, and the `Redpart` tools.
-/

namespace FourColor

universe u

/-! ### Zipper parts -/

/-- Coq `zpart_loc`: the index type for zipper part dart locations: `Z[hub|hat][lr]?` for the
hub/hat inter-spoke nodes, `ZfanNl`, `ZfanNr` (`N` in `0..3`) for the fan locations, and `Znil`
for "out of bounds" locations. -/
inductive ZpartLoc : Type where
  /-- Coq `Znil`: the out-of-bounds error value. -/
  | Znil
  /-- Coq `Zhub`: the hub dart of the hub-side node cycle. -/
  | Zhub
  /-- Coq `Zhubl`: the left spoke dart of the hub-side node cycle. -/
  | Zhubl
  /-- Coq `Zhubr`: the right spoke dart of the hub-side node cycle. -/
  | Zhubr
  /-- Coq `Zhat`: the hat dart of the hat-side node cycle. -/
  | Zhat
  /-- Coq `Zhatl`: the left spoke dart of the hat-side node cycle. -/
  | Zhatl
  /-- Coq `Zhatr`: the right spoke dart of the hat-side node cycle. -/
  | Zhatr
  /-- Coq `Zfan0l`: the last dart of the left step chain. -/
  | Zfan0l
  /-- Coq `Zfan1l`. -/
  | Zfan1l
  /-- Coq `Zfan2l`. -/
  | Zfan2l
  /-- Coq `Zfan3l`. -/
  | Zfan3l
  /-- Coq `Zfan0r`: the last dart of the right step chain. -/
  | Zfan0r
  /-- Coq `Zfan1r`. -/
  | Zfan1r
  /-- Coq `Zfan2r`. -/
  | Zfan2r
  /-- Coq `Zfan3r`. -/
  | Zfan3r
  deriving DecidableEq, Repr, Inhabited

export ZpartLoc (Znil Zhub Zhubl Zhubr Zhat Zhatl Zhatr Zfan0l Zfan1l Zfan2l Zfan3l Zfan0r
  Zfan1r Zfan2r Zfan3r)

/-- Coq `zpart`: zipper parts. `Zpart.mk zi pl pr` (Coq `Zpart zi pl pr`) has the location
`zi`, the reversed left sector `pl` and the right sector `pr`. -/
inductive Zpart : Type where
  /-- Coq constructor `Zpart`. -/
  | mk (zi : ZpartLoc) (pl pr : Part)
  deriving DecidableEq, Repr, Inhabited

/-- Coq `zproper zp`: the index of `zp` is not `Znil`. -/
def zproper : Zpart → Bool
  | ⟨Znil, _, _⟩ => false
  | _ => true

/-- Coq `zvalid pl pr` (with the section variable `p0r` as first argument): `pl` reversed,
followed by `pr`, is `p0r` twice. -/
def Zvalid (p0r pl pr : Part) : Prop := catrevPart pl pr = catPart p0r p0r

/-- Coq `zpvalid zp`: the left/right sectors of `zp` satisfy `Zvalid`. -/
def Zpvalid (p0r : Part) : Zpart → Prop
  | ⟨_, pl, pr⟩ => Zvalid p0r pl pr

/-- Coq `zvalid_init`. -/
theorem zvalid_init {p0l p0r : Part} (Dp0l : p0l = revPart p0r) : Zvalid p0r p0l p0r := by
  rw [Zvalid, catrev_part_eq, Dp0l, rev_rev_part]

namespace Hypermap

variable {D : Type u}

section Defs

variable (G : Hypermap D)

/-- Coq `zmove zi x`: the dart indexed by `zi`, from the reference (hub) dart `x`. -/
def zmove (zi : ZpartLoc) (x : D) : D :=
  match zi with
  | Znil => x
  | Zhub => x
  | Zhubl => G.node x
  | Zhubr => G.node (G.node x)
  | Zhat => G.node (G.edge (G.node (G.node x)))
  | Zhatl => G.edge (G.node (G.node x))
  | Zhatr => G.face (G.node (G.node x))
  | Zfan0l => G.face (G.edge ((G.edge ∘ G.node)^[2] (G.node x)))
  | Zfan1l => G.face (G.edge ((G.edge ∘ G.node)^[3] (G.node x)))
  | Zfan2l => G.face (G.edge ((G.edge ∘ G.node)^[4] (G.node x)))
  | Zfan3l => G.face (G.edge ((G.edge ∘ G.node)^[5] (G.node x)))
  | Zfan0r => G.edge (G.face^[2] (G.node x))
  | Zfan1r => G.edge (G.face^[3] (G.node x))
  | Zfan2r => G.edge (G.face^[4] (G.node x))
  | Zfan3r => G.edge (G.face^[5] (G.node x))

/-- Coq `zorg pl` (with the section variable `x0`): the reference hub dart (in the face orbit of
`x0`) for a zipper part with left sector `pl`, i.e., the reference dart for the subpart just
after `pl`. -/
def zorg (x0 : D) (pl : Part) : D := G.face^[sizePart pl] x0

/-- Coq `zporg zp`: the reference dart of the zipper part `zp`. -/
def zporg (x0 : D) : Zpart → D
  | ⟨_, pl, _⟩ => G.zorg x0 pl

/-- Coq `zdart zp`: the dart in the second neighbourhood of `x0` indexed by `zp`. -/
def zdart (x0 : D) : Zpart → D
  | ⟨zi, pl, _⟩ => G.zmove zi (G.zorg x0 pl)

/-- Coq `zpfit x zp`: if `zp` is proper, then `zdart zp = x`. -/
def Zpfit (x0 x : D) (zp : Zpart) : Prop := zproper zp = true → G.zdart x0 zp = x

/-- Unfolding `zdart`. -/
@[simp] theorem zdart_mk (x0 : D) (zi : ZpartLoc) (pl pr : Part) :
    G.zdart x0 ⟨zi, pl, pr⟩ = G.zmove zi (G.zorg x0 pl) := rfl

/-- Unfolding `zporg`. -/
@[simp] theorem zporg_mk (x0 : D) (zi : ZpartLoc) (pl pr : Part) :
    G.zporg x0 ⟨zi, pl, pr⟩ = G.zorg x0 pl := rfl

/-- `zorg` of a part extended by one subpart. -/
theorem zorg_cons (x0 : D) (s h : Prange) (pl : Part) :
    G.zorg x0 (.cons s h pl) = G.face (G.zorg x0 pl) :=
  Function.iterate_succ_apply' _ _ _

/-- `zorg` of a part extended by one subpart. -/
theorem zorg_cons6 (x0 : D) (h f1 : Prange) (pl : Part) :
    G.zorg x0 (.cons6 h f1 pl) = G.face (G.zorg x0 pl) :=
  Function.iterate_succ_apply' _ _ _

/-- `zorg` of a part extended by one subpart. -/
theorem zorg_cons7 (x0 : D) (h f1 f2 : Prange) (pl : Part) :
    G.zorg x0 (.cons7 h f1 f2 pl) = G.face (G.zorg x0 pl) :=
  Function.iterate_succ_apply' _ _ _

/-- `zorg` of a part extended by one subpart. -/
theorem zorg_cons8 (x0 : D) (h f1 f2 f3 : Prange) (pl : Part) :
    G.zorg x0 (.cons8 h f1 f2 f3 pl) = G.face (G.zorg x0 pl) :=
  Function.iterate_succ_apply' _ _ _

end Defs

/-! ### Section `Let`s and proof tools -/

namespace Redpart

variable [Finite D] {G : Hypermap D}

/-- In a plain cubic map, `face = node ∘ node ∘ edge`. -/
theorem face_nne (geoG : G.PlainCubicPentagonal) (z : D) :
    G.face z = G.node (G.node (G.edge z)) := by
  rw [G.cubic_eq' geoG.cubic, G.plain_eq geoG.plain]

/-- Coq section `Let De2`. -/
theorem De2 (geoG : G.PlainCubicPentagonal) (x : D) : G.edge (G.edge x) = x :=
  G.plain_eq geoG.plain x

/-- Coq section `Let Dnf`. -/
theorem Dnf (geoG : G.PlainCubicPentagonal) (x : D) : G.node (G.face x) = G.edge x :=
  G.plain_eq' geoG.plain x

/-- Coq section `Let Dn3`. -/
theorem Dn3 (geoG : G.PlainCubicPentagonal) (x : D) : G.node (G.node (G.node x)) = x :=
  G.cubic_eq geoG.cubic x

/-- Coq section `Let Dn2`. -/
theorem Dn2 (geoG : G.PlainCubicPentagonal) (x : D) : G.node (G.node x) = G.face (G.edge x) :=
  G.cubic_eq' geoG.cubic x

/-- Coq section `Let Dne`. -/
theorem Dne (geoG : G.PlainCubicPentagonal) (x : D) :
    G.node (G.edge x) = G.face (G.edge (G.face x)) := by
  rw [← G.cubic_eq' geoG.cubic, G.plain_eq' geoG.plain]

/-- Coq section `Let Dfn`. -/
theorem Dfn (n : ℕ) (x : D) (h : G.arity x = n) : x = G.face^[n] x := by
  rw [← h, G.iter_face_arity]

/-- Coq section `Let Dfnn`. -/
theorem Dfnn (geoG : G.PlainCubicPentagonal) (n : ℕ) (x : D) (h : G.arity x = n) :
    G.node x = G.edge (G.face^[n - 1] x) := by
  have hn : 0 < n := h ▸ order_pos G.faceI x
  conv_lhs => rw [Dfn n x h, show n = n - 1 + 1 by omega, Function.iterate_succ_apply']
  exact Dnf geoG _

/-- `face^[k] z = z` when `z` has arity `k`. -/
theorem iter_face_of_arity {z : D} {k : ℕ} (h : G.arity z = k) : G.face^[k] z = z := by
  rw [← h, G.iter_face_arity]

/-- Arity is constant along face orbits (the tool for arity identities). -/
theorem arity_eq_iter (i : ℕ) {a b : D} (h : a = G.face^[i] b) : G.arity a = G.arity b := by
  rw [h, G.arity_iter_face]

omit [Finite D] in
/-- Every dart of a pentagonal map is in the free range. -/
theorem mem59 (geoG : G.PlainCubicPentagonal) (y : D) : memRange .pr59 (G.arity y) = true :=
  decide_eq_true (geoG.pentagonal y)

/-- Membership in the singleton range `pr55`. -/
theorem mem55 {n : ℕ} (h : memRange .pr55 n = true) : n = 5 := by simpa [memRange] using h

/-- Membership in the singleton range `pr66`. -/
theorem mem66 {n : ℕ} (h : memRange .pr66 n = true) : n = 6 := by simpa [memRange] using h

/-- Membership in the singleton range `pr77`. -/
theorem mem77 {n : ℕ} (h : memRange .pr77 n = true) : n = 7 := by simpa [memRange] using h

/-- Membership in the singleton range `pr88`. -/
theorem mem88 {n : ℕ} (h : memRange .pr88 n = true) : n = 8 := by simpa [memRange] using h

set_option hygiene false in
/-- `hnorm`: normalize the darts of a plain cubic map `G` (with hypothesis `geoG`) as words in
`node` and `edge`, unfolding `face`, `qstepL`, `qstepR`, iterates and `zorg` of a cons. -/
scoped syntax "hnorm" (Lean.Parser.Tactic.location)? : tactic

set_option hygiene false in
macro_rules
  | `(tactic| hnorm $[$loc]?) =>
    `(tactic| simp only [Redpart.face_nne geoG, Redpart.De2 geoG, Redpart.Dn3 geoG,
        Function.iterate_succ_apply', Function.iterate_zero_apply, Function.comp_apply,
        qstepL, qstepR, zorg_cons, zorg_cons6, zorg_cons7, zorg_cons8, SubpartLoc.move] $[$loc]?)

/-- `wrap_tac h` (with `h : face^[k] z = z`): prove a dart identity after inserting
`face^[k]` in front of `z` on one side. -/
scoped macro "wrap_tac " h:term : tactic =>
  `(tactic| (hnorm <;> first
    | ((conv_lhs => rw [← $h:term]); hnorm; done)
    | ((conv_rhs => rw [← $h:term]); hnorm; done)))

/-- `arity_tac`: prove `arity a = arity b` by finding `i` with `a = face^[i] b` or
`b = face^[i] a` (`i ≤ 6`). -/
scoped macro "arity_tac" : tactic => `(tactic| first
  | (refine Redpart.arity_eq_iter 0 ?_; hnorm; done)
  | (refine Redpart.arity_eq_iter 1 ?_; hnorm; done)
  | (refine Redpart.arity_eq_iter 2 ?_; hnorm; done)
  | (refine Redpart.arity_eq_iter 3 ?_; hnorm; done)
  | (refine Redpart.arity_eq_iter 4 ?_; hnorm; done)
  | (refine Redpart.arity_eq_iter 5 ?_; hnorm; done)
  | (refine Redpart.arity_eq_iter 6 ?_; hnorm; done)
  | (refine (Redpart.arity_eq_iter 1 ?_).symm; hnorm; done)
  | (refine (Redpart.arity_eq_iter 2 ?_).symm; hnorm; done)
  | (refine (Redpart.arity_eq_iter 3 ?_).symm; hnorm; done)
  | (refine (Redpart.arity_eq_iter 4 ?_).symm; hnorm; done)
  | (refine (Redpart.arity_eq_iter 5 ?_).symm; hnorm; done)
  | (refine (Redpart.arity_eq_iter 6 ?_).symm; hnorm; done))

/-- `arity_wrap_tac h`: `arity_tac`, using `wrap_tac h` for the dart identities. -/
scoped macro "arity_wrap_tac " h:term : tactic => `(tactic| first
  | (refine Redpart.arity_eq_iter 0 ?_; wrap_tac $h)
  | (refine Redpart.arity_eq_iter 1 ?_; wrap_tac $h)
  | (refine Redpart.arity_eq_iter 2 ?_; wrap_tac $h)
  | (refine Redpart.arity_eq_iter 3 ?_; wrap_tac $h)
  | (refine Redpart.arity_eq_iter 4 ?_; wrap_tac $h)
  | (refine Redpart.arity_eq_iter 5 ?_; wrap_tac $h)
  | (refine Redpart.arity_eq_iter 6 ?_; wrap_tac $h)
  | (refine (Redpart.arity_eq_iter 1 ?_).symm; wrap_tac $h)
  | (refine (Redpart.arity_eq_iter 2 ?_).symm; wrap_tac $h)
  | (refine (Redpart.arity_eq_iter 3 ?_).symm; wrap_tac $h)
  | (refine (Redpart.arity_eq_iter 4 ?_).symm; wrap_tac $h)
  | (refine (Redpart.arity_eq_iter 5 ?_).symm; wrap_tac $h)
  | (refine (Redpart.arity_eq_iter 6 ?_).symm; wrap_tac $h))

omit [Finite D] in
/-- Coq section `Let Ep0r`. -/
theorem Ep0r {x0 : D} {p0r : Part} {ahub : Qarity} (fitP0r : G.exactFitp x0 p0r = true)
    (nFx0 : G.arity x0 = ahub) : sizePart p0r = ahub := by
  simp only [exactFitp, Bool.and_eq_true, beq_iff_eq] at fitP0r
  rw [← fitP0r.1, nFx0]

omit [Finite D] in
/-- The size of `p0r` is the arity of `x0`. -/
theorem size_p0r {x0 : D} {p0r : Part} (fitP0r : G.exactFitp x0 p0r = true) :
    sizePart p0r = G.arity x0 := by
  simp only [exactFitp, Bool.and_eq_true, beq_iff_eq] at fitP0r
  exact fitP0r.1.symm

omit [Finite D] in
/-- The size of `p0l` is the arity of `x0`. -/
theorem size_p0l {x0 : D} {p0l p0r : Part} (Dp0l : p0l = revPart p0r)
    (fitP0r : G.exactFitp x0 p0r = true) : sizePart p0l = G.arity x0 := by
  rw [Dp0l, size_rev_part, size_p0r fitP0r]

/-- `p0l` is not empty. -/
theorem size_p0l_pos {x0 : D} {p0l p0r : Part} (Dp0l : p0l = revPart p0r)
    (fitP0r : G.exactFitp x0 p0r = true) : 0 < sizePart p0l := by
  rw [size_p0l Dp0l fitP0r]; exact order_pos G.faceI x0

/-- `p0r` is not empty. -/
theorem size_p0r_pos {x0 : D} {p0r : Part} (fitP0r : G.exactFitp x0 p0r = true) :
    0 < sizePart p0r := by
  rw [size_p0r fitP0r]; exact order_pos G.faceI x0

omit [Finite D] in
/-- The first subpart of a part fitting at `x`. -/
theorem fitp_head (geoG : G.PlainCubicPentagonal) {x : D} {p : Part} (h : G.fitp x p = true) :
    memRange (getSpoke p) (G.arity (G.edge x)) = true ∧
    memRange (getHat p) (G.arity (G.edge (G.face^[2] (G.edge x)))) = true ∧
    memRange (getFan1r p) (G.arity (G.edge (G.face^[3] (G.edge x)))) = true ∧
    memRange (getFan2r p) (G.arity (G.edge (G.face^[4] (G.edge x)))) = true ∧
    memRange (getFan3r p) (G.arity (G.edge (G.face^[5] (G.edge x)))) = true := by
  cases p with
  | nil => exact ⟨mem59 geoG _, mem59 geoG _, mem59 geoG _, mem59 geoG _, mem59 geoG _⟩
  | cons s h p =>
    simp only [fitp, SubpartLoc.move, Bool.and_eq_true] at h
    exact ⟨h.1, h.2.1, mem59 geoG _, mem59 geoG _, mem59 geoG _⟩
  | cons6 h f1 p =>
    simp only [fitp, SubpartLoc.move, Bool.and_eq_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, mem59 geoG _, mem59 geoG _⟩
  | cons7 h f1 f2 p =>
    simp only [fitp, SubpartLoc.move, Bool.and_eq_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, mem59 geoG _⟩
  | cons8 h f1 f2 f3 p =>
    simp only [fitp, SubpartLoc.move, Bool.and_eq_true] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

end Redpart

open Redpart

/-! ### Fitting the zipper parts -/

section RedpartRec

variable [Finite D] {G : Hypermap D}

/-- Coq `zvalid_fit`. -/
theorem zvalid_fit {p0r : Part} {x0 : D} (fitP0r : G.exactFitp x0 p0r = true) {pl pr : Part}
    (h : Zvalid p0r pl pr) : G.fitp x0 (catrevPart pl pr) = true := by
  have e := fitP0r
  simp only [exactFitp, Bool.and_eq_true, beq_iff_eq] at e
  rw [h, G.fitp_cat, ← e.1, G.iter_face_arity, e.2, Bool.and_self]

/-- The right sector of a valid zipper part fits at its reference dart. -/
theorem zvalid_fit_r {p0r : Part} {x0 : D} (fitP0r : G.exactFitp x0 p0r = true) {pl pr : Part}
    (h : Zvalid p0r pl pr) : G.fitp (G.zorg x0 pl) pr = true := by
  have e := zvalid_fit fitP0r h
  rw [G.fitp_catrev, Bool.and_eq_true] at e
  exact e.2

/-- The first subpart of the left sector of a valid zipper part. -/
theorem fitp_head_l (geoG : G.PlainCubicPentagonal) {p0r : Part} {x0 : D}
    (fitP0r : G.exactFitp x0 p0r = true) {pl pr : Part} (h : Zvalid p0r pl pr) :
    memRange (getSpoke pl) (G.arity (G.node (G.zorg x0 pl))) = true ∧
    memRange (getHat pl) (G.arity (G.edge (G.face^[2] (G.node (G.zorg x0 pl))))) = true ∧
    memRange (getFan1r pl) (G.arity (G.edge (G.face^[3] (G.node (G.zorg x0 pl))))) = true ∧
    memRange (getFan2r pl) (G.arity (G.edge (G.face^[4] (G.node (G.zorg x0 pl))))) = true ∧
    memRange (getFan3r pl) (G.arity (G.edge (G.face^[5] (G.node (G.zorg x0 pl))))) = true := by
  cases pl with
  | nil => exact ⟨mem59 geoG _, mem59 geoG _, mem59 geoG _, mem59 geoG _, mem59 geoG _⟩
  | cons s h' pl =>
    rw [zorg_cons, Dnf geoG]
    have e := fitp_head geoG (zvalid_fit_r fitP0r (pl := pl) (pr := .cons s h' pr) h)
    exact e
  | cons6 h' f1 pl =>
    rw [zorg_cons6, Dnf geoG]
    have e := fitp_head geoG (zvalid_fit_r fitP0r (pl := pl) (pr := .cons6 h' f1 pr) h)
    exact e
  | cons7 h' f1 f2 pl =>
    rw [zorg_cons7, Dnf geoG]
    have e := fitp_head geoG (zvalid_fit_r fitP0r (pl := pl) (pr := .cons7 h' f1 f2 pr) h)
    exact e
  | cons8 h' f1 f2 f3 pl =>
    rw [zorg_cons8, Dnf geoG]
    have e := fitp_head geoG (zvalid_fit_r fitP0r (pl := pl) (pr := .cons8 h' f1 f2 f3 pr) h)
    exact e

end RedpartRec

end Hypermap

/-- Coq `hub_range`: the range for the hub; a singleton unless `ahub > 8`. -/
def hubRange (ahub : Qarity) : Prange :=
  match ahub with
  | Qa5 => .pr55
  | Qa6 => .pr66
  | Qa7 => .pr77
  | Qa8 => .pr88
  | _ => .pr99

/-- Coq `zrange zp`: the range for the arity of `zdart zp`. -/
def zrange (ahub : Qarity) : Zpart → Prange
  | ⟨Znil, _, _⟩ => .pr59
  | ⟨Zhub, _, _⟩ => hubRange ahub
  | ⟨Zhubl, pl, _⟩ => getSpoke pl
  | ⟨Zhubr, _, pr⟩ => getSpoke pr
  | ⟨Zhatl, pl, _⟩ => getSpoke pl
  | ⟨Zhat, _, pr⟩ => getHat pr
  | ⟨Zhatr, _, pr⟩ => getSpoke pr
  | ⟨Zfan0l, _, pr⟩ => getHat pr
  | ⟨Zfan1l, pl, _⟩ => getFan1l pl
  | ⟨Zfan2l, pl, _⟩ => getFan2l pl
  | ⟨Zfan3l, pl, _⟩ => getFan3l pl
  | ⟨Zfan0r, pl, _⟩ => getHat pl
  | ⟨Zfan1r, pl, _⟩ => getFan1r pl
  | ⟨Zfan2r, pl, _⟩ => getFan2r pl
  | ⟨Zfan3r, pl, _⟩ => getFan3r pl

namespace Hypermap

open Redpart

variable {D : Type u} [Finite D] {G : Hypermap D}

/-- The arity of the hub dart is in the hub range. -/
theorem mem_hubRange (ahub : Qarity) : memRange (hubRange ahub) ahub = true := by
  cases ahub <;> rfl

/-- The arities of the left step chain darts `Zfan1l`, `Zfan2l`, `Zfan3l` of the subpart at
`face y`: they are the fans of the subpart at `y` (whose spoke has arity `k`), counted
clockwise. -/
theorem arity_zfanl (geoG : G.PlainCubicPentagonal) {y : D} {k : ℕ}
    (hk : G.arity (G.edge y) = k) :
    (k = 6 → G.arity (G.zmove Zfan1l (G.face y)) = G.arity (SubpartLoc.fan1.move G y)) ∧
    (k = 7 → G.arity (G.zmove Zfan1l (G.face y)) = G.arity (SubpartLoc.fan2.move G y) ∧
      G.arity (G.zmove Zfan2l (G.face y)) = G.arity (SubpartLoc.fan1.move G y)) ∧
    (k = 8 → G.arity (G.zmove Zfan1l (G.face y)) = G.arity (SubpartLoc.fan3.move G y) ∧
      G.arity (G.zmove Zfan2l (G.face y)) = G.arity (SubpartLoc.fan2.move G y) ∧
      G.arity (G.zmove Zfan3l (G.face y)) = G.arity (SubpartLoc.fan1.move G y)) := by
  have hk' := iter_face_of_arity hk
  refine ⟨fun e => ?_, fun e => ⟨?_, ?_⟩, fun e => ⟨?_, ?_, ?_⟩⟩ <;> subst e <;>
    simp only [zmove, SubpartLoc.move] <;> arity_wrap_tac hk'

/-- The left fan chain, for a left spoke of arity `k` (`Zfan[123]l` darts). -/
private theorem fitp_fanl (geoG : G.PlainCubicPentagonal) {p0r : Part} {x0 : D}
    (fitP0r : G.exactFitp x0 p0r = true) {pl pr : Part} (h : Zvalid p0r pl pr) :
    memRange (getFan1l pl) (G.arity (G.zmove Zfan1l (G.zorg x0 pl))) = true ∧
    memRange (getFan2l pl) (G.arity (G.zmove Zfan2l (G.zorg x0 pl))) = true ∧
    memRange (getFan3l pl) (G.arity (G.zmove Zfan3l (G.zorg x0 pl))) = true := by
  cases pl with
  | nil => exact ⟨mem59 geoG _, mem59 geoG _, mem59 geoG _⟩
  | cons s h' pl => exact ⟨mem59 geoG _, mem59 geoG _, mem59 geoG _⟩
  | cons6 h' f1 pl =>
    have hf := zvalid_fit_r fitP0r (pl := pl) (pr := .cons6 h' f1 pr) h
    simp only [fitp, Bool.and_eq_true] at hf
    have e := (arity_zfanl geoG (mem66 hf.1)).1 rfl
    rw [zorg_cons6]
    exact ⟨e ▸ hf.2.2.1, mem59 geoG _, mem59 geoG _⟩
  | cons7 h' f1 f2 pl =>
    have hf := zvalid_fit_r fitP0r (pl := pl) (pr := .cons7 h' f1 f2 pr) h
    simp only [fitp, Bool.and_eq_true] at hf
    have e := (arity_zfanl geoG (mem77 hf.1)).2.1 rfl
    rw [zorg_cons7]
    exact ⟨e.1 ▸ hf.2.2.2.1, e.2 ▸ hf.2.2.1, mem59 geoG _⟩
  | cons8 h' f1 f2 f3 pl =>
    have hf := zvalid_fit_r fitP0r (pl := pl) (pr := .cons8 h' f1 f2 f3 pr) h
    simp only [fitp, Bool.and_eq_true] at hf
    have e := (arity_zfanl geoG (mem88 hf.1)).2.2 rfl
    rw [zorg_cons8]
    exact ⟨e.1 ▸ hf.2.2.2.2.1, e.2.1 ▸ hf.2.2.2.1, e.2.2 ▸ hf.2.2.1⟩

/-- Coq `zrange_dart`. -/
theorem zrange_dart (geoG : G.PlainCubicPentagonal) {ahub : Qarity} {p0r : Part} {x0 : D}
    (fitP0r : G.exactFitp x0 p0r = true) (nFx0 : G.arity x0 = ahub) (zp : Zpart)
    (hzp : Zpvalid p0r zp) : memRange (zrange ahub zp) (G.arity (G.zdart x0 zp)) = true := by
  obtain ⟨zi, pl, pr⟩ := zp
  change Zvalid p0r pl pr at hzp
  have hr := fitp_head geoG (zvalid_fit_r fitP0r hzp)
  have hl := fitp_head_l geoG fitP0r hzp
  have hf := fitp_fanl geoG fitP0r hzp
  simp only [zdart_mk, zrange]
  cases zi with
  | Znil => exact mem59 geoG _
  | Zhub =>
    simp only [zmove, zorg, G.arity_iter_face, nFx0]
    exact mem_hubRange ahub
  | Zhubl => exact hl.1
  | Zhubr =>
    have e : G.arity (G.zmove Zhubr (G.zorg x0 pl)) = G.arity (G.edge (G.zorg x0 pl)) := by
      simp only [zmove]; arity_tac
    rw [e]; exact hr.1
  | Zhat =>
    have e : G.arity (G.zmove Zhat (G.zorg x0 pl)) =
        G.arity (G.edge (G.face^[2] (G.edge (G.zorg x0 pl)))) := by
      simp only [zmove]; arity_tac
    rw [e]; exact hr.2.1
  | Zhatl =>
    have e : G.arity (G.zmove Zhatl (G.zorg x0 pl)) = G.arity (G.node (G.zorg x0 pl)) := by
      simp only [zmove]; arity_tac
    rw [e]; exact hl.1
  | Zhatr =>
    have e : G.arity (G.zmove Zhatr (G.zorg x0 pl)) = G.arity (G.edge (G.zorg x0 pl)) := by
      simp only [zmove]; arity_tac
    rw [e]; exact hr.1
  | Zfan0l =>
    have e : G.arity (G.zmove Zfan0l (G.zorg x0 pl)) =
        G.arity (G.edge (G.face^[2] (G.edge (G.zorg x0 pl)))) := by
      simp only [zmove]; arity_tac
    rw [e]; exact hr.2.1
  | Zfan1l => exact hf.1
  | Zfan2l => exact hf.2.1
  | Zfan3l => exact hf.2.2
  | Zfan0r => exact hl.2.1
  | Zfan1r => exact hl.2.2.1
  | Zfan2r => exact hl.2.2.2.1
  | Zfan3r => exact hl.2.2.2.2

end Hypermap

/-! ### Shifting zipper parts -/

/-- Coq `shift_part pl pr`: the part obtained by prepending the first subpart of `pl` to `pr`;
this is the "right" shift used to rotate zipper parts (the "left" shift is `dropPart 1`). -/
def shiftPart (p1 p2 : Part) : Part := catPart (takePart 1 p1) p2

/-- Shifting a subpart across the zipper preserves its contents. -/
theorem catrev_shift {pl pr : Part} (h : 0 < sizePart pl) :
    catrevPart (dropPart 1 pl) (shiftPart pl pr) = catrevPart pl pr := by
  cases pl with
  | nil => simp [sizePart] at h
  | _ => rfl

/-- The size of a shifted part. -/
theorem size_shift_part {p1 : Part} (p2 : Part) (h : 0 < sizePart p1) :
    sizePart (shiftPart p1 p2) = sizePart p2 + 1 := by
  cases p1 with
  | nil => simp [sizePart] at h
  | _ => simp [shiftPart, takePart, catPart, sizePart]

/-- Coq `zvalid_initl`. -/
theorem zvalid_initl {p0l p0r : Part} (Dp0l : p0l = revPart p0r) (h : 0 < sizePart p0l) :
    Zvalid p0r (dropPart 1 p0l) (shiftPart p0l p0r) := by
  rw [Zvalid, catrev_shift h]; exact zvalid_init Dp0l

/-- Coq `zvalid_initr`. -/
theorem zvalid_initr {p0l p0r : Part} (Dp0l : p0l = revPart p0r) (h : 0 < sizePart p0r) :
    Zvalid p0r (shiftPart p0r p0l) (dropPart 1 p0r) := by
  cases p0r with
  | nil => simp [sizePart] at h
  | _ => exact zvalid_init Dp0l

/-- Coq `zshiftl zi zp`: the zipper part corresponding to the location `zi` in the subpart to
the left of the location of `zp`. -/
def zshiftl (p0l p0r : Part) (zi : ZpartLoc) (zp : Zpart) : Zpart :=
  match zp with
  | ⟨_, .cons _ _ .nil, _⟩ => ⟨zi, p0l, p0r⟩
  | ⟨_, .cons6 _ _ .nil, _⟩ => ⟨zi, p0l, p0r⟩
  | ⟨_, .cons7 _ _ _ .nil, _⟩ => ⟨zi, p0l, p0r⟩
  | ⟨_, .cons8 _ _ _ _ .nil, _⟩ => ⟨zi, p0l, p0r⟩
  | ⟨_, .cons s h pl, pr⟩ => ⟨zi, pl, .cons s h pr⟩
  | ⟨_, .cons6 h f1 pl, pr⟩ => ⟨zi, pl, .cons6 h f1 pr⟩
  | ⟨_, .cons7 h f1 f2 pl, pr⟩ => ⟨zi, pl, .cons7 h f1 f2 pr⟩
  | ⟨_, .cons8 h f1 f2 f3 pl, pr⟩ => ⟨zi, pl, .cons8 h f1 f2 f3 pr⟩
  | ⟨_, .nil, _⟩ => ⟨zi, dropPart 1 p0l, shiftPart p0l p0r⟩

/-- Coq `zshiftr zi zp`: the zipper part corresponding to the location `zi` in the subpart to
the right of the location of `zp`. -/
def zshiftr (p0l p0r : Part) (zi : ZpartLoc) (zp : Zpart) : Zpart :=
  match zp with
  | ⟨_, _, .cons _ _ .nil⟩ => ⟨zi, p0l, p0r⟩
  | ⟨_, _, .cons6 _ _ .nil⟩ => ⟨zi, p0l, p0r⟩
  | ⟨_, _, .cons7 _ _ _ .nil⟩ => ⟨zi, p0l, p0r⟩
  | ⟨_, _, .cons8 _ _ _ _ .nil⟩ => ⟨zi, p0l, p0r⟩
  | ⟨_, pl, .cons s h pr⟩ => ⟨zi, .cons s h pl, pr⟩
  | ⟨_, pl, .cons6 h f1 pr⟩ => ⟨zi, .cons6 h f1 pl, pr⟩
  | ⟨_, pl, .cons7 h f1 f2 pr⟩ => ⟨zi, .cons7 h f1 f2 pl, pr⟩
  | ⟨_, pl, .cons8 h f1 f2 f3 pr⟩ => ⟨zi, .cons8 h f1 f2 f3 pl, pr⟩
  | ⟨_, _, .nil⟩ => ⟨zi, shiftPart p0r p0l, dropPart 1 p0r⟩

/-- `zshiftl` on an empty left sector. -/
theorem zshiftl_nil (p0l p0r : Part) (zi zi' : ZpartLoc) (pr : Part) :
    zshiftl p0l p0r zi ⟨zi', .nil, pr⟩ = ⟨zi, dropPart 1 p0l, shiftPart p0l p0r⟩ := rfl

/-- `zshiftl` on a left sector with one subpart. -/
theorem zshiftl_one (p0l p0r : Part) (zi zi' : ZpartLoc) {pl : Part} (pr : Part)
    (h : sizePart pl = 1) : zshiftl p0l p0r zi ⟨zi', pl, pr⟩ = ⟨zi, p0l, p0r⟩ := by
  rcases pl with _ | ⟨s, h', pl⟩ | ⟨h', f1, pl⟩ | ⟨h', f1, f2, pl⟩ | ⟨h', f1, f2, f3, pl⟩ <;>
    simp only [sizePart] at h
  · omega
  all_goals (cases pl <;> simp only [sizePart] at h <;> first | omega | rfl)

/-- Coq `zshiftl_eq`. -/
theorem zshiftl_eq (p0l p0r : Part) (zi zi' : ZpartLoc) (pl pr : Part) (h : 1 < sizePart pl) :
    zshiftl p0l p0r zi' ⟨zi, pl, pr⟩ = ⟨zi', dropPart 1 pl, shiftPart pl pr⟩ := by
  rcases pl with _ | ⟨s, h', pl⟩ | ⟨h', f1, pl⟩ | ⟨h', f1, f2, pl⟩ | ⟨h', f1, f2, f3, pl⟩ <;>
    simp only [sizePart] at h
  · omega
  all_goals (cases pl <;> simp only [sizePart] at h <;> first | omega | rfl)

/-- `zshiftr` on an empty right sector. -/
theorem zshiftr_nil (p0l p0r : Part) (zi zi' : ZpartLoc) (pl : Part) :
    zshiftr p0l p0r zi ⟨zi', pl, .nil⟩ = ⟨zi, shiftPart p0r p0l, dropPart 1 p0r⟩ := rfl

/-- `zshiftr` on a right sector with one subpart. -/
theorem zshiftr_one (p0l p0r : Part) (zi zi' : ZpartLoc) (pl : Part) {pr : Part}
    (h : sizePart pr = 1) : zshiftr p0l p0r zi ⟨zi', pl, pr⟩ = ⟨zi, p0l, p0r⟩ := by
  rcases pr with _ | ⟨s, h', pr⟩ | ⟨h', f1, pr⟩ | ⟨h', f1, f2, pr⟩ | ⟨h', f1, f2, f3, pr⟩ <;>
    simp only [sizePart] at h
  · omega
  all_goals (cases pr <;> simp only [sizePart] at h <;> first | omega | rfl)

/-- Coq `zshiftr_eq`. -/
theorem zshiftr_eq (p0l p0r : Part) (zi zi' : ZpartLoc) (pl pr : Part) (h : 1 < sizePart pr) :
    zshiftr p0l p0r zi' ⟨zi, pl, pr⟩ = ⟨zi', shiftPart pr pl, dropPart 1 pr⟩ := by
  rcases pr with _ | ⟨s, h', pr⟩ | ⟨h', f1, pr⟩ | ⟨h', f1, f2, pr⟩ | ⟨h', f1, f2, f3, pr⟩ <;>
    simp only [sizePart] at h
  · omega
  all_goals (cases pr <;> simp only [sizePart] at h <;> first | omega | rfl)

/-- The three cases of `zshiftl`. -/
theorem zshiftl_cases (p0l p0r : Part) (zi zi' : ZpartLoc) (pl pr : Part) :
    (sizePart pl = 0 ∧ pl = .nil ∧
        zshiftl p0l p0r zi ⟨zi', pl, pr⟩ = ⟨zi, dropPart 1 p0l, shiftPart p0l p0r⟩) ∨
      (sizePart pl = 1 ∧ zshiftl p0l p0r zi ⟨zi', pl, pr⟩ = ⟨zi, p0l, p0r⟩) ∨
      (1 < sizePart pl ∧
        zshiftl p0l p0r zi ⟨zi', pl, pr⟩ = ⟨zi, dropPart 1 pl, shiftPart pl pr⟩) := by
  rcases Nat.lt_trichotomy (sizePart pl) 1 with h | h | h
  · have h0 : sizePart pl = 0 := by omega
    have hpl : pl = .nil := by cases pl <;> simp_all [sizePart]
    subst hpl
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨h, zshiftl_one p0l p0r zi zi' pr h⟩)
  · exact Or.inr (Or.inr ⟨h, zshiftl_eq p0l p0r zi' zi pl pr h⟩)

/-- The three cases of `zshiftr`. -/
theorem zshiftr_cases (p0l p0r : Part) (zi zi' : ZpartLoc) (pl pr : Part) :
    (sizePart pr = 0 ∧ pr = .nil ∧
        zshiftr p0l p0r zi ⟨zi', pl, pr⟩ = ⟨zi, shiftPart p0r p0l, dropPart 1 p0r⟩) ∨
      (sizePart pr = 1 ∧ zshiftr p0l p0r zi ⟨zi', pl, pr⟩ = ⟨zi, p0l, p0r⟩) ∨
      (1 < sizePart pr ∧
        zshiftr p0l p0r zi ⟨zi', pl, pr⟩ = ⟨zi, shiftPart pr pl, dropPart 1 pr⟩) := by
  rcases Nat.lt_trichotomy (sizePart pr) 1 with h | h | h
  · have h0 : sizePart pr = 0 := by omega
    have hpr : pr = .nil := by cases pr <;> simp_all [sizePart]
    subst hpr
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨h, zshiftr_one p0l p0r zi zi' pl h⟩)
  · exact Or.inr (Or.inr ⟨h, zshiftr_eq p0l p0r zi' zi pl pr h⟩)

/-- `zproper` of a zipper part only depends on its location. -/
theorem zproper_mk (zi : ZpartLoc) (pl pr : Part) :
    zproper ⟨zi, pl, pr⟩ = (match zi with | Znil => false | _ => true) := by
  cases zi <;> rfl

/-- Coq `zpvalid_shiftl`. -/
theorem zpvalid_shiftl {p0l p0r : Part} (Dp0l : p0l = revPart p0r) (h0 : 0 < sizePart p0l)
    (zi : ZpartLoc) (zp : Zpart) (hzp : Zpvalid p0r zp) : Zpvalid p0r (zshiftl p0l p0r zi zp) := by
  obtain ⟨zi', pl, pr⟩ := zp
  change Zvalid p0r pl pr at hzp
  rcases zshiftl_cases p0l p0r zi zi' pl pr with ⟨-, -, e⟩ | ⟨-, e⟩ | ⟨h, e⟩ <;> rw [e]
  · exact zvalid_initl Dp0l h0
  · exact zvalid_init Dp0l
  · show Zvalid p0r _ _
    rw [Zvalid, catrev_shift (by omega)]; exact hzp

/-- Coq `zproper_shiftl`. -/
theorem zproper_shiftl (p0l p0r : Part) (zi : ZpartLoc) (zp : Zpart) :
    zproper (zshiftl p0l p0r zi zp) = (match zi with | Znil => false | _ => true) := by
  obtain ⟨zi', pl, pr⟩ := zp
  rcases zshiftl_cases p0l p0r zi zi' pl pr with ⟨-, -, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;>
    rw [e, zproper_mk]

/-- Coq `zpvalid_shiftr`. -/
theorem zpvalid_shiftr {p0l p0r : Part} (Dp0l : p0l = revPart p0r) (h0 : 0 < sizePart p0r)
    (zi : ZpartLoc) (zp : Zpart) (hzp : Zpvalid p0r zp) : Zpvalid p0r (zshiftr p0l p0r zi zp) := by
  obtain ⟨zi', pl, pr⟩ := zp
  change Zvalid p0r pl pr at hzp
  rcases zshiftr_cases p0l p0r zi zi' pl pr with ⟨-, -, e⟩ | ⟨-, e⟩ | ⟨h, e⟩ <;> rw [e]
  · exact zvalid_initr Dp0l h0
  · exact zvalid_init Dp0l
  · show Zvalid p0r _ _
    cases pr with
    | nil => simp [sizePart] at h
    | _ => exact hzp

/-- Coq `zproper_shiftr`. -/
theorem zproper_shiftr (p0l p0r : Part) (zi : ZpartLoc) (zp : Zpart) :
    zproper (zshiftr p0l p0r zi zp) = (match zi with | Znil => false | _ => true) := by
  obtain ⟨zi', pl, pr⟩ := zp
  rcases zshiftr_cases p0l p0r zi zi' pl pr with ⟨-, -, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ <;>
    rw [e, zproper_mk]

namespace Hypermap

open Redpart

variable {D : Type u} [Finite D] {G : Hypermap D}

/-- `edge ∘ node` cancels `face`. -/
private theorem en_iter_succ (m : ℕ) (x : D) :
    G.edge (G.node (G.face^[m + 1] x)) = G.face^[m] x := by
  rw [Function.iterate_succ_apply', G.faceK]

/-- `zorg` of a sector twice the size of `p0r` is `x0`. -/
theorem zorg_size2 {p0r : Part} {x0 : D} (fitP0r : G.exactFitp x0 p0r = true)
    {pl : Part} (h : sizePart pl = sizePart p0r + sizePart p0r) : G.zorg x0 pl = x0 := by
  rw [zorg, h, size_p0r fitP0r, Function.iterate_add_apply, G.iter_face_arity,
    G.iter_face_arity]

/-- The size of a valid left sector. -/
theorem size_zvalid {p0r pl pr : Part} (h : Zvalid p0r pl pr) :
    sizePart pl + sizePart pr = sizePart p0r + sizePart p0r := by
  have e := congrArg sizePart h
  rwa [catrev_part_eq, size_cat_part, size_cat_part, size_rev_part] at e

/-- Coq `zdart_shiftl`. -/
theorem zdart_shiftl {p0l p0r : Part} {x0 : D} (Dp0l : p0l = revPart p0r)
    (fitP0r : G.exactFitp x0 p0r = true) (zi : ZpartLoc) (zp : Zpart) :
    G.zdart x0 (zshiftl p0l p0r zi zp) = G.zmove zi (G.edge (G.node (G.zporg x0 zp))) := by
  have sz0l := size_p0l Dp0l fitP0r
  have zorg0l : G.zorg x0 p0l = x0 := by rw [zorg, sz0l, G.iter_face_arity]
  have hpos : 0 < G.arity x0 := order_pos G.faceI x0
  obtain ⟨zi', pl, pr⟩ := zp
  rcases zshiftl_cases p0l p0r zi zi' pl pr with ⟨-, rfl, e⟩ | ⟨h1, e⟩ | ⟨h, e⟩ <;>
    rw [e, zdart_mk, zporg_mk]
  · congr 1
    rw [zorg, size_drop_part, sz0l]
    conv_rhs => rw [zorg, sizePart, Function.iterate_zero_apply, ← G.iter_face_arity x0,
      show G.arity x0 = G.arity x0 - 1 + 1 by omega, en_iter_succ]
  · rw [zorg0l, zorg, h1, en_iter_succ]; rfl
  · rw [zorg, zorg, size_drop_part]
    conv_rhs => rw [show sizePart pl = sizePart pl - 1 + 1 by omega, en_iter_succ]

/-- Coq `zdart_shiftr`. -/
theorem zdart_shiftr {p0l p0r : Part} {x0 : D} (Dp0l : p0l = revPart p0r)
    (fitP0r : G.exactFitp x0 p0r = true) (zi : ZpartLoc) (zp : Zpart) (hzp : Zpvalid p0r zp) :
    G.zdart x0 (zshiftr p0l p0r zi zp) = G.zmove zi (G.face (G.zporg x0 zp)) := by
  have sz0l := size_p0l Dp0l fitP0r
  have sz0r := size_p0r fitP0r
  have zorg0l : G.zorg x0 p0l = x0 := by rw [zorg, sz0l, G.iter_face_arity]
  have hpos : 0 < sizePart p0r := size_p0r_pos fitP0r
  obtain ⟨zi', pl, pr⟩ := zp
  change Zvalid p0r pl pr at hzp
  have hsz := size_zvalid hzp
  rcases zshiftr_cases p0l p0r zi zi' pl pr with ⟨h0, rfl, e⟩ | ⟨h1, e⟩ | ⟨h, e⟩ <;>
    rw [e, zdart_mk, zporg_mk]
  · congr 1
    rw [zorg_size2 fitP0r (pl := pl) (by omega), zorg, size_shift_part _ hpos, sz0l,
      Function.iterate_succ_apply', G.iter_face_arity]
  · congr 1
    rw [zorg0l]
    have e2 : G.face (G.zorg x0 pl) = G.zorg x0 (.cons .pr59 .pr59 pl) := (zorg_cons G _ _ _ _).symm
    rw [e2, zorg_size2 fitP0r (by simp only [sizePart]; omega)]
  · rw [zorg, zorg, size_shift_part _ (by omega), Function.iterate_succ_apply']

end Hypermap

/-! ### Stepping through zipper parts -/

/-- Coq `zfanL pr`: the leftmost location in the `Zfan*l` chain in the first subpart of `pr`, or
`Znil` if the spoke arity can't be determined. -/
def zfanL : Part → ZpartLoc
  | .cons .pr55 _ _ => Zfan0l
  | .cons6 _ _ _ => Zfan1l
  | .cons7 _ _ _ _ => Zfan2l
  | .cons8 _ _ _ _ _ => Zfan3l
  | _ => Znil

/-- Coq `zfanR pl`: the rightmost location in the `Zfan*r` chain in the first subpart of `pl`,
or `Znil` if the spoke arity can't be determined. -/
def zfanR : Part → ZpartLoc
  | .cons .pr55 _ _ => Zfan0r
  | .cons6 _ _ _ => Zfan1r
  | .cons7 _ _ _ _ => Zfan2r
  | .cons8 _ _ _ _ _ => Zfan3r
  | _ => Znil

/-- Coq `zstepL zp`: a zipper part that fits `qstepL x`, where `x = zdart zp` (possibly improper,
if the arity test at the result would be destined to fail). -/
def zstepL (p0l p0r : Part) (zp : Zpart) : Zpart :=
  match zp with
  | ⟨Zhub, _, _⟩ => zshiftl p0l p0r Zhubl zp
  | ⟨Zhubl, pl, pr⟩ => ⟨Zhat, pl, pr⟩
  | ⟨Zhubr, _, _⟩ => zshiftr p0l p0r Zhubr zp
  | ⟨Zhat, _, pr⟩ => zshiftr p0l p0r (zfanL pr) zp
  | ⟨Zhatl, pl, pr⟩ => ⟨zfanR pl, pl, pr⟩
  | ⟨Zhatr, pl, pr⟩ => ⟨Zhub, pl, pr⟩
  | ⟨Zfan0l, pl, pr⟩ => ⟨Zhatr, pl, pr⟩
  | ⟨Zfan1l, pl, pr⟩ => ⟨Zfan0l, pl, pr⟩
  | ⟨Zfan2l, pl, pr⟩ => ⟨Zfan1l, pl, pr⟩
  | ⟨Zfan3l, pl, pr⟩ => ⟨Zfan2l, pl, pr⟩
  | ⟨_, pl, pr⟩ => ⟨Znil, pl, pr⟩

/-- Coq `zstepR zp`: a zipper part that fits `qstepR x`, where `x = zdart zp`. -/
def zstepR (p0l p0r : Part) (zp : Zpart) : Zpart :=
  match zp with
  | ⟨Zhub, _, _⟩ => zshiftr p0l p0r Zhubr zp
  | ⟨Zhubl, _, _⟩ => zshiftl p0l p0r Zhubl zp
  | ⟨Zhubr, pl, pr⟩ => ⟨Zhat, pl, pr⟩
  | ⟨Zhat, pl, pr⟩ => ⟨zfanR pl, pl, pr⟩
  | ⟨Zhatl, pl, pr⟩ => ⟨Zhub, pl, pr⟩
  | ⟨Zhatr, _, pr⟩ => zshiftr p0l p0r (zfanL pr) zp
  | ⟨Zfan0r, _, _⟩ => zshiftl p0l p0r Zhatl zp
  | ⟨Zfan1r, pl, pr⟩ => ⟨Zfan0r, pl, pr⟩
  | ⟨Zfan2r, pl, pr⟩ => ⟨Zfan1r, pl, pr⟩
  | ⟨Zfan3r, pl, pr⟩ => ⟨Zfan2r, pl, pr⟩
  | ⟨_, pl, pr⟩ => ⟨Znil, pl, pr⟩

/-- Coq `zproper_stepL`. -/
theorem zproper_stepL (p0l p0r : Part) (zp : Zpart) :
    zproper (zstepL p0l p0r zp) = true → zproper zp = true := by
  obtain ⟨zi, pl, pr⟩ := zp
  intro h
  cases zi <;> first | rfl | exact h

/-- Coq `zpvalid_stepL`. -/
theorem zpvalid_stepL {p0l p0r : Part} (Dp0l : p0l = revPart p0r) (h0 : 0 < sizePart p0r)
    (zp : Zpart) (hzp : Zpvalid p0r zp) : Zpvalid p0r (zstepL p0l p0r zp) := by
  have h0l : 0 < sizePart p0l := by rw [Dp0l, size_rev_part]; exact h0
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi
  case Zhub => exact zpvalid_shiftl Dp0l h0l _ _ hzp
  case Zhubr => exact zpvalid_shiftr Dp0l h0 _ _ hzp
  case Zhat => exact zpvalid_shiftr Dp0l h0 _ _ hzp
  all_goals exact hzp

/-- Coq `zproper_stepR`. -/
theorem zproper_stepR (p0l p0r : Part) (zp : Zpart) :
    zproper (zstepR p0l p0r zp) = true → zproper zp = true := by
  obtain ⟨zi, pl, pr⟩ := zp
  intro h
  cases zi <;> first | rfl | exact h

/-- Coq `zpvalid_stepR`. -/
theorem zpvalid_stepR {p0l p0r : Part} (Dp0l : p0l = revPart p0r) (h0 : 0 < sizePart p0r)
    (zp : Zpart) (hzp : Zpvalid p0r zp) : Zpvalid p0r (zstepR p0l p0r zp) := by
  have h0l : 0 < sizePart p0l := by rw [Dp0l, size_rev_part]; exact h0
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi
  case Zhub => exact zpvalid_shiftr Dp0l h0 _ _ hzp
  case Zhubl => exact zpvalid_shiftl Dp0l h0l _ _ hzp
  case Zhatr => exact zpvalid_shiftr Dp0l h0 _ _ hzp
  case Zfan0r => exact zpvalid_shiftl Dp0l h0l _ _ hzp
  all_goals exact hzp

namespace Hypermap

open Redpart

variable {D : Type u} [Finite D] {G : Hypermap D}

/-- The start of the left step chain of the subpart at `face x` (right spoke of arity `k`). -/
theorem zfanL_dart (geoG : G.PlainCubicPentagonal) {x : D} {pr : Part}
    (hr : G.fitp x pr = true) (hL : zfanL pr ≠ Znil) :
    G.zmove (zfanL pr) (G.face x) = G.qstepL (G.zmove Zhat x) := by
  have hs := (fitp_head geoG hr).1
  rcases pr with _ | ⟨s, h, pr⟩ | ⟨h, f1, pr⟩ | ⟨h, f1, f2, pr⟩ | ⟨h, f1, f2, f3, pr⟩
  · exact absurd rfl hL
  · cases s <;> try exact absurd rfl hL
    have hk := iter_face_of_arity (mem55 hs)
    simp only [zfanL, zmove]; wrap_tac hk
  · have hk := iter_face_of_arity (mem66 hs)
    simp only [zfanL, zmove]; wrap_tac hk
  · have hk := iter_face_of_arity (mem77 hs)
    simp only [zfanL, zmove]; wrap_tac hk
  · have hk := iter_face_of_arity (mem88 hs)
    simp only [zfanL, zmove]; wrap_tac hk

/-- The end of the right step chain of the subpart at `y` (left spoke of arity `k`). -/
theorem zfanR_dart (geoG : G.PlainCubicPentagonal) {y : D} {pl : Part}
    (hl : memRange (getSpoke pl) (G.arity (G.edge y)) = true) (hR : zfanR pl ≠ Znil) :
    G.zmove (zfanR pl) (G.face y) = G.qstepR (G.zmove Zhat (G.face y)) := by
  rcases pl with _ | ⟨s, h, pl⟩ | ⟨h, f1, pl⟩ | ⟨h, f1, f2, pl⟩ | ⟨h, f1, f2, f3, pl⟩
  · exact absurd rfl hR
  · cases s <;> try exact absurd rfl hR
    have hk := iter_face_of_arity (mem55 hl)
    simp only [zfanR, zmove]; wrap_tac hk
  · have hk := iter_face_of_arity (mem66 hl)
    simp only [zfanR, zmove]; wrap_tac hk
  · have hk := iter_face_of_arity (mem77 hl)
    simp only [zfanR, zmove]; wrap_tac hk
  · have hk := iter_face_of_arity (mem88 hl)
    simp only [zfanR, zmove]; wrap_tac hk

/-- `zfanR_dart` for a zipper part: the left subpart of `zorg pl` is the first one of `pl`. -/
theorem zfanR_dart' (geoG : G.PlainCubicPentagonal) {p0r : Part} {x0 : D}
    (fitP0r : G.exactFitp x0 p0r = true) {pl pr : Part} (hzp : Zvalid p0r pl pr)
    (hR : zfanR pl ≠ Znil) :
    G.zmove (zfanR pl) (G.zorg x0 pl) = G.qstepR (G.zmove Zhat (G.zorg x0 pl)) := by
  rcases pl with _ | ⟨s, h, pl⟩ | ⟨h, f1, pl⟩ | ⟨h, f1, f2, pl⟩ | ⟨h, f1, f2, f3, pl⟩
  · exact absurd rfl hR
  · rw [zorg_cons]
    exact zfanR_dart geoG (fitp_head geoG (zvalid_fit_r fitP0r (pl := pl)
      (pr := .cons s h pr) hzp)).1 hR
  · rw [zorg_cons6]
    exact zfanR_dart geoG (fitp_head geoG (zvalid_fit_r fitP0r (pl := pl)
      (pr := .cons6 h f1 pr) hzp)).1 hR
  · rw [zorg_cons7]
    exact zfanR_dart geoG (fitp_head geoG (zvalid_fit_r fitP0r (pl := pl)
      (pr := .cons7 h f1 f2 pr) hzp)).1 hR
  · rw [zorg_cons8]
    exact zfanR_dart geoG (fitp_head geoG (zvalid_fit_r fitP0r (pl := pl)
      (pr := .cons8 h f1 f2 f3 pr) hzp)).1 hR

/-- Coq `zdart_stepL`. -/
theorem zdart_stepL (geoG : G.PlainCubicPentagonal) {p0l p0r : Part} {x0 : D}
    (Dp0l : p0l = revPart p0r) (fitP0r : G.exactFitp x0 p0r = true) (zp : Zpart)
    (hzp : Zpvalid p0r zp) : G.Zpfit x0 (G.qstepL (G.zdart x0 zp)) (zstepL p0l p0r zp) := by
  obtain ⟨zi, pl, pr⟩ := zp
  change Zvalid p0r pl pr at hzp
  intro hprop
  cases zi with
  | Znil => simp [zstepL, zproper] at hprop
  | Zhub =>
    change G.zdart x0 (zshiftl p0l p0r Zhubl _) = _
    rw [zdart_shiftl Dp0l fitP0r]; simp only [zporg_mk, zdart_mk, zmove]; hnorm
  | Zhubl => simp only [zstepL, zdart_mk, zmove]; hnorm
  | Zhubr =>
    change G.zdart x0 (zshiftr p0l p0r Zhubr _) = _
    rw [zdart_shiftr Dp0l fitP0r _ ⟨Zhubr, pl, pr⟩ hzp]; simp only [zporg_mk, zdart_mk, zmove]
    hnorm
  | Zhat =>
    change zproper (zshiftr p0l p0r (zfanL pr) _) = true at hprop
    change G.zdart x0 (zshiftr p0l p0r (zfanL pr) _) = _
    rw [zproper_shiftr] at hprop
    rw [zdart_shiftr Dp0l fitP0r _ ⟨Zhat, pl, pr⟩ hzp, zporg_mk, zdart_mk]
    exact zfanL_dart geoG (zvalid_fit_r fitP0r hzp) (by intro e; rw [e] at hprop; exact absurd hprop (by decide))
  | Zhatl =>
    change zproper ⟨zfanR pl, pl, pr⟩ = true at hprop
    change G.zmove (zfanR pl) (G.zorg x0 pl) = _
    rw [zproper_mk] at hprop
    rw [zfanR_dart' geoG fitP0r hzp (by intro e; rw [e] at hprop; exact absurd hprop (by decide))]
    simp only [zdart_mk, zmove, qstepL, qstepR]
  | Zhatr => simp only [zstepL, zdart_mk, zmove]; hnorm
  | Zfan0l => simp only [zstepL, zdart_mk, zmove]; hnorm
  | Zfan1l => simp only [zstepL, zdart_mk, zmove]; hnorm
  | Zfan2l => simp only [zstepL, zdart_mk, zmove]; hnorm
  | Zfan3l => simp only [zstepL, zdart_mk, zmove]; hnorm
  | Zfan0r | Zfan1r | Zfan2r | Zfan3r => simp [zstepL, zproper] at hprop

/-- Coq `zdart_stepR`. -/
theorem zdart_stepR (geoG : G.PlainCubicPentagonal) {p0l p0r : Part} {x0 : D}
    (Dp0l : p0l = revPart p0r) (fitP0r : G.exactFitp x0 p0r = true) (zp : Zpart)
    (hzp : Zpvalid p0r zp) : G.Zpfit x0 (G.qstepR (G.zdart x0 zp)) (zstepR p0l p0r zp) := by
  obtain ⟨zi, pl, pr⟩ := zp
  change Zvalid p0r pl pr at hzp
  intro hprop
  cases zi with
  | Znil => simp [zstepR, zproper] at hprop
  | Zhub =>
    change G.zdart x0 (zshiftr p0l p0r Zhubr _) = _
    rw [zdart_shiftr Dp0l fitP0r _ ⟨Zhub, pl, pr⟩ hzp]; simp only [zporg_mk, zdart_mk, zmove]
    hnorm
  | Zhubl =>
    change G.zdart x0 (zshiftl p0l p0r Zhubl _) = _
    rw [zdart_shiftl Dp0l fitP0r]; simp only [zporg_mk, zdart_mk, zmove]; hnorm
  | Zhubr => simp only [zstepR, zdart_mk, zmove]; hnorm
  | Zhat =>
    change zproper ⟨zfanR pl, pl, pr⟩ = true at hprop
    change G.zmove (zfanR pl) (G.zorg x0 pl) = _
    rw [zproper_mk] at hprop
    rw [zfanR_dart' geoG fitP0r hzp (by intro e; rw [e] at hprop; exact absurd hprop (by decide))]
    simp only [zdart_mk]
  | Zhatl => simp only [zstepR, zdart_mk, zmove]; hnorm
  | Zhatr =>
    change zproper (zshiftr p0l p0r (zfanL pr) _) = true at hprop
    change G.zdart x0 (zshiftr p0l p0r (zfanL pr) _) = _
    rw [zproper_shiftr] at hprop
    rw [zdart_shiftr Dp0l fitP0r _ ⟨Zhatr, pl, pr⟩ hzp, zporg_mk, zdart_mk]
    rw [zfanL_dart geoG (zvalid_fit_r fitP0r hzp) (by intro e; rw [e] at hprop; exact absurd hprop (by decide))]
    simp only [zmove]; hnorm
  | Zfan0r =>
    change G.zdart x0 (zshiftl p0l p0r Zhatl _) = _
    rw [zdart_shiftl Dp0l fitP0r]; simp only [zporg_mk, zdart_mk, zmove]; hnorm
  | Zfan1r => simp only [zstepR, zdart_mk, zmove]; hnorm
  | Zfan2r => simp only [zstepR, zdart_mk, zmove]; hnorm
  | Zfan3r => simp only [zstepR, zdart_mk, zmove]; hnorm
  | Zfan0l | Zfan1l | Zfan2l | Zfan3l => simp [zstepR, zproper] at hprop

end Hypermap

/-! ### Question arities and ranges -/

/-- Coq `topqa r`: the top qarity of `r`; `Qa9` if `r` is unbounded. -/
def topqa : Prange → Qarity
  | .pr55 => Qa5
  | .pr56 | .pr66 => Qa6
  | .pr57 | .pr67 | .pr77 => Qa7
  | .pr58 | .pr68 | .pr78 | .pr88 => Qa8
  | _ => Qa9

/-- Coq `fitqa r qa`: the top qarity of `r` is `qa ≤ 8`. -/
def fitqa (r : Prange) (qa : Qarity) : Bool :=
  match r, qa with
  | .pr55, Qa5 => true
  | .pr56, Qa6 | .pr66, Qa6 => true
  | .pr57, Qa7 | .pr67, Qa7 | .pr77, Qa7 => true
  | .pr58, Qa8 | .pr68, Qa8 | .pr78, Qa8 | .pr88, Qa8 => true
  | _, _ => false

/-- Coq `popqa r`: if `r` represents `[M, N]` with `M < N < 9`, the range `[M, N-1]`; `pr99`
otherwise. -/
def popqa : Prange → Prange
  | .pr56 => .pr55
  | .pr57 => .pr56
  | .pr58 => .pr57
  | .pr67 => .pr66
  | .pr68 => .pr67
  | .pr78 => .pr77
  | _ => .pr99

/-- Coq `fitqa_topqa`. -/
theorem fitqa_topqa (r : Prange) (qa : Qarity) :
    fitqa r qa = (decide ((qa : ℕ) ≤ 8) && ((qa : ℕ) == (topqa r : ℕ))) := by
  cases r <;> cases qa <;> rfl

/-- Coq `fitqa_proper`. -/
theorem fitqa_proper (ahub : Qarity) (zp : Zpart) (qa : Qarity) :
    fitqa (zrange ahub zp) qa = true → zproper zp = true := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi <;> intro h <;> first | rfl | (cases qa <;> simp [zrange, fitqa] at h)

/-- Coq `fitqa_popqa`. -/
theorem fitqa_popqa {r : Prange} {qa : Qarity} (h : fitqa r qa = true) (n : ℕ)
    (hn : (memRange r n && (memRange (popqa r) 9 || !memRange (popqa r) n)) = true) :
    n = qa := by
  cases r <;> cases qa <;> simp [fitqa] at h <;> simp [memRange, popqa, natOfQarity] at hn ⊢ <;>
    omega

namespace Hypermap

variable {D : Type u} (G : Hypermap D)

/-- Coq `zpfit_top zp`: the arity of `zdart zp` is the top of `zrange zp`; the precondition for
using `zstepLt`/`zstepRt`. -/
def ZpfitTop (ahub : Qarity) (x0 : D) (zp : Zpart) : Prop :=
  G.arity (G.zdart x0 zp) = (topqa (zrange ahub zp) : ℕ)

end Hypermap

/-! ### Step variants assuming `ZpfitTop` -/

/-- Coq `zfanLt pr`: `zfanL pr`, assuming the spoke arity is the top of its range. -/
def zfanLt : Part → ZpartLoc
  | .cons .pr55 _ _ => Zfan0l
  | .cons .pr56 _ _ => Zfan1l
  | .cons .pr66 _ _ => Zfan1l
  | .cons6 _ _ _ => Zfan1l
  | .cons7 _ _ _ _ => Zfan2l
  | .cons8 _ _ _ _ _ => Zfan3l
  | _ => Znil

/-- Coq `zfanRt pl`: `zfanR pl`, assuming the spoke arity is the top of its range. -/
def zfanRt : Part → ZpartLoc
  | .cons .pr55 _ _ => Zfan0r
  | .cons .pr56 _ _ => Zfan1r
  | .cons .pr66 _ _ => Zfan1r
  | .cons6 _ _ _ => Zfan1r
  | .cons7 _ _ _ _ => Zfan2r
  | .cons8 _ _ _ _ _ => Zfan3r
  | _ => Znil

/-- Coq `zstepLt zp`: `zstepL zp`, assuming `ZpfitTop zp`. -/
def zstepLt (p0l p0r : Part) (zp : Zpart) : Zpart :=
  match zp with
  | ⟨Zhub, _, _⟩ => zshiftl p0l p0r Zhubl zp
  | ⟨Zhubl, pl, pr⟩ => ⟨Zhat, pl, pr⟩
  | ⟨Zhubr, _, _⟩ => zshiftr p0l p0r Zhubr zp
  | ⟨Zhat, _, pr⟩ => zshiftr p0l p0r (zfanL pr) zp
  | ⟨Zhatl, pl, pr⟩ => ⟨zfanRt pl, pl, pr⟩
  | ⟨Zhatr, pl, pr⟩ => ⟨Zhub, pl, pr⟩
  | ⟨Zfan0l, pl, pr⟩ => ⟨Zhatr, pl, pr⟩
  | ⟨Zfan1l, pl, pr⟩ => ⟨Zfan0l, pl, pr⟩
  | ⟨Zfan2l, pl, pr⟩ => ⟨Zfan1l, pl, pr⟩
  | ⟨Zfan3l, pl, pr⟩ => ⟨Zfan2l, pl, pr⟩
  | ⟨_, pl, pr⟩ => ⟨Znil, pl, pr⟩

/-- Coq `zstepRt zp`: `zstepR zp`, assuming `ZpfitTop zp`. -/
def zstepRt (p0l p0r : Part) (zp : Zpart) : Zpart :=
  match zp with
  | ⟨Zhub, _, _⟩ => zshiftr p0l p0r Zhubr zp
  | ⟨Zhubl, _, _⟩ => zshiftl p0l p0r Zhubl zp
  | ⟨Zhubr, pl, pr⟩ => ⟨Zhat, pl, pr⟩
  | ⟨Zhat, pl, pr⟩ => ⟨zfanR pl, pl, pr⟩
  | ⟨Zhatl, pl, pr⟩ => ⟨Zhub, pl, pr⟩
  | ⟨Zhatr, _, pr⟩ => zshiftr p0l p0r (zfanLt pr) zp
  | ⟨Zfan0r, _, _⟩ => zshiftl p0l p0r Zhatl zp
  | ⟨Zfan1r, pl, pr⟩ => ⟨Zfan0r, pl, pr⟩
  | ⟨Zfan2r, pl, pr⟩ => ⟨Zfan1r, pl, pr⟩
  | ⟨Zfan3r, pl, pr⟩ => ⟨Zfan2r, pl, pr⟩
  | ⟨_, pl, pr⟩ => ⟨Znil, pl, pr⟩

/-- Coq `zproper_stepLt`. -/
theorem zproper_stepLt (p0l p0r : Part) (zp : Zpart) :
    zproper (zstepLt p0l p0r zp) = true → zproper zp = true := by
  obtain ⟨zi, pl, pr⟩ := zp
  intro h
  cases zi <;> first | rfl | exact h

/-- Coq `zpvalid_stepLt`. -/
theorem zpvalid_stepLt {p0l p0r : Part} (Dp0l : p0l = revPart p0r) (h0 : 0 < sizePart p0r)
    (zp : Zpart) (hzp : Zpvalid p0r zp) : Zpvalid p0r (zstepLt p0l p0r zp) := by
  have h0l : 0 < sizePart p0l := by rw [Dp0l, size_rev_part]; exact h0
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi
  case Zhub => exact zpvalid_shiftl Dp0l h0l _ _ hzp
  case Zhubr => exact zpvalid_shiftr Dp0l h0 _ _ hzp
  case Zhat => exact zpvalid_shiftr Dp0l h0 _ _ hzp
  all_goals exact hzp

/-- Coq `zproper_stepRt`. -/
theorem zproper_stepRt (p0l p0r : Part) (zp : Zpart) :
    zproper (zstepRt p0l p0r zp) = true → zproper zp = true := by
  obtain ⟨zi, pl, pr⟩ := zp
  intro h
  cases zi <;> first | rfl | exact h

/-- Coq `zpvalid_stepRt`. -/
theorem zpvalid_stepRt {p0l p0r : Part} (Dp0l : p0l = revPart p0r) (h0 : 0 < sizePart p0r)
    (zp : Zpart) (hzp : Zpvalid p0r zp) : Zpvalid p0r (zstepRt p0l p0r zp) := by
  have h0l : 0 < sizePart p0l := by rw [Dp0l, size_rev_part]; exact h0
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi
  case Zhub => exact zpvalid_shiftr Dp0l h0 _ _ hzp
  case Zhubl => exact zpvalid_shiftl Dp0l h0l _ _ hzp
  case Zhatr => exact zpvalid_shiftr Dp0l h0 _ _ hzp
  case Zfan0r => exact zpvalid_shiftl Dp0l h0l _ _ hzp
  all_goals exact hzp

namespace Hypermap

open Redpart

variable {D : Type u} [Finite D] {G : Hypermap D}

/-- Coq `zdart_stepLt`. -/
theorem zdart_stepLt (geoG : G.PlainCubicPentagonal) {ahub : Qarity} {p0l p0r : Part} {x0 : D}
    (Dp0l : p0l = revPart p0r) (fitP0r : G.exactFitp x0 p0r = true) (zp : Zpart)
    (htop : G.ZpfitTop ahub x0 zp) (hzp : Zpvalid p0r zp) :
    G.Zpfit x0 (G.qstepL (G.zdart x0 zp)) (zstepLt p0l p0r zp) := by
  have H := zdart_stepL geoG Dp0l fitP0r zp hzp
  obtain ⟨zi, pl, pr⟩ := zp
  change Zvalid p0r pl pr at hzp
  cases zi
  case Zhatl =>
    rcases pl with _ | ⟨s, h, pl⟩ | ⟨h, f1, pl⟩ | ⟨h, f1, f2, pl⟩ | ⟨h, f1, f2, f3, pl⟩
    case cons =>
      cases s
      case pr56 | pr66 =>
        -- the left spoke is a hexagon
        intro _
        simp only [ZpfitTop, zrange, getSpoke, topqa, natOfQarity, zdart_mk] at htop
        have e : G.arity (G.edge (G.zorg x0 pl)) = 6 := by
          rw [← htop]; symm; simp only [zmove]; arity_tac
        have hk := iter_face_of_arity e
        simp only [zstepLt, zfanRt, zdart_mk, zmove]
        wrap_tac hk
      all_goals exact H
    all_goals exact H
  all_goals exact H

/-- Coq `zdart_stepRt`. -/
theorem zdart_stepRt (geoG : G.PlainCubicPentagonal) {ahub : Qarity} {p0l p0r : Part} {x0 : D}
    (Dp0l : p0l = revPart p0r) (fitP0r : G.exactFitp x0 p0r = true) (zp : Zpart)
    (htop : G.ZpfitTop ahub x0 zp) (hzp : Zpvalid p0r zp) :
    G.Zpfit x0 (G.qstepR (G.zdart x0 zp)) (zstepRt p0l p0r zp) := by
  have H := zdart_stepR geoG Dp0l fitP0r zp hzp
  obtain ⟨zi, pl, pr⟩ := zp
  change Zvalid p0r pl pr at hzp
  cases zi
  case Zhatr =>
    rcases pr with _ | ⟨s, h, pr⟩ | ⟨h, f1, pr⟩ | ⟨h, f1, f2, pr⟩ | ⟨h, f1, f2, f3, pr⟩
    case cons =>
      cases s
      case pr56 | pr66 =>
        -- the right spoke is a hexagon
        intro _
        simp only [ZpfitTop, zrange, getSpoke, topqa, natOfQarity, zdart_mk] at htop
        have e : G.arity (G.edge (G.zorg x0 pl)) = 6 := by
          rw [← htop]; symm; simp only [zmove]; arity_tac
        have hk := iter_face_of_arity e
        change G.zdart x0 (zshiftr p0l p0r Zfan1l _) = _
        rw [zdart_shiftr Dp0l fitP0r _ ⟨Zhatr, pl, _⟩ hzp, zporg_mk, zdart_mk]
        simp only [zmove]
        wrap_tac hk
      all_goals exact H
    all_goals exact H
  all_goals exact H

end Hypermap

end FourColor
