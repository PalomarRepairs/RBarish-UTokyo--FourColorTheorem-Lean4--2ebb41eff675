/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Patch

/-!
# Sewing two hypermaps along a common border  (port of `sew.v`)

This file provides the means for "sewing" two hypermaps `Gd` and `Gr` along a common cycle; the
resulting map `G` satisfies the `Patch` predicate of `FourColor/Patch.lean`.

Let `Gd : Hypermap Dd`, `Gr : Hypermap Dr`, `bGd : List Dd` and `bGr : List Dr` be such that
`bGd` is a simple E-cycle of `Gd` (`cycEbGd : Gd.SFCycle Gd.edge bGd`), `bGr` is a node (a
duplicate-free N-cycle) of `Gr` (`cycNbGr : UCycle (frel Gr.node) bGr`), and both cycles have
the same length (`sz_bG : bGd.length = bGr.length`). Then

* `SewDart Dd bGr` : the dart type of the sewn map, the darts of `Gd` together with the darts of
  `Gr` off the border `bGr` (Coq `sew_dart Gd bGr`);
* `sewd bGr xd`    : the image of `xd : Dd` in `SewDart Dd bGr` (Coq `sewd`);
* `sewr sz_bG xr`  : the image of `xr : Dr` in `SewDart Dd bGr` (Coq `sewr`): a border dart
  `xr ∈ bGr` is identified with the dart of `bGd` in the mirror position, the others are kept;
* `sewMap cycEbGd cycNbGr sz_bG` : the hypermap on `SewDart Dd bGr` obtained by glueing `Gd` and
  `Gr` along `bGd` and `bGr` (Coq `sew_map`).

When `G := sewMap cycEbGd cycNbGr sz_bG` is defined, we always have
`G.Patch Gd Gr (sewd bGr) (sewr sz_bG) bGd bGr` (`sew_map_patch`).

## Porting notes

* The Coq dart type `sew_dart := {i : sew_tag & sew_dart_at i}` is the tagged union of `Gd` and
  of the subtype `{xr | xr \notin bGr}` of `Gr`, over the two-element tag type
  `sew_tag := SewDisk | SewRest`. In Lean it is the sum type `Dd ⊕ {xr : Dr // xr ∉ bGr}`
  (which also accommodates dart types in different universes): the tag `SewDisk` is `Sum.inl`
  and `SewRest` is `Sum.inr`. The finite type boilerplate of the Coq file (`sew_tag`,
  `sew_tag_code`, `sew_tag_decode`, `sew_tag_subproof`, `sew_dart_at` and the `HB.instance`
  declarations) is therefore replaced by Lean's `Sum` and `Subtype` instances (`SewDart` is an
  `abbrev`, so its `Fintype`/`DecidableEq` instances are found automatically).
* The section `Let`s of the Coq file (`EbGdE`, `EbGdE1`, `EbGrN`, `EbGrN1`, `in_bGd`, `in_bGr`,
  `hdr`, `hrd`, `bGr_hdr`, `bGd_hrd`, `hrd_hdr`, `hdr_hrd`, `node_hdr`, `edge_hrd`, `sewr_bGr`,
  `sewr_Gr`, `sewr_hdr`) are private declarations of this file.
* Coq's local `in_bGd xd : {xr0 : Gr | xd \in bGd} + {xd \notin bGd}` (and `in_bGr`) is a
  decision of `xd ∈ bGd` that also supplies a default dart of the other map (needed by `nth`)
  when `xd ∈ bGd`. In Lean the definitions branch with `if b_xd : xd ∈ bGd then … else …`, and
  the default dart is `inBGd sz_bG b_xd` (the head of `bGr`), resp. `inBGr sz_bG b_xr`. Since the
  default dart is extracted from `sz_bG`, `sewr` and the three permutations take `sz_bG` as an
  argument (as they do in Coq, where `in_bGr` depends on `sz_bG`), and `bGd`, `bGr` are inferred
  from it.
* The Coq section hypotheses become explicit arguments, taken (as when the Coq section is
  closed) by the declarations that use them: `inj_sewr cycEbGd sz_bG`,
  `sew_map_subproof cycEbGd cycNbGr sz_bG`, `sewMap cycEbGd cycNbGr sz_bG`,
  `sewr_rev_sewd cycEbGd cycNbGr sz_bG` and `sew_map_patch cycEbGd cycNbGr sz_bG`. The results
  that use the injectivity of `node` (i.e. finiteness) assume `[Finite Dd] [Finite Dr]`.
* math-comp's `nth x0 s i` and `index x s` are `s.getD i x0` and `s.idxOf x`; the Coq proof of
  `node_hdr` through `next`/`prev` is replaced by index computations on the two cycles.
-/

namespace FourColor

open Function

/-! ### Index form of functional cycles -/

section CycleIndex

variable {α : Type*}

/-- `getD` at a valid index is `getElem`. -/
private theorem getD_of_lt {l : List α} {i : ℕ} (h : i < l.length) (d : α) :
    l.getD i d = l[i] := by
  simp [h]

/-- In an `f`-path, `f` maps each item to the next one. -/
private theorem fpath_getElem {f : α → α} :
    ∀ {x : α} {l : List α}, fpath f x l →
      ∀ (i : ℕ) (hi : i < l.length), f ((x :: l)[i]'(by simp; omega)) = l[i]
  | _, [], _, _, hi => absurd hi (by simp)
  | _, _ :: _, hp, 0, _ => hp.1
  | _, _ :: l, hp, i + 1, hi => fpath_getElem hp.2 i (by simpa using hi)

/-- In an `f`-cycle, `f` maps each item but the last to the next one. -/
private theorem fcycle_getElem_succ {f : α → α} {p : List α} (hp : fcycle f p) {i : ℕ}
    (hi : i + 1 < p.length) : f (p[i]'(by omega)) = p[i + 1] := by
  cases p with
  | nil => simp at hi
  | cons y q =>
    have hi' : i < (q ++ [y]).length := by simp at hi ⊢; omega
    have h : f (((y :: q) ++ [y])[i]'(by simp at hi ⊢; omega)) = (q ++ [y])[i] :=
      fpath_getElem ((cycle_cons _ y q).1 hp) i hi'
    have h1 : ((y :: q) ++ [y])[i]'(by simp at hi ⊢; omega) = (y :: q)[i]'(by omega) :=
      List.getElem_append_left (by omega)
    have h2 : (q ++ [y])[i] = q[i]'(by simp at hi; omega) :=
      List.getElem_append_left (by simp at hi; omega)
    rw [h1, h2] at h
    rw [h, List.getElem_cons_succ]

/-- In an `f`-cycle, `f` maps the last item to the first one. -/
private theorem fcycle_getElem_last {f : α → α} {p : List α} (hp : fcycle f p)
    (hn : 0 < p.length) : f (p[p.length - 1]'(by omega)) = p[0] := by
  cases p with
  | nil => simp at hn
  | cons y q =>
    have hi' : q.length < (q ++ [y]).length := by simp
    have h := fpath_getElem ((cycle_cons _ y q).1 hp) q.length hi'
    have e1 : (y :: (q ++ [y]))[q.length]'(by simp) =
        (y :: q)[(y :: q).length - 1]'(by simp) := by
      simp only [← List.cons_append, List.length_cons, Nat.add_sub_cancel]
      rw [List.getElem_append_left]
    have e2 : (q ++ [y])[q.length] = (y :: q)[0] := by simp
    rw [← e1, h, e2]

end CycleIndex

namespace Hypermap

universe v w

section Sew

variable {Dd : Type v} {Dr : Type w} [DecidableEq Dd] [DecidableEq Dr]

/-! ### Local consequences of the border hypotheses (math-comp section `Let`s) -/

section Lets

variable {Gd : Hypermap Dd} {Gr : Hypermap Dr} {bGd : List Dd} {bGr : List Dr}

omit [DecidableEq Dd] in
/-- math-comp local `EbGdE`. -/
private theorem EbGdE (cycEbGd : Gd.SFCycle Gd.edge bGd) {xd : Dd} (b_xd : xd ∈ bGd)
    (yd : Dd) : Gd.cedge xd yd ↔ yd ∈ bGd :=
  fconnect_cycle cycEbGd.1 b_xd

omit [DecidableEq Dd] in
/-- math-comp local `EbGdE1`. -/
private theorem EbGdE1 [Finite Dd] (cycEbGd : Gd.SFCycle Gd.edge bGd) {xd : Dd}
    (b_exd : Gd.edge xd ∈ bGd) : xd ∈ bGd :=
  (EbGdE cycEbGd b_exd xd).1 (Gd.cedge_sym _ _ (fconnect1 _ _))

omit [DecidableEq Dr] in
/-- math-comp local `EbGrN`. -/
private theorem EbGrN (cycNbGr : UCycle (frel Gr.node) bGr) {xr : Dr} (b_xr : xr ∈ bGr)
    (yr : Dr) : Gr.cnode xr yr ↔ yr ∈ bGr :=
  fconnect_cycle cycNbGr.1 b_xr

omit [DecidableEq Dr] in
/-- math-comp local `EbGrN1`. -/
private theorem EbGrN1 [Finite Dr] (cycNbGr : UCycle (frel Gr.node) bGr) {xr : Dr}
    (b_nxr : Gr.node xr ∈ bGr) : xr ∈ bGr :=
  (EbGrN cycNbGr b_nxr xr).1 (Gr.cnode_sym _ _ (fconnect1 _ _))

end Lets

/-! ### Default darts (math-comp local `in_bGd`, `in_bGr`) -/

/-- math-comp local `in_bGd` (its left branch): a default dart of `Gr`, available when
`xd ∈ bGd` since the two borders have the same length. -/
private def inBGd {bGd : List Dd} {bGr : List Dr} (sz_bG : bGd.length = bGr.length) {xd : Dd}
    (b_xd : xd ∈ bGd) : Dr :=
  bGr.head (List.ne_nil_of_length_pos (sz_bG ▸ List.length_pos_of_mem b_xd))

/-- math-comp local `in_bGr` (its left branch): a default dart of `Gd`, available when
`xr ∈ bGr` since the two borders have the same length. -/
private def inBGr {bGd : List Dd} {bGr : List Dr} (sz_bG : bGd.length = bGr.length) {xr : Dr}
    (b_xr : xr ∈ bGr) : Dd :=
  bGd.head (List.ne_nil_of_length_pos (sz_bG ▸ List.length_pos_of_mem b_xr))

/-! ### Transfer between the two borders (math-comp local `hdr`, `hrd`) -/

/-- math-comp local `hdr xr0 xd := nth xr0 (rev bGr) (index xd bGd)`: the dart of the remainder
border `bGr` that is glued to the dart `xd` of the disk border `bGd` (`xr0` is a default). -/
private def hdr (bGd : List Dd) (bGr : List Dr) (xr0 : Dr) (xd : Dd) : Dr :=
  bGr.reverse.getD (bGd.idxOf xd) xr0

/-- math-comp local `hrd xd0 xr := nth xd0 bGd (index xr (rev bGr))`: the dart of the disk
border `bGd` that is glued to the dart `xr` of the remainder border `bGr` (`xd0` is a
default). -/
private def hrd (bGd : List Dd) (bGr : List Dr) (xd0 : Dd) (xr : Dr) : Dd :=
  bGd.getD (bGr.reverse.idxOf xr) xd0

section Transfer

variable {Gd : Hypermap Dd} {Gr : Hypermap Dr} {bGd : List Dd} {bGr : List Dr}

omit [DecidableEq Dr] in
/-- `hdr` on the `j`-th dart of a duplicate-free disk border. -/
private theorem hdr_getElem (UbGd : bGd.Nodup) (sz_bG : bGd.length = bGr.length) (xr0 : Dr)
    (j : ℕ) (hj : j < bGd.length) :
    hdr bGd bGr xr0 bGd[j] = bGr.reverse[j]'(by rw [List.length_reverse, ← sz_bG]; exact hj) := by
  rw [hdr, UbGd.idxOf_getElem, getD_of_lt]

omit [DecidableEq Dd] in
/-- `hrd` on the `j`-th dart of the reversed, duplicate-free remainder border. -/
private theorem hrd_getElem (UbGr : bGr.Nodup) (sz_bG : bGd.length = bGr.length) (xd0 : Dd)
    (j : ℕ) (hj : j < bGr.reverse.length) :
    hrd bGd bGr xd0 bGr.reverse[j] = bGd[j]'(by rw [sz_bG, ← List.length_reverse]; exact hj) := by
  rw [hrd, (List.nodup_reverse.2 UbGr).idxOf_getElem, getD_of_lt]

omit [DecidableEq Dr] in
/-- math-comp local `bGr_hdr`. -/
private theorem bGr_hdr (sz_bG : bGd.length = bGr.length) {xr0 : Dr} {xd : Dd}
    (b_xd : xd ∈ bGd) : hdr bGd bGr xr0 xd ∈ bGr := by
  have hi : bGd.idxOf xd < bGr.reverse.length := by
    rw [List.length_reverse, ← sz_bG]; exact List.idxOf_lt_length_of_mem b_xd
  rw [hdr, getD_of_lt hi]
  exact List.mem_reverse.1 (List.getElem_mem hi)

omit [DecidableEq Dd] in
/-- math-comp local `bGd_hrd`. -/
private theorem bGd_hrd (sz_bG : bGd.length = bGr.length) {xd0 : Dd} {xr : Dr}
    (b_xr : xr ∈ bGr) : hrd bGd bGr xd0 xr ∈ bGd := by
  have hi : bGr.reverse.idxOf xr < bGd.length := by
    rw [sz_bG, ← List.length_reverse]; exact List.idxOf_lt_length_of_mem (List.mem_reverse.2 b_xr)
  rw [hrd, getD_of_lt hi]
  exact List.getElem_mem hi

/-- math-comp local `hrd_hdr`. -/
private theorem hrd_hdr (UbGr : bGr.Nodup) (sz_bG : bGd.length = bGr.length) {xd0 : Dd}
    {xr0 : Dr} {xd : Dd} (b_xd : xd ∈ bGd) : hrd bGd bGr xd0 (hdr bGd bGr xr0 xd) = xd := by
  have hi : bGd.idxOf xd < bGr.reverse.length := by
    rw [List.length_reverse, ← sz_bG]; exact List.idxOf_lt_length_of_mem b_xd
  rw [hdr, getD_of_lt hi, hrd_getElem UbGr sz_bG]
  exact List.getElem_idxOf _

/-- math-comp local `hdr_hrd`. -/
private theorem hdr_hrd (UbGd : bGd.Nodup) (sz_bG : bGd.length = bGr.length) {xd0 : Dd}
    {xr0 : Dr} {xr : Dr} (b_xr : xr ∈ bGr) : hdr bGd bGr xr0 (hrd bGd bGr xd0 xr) = xr := by
  have hi : bGr.reverse.idxOf xr < bGd.length := by
    rw [sz_bG, ← List.length_reverse]; exact List.idxOf_lt_length_of_mem (List.mem_reverse.2 b_xr)
  rw [hrd, getD_of_lt hi, hdr_getElem UbGd sz_bG]
  exact List.getElem_idxOf _

omit [DecidableEq Dr] in
/-- math-comp local `node_hdr`. -/
private theorem node_hdr (cycEbGd : Gd.SFCycle Gd.edge bGd)
    (cycNbGr : UCycle (frel Gr.node) bGr) (sz_bG : bGd.length = bGr.length) {xr0 : Dr}
    {xd : Dd} (b_xd : xd ∈ bGd) :
    Gr.node (hdr bGd bGr xr0 xd) = hdr bGd bGr xr0 (Gd.node (Gd.face xd)) := by
  have UbGd : bGd.Nodup := Gd.scycle_uniq cycEbGd
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 b_xd
  have hn : 0 < bGd.length := by omega
  rw [hdr_getElem UbGd sz_bG, List.getElem_reverse]
  cases i with
  | zero =>
    have hE := fcycle_getElem_last cycEbGd.1 hn
    rw [← hE, Gd.edgeK, hdr_getElem UbGd sz_bG, List.getElem_reverse]
    have hN := fcycle_getElem_last cycNbGr.1 (by omega)
    simp only [Nat.sub_zero]
    rw [hN]
    simp only [show bGr.length - 1 - (bGd.length - 1) = 0 by omega]
  | succ k =>
    have hE := fcycle_getElem_succ cycEbGd.1 hi
    rw [← hE, Gd.edgeK, hdr_getElem UbGd sz_bG, List.getElem_reverse]
    have hN := fcycle_getElem_succ cycNbGr.1 (i := bGr.length - 1 - (k + 1)) (by omega)
    rw [hN]
    simp only [show bGr.length - 1 - (k + 1) + 1 = bGr.length - 1 - k by omega]

/-- math-comp local `edge_hrd`. -/
private theorem edge_hrd [Finite Dd] [Finite Dr] (cycEbGd : Gd.SFCycle Gd.edge bGd)
    (cycNbGr : UCycle (frel Gr.node) bGr) (sz_bG : bGd.length = bGr.length) {xd0 : Dd}
    {xr : Dr} (b_xr : xr ∈ bGr) :
    Gd.edge (hrd bGd bGr xd0 xr) = hrd bGd bGr xd0 (Gr.face (Gr.edge xr)) := by
  have UbGd : bGd.Nodup := Gd.scycle_uniq cycEbGd
  have UbGr : bGr.Nodup := cycNbGr.2
  set yr := Gr.face (Gr.edge xr)
  have b_yr : yr ∈ bGr := EbGrN1 cycNbGr (by rw [Gr.edgeK]; exact b_xr)
  set yd := hrd bGd bGr xd0 yr
  have b_yd : yd ∈ bGd := bGd_hrd sz_bG b_yr
  have exr : xr = Gr.node (hdr bGd bGr xr (hrd bGd bGr xd0 yr)) := by
    rw [hdr_hrd UbGd sz_bG b_yr, Gr.edgeK]
  have b_nfyd : Gd.node (Gd.face yd) ∈ bGd := EbGdE1 cycEbGd (by rw [Gd.faceK]; exact b_yd)
  rw [exr, node_hdr cycEbGd cycNbGr sz_bG b_yd, hrd_hdr UbGr sz_bG b_nfyd, Gd.faceK]

omit [DecidableEq Dd] in
/-- The default dart of `hrd` is irrelevant on the border (used for math-comp local
`sewr_bGr`). -/
private theorem hrd_default (sz_bG : bGd.length = bGr.length) (xd0 xd1 : Dd) {xr : Dr}
    (b_xr : xr ∈ bGr) : hrd bGd bGr xd0 xr = hrd bGd bGr xd1 xr := by
  have hi : bGr.reverse.idxOf xr < bGd.length := by
    rw [sz_bG, ← List.length_reverse]; exact List.idxOf_lt_length_of_mem (List.mem_reverse.2 b_xr)
  rw [hrd, hrd, getD_of_lt hi, getD_of_lt hi]

end Transfer

/-! ### The sewn dart type and its injections -/

/-- math-comp `sew_dart Gd bGr`: the darts of the map obtained by sewing `Gd` and `Gr` along
`bGd` and `bGr`, i.e., the darts of `Gd` together with the darts of `Gr` off the border `bGr`.
The math-comp tagged union `{i : sew_tag & sew_dart_at i}` over the tags `SewDisk`, `SewRest`
(math-comp `sew_tag`, `sew_dart_at`) is the sum type: `Sum.inl` is `SewDisk`, `Sum.inr` is
`SewRest`. -/
abbrev SewDart (Dd : Type v) (bGr : List Dr) : Type (max v w) := Dd ⊕ {xr : Dr // xr ∉ bGr}

/-- math-comp `sewd bGr xd`: the image of the dart `xd` of the disk map `Gd` in the sewn map. -/
def sewd (bGr : List Dr) (xd : Dd) : SewDart Dd bGr := Sum.inl xd

/-- math-comp `sewr_r xr b'xr`: the image of the dart `xr ∉ bGr` of the remainder map `Gr` in
the sewn map. -/
def sewrR {bGr : List Dr} (xr : Dr) (b'xr : xr ∉ bGr) : SewDart Dd bGr := Sum.inr ⟨xr, b'xr⟩

/-- math-comp `sewr`: the image of the dart `xr` of the remainder map `Gr` in the sewn map; a
border dart `xr ∈ bGr` is identified with the dart of the disk border `bGd` glued to it
(`hrd`), the other darts are kept (`sewrR`). The default dart of `Gd` needed when `xr ∈ bGr` is
extracted from `sz_bG` (math-comp local `in_bGr`). -/
def sewr {bGd : List Dd} {bGr : List Dr} (sz_bG : bGd.length = bGr.length) (xr : Dr) :
    SewDart Dd bGr :=
  if b_xr : xr ∈ bGr then sewd bGr (hrd bGd bGr (inBGr sz_bG b_xr) xr) else sewrR xr b_xr

omit [DecidableEq Dd] [DecidableEq Dr] in
/-- math-comp `inj_sewd`. -/
theorem inj_sewd (bGr : List Dr) : Injective (sewd (Dd := Dd) bGr) :=
  fun _ _ h => Sum.inl_injective h

/-- math-comp `inj_sewr`. -/
theorem inj_sewr {Gd : Hypermap Dd} {bGd : List Dd} {bGr : List Dr}
    (cycEbGd : Gd.SFCycle Gd.edge bGd) (sz_bG : bGd.length = bGr.length) :
    Injective (sewr sz_bG) := by
  have UbGd : bGd.Nodup := Gd.scycle_uniq cycEbGd
  intro xr yr h
  unfold sewr at h
  by_cases b_xr : xr ∈ bGr <;> by_cases b_yr : yr ∈ bGr
  · rw [dite_eq_left b_xr, dite_eq_left b_yr] at h
    have h' := congrArg (hdr bGd bGr xr) (inj_sewd bGr h)
    rwa [hdr_hrd UbGd sz_bG b_xr, hdr_hrd UbGd sz_bG b_yr] at h'
  · rw [dite_eq_left b_xr, dite_eq_right b_yr] at h
    exact absurd h Sum.inl_ne_inr
  · rw [dite_eq_right b_xr, dite_eq_left b_yr] at h
    exact absurd h Sum.inr_ne_inl
  · rw [dite_eq_right b_xr, dite_eq_right b_yr] at h
    exact congrArg Subtype.val (Sum.inr_injective h)

section SewLets

variable {bGd : List Dd} {bGr : List Dr}

omit [DecidableEq Dd] in
/-- math-comp local `sewr_bGr`. -/
private theorem sewr_bGr (sz_bG : bGd.length = bGr.length) {xd0 : Dd} {xr : Dr}
    (b_xr : xr ∈ bGr) : sewr sz_bG xr = sewd bGr (hrd bGd bGr xd0 xr) := by
  rw [sewr, dite_eq_left b_xr, hrd_default sz_bG _ xd0 b_xr]

omit [DecidableEq Dd] in
/-- math-comp local `sewr_Gr`. -/
private theorem sewr_Gr (sz_bG : bGd.length = bGr.length) {xr : Dr} (b'xr : xr ∉ bGr) :
    sewr sz_bG xr = sewrR xr b'xr := by
  rw [sewr, dite_eq_right b'xr]

/-- math-comp local `sewr_hdr`. -/
private theorem sewr_hdr (UbGr : bGr.Nodup) (sz_bG : bGd.length = bGr.length) {xr0 : Dr}
    {xd : Dd} (b_xd : xd ∈ bGd) : sewr sz_bG (hdr bGd bGr xr0 xd) = sewd bGr xd := by
  rw [sewr_bGr sz_bG (xd0 := xd) (bGr_hdr sz_bG b_xd), hrd_hdr UbGr sz_bG b_xd]

end SewLets

/-! ### The sewn hypermap -/

section SewMap

variable (Gd : Hypermap Dd) (Gr : Hypermap Dr) {bGd : List Dd} {bGr : List Dr}
  (sz_bG : bGd.length = bGr.length)

/-- math-comp `sew_edge`: the edge permutation of the sewn map; on a border dart of `Gd` it
follows the edge of the glued dart of `Gr`. -/
def sewEdge : SewDart Dd bGr → SewDart Dd bGr
  | Sum.inl xd =>
    if b_xd : xd ∈ bGd then sewr sz_bG (Gr.edge (hdr bGd bGr (inBGd sz_bG b_xd) xd))
    else sewd bGr (Gd.edge xd)
  | Sum.inr ur => sewr sz_bG (Gr.edge ur.1)

/-- math-comp `sew_face_r`: the face permutation of the sewn map, on (the image of) a dart `xr`
of `Gr`. -/
def sewFaceR (xr : Dr) : SewDart Dd bGr :=
  match sewr sz_bG (Gr.face xr) with
  | Sum.inl xd => sewd bGr (Gd.face xd)
  | ufr => ufr

/-- math-comp `sew_face`: the face permutation of the sewn map. -/
def sewFace : SewDart Dd bGr → SewDart Dd bGr
  | Sum.inl xd =>
    if b_xd : xd ∈ bGd then sewFaceR Gd Gr sz_bG (hdr bGd bGr (inBGd sz_bG b_xd) xd)
    else sewd bGr (Gd.face xd)
  | Sum.inr ur => sewFaceR Gd Gr sz_bG ur.1

/-- math-comp `sew_node`: the node permutation of the sewn map. -/
def sewNode : SewDart Dd bGr → SewDart Dd bGr
  | Sum.inl xd => sewd bGr (Gd.node xd)
  | Sum.inr ur => sewr sz_bG (Gr.node ur.1)

variable {Gd Gr}

/-- `sew_face` on the image of a dart of `Gr` (a step of math-comp `sew_map_subproof`). -/
private theorem sewFace_sewr (cycEbGd : Gd.SFCycle Gd.edge bGd) (xr : Dr) :
    sewFace Gd Gr sz_bG (sewr sz_bG xr) = sewFaceR Gd Gr sz_bG xr := by
  have UbGd : bGd.Nodup := Gd.scycle_uniq cycEbGd
  by_cases b_xr : xr ∈ bGr
  · have b_yd : hrd bGd bGr (inBGr sz_bG b_xr) xr ∈ bGd := bGd_hrd sz_bG b_xr
    rw [sewr, dite_eq_left b_xr]
    simp only [sewd, sewFace, dite_eq_left b_yd]
    rw [hdr_hrd UbGd sz_bG b_xr]
  · rw [sewr_Gr sz_bG b_xr]
    rfl

/-- `sew_edge` on the image of a dart of `Gr` (a step of math-comp `sew_map_patch`). -/
private theorem sewEdge_sewr (cycEbGd : Gd.SFCycle Gd.edge bGd) (xr : Dr) :
    sewEdge Gd Gr sz_bG (sewr sz_bG xr) = sewr sz_bG (Gr.edge xr) := by
  have UbGd : bGd.Nodup := Gd.scycle_uniq cycEbGd
  by_cases b_xr : xr ∈ bGr
  · have b_yd : hrd bGd bGr (inBGr sz_bG b_xr) xr ∈ bGd := bGd_hrd sz_bG b_xr
    rw [sewr, dite_eq_left b_xr]
    simp only [sewd, sewEdge, dite_eq_left b_yd]
    rw [hdr_hrd UbGd sz_bG b_xr]
  · rw [sewr_Gr sz_bG b_xr]
    rfl

end SewMap

/-- math-comp `sew_map_subproof`: the sewn permutations satisfy `cancel3 edge node face`. -/
theorem sew_map_subproof [Finite Dd] [Finite Dr] {Gd : Hypermap Dd} {Gr : Hypermap Dr}
    {bGd : List Dd} {bGr : List Dr} (cycEbGd : Gd.SFCycle Gd.edge bGd)
    (cycNbGr : UCycle (frel Gr.node) bGr) (sz_bG : bGd.length = bGr.length)
    (w : SewDart Dd bGr) :
    sewNode Gd Gr sz_bG (sewFace Gd Gr sz_bG (sewEdge Gd Gr sz_bG w)) = w := by
  have UbGd : bGd.Nodup := Gd.scycle_uniq cycEbGd
  have UbGr : bGr.Nodup := cycNbGr.2
  rcases w with xd | ⟨xr, b'xr⟩
  · by_cases b_xd : xd ∈ bGd
    · set xr1 := hdr bGd bGr (inBGd sz_bG b_xd) xd
      have b_xr1 : xr1 ∈ bGr := bGr_hdr sz_bG b_xd
      have hE : sewEdge Gd Gr sz_bG (Sum.inl xd) = sewr sz_bG (Gr.edge xr1) := by
        simp only [sewEdge, dite_eq_left b_xd, xr1]
      have b_fexr : Gr.face (Gr.edge xr1) ∈ bGr := EbGrN1 cycNbGr (by rw [Gr.edgeK]; exact b_xr1)
      have hF : sewFaceR Gd Gr sz_bG (Gr.edge xr1) = sewd bGr (Gd.face (Gd.edge xd)) := by
        unfold sewFaceR
        rw [sewr_bGr sz_bG (xd0 := xd) b_fexr]
        show sewd bGr (Gd.face (hrd bGd bGr xd (Gr.face (Gr.edge xr1)))) = _
        rw [← edge_hrd cycEbGd cycNbGr sz_bG b_xr1, hrd_hdr UbGr sz_bG b_xd]
      rw [hE, sewFace_sewr sz_bG cycEbGd, hF]
      show sewd bGr (Gd.node (Gd.face (Gd.edge xd))) = _
      rw [Gd.edgeK]
      rfl
    · have b'exd : Gd.edge xd ∉ bGd := fun h => b_xd (EbGdE1 cycEbGd h)
      simp only [sewEdge, dite_eq_right b_xd, sewd, sewFace, dite_eq_right b'exd, sewNode,
        Gd.edgeK]
  · have b'fexr : Gr.face (Gr.edge xr) ∉ bGr := fun h =>
      b'xr ((EbGrN cycNbGr h xr).1 (connect_of_rel (Gr.edgeK xr)))
    show sewNode Gd Gr sz_bG (sewFace Gd Gr sz_bG (sewr sz_bG (Gr.edge xr))) = _
    rw [sewFace_sewr sz_bG cycEbGd]
    unfold sewFaceR
    rw [sewr_Gr sz_bG b'fexr]
    show sewr sz_bG (Gr.node (Gr.face (Gr.edge xr))) = _
    rw [Gr.edgeK, sewr_Gr sz_bG b'xr]
    rfl

/-- math-comp `sew_map`: the hypermap obtained by glueing `Gd` and `Gr` along the simple E-cycle
`bGd` of `Gd` and the duplicate-free N-cycle `bGr` of `Gr`, which have the same length. -/
def sewMap [Finite Dd] [Finite Dr] {Gd : Hypermap Dd} {Gr : Hypermap Dr} {bGd : List Dd}
    {bGr : List Dr} (cycEbGd : Gd.SFCycle Gd.edge bGd) (cycNbGr : UCycle (frel Gr.node) bGr)
    (sz_bG : bGd.length = bGr.length) : Hypermap (SewDart Dd bGr) where
  edge := sewEdge Gd Gr sz_bG
  node := sewNode Gd Gr sz_bG
  face := sewFace Gd Gr sz_bG
  edgeK := sew_map_subproof cycEbGd cycNbGr sz_bG

section SewPatch

variable [Finite Dd] [Finite Dr] {Gd : Hypermap Dd} {Gr : Hypermap Dr} {bGd : List Dd}
  {bGr : List Dr}

omit [Finite Dd] [Finite Dr] in
/-- math-comp `sewr_rev_sewd`: the two borders are glued in opposite directions. -/
theorem sewr_rev_sewd (cycEbGd : Gd.SFCycle Gd.edge bGd) (cycNbGr : UCycle (frel Gr.node) bGr)
    (sz_bG : bGd.length = bGr.length) :
    bGr.map (sewr sz_bG) = (bGd.map (sewd bGr)).reverse := by
  have UbGd : bGd.Nodup := Gd.scycle_uniq cycEbGd
  have UbGr : bGr.Nodup := cycNbGr.2
  refine List.ext_getElem (by simp [sz_bG]) fun j h1 h2 => ?_
  have hj : j < bGr.length := by simpa using h1
  have hk : bGd.length - 1 - j < bGd.length := by omega
  rw [List.getElem_map, List.getElem_reverse, List.getElem_map]
  have e : bGr[j] = hdr bGd bGr bGr[j] bGd[bGd.length - 1 - j] := by
    rw [hdr_getElem UbGd sz_bG, List.getElem_reverse]
    simp only [show bGr.length - 1 - (bGd.length - 1 - j) = j by omega]
  simp only [List.length_map]
  rw [e, sewr_hdr UbGr sz_bG (List.getElem_mem hk)]

/-- math-comp `sew_map_patch`: the sewn map is the patch of `Gd` and `Gr` along `bGd` and
`bGr`, via the injections `sewd` and `sewr`. -/
theorem sew_map_patch (cycEbGd : Gd.SFCycle Gd.edge bGd) (cycNbGr : UCycle (frel Gr.node) bGr)
    (sz_bG : bGd.length = bGr.length) :
    (sewMap cycEbGd cycNbGr sz_bG).Patch Gd Gr (sewd bGr) (sewr sz_bG) bGd bGr where
  injd := inj_sewd bGr
  injr := inj_sewr cycEbGd sz_bG
  cycle_d := cycEbGd
  cycle_r := cycNbGr
  map_ring_r := sewr_rev_sewd cycEbGd cycNbGr sz_bG
  codom_r := by
    have UbGr : bGr.Nodup := cycNbGr.2
    rintro (xd | ⟨xr, b'xr⟩)
    · have h1 : (Sum.inl xd : SewDart Dd bGr) ∈ Set.range (sewd bGr) := ⟨xd, rfl⟩
      have h2 : (Sum.inl xd : SewDart Dd bGr) ∈ bGd.map (sewd bGr) ↔ xd ∈ bGd :=
        List.mem_map_of_injective (inj_sewd bGr)
      rw [h2]
      simp only [h1, not_true_eq_false, false_or]
      constructor
      · rintro ⟨xr, hxr⟩
        by_cases b_xr : xr ∈ bGr
        · rw [sewr_bGr sz_bG (xd0 := xd) b_xr] at hxr
          rw [← inj_sewd bGr hxr]
          exact bGd_hrd sz_bG b_xr
        · rw [sewr_Gr sz_bG b_xr] at hxr
          exact absurd hxr Sum.inr_ne_inl
      · intro b_xd
        exact ⟨hdr bGd bGr (inBGd sz_bG b_xd) xd, sewr_hdr UbGr sz_bG b_xd⟩
    · refine iff_of_true ⟨xr, sewr_Gr sz_bG b'xr⟩ (Or.inl ?_)
      rintro ⟨xd, h⟩
      exact Sum.inl_ne_inr h
  edge_d := fun xd b'xd => by
    show sewd bGr (Gd.edge xd) = sewEdge Gd Gr sz_bG (Sum.inl xd)
    simp only [sewEdge, dite_eq_right b'xd]
  node_d := fun _ => rfl
  edge_r := fun xr => (sewEdge_sewr sz_bG cycEbGd xr).symm
  node_r := fun xr b'xr => by
    show sewr sz_bG (Gr.node xr) = sewNode Gd Gr sz_bG (sewr sz_bG xr)
    rw [sewr_Gr sz_bG b'xr]
    rfl

end SewPatch

end Sew

end Hypermap

end FourColor
