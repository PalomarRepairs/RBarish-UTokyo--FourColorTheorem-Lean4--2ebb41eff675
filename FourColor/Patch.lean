/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Coloring

/-!
# Patching two maps to cover a larger one  (port of `patch.v`)

The relations established here are used in both directions: with sew, to deduce the properties
of the new map created by glueing, and in snip, to deduce the properties of the two maps created
by cutting along a ring (i.e., a simple R-cycle).

It is important to note that the relations between the two parts are not quite symmetrical: the
border of the inside ("disk") map is an edge cycle, while the border of the outer ("remainder")
part is a node orbit. The disk border E-cycle must be simple, but only in the disk map; the
corresponding R-cycle in the main map, and N-cycle in the remainder map need only be
duplicate-free.

* `G.Patch Gd Gr hd hr bGd bGr` : the hypermap `G` is the glueing via `hd : Dd → D` and
  `hr : Dr → D` of the disk hypermap `Gd` and the remainder hypermap `Gr`, along their
  respective edge and node borders `bGd` and `bGr`: `bGd` is a simple E-cycle of `Gd`, `bGr` a
  duplicate-free N-cycle of `Gr`, `hd` and `hr` are injective, their ranges cover `G` and
  intersect exactly on the border R-ring, `bGr.map hr = (bGd.map hd).reverse`; except on the
  border, `hd` preserves E-links and `hr` preserves N-links (Coq `patch`).
* `G.outer hr` : the face closure of the range of `hr` (Coq `outer`).

The consequences of `hP : G.Patch Gd Gr hd hr bGd bGr` are in the namespace `Hypermap.Patch`,
so that they can be used with dot notation: `hP.card_patch`, `hP.plain_patch`,
`hP.cubic_patch`, `hP.patch_face_r`, `hP.patch_bridgeless`, `hP.bridgeless_patch`,
`hP.genus_patch`, `hP.planar_patch`, `hP.colorable_patch`, ...

At the end of this file we give a first application of patching: we prove that a minimal
counter example must be connected, using

* `G.gcompDisk z` : the "disk" hypermap whose set of darts `G.GcompdDart z` is the connected
  component of `z` in a hypermap `G` (Coq `gcomp_disk`, `gcompd_dart`);
* `G.gcompRem z`  : the "remainder" hypermap whose set of darts `G.GcomprDart z` is the
  complement of the connected component of `z` (Coq `gcomp_rem`, `gcompr_dart`);
* `G.gcompd z u`, `G.gcompr z u` : the projections in `G` of darts of `gcompDisk z` and
  `gcompRem z` (Coq `gcompd`, `gcompr`).

For any dart `z` of `G`, `G.Patch (G.gcompDisk z) (G.gcompRem z) (G.gcompd z) (G.gcompr z) [] []`
holds (`patch_gcomp`), though `gcompRem z` is empty when `G` is connected.

## Porting notes

* math-comp `codom f` is `Set.range f`, and `=i` is a pointwise `↔`; boolean equations between
  predicates (`plain_patch`, `cubic_patch`, `planar_patch`, `patch_face_d`, ...) are `↔`.
* `plainb [predC bGd]` is `Gd.PlainOn {x | x ∉ bGd}`, `cubicb [predC bGr]` is
  `Gr.CubicOn {x | x ∉ bGr}`, and `plainb Gr`, `cubicb Gd`, `planarb Gd` are `Gr.Plain`,
  `Gd.Cubic`, `Gd.Planar`.
* The section `Let`s of the Coq file (`EbGr`, `im_hd`, `EbGdr`, `hdErN`, `bGdP`, `hdF`, `hrF`,
  `hdFrF`, `adj_hd`, `cFhd`, `oaGr`, ...) are private theorems of the namespace `Hypermap.Patch`.
* math-comp's `adjunction_n_comp` allows the points of the counted set to be merely connected to
  the image of the adjunction; since `FourColor.nComp_adjunction` requires them to lie in the
  image, the general form is proved here as the private lemma `nComp_adjunction_closed`.
* The math-comp lemmas on `next`/`prev` used here (`next_cycle`, `prev_cycle`, `next_map`,
  `next_rev`, `prev_next`, `next_prev`, `mem_next`) are proved as private lemmas, through
  Mathlib's `List.next`/`List.prev`.
* The dart types `GcompdDart z`, `GcomprDart z` are type synonyms of subtypes, with
  (noncomputable, classical) `Fintype` instances and `DecidableEq`, `Finite` instances.
* The Coq coercions `minimal_counter_example_is_connected`,
  `minimal_counter_example_is_planar_bridgeless_plain_connected` and
  `minimal_counter_example_is_planar_plain_cubic_connected` are theorems, with the dot-notation
  versions `MinimalCounterExample.connected`,
  `MinimalCounterExample.toPlanarBridgelessPlainConnected` and
  `MinimalCounterExample.toPlanarPlainCubicConnected`.
-/

namespace FourColor

open Function

/-! ### Cyclic successor and predecessor: complements to `FourColor.Geometry` -/

section NextPrev

variable {α β : Type*} [DecidableEq α]

/-- math-comp `next_nth` (default case): `next` fixes the points outside the sequence. -/
private theorem next_of_not_mem {p : List α} {x : α} (h : x ∉ p) : next p x = x := by
  cases p with
  | nil => rfl
  | cons y p => exact nextAt_of_not_mem h

/-- math-comp `prev_nth` (default case): `prev` fixes the points outside the sequence. -/
private theorem prev_of_not_mem {p : List α} {x : α} (h : x ∉ p) : prev p x = x := by
  cases p with
  | nil => rfl
  | cons y p =>
    show prevAt x y y p = x
    rw [prevAt_of_not_mem (fun hm => h (List.mem_cons_of_mem _ hm)),
      ite_eq_right (fun e => h (List.mem_cons.2 (Or.inl e)))]

/-- `next_at` agrees with Mathlib's `List.nextOr` on the items of the sequence. -/
private theorem nextAt_eq_nextOr {x y0 : α} :
    ∀ {y : α} {p : List α}, x ∈ y :: p → nextAt x y0 y p = List.nextOr (y :: p) x y0
  | y, [], h => by
    rw [List.mem_singleton] at h
    subst h
    simp [nextAt, List.nextOr]
  | y, z :: p, h => by
    by_cases hxy : x = y
    · subst hxy
      simp [nextAt, List.nextOr]
    · have h' : x ∈ z :: p := (List.mem_cons.1 h).resolve_left hxy
      rw [nextAt, ite_eq_right hxy, nextAt_eq_nextOr h', List.nextOr_cons_of_ne _ _ _ _ hxy]

/-- The total `next` agrees with Mathlib's `List.next` on the items of the sequence. -/
private theorem next_eq_listNext {p : List α} {x : α} (hx : x ∈ p) :
    next p x = p.next x hx := by
  cases p with
  | nil => simp at hx
  | cons y p =>
    show nextAt x y y p = _
    rw [nextAt_eq_nextOr hx]
    rfl

omit [DecidableEq α] in
/-- math-comp `last` agrees with `List.getLast`. -/
private theorem last_eq_getLast (z : α) (p : List α) :
    last z p = (z :: p).getLast (List.cons_ne_nil z p) := by
  induction p generalizing z with
  | nil => rfl
  | cons w p ih => rw [last_cons, ih w, List.getLast_cons_cons]

/-- `prev_at` agrees with Mathlib's `List.prev` on the tail items of a duplicate-free
sequence. -/
private theorem prevAt_eq_listPrev {x y0 : α} :
    ∀ {y : α} {p : List α} (_ : (y :: p).Nodup) (hx : x ∈ p),
      prevAt x y0 y p = (y :: p).prev x (List.mem_cons_of_mem _ hx)
  | y, [], _, hx => by simp at hx
  | y, z :: p, hn, hx => by
    have hxy : x ≠ y := by
      rintro rfl
      exact (List.nodup_cons.1 hn).1 hx
    by_cases hxz : x = z
    · subst hxz
      rw [prevAt, ite_eq_left rfl, List.prev_cons_cons_of_ne (hy := hxy)]
    · have hx' : x ∈ p := (List.mem_cons.1 hx).resolve_left hxz
      rw [prevAt, ite_eq_right hxz, List.prev_ne_cons_cons (hy := hxy) (hz := hxz),
        prevAt_eq_listPrev (List.nodup_cons.1 hn).2 hx']

/-- The total `prev` agrees with Mathlib's `List.prev` on the items of a duplicate-free
sequence. -/
private theorem prev_eq_listPrev {p : List α} (hp : p.Nodup) {x : α} (hx : x ∈ p) :
    prev p x = p.prev x hx := by
  cases p with
  | nil => simp at hx
  | cons y p =>
    show prevAt x y y p = _
    by_cases hxy : x = y
    · subst hxy
      have hxp : x ∉ p := (List.nodup_cons.1 hp).1
      rw [prevAt_of_not_mem hxp, ite_eq_left rfl]
      cases p with
      | nil => rfl
      | cons z p =>
        rw [List.prev_cons_cons_eq, last_cons, last_eq_getLast]
    · rw [prevAt_eq_listPrev hp ((List.mem_cons.1 hx).resolve_left hxy)]

/-- math-comp `mem_next`. -/
private theorem mem_next {p : List α} {x : α} : next p x ∈ p ↔ x ∈ p := by
  by_cases hx : x ∈ p
  · rw [next_eq_listNext hx]
    exact ⟨fun _ => hx, fun _ => List.next_mem _ _ _⟩
  · rw [next_of_not_mem hx]

/-- math-comp `prev_next`. -/
private theorem prev_next {p : List α} (hp : p.Nodup) (x : α) : prev p (next p x) = x := by
  by_cases hx : x ∈ p
  · rw [prev_eq_listPrev hp (mem_next.2 hx)]
    simp only [next_eq_listNext hx]
    exact List.prev_next p hp x hx
  · rw [next_of_not_mem hx, prev_of_not_mem hx]

/-- math-comp `mem_prev`. -/
private theorem mem_prev {p : List α} (hp : p.Nodup) {x : α} : prev p x ∈ p ↔ x ∈ p := by
  by_cases hx : x ∈ p
  · rw [prev_eq_listPrev hp hx]
    exact ⟨fun _ => hx, fun _ => List.prev_mem _ _ _⟩
  · rw [prev_of_not_mem hx]

/-- math-comp `next_prev`. -/
private theorem next_prev {p : List α} (hp : p.Nodup) (x : α) : next p (prev p x) = x := by
  by_cases hx : x ∈ p
  · rw [next_eq_listNext ((mem_prev hp).2 hx)]
    simp only [prev_eq_listPrev hp hx]
    exact List.next_prev p hp x hx
  · rw [prev_of_not_mem hx, next_of_not_mem hx]

/-- math-comp `next_rev`. -/
private theorem next_rev {p : List α} (hp : p.Nodup) (x : α) :
    next p.reverse x = prev p x := by
  by_cases hx : x ∈ p
  · rw [next_eq_listNext (List.mem_reverse.2 hx), prev_eq_listPrev hp hx]
    exact List.next_reverse_eq_prev p hp x hx
  · rw [next_of_not_mem (fun h => hx (List.mem_reverse.1 h)), prev_of_not_mem hx]

/-- `next_at` commutes with injections (helper for math-comp `next_map`). -/
private theorem nextAt_map [DecidableEq β] {f : α → β} (hf : Injective f) (x y0 : α) :
    ∀ (y : α) (p : List α), nextAt (f x) (f y0) (f y) (p.map f) = f (nextAt x y0 y p)
  | y, [] => by
    simp only [List.map_nil, nextAt, hf.eq_iff]
    split_ifs <;> rfl
  | y, z :: p => by
    simp only [List.map_cons, nextAt, hf.eq_iff]
    split_ifs
    · rfl
    · exact nextAt_map hf x y0 z p

/-- math-comp `next_map`. -/
private theorem next_map [DecidableEq β] {f : α → β} (hf : Injective f) (p : List α) (x : α) :
    next (p.map f) (f x) = f (next p x) := by
  cases p with
  | nil => rfl
  | cons y p => exact nextAt_map hf x y y p

/-- Helper for math-comp `next_cycle`. -/
private theorem nextAt_cycle {e : α → α → Prop} {x y0 : α} :
    ∀ {y : α} {p : List α}, path e y (p ++ [y0]) → x ∈ y :: p → e x (nextAt x y0 y p)
  | y, [], hp, hx => by
    rw [List.mem_singleton] at hx
    subst hx
    rw [nextAt, ite_eq_left rfl]
    exact hp.1
  | y, z :: p, hp, hx => by
    rw [nextAt]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
      subst hxy
      exact hp.1
    · rw [ite_eq_right hxy]
      exact nextAt_cycle hp.2 ((List.mem_cons.1 hx).resolve_left hxy)

/-- math-comp `next_cycle`. -/
private theorem next_cycle {e : α → α → Prop} {p : List α} (hp : cycle e p) {x : α}
    (hx : x ∈ p) : e x (next p x) := by
  cases p with
  | nil => simp at hx
  | cons y p => exact nextAt_cycle hp hx

/-- Helper for math-comp `prev_cycle`. -/
private theorem prevAt_cycle {e : α → α → Prop} {x y0 : α} :
    ∀ {y : α} {p : List α}, path e y (p ++ [y0]) → x ∈ p ++ [y0] → e (prevAt x y0 y p) x
  | y, [], hp, hx => by
    rw [List.nil_append, List.mem_singleton] at hx
    subst hx
    rw [prevAt, ite_eq_left rfl]
    exact hp.1
  | y, z :: p, hp, hx => by
    rw [prevAt]
    by_cases hxz : x = z
    · rw [ite_eq_left hxz]
      subst hxz
      exact hp.1
    · rw [ite_eq_right hxz]
      exact prevAt_cycle hp.2 ((List.mem_cons.1 hx).resolve_left hxz)

/-- math-comp `prev_cycle`. -/
private theorem prev_cycle {e : α → α → Prop} {p : List α} (hp : cycle e p) {x : α}
    (hx : x ∈ p) : e (prev p x) x := by
  cases p with
  | nil => simp at hx
  | cons y p =>
    refine prevAt_cycle hp ?_
    rcases List.mem_cons.1 hx with rfl | h
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_left _ h

end NextPrev

/-- math-comp `adjunction_n_comp`, in its general form: the points of the `e`-closed set `a`
need only be connected to (rather than equal to) images of `h`. -/
private theorem nComp_adjunction_closed {α β : Type*} {e : α → α → Prop}
    {e' : β → β → Prop} (hs : ConnectSym e) (hs' : ConnectSym e') (h : β → α) {a : Set α}
    (ha : Closed e a) (hunit : ∀ x ∈ a, ∃ x', connect e x (h x'))
    (hfun : ∀ x' y', h x' ∈ a → h y' ∈ a → (connect e' x' y' ↔ connect e (h x') (h y'))) :
    nComp e a = nComp e' (h ⁻¹' a) := by
  have himg : comp e '' a = (comp e ∘ h) '' (h ⁻¹' a) := by
    ext c
    simp only [Set.mem_image, Set.mem_preimage, Function.comp_apply]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨x', hxx'⟩ := hunit x hx
      exact ⟨x', (ha.connect_iff hxx').1 hx, ((comp_eq_iff hs).2 hxx').symm⟩
    · rintro ⟨x', hx', rfl⟩
      exact ⟨h x', hx', rfl⟩
  rw [nComp, nComp, himg]
  apply ncard_image_eq_of_ker
  intro x hx y hy
  simp only [comp_apply]
  rw [comp_eq_iff hs, comp_eq_iff hs', hfun x y hx hy]

/-- Two lists with the same image under the injection `f` and `g`, and under `f'` and `g'`:
the items glued by `f` and `g` have the same images by `f'` and `g'` (used for math-comp's
local `eq_kdr` in `colorable_patch`). -/
private theorem map_eq_map_mem {α β γ δ : Type*} {f : α → γ} {g : β → γ} {f' : α → δ}
    {g' : β → δ} (hf : Injective f) :
    ∀ {l1 : List α} {l2 : List β}, l1.map f = l2.map g → l1.map f' = l2.map g' →
      ∀ x y, y ∈ l2 → f x = g y → f' x = g' y
  | [], [], _, _, _, _, hy, _ => absurd hy List.not_mem_nil
  | [], _ :: _, h, _, _, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _, _, _ => by simp at h
  | a :: l1, b :: l2, h, h', x, y, hy, hxy => by
    simp only [List.map_cons, List.cons.injEq] at h h'
    rcases List.mem_cons.1 hy with rfl | hy
    · rw [hf (hxy.trans h.1.symm), h'.1]
    · exact map_eq_map_mem hf h.2 h'.2 x y hy hxy

/-- Shifting a perimeter coloring by a constant color leaves its trace unchanged, and the
shift can be chosen to match the head color of another perimeter coloring with the same
trace (the core of math-comp's local `Tkd'` in `colorable_patch`). -/
private theorem map_addc_of_trace_eq {a b : Color} {s t : Colseq}
    (h : trace (a :: s) = trace (b :: t)) : (a :: s).map (addc (addc a b)) = b :: t := by
  have hb : addc (addc a b) a = b := by rw [addcC, addKc]
  have e : (a :: s).map (addc (addc a b)) = b :: s.map (addc (addc a b)) := by
    rw [List.map_cons, hb]
  rw [e, ← untrace_trace b (s.map (addc (addc a b))), ← e, trace_addc, h, untrace_trace]

namespace Hypermap

universe u v w

/-! ### The `patch` predicate -/

section PatchDef

variable {D : Type u} {Dd : Type v} {Dr : Type w}

/-- math-comp `patch hd hr bGd bGr`: the hypermap `G` is the glueing, via `hd : Dd → D` and
`hr : Dr → D`, of the "disk" hypermap `Gd` and the "remainder" hypermap `Gr` along their
respective edge and node borders `bGd` and `bGr`: `bGd` is a simple E-cycle of `Gd`, `bGr` a
duplicate-free N-cycle of `Gr`, `hd` and `hr` are injective, their ranges cover `G` and
intersect exactly on the border ring, `map hr bGr = rev (map hd bGd)`; except on the border,
`hd` preserves E-links and `hr` preserves N-links. -/
structure Patch (G : Hypermap D) (Gd : Hypermap Dd) (Gr : Hypermap Dr) (hd : Dd → D)
    (hr : Dr → D) (bGd : List Dd) (bGr : List Dr) : Prop where
  /-- math-comp `patch_injd`. -/
  injd : Injective hd
  /-- math-comp `patch_injr`. -/
  injr : Injective hr
  /-- math-comp `patch_cycle_d`: the disk border is a simple E-cycle. -/
  cycle_d : Gd.SFCycle Gd.edge bGd
  /-- math-comp `patch_cycle_r`: the remainder border is a duplicate-free N-cycle. -/
  cycle_r : UCycle (frel Gr.node) bGr
  /-- math-comp `patch_map_ring_r`. -/
  map_ring_r : bGr.map hr = (bGd.map hd).reverse
  /-- math-comp `patch_codom_r`: `codom hr =i [predU [predC codom hd] & map hd bGd]`. -/
  codom_r : ∀ x, x ∈ Set.range hr ↔ x ∉ Set.range hd ∨ x ∈ bGd.map hd
  /-- math-comp `patch_edge_d`: `{in [predC bGd], {morph hd : xd / edge xd}}`. -/
  edge_d : ∀ xd, xd ∉ bGd → hd (Gd.edge xd) = G.edge (hd xd)
  /-- math-comp `patch_node_d`: `{morph hd : xd / node xd}`. -/
  node_d : ∀ xd, hd (Gd.node xd) = G.node (hd xd)
  /-- math-comp `patch_edge_r`: `{morph hr : xr / edge xr}`. -/
  edge_r : ∀ xr, hr (Gr.edge xr) = G.edge (hr xr)
  /-- math-comp `patch_node_r`: `{in [predC bGr], {morph hr : xr / node xr}}`. -/
  node_r : ∀ xr, xr ∉ bGr → hr (Gr.node xr) = G.node (hr xr)

/-- math-comp `outer`: the face closure of the range of `hr`, i.e., the darts of `G` whose face
meets the remainder map. -/
def outer (G : Hypermap D) (hr : Dr → D) : Set D := fclosure G.face (Set.range hr)

/-- math-comp `closed_outer`. -/
theorem closed_outer [Finite D] (G : Hypermap D) (hr : Dr → D) :
    Closed (frel G.face) (G.outer hr) :=
  closure_closed G.cface_sym _

/-- math-comp `closed_outerC` (a `Remark` in math-comp). -/
theorem closed_outerC [Finite D] (G : Hypermap D) (hr : Dr → D) :
    Closed (frel G.face) (G.outer hr)ᶜ :=
  (closed_outer G hr).compl

end PatchDef

/-! ### Local consequences of `patch` (math-comp section `Let`s) -/

namespace Patch

variable {D : Type u} {Dd : Type v} {Dr : Type w} {G : Hypermap D} {Gd : Hypermap Dd}
  {Gr : Hypermap Dr} {hd : Dd → D} {hr : Dr → D} {bGd : List Dd} {bGr : List Dr}
  (hP : G.Patch Gd Gr hd hr bGd bGr)
include hP

/-- math-comp local `EbGr`. -/
private theorem EbGr (u : D) : u ∈ bGr.map hr ↔ u ∈ bGd.map hd := by
  rw [hP.map_ring_r, List.mem_reverse]

/-- math-comp local `im_hd`. -/
private theorem im_hd (x : D) : x ∈ Set.range hd ↔ x ∉ Set.range hr ∨ x ∈ bGd.map hd := by
  rw [hP.codom_r]
  by_cases hb : x ∈ bGd.map hd
  · simp only [hb, or_true, iff_true]
    obtain ⟨xd, -, rfl⟩ := List.mem_map.1 hb
    exact ⟨xd, rfl⟩
  · simp only [hb, or_false, not_not]

/-- math-comp local `UbGd`. -/
private theorem UbGd : bGd.Nodup := Gd.scycle_uniq hP.cycle_d

/-- math-comp local `UbGr`. -/
private theorem UbGr : bGr.Nodup := hP.cycle_r.2

/-- math-comp local `UbG`. -/
private theorem UbG : (bGd.map hd).Nodup := hP.UbGd.map hP.injd

/-- math-comp local `EbGdr`. -/
private theorem EbGdr (xd : Dd) : hd xd ∈ Set.range hr ↔ xd ∈ bGd := by
  rw [hP.codom_r, List.mem_map_of_injective hP.injd]
  simp

/-- math-comp local `EbGdE`. -/
private theorem EbGdE {xd : Dd} (h : xd ∈ bGd) (yd : Dd) : Gd.cedge xd yd ↔ yd ∈ bGd :=
  fconnect_cycle hP.cycle_d.1 h

/-- math-comp local `EbGrd`. -/
private theorem EbGrd (xr : Dr) : hr xr ∈ Set.range hd ↔ xr ∈ bGr := by
  rw [hP.im_hd, ← hP.EbGr, List.mem_map_of_injective hP.injr]
  simp

/-- math-comp local `EbGrN`. -/
private theorem EbGrN {xr : Dr} (h : xr ∈ bGr) (yr : Dr) : Gr.cnode xr yr ↔ yr ∈ bGr :=
  fconnect_cycle hP.cycle_r.1 h

/-- math-comp local `EhdUr`. -/
private theorem EhdUr (x : D) : x ∈ Set.range hd ∨ x ∈ Set.range hr := by
  rw [hP.codom_r]
  tauto

/-- math-comp local `EhdIr`. -/
private theorem EhdIr (x : D) : (x ∈ Set.range hd ∧ x ∈ Set.range hr) ↔ x ∈ bGd.map hd := by
  rw [hP.codom_r]
  constructor
  · rintro ⟨h1, h2 | h2⟩
    · exact absurd h1 h2
    · exact h2
  · intro h
    obtain ⟨xd, -, rfl⟩ := List.mem_map.1 h
    exact ⟨⟨xd, rfl⟩, Or.inr h⟩

variable [Finite Dd] [Finite Dr] [Finite D]

omit [Finite Dr] [Finite D] in
/-- math-comp local `clEbGd`. -/
private theorem clEbGd : Closed (frel Gd.edge) {x | x ∈ bGd} :=
  Closed.of_forward Gd.cedge_sym fun xd _ h hx =>
    (hP.EbGdE hx _).1 (by rw [← h]; exact fconnect1 _ _)

omit [Finite Dd] [Finite D] in
/-- math-comp local `clNbGr`. -/
private theorem clNbGr : Closed (frel Gr.node) {x | x ∈ bGr} :=
  Closed.of_forward Gr.cnode_sym fun xr _ h hx =>
    (hP.EbGrN hx _).1 (by rw [← h]; exact fconnect1 _ _)

omit [Finite Dr] [Finite D] in
/-- The darts off the disk border are closed under `edge` (a use of math-comp local
`clEbGd`). -/
private theorem not_mem_bGd_edge {xd : Dd} (h : xd ∉ bGd) : Gd.edge xd ∉ bGd :=
  fun h' => h ((hP.clEbGd _ _ rfl).2 h')

omit [Finite Dd] [Finite D] in
/-- The darts off the remainder border are closed under `node` (a use of math-comp local
`clNbGr`). -/
private theorem not_mem_bGr_node {xr : Dr} (h : xr ∉ bGr) : Gr.node xr ∉ bGr :=
  fun h' => h ((hP.clNbGr _ _ rfl).2 h')

omit [Finite D] in
/-- math-comp local `hdErN`. -/
private theorem hdErN (xd : Dd) (xr : Dr) :
    hd (Gd.edge xd) = hr xr ↔ hd xd = hr (Gr.node xr) := by
  classical
  by_cases b_xd : xd ∈ bGd
  · have hn1 : Gd.edge xd = next bGd xd := next_cycle hP.cycle_d.1 b_xd
    have key : ∀ a b : D, next (bGd.map hd) a = b ↔ a = prev (bGd.map hd) b := by
      intro a b
      constructor
      · rintro rfl
        exact (prev_next hP.UbG a).symm
      · rintro rfl
        exact next_prev hP.UbG b
    rw [hn1, ← next_map hP.injd, key, ← next_rev hP.UbG, ← hP.map_ring_r, next_map hP.injr]
    by_cases b_xr : xr ∈ bGr
    · have hn2 : Gr.node xr = next bGr xr := next_cycle hP.cycle_r.1 b_xr
      rw [hn2]
    · constructor <;> intro Dx <;> exfalso <;> apply b_xr
      · rw [← mem_next, ← List.mem_map_of_injective hP.injr, hP.EbGr, ← Dx]
        exact List.mem_map_of_mem b_xd
      · refine (hP.clNbGr _ _ rfl).2 ?_
        show Gr.node xr ∈ bGr
        rw [← List.mem_map_of_injective hP.injr, hP.EbGr, ← Dx]
        exact List.mem_map_of_mem b_xd
  · constructor <;> intro Dx <;> exfalso <;> apply b_xd
    · refine (hP.clEbGd _ _ rfl).2 ?_
      show Gd.edge xd ∈ bGd
      rw [← List.mem_map_of_injective hP.injd, ← hP.EhdIr]
      exact ⟨⟨_, rfl⟩, ⟨xr, Dx.symm⟩⟩
    · rw [← List.mem_map_of_injective hP.injd, ← hP.EhdIr]
      exact ⟨⟨_, rfl⟩, ⟨_, Dx.symm⟩⟩

omit [Finite D] in
/-- math-comp local `bGdP`. -/
private theorem bGdP {xd : Dd} (b_xd : xd ∈ bGd) :
    ∃ xr, hd (Gd.edge xd) = hr xr ∧ hd xd = hr (Gr.node xr) := by
  obtain ⟨yr, hyr⟩ := (hP.EbGdr xd).2 b_xd
  refine ⟨Gr.face (Gr.edge yr), ?_, ?_⟩
  · rw [hP.hdErN, Gr.edgeK, hyr]
  · rw [Gr.edgeK, hyr]

omit [Finite D] in
/-- math-comp local `bGrP`. -/
private theorem bGrP {xr : Dr} (b_xr : xr ∈ bGr) :
    ∃ xd, hd (Gd.edge xd) = hr xr ∧ hd xd = hr (Gr.node xr) := by
  obtain ⟨yd, hyd⟩ := (hP.EbGrd xr).2 b_xr
  refine ⟨Gd.node (Gd.face yd), ?_, ?_⟩
  · rw [Gd.faceK, hyd]
  · rw [← hP.hdErN, Gd.faceK, hyd]

omit [Finite Dr] in
/-- math-comp local `hdF`. -/
private theorem hdF {xd : Dd} (b'xd : xd ∉ bGd) : hd (Gd.face xd) = G.face (hd xd) := by
  have h1 : Gd.node (Gd.face xd) ∉ bGd := fun h => b'xd (by
    have := (hP.clEbGd _ _ rfl).1 h
    rwa [Gd.faceK] at this)
  have h2 : hd xd = G.edge (G.node (hd (Gd.face xd))) := by
    conv_lhs => rw [← Gd.faceK xd]
    rw [hP.edge_d _ h1, hP.node_d]
  rw [h2, G.nodeK]

omit [Finite Dd] in
/-- math-comp local `hrF`. -/
private theorem hrF {xr : Dr} (b'fxr : Gr.face xr ∉ bGr) :
    hr (Gr.face xr) = G.face (hr xr) := by
  have h : hr xr = G.edge (G.node (hr (Gr.face xr))) := by
    conv_lhs => rw [← Gr.faceK xr]
    rw [hP.edge_r, hP.node_r _ b'fxr]
  rw [h, G.nodeK]

/-- math-comp local `hdFrF`. -/
private theorem hdFrF (xd : Dd) (xr : Dr) :
    hd (Gd.face xd) = G.face (hr xr) ↔ hd xd = hr (Gr.face xr) := by
  have e1 : G.edge (hr (Gr.node (Gr.face xr))) = hr xr := by rw [← hP.edge_r, Gr.faceK]
  conv_rhs => rw [← Gd.faceK xd]
  rw [hP.hdErN, hP.node_d, eq_comm (a := G.node _), G.eq_node_iff, e1, eq_comm]

end Patch

/-! ### Counting darts, closure properties, and geometrical properties of patched maps -/

section PatchLemmas

variable {D : Type u} {Dd : Type v} {Dr : Type w} {G : Hypermap D} {Gd : Hypermap Dd}
  {Gr : Hypermap Dr} {hd : Dd → D} {hr : Dr → D} {bGd : List Dd} {bGr : List Dr}

namespace Patch

/-- math-comp `card_patch`. -/
theorem card_patch [Fintype D] [Fintype Dd] [Fintype Dr]
    (hP : G.Patch Gd Gr hd hr bGd bGr) :
    Fintype.card Dd + Fintype.card Dr = (bGd.map hd).length + Fintype.card D := by
  have h1 := Set.ncard_range_of_injective hP.injd
  have h2 := Set.ncard_range_of_injective hP.injr
  have h3 := Set.ncard_union_add_ncard_inter (Set.range hd) (Set.range hr)
  have hU : Set.range hd ∪ Set.range hr = Set.univ := Set.eq_univ_of_forall hP.EhdUr
  have hI : Set.range hd ∩ Set.range hr = {x | x ∈ bGd.map hd} := Set.ext hP.EhdIr
  rw [hU, hI, Set.ncard_univ, ncard_mem_of_nodup hP.UbG] at h3
  simp only [Nat.card_eq_fintype_card] at h1 h2 h3
  omega

/-- math-comp `patch_fcard_face_d`. -/
theorem patch_fcard_face_d [Finite Dd] (hP : G.Patch Gd Gr hd hr bGd bGr) :
    fcard Gd.face Set.univ = (bGd.map hd).length + fcard Gd.face (Gd.fband bGd)ᶜ := by
  rw [List.length_map, ← Gd.scycle_fcard_fband hP.cycle_d]
  exact nComp_compl (Gd.fbandF bGd)

/-- math-comp `closed_Gr`. -/
theorem closed_Gr [Finite D] (hP : G.Patch Gd Gr hd hr bGd bGr) :
    Closed (frel G.edge) (Set.range hr) :=
  Closed.of_forward G.cedge_sym fun _ _ h => by
    rintro ⟨xr, rfl⟩
    exact ⟨Gr.edge xr, (hP.edge_r xr).trans h⟩

/-- math-comp `closed_Gd`. -/
theorem closed_Gd [Finite D] (hP : G.Patch Gd Gr hd hr bGd bGr) :
    Closed (frel G.node) (Set.range hd) :=
  Closed.of_forward G.cnode_sym fun _ _ h => by
    rintro ⟨xd, rfl⟩
    exact ⟨Gd.node xd, (hP.node_d xd).trans h⟩

variable [Finite D] [Finite Dd] [Finite Dr]

/-- math-comp `plain_patch`. -/
theorem plain_patch (hP : G.Patch Gd Gr hd hr bGd bGr) :
    G.Plain ↔ Gd.PlainOn {x | x ∉ bGd} ∧ Gr.Plain := by
  constructor
  · intro hG
    refine ⟨(Gd.plainP).2 fun xd b'xd => ?_, (Gr.plainP).2 fun xr _ => ?_⟩
    · have b'exd : Gd.edge xd ∉ bGd := hP.not_mem_bGd_edge b'xd
      constructor
      · apply hP.injd
        rw [hP.edge_d _ b'exd, hP.edge_d _ b'xd, G.plain_eq hG]
      · intro h
        apply G.plain_neq hG (hd xd)
        rw [← hP.edge_d _ b'xd, h]
    · constructor
      · apply hP.injr
        rw [hP.edge_r, hP.edge_r, G.plain_eq hG]
      · intro h
        apply G.plain_neq hG (hr xr)
        rw [← hP.edge_r, h]
  · rintro ⟨hGd, hGr⟩
    refine (G.plainP).2 fun x _ => ?_
    by_cases hx : x ∈ Set.range hr
    · obtain ⟨xr, rfl⟩ := hx
      rw [← hP.edge_r, ← hP.edge_r, Gr.plain_eq hGr]
      exact ⟨rfl, fun h => Gr.plain_neq hGr xr (hP.injr h)⟩
    · obtain ⟨xd, rfl⟩ := (hP.EhdUr x).resolve_right hx
      have b'xd : xd ∉ bGd := fun h => hx ((hP.EbGdr xd).2 h)
      obtain ⟨h1, h2⟩ := (Gd.plainP).1 hGd xd b'xd
      rw [← hP.edge_d _ b'xd, ← hP.edge_d _ (hP.not_mem_bGd_edge b'xd), h1]
      exact ⟨rfl, fun h => h2 (hP.injd h)⟩

/-- math-comp `cubic_patch`. -/
theorem cubic_patch (hP : G.Patch Gd Gr hd hr bGd bGr) :
    G.Cubic ↔ Gd.Cubic ∧ Gr.CubicOn {x | x ∉ bGr} := by
  constructor
  · intro hG
    refine ⟨(Gd.cubicP).2 fun xd _ => ?_, (Gr.cubicP).2 fun xr b'xr => ?_⟩
    · constructor
      · apply hP.injd
        rw [hP.node_d, hP.node_d, hP.node_d, G.cubic_eq hG]
      · intro h
        apply G.cubic_neq hG (hd xd)
        rw [← hP.node_d, h]
    · have b'nxr := hP.not_mem_bGr_node b'xr
      have b'nnxr := hP.not_mem_bGr_node b'nxr
      constructor
      · apply hP.injr
        rw [hP.node_r _ b'nnxr, hP.node_r _ b'nxr, hP.node_r _ b'xr, G.cubic_eq hG]
      · intro h
        apply G.cubic_neq hG (hr xr)
        rw [← hP.node_r _ b'xr, h]
  · rintro ⟨hGd, hGr⟩
    refine (G.cubicP).2 fun x _ => ?_
    by_cases hx : x ∈ Set.range hd
    · obtain ⟨xd, rfl⟩ := hx
      rw [← hP.node_d, ← hP.node_d, ← hP.node_d, Gd.cubic_eq hGd]
      exact ⟨rfl, fun h => Gd.cubic_neq hGd xd (hP.injd h)⟩
    · obtain ⟨xr, rfl⟩ := (hP.EhdUr x).resolve_left hx
      have b'xr : xr ∉ bGr := fun h => hx ((hP.EbGrd xr).2 h)
      obtain ⟨h1, h2⟩ := (Gr.cubicP).1 hGr xr b'xr
      have b'nxr := hP.not_mem_bGr_node b'xr
      have b'nnxr := hP.not_mem_bGr_node b'nxr
      rw [← hP.node_r _ b'xr, ← hP.node_r _ b'nxr, ← hP.node_r _ b'nnxr, h1]
      exact ⟨rfl, fun h => h2 (hP.injr h)⟩

omit [Finite Dr] in
/-- math-comp `outer_hd`. -/
theorem outer_hd (hP : G.Patch Gd Gr hd hr bGd bGr) (xd : Dd) :
    hd xd ∈ G.outer hr ↔ xd ∈ Gd.fband bGd := by
  constructor
  · rintro ⟨_, ⟨yr, rfl⟩, hxy⟩
    obtain ⟨p, hp, hl⟩ := connect_iff_path.1 hxy
    clear hxy
    induction p generalizing xd with
    | nil => exact Gd.ring_fband _ _ ((hP.EbGdr xd).1 ⟨yr, hl.symm⟩)
    | cons y p ih =>
      by_cases b_xd : xd ∈ bGd
      · exact Gd.ring_fband _ _ b_xd
      · obtain ⟨hy, hp⟩ := hp
        have hy' : y = hd (Gd.face xd) := by rw [hP.hdF b_xd]; exact hy.symm
        subst hy'
        exact (Gd.fbandF bGd xd _ rfl).2 (ih (Gd.face xd) hp hl)
  · rintro ⟨zd, b_zd, hxz⟩
    obtain ⟨p, hp, hl⟩ := connect_iff_path.1 hxz
    clear hxz
    induction p generalizing xd with
    | nil =>
      have hx : xd = zd := hl
      subst hx
      exact subset_closure _ ((hP.EbGdr xd).2 b_zd)
    | cons yd p ih =>
      by_cases b_xd : xd ∈ bGd
      · exact subset_closure _ ((hP.EbGdr xd).2 b_xd)
      · obtain ⟨rfl, hp⟩ := hp
        have h := ih (Gd.face xd) hp hl
        rw [hP.hdF b_xd] at h
        exact ((closed_outer G hr) _ _ rfl).2 h

omit [Finite Dr] in
/-- math-comp local `adj_hd`: `hd` is a strict adjunction for the face permutations on the
complement of `outer` (math-comp states it as a `fun_adjunction hd face face [predC outer]`
built with `strict_adjunction`; here are the two conditions of `strict_adjunction`). -/
private theorem adj_hd (hP : G.Patch Gd Gr hd hr bGd bGr) :
    (G.outer hr)ᶜ ⊆ Set.range hd ∧
      ∀ xd yd, hd xd ∈ (G.outer hr)ᶜ → (G.face (hd xd) = hd yd ↔ Gd.face xd = yd) := by
  refine ⟨fun x hx => ?_, fun xd yd hx => ?_⟩
  · rcases hP.EhdUr x with h | h
    · exact h
    · exact absurd (subset_closure _ h) hx
  · have b'x : xd ∉ bGd := fun hb => hx ((hP.outer_hd xd).2 (Gd.ring_fband _ _ hb))
    rw [← hP.hdF b'x, hP.injd.eq_iff]

omit [Finite Dr] in
/-- math-comp `patch_face_d`. -/
theorem patch_face_d (hP : G.Patch Gd Gr hd hr bGd bGr) {xd yd : Dd}
    (h : hd xd ∉ G.outer hr) : Gd.cface xd yd ↔ G.cface (hd xd) (hd yd) :=
  connect_iff_of_base hP.injd (fun x y hxy hx => ((closed_outerC G hr) x y hxy).1 hx)
    hP.adj_hd.1 hP.adj_hd.2 h

omit [Finite Dr] in
/-- math-comp local `cFhd`. -/
private theorem cFhd (hP : G.Patch Gd Gr hd hr bGd bGr) (xd : Dd) :
    G.cface (hd xd) (hd (Gd.face xd)) := by
  by_cases b_xd : xd ∈ bGd
  · have h1 : Gd.cface (Gd.face xd) xd := Gd.cfaceC.1 (fconnect1 _ xd)
    obtain ⟨p, hp, hl⟩ := connect_iff_path.1 h1
    suffices key : ∀ (p : List Dd) (yd : Dd), path (frel Gd.face) yd p → last yd p = xd →
        G.cface (hd xd) (hd yd) from key p _ hp hl
    intro p
    induction p with
    | nil =>
      intro yd _ hl
      have hy : yd = xd := hl
      subst hy
      exact connect_refl _
    | cons zd p ih =>
      intro yd hp hl
      by_cases b_yd : yd ∈ bGd
      · have : yd = xd := Gd.scycle_cface hP.cycle_d yd b_yd xd b_xd
          (connect_iff_path.2 ⟨zd :: p, hp, hl⟩)
        subst this
        exact connect_refl _
      · have h2 := ih zd hp.2 hl
        have h3 : hd zd = G.face (hd yd) := by rw [← hP.hdF b_yd, hp.1]
        rw [h3] at h2
        exact connect_trans h2 (G.cfaceC.1 (fconnect1 _ _))
  · rw [hP.hdF b_xd]
    exact fconnect1 _ _

omit [Finite Dr] in
/-- math-comp `patch_face_d'`. -/
theorem patch_face_d' (hP : G.Patch Gd Gr hd hr bGd bGr) {xd yd : Dd}
    (h : Gd.cface xd yd) : G.cface (hd xd) (hd yd) := by
  induction h with
  | refl => exact connect_refl _
  | tail _ hbc ih =>
    rw [← hbc]
    exact connect_trans ih (hP.cFhd _)

/-- math-comp `patch_face_r`. -/
theorem patch_face_r (hP : G.Patch Gd Gr hd hr bGd bGr) (xr yr : Dr) :
    Gr.cface xr yr ↔ G.cface (hr xr) (hr yr) := by
  constructor
  · intro h
    induction h with
    | refl => exact connect_refl _
    | tail hpath hbc ih =>
      rename_i b c
      subst hbc
      refine connect_trans ih ?_
      show G.cface (hr b) (hr (Gr.face b))
      by_cases b_fb : Gr.face b ∈ bGr
      · obtain ⟨xd, Dfxr, Dxd⟩ := hP.bGrP b_fb
        have e1 : hr b = G.edge (hd xd) := by rw [Dxd, ← hP.edge_r, Gr.faceK]
        have e2 : G.edge (hd xd) = G.edge (G.node (hd (Gd.face (Gd.edge xd)))) := by
          rw [← hP.node_d, Gd.edgeK]
        rw [← Dfxr, e1, e2, G.cface1, G.nodeK]
        exact hP.patch_face_d' (Gd.cfaceC.1 (fconnect1 _ _))
      · rw [hP.hrF b_fb]
        exact fconnect1 _ _
  · intro h
    obtain ⟨p, hp, hl⟩ := connect_iff_path.1 h
    -- math-comp's invariant: either `x = hr xr`, or `x` lies in the disk, in the face of some
    -- `yd` glued to `hr xr` (`cFdr x xr`).
    suffices key : ∀ (p : List D) (x : D) (xr : Dr), path (frel G.face) x p →
        last x p = hr yr → (x ∈ Set.range hr → x = hr xr) →
        (x ∉ Set.range hr → ∃ xd, x = hd xd ∧ ∃ yd, hd yd = hr xr ∧ Gd.cface yd xd) →
        Gr.cface xr yr from
      key p _ xr hp hl (fun _ => rfl) (fun h => absurd ⟨xr, rfl⟩ h)
    intro p
    induction p with
    | nil =>
      intro x xr _ hl h1 _
      have hx : x = hr xr := h1 ⟨yr, hl.symm⟩
      have : yr = xr := hP.injr (hl.symm.trans hx)
      subst this
      exact connect_refl _
    | cons z p ih =>
      intro x xr hp hl h1 h2
      obtain ⟨Dz, zFp⟩ := hp
      by_cases hx : x ∈ Set.range hr
      · have Dx : x = hr xr := h1 hx
        subst Dx
        refine (Gr.cface1 xr yr).2 (ih z (Gr.face xr) zFp hl ?_ ?_)
        · intro fxrP
          rw [← Dz]
          by_cases b_fxr : Gr.face xr ∈ bGr
          · obtain ⟨xd, Dfxr, Dxd⟩ := hP.bGrP b_fxr
            have e1 : hr xr = G.edge (hd xd) := by rw [Dxd, ← hP.edge_r, Gr.faceK]
            have e2 : G.face (G.edge (hd xd)) = hd (Gd.face (Gd.edge xd)) := by
              conv_lhs => rw [← Gd.edgeK xd]
              rw [hP.node_d, G.nodeK]
            rw [e1, e2, ← Dfxr]
            congr 1
            refine Gd.scycle_cface hP.cycle_d _ ?_ _ ?_ (Gd.cfaceC.1 (fconnect1 _ _))
            · rw [← hP.EbGdr, e2.symm, ← e1, Dz]
              exact fxrP
            · rw [← hP.EbGdr, Dfxr]
              exact ⟨_, rfl⟩
          · exact (hP.hrF b_fxr).symm
        · intro fxrP
          obtain ⟨xd, Dxd⟩ := (hP.EhdUr z).resolve_right fxrP
          refine ⟨xd, Dxd.symm, Gd.edge (Gd.node xd), ?_, ?_⟩
          · rw [hP.hdErN, hP.node_d, Dxd, ← Dz]
            conv_lhs => rw [← Gr.faceK xr]
            rw [hP.edge_r, G.edgeK]
          · have := fconnect1 Gd.face (Gd.edge (Gd.node xd))
            rwa [Gd.nodeK] at this
      · obtain ⟨xd, Dxd, yd, Dyd, ydFxd⟩ := h2 hx
        subst Dxd
        have b'xd : xd ∉ bGd := fun h => hx ((hP.EbGdr xd).2 h)
        have Dz' : z = hd (Gd.face xd) := by rw [hP.hdF b'xd]; exact Dz.symm
        subst Dz'
        have ydFfxd : Gd.cface yd (Gd.face xd) := (Gd.cface1r _ _).1 ydFxd
        refine ih _ xr zFp hl ?_ ?_
        · intro hz
          have b_fxd : Gd.face xd ∈ bGd := (hP.EbGdr _).1 hz
          have b_yd : yd ∈ bGd := (hP.EbGdr yd).1 ⟨xr, Dyd.symm⟩
          rw [← Dyd, Gd.scycle_cface hP.cycle_d yd b_yd _ b_fxd ydFfxd]
        · intro _
          exact ⟨Gd.face xd, rfl, yd, Dyd, ydFfxd⟩

/-- math-comp `patch_bridgeless`. -/
theorem patch_bridgeless (hP : G.Patch Gd Gr hd hr bGd bGr) (hG : G.Bridgeless) :
    Gd.Bridgeless ∧ Gr.Bridgeless := by
  constructor
  · rintro ⟨xd, xFex⟩
    apply hG ⟨hd xd, ?_⟩
    have e : G.edge (hd xd) = G.edge (G.node (hd (Gd.face (Gd.edge xd)))) := by
      rw [← hP.node_d, Gd.edgeK]
    rw [e, G.cface1r, G.nodeK]
    exact hP.patch_face_d' ((Gd.cface1r _ _).1 xFex)
  · rintro ⟨xr, xFex⟩
    exact hG ⟨hr xr, by rw [← hP.edge_r, ← hP.patch_face_r]; exact xFex⟩

/-- math-comp `bridgeless_patch`. -/
theorem bridgeless_patch (hP : G.Patch Gd Gr hd hr bGd bGr) (hGd : Gd.Bridgeless)
    (hGr : Gr.Bridgeless) (hc : Gd.Chordless bGd) : G.Bridgeless := by
  classical
  rintro ⟨x, xFex⟩
  by_cases hx : x ∈ Set.range hr
  · obtain ⟨xr, rfl⟩ := hx
    exact hGr ⟨xr, by rw [hP.patch_face_r, hP.edge_r]; exact xFex⟩
  · obtain ⟨xd, rfl⟩ := (hP.EhdUr x).resolve_right hx
    have b'xd : xd ∉ bGd := fun h => hx ((hP.EbGdr xd).2 h)
    rw [← hP.edge_d xd b'xd] at xFex
    by_cases out_x : hd xd ∈ G.outer hr
    · have out_ex : hd (Gd.edge xd) ∈ G.outer hr :=
        ((closed_outer G hr).connect_iff xFex).1 out_x
      obtain ⟨yd, b_yd, xFyd⟩ := (hP.outer_hd xd).1 out_x
      obtain ⟨zd, b_zd, exFzd⟩ := (hP.outer_hd _).1 out_ex
      have hadj : Gd.adj yd zd := Gd.adjP.2 ⟨xd, Gd.cfaceC.1 xFyd, exFzd⟩
      obtain ⟨yr, Dyr, Dnyr⟩ := hP.bGdP b_yd
      have hyz : G.cface (hd yd) (hd zd) :=
        connect_trans (connect_trans (hP.patch_face_d' (Gd.cfaceC.1 xFyd)) xFex)
          (hP.patch_face_d' exFzd)
      rcases (Gd.chordless_iff.1 hc) yd b_yd zd b_zd hadj with Dzd | Dzd
      · have hez : Gd.edge zd = yd := by rw [Dzd]; exact prev_cycle hP.cycle_d.1 b_yd
        have e1 : hd zd = hr (Gr.node (Gr.node yr)) := by
          rw [← hP.hdErN, hez]
          exact Dnyr
        refine hGr ⟨Gr.node (Gr.node yr), ?_⟩
        rw [Gr.cface1r, Gr.nodeK, hP.patch_face_r, ← e1, ← Dnyr]
        exact G.cfaceC.1 hyz
      · have hez : Gd.edge yd = zd := by rw [Dzd]; exact next_cycle hP.cycle_d.1 b_yd
        refine hGr ⟨Gr.node yr, ?_⟩
        rw [Gr.cface1r, Gr.nodeK, hP.patch_face_r, ← Dnyr, ← Dyr, hez]
        exact hyz
    · exact hGd ⟨xd, (hP.patch_face_d out_x).2 xFex⟩

/-- The functor part of math-comp's local `oaGr`: `hr` preserves and reflects components. -/
private theorem gcomp_hr (hP : G.Patch Gd Gr hd hr bGd bGr) (xr zr : Dr) :
    Gr.gcomp xr zr ↔ G.gcomp (hr xr) (hr zr) := by
  have hGFr : ∀ zr, G.gcomp (hr zr) (hr (Gr.face zr)) := fun zr =>
    G.gcomp_of_cface ((hP.patch_face_r _ _).1 (fconnect1 _ _))
  constructor
  · intro h
    rw [← Gr.clink_glink] at h
    induction h with
    | refl => exact connect_refl _
    | tail hpath hbc ih =>
      rename_i b c
      refine connect_trans ih ?_
      rcases hbc with Dxr | rfl
      · subst Dxr
        have e : hr c = hr (Gr.face (Gr.edge (Gr.node c))) := by rw [Gr.nodeK]
        rw [e]
        refine connect_trans (connect_of_rel (G.glinkE _)) ?_
        rw [← hP.edge_r]
        exact hGFr _
      · exact hGFr _
  · intro h
    rw [← G.clink_glink] at h
    obtain ⟨p, hp, hl⟩ := connect_iff_path.1 h
    -- math-comp's invariant: either `x = hr xr`, or `x` lies in the disk and `xr` on the border.
    suffices key : ∀ (p : List D) (x : D) (xr : Dr), path G.clink x p → last x p = hr zr →
        (x ∈ Set.range hr → x = hr xr) → (x ∉ Set.range hr → xr ∈ bGr) → Gr.gcomp xr zr from
      key p _ xr hp hl (fun _ => rfl) (fun h => absurd ⟨xr, rfl⟩ h)
    intro p
    induction p with
    | nil =>
      intro x xr _ hl h1 _
      have hx : x = hr xr := h1 ⟨zr, hl.symm⟩
      have : zr = xr := hP.injr (hl.symm.trans hx)
      subst this
      exact connect_refl _
    | cons y p ih =>
      intro x xr hp hl h1 h2
      obtain ⟨xCy, yCp⟩ := hp
      have yGzr : ∀ yr', (y ∈ Set.range hr → y = hr yr') → (y ∉ Set.range hr → yr' ∈ bGr) →
          Gr.gcomp yr' zr := fun yr' => ih y yr' yCp hl
      by_cases hy : y ∈ Set.range hd
      · obtain ⟨yd, rfl⟩ := hy
        have bGzr : ∀ tr ∈ bGr, Gr.gcomp tr zr := by
          intro tr b_tr
          by_cases hy' : hd yd ∈ Set.range hr
          · obtain ⟨yr, Dy⟩ := hy'
            have b_yr : yr ∈ bGr := (hP.EbGrd yr).1 ⟨yd, Dy.symm⟩
            refine connect_trans (Gr.gcomp_of_cnode ((hP.EbGrN b_tr yr).2 b_yr)) ?_
            exact yGzr yr (fun _ => Dy.symm) (fun h => absurd ⟨yr, Dy⟩ h)
          · exact yGzr tr (fun h => absurd h hy') (fun _ => b_tr)
        by_cases hx : x ∈ Set.range hr
        · have Dx : x = hr xr := h1 hx
          subst Dx
          rcases xCy with xr_ny | fxr_y
          · apply bGzr
            rw [← hP.EbGrd, xr_ny, ← hP.node_d]
            exact ⟨_, rfl⟩
          · refine connect_trans (connect_of_rel (Gr.glinkF xr)) (bGzr _ ?_)
            by_contra b'fxr
            apply b'fxr
            rw [← hP.EbGrd, hP.hrF b'fxr, fxr_y]
            exact ⟨_, rfl⟩
        · exact bGzr xr (h2 hx)
      · obtain ⟨yr, rfl⟩ := (hP.EhdUr y).resolve_left hy
        have b'yr : yr ∉ bGr := fun h => hy ((hP.EbGrd yr).2 h)
        refine connect_trans ?_ (yGzr yr (fun _ => rfl) (fun h => absurd ⟨yr, rfl⟩ h))
        show Gr.gcomp xr yr
        rw [← Gr.clink_glink]
        refine connect_of_rel ?_
        rcases xCy with xny | fxy
        · rw [← hP.node_r _ b'yr] at xny
          have hx := h1 ⟨_, xny.symm⟩
          rw [xny] at hx
          rw [← hP.injr hx]
          exact Gr.clinkN yr
        · have ex : x = hr (Gr.edge (Gr.node yr)) := by
            rw [hP.edge_r, hP.node_r _ b'yr]
            exact (G.face_eq_iff).1 fxy
          have hx := h1 ⟨_, ex.symm⟩
          rw [ex] at hx
          rw [← hP.injr hx]
          exact Or.inr (Gr.nodeK yr)

/-- math-comp local `oaGr`: the remainder map has as many components as the `glink` closure
of the range of `hr` in `G` (math-comp local `a`). -/
private theorem oaGr (hP : G.Patch Gd Gr hd hr bGd bGr) :
    nComp Gr.glink Set.univ = nComp G.glink (closure G.glink (Set.range hr)) := by
  rw [nComp_adjunction_closed G.glinkC Gr.glinkC hr (closure_closed G.glinkC _)]
  · congr 1
    ext xr
    simp only [Set.mem_univ, Set.mem_preimage, true_iff]
    exact subset_closure _ ⟨xr, rfl⟩
  · rintro x ⟨_, ⟨yr, rfl⟩, hxy⟩
    exact ⟨yr, hxy⟩
  · intro xr zr _ _
    exact hP.gcomp_hr xr zr

/-- math-comp `patch_connected_r`. -/
theorem patch_connected_r (hP : G.Patch Gd Gr hd hr bGd bGr) (hG : G.Connected) (xr : Dr) :
    Gr.Connected := by
  unfold Connected
  rw [hP.oaGr]
  have : closure G.glink (Set.range hr) = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true]
    exact ⟨hr xr, ⟨xr, rfl⟩,
      connect_of_nComp_eq_one G.glinkC hG (Set.mem_univ _) (Set.mem_univ _)⟩
  rw [this]
  exact hG

/-- math-comp `patch_fcard_face_r`. -/
theorem patch_fcard_face_r (hP : G.Patch Gd Gr hd hr bGd bGr) :
    fcard Gr.face Set.univ = fcard G.face (G.outer hr) := by
  unfold fcard
  rw [nComp_adjunction_closed G.cface_sym Gr.cface_sym hr (closed_outer G hr)]
  · congr 1
    ext xr
    simp only [Set.mem_univ, Set.mem_preimage, true_iff]
    exact subset_closure _ ⟨xr, rfl⟩
  · rintro x ⟨_, ⟨yr, rfl⟩, hxy⟩
    exact ⟨yr, hxy⟩
  · intro x' y' _ _
    exact hP.patch_face_r x' y'

end Patch

end PatchLemmas

/-! ### Genus and planarity of patched maps -/

section PatchGenus

variable {D : Type u} {Dd : Type v} {Dr : Type w} {G : Hypermap D} {Gd : Hypermap Dd}
  {Gr : Hypermap Dr} {hd : Dd → D} {hr : Dr → D} {bGd : List Dd} {bGr : List Dr}
  [Fintype D] [Fintype Dd] [Fintype Dr]

namespace Patch

/-- math-comp `genus_patch`. -/
theorem genus_patch (hP : G.Patch Gd Gr hd hr bGd bGr) : G.genus = Gd.genus + Gr.genus := by
  classical
  -- `b` is math-comp's `~~ eb`, with `eb := nilp bG`.
  obtain ⟨b, hb⟩ : ∃ b : ℕ, b = if bGd = [] then 0 else 1 := ⟨_, rfl⟩
  have hlen : bGr.length = bGd.length := by
    have := congrArg List.length hP.map_ring_r
    simpa using this
  have hbr : bGr = [] ↔ bGd = [] := by
    rw [← List.length_eq_zero_iff, ← List.length_eq_zero_iff, hlen]
  set a := closure G.glink (Set.range hr) with ha
  have clGa : Closed G.glink a := closure_closed G.glinkC _
  -- the three counts of `Gd`
  have oGdE : fcard Gd.edge Set.univ = b + fcard G.edge (Set.range hr)ᶜ := by
    unfold fcard
    rw [nComp_compl hP.clEbGd]
    congr 1
    · by_cases h0 : bGd = []
      · simp only [h0, List.not_mem_nil, Set.ofPred_false, nComp_empty, hb, ite_true]
      · obtain ⟨xd, hxd⟩ := List.exists_mem_of_ne_nil bGd h0
        have : {x | x ∈ bGd} = comp (frel Gd.edge) xd :=
          Set.ext fun y => (hP.EbGdE hxd y).symm
        rw [this, nComp_comp Gd.cedge_sym, hb, ite_eq_right h0]
    · rw [nComp_adjunction G.cedge_sym Gd.cedge_sym hd (a := (Set.range hr)ᶜ)]
      · congr 1
        ext xd
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage, hP.EbGdr]
      · intro x hx
        exact (hP.EhdUr x).resolve_right hx
      · intro x' y' hx' _
        refine connect_iff_of_base hP.injd (fun x y h hx => (hP.closed_Gr.compl x y h).1 hx)
          (fun x hx => (hP.EhdUr x).resolve_right hx) (fun x' y' hx' => ?_) hx'
        have b'x : x' ∉ bGd := fun hb' => hx' ((hP.EbGdr x').2 hb')
        show G.edge (hd x') = hd y' ↔ Gd.edge x' = y'
        rw [← hP.edge_d _ b'x, hP.injd.eq_iff]
  have oGdF : fcard Gd.face Set.univ = (bGd.map hd).length + fcard G.face (G.outer hr)ᶜ := by
    rw [hP.patch_fcard_face_d]
    congr 1
    unfold fcard
    rw [nComp_adjunction G.cface_sym Gd.cface_sym hd hP.adj_hd.1
      (fun x' y' hx' _ => hP.patch_face_d hx')]
    congr 1
    ext xd
    simp only [Set.mem_compl_iff, Set.mem_preimage, hP.outer_hd]
  have oGdN : fcard Gd.node Set.univ = fcard G.node (Set.range hd) := by
    unfold fcard
    rw [nComp_adjunction G.cnode_sym Gd.cnode_sym hd (a := Set.range hd) subset_rfl]
    · congr 1
      ext xd
      simp
    · intro x' y' hx' _
      refine connect_iff_of_base hP.injd (fun x y h hx => (hP.closed_Gd x y h).1 hx) subset_rfl
        (fun x' y' _ => ?_) hx'
      show G.node (hd x') = hd y' ↔ Gd.node x' = y'
      rw [← hP.node_d, hP.injd.eq_iff]
  -- the component count of `Gd`
  have oGdG : nComp Gd.glink Set.univ = b + nComp G.glink aᶜ := by
    have hdG : ∀ xd yd, xd ∉ bGd → (G.glink (hd xd) (hd yd) ↔ Gd.glink xd yd) := by
      intro xd yd b'xd
      simp only [glink]
      rw [← hP.edge_d _ b'xd, ← hP.node_d, ← hP.hdF b'xd, hP.injd.eq_iff, hP.injd.eq_iff,
        hP.injd.eq_iff]
    -- the points of `G` linked to `hd yd`, for `yd` off the border, are images of `hd`
    have hdG' : ∀ yd y, yd ∉ bGd → G.glink (hd yd) y →
        ∃ yd', y = hd yd' ∧ Gd.glink yd yd' := by
      intro yd y b'yd hy
      rcases hy with rfl | rfl | rfl
      · exact ⟨_, (hP.edge_d _ b'yd).symm, Gd.glinkE yd⟩
      · exact ⟨_, (hP.node_d _).symm, Gd.glinkN yd⟩
      · exact ⟨_, (hP.hdF b'yd).symm, Gd.glinkF yd⟩
    -- the preimage of `a` is empty or a single component
    have hpre : Closed Gd.glink (hd ⁻¹' a) ∧ nComp Gd.glink (hd ⁻¹' a) = b := by
      by_cases h0 : bGd = []
      · have hempty : hd ⁻¹' a = ∅ := by
          ext xd
          simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
          rintro ⟨_, ⟨yr, rfl⟩, hxy⟩
          have fwd : ∀ x y, G.glink x y → x ∈ Set.range hd → y ∈ Set.range hd := by
            rintro x y hxy ⟨xd', rfl⟩
            have b'xd' : xd' ∉ bGd := by rw [h0]; exact List.not_mem_nil
            obtain ⟨yd', rfl, -⟩ := hdG' xd' y b'xd' hxy
            exact ⟨yd', rfl⟩
          have h1 : hr yr ∈ Set.range hd := mem_of_connect_of_forward fwd hxy ⟨xd, rfl⟩
          have h2 := (hP.EhdIr (hr yr)).1 ⟨h1, ⟨yr, rfl⟩⟩
          rw [h0] at h2
          exact List.not_mem_nil h2
        rw [hempty, hb, ite_eq_left h0]
        exact ⟨fun x y _ => ⟨fun h => h.elim, fun h => h.elim⟩, nComp_empty⟩
      · obtain ⟨xd, b_xd⟩ := List.exists_mem_of_ne_nil bGd h0
        have hcomp : hd ⁻¹' a = comp Gd.glink xd := by
          ext yd
          simp only [Set.mem_preimage, mem_comp]
          constructor
          · rintro ⟨_, ⟨zr, rfl⟩, hyz⟩
            obtain ⟨p, hp, hl⟩ := connect_iff_path.1 hyz
            suffices key : ∀ (p : List D) (yd : Dd), path G.glink (hd yd) p →
                last (hd yd) p ∈ Set.range hr → Gd.gcomp xd yd from
              key p yd hp (hl ▸ ⟨zr, rfl⟩)
            intro p
            induction p with
            | nil =>
              intro yd _ hl
              exact Gd.gcomp_of_cedge ((hP.EbGdE b_xd yd).2 ((hP.EbGdr yd).1 hl))
            | cons y p ih =>
              intro yd hp hl
              by_cases b_yd : yd ∈ bGd
              · exact Gd.gcomp_of_cedge ((hP.EbGdE b_xd yd).2 b_yd)
              · obtain ⟨yd', rfl, hyy⟩ := hdG' yd y b_yd hp.1
                exact connect_trans (ih yd' hp.2 hl) (Gd.glinkC _ _ (connect_of_rel hyy))
          · intro hxy
            obtain ⟨p, hp, hl⟩ := connect_iff_path.1 (Gd.glinkC _ _ hxy)
            suffices key : ∀ (p : List Dd) (yd : Dd), path Gd.glink yd p → last yd p ∈ bGd →
                hd yd ∈ a from key p yd hp (hl ▸ b_xd)
            intro p
            induction p with
            | nil =>
              intro yd _ hl
              exact subset_closure _ ((hP.EbGdr yd).2 hl)
            | cons y p ih =>
              intro yd hp hl
              by_cases b_yd : yd ∈ bGd
              · exact subset_closure _ ((hP.EbGdr yd).2 b_yd)
              · exact (clGa _ _ ((hdG yd y b_yd).2 hp.1)).2 (ih y hp.2 hl)
        rw [hcomp, hb, ite_eq_right h0]
        exact ⟨closed_comp Gd.glinkC xd, nComp_comp Gd.glinkC xd⟩
    rw [nComp_compl hpre.1, hpre.2]
    congr 1
    rw [nComp_adjunction G.glinkC Gd.glinkC hd (a := aᶜ), Set.preimage_compl]
    · intro x hx
      rcases hP.EhdUr x with h | h
      · exact h
      · exact absurd (subset_closure _ h) hx
    · intro x' y' hx' _
      refine connect_iff_of_base hP.injd (fun x y h hx => (clGa.compl x y h).1 hx)
        (fun x hx => ?_) (fun x' y' hx' => ?_) hx'
      · rcases hP.EhdUr x with h | h
        · exact h
        · exact absurd (subset_closure _ h) hx
      · have b'x : x' ∉ bGd := fun hb' => hx' (subset_closure _ ((hP.EbGdr x').2 hb'))
        exact hdG x' y' b'x
  -- the three counts of `Gr`
  have oGrE : fcard Gr.edge Set.univ = fcard G.edge (Set.range hr) := by
    unfold fcard
    rw [nComp_adjunction G.cedge_sym Gr.cedge_sym hr (a := Set.range hr) subset_rfl]
    · congr 1
      ext xr
      simp
    · intro x' y' hx' _
      refine connect_iff_of_base hP.injr (fun x y h hx => (hP.closed_Gr x y h).1 hx) subset_rfl
        (fun x' y' _ => ?_) hx'
      show G.edge (hr x') = hr y' ↔ Gr.edge x' = y'
      rw [← hP.edge_r, hP.injr.eq_iff]
  have oGrN : fcard Gr.node Set.univ = b + fcard G.node (Set.range hd)ᶜ := by
    unfold fcard
    rw [nComp_compl hP.clNbGr]
    congr 1
    · by_cases h0 : bGd = []
      · have h0' : bGr = [] := hbr.2 h0
        simp only [h0', List.not_mem_nil, Set.ofPred_false, nComp_empty, hb, h0, ite_true]
      · have h0' : bGr ≠ [] := fun h => h0 (hbr.1 h)
        obtain ⟨xr, hxr⟩ := List.exists_mem_of_ne_nil bGr h0'
        have : {x | x ∈ bGr} = comp (frel Gr.node) xr :=
          Set.ext fun y => (hP.EbGrN hxr y).symm
        rw [this, nComp_comp Gr.cnode_sym, hb, ite_eq_right h0]
    · rw [nComp_adjunction G.cnode_sym Gr.cnode_sym hr (a := (Set.range hd)ᶜ)]
      · congr 1
        ext xr
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_preimage, hP.EbGrd]
      · intro x hx
        exact (hP.EhdUr x).resolve_left hx
      · intro x' y' hx' _
        refine connect_iff_of_base hP.injr (fun x y h hx => (hP.closed_Gd.compl x y h).1 hx)
          (fun x hx => (hP.EhdUr x).resolve_left hx) (fun x' y' hx' => ?_) hx'
        have b'x : x' ∉ bGr := fun hb' => hx' ((hP.EbGrd x').2 hb')
        show G.node (hr x') = hr y' ↔ Gr.node x' = y'
        rw [← hP.node_r _ b'x, hP.injr.eq_iff]
  -- the splittings of the counts of `G`
  have hGa : nComp G.glink Set.univ = nComp G.glink a + nComp G.glink aᶜ := nComp_compl clGa
  have hGE : fcard G.edge Set.univ =
      fcard G.edge (Set.range hr) + fcard G.edge (Set.range hr)ᶜ :=
    nComp_compl hP.closed_Gr
  have hGN : fcard G.node Set.univ =
      fcard G.node (Set.range hd) + fcard G.node (Set.range hd)ᶜ :=
    nComp_compl hP.closed_Gd
  have hGF : fcard G.face Set.univ = fcard G.face (G.outer hr) + fcard G.face (G.outer hr)ᶜ :=
    nComp_compl (closed_outer G hr)
  have hoa : nComp Gr.glink Set.univ = nComp G.glink a := hP.oaGr
  have hFr := hP.patch_fcard_face_r
  have hcard := hP.card_patch
  have eGd := Gd.evenGenus
  have eGr := Gr.evenGenus
  unfold EvenGenus eulerLhs eulerRhs at eGd eGr
  have key : G.eulerLhs = 2 * (Gd.genus + Gr.genus) + G.eulerRhs := by
    unfold eulerLhs eulerRhs
    omega
  rw [show G.genus = (G.eulerLhs - G.eulerRhs) / 2 from rfl, key]
  omega

/-- math-comp `planar_patch`. -/
theorem planar_patch (hP : G.Patch Gd Gr hd hr bGd bGr) :
    G.Planar ↔ Gd.Planar ∧ Gr.Planar := by
  unfold Planar
  rw [hP.genus_patch]
  exact Nat.add_eq_zero_iff

end Patch

end PatchGenus

/-! ### Colorings of patched maps -/

section PatchColoring

variable {D : Type u} {Dd : Type v} {Dr : Type w} {G : Hypermap D} {Gd : Hypermap Dd}
  {Gr : Hypermap Dr} {hd : Dd → D} {hr : Dr → D} {bGd : List Dd} {bGr : List Dr}
  [Finite D] [Finite Dd] [Finite Dr]

namespace Patch

/-- math-comp `colorable_patch`. -/
theorem colorable_patch (hP : G.Patch Gd Gr hd hr bGd bGr) :
    G.FourColorable ↔ ∃ et, Gd.RingTrace bGd et ∧ Gr.RingTrace bGr (rot 1 et.reverse) := by
  constructor
  · rintro ⟨k, hk⟩
    have kdF : ∀ xd, k (hd (Gd.face xd)) = k (hd xd) := fun xd =>
      (G.coloring_cface hk (hP.patch_face_d' (fconnect1 _ xd))).symm
    refine ⟨trace ((bGd.map hd).map k), ⟨k ∘ hd, ⟨fun xd => ?_, kdF⟩, ?_⟩,
      ⟨k ∘ hr, ⟨fun xr => ?_, fun xr => ?_⟩, ?_⟩⟩
    · show k (hd (Gd.edge xd)) ≠ k (hd xd)
      rw [show hd xd = G.node (hd (Gd.face (Gd.edge xd))) by rw [← hP.node_d, Gd.edgeK],
        ← kdF (Gd.edge xd)]
      generalize hd (Gd.face (Gd.edge xd)) = y
      intro h
      apply hk.1 (G.node y)
      rw [← hk.2 (G.edge (G.node y)), G.nodeK]
      exact h
    · rw [List.map_map]
    · show k (hr (Gr.edge xr)) ≠ k (hr xr)
      rw [hP.edge_r]
      exact hk.1 _
    · show k (hr (Gr.face xr)) = k (hr xr)
      exact (G.coloring_cface hk ((hP.patch_face_r _ _).1 (fconnect1 _ xr))).symm
    · rw [← trace_rev, ← List.map_reverse, ← hP.map_ring_r, List.map_map]
  · rintro ⟨et, ⟨kd, hkd, Tkd⟩, ⟨kr, hkr, Tkr⟩⟩
    classical
    have Ekdr : trace (bGd.reverse.map kd) = trace (bGr.map kr) := by
      rw [List.map_reverse, trace_rev, ← Tkd, Tkr]
    -- shift the colors of `kd` so that they agree with `kr` on the border (math-comp `kd'`)
    obtain ⟨kd', hkd', Tkd'⟩ : ∃ kd' : Dd → Color,
        Gd.Coloring kd' ∧ bGd.reverse.map kd' = bGr.map kr := by
      rcases hrev : bGd.reverse with _ | ⟨xd, bGd'⟩
      · rw [hrev] at Ekdr
        refine ⟨kd, hkd, ?_⟩
        cases hbr : bGr with
        | nil => rfl
        | cons xr bGr' =>
          rw [hbr] at Ekdr
          simp [trace, ctrace] at Ekdr
      · rw [hrev] at Ekdr
        cases hbr : bGr with
        | nil =>
          rw [hbr] at Ekdr
          simp [trace, ctrace] at Ekdr
        | cons xr bGr' =>
          rw [hbr] at Ekdr
          refine ⟨addc (addc (kd xd) (kr xr)) ∘ kd, Gd.coloring_inj (addcI _) hkd, ?_⟩
          rw [← List.map_map]
          exact map_addc_of_trace_eq Ekdr
    -- the two colorings agree on the border (math-comp `eq_kdr`)
    have eq_kdr : ∀ xd xr, hd xd = hr xr → kd' xd = kr xr := by
      have h1 : bGd.reverse.map hd = bGr.map hr := by rw [List.map_reverse, hP.map_ring_r]
      intro xd xr hx
      have b_xr : xr ∈ bGr := (hP.EbGrd xr).1 ⟨xd, hx⟩
      exact map_eq_map_mem hP.injd h1 Tkd' xd xr b_xr hx
    -- the glued coloring (math-comp `k`, defined through `kP`)
    obtain ⟨k, k_hr, k_hd⟩ : ∃ k : D → Color,
        (∀ xr, k (hr xr) = kr xr) ∧ ∀ xd, k (hd xd) = kd' xd := by
      refine ⟨fun x => if h : ∃ xr, hr xr = x then kr h.choose
        else if h' : ∃ xd, hd xd = x then kd' h'.choose else Color0, fun xr => ?_, fun xd => ?_⟩
      · have h : ∃ xr', hr xr' = hr xr := ⟨xr, rfl⟩
        dsimp only
        rw [dite_eq_left h, hP.injr h.choose_spec]
      · dsimp only
        by_cases h : ∃ xr, hr xr = hd xd
        · rw [dite_eq_left h]
          exact (eq_kdr xd _ h.choose_spec.symm).symm
        · have h' : ∃ xd', hd xd' = hd xd := ⟨xd, rfl⟩
          rw [dite_eq_right h, dite_eq_left h', hP.injd h'.choose_spec]
    refine ⟨k, fun x => ?_, fun x => ?_⟩
    · by_cases hx : x ∈ Set.range hr
      · obtain ⟨xr, rfl⟩ := hx
        rw [← hP.edge_r, k_hr, k_hr]
        exact hkr.1 xr
      · obtain ⟨xd, rfl⟩ := (hP.EhdUr x).resolve_right hx
        have b'xd : xd ∉ bGd := fun h => hx ((hP.EbGdr xd).2 h)
        rw [← hP.edge_d _ b'xd, k_hd, k_hd]
        exact hkd'.1 xd
    · by_cases hx : x ∈ Set.range hr
      · obtain ⟨xr, rfl⟩ := hx
        rw [k_hr]
        by_cases hfx : G.face (hr xr) ∈ Set.range hr
        · obtain ⟨yr, Dy⟩ := hfx
          rw [← Dy, k_hr]
          have hF : G.cface (hr xr) (hr yr) := by rw [Dy]; exact fconnect1 _ _
          exact (Gr.coloring_cface hkr ((hP.patch_face_r xr yr).2 hF)).symm
        · obtain ⟨yd, Dy⟩ := (hP.EhdUr _).resolve_right hfx
          rw [← Dy, k_hd]
          have h1 : hd (Gd.face (Gd.edge (Gd.node yd))) = G.face (hr xr) := by
            rw [Gd.nodeK]
            exact Dy
          have h2 := eq_kdr _ _ ((hP.hdFrF _ _).1 h1)
          rw [← Gd.nodeK yd, hkd'.2, h2, hkr.2]
      · obtain ⟨xd, rfl⟩ := (hP.EhdUr x).resolve_right hx
        have b'xd : xd ∉ bGd := fun h => hx ((hP.EbGdr xd).2 h)
        rw [← hP.hdF b'xd, k_hd, k_hd]
        exact hkd'.2 xd

end Patch

end PatchColoring

/-! ### Patching disjoint components of a map along empty borders

This is used to show that a minimal counter example is connected. -/

section PatchGcomp

variable {D : Type u} (G : Hypermap D) (z : D)

/-- math-comp `gcompd_dart`: the darts of the connected component of `z`. -/
def GcompdDart : Type u := {x : D // G.gcomp z x}

/-- math-comp `Finite.on gcompd_dart`. -/
noncomputable instance [Fintype D] : Fintype (G.GcompdDart z) := by
  classical exact (inferInstance : Fintype {x : D // G.gcomp z x})

/-- math-comp `Finite.on gcompd_dart`, for `Finite` dart types. -/
instance [Finite D] : Finite (G.GcompdDart z) := inferInstanceAs (Finite {x : D // G.gcomp z x})

/-- The equality of `gcompd_dart` (math-comp `Finite.on gcompd_dart` provides an `eqType`). -/
instance [DecidableEq D] : DecidableEq (G.GcompdDart z) :=
  inferInstanceAs (DecidableEq {x : D // G.gcomp z x})

/-- math-comp `gcompd_edge_subproof`. -/
theorem gcompd_edge_subproof (u : G.GcompdDart z) : G.gcomp z (G.edge u.1) :=
  connect_trans u.2 (connect_of_rel (G.glinkE _))

/-- math-comp `gcompd_node_subproof`. -/
theorem gcompd_node_subproof (u : G.GcompdDart z) : G.gcomp z (G.node u.1) :=
  connect_trans u.2 (connect_of_rel (G.glinkN _))

/-- math-comp `gcompd_face_subproof`. -/
theorem gcompd_face_subproof (u : G.GcompdDart z) : G.gcomp z (G.face u.1) :=
  connect_trans u.2 (connect_of_rel (G.glinkF _))

/-- math-comp `gcompd_edge`. -/
def gcompdEdge (u : G.GcompdDart z) : G.GcompdDart z := ⟨G.edge u.1, G.gcompd_edge_subproof z u⟩

/-- math-comp `gcompd_node`. -/
def gcompdNode (u : G.GcompdDart z) : G.GcompdDart z := ⟨G.node u.1, G.gcompd_node_subproof z u⟩

/-- math-comp `gcompd_face`. -/
def gcompdFace (u : G.GcompdDart z) : G.GcompdDart z := ⟨G.face u.1, G.gcompd_face_subproof z u⟩

/-- math-comp `gcompd_subproof`: `cancel3 gcompd_edge gcompd_node gcompd_face`. -/
theorem gcompd_subproof (u : G.GcompdDart z) :
    G.gcompdNode z (G.gcompdFace z (G.gcompdEdge z u)) = u :=
  Subtype.ext (G.edgeK u.1)

/-- math-comp `gcomp_disk`: the "disk" hypermap whose darts are the connected component of
`z` in `G`. -/
def gcompDisk : Hypermap (G.GcompdDart z) where
  edge := G.gcompdEdge z
  node := G.gcompdNode z
  face := G.gcompdFace z
  edgeK := G.gcompd_subproof z

/-- math-comp `gcompd`: the projection in `G` of the darts of `gcompDisk z`. -/
def gcompd (u : G.GcompdDart z) : D := u.1

/-- math-comp `inj_gcompd`. -/
theorem inj_gcompd : Injective (G.gcompd z) := fun _ _ h => Subtype.ext h

/-- math-comp `codom_gcompd`. -/
theorem codom_gcompd (x : D) : x ∈ Set.range (G.gcompd z) ↔ G.gcomp z x :=
  ⟨by rintro ⟨u, rfl⟩; exact u.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

/-- math-comp `gcompr_dart`: the darts outside the connected component of `z`. -/
def GcomprDart : Type u := {x : D // ¬ G.gcomp z x}

/-- math-comp `Finite.on gcompr_dart`. -/
noncomputable instance [Fintype D] : Fintype (G.GcomprDart z) := by
  classical exact (inferInstance : Fintype {x : D // ¬ G.gcomp z x})

/-- math-comp `Finite.on gcompr_dart`, for `Finite` dart types. -/
instance [Finite D] : Finite (G.GcomprDart z) :=
  inferInstanceAs (Finite {x : D // ¬ G.gcomp z x})

/-- The equality of `gcompr_dart` (math-comp `Finite.on gcompr_dart` provides an `eqType`). -/
instance [DecidableEq D] : DecidableEq (G.GcomprDart z) :=
  inferInstanceAs (DecidableEq {x : D // ¬ G.gcomp z x})

variable [Finite D]

/-- math-comp `gcompr_edge_subproof`. -/
theorem gcompr_edge_subproof (v : G.GcomprDart z) : ¬ G.gcomp z (G.edge v.1) :=
  fun h => v.2 (connect_trans h (G.glinkC _ _ (connect_of_rel (G.glinkE _))))

/-- math-comp `gcompr_node_subproof`. -/
theorem gcompr_node_subproof (v : G.GcomprDart z) : ¬ G.gcomp z (G.node v.1) :=
  fun h => v.2 (connect_trans h (G.glinkC _ _ (connect_of_rel (G.glinkN _))))

/-- math-comp `gcompr_face_subproof`. -/
theorem gcompr_face_subproof (v : G.GcomprDart z) : ¬ G.gcomp z (G.face v.1) :=
  fun h => v.2 (connect_trans h (G.glinkC _ _ (connect_of_rel (G.glinkF _))))

/-- math-comp `gcompr_edge`. -/
def gcomprEdge (v : G.GcomprDart z) : G.GcomprDart z := ⟨G.edge v.1, G.gcompr_edge_subproof z v⟩

/-- math-comp `gcompr_node`. -/
def gcomprNode (v : G.GcomprDart z) : G.GcomprDart z := ⟨G.node v.1, G.gcompr_node_subproof z v⟩

/-- math-comp `gcompr_face`. -/
def gcomprFace (v : G.GcomprDart z) : G.GcomprDart z := ⟨G.face v.1, G.gcompr_face_subproof z v⟩

/-- math-comp `gcompr_subproof`: `cancel3 gcompr_edge gcompr_node gcompr_face`. -/
theorem gcompr_subproof (v : G.GcomprDart z) :
    G.gcomprNode z (G.gcomprFace z (G.gcomprEdge z v)) = v :=
  Subtype.ext (G.edgeK v.1)

/-- math-comp `gcomp_rem`: the "remainder" hypermap whose darts are the complement of the
connected component of `z` in `G`. -/
def gcompRem : Hypermap (G.GcomprDart z) where
  edge := G.gcomprEdge z
  node := G.gcomprNode z
  face := G.gcomprFace z
  edgeK := G.gcompr_subproof z

omit [Finite D] in
/-- math-comp `gcompr`: the projection in `G` of the darts of `gcompRem z`. -/
def gcompr (v : G.GcomprDart z) : D := v.1

omit [Finite D] in
/-- math-comp `inj_gcompr`. -/
theorem inj_gcompr : Injective (G.gcompr z) := fun _ _ h => Subtype.ext h

omit [Finite D] in
/-- math-comp `codom_gcompr`. -/
theorem codom_gcompr (x : D) : x ∈ Set.range (G.gcompr z) ↔ ¬ G.gcomp z x :=
  ⟨by rintro ⟨v, rfl⟩; exact v.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

/-- math-comp `patch_gcomp`. -/
theorem patch_gcomp :
    G.Patch (G.gcompDisk z) (G.gcompRem z) (G.gcompd z) (G.gcompr z) [] [] where
  injd := G.inj_gcompd z
  injr := G.inj_gcompr z
  cycle_d := ⟨trivial, List.nodup_nil⟩
  cycle_r := ⟨trivial, List.nodup_nil⟩
  map_ring_r := rfl
  codom_r x := by
    rw [G.codom_gcompr, G.codom_gcompd]
    simp
  edge_d _ _ := rfl
  node_d _ := rfl
  edge_r _ := rfl
  node_r _ _ := rfl

end PatchGcomp

/-! ### Minimal counter examples are connected -/

section MinimalCounterExampleConnected

variable {D : Type u} [Fintype D]

/-- math-comp `minimal_counter_example_is_connected`. -/
theorem minimal_counter_example_is_connected {G : Hypermap D}
    (cexG : G.MinimalCounterExample) : G.Connected := by
  classical
  by_contra cc'G
  apply cexG.noncolorable
  rcases isEmpty_or_nonempty D with hD | ⟨⟨z⟩⟩
  · exact ⟨fun _ => Color0, fun x => isEmptyElim x, fun x => isEmptyElim x⟩
  have ppG := G.patch_gcomp z
  have minG := cexG.minimal
  obtain ⟨planarGd, planarGr⟩ := ppG.planar_patch.1 cexG.planar
  obtain ⟨bridge'Gd, bridge'Gr⟩ := ppG.patch_bridgeless cexG.bridgeless
  obtain ⟨plainGd, plainGr⟩ := ppG.plain_patch.1 cexG.plain
  obtain ⟨cubicGd, cubicGr⟩ := ppG.cubic_patch.1 cexG.cubic
  have plainGd' : (G.gcompDisk z).Plain := fun x _ => plainGd (List.not_mem_nil (a := x))
  have cubicGr' : (G.gcompRem z).Cubic := fun x _ => cubicGr (List.not_mem_nil (a := x))
  refine ppG.colorable_patch.2 ⟨[], ?_, ?_⟩
  · have hlt : Fintype.card (G.GcompdDart z) < Fintype.card D := by
      have : ∃ y, ¬ G.gcomp z y := by
        by_contra! hall
        apply cc'G
        have huniv : (Set.univ : Set D) = comp G.glink z :=
          Set.ext fun y => ⟨fun _ => hall y, fun _ => trivial⟩
        unfold Connected
        rw [huniv, nComp_comp G.glinkC]
      obtain ⟨y, hy⟩ := this
      exact Fintype.card_lt_of_injective_of_notMem (G.gcompd z) (G.inj_gcompd z) (b := y)
        (fun h => hy ((G.codom_gcompd z y).1 h))
    obtain ⟨k, hk⟩ := minG (G.GcompdDart z) (G.gcompDisk z)
      ⟨⟨⟨planarGd, bridge'Gd⟩, plainGd'⟩, (G.gcompDisk z).cubic_precubic cubicGd⟩ hlt
    exact ⟨k, hk, rfl⟩
  · have hlt : Fintype.card (G.GcomprDart z) < Fintype.card D :=
      Fintype.card_lt_of_injective_of_notMem (G.gcompr z) (G.inj_gcompr z) (b := z)
        (fun h => (G.codom_gcompr z z).1 h (connect_refl z))
    obtain ⟨k, hk⟩ := minG (G.GcomprDart z) (G.gcompRem z)
      ⟨⟨⟨planarGr, bridge'Gr⟩, plainGr⟩, (G.gcompRem z).cubic_precubic cubicGr'⟩ hlt
    exact ⟨k, hk, rfl⟩

/-- math-comp coercion `minimal_counter_example_is_connected`, for dot notation. -/
theorem MinimalCounterExample.connected {G : Hypermap D} (cexG : G.MinimalCounterExample) :
    G.Connected :=
  minimal_counter_example_is_connected cexG

/-- math-comp `minimal_counter_example_is_planar_bridgeless_plain_connected` (a coercion in
math-comp). -/
theorem minimal_counter_example_is_planar_bridgeless_plain_connected {G : Hypermap D}
    (cexG : G.MinimalCounterExample) : G.PlanarBridgelessPlainConnected :=
  ⟨⟨⟨cexG.planar, cexG.bridgeless⟩, cexG.plain⟩, minimal_counter_example_is_connected cexG⟩

/-- math-comp coercion `minimal_counter_example_is_planar_bridgeless_plain_connected`, for dot
notation. -/
theorem MinimalCounterExample.toPlanarBridgelessPlainConnected {G : Hypermap D}
    (cexG : G.MinimalCounterExample) : G.PlanarBridgelessPlainConnected :=
  minimal_counter_example_is_planar_bridgeless_plain_connected cexG

/-- math-comp `minimal_counter_example_is_planar_plain_cubic_connected` (a coercion in
math-comp). -/
theorem minimal_counter_example_is_planar_plain_cubic_connected {G : Hypermap D}
    (cexG : G.MinimalCounterExample) : G.PlanarPlainCubicConnected :=
  ⟨⟨⟨cexG.plain, cexG.cubic⟩, minimal_counter_example_is_connected cexG⟩, cexG.planar⟩

/-- math-comp coercion `minimal_counter_example_is_planar_plain_cubic_connected`, for dot
notation. -/
theorem MinimalCounterExample.toPlanarPlainCubicConnected {G : Hypermap D}
    (cexG : G.MinimalCounterExample) : G.PlanarPlainCubicConnected :=
  minimal_counter_example_is_planar_plain_cubic_connected cexG

end MinimalCounterExampleConnected

end Hypermap

end FourColor
