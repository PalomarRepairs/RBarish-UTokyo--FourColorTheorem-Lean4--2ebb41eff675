/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Patch

/-!
# Cutting a planar map along a ring  (port of `snip.v`)

This file provides a construction for cutting a planar hypermap `G` along a ring `r` (i.e., a
simple R-cycle, `G.SCycle G.rlink r`) so as to yield two maps `Gd` and `Gr` that satisfy the
"patch" predicate. We could have carried out a more general division of the map `G` along a
contour (duplicate-free C-cycle), from which the ring `r` could be extracted as a subpath;
indeed we do construct such a contour inside the proof of our main lemma `diskE_edge`, which
establishes that the "inside" of the disk part is edge-closed. However for the proof of the
Four Color Theorem the ring `r` is a more natural parameter and the stronger assumption on `r`
(that it is face-simple, rather than part of a contour) lets us prove the other closure
properties without using the planarity of `G`. The construction is used in the preliminary
reducibility results, mainly Birkhoff's connectivity theorem.

Given `G : Hypermap D`, `r : List D`, `hG : G.Planar` and `hr : G.SCycle G.rlink r`:

* `G.dlink r x y`   : there is a C-link from `x ∉ r` to `y` (math-comp `dlink`).
* `G.dconnect r x y` : there is an internally `r`-disjoint C-path from `y` to `x` that starts
  with a (reverse) N-link, i.e., a `dlink` path from `finv node y` to `x` (math-comp `dconnect`).
* `G.diskN r`   : the darts inside the N-closed disk delimited by `r`, i.e., the `x` with
  `dconnect r x y` for some `y ∈ r`; `diskN r` contains `r` (math-comp `diskN`).
* `G.diskE r`   : the E-closed disk strictly delimited by `r`: `diskN r` minus `r`.
* `G.diskF r`   : the F-closed disk strictly delimited by `r`: `diskN r` minus `fband r`.
* `G.diskFC r`  : the darts strictly outside the F-closure of the disk: neither in `diskN r`
  nor in `fband r`.
* `G.snipDisk hG hr` : a "disk" planar hypermap, whose darts `G.SnipdDart r` are those of
  `diskN r` (math-comp `snip_disk planarG scycRr`).
* `G.snipdRing r` : the border E-cycle of `G.snipDisk hG hr` (math-comp `snipd_ring`).
* `G.snipd r u`   : the projection in `G` of `u : G.SnipdDart r` (math-comp `snipd`).
* `G.snipRem hG hr` : a "remainder" hypermap, whose darts `G.SniprDart r` are the darts of `G`
  on or outside `r`, including those not connected to `r` (math-comp `snip_rem`).
* `G.sniprRing r` : the border N-cycle of `G.snipRem hG hr` (math-comp `snipr_ring`).
* `G.snipr r u`   : the projection in `G` of `u : G.SniprDart r` (math-comp `snipr`).

We then have `G.snip_patch hG hr : G.Patch (G.snipDisk hG hr) (G.snipRem hG hr) (G.snipd r)
(G.snipr r) (G.snipdRing r) (G.sniprRing r)`, and both maps are planar (`planar_snipd`,
`planar_snipr`). The disks only depend on the extent of the ring (`diskN_rot`, ...).

## Coq → Lean names

| Coq | Lean |
|---|---|
| `dlink`, `dconnect`, `diskN`, `diskE`, `diskF`, `diskFC` | same names (`diskE`, `diskF`, `diskFC` are `Set` differences) |
| `diskN_node`, `diskN_E`, `diskF_face`, `diskFC_face`, `diskE_edge` | same names |
| section `Let ddart`, `Let rdart` | `SnipdDart r`, `SniprDart r` |
| `snipd_edge`, `snipd_face`, `snipr_node`, `snipr_face` | `snipdEdge`, `snipdFace`, `sniprNode`, `sniprFace` |
| `dedge_subproof`, `dface_subproof`, `dnode_subproof`, `snipd_subproof` | same names |
| section `Let dedge`, `dnode`, `dface` | `snipDiskEdge`, `snipDiskNode`, `snipDiskFace` |
| `redge_subproof`, `rnode_subproof`, `rface_subproof`, `snipr_subproof` | same names |
| section `Let redge`, `rnode`, `rface` | `snipRemEdge`, `snipRemNode`, `snipRemFace` |
| `snip_disk`, `snip_rem`, `snipd_ring`, `snipr_ring` | `snipDisk`, `snipRem`, `snipdRing`, `sniprRing` |
| `snipd`, `snipr`, `inj_snipd`, `inj_snipr`, `codom_snipd`, `codom_snipr` | same names |
| `map_snipd_ring`, `ucycle_snipd_ring`, `cface_snipd`, `simple_snipd_ring`, `scycle_snipd_ring` | same names |
| `map_snipr_ring`, `ucycle_snipr_ring`, `snip_patch`, `planar_snipd`, `planar_snipr` | same names |
| `diskN_rot`, `diskE_rot`, `diskF_rot`, `diskFC_rot` | same names |
| math-comp `preim_seq`, `map_preim` (`fintype.v`) | `preimSeq`, `map_preim` |

Lean-only helpers: `diskN_dlink` (`diskN r` is closed under `dlink` steps), `mem_diskN_of_mem`
(`diskN r` contains `r`), `diskE_of_fpath` (the first step of the proof of `diskE_edge`),
`mem_snipd_ring`, `mem_snipr_ring`, and the `rfl` lemmas `snipDisk_edge`, `snipDisk_node`,
`snipDisk_face`, `snipRem_edge`, `snipRem_node`, `snipRem_face`.

## Porting notes

* The section hypotheses `planarG : planar G` and `scycRr : scycle rlink r` are explicit
  arguments `hG : G.Planar` and `hr : G.SCycle G.rlink r` of the declarations that use them,
  with `r` then implicit (`G.diskE_edge hG hr`, `G.snipDisk hG hr`, `G.snip_patch hG hr`); the
  section `Let`s `cycRr`, `UrF`, `Ur` are `hr.1`, `hr.2` and `G.scycle_uniq hr`.
* The dart types `G.SnipdDart r = {x // x ∈ G.diskN r}` and `G.SniprDart r = {x // x ∉ G.diskE r}`
  do not depend on `hG`, `hr`, and neither do `snipd`, `snipr`, `snipdRing`, `sniprRing` and the
  lemmas `codom_*`, `map_*` (math-comp's `snipd_ring planarG scycRr` is `G.snipdRing r`). They
  have classical (noncomputable) `Fintype` instances, and `Finite`, `DecidableEq` instances.
* `dnode_subproof` needs neither hypothesis, and `dface_subproof`, `rnode_subproof` only need
  `hr` (not the planarity of `G`): `dface_subproof` is proved by a direct `dlink` step instead of
  going through `diskE_edge`.
* `fclosed f a` is `Closed (frel f) a`; `=i` between predicates is `↔` pointwise, or equality of
  sets for the rotation lemmas; `{mono snipd : u v / cface u v}` is
  `∀ u v, G.cface (snipd u) (snipd v) ↔ Gd.cface u v`; `codom f` is `Set.range f`.
* math-comp's `rot n0 r` is `r.rotate n0` (as in `FourColor.Geometry`); the rotation lemmas
  hold for every `n0`.
* math-comp's `preim_seq` picks preimages with `pick`; `preimSeq` uses `Classical.choose`. Since
  `snipd` and `snipr` are injective, `snipdRing` and `sniprRing` are nevertheless determined by
  `map_snipd_ring` and `map_snipr_ring`.
* The canonical structure `dconnect_app_pred` is a Coq device and is omitted.
* The math-comp lemmas on `next`/`prev` used here (`mem_next`, `mem_prev`, `prev_next`,
  `next_rev`, `next_map`, `prev_cycle`, `cycle_from_next`) are proved as private lemmas, as in
  `FourColor.Patch`.
-/

namespace FourColor

open Function

universe u

/-! ### Preimages of sequences (math-comp `preim_seq`) -/

section PreimSeq

variable {α β : Type*}

open Classical in
/-- math-comp `preim_seq f s`: a sequence of preimages by `f` of the items of `s`; the items of
`s` that have no preimage are skipped. The preimages are chosen with `Classical.choose` (math-comp
uses `pick`); when `f` is injective the result is unique (see `map_preim`). -/
noncomputable def preimSeq (f : α → β) : List β → List α
  | [] => []
  | y :: s => if h : ∃ x, f x = y then Classical.choose h :: preimSeq f s else preimSeq f s

/-- math-comp `map_preim`. -/
theorem map_preim {f : α → β} {s : List β} (hs : ∀ y ∈ s, y ∈ Set.range f) :
    (preimSeq f s).map f = s := by
  induction s with
  | nil => rfl
  | cons y s ih =>
    have hy : ∃ x, f x = y := hs y List.mem_cons_self
    rw [preimSeq, dite_eq_left hy, List.map_cons, Classical.choose_spec hy,
      ih fun z hz => hs z (List.mem_cons_of_mem _ hz)]

end PreimSeq

/-! ### Cyclic successor and predecessor: complements to `FourColor.Geometry`

These are the math-comp lemmas on `next`/`prev` used by `snip.v`. The same statements are
proved (as private lemmas) in `FourColor.Patch`; they are reproved here, through Mathlib's
`List.next`/`List.prev`. -/

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

/-- Helper for math-comp `cycle_from_next`. -/
private theorem path_from_nextAt {e : α → α → Prop} {y0 : α} :
    ∀ {y : α} {p : List α}, (y :: p).Nodup → (∀ x ∈ y :: p, e x (nextAt x y0 y p)) →
      path e y (p ++ [y0])
  | y, [], _, h => by
    have := h y List.mem_cons_self
    rw [nextAt, ite_eq_left rfl] at this
    exact ⟨this, trivial⟩
  | y, z :: p, hn, h => by
    have hy := h y List.mem_cons_self
    rw [nextAt, ite_eq_left rfl] at hy
    refine ⟨hy, path_from_nextAt (List.nodup_cons.1 hn).2 fun x hx => ?_⟩
    have hxy : x ≠ y := by
      rintro rfl
      exact (List.nodup_cons.1 hn).1 hx
    have := h x (List.mem_cons_of_mem _ hx)
    rwa [nextAt, ite_eq_right hxy] at this

/-- math-comp `cycle_from_next`: a duplicate-free sequence in which every item is `e`-related to
its successor is an `e`-cycle. -/
private theorem cycle_from_next {e : α → α → Prop} {p : List α} (hp : p.Nodup)
    (h : ∀ x ∈ p, e x (next p x)) : cycle e p := by
  cases p with
  | nil => trivial
  | cons y p => exact path_from_nextAt hp h

end NextPrev

namespace Hypermap

/-! ### The disk delimited by a ring -/

section Disk

variable {D : Type u} (G : Hypermap D) (r : List D)

/-- math-comp `dlink r x y`: there is a C-link from `x ∉ r` to `y`. -/
def dlink (x y : D) : Prop := x ∉ r ∧ G.clink x y

/-- math-comp `dconnect r x y`: there is an internally `r`-disjoint C-path from `y` to `x` that
starts with a (reverse) N-link, i.e., a `dlink` path from `finv node y = face (edge y)` to `x`. -/
def dconnect (x y : D) : Prop := connect (G.dlink r) (G.face (G.edge y)) x

/-- math-comp `diskN r`: the darts inside the N-closed disk delimited by `r`, i.e., the `x` such
that `dconnect r x y` for some `y ∈ r`. Note that `diskN r` contains `r` (`diskN_E`). -/
def diskN : Set D := {x | ∃ y ∈ r, G.dconnect r x y}

/-- math-comp `diskE r`: the darts inside the E-closed disk strictly delimited by `r`, that is,
in `diskN r` but not in `r` (math-comp `[predD diskN & r]`). -/
def diskE : Set D := G.diskN r \ {x | x ∈ r}

/-- math-comp `diskF r`: the darts inside the F-closed disk strictly delimited by `r`, that is,
in `diskN r` but not in `fband r` (math-comp `[predD diskN & fband r]`). -/
def diskF : Set D := G.diskN r \ G.fband r

/-- math-comp `diskFC r`: the darts strictly outside the F-closure of the disk, i.e., neither in
`diskN r` nor in `fband r` (math-comp `[predD [predC diskN] & fband r]`). -/
def diskFC : Set D := (G.diskN r)ᶜ \ G.fband r

/-- `diskN r` is closed under `dlink` steps (the one-step form of the definition). -/
theorem diskN_dlink {x y : D} (hx : x ∈ G.diskN r) (h : G.dlink r x y) : y ∈ G.diskN r := by
  obtain ⟨z, hz, hzx⟩ := hx
  exact ⟨z, hz, connect_trans hzx (connect_of_rel h)⟩

/-- A face path that avoids `r` and starts in `diskN r` stays in `diskE r` (the first step of
the proof of math-comp `diskE_edge`). -/
theorem diskE_of_fpath {x : D} {p : List D} (dNx : x ∈ G.diskN r) (xFp : fpath G.face x p)
    (r'p : ∀ t ∈ x :: p, t ∉ r) : last x p ∈ G.diskE r := by
  induction p generalizing x with
  | nil => exact ⟨dNx, r'p x List.mem_cons_self⟩
  | cons y p ih =>
    obtain ⟨Dy, yFp⟩ := xFp
    have dNy : y ∈ G.diskN r :=
      G.diskN_dlink r dNx ⟨r'p x List.mem_cons_self, Or.inr Dy⟩
    exact ih dNy yFp fun t ht => r'p t (List.mem_cons_of_mem _ ht)

variable [Finite D]

/-- math-comp `diskN_node`. -/
theorem diskN_node : Closed (frel G.node) (G.diskN r) := by
  -- `diskN r` is closed under `finv node = face ∘ edge`
  have hN' : ∀ x, x ∈ G.diskN r → G.face (G.edge x) ∈ G.diskN r := by
    intro x dNx
    by_cases rx : x ∈ r
    · exact ⟨x, rx, connect_refl _⟩
    · exact G.diskN_dlink r dNx ⟨rx, Or.inl (G.edgeK x).symm⟩
  have hinj : Injective fun x => G.face (G.edge x) := fun a b h => G.edgeI (G.faceI h)
  have hcl : Closed (frel fun x => G.face (G.edge x)) (G.diskN r) :=
    Closed.of_forward (fconnect_sym hinj) (by rintro x _ rfl dNx; exact hN' x dNx)
  rintro x _ rfl
  exact (hcl (G.node x) x (G.nodeK x)).symm

/-- `diskN r` contains `r` (the non-trivial half of math-comp `diskN_E`). -/
theorem mem_diskN_of_mem {x : D} (hx : x ∈ r) : x ∈ G.diskN r :=
  ((G.diskN_node r) (G.face (G.edge x)) x (G.edgeK x)).1 ⟨x, hx, connect_refl _⟩

/-- math-comp `diskN_E`. -/
theorem diskN_E (x : D) : x ∈ G.diskN r ↔ x ∈ r ∨ x ∈ G.diskE r := by
  constructor
  · intro dNx
    by_cases rx : x ∈ r
    · exact Or.inl rx
    · exact Or.inr ⟨dNx, rx⟩
  · rintro (rx | dEx)
    · exact G.mem_diskN_of_mem r rx
    · exact dEx.1

/-- math-comp `diskF_face`. -/
theorem diskF_face : Closed (frel G.face) (G.diskF r) := by
  apply Closed.of_forward G.cface_sym
  rintro x _ rfl ⟨dNx, F'x⟩
  refine ⟨?_, fun h => F'x (((G.fbandF r) x _ rfl).2 h)⟩
  have r'x : x ∉ r := fun h => F'x (G.ring_fband r x h)
  exact G.diskN_dlink r dNx ⟨r'x, G.clinkF x⟩

/-- math-comp `diskFC_face`. -/
theorem diskFC_face : Closed (frel G.face) (G.diskFC r) := by
  intro x y xFy
  have hF := G.diskF_face r x y xFy
  have hb := G.fbandF r x y xFy
  show (x ∉ G.diskN r ∧ x ∉ G.fband r) ↔ (y ∉ G.diskN r ∧ y ∉ G.fband r)
  change (x ∈ G.diskN r ∧ x ∉ G.fband r) ↔ (y ∈ G.diskN r ∧ y ∉ G.fband r) at hF
  by_cases bx : x ∈ G.fband r
  · have by' := hb.1 bx
    exact ⟨fun h => absurd bx h.2, fun h => absurd by' h.2⟩
  · have by' : y ∉ G.fband r := fun h => bx (hb.2 h)
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨fun h => h1 (hF.2 ⟨h, by'⟩).1, by'⟩
    · rintro ⟨h1, -⟩
      exact ⟨fun h => h1 (hF.1 ⟨h, bx⟩).1, bx⟩

end Disk

/-! ### The disk of a ring in a planar map is edge-closed -/

section DiskEdge

variable {D : Type u} [Fintype D] (G : Hypermap D) {r : List D}

/-- math-comp `diskE_edge`: in a planar map, the strict disk `diskE r` delimited by a ring `r`
(a simple R-cycle) is closed under `edge`. -/
theorem diskE_edge (hG : G.Planar) (hr : G.SCycle G.rlink r) :
    Closed (frel G.edge) (G.diskE r) := by
  classical
  have hJ : G.Jordan := (G.planar_iff_jordan).1 hG
  have Ur : r.Nodup := G.scycle_uniq hr
  have rF : ∀ x ∈ r, ∀ y ∈ r, G.cface x y → x = y := G.scycle_cface hr
  -- math-comp local `cFpL`: the darts of a face path lie in the face of its last dart
  have cFpL : ∀ (t : D) (c : List D), fpath G.face t c → ∀ u ∈ t :: c, G.cface u (last t c) :=
    fun t c tFc u hu =>
      connect_trans (G.cfaceC.1 (path_connect tFc hu)) (path_connect tFc (mem_last t c))
  -- math-comp local `rclink`: follow `face`, except on the ring where `face ∘ edge` is followed
  obtain ⟨rcl, hrcl⟩ : ∃ f : D → D, ∀ t, f t = G.face (if t ∈ r then G.edge t else t) :=
    ⟨_, fun _ => rfl⟩
  have rclR : ∀ t ∈ r, rcl t = G.face (G.edge t) := fun t ht => by rw [hrcl, ite_eq_left ht]
  have rclN : ∀ t, t ∉ r → rcl t = G.face t := fun t ht => by rw [hrcl, ite_eq_right ht]
  -- math-comp local `sFCr`: a duplicate-free face path ending on the ring is an `rclink` path
  have sFCr : ∀ (t : D) (c : List D), (t :: c).Nodup → last t c ∈ r → fpath G.face t c →
      path (frel rcl) t c := by
    intro t c Uc Lc tFc
    have hb : ∀ u ∈ belast t c, u ∉ r := by
      intro u hu ru
      have hUc := Uc
      rw [lastI t c, List.nodup_append] at hUc
      exact hUc.2.2 u hu _ List.mem_cons_self (rF u ru _ Lc (cFpL t c tFc u (mem_belast hu)))
    have key : ∀ (c : List D) (t : D), (∀ u ∈ belast t c, u ∉ r) → fpath G.face t c →
        path (frel rcl) t c := by
      intro c
      induction c with
      | nil => intro _ _ _; trivial
      | cons w c ih =>
        intro t hb tFc
        rw [belast_cons] at hb
        exact ⟨show rcl t = w by rw [rclN t (hb t List.mem_cons_self)]; exact tFc.1,
          ih w (fun u hu => hb u (List.mem_cons_of_mem _ hu)) tFc.2⟩
    exact key c t hb tFc
  -- the recursive part of the construction of the contour `c` (see below)
  have claim2 : ∀ (r1 : List D) (y : D), y ∈ r → (∀ t ∈ r1, t ∈ r) → path G.rlink y r1 →
      r1.Nodup → ∃ c2, path (frel rcl) y c2 ∧ c2.Nodup ∧ last y c2 = last y r1 ∧
        (∀ t ∈ r1, t ∈ c2) ∧ ∀ t ∈ G.fband c2, t ∈ G.fband r1 := by
    intro r1
    induction r1 with
    | nil =>
      intro y _ _ _ _
      exact ⟨[], trivial, List.nodup_nil, rfl, fun t ht => absurd ht List.not_mem_nil,
        fun t ht => ht⟩
    | cons w r1 ih =>
      intro y ry sr1r yRr1 Ur1
      have rw' : w ∈ r := sr1r w List.mem_cons_self
      have sr1r' : ∀ t ∈ r1, t ∈ r := fun t ht => sr1r t (List.mem_cons_of_mem _ ht)
      obtain ⟨yRw, wRr1⟩ := yRr1
      obtain ⟨r1'w, Ur1'⟩ := List.nodup_cons.1 Ur1
      obtain ⟨c2, wRc2, Uc2, Lc2, sr1c2, sc2r1⟩ := ih w rw' sr1r' wRr1 Ur1'
      obtain ⟨c0, yFc0, Lc0⟩ := connect_iff_path.1 ((G.cface1 _ _).1 yRw)
      obtain ⟨c1, yFc1, Uc1, -, Lc1⟩ := shortenP yFc0
      rw [Lc0] at Lc1
      have sc1Fw : ∀ t ∈ G.face (G.edge y) :: c1, G.cface t w := fun t ht => by
        rw [← Lc1]; exact cFpL _ _ yFc1 t ht
      refine ⟨(G.face (G.edge y) :: c1) ++ c2, ?_, ?_, ?_, ?_, ?_⟩
      · rw [path_append, last_cons, Lc1]
        exact ⟨⟨rclR y ry, sFCr _ _ Uc1 (by rw [Lc1]; exact rw') yFc1⟩, wRc2⟩
      · rw [List.nodup_append]
        refine ⟨Uc1, Uc2, fun a ha b hb hab => ?_⟩
        rw [← hab] at hb
        obtain ⟨u, r1u, aFu⟩ := sc2r1 a (G.ring_fband c2 a hb)
        have wu : w = u := rF w rw' u (sr1r' u r1u) (connect_trans (G.cfaceC.1 (sc1Fw a ha)) aFu)
        exact r1'w (by rw [wu]; exact r1u)
      · simp only [last_append, last_cons, Lc1, Lc2]
      · intro t ht
        rcases List.mem_cons.1 ht with rfl | ht
        · exact List.mem_append_left _ (by rw [← Lc1]; exact mem_last _ _)
        · exact List.mem_append_right _ (sr1c2 t ht)
      · intro t ht
        rcases (G.fband_cat _ _ t).1 ht with ⟨u, hu, tFu⟩ | ht2
        · exact (G.fband_cons w r1 t).2 (Or.inl (connect_trans tFu (sc1Fw u hu)))
        · obtain ⟨u, hu, tFu⟩ := sc2r1 t ht2
          exact ⟨u, List.mem_cons_of_mem _ hu, tFu⟩
  apply Closed.of_forward G.cedge_sym
  rintro x _ rfl ⟨dNx, r'x⟩
  change x ∉ r at r'x
  suffices H : ∃ x', x' ∈ G.diskN r ∧ ∃ p, fpath G.face x' p ∧ last x' p = G.edge x ∧
      ∀ t ∈ x' :: p, t ∉ r by
    obtain ⟨x', dNx', p, x'Fp, Lp, r'p⟩ := H
    rw [← Lp]
    exact G.diskE_of_fpath r dNx' x'Fp r'p
  set x' := G.face (G.edge x) with hx'
  have dNx' : x' ∈ G.diskN r := ((G.diskN_node r) x' x (G.edgeK x)).2 dNx
  obtain ⟨q0, x'Fq0, Lq0⟩ := connect_iff_path.1 (G.cfaceC.1 (fconnect1 G.face (G.edge x)))
  obtain ⟨q, x'Fq, Uq, -, Lq⟩ := shortenP x'Fq0
  rw [Lq0] at Lq
  by_cases hq : ∃ y ∈ x' :: q, y ∈ r
  swap
  · exact ⟨x', dNx', q, x'Fq, Lq, fun t ht rt => hq ⟨t, ht, rt⟩⟩
  obtain ⟨y, qy, ry⟩ := hq
  -- rotate `r` to bring `y` in front (math-comp `rot_to`)
  obtain ⟨s1, s2, Dr⟩ := List.append_of_mem ry
  have hrot : r.rotate s1.length = y :: (s2 ++ s1) := by
    rw [Dr, List.rotate_append_length_eq, List.cons_append]
  generalize s2 ++ s1 = r1 at hrot
  have mem_r1 : ∀ t, t ∈ y :: r1 ↔ t ∈ r := fun t => by rw [← hrot, List.mem_rotate]
  have cyc1 : cycle G.rlink (y :: r1) := by rw [← hrot]; exact (cycle_rotate _ _).2 hr.1
  have U1 : (y :: r1).Nodup := by rw [← hrot]; exact List.nodup_rotate.2 Ur
  obtain ⟨r1'y, Ur1⟩ := List.nodup_cons.1 U1
  rw [cycle_cons, path_concat] at cyc1
  obtain ⟨yRr1, zRy⟩ := cyc1
  have sr1r : ∀ t ∈ r1, t ∈ r := fun t ht => (mem_r1 t).1 (List.mem_cons_of_mem _ ht)
  generalize hz : last y r1 = z at zRy
  have rz : z ∈ r := (mem_r1 z).1 (hz ▸ mem_last y r1)
  set z' := G.face (G.edge z) with hz'
  have yFz' : G.cface y z' := G.cfaceC.1 ((G.cface1 _ _).1 zRy)
  -- `z'` lies on the face path `x' :: q`
  have cycq : cycle (frel G.face) (x' :: q) := by
    rw [cycle_cons, path_concat]
    exact ⟨x'Fq, by rw [Lq]⟩
  have Fx' : ∀ t, G.cface x' t ↔ t ∈ x' :: q := fun t => fconnect_cycle cycq List.mem_cons_self
  have z'q : z' ∈ x' :: q := (Fx' z').1 (connect_trans ((Fx' y).2 qy) yFz')
  rcases List.mem_cons.1 z'q with zx | qz'
  · exact (r'x (G.edgeI (G.faceI zx) ▸ rz)).elim
  obtain ⟨q1, q2, rfl⟩ := List.append_of_mem qz'
  rw [← List.cons_append, List.nodup_append] at Uq
  obtain ⟨Uq1, Uq2, Uq12⟩ := Uq
  rw [path_append, path_cons] at x'Fq
  obtain ⟨x'Fq1, Lq1, zFq2⟩ := x'Fq
  rw [last_append, last_cons] at Lq
  rw [← List.cons_append, List.mem_append] at qy
  rcases qy with q1y | q2y
  · -- `y` lies on `x' :: q1`: the face path `z' :: q2` avoids the ring
    refine ⟨z', ((G.diskN_node r) z' z (G.edgeK z)).2 (G.mem_diskN_of_mem r rz), q2, zFq2, Lq, ?_⟩
    intro t ht rt
    exact Uq12 y q1y t ht (rF y ry t rt (connect_trans yFz' (path_connect zFq2 ht)))
  -- `y` lies on `z' :: q2`: we build a Moebius path, contradicting the planarity of `G`
  exfalso
  obtain ⟨c2, yRc2, Uc2, Lc2, sr1c2, sc2r1⟩ := claim2 r1 y ry sr1r yRr1 Ur1
  rw [hz] at Lc2
  have c2F'y : ∀ t ∈ c2, ¬ G.cface y t := by
    intro t ht yFt
    obtain ⟨u, r1u, tFu⟩ := sc2r1 t (G.ring_fband c2 t ht)
    have yu : y = u := rF y ry u (sr1r u r1u) (connect_trans yFt tFu)
    exact r1'y (by rw [yu]; exact r1u)
  obtain ⟨c1, q2', rfl, Lc1⟩ := splitPl q2y
  rw [path_append] at zFq2
  have z'Fc1 := zFq2.1
  have sub1 : (z' :: c1).Sublist (z' :: (c1 ++ q2')) :=
    (List.sublist_append_left c1 q2').cons_cons z'
  have Uc1 : (z' :: c1).Nodup := Uq2.sublist sub1
  -- the contour `z' :: c`, an `rclink` path from `z'` to `z` that covers the ring
  have claimC : ∃ c, path (frel rcl) z' c ∧ (z' :: c).Nodup ∧ last z' c = z ∧
      (∀ t ∈ y :: r1, t ∈ z' :: c) ∧ ∀ t ∈ z' :: c, t ∉ x' :: q1 := by
    refine ⟨c1 ++ c2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [path_append, Lc1]
      exact ⟨sFCr _ _ Uc1 (by rw [Lc1]; exact ry) z'Fc1, yRc2⟩
    · rw [← List.cons_append, List.nodup_append]
      refine ⟨Uc1, Uc2, fun a ha b hb hab => c2F'y b hb ?_⟩
      rw [← hab]
      have := cFpL _ _ z'Fc1 a ha
      rw [Lc1] at this
      exact G.cfaceC.1 this
    · rw [last_append, Lc1, Lc2]
    · intro t ht
      rcases List.mem_cons.1 ht with rfl | ht
      · rw [← List.cons_append]
        exact List.mem_append_left _ (by rw [← Lc1]; exact mem_last _ _)
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (sr1c2 t ht))
    · intro t ht hq1
      rw [← List.cons_append, List.mem_append] at ht
      rcases ht with ht | ht
      · exact Uq12 t hq1 t (sub1.subset ht) rfl
      · apply c2F'y t ht
        have h1 : G.cface t (last x' q1) := cFpL _ _ x'Fq1 t hq1
        have h2 : G.cface (last x' q1) z' := by rw [← Lq1]; exact fconnect1 _ _
        exact connect_trans yFz' (G.cfaceC.1 (connect_trans h1 h2))
  obtain ⟨c, z'Cc, Uc, Lc, sr1c, Uq1c⟩ := claimC
  have x'c : x' ∉ z' :: c := fun h => Uq1c x' h List.mem_cons_self
  have cycCc : cycle (frel rcl) (z' :: c) := by
    rw [cycle_cons, path_concat, Lc]
    exact ⟨z'Cc, rclR z rz⟩
  -- a C-path from a dart `x1` with `node x1` on the contour to `x'`, avoiding the contour
  have claimX : ∃ x1, G.node x1 ∈ z' :: c ∧ ∃ p, path G.clink x1 p ∧ last x1 p = x' ∧
      ∀ t ∈ x1 :: p, t ∉ z' :: c := by
    obtain ⟨x0, rx0, x0Dx⟩ := dNx
    obtain ⟨p, x0Dp, Lp⟩ := connect_iff_path.1 x0Dx
    have cx0 : ∃ t ∈ G.face (G.edge x0) :: p, t ∈ z' :: c := by
      refine ⟨_, List.mem_cons_self, ?_⟩
      obtain ⟨v, hv, hx0v⟩ := cycle.exists_succ cycCc (sr1c x0 ((mem_r1 x0).2 rx0))
      rw [← rclR x0 rx0, hx0v]
      exact hv
    clear x0Dx
    generalize G.face (G.edge x0) = a at x0Dp Lp cx0
    induction p generalizing a with
    | nil =>
      obtain ⟨t, ht, hct⟩ := cx0
      rw [List.mem_singleton] at ht
      rw [ht] at hct
      change a = x at Lp
      rw [Lp] at hct
      refine ⟨x', ?_, [], trivial, rfl, fun t ht => ?_⟩
      · show G.node (G.face (G.edge x)) ∈ z' :: c
        rw [G.edgeK]
        exact hct
      · rw [List.mem_singleton] at ht
        rw [ht]
        exact x'c
    | cons b p ih =>
      obtain ⟨aDb, bDp⟩ := x0Dp
      rw [last_cons] at Lp
      by_cases hc : ∃ t ∈ b :: p, t ∈ z' :: c
      · exact ih b bDp Lp hc
      have ca : a ∈ z' :: c := by
        obtain ⟨t, ht, hct⟩ := cx0
        rcases List.mem_cons.1 ht with rfl | ht
        · exact hct
        · exact absurd ⟨t, ht, hct⟩ hc
      obtain ⟨r'a, aCb⟩ := aDb
      obtain ⟨v, hv, hav⟩ := cycle.exists_succ cycCc ca
      change rcl a = v at hav
      rw [rclN a r'a] at hav
      rcases aCb with Da | Db
      · refine ⟨b, Da ▸ ca, p ++ [x'], ?_, last_concat _ _ _, ?_⟩
        · rw [path_concat, Lp]
          exact ⟨bDp.mono fun _ _ h => h.2, Or.inl (G.edgeK x).symm⟩
        · intro t ht
          rw [← List.cons_append, List.mem_append, List.mem_singleton] at ht
          rcases ht with ht | ht
          · exact fun h => hc ⟨t, ht, h⟩
          · rw [ht]
            exact x'c
      · exact absurd ⟨b, List.mem_cons_self, by rw [← Db, hav]; exact hv⟩ hc
  obtain ⟨x1, c_nx1, p, x1Cp, Lp, Upc⟩ := claimX
  have z'Cc' : path G.clink z' c := z'Cc.mono fun t u h => by
    change rcl t = u at h
    by_cases rt : t ∈ r
    · rw [rclR t rt] at h
      exact Or.inl (by rw [← h, G.edgeK])
    · rw [rclN t rt] at h
      exact Or.inr h
  have claimC0 : ∃ c0, path G.clink x1 c0 ∧ G.clink (last x1 c0) z' ∧
      ∀ t ∈ x1 :: c0, t ∉ z' :: c := by
    refine ⟨p ++ q1, ?_, ?_, ?_⟩
    · rw [path_append, Lp]
      exact ⟨x1Cp, x'Fq1.mono fun _ _ h => Or.inr h⟩
    · rw [last_append, Lp]
      exact Or.inr Lq1
    · intro t ht
      rw [← List.cons_append, List.mem_append] at ht
      rcases ht with ht | ht
      · exact Upc t ht
      · exact fun h => Uq1c t h (List.mem_cons_of_mem _ ht)
  obtain ⟨c0, x1Cc0, Lc0, Ucc0⟩ := claimC0
  obtain ⟨c1', x1Cc1, Uc1', sc01, Lc1'⟩ := shortenP x1Cc0
  rw [← Lc1'] at Lc0
  apply hJ (x1 :: (c1' ++ z' :: c))
  refine ⟨?_, ?_, ?_⟩
  · rw [← List.cons_append, List.nodup_append]
    refine ⟨Uc1', Uc, fun a ha b hb hab => ?_⟩
    rw [← hab] at hb
    have ha' : a ∈ x1 :: c0 := by
      rcases List.mem_cons.1 ha with rfl | ha
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (sc01 a ha)
    exact Ucc0 a ha' hb
  · rw [path_append]
    exact ⟨x1Cc1, Lc0, z'Cc'⟩
  · rw [last_append, last_cons, Lc]
    exact mem2_append.2 (Or.inr (Or.inr (mem2_cons_self.2 c_nx1)))

end DiskEdge

/-! ### The disk map -/

section SnipDisk

variable {D : Type u} (G : Hypermap D)

/-- The darts of the disk map `snip_disk`: the darts of `diskN r` (math-comp section
`Let ddart := {x | x \in diskN}`). -/
def SnipdDart (r : List D) : Type u := {x : D // x ∈ G.diskN r}

/-- The (classical) finite type structure of the disk darts. -/
noncomputable instance (r : List D) [Fintype D] : Fintype (G.SnipdDart r) := by
  classical exact (inferInstance : Fintype {x : D // x ∈ G.diskN r})

instance (r : List D) [Finite D] : Finite (G.SnipdDart r) :=
  inferInstanceAs (Finite {x : D // x ∈ G.diskN r})

instance (r : List D) [DecidableEq D] : DecidableEq (G.SnipdDart r) :=
  inferInstanceAs (DecidableEq {x : D // x ∈ G.diskN r})

/-- math-comp `snipd_edge`: the edge function of the disk map, which follows the ring `r` on
its darts. -/
def snipdEdge [DecidableEq D] (r : List D) (x : D) : D := if x ∈ r then next r x else G.edge x

/-- math-comp `dedge_subproof`. -/
theorem dedge_subproof [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) (u : G.SnipdDart r) : G.snipdEdge r u.1 ∈ G.diskN r := by
  unfold snipdEdge
  split_ifs with ru
  · exact G.mem_diskN_of_mem r (mem_next.2 ru)
  · exact (((G.diskE_edge hG hr) u.1 _ rfl).1 ⟨u.2, ru⟩).1

/-- math-comp `snipd_face`: the face function of the disk map. -/
def snipdFace [DecidableEq D] (r : List D) (x : D) : D :=
  if x ∈ r then G.face (G.edge (prev r x)) else G.face x

/-- math-comp `dface_subproof`. -/
theorem dface_subproof [Finite D] [DecidableEq D] {r : List D} (hr : G.SCycle G.rlink r)
    (u : G.SnipdDart r) : G.snipdFace r u.1 ∈ G.diskN r := by
  unfold snipdFace
  split_ifs with ru
  · exact ((G.diskN_node r) _ _ (G.edgeK _)).2
      (G.mem_diskN_of_mem r ((mem_prev (G.scycle_uniq hr)).2 ru))
  · exact G.diskN_dlink r u.2 ⟨ru, G.clinkF _⟩

/-- math-comp `dnode_subproof`. -/
theorem dnode_subproof [Finite D] {r : List D} (u : G.SnipdDart r) : G.node u.1 ∈ G.diskN r :=
  ((G.diskN_node r) _ _ rfl).1 u.2

/-- The edge permutation of `snip_disk` (math-comp section `Let dedge`). -/
def snipDiskEdge [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) (u : G.SnipdDart r) : G.SnipdDart r :=
  ⟨G.snipdEdge r u.1, G.dedge_subproof hG hr u⟩

/-- The node permutation of `snip_disk` (math-comp section `Let dnode`). -/
def snipDiskNode [Finite D] {r : List D} (u : G.SnipdDart r) : G.SnipdDart r :=
  ⟨G.node u.1, G.dnode_subproof u⟩

/-- The face permutation of `snip_disk` (math-comp section `Let dface`). -/
def snipDiskFace [Finite D] [DecidableEq D] {r : List D} (hr : G.SCycle G.rlink r)
    (u : G.SnipdDart r) : G.SnipdDart r :=
  ⟨G.snipdFace r u.1, G.dface_subproof hr u⟩

/-- math-comp `snipd_subproof`: `cancel3 dedge dnode dface`. -/
theorem snipd_subproof [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) (u : G.SnipdDart r) :
    G.snipDiskNode (G.snipDiskFace hr (G.snipDiskEdge hG hr u)) = u := by
  apply Subtype.ext
  show G.node (G.snipdFace r (G.snipdEdge r u.1)) = u.1
  by_cases ru : u.1 ∈ r
  · rw [snipdEdge, ite_eq_left ru, snipdFace, ite_eq_left (mem_next.2 ru),
      prev_next (G.scycle_uniq hr), G.edgeK]
  · have r'eu : G.edge u.1 ∉ r := (((G.diskE_edge hG hr) u.1 _ rfl).1 ⟨u.2, ru⟩).2
    rw [snipdEdge, ite_eq_right ru, snipdFace, ite_eq_right r'eu, G.edgeK]

/-- math-comp `snip_disk`: the "disk" hypermap obtained by cutting the planar map `G` along the
ring `r`; its darts are those of `diskN r` (a planar hypermap, see `planar_snipd`). -/
def snipDisk [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) : Hypermap (G.SnipdDart r) where
  edge := G.snipDiskEdge hG hr
  node := G.snipDiskNode
  face := G.snipDiskFace hr
  edgeK := G.snipd_subproof hG hr

/-- math-comp `snipd`: the projection in `G` of a dart of the disk map `snip_disk`. -/
def snipd (r : List D) (u : G.SnipdDart r) : D := u.1

/-- The projection of the edge permutation of `snip_disk` (by definition). -/
@[simp] theorem snipDisk_edge [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) (u : G.SnipdDart r) :
    G.snipd r ((G.snipDisk hG hr).edge u) = G.snipdEdge r (G.snipd r u) := rfl

/-- The projection of the node permutation of `snip_disk` (by definition). -/
@[simp] theorem snipDisk_node [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) (u : G.SnipdDart r) :
    G.snipd r ((G.snipDisk hG hr).node u) = G.node (G.snipd r u) := rfl

/-- The projection of the face permutation of `snip_disk` (by definition). -/
@[simp] theorem snipDisk_face [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) (u : G.SnipdDart r) :
    G.snipd r ((G.snipDisk hG hr).face u) = G.snipdFace r (G.snipd r u) := rfl

/-- math-comp `inj_snipd`. -/
theorem inj_snipd (r : List D) : Injective (G.snipd r) := fun _ _ h => Subtype.ext h

/-- math-comp `codom_snipd`. -/
theorem codom_snipd (r : List D) (x : D) : x ∈ Set.range (G.snipd r) ↔ x ∈ G.diskN r :=
  ⟨by rintro ⟨u, rfl⟩; exact u.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

/-- math-comp `snipd_ring`: the border of the disk map, the preimage of `r` by `snipd`. -/
noncomputable def snipdRing (r : List D) : List (G.SnipdDart r) := preimSeq (G.snipd r) r

/-- math-comp `map_snipd_ring`. -/
theorem map_snipd_ring [Finite D] (r : List D) : (G.snipdRing r).map (G.snipd r) = r :=
  map_preim fun x hx => (G.codom_snipd r x).2 (G.mem_diskN_of_mem r hx)

/-- The darts of the border of the disk map are those projected on the ring. -/
theorem mem_snipd_ring [Finite D] {r : List D} {u : G.SnipdDart r} :
    u ∈ G.snipdRing r ↔ G.snipd r u ∈ r := by
  rw [← List.mem_map_of_injective (G.inj_snipd r), G.map_snipd_ring]

/-- math-comp `ucycle_snipd_ring`. -/
theorem ucycle_snipd_ring [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) : UCycle (frel (G.snipDisk hG hr).edge) (G.snipdRing r) := by
  have UbGd : (G.snipdRing r).Nodup :=
    List.Nodup.of_map (G.snipd r) (by rw [G.map_snipd_ring]; exact G.scycle_uniq hr)
  refine ⟨cycle_from_next UbGd fun u hu => ?_, UbGd⟩
  show (G.snipDisk hG hr).edge u = next (G.snipdRing r) u
  apply G.inj_snipd r
  show G.snipdEdge r (G.snipd r u) = G.snipd r (next (G.snipdRing r) u)
  rw [snipdEdge, ite_eq_left (G.mem_snipd_ring.1 hu), ← next_map (G.inj_snipd r),
    G.map_snipd_ring]

/-- math-comp `cface_snipd`: `snipd` preserves and reflects face connectivity
(`{mono snipd : u v / cface u v}`). -/
theorem cface_snipd [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) (u v : G.SnipdDart r) :
    G.cface (G.snipd r u) (G.snipd r v) ↔ (G.snipDisk hG hr).cface u v := by
  set Gd := G.snipDisk hG hr
  have rF := G.scycle_cface hr
  -- math-comp local `homFd`
  have homFd : ∀ u v : G.SnipdDart r, Gd.cface u v → G.cface (G.snipd r u) (G.snipd r v) := by
    intro u v h
    induction h with
    | refl => exact connect_refl _
    | @tail w v' _ hwv ih =>
      refine connect_trans ih ?_
      obtain rfl : Gd.face w = v' := hwv
      show G.cface (G.snipd r w) (G.snipdFace r (G.snipd r w))
      unfold snipdFace
      split_ifs with rw
      · exact G.cfaceC.1 ((G.cface1 _ _).1 (prev_cycle hr.1 rw))
      · exact fconnect1 _ _
  -- math-comp local `homFd'`
  have homFd' : ∀ (p : List D) (u v : G.SnipdDart r), u ∉ Gd.fband (G.snipdRing r) →
      path (frel G.face) (G.snipd r u) p → last (G.snipd r u) p = G.snipd r v →
      Gd.cface u v := by
    intro p
    induction p with
    | nil =>
      intro u v _ _ h
      obtain rfl : u = v := G.inj_snipd r h
      exact connect_refl _
    | cons y p ih =>
      intro u v b'u hp Lp
      obtain ⟨Dy, yFp⟩ := hp
      change G.face (G.snipd r u) = y at Dy
      have r'u : G.snipd r u ∉ r := fun ru => b'u ⟨u, G.mem_snipd_ring.2 ru, connect_refl _⟩
      have dNy : y ∈ G.diskN r := by
        rw [← Dy]
        exact G.diskN_dlink r u.2 ⟨r'u, G.clinkF _⟩
      have hstep : Gd.face u = ⟨y, dNy⟩ := by
        apply Subtype.ext
        show G.snipdFace r (G.snipd r u) = y
        rw [snipdFace, ite_eq_right r'u]
        exact Dy
      have b'y : (⟨y, dNy⟩ : G.SnipdDart r) ∉ Gd.fband (G.snipdRing r) := by
        rintro ⟨w, hw, yFw⟩
        exact b'u ⟨w, hw, connect_trans (connect_of_rel hstep) yFw⟩
      exact connect_trans (connect_of_rel hstep) (ih ⟨y, dNy⟩ v b'y yFp Lp)
  refine ⟨fun h => ?_, homFd u v⟩
  by_cases bu : u ∈ Gd.fband (G.snipdRing r)
  swap
  · obtain ⟨p, hp, hl⟩ := connect_iff_path.1 h
    exact homFd' p u v bu hp hl
  by_cases bv : v ∈ Gd.fband (G.snipdRing r)
  swap
  · obtain ⟨p, hp, hl⟩ := connect_iff_path.1 (G.cfaceC.1 h)
    exact Gd.cfaceC.1 (homFd' p v u bv hp hl)
  obtain ⟨u1, hu1, uFu1⟩ := bu
  obtain ⟨v1, hv1, vFv1⟩ := bv
  have u1Fv1 : G.cface (G.snipd r u1) (G.snipd r v1) :=
    connect_trans (G.cfaceC.1 (homFd u u1 uFu1)) (connect_trans h (homFd v v1 vFv1))
  obtain rfl : u1 = v1 :=
    G.inj_snipd r (rF _ (G.mem_snipd_ring.1 hu1) _ (G.mem_snipd_ring.1 hv1) u1Fv1)
  exact connect_trans uFu1 (Gd.cfaceC.1 vFv1)

/-- math-comp `simple_snipd_ring`. -/
theorem simple_snipd_ring [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) : (G.snipDisk hG hr).Simple (G.snipdRing r) := by
  have h := simple_map (G := G.snipDisk hG hr) (G' := G) (G.cface_snipd hG hr) (G.snipdRing r)
  rw [G.map_snipd_ring] at h
  exact h.1 hr.2

/-- math-comp `scycle_snipd_ring`. -/
theorem scycle_snipd_ring [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) :
    (G.snipDisk hG hr).SFCycle (G.snipDisk hG hr).edge (G.snipdRing r) :=
  ⟨(G.ucycle_snipd_ring hG hr).1, G.simple_snipd_ring hG hr⟩

end SnipDisk

/-! ### The remainder map -/

section SnipRem

variable {D : Type u} (G : Hypermap D)

/-- The darts of the remainder map `snip_rem`: the darts outside `diskE r` (math-comp section
`Let rdart := {x | x \notin diskE}`). -/
def SniprDart (r : List D) : Type u := {x : D // x ∉ G.diskE r}

/-- The (classical) finite type structure of the remainder darts. -/
noncomputable instance (r : List D) [Fintype D] : Fintype (G.SniprDart r) := by
  classical exact (inferInstance : Fintype {x : D // x ∉ G.diskE r})

instance (r : List D) [Finite D] : Finite (G.SniprDart r) :=
  inferInstanceAs (Finite {x : D // x ∉ G.diskE r})

instance (r : List D) [DecidableEq D] : DecidableEq (G.SniprDart r) :=
  inferInstanceAs (DecidableEq {x : D // x ∉ G.diskE r})

/-- math-comp `redge_subproof`. -/
theorem redge_subproof [Fintype D] {r : List D} (hG : G.Planar) (hr : G.SCycle G.rlink r)
    (u : G.SniprDart r) : G.edge u.1 ∉ G.diskE r :=
  fun h => u.2 (((G.diskE_edge hG hr) u.1 _ rfl).2 h)

/-- math-comp `snipr_node`: the node function of the remainder map, which follows the reversed
ring on its darts. -/
def sniprNode [DecidableEq D] (r : List D) (z : D) : D := if z ∈ r then prev r z else G.node z

/-- math-comp `rnode_subproof`. -/
theorem rnode_subproof [Finite D] [DecidableEq D] {r : List D} (hr : G.SCycle G.rlink r)
    (u : G.SniprDart r) : G.sniprNode r u.1 ∉ G.diskE r := by
  unfold sniprNode
  split_ifs with ru
  · exact fun h => h.2 ((mem_prev (G.scycle_uniq hr)).2 ru)
  · exact fun h => u.2 ⟨((G.diskN_node r) _ _ rfl).2 h.1, ru⟩

/-- math-comp `snipr_face`: the face function of the remainder map. -/
def sniprFace [DecidableEq D] (r : List D) (z : D) : D :=
  if G.node (G.face z) ∈ r then next r (G.node (G.face z)) else G.face z

/-- math-comp `rface_subproof`. -/
theorem rface_subproof [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) (u : G.SniprDart r) : G.sniprFace r u.1 ∉ G.diskE r := by
  unfold sniprFace
  split_ifs with rnfu
  · exact fun h => h.2 (mem_next.2 rnfu)
  · intro h
    apply u.2
    have h1 : G.node (G.face u.1) ∈ G.diskE r := ⟨((G.diskN_node r) _ _ rfl).1 h.1, rnfu⟩
    exact ((G.diskE_edge hG hr) _ _ (G.faceK u.1)).1 h1

/-- The edge permutation of `snip_rem` (math-comp section `Let redge`). -/
def snipRemEdge [Fintype D] {r : List D} (hG : G.Planar) (hr : G.SCycle G.rlink r)
    (u : G.SniprDart r) : G.SniprDart r :=
  ⟨G.edge u.1, G.redge_subproof hG hr u⟩

/-- The node permutation of `snip_rem` (math-comp section `Let rnode`). -/
def snipRemNode [Finite D] [DecidableEq D] {r : List D} (hr : G.SCycle G.rlink r)
    (u : G.SniprDart r) : G.SniprDart r :=
  ⟨G.sniprNode r u.1, G.rnode_subproof hr u⟩

/-- The face permutation of `snip_rem` (math-comp section `Let rface`). -/
def snipRemFace [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) (u : G.SniprDart r) : G.SniprDart r :=
  ⟨G.sniprFace r u.1, G.rface_subproof hG hr u⟩

/-- math-comp `snipr_subproof`: `cancel3 redge rnode rface`. -/
theorem snipr_subproof [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) (u : G.SniprDart r) :
    G.snipRemNode hr (G.snipRemFace hG hr (G.snipRemEdge hG hr u)) = u := by
  apply Subtype.ext
  show G.sniprNode r (G.sniprFace r (G.edge u.1)) = u.1
  rw [sniprFace, G.edgeK]
  by_cases ru : u.1 ∈ r
  · rw [ite_eq_left ru, sniprNode, ite_eq_left (mem_next.2 ru), prev_next (G.scycle_uniq hr)]
  · have r'feu : G.face (G.edge u.1) ∉ r := fun h =>
      u.2 ⟨((G.diskN_node r) _ _ (G.edgeK u.1)).1 (G.mem_diskN_of_mem r h), ru⟩
    rw [ite_eq_right ru, sniprNode, ite_eq_right r'feu, G.edgeK]

/-- math-comp `snip_rem`: the "remainder" hypermap obtained by cutting the planar map `G` along
the ring `r`; its darts are the darts of `G` on or outside `r`, including those not connected
to `r` (a planar hypermap, see `planar_snipr`). -/
def snipRem [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) : Hypermap (G.SniprDart r) where
  edge := G.snipRemEdge hG hr
  node := G.snipRemNode hr
  face := G.snipRemFace hG hr
  edgeK := G.snipr_subproof hG hr

/-- math-comp `snipr`: the projection in `G` of a dart of the remainder map `snip_rem`. -/
def snipr (r : List D) (u : G.SniprDart r) : D := u.1

/-- The projection of the edge permutation of `snip_rem` (by definition). -/
@[simp] theorem snipRem_edge [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) (u : G.SniprDart r) :
    G.snipr r ((G.snipRem hG hr).edge u) = G.edge (G.snipr r u) := rfl

/-- The projection of the node permutation of `snip_rem` (by definition). -/
@[simp] theorem snipRem_node [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) (u : G.SniprDart r) :
    G.snipr r ((G.snipRem hG hr).node u) = G.sniprNode r (G.snipr r u) := rfl

/-- The projection of the face permutation of `snip_rem` (by definition). -/
@[simp] theorem snipRem_face [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) (u : G.SniprDart r) :
    G.snipr r ((G.snipRem hG hr).face u) = G.sniprFace r (G.snipr r u) := rfl

/-- math-comp `inj_snipr`. -/
theorem inj_snipr (r : List D) : Injective (G.snipr r) := fun _ _ h => Subtype.ext h

/-- math-comp `codom_snipr`. -/
theorem codom_snipr (r : List D) (x : D) : x ∈ Set.range (G.snipr r) ↔ x ∉ G.diskE r :=
  ⟨by rintro ⟨u, rfl⟩; exact u.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

/-- math-comp `snipr_ring`: the border of the remainder map, the preimage of `rev r` by
`snipr`. -/
noncomputable def sniprRing (r : List D) : List (G.SniprDart r) := preimSeq (G.snipr r) r.reverse

/-- math-comp `map_snipr_ring`. -/
theorem map_snipr_ring (r : List D) : (G.sniprRing r).map (G.snipr r) = r.reverse :=
  map_preim fun x hx => (G.codom_snipr r x).2 fun h => h.2 (List.mem_reverse.1 hx)

/-- The darts of the border of the remainder map are those projected on the ring. -/
theorem mem_snipr_ring {r : List D} {u : G.SniprDart r} :
    u ∈ G.sniprRing r ↔ G.snipr r u ∈ r := by
  rw [← List.mem_map_of_injective (G.inj_snipr r), G.map_snipr_ring, List.mem_reverse]

/-- math-comp `ucycle_snipr_ring`. -/
theorem ucycle_snipr_ring [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) : UCycle (frel (G.snipRem hG hr).node) (G.sniprRing r) := by
  have Ur := G.scycle_uniq hr
  have Ubr : (G.sniprRing r).Nodup :=
    List.Nodup.of_map (G.snipr r) (by rw [G.map_snipr_ring]; exact List.nodup_reverse.2 Ur)
  refine ⟨cycle_from_next Ubr fun u hu => ?_, Ubr⟩
  show (G.snipRem hG hr).node u = next (G.sniprRing r) u
  apply G.inj_snipr r
  show G.sniprNode r (G.snipr r u) = G.snipr r (next (G.sniprRing r) u)
  rw [sniprNode, ite_eq_left (G.mem_snipr_ring.1 hu), ← next_rev Ur, ← next_map (G.inj_snipr r),
    G.map_snipr_ring]

/-! ### Patching the disk and remainder maps -/

/-- math-comp `snip_patch`: `G` is the patch of the disk map and of the remainder map, along
their borders `snipd_ring` and `snipr_ring`. -/
theorem snip_patch [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) :
    G.Patch (G.snipDisk hG hr) (G.snipRem hG hr) (G.snipd r) (G.snipr r) (G.snipdRing r)
      (G.sniprRing r) where
  injd := G.inj_snipd r
  injr := G.inj_snipr r
  cycle_d := G.scycle_snipd_ring hG hr
  cycle_r := G.ucycle_snipr_ring hG hr
  map_ring_r := by rw [G.map_snipd_ring, G.map_snipr_ring]
  codom_r x := by
    rw [G.map_snipd_ring, G.codom_snipr, G.codom_snipd]
    constructor
    · intro h
      by_cases rx : x ∈ r
      · exact Or.inr rx
      · exact Or.inl fun dNx => h ⟨dNx, rx⟩
    · rintro (h | h) dEx
      · exact h dEx.1
      · exact dEx.2 h
  edge_d xd h := by
    have r'xd : G.snipd r xd ∉ r := fun h' => h (G.mem_snipd_ring.2 h')
    show G.snipdEdge r (G.snipd r xd) = G.edge (G.snipd r xd)
    rw [snipdEdge, ite_eq_right r'xd]
  node_d _ := rfl
  edge_r _ := rfl
  node_r xr h := by
    have r'xr : G.snipr r xr ∉ r := fun h' => h (G.mem_snipr_ring.2 h')
    show G.sniprNode r (G.snipr r xr) = G.node (G.snipr r xr)
    rw [sniprNode, ite_eq_right r'xr]

/-- math-comp `planar_snipd`. -/
theorem planar_snipd [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) : (G.snipDisk hG hr).Planar :=
  ((G.snip_patch hG hr).planar_patch.1 hG).1

/-- math-comp `planar_snipr`. -/
theorem planar_snipr [Fintype D] [DecidableEq D] {r : List D} (hG : G.Planar)
    (hr : G.SCycle G.rlink r) : (G.snipRem hG hr).Planar :=
  ((G.snip_patch hG hr).planar_patch.1 hG).2

end SnipRem

/-! ### Rotation invariance

Disks only depend on the extent of their ring; hence, they are invariant under rotation
(math-comp section `SnipRot`). -/

section SnipRot

variable {D : Type u} (G : Hypermap D) (n0 : ℕ) (r : List D)

/-- math-comp `diskN_rot`. -/
theorem diskN_rot : G.diskN (r.rotate n0) = G.diskN r := by
  have hd : G.dlink (r.rotate n0) = G.dlink r := by
    funext x y
    simp only [dlink, List.mem_rotate]
  ext x
  simp only [diskN, dconnect, hd, Set.mem_ofPred_eq, List.mem_rotate]

/-- math-comp `diskE_rot`. -/
theorem diskE_rot : G.diskE (r.rotate n0) = G.diskE r := by
  ext x
  simp only [diskE, diskN_rot, Set.mem_sdiff, Set.mem_ofPred_eq, List.mem_rotate]

/-- math-comp `diskF_rot`. -/
theorem diskF_rot : G.diskF (r.rotate n0) = G.diskF r := by
  rw [diskF, diskF, diskN_rot, fband_rot]

/-- math-comp `diskFC_rot`. -/
theorem diskFC_rot : G.diskFC (r.rotate n0) = G.diskFC r := by
  rw [diskFC, diskFC, diskN_rot, fband_rot]

end SnipRot

end Hypermap

end FourColor
