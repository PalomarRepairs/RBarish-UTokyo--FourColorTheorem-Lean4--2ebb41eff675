/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Snip
import FourColor.Sew
import FourColor.Kempe

/-!
# Dissecting a map along a ring and its reverse  (port of `revsnip.v`)

This file dissects a connected plain map along a proper ring and its reverse edge-conjugate.
This gives a symmetric cover (compare with `FourColor.Snip`, where the construction is
asymmetric). For a hypermap `G : Hypermap D` and a ring `r : List D` (a simple R-cycle,
`hr : G.SCycle G.rlink r`) we define

* `G.ProperRing r`        : `r` is non-empty and not an E-path of size 2 (math-comp
  `proper_ring r`).
* `G.NontrivialRing m r`  : there are more than `m` faces both strictly inside and strictly
  outside `r`, i.e., included in `diskF r` and `diskFC r`, respectively (math-comp
  `nontrivial_ring m r`).
* `G.revRing r`           : the dual of the ring `r`, that goes, around the outside of `r`,
  through the same faces as `r`, in reverse order, `(r.map G.edge).reverse` (math-comp
  `rev_ring r`).
* `G.chordRing r x`       : the ring consisting of `x` followed by a portion of `r`, when `x` is
  a "chord" of `r`, linking two faces of `r`, i.e., both `x` and `edge x` are in `fband r`
  (math-comp `chord_ring r x`).

The properties established here feed directly into `birkhoff.v`; the chord constructions are
also used in `embed.v` when using induction over the disk size of a ring. If
`hG : G.PlanarBridgelessPlainConnected`, `hGp : G.Planar` and `hr : G.SCycle G.rlink r`, then
we also define:

* `G.revSnipdDisk hG hGp hr` : the disk hypermap obtained by cutting `G` along `revRing r`,
  whose dart set is the exact complement of `diskN r` (math-comp `rev_snipd_disk`).
* `G.revSniprDisk hG hGp hr` : the corresponding remainder hypermap (math-comp
  `rev_snipr_disk`).
* `G.revSnipdRing r`, `G.revSniprRing r` : the border rings of these two maps (math-comp
  `rev_snipd_ring`, `rev_snipr_ring`); the injections to `G` are
  `G.snipd (G.revRing r)` and `G.snipr (G.revRing r)`.

The main results are `rev_ring_cotrace` (the disk map of `r` and the remainder map of
`revRing r` have the same border traces), `ring_disk_closed` (the ring traces of the disk map
of a nontrivial ring are Kempe closed when `G` is cubic), `colorable_from_ring` and
`ring_disk_chord` (a chord of the disk border yields a shorter nontrivial ring).

This file also ports the math-comp `path.v` definition `arc` and the lemmas `left_arc`,
`right_arc`, `rot_to_arc` used by `chord_ring`, which were not yet available.

## Coq → Lean names

| Coq | Lean |
|---|---|
| `arc`, `left_arc`, `right_arc`, `rot_to_arc` (`path.v`) | same names (in `FourColor`) |
| `proper_ring`, `size_proper_ring` | `ProperRing`, `size_proper_ring` |
| `proper_ring_rot` | `proper_ring_rot` (`List.rotate`), `proper_ring_rot'` (`rot`) |
| `nontrivial_ring` | `NontrivialRing` |
| `fcard0P`, `fcard1P`, `nontrivial0P`, `nontrivial1P` | same names |
| `rev_ring`, `rev_rev_ring`, `proper_rev_ring` | `revRing`, `rev_rev_ring`, `proper_rev_ring` |
| `mem_rev_ring`, `cycle_rev_ring`, `froot_face_rev_ring` | same names |
| `simple_rev_ring`, `scycle_rev_ring`, `fband_rev_ring` | same names |
| `pick_in_ring`, `diskN_edge_ring`, `diskN_rev_ring`, `diskF_rev_ring` | same names |
| `chord_ring`, `scycle_chord_ring`, `proper_chord_ring` | `chordRing`, same names |
| `diskN_chord_ring`, `fband_chord_ring`, `diskF_chord_ring` | same names |
| `nontrivial_chord_ring`, `nontrivial_ring_proper`, `nontrivial_rev_ring` | same names |
| `rev_snipd_disk`, `rev_snipr_disk` | `revSnipdDisk`, `revSniprDisk` |
| `rev_snipd_ring`, `rev_snipr_ring` | `revSnipdRing`, `revSniprRing` |
| `rev_snipr_ring_eq`, `rev_ring_cotrace`, `ring_disk_closed` | same names |
| `colorable_from_ring`, `ring_disk_chord` | same names |
| section `Let`s `pfd`, `pfdP`, `pfrr`, `pfrrP` | private `liftCol`, `liftCol_eq` |

Lean-only public additions: `arc_of_rotate` (the arcs of any rotation of a duplicate-free
sequence), and `diskFC_rev_ring` (`diskFC (revRing r) = diskF r`, the dual of
`diskF_rev_ring`).

## Porting notes

* The section hypotheses become explicit arguments of the declarations that use them, in the
  Coq order: `hG : G.PlanarBridgelessPlainConnected` (math-comp `geoG`), `hGp : G.Planar`
  (math-comp `planarG`), `hr : G.SCycle G.rlink r` (math-comp `scycRr`, with `r` implicit),
  `nt_r` (`G.ProperRing r` in section `RingPartitions`, `G.NontrivialRing m r` in section
  `NonTrivialRing`, with `m` implicit), and the chord `x` with `dEx : x ∈ G.diskE r`,
  `rFx : x ∈ G.fband r`, `rFex : G.edge x ∈ G.fband r` (with `x` implicit; the rings and darts
  of the membership lemmas such as `mem_rev_ring` are implicit too). As in Coq, a declaration
  only takes the hypotheses its proof uses (for instance `froot_face_rev_ring` and
  `simple_rev_ring` only take `hr`). The redundant planarity hypothesis `hGp` is kept, as in
  Coq, exactly for the declarations that mention the snip maps; the other lemmas use
  `hG.planar`.
* `proper_ring` and `nontrivial_ring` are `Prop`s (`ProperRing` is decidable); boolean
  equations and `reflect` lemmas are `↔`; `=i` between predicates is an equality of sets;
  `[predD A & B]` is `A \ B` and `[predC A]` is `Aᶜ`; `exists2` is `∃ _, _ ∧ _`; the
  sigma-type `pick_in_ring` is an existential.
* math-comp's `rot n0 r` is `List.rotate` in the ring lemmas of `FourColor.Geometry` and
  `FourColor.Snip`; `proper_ring_rot` is stated for `List.rotate`, and `proper_ring_rot'` for
  the literal math-comp `rot` of `FourColor.Color`. `froot_face_rev_ring`, `rot_to_arc` and
  `rev_ring_cotrace` use the math-comp `rot`/`rotr` of `FourColor.Color` (as the trace lemmas
  `trace_rot`, `rotrK` do).
* `fcard0P` and `fcard1P` keep the face-closedness hypothesis of the Coq statements, although
  the Lean count `fcard` (`nComp`) does not need it.
* The dart types of `revSnipdDisk`, `revSniprDisk` do not depend on the hypotheses, and
  neither do `revSnipdRing r`, `revSniprRing r` and `rev_snipr_ring_eq`. The four definitions
  are `abbrev`s, so that the lemmas of `FourColor.Snip` apply to them directly.
* The math-comp lemmas on `next`/`prev` used here (`mem_next`, `mem_prev`, `prev_next`,
  `next_map`, `next_cycle`, `prev_cycle`) are private in `FourColor.Patch` and
  `FourColor.Snip`; they are reproved here as private lemmas.
* The Coq proof of `diskN_chord_ring` counts `(y ∈ diskN cr1) + (y ∈ diskN cr2)`; here the
  same induction carries the equivalent invariant `ChordInv` (a dart is in exactly one of the
  two chord disks iff it is in `diskN r`).
-/

namespace FourColor

open Function

universe u

/-! ### Cyclic successor and predecessor: complements to `FourColor.Geometry`

The math-comp lemmas on `next`/`prev` used here; the same statements are private in
`FourColor.Patch` and `FourColor.Snip`, and are reproved here in the same way. -/

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
private theorem next_map [DecidableEq β] {f : α → β} (hf : Injective f) (p : List α)
    (x : α) :
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

/-! ### Rotations and arcs of a cyclic sequence (math-comp `arc`, `rot_to_arc`) -/

section Arc

variable {α : Type*}

/-- Any item of a sequence can be rotated to its head (math-comp `rot_to`, for
`List.rotate`). -/
private theorem rotate_to {p : List α} {x : α} (h : x ∈ p) : ∃ i s, p.rotate i = x :: s := by
  obtain ⟨u, v, rfl⟩ := List.append_of_mem h
  exact ⟨u.length, v ++ u, by rw [List.rotate_append_length_eq, List.cons_append]⟩

/-- Any math-comp rotation `rot i p` is a `List.rotate` rotation. -/
private theorem exists_rotate_of_rot (i : ℕ) (p : List α) : ∃ j, rot i p = p.rotate j := by
  rcases le_or_gt i p.length with h | h
  · exact ⟨i, rot_eq_rotate h⟩
  · exact ⟨0, by rw [rot_oversize h.le, List.rotate_zero]⟩

/-- Two rotations of a duplicate-free sequence that start with the same item are equal. -/
private theorem rotate_head_unique {p : List α} (hp : p.Nodup) {i j : ℕ} {x : α}
    {s t : List α} (hi : p.rotate i = x :: s) (hj : p.rotate j = x :: t) : s = t := by
  have hlen : 0 < p.length := by
    rw [← List.length_rotate p i, hi]
    exact Nat.succ_pos _
  have h0i : (p.rotate i)[0]'(by rw [List.length_rotate]; exact hlen) = x := by
    simp only [hi, List.getElem_cons_zero]
  have h0j : (p.rotate j)[0]'(by rw [List.length_rotate]; exact hlen) = x := by
    simp only [hj, List.getElem_cons_zero]
  rw [List.getElem_rotate] at h0i h0j
  have hij : (0 + i) % p.length = (0 + j) % p.length := (hp.getElem_inj_iff).1 (h0i.trans h0j.symm)
  have hrot : p.rotate i = p.rotate j := by
    rw [← List.rotate_mod p i, ← List.rotate_mod p j]
    simpa only [Nat.zero_add] using congrArg p.rotate hij
  rw [hi, hj] at hrot
  exact (List.cons.inj hrot).2

variable [DecidableEq α]

/-- math-comp `arc p x y`: the arc of the cyclic sequence `p` from `x` (included) to `y`
(excluded), i.e., the prefix of `rot (index x p) p` before the first occurrence of `y`. -/
def arc (p : List α) (x y : α) : List α :=
  let px := rot (p.idxOf x) p
  px.take (px.idxOf y)

/-- Rotating a duplicate-free sequence to the index of `x` gives its unique rotation that starts
with `x`. -/
private theorem rot_idxOf_of_rotate {p : List α} (hp : p.Nodup) {i : ℕ} {x : α} {s : List α}
    (h : p.rotate i = x :: s) : rot (p.idxOf x) p = x :: s := by
  have hx : x ∈ p := List.mem_rotate.1 (h ▸ List.mem_cons_self)
  obtain ⟨u, v, rfl⟩ := List.append_of_mem hx
  have hxu : x ∉ u := fun hm =>
    (List.nodup_cons.1 (List.nodup_middle.1 hp)).1 (List.mem_append_left _ hm)
  have h' : (u ++ x :: v).rotate u.length = x :: (v ++ u) := by
    rw [List.rotate_append_length_eq, List.cons_append]
  rw [List.idxOf_append_of_notMem hxu, List.idxOf_cons_self, Nat.add_zero, rot_size_cat,
    List.cons_append, rotate_head_unique hp h' h]

/-- The two arcs of a rotation of a duplicate-free sequence (the core of math-comp `left_arc`,
`right_arc` and `rot_to_arc`). -/
theorem arc_of_rotate {p : List α} (hp : p.Nodup) {i : ℕ} {x y : α} {p1 p2 : List α}
    (h : p.rotate i = x :: p1 ++ y :: p2) : arc p x y = x :: p1 ∧ arc p y x = y :: p2 := by
  have hn : (x :: p1 ++ y :: p2).Nodup := h ▸ List.nodup_rotate.2 hp
  have hd := List.disjoint_of_nodup_append hn
  have hy : y ∉ x :: p1 := fun hm => hd hm List.mem_cons_self
  have hx : x ∉ y :: p2 := fun hm => hd List.mem_cons_self hm
  have h1 : p.rotate i = x :: (p1 ++ y :: p2) := by rw [h, List.cons_append]
  have h2 : p.rotate (i + (x :: p1).length) = y :: (p2 ++ x :: p1) := by
    rw [← List.rotate_rotate, h, List.rotate_append_length_eq, List.cons_append]
  constructor
  · simp only [arc]
    rw [rot_idxOf_of_rotate hp h1, ← List.cons_append, List.idxOf_append_of_notMem hy,
      List.idxOf_cons_self, Nat.add_zero, List.take_left' rfl]
  · simp only [arc]
    rw [rot_idxOf_of_rotate hp h2, ← List.cons_append, List.idxOf_append_of_notMem hx,
      List.idxOf_cons_self, Nat.add_zero, List.take_left' rfl]

/-- math-comp `left_arc`. -/
theorem left_arc {x y : α} {p1 p2 : List α} (hp : (x :: p1 ++ y :: p2).Nodup) :
    arc (x :: p1 ++ y :: p2) x y = x :: p1 :=
  (arc_of_rotate hp (List.rotate_zero _)).1

/-- math-comp `right_arc`. -/
theorem right_arc {x y : α} {p1 p2 : List α} (hp : (x :: p1 ++ y :: p2).Nodup) :
    arc (x :: p1 ++ y :: p2) y x = y :: p2 :=
  (arc_of_rotate hp (List.rotate_zero _)).2

/-- math-comp `rot_to_arc` (with the variant type `rot_to_arc_spec` unfolded into an
existential): two distinct items `x`, `y` of a duplicate-free sequence `p` split a rotation of
`p` into the arcs `arc p x y` and `arc p y x`. -/
theorem rot_to_arc {p : List α} (hp : p.Nodup) {x y : α} (hx : x ∈ p) (hy : y ∈ p)
    (hxy : x ≠ y) :
    ∃ i p1 p2, x :: p1 = arc p x y ∧ y :: p2 = arc p y x ∧ rot i p = x :: p1 ++ y :: p2 := by
  obtain ⟨u, v, rfl⟩ := List.append_of_mem hx
  have hyv : y ∈ v ++ u := by
    rcases List.mem_append.1 hy with h | h
    · exact List.mem_append_right _ h
    · exact List.mem_append_left _ ((List.mem_cons.1 h).resolve_left (Ne.symm hxy))
  obtain ⟨p1, p2, hv⟩ := List.append_of_mem hyv
  have hrot : (u ++ x :: v).rotate u.length = x :: p1 ++ y :: p2 := by
    rw [List.rotate_append_length_eq, List.cons_append, hv]
    rfl
  obtain ⟨h1, h2⟩ := arc_of_rotate hp hrot
  refine ⟨u.length, p1, p2, h1.symm, h2.symm, ?_⟩
  rw [rot_eq_rotate (by rw [List.length_append]; omega), hrot]

end Arc

/-! ### Cycles, reversal and maps -/

section CycleRev

variable {α β : Type*}

/-- `cycle` is monotone in the relation. -/
private theorem cycle_mono {e e' : α → α → Prop} (h : ∀ a b, e a b → e' a b) {p : List α}
    (hp : cycle e p) : cycle e' p := by
  cases p with
  | nil => trivial
  | cons x p => exact path.mono h hp

/-- math-comp `map_cycle` (for an arbitrary relation). -/
private theorem cycle_map {e : α → α → Prop} {f : β → α} {p : List β} :
    cycle e (p.map f) ↔ cycle (fun a b => e (f a) (f b)) p := by
  cases p with
  | nil => exact Iff.rfl
  | cons x p =>
    show path e (f x) (p.map f ++ [f x]) ↔ path _ x (p ++ [x])
    rw [show p.map f ++ [f x] = (p ++ [x]).map f by simp, path_map]

/-- math-comp `rev_cycle`: the reverse of an `e`-cycle is an `e`-cycle for the converse
relation. -/
private theorem cycle_reverse {e : α → α → Prop} {p : List α} :
    cycle e p.reverse ↔ cycle (fun a b => e b a) p := by
  cases p with
  | nil => exact Iff.rfl
  | cons x q =>
    rw [List.reverse_cons, cycle_rotate_one]
    show path e x (q.reverse ++ [x]) ↔ path _ x (q ++ [x])
    have h := path_reverse (e := e) (x := x) (p := q ++ [x])
    rwa [last_concat, belast_concat, List.reverse_cons] at h

end CycleRev

namespace Hypermap

/-! ### Proper and nontrivial rings (math-comp section `ProperRing`)

A proper ring is a non-empty ring that is NOT an edge orbit. A nontrivial ring of order `m` must
have more than `m` face orbits in both its inner and outer face disks. -/

section ProperRing

variable {D : Type u} (G : Hypermap D)

/-- math-comp `proper_ring r`: `r` is non-empty and not an E-path of size 2, i.e., `r` has at
least three darts, or `r = [x, y]` with `edge x ≠ y`. -/
def ProperRing : List D → Prop
  | [] => False
  | [_] => False
  | [x, y] => G.edge x ≠ y
  | _ :: _ :: _ :: _ => True

/-- `proper_ring` is a boolean predicate in math-comp. -/
instance [DecidableEq D] : DecidablePred G.ProperRing
  | [] => isFalse id
  | [_] => isFalse id
  | [x, y] => inferInstanceAs (Decidable (G.edge x ≠ y))
  | _ :: _ :: _ :: _ => isTrue trivial

/-- math-comp `size_proper_ring`. -/
theorem size_proper_ring {r : List D} (h : 2 < r.length) : G.ProperRing r :=
  match r, h with
  | [], h => absurd h (by simp)
  | [_], h => absurd h (by simp)
  | [_, _], h => absurd h (by simp)
  | _ :: _ :: _ :: _, _ => trivial

/-- In a plain map, `edge x = y` iff `edge y = x`. -/
private theorem edge_eq_comm [Finite D] (hG : G.Plain) {x y : D} : G.edge x = y ↔ G.edge y = x :=
  ⟨fun h => by rw [← h, G.plain_eq hG], fun h => by rw [← h, G.plain_eq hG]⟩

/-- math-comp `proper_ring_rot`, for the rotations `List.rotate` (used by the ring lemmas of
`FourColor.Geometry` and `FourColor.Snip`); see `proper_ring_rot'` for math-comp's `rot`. -/
theorem proper_ring_rot [Finite D] (hG : G.Plain) (n0 : ℕ) (r : List D) :
    G.ProperRing (r.rotate n0) ↔ G.ProperRing r := by
  match r with
  | [] => rw [List.rotate_nil]
  | [x] => rw [List.rotate_singleton]
  | [x, y] =>
    rw [← List.rotate_mod]
    rcases Nat.mod_two_eq_zero_or_one n0 with h | h
    · rw [show n0 % [x, y].length = 0 from h, List.rotate_zero]
    · rw [show n0 % [x, y].length = 1 from h]
      show G.edge y ≠ x ↔ G.edge x ≠ y
      rw [ne_eq, ne_eq, G.edge_eq_comm hG]
  | a :: b :: c :: l =>
    exact iff_of_true (G.size_proper_ring (by simp)) trivial

/-- math-comp `proper_ring_rot`, for math-comp's rotation `rot` (`FourColor.rot`). -/
theorem proper_ring_rot' [Finite D] (hG : G.Plain) (n0 : ℕ) (r : List D) :
    G.ProperRing (rot n0 r) ↔ G.ProperRing r := by
  rcases le_or_gt n0 r.length with h | h
  · rw [rot_eq_rotate h, G.proper_ring_rot hG]
  · rw [rot_oversize h.le]

/-- math-comp `nontrivial_ring m r`: there are more than `m` faces both strictly inside `r`
(in `diskF r`) and strictly outside `r` (in `diskFC r`). -/
def NontrivialRing (m : ℕ) (r : List D) : Prop :=
  m < fcard G.face (G.diskF r) ∧ m < fcard G.face (G.diskFC r)

variable [Finite D]

/-- math-comp `fcard0P`: a face-closed set has a face orbit iff it is non-empty. -/
theorem fcard0P {A : Set D} (_hA : Closed (frel G.face) A) :
    0 < fcard G.face A ↔ ∃ x, x ∈ A :=
  nComp_pos

/-- math-comp `fcard1P`: a face-closed set has more than one face orbit iff it contains two
darts in different faces. -/
theorem fcard1P {A : Set D} (_hA : Closed (frel G.face) A) :
    1 < fcard G.face A ↔ ∃ x ∈ A, ∃ y ∈ A, ¬ G.cface x y := by
  constructor
  · intro h
    obtain ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hne⟩ :=
      (Set.one_lt_ncard (Set.finite_of_ncard_pos (by unfold fcard nComp at h; omega))).1 h
    exact ⟨x, hx, y, hy, fun hxy => hne ((comp_eq_iff G.cface_sym).2 hxy)⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact one_lt_nComp G.cface_sym hx hy hxy

/-- math-comp `nontrivial0P`. -/
theorem nontrivial0P (r : List D) :
    G.NontrivialRing 0 r ↔ (∃ x, x ∈ G.diskF r) ∧ (∃ x, x ∈ G.diskFC r) := by
  unfold NontrivialRing
  rw [G.fcard0P (G.diskF_face r), G.fcard0P (G.diskFC_face r)]

/-- math-comp `nontrivial1P`. -/
theorem nontrivial1P (r : List D) :
    G.NontrivialRing 1 r ↔
      (∃ x ∈ G.diskF r, ∃ y ∈ G.diskF r, ¬ G.cface x y) ∧
        (∃ x ∈ G.diskFC r, ∃ y ∈ G.diskFC r, ¬ G.cface x y) := by
  unfold NontrivialRing
  rw [G.fcard1P (G.diskF_face r), G.fcard1P (G.diskFC_face r)]

end ProperRing

/-! ### The reverse ring (math-comp section `RevSnip`) -/

section RevRing

variable {D : Type u} (G : Hypermap D)

/-- math-comp `rev_ring r`: the dual of the ring `r`, that goes around the outside of `r`
through the same faces as `r`, in reverse order: `rev (map edge r)`. -/
def revRing (r : List D) : List D := (r.map G.edge).reverse

variable [Fintype D]

/-- math-comp `rev_rev_ring`. -/
theorem rev_rev_ring (hG : G.PlanarBridgelessPlainConnected) (r : List D) :
    G.revRing (G.revRing r) = r := by
  simp only [revRing, List.map_reverse, List.reverse_reverse, List.map_map]
  conv_rhs => rw [← List.map_id r]
  exact List.map_congr_left fun x _ => G.plain_eq hG.plain x

/-- math-comp `proper_rev_ring`. -/
theorem proper_rev_ring (hG : G.PlanarBridgelessPlainConnected) (r : List D) :
    G.ProperRing (G.revRing r) ↔ G.ProperRing r := by
  match r with
  | [] => exact Iff.rfl
  | [_] => exact Iff.rfl
  | [x, y] =>
    show G.edge (G.edge y) ≠ G.edge x ↔ G.edge x ≠ y
    rw [G.plain_eq hG.plain]
    exact ne_comm
  | a :: b :: c :: l =>
    exact iff_of_true (G.size_proper_ring (by simp [revRing])) trivial

/-- math-comp `mem_rev_ring`. -/
theorem mem_rev_ring (hG : G.PlanarBridgelessPlainConnected) {r : List D} {x : D} :
    x ∈ G.revRing r ↔ G.edge x ∈ r := by
  rw [revRing, List.mem_reverse, List.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [G.plain_eq hG.plain]
  · intro h
    exact ⟨G.edge x, h, G.plain_eq hG.plain x⟩

/-- math-comp `cycle_rev_ring`. -/
theorem cycle_rev_ring (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) : cycle G.rlink (G.revRing r) := by
  rw [revRing, cycle_reverse, cycle_map]
  refine cycle_mono (fun a b h => ?_) hr.1
  show G.cface (G.edge (G.edge b)) (G.edge a)
  rw [G.plain_eq hG.plain]
  exact G.cfaceC.1 h

/-- math-comp `froot_face_rev_ring`. -/
theorem froot_face_rev_ring {r : List D} (hr : G.SCycle G.rlink r) :
    (G.revRing r).map (froot G.face) = (rot 1 (r.map (froot G.face))).reverse := by
  rw [revRing, List.map_reverse, List.map_map]
  congr 1
  cases r with
  | nil => rfl
  | cons x0 p =>
    rw [List.map_cons (f := froot G.face) (a := x0) (l := p), rot1_cons]
    have key : ∀ (q : List D) (x : D), path G.rlink x (q ++ [x0]) →
        (x :: q).map (froot G.face ∘ G.edge) = q.map (froot G.face) ++ [froot G.face x0] := by
      intro q
      induction q with
      | nil =>
        intro x hx
        simp only [List.map_cons, List.map_nil, List.nil_append, Function.comp_apply]
        rw [(G.froot_face_eq_iff).2 hx.1]
      | cons y q ih =>
        intro x hx
        rw [List.map_cons, ih y hx.2, List.map_cons, Function.comp_apply,
          (G.froot_face_eq_iff).2 hx.1, List.cons_append]
    exact key p x0 hr.1

/-- math-comp `simple_rev_ring`. -/
theorem simple_rev_ring {r : List D} (hr : G.SCycle G.rlink r) : G.Simple (G.revRing r) := by
  unfold Simple
  rw [G.froot_face_rev_ring hr, List.nodup_reverse, nodup_rot]
  exact hr.2

/-- math-comp `scycle_rev_ring`. -/
theorem scycle_rev_ring (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) : G.SCycle G.rlink (G.revRing r) :=
  ⟨G.cycle_rev_ring hG hr, G.simple_rev_ring hr⟩

variable [DecidableEq D]

/-- math-comp `fband_rev_ring`. -/
theorem fband_rev_ring (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) : G.fband (G.revRing r) = G.fband r := by
  ext x
  constructor
  · rintro ⟨y, ry, xFy⟩
    rw [G.mem_rev_ring hG] at ry
    refine ⟨next r (G.edge y), mem_next.2 ry, connect_trans xFy ?_⟩
    have h : G.cface (G.edge (G.edge y)) (next r (G.edge y)) := next_cycle hr.1 ry
    rwa [G.plain_eq hG.plain] at h
  · rintro ⟨y, ry, xFy⟩
    refine ⟨G.edge (prev r y), (G.mem_rev_ring hG).2 ?_,
      connect_trans xFy (G.cfaceC.1 (prev_cycle hr.1 ry))⟩
    rw [G.plain_eq hG.plain]
    exact (mem_prev (G.scycle_uniq hr)).2 ry

end RevRing

/-! ### Ring partitions (math-comp section `RingPartitions`)

In this section the ring `r` is proper (`nt_r : G.ProperRing r`); we show that the inner disk
of `rev_ring r` is the complement of the disk of `r`, and that a chord `x` of `r` (a dart of
`diskE r` such that `x` and `edge x` are both in `fband r`) splits the disk of `r` into the
disks of the two rings `chord_ring r x` and `chord_ring r (edge x)`. -/

section RingPartitions

variable {D : Type u} (G : Hypermap D)

/-- math-comp `pick_in_ring`: a proper ring is non-empty. -/
theorem pick_in_ring {r : List D} (nt_r : G.ProperRing r) : ∃ x, x ∈ r :=
  match r, nt_r with
  | x :: _, _ => ⟨x, List.mem_cons_self⟩

variable [Fintype D] [DecidableEq D]

/-- math-comp `diskN_edge_ring`: the edge of a dart of a proper ring `r` lies outside the disk
of `r`. -/
theorem diskN_edge_ring (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) (nt_r : G.ProperRing r) {x : D} (r_x : x ∈ r) :
    G.edge x ∉ G.diskN r := by
  have hpl := hG.plain
  have Ur := G.scycle_uniq hr
  intro h
  rcases (G.diskN_E r _).1 h with r_ex | dEex
  · have Dex : G.edge x = next r x :=
      G.scycle_cface hr _ r_ex _ (mem_next.2 r_x) (next_cycle hr.1 r_x)
    have Dx : x = next r (G.edge x) := by
      refine G.scycle_cface hr _ r_x _ (mem_next.2 r_ex) ?_
      have h1 : G.cface (G.edge (G.edge x)) (next r (G.edge x)) := next_cycle hr.1 r_ex
      rwa [G.plain_eq hpl] at h1
    obtain ⟨i, p, hi⟩ := rotate_to r_x
    have nt' := (G.proper_ring_rot hpl i r).2 nt_r
    rw [← next_rotate Ur i, hi] at Dex Dx
    have U' : (x :: p).Nodup := hi ▸ List.nodup_rotate.2 Ur
    rw [hi] at nt'
    match p, Dex, Dx, U', nt' with
    | [], _, _, _, nt' => exact nt'
    | [y], Dex, _, _, nt' =>
      apply nt'
      rw [Dex]
      simp [next, nextAt]
    | y :: z :: p, Dex, Dx, U', _ =>
      have hxy : y ≠ x := fun e => (List.nodup_cons.1 U').1 (e ▸ List.mem_cons_self)
      have e1 : next (x :: y :: z :: p) x = y := by simp [next, nextAt]
      have e2 : next (x :: y :: z :: p) y = z := by simp [next, nextAt, hxy]
      rw [e1] at Dex
      rw [Dex, e2] at Dx
      exact (List.nodup_cons.1 U').1 (by rw [Dx]; simp)
  · have dEx : x ∈ G.diskE r := ((G.diskE_edge hG.planar hr) x _ rfl).2 dEex
    exact dEx.2 r_x

/-- math-comp `diskN_rev_ring`: the disk of the reverse ring of a proper ring `r` is the
complement of the disk of `r`. -/
theorem diskN_rev_ring (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) (nt_r : G.ProperRing r) :
    G.diskN (G.revRing r) = (G.diskN r)ᶜ := by
  have hpl := hG.plain
  have hrr := G.scycle_rev_ring hG hr
  obtain ⟨y0, r_y0⟩ := G.pick_in_ring nt_r
  have key : ∀ (p : List D) (x : D), path G.clink x p → G.edge (last x p) ∈ r →
      (x ∈ G.diskN (G.revRing r) ↔ x ∉ G.diskN r) := by
    intro p
    induction p with
    | nil =>
      intro x _ r_ex
      rw [last_nil] at r_ex
      have h := G.diskN_edge_ring hG hr nt_r r_ex
      rw [G.plain_eq hpl] at h
      exact iff_of_true (G.mem_diskN_of_mem _ ((G.mem_rev_ring hG).2 r_ex)) h
    | cons y p ih =>
      intro x xCp r_el
      obtain ⟨xCy, yCp⟩ := xCp
      have ihy := ih y yCp (by rwa [last_cons] at r_el)
      rcases xCy with rfl | fxy
      · rw [← (G.diskN_node _) y _ rfl, ← (G.diskN_node r) y _ rfl]
        exact ihy
      · rw [G.diskN_E (G.revRing r) x, G.mem_rev_ring hG]
        by_cases r_ex : G.edge x ∈ r
        · have h := G.diskN_edge_ring hG hr nt_r r_ex
          rw [G.plain_eq hpl] at h
          exact iff_of_true (Or.inl r_ex) h
        · have hex : G.edge x = G.node y := by rw [← fxy, G.plain_eq' hpl]
          have hN : ∀ s, G.edge x ∈ G.diskN s ↔ y ∈ G.diskN s := fun s => by
            rw [hex]
            exact ((G.diskN_node s) y _ rfl).symm
          have hEr : x ∈ G.diskE r ↔ G.edge x ∈ G.diskN r := by
            rw [(G.diskE_edge hG.planar hr) x _ rfl]
            exact ⟨fun h => h.1, fun h => ⟨h, r_ex⟩⟩
          have hErr :
              x ∈ G.diskE (G.revRing r) ↔ G.edge x ∈ G.diskN (G.revRing r) ∧ x ∉ r := by
            rw [(G.diskE_edge hG.planar hrr) x _ rfl]
            show (G.edge x ∈ G.diskN _ ∧ G.edge x ∉ G.revRing r) ↔ _
            rw [G.mem_rev_ring hG, G.plain_eq hpl]
          rw [G.diskN_E r x, hEr, hErr, hN, hN, ihy]
          tauto
  ext x
  obtain ⟨p, xCp, hlast⟩ := G.connected_clink hG.connected x (G.edge y0)
  exact key p x xCp (by rw [hlast, G.plain_eq hpl]; exact r_y0)

/-- math-comp `diskF_rev_ring`. -/
theorem diskF_rev_ring (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) (nt_r : G.ProperRing r) :
    G.diskF (G.revRing r) = (G.diskN r)ᶜ \ G.fband r := by
  rw [diskF, G.diskN_rev_ring hG hr nt_r, G.fband_rev_ring hG hr]

/-- The outer face disk of the reverse ring of a proper ring `r` is the inner face disk of `r`
(the dual of `diskF_rev_ring`; not in math-comp). -/
theorem diskFC_rev_ring (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) (nt_r : G.ProperRing r) :
    G.diskFC (G.revRing r) = G.diskF r := by
  rw [diskFC, G.diskN_rev_ring hG hr nt_r, G.fband_rev_ring hG hr, compl_compl, diskF]

/-- math-comp `chord_ring r x`: the ring consisting of `x` followed by a portion of `r`, when
`x` is a "chord" of `r`, linking two faces of `r` (both `x` and `edge x` are in `fband r`):
`x :: arc r (fproj r (edge x)) (fproj r x)`. -/
noncomputable def chordRing (r : List D) (x : D) : List D :=
  x :: arc r (G.fproj r (G.edge x)) (G.fproj r x)

/-- math-comp `scycle_chord_ring`. -/
theorem scycle_chord_ring (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) {x : D} (rFx : x ∈ G.fband r) (rFex : G.edge x ∈ G.fband r) :
    G.SCycle G.rlink (G.chordRing r x) := by
  obtain ⟨r_y1, xFy1⟩ := G.fprojP rFx
  obtain ⟨r_y2, exFy2⟩ := G.fprojP rFex
  have neq : G.fproj r (G.edge x) ≠ G.fproj r x := by
    intro h
    apply hG.bridgeless
    exact ⟨x, connect_trans xFy1 (G.cfaceC.1 (h ▸ exFy2))⟩
  obtain ⟨i, p1, p2, h1, -, hrot⟩ := rot_to_arc (G.scycle_uniq hr) r_y2 r_y1 neq
  have hcr : G.chordRing r x = x :: G.fproj r (G.edge x) :: p1 := by rw [chordRing, ← h1]
  rw [hcr]
  obtain ⟨j, hj⟩ := exists_rotate_of_rot i r
  have hcyc := (cycle_rotate j r).2 hr.1
  have hsim := (G.simple_rot j r).2 hr.2
  rw [← hj, hrot] at hcyc hsim
  set y1 := G.fproj r x
  set y2 := G.fproj r (G.edge x)
  rw [List.cons_append, cycle_cons, List.append_assoc, path_append, List.cons_append,
    path_cons] at hcyc
  obtain ⟨y2p1, p1y1, -⟩ := hcyc
  obtain ⟨-, hdisj, -⟩ := (G.simple_cat _ _).1 hsim
  have hsim1 : G.Simple (y2 :: p1) := ((G.simple_cat _ _).1 hsim).1
  refine ⟨?_, ?_⟩
  · show path G.rlink x ((y2 :: p1) ++ [x])
    rw [List.cons_append, path_cons, path_concat]
    exact ⟨exFy2, y2p1, connect_trans p1y1 (G.cfaceC.1 xFy1)⟩
  · rw [G.simple_cons]
    refine ⟨fun ⟨w, hw, xFw⟩ => hdisj ⟨y1, List.mem_cons_self, w, hw, ?_⟩, hsim1⟩
    exact connect_trans (G.cfaceC.1 xFy1) xFw

/-- The two arcs cut by a chord `x` of `r` (the section `Let`s `x1`, `x2`, `r1`, `r2`, `ix`,
`Dr`, `Dr1`, `Dr2`, `Dcr1`, `Dcr2` of math-comp): a rotation of `r` is `r1 ++ r2`, with
`r1 = fproj r x :: p1` and `r2 = fproj r (edge x) :: p2`, and the chord rings of `x` and
`edge x` are `x :: r2` and `edge x :: r1`. -/
private theorem chord_split (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) {x : D} (rFx : x ∈ G.fband r) (rFex : G.edge x ∈ G.fband r) :
    ∃ j p1 p2, r.rotate j = (G.fproj r x :: p1) ++ (G.fproj r (G.edge x) :: p2) ∧
      G.chordRing r x = x :: G.fproj r (G.edge x) :: p2 ∧
      G.chordRing r (G.edge x) = G.edge x :: G.fproj r x :: p1 := by
  obtain ⟨r_x1, xFx1⟩ := G.fprojP rFx
  obtain ⟨r_x2, exFx2⟩ := G.fprojP rFex
  have neq : G.fproj r x ≠ G.fproj r (G.edge x) := by
    intro h
    apply hG.bridgeless
    exact ⟨x, connect_trans xFx1 (h ▸ G.cfaceC.1 exFx2)⟩
  obtain ⟨i, p1, p2, h1, h2, hrot⟩ := rot_to_arc (G.scycle_uniq hr) r_x1 r_x2 neq
  obtain ⟨j, hj⟩ := exists_rotate_of_rot i r
  refine ⟨j, p1, p2, by rw [← hj]; exact hrot, ?_, ?_⟩
  · rw [chordRing, ← h2]
  · rw [chordRing, G.plain_eq hG.plain, ← h1]

/-- math-comp `proper_chord_ring`. -/
theorem proper_chord_ring (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) {x : D} (dEx : x ∈ G.diskE r) (rFx : x ∈ G.fband r)
    (rFex : G.edge x ∈ G.fband r) : G.ProperRing (G.chordRing r x) := by
  obtain ⟨j, p1, p2, -, hc1, -⟩ := G.chord_split hG hr rFx rFex
  rw [hc1]
  cases p2 with
  | cons z p => trivial
  | nil =>
    show G.edge x ≠ G.fproj r (G.edge x)
    intro h
    have dEex : G.edge x ∈ G.diskE r := ((G.diskE_edge hG.planar hr) x _ rfl).1 dEx
    exact dEex.2 (h ▸ (G.fprojP rFex).1)

/-- The invariant of the proof of `diskN_chord_ring`: a dart lies in exactly one of the disks
`N1`, `N2` iff it lies in `N` (math-comp `(y \in diskN cr1) + (y \in diskN cr2) =
(y \in diskN r)`). -/
private def ChordInv (N1 N2 N : Set D) (w : D) : Prop :=
  (w ∈ N1 ∨ w ∈ N2 ↔ w ∈ N) ∧ ¬ (w ∈ N1 ∧ w ∈ N2)

omit [Fintype D] [DecidableEq D] in
/-- The propositional core of the E-step of the proof of `diskN_chord_ring`, for a dart `w`
off the ring: `A1`, `A2`, `R1`, `R2`, `NR`, `Rr` stand for `edge w ∈ diskE cr1`,
`edge w ∈ diskE cr2`, `edge w ∈ r1`, `edge w ∈ r2`, `edge w ∈ diskN r` and
`edge w ∈ r`. -/
private theorem chordInv_step {A1 A2 R1 R2 NR Rr : Prop} (e1 : R2 → ¬ A1) (e2 : R1 → ¬ A2)
    (er : Rr ↔ R1 ∨ R2) (dj : R1 → ¬ R2) (rN : Rr → NR)
    (IH : ((R2 ∨ A1) ∨ (R1 ∨ A2) ↔ NR) ∧ ¬ ((R2 ∨ A1) ∧ (R1 ∨ A2))) :
    (A1 ∨ A2 ↔ NR ∧ ¬ Rr) ∧ ¬ (A1 ∧ A2) := by
  tauto

omit [Fintype D] [DecidableEq D] in
/-- Reading `diskN_chord_ring` off the invariant `ChordInv`. -/
private theorem chordInv_iff {a b c : Prop} (h : (a ∨ b ↔ c) ∧ ¬ (a ∧ b)) :
    a ↔ c ∧ ¬ b := by
  tauto

/-- math-comp `diskN_chord_ring`: a chord `x` of a proper ring `r` splits the disk of `r` into
the disks of `chord_ring r x` and `chord_ring r (edge x)`. -/
theorem diskN_chord_ring (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) (nt_r : G.ProperRing r) {x : D} (dEx : x ∈ G.diskE r)
    (rFx : x ∈ G.fband r) (rFex : G.edge x ∈ G.fband r) :
    G.diskN (G.chordRing r x) = G.diskN r \ G.diskN (G.chordRing r (G.edge x)) := by
  have hpl := hG.plain
  have hcr1 := G.scycle_chord_ring hG hr rFx rFex
  have hcr2 := G.scycle_chord_ring hG hr rFex (by rwa [G.plain_eq hpl])
  obtain ⟨j, p1, p2, hrot, hc1, hc2⟩ := G.chord_split hG hr rFx rFex
  set cr1 := G.chordRing r x
  set cr2 := G.chordRing r (G.edge x)
  set r1 := G.fproj r x :: p1
  set r2 := G.fproj r (G.edge x) :: p2
  have Ur := G.scycle_uniq hr
  have Dr12 : ∀ w, w ∈ r ↔ w ∈ r1 ∨ w ∈ r2 := fun w => by
    rw [← List.mem_rotate (n := j), hrot, List.mem_append]
  have Ur12 : (r1 ++ r2).Nodup := hrot ▸ List.nodup_rotate.2 Ur
  have disj : ∀ w, w ∈ r1 → w ∉ r2 := fun w h1 h2 =>
    List.disjoint_of_nodup_append Ur12 h1 h2
  have mem1 : ∀ w, w ∈ cr1 ↔ w = x ∨ w ∈ r2 := fun w => by rw [hc1, List.mem_cons]
  have mem2 : ∀ w, w ∈ cr2 ↔ w = G.edge x ∨ w ∈ r1 := fun w => by rw [hc2, List.mem_cons]
  have hE1 : ∀ w, w ∈ G.diskE cr1 ↔ G.edge w ∈ G.diskE cr1 := fun w =>
    (G.diskE_edge hG.planar hcr1) w _ rfl
  have hE2 : ∀ w, w ∈ G.diskE cr2 ↔ G.edge w ∈ G.diskE cr2 := fun w =>
    (G.diskE_edge hG.planar hcr2) w _ rfl
  have hEr : ∀ w, w ∈ G.diskE r ↔ G.edge w ∈ G.diskE r := fun w =>
    (G.diskE_edge hG.planar hr) w _ rfl
  have r'x : x ∉ r := dEx.2
  have dEex : G.edge x ∈ G.diskE r := (hEr x).1 dEx
  have r'ex : G.edge x ∉ r := dEex.2
  have e'id : G.edge x ≠ x := G.plain_neq hpl x
  have hN : ∀ s w, w ∈ G.diskN s ↔ w ∈ s ∨ w ∈ G.diskE s := fun s w => G.diskN_E s w
  -- the invariant holds at `x` and at `edge x`
  have Px : ChordInv (G.diskN cr1) (G.diskN cr2) (G.diskN r) x := by
    have a : x ∈ G.diskN cr1 := G.mem_diskN_of_mem cr1 ((mem1 x).2 (Or.inl rfl))
    have b : x ∉ G.diskN cr2 := by
      rw [hN, mem2, not_or, hE2]
      refine ⟨?_, fun h => h.2 ((mem2 _).2 (Or.inl rfl))⟩
      rintro (h | h)
      · exact e'id h.symm
      · exact r'x ((Dr12 x).2 (Or.inl h))
    exact ⟨iff_of_true (Or.inl a) dEx.1, fun h => b h.2⟩
  have Pex : ChordInv (G.diskN cr1) (G.diskN cr2) (G.diskN r) (G.edge x) := by
    have b : G.edge x ∈ G.diskN cr2 := G.mem_diskN_of_mem cr2 ((mem2 _).2 (Or.inl rfl))
    have a : G.edge x ∉ G.diskN cr1 := by
      rw [hN, mem1, not_or, ← hE1]
      refine ⟨?_, fun h => h.2 ((mem1 _).2 (Or.inl rfl))⟩
      rintro (h | h)
      · exact e'id h
      · exact r'ex ((Dr12 _).2 (Or.inr h))
    exact ⟨iff_of_true (Or.inr b) dEex.1, fun h => a h.1⟩
  -- the invariant is preserved by N-links
  have Pnode : ∀ w, ChordInv (G.diskN cr1) (G.diskN cr2) (G.diskN r) (G.node w) ↔
      ChordInv (G.diskN cr1) (G.diskN cr2) (G.diskN r) w := by
    intro w
    unfold ChordInv
    rw [← (G.diskN_node cr1) w _ rfl, ← (G.diskN_node cr2) w _ rfl,
      ← (G.diskN_node r) w _ rfl]
  -- the invariant is preserved by (reverse) E-links
  have Pedge : ∀ w, ChordInv (G.diskN cr1) (G.diskN cr2) (G.diskN r) (G.edge w) →
      ChordInv (G.diskN cr1) (G.diskN cr2) (G.diskN r) w := by
    intro w IH
    by_cases hwex : w = G.edge x
    · rw [hwex]
      exact Pex
    by_cases hwx : w = x
    · rw [hwx]
      exact Px
    by_cases hw : w ∈ r
    · have h1 : G.edge w ∉ G.diskN r := G.diskN_edge_ring hG hr nt_r hw
      have hwN : w ∈ G.diskN r := G.mem_diskN_of_mem r hw
      obtain ⟨ih1, -⟩ := IH
      have ne1 : G.edge w ∉ G.diskN cr1 := fun h => h1 (ih1.1 (Or.inl h))
      have ne2 : G.edge w ∉ G.diskN cr2 := fun h => h1 (ih1.1 (Or.inr h))
      have a : w ∈ G.diskN cr1 ↔ w ∈ r2 := by
        rw [hN, mem1, hE1]
        constructor
        · rintro ((h | h) | h)
          · exact absurd h hwx
          · exact h
          · exact absurd h.1 ne1
        · intro h
          exact Or.inl (Or.inr h)
      have b : w ∈ G.diskN cr2 ↔ w ∈ r1 := by
        rw [hN, mem2, hE2]
        constructor
        · rintro ((h | h) | h)
          · exact absurd h hwex
          · exact h
          · exact absurd h.1 ne2
        · intro h
          exact Or.inl (Or.inr h)
      have c := (Dr12 w).1 hw
      have d := disj w
      unfold ChordInv
      rw [a, b]
      exact ⟨iff_of_true c.symm hwN, fun ⟨h2, h1⟩ => d h1 h2⟩
    · have r1'w : w ∉ r1 := fun h => hw ((Dr12 w).2 (Or.inl h))
      have r2'w : w ∉ r2 := fun h => hw ((Dr12 w).2 (Or.inr h))
      have a : w ∈ G.diskN cr1 ↔ G.edge w ∈ G.diskE cr1 := by
        rw [hN, mem1, hE1, or_iff_right]
        rintro (h | h)
        exacts [hwx h, r2'w h]
      have b : w ∈ G.diskN cr2 ↔ G.edge w ∈ G.diskE cr2 := by
        rw [hN, mem2, hE2, or_iff_right]
        rintro (h | h)
        exacts [hwex h, r1'w h]
      have c : w ∈ G.diskN r ↔ G.edge w ∈ G.diskN r ∧ G.edge w ∉ r := by
        rw [hN, hEr]
        exact ⟨fun h => h.resolve_left hw, Or.inr⟩
      have hewx : G.edge w ≠ x := fun h => hwex (by rw [← h, G.plain_eq hpl])
      have hewex : G.edge w ≠ G.edge x := fun h => hwx (G.edgeI h)
      have a' : G.edge w ∈ G.diskN cr1 ↔ G.edge w ∈ r2 ∨ G.edge w ∈ G.diskE cr1 := by
        rw [hN, mem1, or_assoc, or_iff_right hewx]
      have b' : G.edge w ∈ G.diskN cr2 ↔ G.edge w ∈ r1 ∨ G.edge w ∈ G.diskE cr2 := by
        rw [hN, mem2, or_assoc, or_iff_right hewex]
      have e1 : G.edge w ∈ r2 → G.edge w ∉ G.diskE cr1 := fun h h' =>
        h'.2 ((mem1 _).2 (Or.inr h))
      have e2 : G.edge w ∈ r1 → G.edge w ∉ G.diskE cr2 := fun h h' =>
        h'.2 ((mem2 _).2 (Or.inr h))
      have er := Dr12 (G.edge w)
      have dj := disj (G.edge w)
      have rN : G.edge w ∈ r → G.edge w ∈ G.diskN r := G.mem_diskN_of_mem r
      unfold ChordInv at IH ⊢
      rw [a, b, c]
      rw [a', b'] at IH
      exact chordInv_step e1 e2 er dj rN IH
  -- the invariant holds everywhere, since `G` is connected
  have Pall : ∀ w, ChordInv (G.diskN cr1) (G.diskN cr2) (G.diskN r) w := by
    intro w
    have hc : connect G.clink x w := by
      obtain ⟨p, hp, hl⟩ := G.connected_clink hG.connected x w
      exact connect_iff_path.2 ⟨p, hp, hl⟩
    induction hc with
    | refl => exact Px
    | @tail z y _ hzy ih =>
      rcases hzy with rfl | hfy
      · exact (Pnode y).1 ih
      · have hz : z = G.edge (G.node y) := by rw [← hfy, G.plain_eq' hpl, G.plain_eq hpl]
        rw [hz] at ih
        exact (Pnode y).1 (Pedge _ ih)
  ext w
  rw [Set.mem_sdiff]
  exact chordInv_iff (Pall w)

/-- math-comp `fband_chord_ring`. -/
theorem fband_chord_ring (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) {x : D} (rFx : x ∈ G.fband r) (rFex : G.edge x ∈ G.fband r) :
    G.fband (G.chordRing r x) ∪ G.fband (G.chordRing r (G.edge x)) = G.fband r := by
  obtain ⟨j, p1, p2, hrot, hc1, hc2⟩ := G.chord_split hG hr rFx rFex
  have key : ∀ y, y ∈ G.fband r ↔
      y ∈ G.fband (G.fproj r x :: p1) ∨ y ∈ G.fband (G.fproj r (G.edge x) :: p2) := by
    intro y
    rw [← G.fband_rot j r, hrot, G.fband_cat]
  ext y
  rw [Set.mem_union, hc1, hc2, G.fband_cons x, G.fband_cons (G.edge x), key]
  have h1 : G.cface y x → y ∈ G.fband r := fun h => ((G.fbandF r).connect_iff h).2 rFx
  have h2 : G.cface y (G.edge x) → y ∈ G.fband r := fun h => ((G.fbandF r).connect_iff h).2 rFex
  rw [key] at h1 h2
  constructor
  · rintro ((h | h) | (h | h))
    · exact h1 h
    · exact Or.inr h
    · exact h2 h
    · exact Or.inl h
  · rintro (h | h)
    · exact Or.inr (Or.inr h)
    · exact Or.inl (Or.inr h)

/-- math-comp `diskF_chord_ring`. -/
theorem diskF_chord_ring (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) (nt_r : G.ProperRing r) {x : D} (dEx : x ∈ G.diskE r)
    (rFx : x ∈ G.fband r) (rFex : G.edge x ∈ G.fband r) :
    G.diskF (G.chordRing r x) = G.diskF r \ G.diskF (G.chordRing r (G.edge x)) := by
  have hN := G.diskN_chord_ring hG hr nt_r dEx rFx rFex
  have hF := G.fband_chord_ring hG hr rFx rFex
  ext y
  constructor
  · intro hy
    have hy' := hy
    rw [diskF, hN] at hy'
    refine ⟨⟨hy'.1.1, fun hb => ?_⟩, fun h2 => hy'.1.2 h2.1⟩
    rw [← hF] at hb
    rcases hb with hb | ⟨z, hz, yFz⟩
    · exact hy'.2 hb
    · have hz' : z ∈ G.diskF (G.chordRing r x) := ((G.diskF_face _).connect_iff yFz).1 hy
      have hzN : z ∈ G.diskN (G.chordRing r x) := hz'.1
      rw [hN] at hzN
      exact hzN.2 (G.mem_diskN_of_mem _ hz)
  · rintro ⟨⟨dNy, rF'y⟩, h2⟩
    have rF1 : y ∉ G.fband (G.chordRing r x) := fun h => rF'y (hF ▸ Set.mem_union_left _ h)
    have rF2 : y ∉ G.fband (G.chordRing r (G.edge x)) := fun h =>
      rF'y (hF ▸ Set.mem_union_right _ h)
    refine ⟨?_, rF1⟩
    rw [hN]
    exact ⟨dNy, fun h => h2 ⟨h, rF2⟩⟩

/-- math-comp `nontrivial_chord_ring`: if the chord `x` does not cut off a single ring dart
(`fproj r (edge x) ≠ next r (fproj r x)`) and `diskF (chord_ring r x)` is non-empty, then
`chord_ring r x` is a nontrivial ring, shorter than `r`. -/
theorem nontrivial_chord_ring (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) (nt_r : G.ProperRing r) {x : D} (dEx : x ∈ G.diskE r)
    (rFx : x ∈ G.fband r) (rFex : G.edge x ∈ G.fband r)
    (h12 : G.fproj r (G.edge x) ≠ next r (G.fproj r x))
    (hF : ∃ y, y ∈ G.diskF (G.chordRing r x)) :
    G.NontrivialRing 0 (G.chordRing r x) ∧ (G.chordRing r x).length < r.length := by
  obtain ⟨j, p1, p2, hrot, hc1, hc2⟩ := G.chord_split hG hr rFx rFex
  have Ur := G.scycle_uniq hr
  obtain ⟨r_x1, xFx1⟩ := G.fprojP rFx
  have hnext := next_rotate Ur j (G.fproj r x)
  rw [hrot] at hnext
  cases p1 with
  | nil =>
    exfalso
    apply h12
    rw [← hnext]
    simp [next, nextAt]
  | cons x3 p1 =>
    have hlen : r.length = p1.length + p2.length + 3 := by
      rw [← List.length_rotate r j, hrot]
      simp only [List.length_append, List.length_cons]
      omega
    refine ⟨?_, by rw [hc1, hlen]; simp⟩
    rw [G.nontrivial0P]
    refine ⟨hF, x3, ?_, ?_⟩
    · rw [G.diskN_chord_ring hG hr nt_r dEx rFx rFex]
      exact fun h => h.2 (G.mem_diskN_of_mem _ (by rw [hc2]; simp))
    · have U' := hrot ▸ List.nodup_rotate.2 Ur
      rw [List.cons_append, List.nodup_cons, List.cons_append, List.nodup_cons] at U'
      obtain ⟨hx1, hx3, -⟩ := U'
      have hx13 : x3 ≠ G.fproj r x := fun h => hx1 (by rw [h]; simp)
      have hx3r2 : x3 ∉ G.fproj r (G.edge x) :: p2 := fun h => hx3 (List.mem_append_right _ h)
      have r_x3 : x3 ∈ r := by
        rw [← List.mem_rotate (n := j), hrot]
        simp
      have hr2 : ∀ w, w ∈ G.fproj r (G.edge x) :: p2 → w ∈ r := fun w h => by
        rw [← List.mem_rotate (n := j), hrot]
        exact List.mem_append_right _ h
      rw [hc1, G.fband_cons]
      rintro (h | ⟨y, hy, h⟩)
      · exact hx13 (G.scycle_cface hr _ r_x3 _ r_x1 (connect_trans h xFx1))
      · exact hx3r2 (by rw [G.scycle_cface hr _ r_x3 _ (hr2 y hy) h]; exact hy)

end RingPartitions

/-! ### Nontrivial rings (math-comp section `NonTrivialRing`)

For a nontrivial ring `r` (`nt_r : G.NontrivialRing m r`), we compare the disk map
`snip_disk r` with the remainder map of the reverse ring `rev_snipr_disk r`: their borders have
the same colorings (`rev_ring_cotrace`), so that the ring traces of the disk map are Kempe closed
when `G` is cubic (`ring_disk_closed`), and `G` is colorable as soon as the two disk maps of `r`
and of `rev_ring r` have matching ring traces (`colorable_from_ring`). Finally a chord in the
disk map yields a shorter nontrivial ring (`ring_disk_chord`). -/

section NonTrivialRing

variable {D : Type u} (G : Hypermap D)

/-- The color of the face of `x` in a coloring `k` of a map projected on `G` by `h`:
`k y` for some `y` with `x` and `h y` in the same face of `G`, or `Color0` if there is none
(the math-comp `oapp k Color0 (pick (preim h (cface x)))` of `rev_ring_cotrace`). -/
private noncomputable def liftCol {D' : Type*} (h : D' → D) (k : D' → Color) (x : D) : Color :=
  open Classical in if hx : ∃ y, G.cface x (h y) then k (Classical.choose hx) else Color0

variable [Fintype D]

/-- The value of `liftCol` (math-comp local `pfdP`, `pfrrP`). -/
private theorem liftCol_eq {D' : Type*} {h : D' → D} {k : D' → Color}
    (hk : ∀ y y', G.cface (h y) (h y') → k y = k y') {x : D} {y : D'} (hxy : G.cface x (h y)) :
    G.liftCol h k x = k y := by
  have hx : ∃ y, G.cface x (h y) := ⟨y, hxy⟩
  rw [liftCol, dite_eq_left hx]
  exact hk _ _ (connect_trans (G.cfaceC.1 (Classical.choose_spec hx)) hxy)

/-- `liftCol` is constant on the faces of `G`. -/
private theorem liftCol_cface {D' : Type*} {h : D' → D} {k : D' → Color}
    (hk : ∀ y y', G.cface (h y) (h y') → k y = k y') {x x' : D} (hxx' : G.cface x x') :
    G.liftCol h k x = G.liftCol h k x' := by
  by_cases hx : ∃ y, G.cface x (h y)
  · obtain ⟨y, hxy⟩ := hx
    rw [G.liftCol_eq hk hxy, G.liftCol_eq hk (connect_trans (G.cfaceC.1 hxx') hxy)]
  · have hx' : ¬ ∃ y, G.cface x' (h y) := fun ⟨y, hy⟩ => hx ⟨y, connect_trans hxx' hy⟩
    rw [liftCol, liftCol, dite_eq_right hx, dite_eq_right hx']

/-- Colorings that agree on the face roots of two sequences agree on the sequences. -/
private theorem map_eq_of_froot {A B : Type*} {f : A → D} {g : B → D} {k1 : A → Color}
    {k2 : B → Color} (hk : ∀ a b, G.cface (f a) (g b) → k1 a = k2 b) :
    ∀ (pa : List A) (pb : List B),
      (pa.map f).map (froot G.face) = (pb.map g).map (froot G.face) → pa.map k1 = pb.map k2
  | [], [], _ => rfl
  | a :: pa, b :: pb, h => by
    simp only [List.map_cons, List.cons.injEq] at h ⊢
    exact ⟨hk a b ((G.froot_face_eq_iff).1 h.1), map_eq_of_froot hk pa pb h.2⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- math-comp `nontrivial_ring_proper`: a nontrivial ring is proper. -/
theorem nontrivial_ring_proper (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) {m : ℕ} (nt_r : G.NontrivialRing m r) : G.ProperRing r := by
  obtain ⟨ntF, ntFC⟩ := nt_r
  match r, hr, ntF, ntFC with
  | [], _, ntF, _ =>
    exfalso
    have h0 : G.diskF [] = ∅ := by
      ext y
      simp [diskF, diskN]
    simp [h0] at ntF
  | [x], hr, _, _ =>
    exact G.bridgeless_cface hG.bridgeless x (G.cfaceC.1 hr.1.1)
  | [x, y], hr, _, ntFC =>
    show G.edge x ≠ y
    rintro rfl
    have hpl := hG.plain
    have rx : x ∈ [x, G.edge x] := List.mem_cons_self
    have hall : ∀ w, w ∈ G.diskN [x, G.edge x] := by
      intro w
      have hc : connect G.clink x w := by
        obtain ⟨p, hp, hl⟩ := G.connected_clink hG.connected x w
        exact connect_iff_path.2 ⟨p, hp, hl⟩
      induction hc with
      | refl => exact G.mem_diskN_of_mem _ rx
      | @tail z w _ hzw ih =>
        rcases hzw with rfl | hfz
        · exact ((G.diskN_node _) w _ rfl).2 ih
        · rw [(G.diskN_node _) w _ rfl, ← hfz, G.plain_eq' hpl]
          by_cases hz : z ∈ [x, G.edge x]
          · apply G.mem_diskN_of_mem
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
            rcases hz with rfl | rfl
            · exact Or.inr rfl
            · exact Or.inl (G.plain_eq hpl _)
          · exact (((G.diskE_edge hG.planar hr) z _ rfl).1 ⟨ih, hz⟩).1
    have h0 : G.diskFC [x, G.edge x] = ∅ := by
      ext w
      exact iff_of_false (fun h => h.1 (hall w)) (Set.notMem_empty w)
    simp [h0] at ntFC
  | _ :: _ :: _ :: _, _, _, _ => trivial

variable [DecidableEq D]

/-- math-comp `nontrivial_rev_ring`. -/
theorem nontrivial_rev_ring (hG : G.PlanarBridgelessPlainConnected) {r : List D}
    (hr : G.SCycle G.rlink r) {m : ℕ} (nt_r : G.NontrivialRing m r) :
    G.NontrivialRing m (G.revRing r) := by
  have r_ok := G.nontrivial_ring_proper hG hr nt_r
  refine ⟨?_, ?_⟩
  · rw [G.diskF_rev_ring hG hr r_ok]
    exact nt_r.2
  · rw [G.diskFC_rev_ring hG hr r_ok]
    exact nt_r.1

/-- math-comp `rev_snipd_disk`: the disk map obtained by cutting `G` along `rev_ring r`, whose
darts are the exact complement of `diskN r` (for a proper ring `r`, by `diskN_rev_ring`). -/
abbrev revSnipdDisk (hG : G.PlanarBridgelessPlainConnected) (hGp : G.Planar) {r : List D}
    (hr : G.SCycle G.rlink r) : Hypermap (G.SnipdDart (G.revRing r)) :=
  G.snipDisk hGp (G.scycle_rev_ring hG hr)

/-- math-comp `rev_snipr_disk`: the remainder map obtained by cutting `G` along
`rev_ring r`. -/
abbrev revSniprDisk (hG : G.PlanarBridgelessPlainConnected) (hGp : G.Planar) {r : List D}
    (hr : G.SCycle G.rlink r) : Hypermap (G.SniprDart (G.revRing r)) :=
  G.snipRem hGp (G.scycle_rev_ring hG hr)

/-- math-comp `rev_snipd_ring`: the border ring of `rev_snipd_disk`. -/
noncomputable abbrev revSnipdRing (r : List D) : List (G.SnipdDart (G.revRing r)) :=
  G.snipdRing (G.revRing r)

/-- math-comp `rev_snipr_ring`: the border ring of `rev_snipr_disk`. -/
noncomputable abbrev revSniprRing (r : List D) : List (G.SniprDart (G.revRing r)) :=
  G.sniprRing (G.revRing r)

omit [Fintype D] [DecidableEq D] in
/-- math-comp `rev_snipr_ring_eq`. -/
theorem rev_snipr_ring_eq (r : List D) :
    (G.revSniprRing r).map (G.snipr (G.revRing r)) = r.map G.edge := by
  rw [revSniprRing, G.map_snipr_ring, revRing, List.reverse_reverse]

/-- math-comp `rev_ring_cotrace`: the border of the disk map of a nontrivial ring `r` and the
(right-rotated) border of the remainder map of `rev_ring r` have the same traces. -/
theorem rev_ring_cotrace (hG : G.PlanarBridgelessPlainConnected) (hGp : G.Planar) {r : List D}
    (hr : G.SCycle G.rlink r) {m : ℕ} (nt_r : G.NontrivialRing m r) (et : Colseq) :
    (G.snipDisk hGp hr).RingTrace (G.snipdRing r) et ↔
      (G.revSniprDisk hG hGp hr).RingTrace (rotr 1 (G.revSniprRing r)) et := by
  have hpl := hG.plain
  have r_ok := G.nontrivial_ring_proper hG hr nt_r
  have ppGr : G.Patch (G.revSnipdDisk hG hGp hr) (G.revSniprDisk hG hGp hr)
      (G.snipd (G.revRing r)) (G.snipr (G.revRing r)) (G.revSnipdRing r) (G.revSniprRing r) :=
    G.snip_patch hGp (G.scycle_rev_ring hG hr)
  have hplrr : (G.revSniprDisk hG hGp hr).Plain := (ppGr.plain_patch.1 hpl).2
  have eqFpdr : ((rotr 1 (G.revSniprRing r)).map (G.snipr (G.revRing r))).map (froot G.face) =
      ((G.snipdRing r).map (G.snipd r)).map (froot G.face) := by
    have h1 : (r.map G.edge).map (froot G.face) = rot 1 (r.map (froot G.face)) := by
      have h := G.froot_face_rev_ring hr
      rw [revRing, List.map_reverse] at h
      rw [← List.reverse_reverse ((r.map G.edge).map (froot G.face)), h, List.reverse_reverse]
    rw [map_rotr, G.rev_snipr_ring_eq, map_rotr, h1, rotK, G.map_snipd_ring]
  -- the faces of the projections of darts of the disk map, and of the remainder map
  have hkd : ∀ {kd : G.SnipdDart r → Color}, (G.snipDisk hGp hr).Coloring kd →
      ∀ y y', G.cface (G.snipd r y) (G.snipd r y') → kd y = kd y' := fun hk y y' h =>
    (G.snipDisk hGp hr).coloring_cface hk ((G.cface_snipd hGp hr y y').1 h)
  have hkr : ∀ {kr : G.SniprDart (G.revRing r) → Color},
      (G.revSniprDisk hG hGp hr).Coloring kr → ∀ y y',
        G.cface (G.snipr (G.revRing r) y) (G.snipr (G.revRing r) y') → kr y = kr y' :=
    fun hk y y' h => (G.revSniprDisk hG hGp hr).coloring_cface hk ((ppGr.patch_face_r y y').2 h)
  constructor
  · rintro ⟨kd, hkdc, rfl⟩
    have kdE := hkdc.1
    have kdF := hkdc.2
    let kr : G.SniprDart (G.revRing r) → Color := fun xr =>
      G.liftCol (G.snipd r) kd (G.snipr (G.revRing r) xr)
    have krF : ∀ xr, kr ((G.revSniprDisk hG hGp hr).face xr) = kr xr := fun xr =>
      G.liftCol_cface (hkd hkdc) (G.cfaceC.1
        ((ppGr.patch_face_r _ _).1 (fconnect1 (G.revSniprDisk hG hGp hr).face xr)))
    have krE : ∀ xr, G.snipr (G.revRing r) xr ∉ G.revRing r →
        kr ((G.revSniprDisk hG hGp hr).edge xr) ≠ kr xr := by
      intro xr hxr
      have dNx : G.snipr (G.revRing r) xr ∈ G.diskN r := by
        have h : G.snipr (G.revRing r) xr ∉ G.diskN (G.revRing r) := by
          rw [G.diskN_E]
          rintro (h | h)
          · exact hxr h
          · exact xr.2 h
        rw [G.diskN_rev_ring hG hr r_ok] at h
        exact not_not.1 h
      let xd : G.SnipdDart r := ⟨G.snipr (G.revRing r) xr, dNx⟩
      have e1 : kr xr = kd xd := G.liftCol_eq (hkd hkdc) (connect_refl _)
      have e2 : kr ((G.revSniprDisk hG hGp hr).edge xr) =
          kd ((G.snipDisk hGp hr).face ((G.snipDisk hGp hr).edge xd)) := by
        apply G.liftCol_eq (hkd hkdc)
        show G.cface (G.edge (G.snipd r xd))
          (G.snipd r ((G.snipDisk hGp hr).face ((G.snipDisk hGp hr).edge xd)))
        have hw : G.node (G.snipd r ((G.snipDisk hGp hr).face ((G.snipDisk hGp hr).edge xd))) =
            G.snipd r xd := by
          show G.snipd r ((G.snipDisk hGp hr).node
            ((G.snipDisk hGp hr).face ((G.snipDisk hGp hr).edge xd))) = _
          rw [(G.snipDisk hGp hr).edgeK]
        rw [← hw]
        have h := fconnect1 G.face (G.edge (G.node
          (G.snipd r ((G.snipDisk hGp hr).face ((G.snipDisk hGp hr).edge xd)))))
        rwa [G.nodeK] at h
      rw [e1, e2, kdF]
      exact kdE xd
    refine ⟨kr, ⟨fun xr => ?_, krF⟩, ?_⟩
    · by_cases hx : G.snipr (G.revRing r) xr ∈ G.revRing r
      · have h : G.snipr (G.revRing r) ((G.revSniprDisk hG hGp hr).edge xr) ∉ G.revRing r := by
          show G.edge (G.snipr (G.revRing r) xr) ∉ G.revRing r
          rw [G.mem_rev_ring hG, G.plain_eq hpl]
          intro h
          rw [G.mem_rev_ring hG] at hx
          have h' := G.diskN_edge_ring hG hr r_ok hx
          rw [G.plain_eq hpl] at h'
          exact h' (G.mem_diskN_of_mem r h)
        have h' := krE _ h
        rw [(G.revSniprDisk hG hGp hr).plain_eq hplrr] at h'
        exact fun e => h' e.symm
      · exact krE xr hx
    · congr 1
      exact G.map_eq_of_froot (fun a b h => (G.liftCol_eq (hkd hkdc) (G.cfaceC.1 h)).symm) _ _
        eqFpdr.symm
  · rintro ⟨kr, hkrc, rfl⟩
    obtain ⟨krE, krF⟩ := hkrc
    let kd : G.SnipdDart r → Color := fun xd =>
      G.liftCol (G.snipr (G.revRing r)) kr (G.snipd r xd)
    have kdF : ∀ xd, kd ((G.snipDisk hGp hr).face xd) = kd xd := fun xd =>
      G.liftCol_cface (hkr ⟨krE, krF⟩) (G.cfaceC.1
        ((G.cface_snipd hGp hr _ _).2 (fconnect1 (G.snipDisk hGp hr).face xd)))
    have kdE : ∀ w, kd w ≠ kd ((G.snipDisk hGp hr).node w) := by
      intro w
      have dNnx : G.node (G.snipd r w) ∈ G.diskN r := ((G.diskN_node r) _ _ rfl).1 w.2
      have hnx : G.node (G.snipd r w) ∉ G.diskE (G.revRing r) := fun h => by
        have h1 := h.1
        rw [G.diskN_rev_ring hG hr r_ok] at h1
        exact h1 dNnx
      let nxr : G.SniprDart (G.revRing r) := ⟨G.node (G.snipd r w), hnx⟩
      have e1 : kd ((G.snipDisk hGp hr).node w) = kr nxr :=
        G.liftCol_eq (hkr ⟨krE, krF⟩) (connect_refl _)
      have e2 : kd w = kr ((G.revSniprDisk hG hGp hr).edge nxr) := by
        apply G.liftCol_eq (hkr ⟨krE, krF⟩)
        show G.cface (G.snipd r w) (G.edge (G.node (G.snipd r w)))
        have h := fconnect1 G.face (G.edge (G.node (G.snipd r w)))
        rw [G.nodeK] at h
        exact G.cfaceC.1 h
      rw [e1, e2]
      exact krE nxr
    refine ⟨kd, ⟨fun xd => ?_, kdF⟩, ?_⟩
    · have h := kdE ((G.snipDisk hGp hr).face ((G.snipDisk hGp hr).edge xd))
      rwa [(G.snipDisk hGp hr).edgeK, kdF] at h
    · congr 1
      exact G.map_eq_of_froot (fun a b h => (G.liftCol_eq (hkr ⟨krE, krF⟩) (G.cfaceC.1 h)).symm)
        _ _ eqFpdr

/-- math-comp `ring_disk_closed`: if `G` is cubic, the ring traces of the disk map of a
nontrivial ring are Kempe closed. -/
theorem ring_disk_closed (hG : G.PlanarBridgelessPlainConnected) (hGp : G.Planar) {r : List D}
    (hr : G.SCycle G.rlink r) {m : ℕ} (nt_r : G.NontrivialRing m r) (hcub : G.Cubic) :
    KempeClosed ((G.snipDisk hGp hr).RingTrace (G.snipdRing r)) := by
  have ppGr : G.Patch (G.revSnipdDisk hG hGp hr) (G.revSniprDisk hG hGp hr)
      (G.snipd (G.revRing r)) (G.snipr (G.revRing r)) (G.revSnipdRing r) (G.revSniprRing r) :=
    G.snip_patch hGp (G.scycle_rev_ring hG hr)
  have hP : (G.snipDisk hGp hr).RingTrace (G.snipdRing r) =
      (G.revSniprDisk hG hGp hr).RingTrace (rotr 1 (G.revSniprRing r)) :=
    funext fun et => propext (G.rev_ring_cotrace hG hGp hr nt_r et)
  rw [hP]
  apply kempe_map
  have hcyc := ppGr.cycle_r
  exact
    { plain := (ppGr.plain_patch.1 hG.plain).2
      quasicubic := fun x hx => (ppGr.cubic_patch.1 hcub).2 fun h => hx (mem_rotr.2 h)
      ucycle := ⟨by
          rw [rotr, rot_eq_rotate (Nat.sub_le _ _)]
          exact (cycle_rotate _ _).2 hcyc.1, nodup_rotr.2 hcyc.2⟩
      planar := G.planar_snipr hGp (G.scycle_rev_ring hG hr) }

/-- math-comp `colorable_from_ring`: `G` is four colorable if the disk maps of a nontrivial
ring `r` and of its reverse `rev_ring r` have (reversed) matching ring traces. -/
theorem colorable_from_ring (hG : G.PlanarBridgelessPlainConnected) (hGp : G.Planar)
    {r : List D} (hr : G.SCycle G.rlink r) {m : ℕ} (nt_r : G.NontrivialRing m r) {et : Colseq}
    (h1 : (G.snipDisk hGp hr).RingTrace (G.snipdRing r) et)
    (h2 : (G.revSnipdDisk hG hGp hr).RingTrace (G.revSnipdRing r) et.reverse) :
    G.FourColorable := by
  obtain ⟨kr, hkr, Det⟩ := (G.rev_ring_cotrace hG hGp hr nt_r et).1 h1
  have ppGr : G.Patch (G.revSnipdDisk hG hGp hr) (G.revSniprDisk hG hGp hr)
      (G.snipd (G.revRing r)) (G.snipr (G.revRing r)) (G.revSnipdRing r) (G.revSniprRing r) :=
    G.snip_patch hGp (G.scycle_rev_ring hG hr)
  refine ppGr.colorable_patch.2 ⟨et.reverse, h2, kr, hkr, ?_⟩
  rw [List.reverse_reverse, Det, map_rotr, ← trace_rot, rotrK]

/-- math-comp `ring_disk_chord`: if the border of the disk map of a nontrivial ring `r` has a
chord, then `G` has a shorter nontrivial ring. -/
theorem ring_disk_chord (hG : G.PlanarBridgelessPlainConnected) (hGp : G.Planar) {r : List D}
    (hr : G.SCycle G.rlink r) {m : ℕ} (nt_r : G.NontrivialRing m r)
    (hch : ¬ (G.snipDisk hGp hr).Chordless (G.snipdRing r)) :
    ∃ r', G.SCycle G.rlink r' ∧ G.NontrivialRing 0 r' ∧ r'.length < r.length := by
  have r_ok := G.nontrivial_ring_proper hG hr nt_r
  have hpl := hG.plain
  have Id := G.inj_snipd r
  have Dbd := G.map_snipd_ring r
  have Ubd : (G.snipdRing r).Nodup := (G.ucycle_snipd_ring hGp hr).2
  rw [(G.snipDisk hGp hr).chordless_iff] at hch
  push Not at hch
  obtain ⟨xd, hxd, yd, hyd, hadj, hprev, hnext⟩ := hch
  obtain ⟨zd, xFz, zRy⟩ := (G.snipDisk hGp hr).adjP.1 hadj
  have rx : G.snipd r xd ∈ r := G.mem_snipd_ring.1 hxd
  have ry : G.snipd r yd ∈ r := G.mem_snipd_ring.1 hyd
  have dNz : G.snipd r zd ∈ G.diskN r := zd.2
  have xFz' : G.cface (G.snipd r xd) (G.snipd r zd) := (G.cface_snipd hGp hr xd zd).2 xFz
  have zRy' : G.rlink (G.snipd r zd) (G.snipd r yd) := by
    have h1 : (G.snipDisk hGp hr).cface
        ((G.snipDisk hGp hr).face ((G.snipDisk hGp hr).edge zd)) yd :=
      ((G.snipDisk hGp hr).cface1 _ _).1 zRy
    have h2 := (G.cface_snipd hGp hr _ _).2 h1
    have hzw : G.node (G.snipd r ((G.snipDisk hGp hr).face ((G.snipDisk hGp hr).edge zd))) =
        G.snipd r zd := by
      show G.snipd r ((G.snipDisk hGp hr).node
        ((G.snipDisk hGp hr).face ((G.snipDisk hGp hr).edge zd))) = _
      rw [(G.snipDisk hGp hr).edgeK]
    have h3 : G.face (G.edge (G.snipd r zd)) =
        G.snipd r ((G.snipDisk hGp hr).face ((G.snipDisk hGp hr).edge zd)) := by
      rw [← hzw, G.nodeK]
    show G.cface (G.edge (G.snipd r zd)) (G.snipd r yd)
    rw [G.cface1, h3]
    exact h2
  set x := G.snipd r xd
  set y := G.snipd r yd
  set z := G.snipd r zd
  have x1'y : y ≠ next r x := by
    intro h
    apply hnext
    apply Id
    rw [← next_map Id, Dbd]
    exact h
  have y1'x : x ≠ next r y := by
    intro h
    apply hprev
    have h' : xd = next (G.snipdRing r) yd := Id (by rw [← next_map Id, Dbd]; exact h)
    rw [h', prev_next Ubd]
  have rFz : z ∈ G.fband r := ⟨x, rx, G.cfaceC.1 xFz'⟩
  have rFez : G.edge z ∈ G.fband r := ⟨y, ry, zRy'⟩
  have dEz : z ∈ G.diskE r := by
    refine ⟨dNz, fun rz => x1'y ?_⟩
    have hxz : x = z := G.scycle_cface hr _ rx _ rz xFz'
    rw [hxz]
    exact G.scycle_cface hr _ ry _ (mem_next.2 rz)
      (connect_trans (G.cfaceC.1 zRy') (next_cycle hr.1 rz))
  have dEez : G.edge z ∈ G.diskE r := ((G.diskE_edge hGp hr) z _ rfl).1 dEz
  have rFz_x : G.fproj r z = x := by rw [← G.fproj_cface r xFz', G.scycle_fproj hr x rx]
  have rFez_y : G.fproj r (G.edge z) = y := by rw [G.fproj_cface r zRy', G.scycle_fproj hr y ry]
  obtain ⟨t, dFt⟩ := (G.fcard0P (G.diskF_face r)).1 (by have := nt_r.1; omega)
  by_cases dzFt : t ∈ G.diskF (G.chordRing r z)
  · refine ⟨G.chordRing r z, G.scycle_chord_ring hG hr rFz rFez, ?_⟩
    refine G.nontrivial_chord_ring hG hr r_ok dEz rFz rFez ?_ ⟨t, dzFt⟩
    rw [rFz_x, rFez_y]
    exact x1'y
  · have dezFt : t ∈ G.diskF (G.chordRing r (G.edge z)) := by
      rw [G.diskF_chord_ring hG hr r_ok dEz rFz rFez] at dzFt
      by_contra h
      exact dzFt ⟨dFt, h⟩
    have rFeez : G.edge (G.edge z) ∈ G.fband r := by rwa [G.plain_eq hpl]
    refine ⟨G.chordRing r (G.edge z), G.scycle_chord_ring hG hr rFez rFeez, ?_⟩
    refine G.nontrivial_chord_ring hG hr r_ok dEez rFez rFeez ?_ ⟨t, dezFt⟩
    rw [G.plain_eq hpl, rFz_x, rFez_y]
    exact y1'x

end NonTrivialRing

end Hypermap

end FourColor
