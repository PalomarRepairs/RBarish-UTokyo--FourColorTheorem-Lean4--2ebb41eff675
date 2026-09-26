/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Contract

/-!
# Embeddings: the section hypotheses and shared helpers (part of the port of `embed.v`)

The math-comp section `Embeddings` of `embed.v` has the variables `Gm Gc : hypermap`,
`rc cc : seq Gc`, `h : Gc -> Gm` and the hypotheses

* `cexGm : minimal_counter_example Gm`,
* `embedGc : embeddable rc`,
* `embed_h : preembedding (kernel rc) h`,
* `Cred_cc : C_reducible rc cc`.

Here the first three are bundled in the structure `Hypermap.EmbedHyps Gm Gc rc h`; the last one
is an explicit argument of the declarations that use it (only the contract part, in
`FourColor.Embed.Contract`). The section `Let`s derived from the hypotheses (`planarGm`,
`bridge'Gm`, `e2m`, `n3m`, ..., `hcE`, `hF`, `h_spoke`) are theorems of the namespace
`Hypermap.EmbedHyps`, used with dot notation (`E.e2m x`, `E.hF hx`, ...).

The math-comp notations `ac := kernel rc`, `bc := [predC rc]` and `hc := edge_central h` are
written out: `x ∈ Gc.kernel rc`, `x ∉ rc` and `x ∈ Gc.edgeCentral Gm h`.

This file also contains the helpers shared by the parts of the port (namespace
`FourColor.Embed`; they are public because the port is split into several files, and are
namespaced to avoid clashes):

* the math-comp lemmas on `next`/`prev` (`mem_next`, `next_map`, `prev_map`, `next_rev`,
  `next_cycle`, `prev_cycle`, `cycle_from_next`, ...), private in the files that already use
  them; `cycle_mono`, `cycle_reverse` (private in `FourColor.Revsnip`), `fconnect_invariant`
  (private in `FourColor.Coloring`), `path_belast`, `mem_arc`;
* the first-item splitting `exists_first` (the math-comp idiom `find`/`nth_find`/`before_find`);
* lemmas on the disks of `FourColor.Snip` that replace the `diskE_edge` detours of the Coq proof
  of `embed_functor`: `rlink_diskN_iff`, `diskN_path`, `diskN_path_rev` and `diskN_subset`;
* `simple_split` and `fproj_eq`, for simple sequences.

It also has consequences of the face morphism property of `h` on the kernel (`ac_edge_node`,
`h_edge_node`, `h_node`) and `cface_edge_node` (`edge (node x)` is in the face of `x`).
-/

namespace FourColor

open Function

universe u v

namespace Embed

/-! ### Cyclic successor and predecessor (math-comp `path.v`)

The math-comp lemmas on `next`/`prev`; the same statements are private in `FourColor.Patch`,
`FourColor.Snip`, `FourColor.Revsnip` and `FourColor.Contract`, and are proved here in the same
way, through Mathlib's `List.next`/`List.prev`. -/

section NextPrev

variable {α β : Type*} [DecidableEq α]

/-- math-comp `next_nth` (default case): `next` fixes the points outside the sequence. -/
theorem next_of_not_mem {p : List α} {x : α} (h : x ∉ p) : next p x = x := by
  cases p with
  | nil => rfl
  | cons y p => exact nextAt_of_not_mem h

/-- math-comp `prev_nth` (default case): `prev` fixes the points outside the sequence. -/
theorem prev_of_not_mem {p : List α} {x : α} (h : x ∉ p) : prev p x = x := by
  cases p with
  | nil => rfl
  | cons y p =>
    show prevAt x y y p = x
    rw [prevAt_of_not_mem (fun hm => h (List.mem_cons_of_mem _ hm)),
      ite_eq_right (fun e => h (List.mem_cons.2 (Or.inl e)))]

/-- `next_at` agrees with Mathlib's `List.nextOr` on the items of the sequence. -/
theorem nextAt_eq_nextOr {x y0 : α} :
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
theorem next_eq_listNext {p : List α} {x : α} (hx : x ∈ p) :
    next p x = p.next x hx := by
  cases p with
  | nil => simp at hx
  | cons y p =>
    show nextAt x y y p = _
    rw [nextAt_eq_nextOr hx]
    rfl

omit [DecidableEq α] in
/-- math-comp `last` agrees with `List.getLast`. -/
theorem last_eq_getLast (z : α) (p : List α) :
    last z p = (z :: p).getLast (List.cons_ne_nil z p) := by
  induction p generalizing z with
  | nil => rfl
  | cons w p ih => rw [last_cons, ih w, List.getLast_cons_cons]

/-- `prev_at` agrees with Mathlib's `List.prev` on the tail items of a duplicate-free
sequence. -/
theorem prevAt_eq_listPrev {x y0 : α} :
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
theorem prev_eq_listPrev {p : List α} (hp : p.Nodup) {x : α} (hx : x ∈ p) :
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
theorem mem_next {p : List α} {x : α} : next p x ∈ p ↔ x ∈ p := by
  by_cases hx : x ∈ p
  · rw [next_eq_listNext hx]
    exact ⟨fun _ => hx, fun _ => List.next_mem _ _ _⟩
  · rw [next_of_not_mem hx]

/-- math-comp `prev_next`. -/
theorem prev_next {p : List α} (hp : p.Nodup) (x : α) : prev p (next p x) = x := by
  by_cases hx : x ∈ p
  · rw [prev_eq_listPrev hp (mem_next.2 hx)]
    simp only [next_eq_listNext hx]
    exact List.prev_next p hp x hx
  · rw [next_of_not_mem hx, prev_of_not_mem hx]

/-- math-comp `mem_prev`. -/
theorem mem_prev {p : List α} (hp : p.Nodup) {x : α} : prev p x ∈ p ↔ x ∈ p := by
  by_cases hx : x ∈ p
  · rw [prev_eq_listPrev hp hx]
    exact ⟨fun _ => hx, fun _ => List.prev_mem _ _ _⟩
  · rw [prev_of_not_mem hx]

/-- math-comp `next_rev`. -/
theorem next_rev {p : List α} (hp : p.Nodup) (x : α) :
    next p.reverse x = prev p x := by
  by_cases hx : x ∈ p
  · rw [next_eq_listNext (List.mem_reverse.2 hx), prev_eq_listPrev hp hx]
    exact List.next_reverse_eq_prev p hp x hx
  · rw [next_of_not_mem (fun h => hx (List.mem_reverse.1 h)), prev_of_not_mem hx]

/-- `next_at` commutes with injections (helper for math-comp `next_map`). -/
theorem nextAt_map [DecidableEq β] {f : α → β} (hf : Injective f) (x y0 : α) :
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
theorem next_map [DecidableEq β] {f : α → β} (hf : Injective f) (p : List α) (x : α) :
    next (p.map f) (f x) = f (next p x) := by
  cases p with
  | nil => rfl
  | cons y p => exact nextAt_map hf x y y p

/-- math-comp `prev_map` (for a duplicate-free sequence). -/
theorem prev_map [DecidableEq β] {f : α → β} (hf : Injective f) {p : List α} (hp : p.Nodup)
    (x : α) : prev (p.map f) (f x) = f (prev p x) := by
  rw [← next_rev (hp.map hf), ← List.map_reverse, next_map hf, next_rev hp]

/-- Helper for math-comp `next_cycle`. -/
theorem nextAt_cycle {e : α → α → Prop} {x y0 : α} :
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
theorem next_cycle {e : α → α → Prop} {p : List α} (hp : cycle e p) {x : α}
    (hx : x ∈ p) : e x (next p x) := by
  cases p with
  | nil => simp at hx
  | cons y p => exact nextAt_cycle hp hx

/-- Helper for math-comp `prev_cycle`. -/
theorem prevAt_cycle {e : α → α → Prop} {x y0 : α} :
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
theorem prev_cycle {e : α → α → Prop} {p : List α} (hp : cycle e p) {x : α}
    (hx : x ∈ p) : e (prev p x) x := by
  cases p with
  | nil => simp at hx
  | cons y p =>
    refine prevAt_cycle hp ?_
    rcases List.mem_cons.1 hx with rfl | h
    · exact List.mem_append_right _ List.mem_cons_self
    · exact List.mem_append_left _ h

/-- Helper for math-comp `cycle_from_next`. -/
theorem path_from_nextAt {e : α → α → Prop} {y0 : α} :
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
theorem cycle_from_next {e : α → α → Prop} {p : List α} (hp : p.Nodup)
    (h : ∀ x ∈ p, e x (next p x)) : cycle e p := by
  cases p with
  | nil => trivial
  | cons y p => exact path_from_nextAt hp h

end NextPrev

/-! ### Other list and graph helpers -/

/-- `cycle` is monotone in the relation (private in `FourColor.Revsnip`). -/
theorem cycle_mono {α : Type*} {e e' : α → α → Prop} (h : ∀ a b, e a b → e' a b)
    {p : List α} (hp : cycle e p) : cycle e' p := by
  cases p with
  | nil => trivial
  | cons x p => exact path.mono h hp

/-- math-comp `rev_cycle`: the reverse of an `e`-cycle is an `e`-cycle for the converse
relation (private in `FourColor.Revsnip`). -/
theorem cycle_reverse {α : Type*} {e : α → α → Prop} {p : List α} :
    cycle e p.reverse ↔ cycle (fun a b => e b a) p := by
  cases p with
  | nil => exact Iff.rfl
  | cons x q =>
    rw [List.reverse_cons, cycle_rotate_one]
    show path e x (q.reverse ++ [x]) ↔ path _ x (q ++ [x])
    have h := path_reverse (e := e) (x := x) (p := q ++ [x])
    rwa [last_concat, belast_concat, List.reverse_cons] at h

/-- Every item of `belast x l` has a successor on the path `x :: l`. -/
theorem path_belast {α : Type*} {e : α → α → Prop} :
    ∀ {x : α} {l : List α}, path e x l → ∀ z ∈ belast x l, ∃ z' ∈ l, e z z'
  | _, [], _, _, hz => absurd hz List.not_mem_nil
  | x, y :: l, ⟨xy, yl⟩, z, hz => by
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨y, List.mem_cons_self, xy⟩
    · obtain ⟨z', hz', zz'⟩ := path_belast yl z hz
      exact ⟨z', List.mem_cons_of_mem _ hz', zz'⟩

/-- The items of an arc of `p` are items of `p` (math-comp `mem_arc`-style fact). -/
theorem mem_arc {α : Type*} [DecidableEq α] {p : List α} {x y t : α} (h : t ∈ arc p x y) :
    t ∈ p := by
  simp only [arc] at h
  exact mem_rot.1 (List.mem_of_mem_take h)

/-- math-comp `fconnect_invariant`: a function invariant under `f` is constant on the
`f`-orbits (private in `FourColor.Coloring`). -/
theorem fconnect_invariant {α β : Type*} {f : α → α} {k : α → β}
    (hk : ∀ x, k (f x) = k x) {x y : α} (h : fconnect f x y) : k y = k x := by
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    subst hbc
    rw [hk, ih]

/-- The first item of a list that satisfies a predicate (the math-comp idiom
`find P l` / `nth_find` / `before_find`, as a splitting of the list). -/
theorem exists_first {α : Type*} (P : α → Prop) :
    ∀ (l : List α), (∃ t ∈ l, P t) → ∃ a b c, l = a ++ b :: c ∧ (∀ t ∈ a, ¬ P t) ∧ P b
  | [], ⟨_, ht, _⟩ => absurd ht List.not_mem_nil
  | y :: l, ⟨t, ht, hPt⟩ => by
    by_cases hy : P y
    · exact ⟨[], y, l, rfl, fun _ h => absurd h List.not_mem_nil, hy⟩
    · have ht' : t ∈ l := by
        rcases List.mem_cons.1 ht with rfl | h
        · exact absurd hPt hy
        · exact h
      obtain ⟨a, b, c, rfl, ha, hb⟩ := exists_first P l ⟨t, ht', hPt⟩
      refine ⟨y :: a, b, c, rfl, fun s hs => ?_, hb⟩
      rcases List.mem_cons.1 hs with rfl | hs
      · exact hy
      · exact ha s hs

/-! ### Disks along R-paths

These lemmas on the disks `diskN` of `FourColor.Snip` replace the detours through
`diskE_edge` in the Coq proof of `embed_functor`: an R-link `w → t` to a dart `t` outside
`fband r` preserves membership in `diskN r` (both ways), and the disk of a sequence `q` is
included in the disk of `r` as soon as `q` is, and the `dlink q` steps out of `diskN q` never
start from `r`. -/

section Disk

variable {D : Type u} (G : Hypermap D) [Finite D]

/-- An R-link `w → t` to a dart `t` outside `fband r` preserves membership in `diskN r`. -/
theorem rlink_diskN_iff {r : List D} {w t : D} (h : G.rlink w t) (ht : t ∉ G.fband r) :
    w ∈ G.diskN r ↔ t ∈ G.diskN r := by
  have hft : G.cface (G.face (G.edge w)) t := (G.cface1 _ _).1 h
  have hf : G.face (G.edge w) ∉ G.fband r := fun hf => ht (((G.fbandF r).connect_iff hft).1 hf)
  have hN : G.face (G.edge w) ∈ G.diskN r ↔ w ∈ G.diskN r :=
    (G.diskN_node r) (G.face (G.edge w)) w (G.edgeK w)
  rw [← hN]
  have hF := (G.diskF_face r).connect_iff hft
  constructor
  · intro h1
    exact (hF.1 ⟨h1, hf⟩).1
  · intro h1
    exact (hF.2 ⟨h1, ht⟩).1

/-- Forward propagation of `diskN r` along an R-path that avoids `fband r`. -/
theorem diskN_path {r : List D} {w : D} {l : List D} (hw : w ∈ G.diskN r)
    (hp : path G.rlink w l) (hl : ∀ t ∈ l, t ∉ G.fband r) : ∀ t ∈ l, t ∈ G.diskN r := by
  induction l generalizing w with
  | nil => intro t ht; exact absurd ht List.not_mem_nil
  | cons y l ih =>
    obtain ⟨wy, yl⟩ := hp
    have hy : y ∈ G.diskN r := (rlink_diskN_iff G wy (hl y List.mem_cons_self)).1 hw
    intro t ht
    rcases List.mem_cons.1 ht with rfl | ht
    · exact hy
    · exact ih hy yl (fun t' ht' => hl t' (List.mem_cons_of_mem _ ht')) t ht

/-- Backward propagation of `diskN r` along an R-path that avoids `fband r` (except at its
start). -/
theorem diskN_path_rev {r : List D} {w : D} {l : List D} (hp : path G.rlink w l)
    (hl : ∀ t ∈ l, t ∉ G.fband r) (hlast : last w l ∈ G.diskN r) : w ∈ G.diskN r := by
  induction l generalizing w with
  | nil => exact hlast
  | cons y l ih =>
    obtain ⟨wy, yl⟩ := hp
    have hy := ih yl (fun t ht => hl t (List.mem_cons_of_mem _ ht)) hlast
    exact (rlink_diskN_iff G wy (hl y List.mem_cons_self)).2 hy

/-- The disk of `q` is included in the disk of `r` if `q` is, and if no dart of `diskN q` (and
`diskN r`) outside `q` lies on `r`. -/
theorem diskN_subset {q r : List D} (hstart : ∀ z ∈ q, z ∈ G.diskN r)
    (hstep : ∀ y, y ∈ G.diskN q → y ∈ G.diskN r → y ∉ q → y ∉ r) :
    G.diskN q ⊆ G.diskN r := by
  rintro t ⟨z, hz, hzt⟩
  have h0 : G.face (G.edge z) ∈ G.diskN r :=
    ((G.diskN_node r) _ _ (G.edgeK z)).2 (hstart z hz)
  have h0q : G.face (G.edge z) ∈ G.diskN q := ⟨z, hz, connect_refl _⟩
  suffices H : ∀ w, connect (G.dlink q) (G.face (G.edge z)) w →
      w ∈ G.diskN q ∧ w ∈ G.diskN r from (H t hzt).2
  intro w hw
  induction hw with
  | refl => exact ⟨h0q, h0⟩
  | @tail b c _ hbc ih =>
    obtain ⟨ihq, ihr⟩ := ih
    refine ⟨G.diskN_dlink q ihq hbc, ?_⟩
    obtain ⟨q'b, hcl⟩ := hbc
    rcases hcl with e | e
    · exact ((G.diskN_node r) c b e.symm).2 ihr
    · exact G.diskN_dlink r ihr ⟨hstep b ihq ihr q'b, Or.inr e⟩

/-- In a face-simple sequence `A ++ a :: B`, the dart `a` is not in the face of a dart of `B`
(the math-comp idiom `simple_cat`, `simple_cons`). -/
theorem simple_split {l A B : List D} {a b : D} (hl : G.Simple l) (e : l = A ++ a :: B)
    (hb : b ∈ B) : ¬ G.cface a b := by
  rw [e, G.simple_cat, G.simple_cons] at hl
  exact fun hab => hl.2.2.1 ⟨b, hb, hab⟩

/-- The projection on a simple cycle `r` of a dart in the face of a dart `w` of `r` is `w`
(math-comp `fproj_cface`, `scycle_fproj`). -/
theorem fproj_eq {e : D → D → Prop} {r : List D} (hr : G.SCycle e r) {c w : D} (hw : w ∈ r)
    (hcw : G.cface c w) : G.fproj r c = w := by
  rw [G.fproj_cface r hcw, G.scycle_fproj hr w hw]

end Disk

end Embed

namespace Hypermap

/-! ### The section hypotheses -/

/-- The hypotheses of math-comp section `Embeddings` (except `Cred_cc`, an explicit argument of
the declarations that use it): `Gm` is a minimal counter-example (`cexGm`), `rc` is an
embeddable ring of `Gc` (`embedGc`), and `h` is a preembedding of the kernel `ac := kernel rc`
of `rc` into `Gm` (`embed_h`). -/
structure EmbedHyps {Dm : Type u} [Fintype Dm] {Dc : Type v} [Fintype Dc] (Gm : Hypermap Dm)
    (Gc : Hypermap Dc) (rc : List Dc) (h : Dc → Dm) : Prop where
  /-- math-comp `cexGm : minimal_counter_example Gm`. -/
  cexGm : Gm.MinimalCounterExample
  /-- math-comp `embedGc : embeddable rc`. -/
  embedGc : Gc.Embeddable rc
  /-- math-comp `embed_h : preembedding ac h`. -/
  embed_h : Gc.Preembedding Gm (Gc.kernel rc) h

namespace EmbedHyps

variable {Dm : Type u} [Fintype Dm] {Gm : Hypermap Dm}
  {Dc : Type v} [Fintype Dc] {Gc : Hypermap Dc} {rc : List Dc} {h : Dc → Dm}
  (E : EmbedHyps Gm Gc rc h)
include E

/-! #### The section `Let`s -/

omit [Fintype Dc] E in
/-- math-comp local `ac_bc`: the kernel is off the ring. -/
theorem ac_bc {x : Dc} (hx : x ∈ Gc.kernel rc) : x ∉ rc := Gc.kernel_off_ring rc hx

omit E in
/-- math-comp local `acF`: the kernel is face-closed. -/
theorem acF : Closed (frel Gc.face) (Gc.kernel rc) := Gc.kernelF rc

/-- math-comp local `planarGm`. -/
theorem planarGm : Gm.Planar := E.cexGm.planar

/-- math-comp local `bridge'Gm`. -/
theorem bridge'Gm (x : Dm) : ¬ Gm.cface x (Gm.edge x) :=
  Gm.bridgeless_cface E.cexGm.bridgeless x

/-- math-comp local `plainGm`. -/
theorem plainGm : Gm.Plain := E.cexGm.plain

/-- math-comp local `e2m`. -/
theorem e2m (x : Dm) : Gm.edge (Gm.edge x) = x := Gm.plain_eq E.cexGm.plain x

/-- math-comp local `n3m`. -/
theorem n3m (x : Dm) : Gm.node (Gm.node (Gm.node x)) = x := Gm.cubic_eq E.cexGm.cubic x

/-- math-comp local `pentaGm` (the Birkhoff theorem `min_arity`). -/
theorem pentaGm [DecidableEq Dm] : Gm.Pentagonal := fun x => Gm.min_arity E.cexGm x

/-- math-comp local `geoGm`. -/
theorem geoGm : Gm.PlanarBridgelessPlainConnected := E.cexGm.toPlanarBridgelessPlainConnected

/-- math-comp local `planarGc`. -/
theorem planarGc : Gc.Planar := E.embedGc.planar

/-- math-comp local `bridge'Gc`. -/
theorem bridge'Gc (x : Dc) : ¬ Gc.cface x (Gc.edge x) :=
  Gc.bridgeless_cface E.embedGc.bridgeless x

/-- math-comp local `plainGc`. -/
theorem plainGc : Gc.Plain := E.embedGc.plain

/-- math-comp local `cubicGc`. -/
theorem cubicGc : Gc.Quasicubic rc := E.embedGc.quasicubic

/-- math-comp local `e2c`. -/
theorem e2c (x : Dc) : Gc.edge (Gc.edge x) = x := Gc.plain_eq E.embedGc.plain x

/-- math-comp local `n3c`. -/
theorem n3c {x : Dc} (hx : x ∉ rc) : Gc.node (Gc.node (Gc.node x)) = x :=
  Gc.quasicubic_eq E.cubicGc x hx

/-- math-comp local `geoGc`. -/
theorem geoGc : Gc.PlanarBridgelessPlainConnected :=
  E.embedGc.toPlanarBridgelessPlainConnected

/-- math-comp local `UNrc`. -/
theorem UNrc : Gc.SFCycle Gc.node rc := E.embedGc.scycle

/-- math-comp local `cycNrc`. -/
theorem cycNrc : fcycle Gc.node rc := E.UNrc.1

/-- math-comp local `Urc`. -/
theorem Urc : rc.Nodup := Gc.scycle_uniq E.UNrc

/-- math-comp local `UrcF`. -/
theorem UrcF : Gc.Simple rc := E.UNrc.2

/-- math-comp local `hcE`: `{mono edge : x / x \in hc}`. -/
theorem hcE (x : Dc) : Gc.edge x ∈ Gc.edgeCentral Gm h ↔ x ∈ Gc.edgeCentral Gm h :=
  Gc.edge_central_edge Gm E.plainGc E.plainGm h x

/-- math-comp local `hF` (`preembedding_face embed_h`). -/
theorem hF {x : Dc} (hx : x ∈ Gc.kernel rc) : h (Gc.face x) = Gm.face (h x) :=
  E.embed_h.face x hx

/-- math-comp local `hFn` (`preembedding_arity embed_h`). -/
theorem hFn {x : Dc} (hx : x ∈ Gc.kernel rc) : Gm.arity (h x) = Gc.arity x :=
  E.embed_h.arity x hx

/-- math-comp notation `h_spoke` (`preembedding_simple_path embed_h acF`). -/
theorem h_spoke {x y : Dc} (hx : Gc.edge x ∈ Gc.kernel rc) (hy : y ∈ Gc.kernel rc) :
    ∃ p, (path Gc.rlink x p ∧ Gc.cface (last x p) y ∧ p ≠ []) ∧
      (Gc.Simple p ∧ ∀ z ∈ p, z ∈ Gc.kernel rc ∩ Gc.edgeCentral Gm h) :=
  Gc.preembedding_simple_path Gm E.embed_h (Gc.kernelF rc) hx hy

/-! #### Consequences of the face morphism property -/

omit [Fintype Dm] E in
/-- The kernel is closed under `edge ∘ node` (the face predecessor). -/
theorem ac_edge_node {y : Dc} (hy : y ∈ Gc.kernel rc) : Gc.edge (Gc.node y) ∈ Gc.kernel rc :=
  ((Gc.kernelF rc) _ _ (Gc.nodeK y)).2 hy

/-- On the kernel, `h` commutes with the face predecessor `edge ∘ node` (the math-comp idiom
`-[x]nodeK hF faceK`). -/
theorem h_edge_node {y : Dc} (hy : y ∈ Gc.kernel rc) :
    h (Gc.edge (Gc.node y)) = Gm.edge (Gm.node (h y)) := by
  have e := E.hF (ac_edge_node hy)
  rw [Gc.nodeK] at e
  rw [e, Gm.faceK]

/-- On the kernel, `h` commutes with `node` at the darts whose node is edge-central. -/
theorem h_node {y : Dc} (hy : y ∈ Gc.kernel rc) (hny : Gc.node y ∈ Gc.edgeCentral Gm h) :
    h (Gc.node y) = Gm.node (h y) := by
  apply Gm.edgeI
  have e : h (Gc.edge (Gc.node y)) = Gm.edge (h (Gc.node y)) := hny
  rw [← e, E.h_edge_node hy]

omit [Fintype Dm] E in
/-- The face predecessor of a dart of `Gc` is in its face. -/
theorem cface_edge_node (x : Dc) : Gc.cface (Gc.edge (Gc.node x)) x := by
  have := fconnect1 Gc.face (Gc.edge (Gc.node x))
  rwa [Gc.nodeK] at this

end EmbedHyps

end Hypermap

end FourColor
