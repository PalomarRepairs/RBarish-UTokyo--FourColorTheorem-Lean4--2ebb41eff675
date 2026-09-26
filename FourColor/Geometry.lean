/-
Copyright (c) 2026. Lean 4 port of the planarity part of the Coq/Rocq formal proof
of the Four Color Theorem by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Jordan
import Mathlib.Data.List.Iterate

/-!
# Geometrical interpretation of hypermaps  (port of `geometry.v`)

The geometrical interpretation of hypermaps, and the definition of most of the geometrical
notions relevant to the statement and proof of the Four Color Theorem. For `G : Hypermap D`:

* `G.Bridgeless`  : no face (F-cycle) of `G` contains both ends of an E-link.
* `G.Loopless`    : no node (N-cycle) of `G` contains both ends of an E-link.
* `G.Plain`       : all edges (E-cycles) of `G` have size 2.
* `G.Cubic`       : all nodes (N-cycles) of `G` have size 3.
* `G.Precubic`    : all nodes of `G` have size at most 3.
* `G.Quasicubic r` : all nodes of `G` not contained in `r` have size 3.
* `G.arity z`     : the face order of `z`, i.e., the size of the face of `z`.
* `G.Pentagonal`  : all faces of `G` have size at least 5.
* `G.Simple p`    : `p : List D` is face-simple: no two darts in `p` lie in the same face.
* `G.SimpleRec p` : alternative recursive definition of `G.Simple p`.
* `G.SCycle e p`  : `p` is simple and `e`-cyclic (`G.SFCycle f p` for `e = frel f`).
* `G.rlink x y`   : `y` is in the same face as `edge x`.
  We refer to `rlink` paths as R-paths, and `rlink` cycles as R-cycles.
* `G.SRPath x0 x p` : `x :: p` is a simple R-path, whose last dart is R-linked to `x0`.
* `G.SRCycle r`   : `r` is a simple R-cycle (a "ring").
* `G.RLinkConnected A` : `A` is R-path connected (with paths included in `A`).
* `G.fproj r x`   : some `y` in the intersection of `r` and the face of `x`, else
  `froot G.face x`; usually `r` is simple, so `y` is unique.
* `G.fband p`     : the face closure of `p : List D` (a set of darts).
* `G.kernel p`    : the complement of `G.fband p`; usually `p` is a node (N-cycle) that
  delimits `G`, so `G.kernel p` is the union of the "inner" faces of `G`.
* `G.adj x y`     : `x` and `y` belong to adjacent faces, that contain the ends of an N-link
  (i.e., `G.rlink z y` for some `z` in the face of `x`).
* `G.Chordless r` : no non-consecutive darts in the cycle `r` belong to adjacent faces.
* `G.insertE p`   : `[e1, edge e1, ..., en, edge en]` when `p = [e1, ..., en]` (the edge
  closure of `p` when `G` is plain).

math-comp's boolean duplicates `bridgelessb`, `plainb`, `cubicb` and `scycleb` collapse to the
`Prop`s above; the subset versions `plainb A`, `cubicb A` are `G.PlainOn A`, `G.CubicOn A`.
The records regrouping geometrical assumptions (`planar_bridgeless`, `plain_cubic`, ...) are
Lean `structure`s whose `_base` fields become `extends` clauses; their `:>` coercions are the
structure projections.  Since hypermap equality is plain `=` here, math-comp's `eqm_bridgeless`
and `eqm_loopless` are trivial and are omitted (as is the canonical structure `adj_app_pred`).

We also port the fragment of math-comp's `fingraph.v` and `path.v` needed here and not yet
provided by `FourColor.FinGraph` / `FourColor.Seq`: canonical representatives (`root`, `froot`),
orbits (`orbit`, `iter_order`, `order_cycle`, `fconnect_orbit`, `orbit_uniq`), `orderSet`,
`fcard_order_set`, `UCycle`, `cycle_rotate` (`rot_cycle`), and the cyclic successor/predecessor
functions `next`/`prev` with their rotation invariance.  math-comp's `traject f x n` is
`List.iterate f x n`, and `rot n p` is `List.rotate p n` (they differ only when `n` exceeds the
length of `p`: `rot` is then the identity while `List.rotate` reduces `n` modulo the length; all
the rotation lemmas below hold for every `n`).
-/

namespace FourColor

open Function

universe u

variable {α : Type*}

/-! ### Canonical representatives (math-comp `root`, `froot`) -/

section Root

variable {e : α → α → Prop}

/-- math-comp `root e x`: a canonical representative of the `connect e`-class of `x`. -/
noncomputable def root (e : α → α → Prop) (x : α) : α :=
  @Classical.epsilon α ⟨x⟩ (connect e x)

/-- math-comp `connect_root`. -/
theorem connect_root (e : α → α → Prop) (x : α) : connect e x (root e x) :=
  @Classical.epsilon_spec α (connect e x) ⟨x, connect_refl x⟩

/-- math-comp `rootP` (and `root_connect`): for a connect-symmetric relation, two points have
the same root iff they are connected. -/
theorem root_eq_iff (hs : ConnectSym e) {x y : α} : root e x = root e y ↔ connect e x y := by
  constructor
  · intro h
    have hx := connect_root e x
    rw [h] at hx
    exact connect_trans hx (hs _ _ (connect_root e y))
  · intro h
    have hxy : connect e x = connect e y := funext fun z => propext (hs.same h z)
    unfold root
    rw [hxy]

/-- math-comp `root_root`. -/
theorem root_root (hs : ConnectSym e) (x : α) : root e (root e x) = root e x :=
  (root_eq_iff hs).2 (hs _ _ (connect_root e x))

/-- math-comp `froot f`: the canonical representative of the `f`-orbit of `x`. -/
noncomputable abbrev froot (f : α → α) : α → α := root (frel f)

end Root

/-! ### Orbits (math-comp `orbit`, `iter_order`, `order_cycle`, `fcard_order_set`) -/

section Orbit

variable {f : α → α}

/-- math-comp `orbit f x`: the orbit of `x` under `f`, as the list
`[x, f x, ..., f^[order f x - 1] x]` (math-comp `traject f x (order f x)`; math-comp's
`traject` is `List.iterate`). -/
noncomputable def orbit (f : α → α) (x : α) : List α := List.iterate f x (order f x)

/-- math-comp `order_set f n`: the points whose `f`-orbit has size `n`. -/
def orderSet (f : α → α) (n : ℕ) : Set α := {x | order f x = n}

/-- math-comp `size_orbit`. -/
theorem length_orbit (f : α → α) (x : α) : (orbit f x).length = order f x :=
  List.length_iterate _ _ _

/-- Orders only depend on the orbits: points with the same forward orbits have the same order. -/
theorem order_congr {g : α → α} {x y : α} (h : ∀ z, fconnect f x z ↔ fconnect g y z) :
    order f x = order g y := by
  unfold order
  congr 1
  ext z
  exact h z

/-- The order of an injective function on a finite type is its minimal period. -/
theorem order_eq_minimalPeriod [Finite α] (hf : Injective f) (x : α) :
    order f x = minimalPeriod f x := by
  obtain ⟨n, hn, hx⟩ := exists_iterate_eq_self hf x
  have hpos : 0 < minimalPeriod f x :=
    minimalPeriod_pos_of_mem_periodicPts (mk_mem_periodicPts hn hx)
  have hset : {y | fconnect f x y} = (fun i => f^[i] x) '' Set.Iio (minimalPeriod f x) := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_Iio, fconnect_iff_iterate]
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m % minimalPeriod f x, Nat.mod_lt _ hpos, iterate_mod_minimalPeriod_eq⟩
    · rintro ⟨m, -, rfl⟩
      exact ⟨m, rfl⟩
  rw [order, hset, iterate_injOn_Iio_minimalPeriod.ncard_image, ← Finset.coe_range,
    Set.ncard_coe_finset, Finset.card_range]

/-- The order of a point under an injection on a finite type is positive (math-comp
`orderSpred`). -/
theorem order_pos [Finite α] (hf : Injective f) (x : α) : 0 < order f x := by
  obtain ⟨n, hn, hx⟩ := exists_iterate_eq_self hf x
  rw [order_eq_minimalPeriod hf]
  exact minimalPeriod_pos_of_mem_periodicPts (mk_mem_periodicPts hn hx)

/-- math-comp `iter_order`. -/
theorem iter_order [Finite α] (hf : Injective f) (x : α) : f^[order f x] x = x := by
  rw [order_eq_minimalPeriod hf]
  exact iterate_minimalPeriod

/-- math-comp `fconnect_orbit`. -/
theorem fconnect_orbit [Finite α] (hf : Injective f) {x y : α} :
    fconnect f x y ↔ y ∈ orbit f x := by
  have hpos := order_pos hf x
  rw [fconnect_iff_iterate, orbit, List.mem_iterate]
  constructor
  · rintro ⟨m, rfl⟩
    refine ⟨m % order f x, Nat.mod_lt _ hpos, ?_⟩
    rw [order_eq_minimalPeriod hf, iterate_mod_minimalPeriod_eq]
  · rintro ⟨m, -, rfl⟩
    exact ⟨m, rfl⟩

/-- math-comp `orbit_uniq`: the orbit list is duplicate-free. -/
theorem orbit_uniq [Finite α] (hf : Injective f) (x : α) : (orbit f x).Nodup := by
  rw [orbit, order_eq_minimalPeriod hf, ← List.range_map_iterate]
  refine List.Nodup.map_on ?_ List.nodup_range
  intro i hi j hj h
  exact iterate_injOn_Iio_minimalPeriod (List.mem_range.1 hi) (List.mem_range.1 hj) h

/-- The number of items of a duplicate-free list. -/
theorem ncard_mem_of_nodup {p : List α} (hp : p.Nodup) : {x | x ∈ p}.ncard = p.length := by
  classical
  rw [← List.coe_toFinset, Set.ncard_coe_finset, List.toFinset_card_of_nodup hp]

/-- math-comp `order_cycle`: in a duplicate-free `f`-cycle, the order of every item is the
size of the cycle. -/
theorem order_cycle {p : List α} (hp : fcycle f p) (hu : p.Nodup) {x : α} (hx : x ∈ p) :
    order f x = p.length := by
  have : {y | fconnect f x y} = {y | y ∈ p} := Set.ext fun y => fconnect_cycle hp hx
  rw [order, this, ncard_mem_of_nodup hu]

/-- math-comp `order_finv`: an inverse of `f` has the same orders as `f`. -/
theorem order_inverse [Finite α] {g : α → α} (hgf : LeftInverse g f) (hfg : RightInverse g f)
    (x : α) : order g x = order f x :=
  order_congr fun _ => fconnect_inverse hgf hfg

/-- The whole type is closed under any relation. -/
theorem closed_univ {e : α → α → Prop} : Closed e (Set.univ : Set α) :=
  fun x y _ => ⟨fun _ => Set.mem_univ y, fun _ => Set.mem_univ x⟩

/-- math-comp `fcard_order_set`: an `f`-closed set whose orbits all have size `n` has
`n` times as many points as orbits. -/
theorem fcard_order_set [Finite α] (hf : Injective f) {n : ℕ} {a : Set α}
    (ha : a ⊆ orderSet f n) (hcl : Closed (frel f) a) : fcard f a * n = a.ncard := by
  classical
  have hs := fconnect_sym hf
  have := Fintype.ofFinite α
  rw [Set.ncard_eq_toFinset_card' a, Finset.card_eq_sum_card_image (comp (frel f)) a.toFinset]
  have hfib : ∀ c ∈ a.toFinset.image (comp (frel f)),
      (a.toFinset.filter (fun y => comp (frel f) y = c)).card = n := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hc
    rw [Set.mem_toFinset] at hx
    have hfil : a.toFinset.filter (fun y => comp (frel f) y = comp (frel f) x) =
        (comp (frel f) x).toFinset := by
      ext y
      simp only [Finset.mem_filter, Set.mem_toFinset, comp_eq_iff hs, mem_comp]
      constructor
      · rintro ⟨-, h⟩
        exact hs _ _ h
      · intro h
        exact ⟨(hcl.connect_iff h).1 hx, hs _ _ h⟩
    rw [hfil, ← Set.ncard_eq_toFinset_card']
    exact ha hx
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  congr 1
  show (comp (frel f) '' a).ncard = _
  rw [← Set.ncard_coe_finset, Finset.coe_image, Set.coe_toFinset]

end Orbit

/-! ### Duplicate-free cycles and rotations (math-comp `ucycle`, `rot_cycle`) -/

section Cycles

variable {e : α → α → Prop}

/-- math-comp `ucycle e p`: `p` is a duplicate-free `e`-cycle. -/
def UCycle (e : α → α → Prop) (p : List α) : Prop := cycle e p ∧ p.Nodup

/-- math-comp `rot_cycle`, for a rotation by one item. -/
theorem cycle_rotate_one (x : α) (p : List α) : cycle e (p ++ [x]) ↔ cycle e (x :: p) := by
  cases p with
  | nil => exact Iff.rfl
  | cons y p =>
    rw [List.cons_append, cycle_cons, cycle_cons, path_concat, path_concat, last_concat,
      List.cons_append, path_cons, path_concat]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h3, h1, h2⟩
    · rintro ⟨h3, h1, h2⟩
      exact ⟨⟨h1, h2⟩, h3⟩

/-- math-comp `rot_cycle`. -/
theorem cycle_rotate (n : ℕ) (p : List α) : cycle e (p.rotate n) ↔ cycle e p := by
  rw [List.rotate_eq_rotate']
  induction n generalizing p with
  | zero => rw [List.rotate'_zero]
  | succ n ih =>
    cases p with
    | nil => rw [List.rotate'_nil]
    | cons a l => rw [List.rotate'_cons_succ, ih, cycle_rotate_one]

end Cycles

/-! ### Cyclic successor and predecessor (math-comp `next`, `prev`) -/

section NextPrev

variable [DecidableEq α]

/-- math-comp `next_at x y0 y p`: the successor of `x` in the cycle `y :: p ++ [y0]`. -/
def nextAt (x y0 : α) : α → List α → α
  | y, [] => if x = y then y0 else x
  | y, y' :: p' => if x = y then y' else nextAt x y0 y' p'

/-- math-comp `next p x`: the item following the first occurrence of `x` in the cyclic sequence
`p`, or `x` itself if `x` does not occur in `p`. -/
def next : List α → α → α
  | [], x => x
  | y :: p', x => nextAt x y y p'

/-- math-comp `prev_at x y0 y p`. -/
def prevAt (x y0 : α) : α → List α → α
  | y, [] => if x = y0 then y else x
  | y, y' :: p' => if x = y' then y else prevAt x y0 y' p'

/-- math-comp `prev p x`: the item preceding `x` in the cyclic sequence `p`, or `x` itself if
`x` does not occur in `p`. -/
def prev : List α → α → α
  | [], x => x
  | y :: p', x => prevAt x y y p'

/-- `next_at` leaves the points outside the sequence unchanged. -/
theorem nextAt_of_not_mem {x y0 y : α} {p : List α} (h : x ∉ y :: p) : nextAt x y0 y p = x := by
  induction p generalizing y with
  | nil =>
    have hxy : x ≠ y := fun e => h (List.mem_cons.2 (Or.inl e))
    simp [nextAt, hxy]
  | cons z p ih =>
    have hxy : x ≠ y := fun e => h (List.mem_cons.2 (Or.inl e))
    have h' : x ∉ z :: p := fun hm => h (List.mem_cons_of_mem _ hm)
    simp [nextAt, hxy, ih h']

/-- `next_at` on a sequence extended at the end (helper for math-comp `next_rot`). -/
theorem nextAt_concat (x y0 y z : α) (p : List α) :
    nextAt x y0 y (p ++ [z]) =
      if x ∈ y :: p then nextAt x z y p else if x = z then y0 else x := by
  induction p generalizing y with
  | nil => by_cases hxy : x = y <;> simp [nextAt, hxy]
  | cons w p ih =>
    rw [List.cons_append, nextAt, ih]
    by_cases hxy : x = y <;> simp [hxy, nextAt]

/-- math-comp `next_rot` for a rotation by one item. -/
theorem next_rotate_one {a : α} {l : List α} (h : (a :: l).Nodup) (x : α) :
    next (l ++ [a]) x = next (a :: l) x := by
  cases l with
  | nil => rfl
  | cons b l =>
    have ha : a ∉ b :: l := (List.nodup_cons.1 h).1
    show nextAt x b b (l ++ [a]) = nextAt x a a (b :: l)
    rw [nextAt_concat]
    by_cases hxa : x = a
    · subst hxa
      simp [ha, nextAt]
    · by_cases hx : x ∈ b :: l
      · simp [hx, hxa, nextAt]
      · simp [hx, hxa, nextAt, nextAt_of_not_mem hx]

/-- math-comp `next_rot`. -/
theorem next_rotate {p : List α} (hp : p.Nodup) (n : ℕ) (x : α) :
    next (p.rotate n) x = next p x := by
  rw [List.rotate_eq_rotate']
  induction n generalizing p with
  | zero => rw [List.rotate'_zero]
  | succ n ih =>
    cases p with
    | nil => rw [List.rotate'_nil]
    | cons a l => rw [List.rotate'_cons_succ, ih (List.nodup_append_comm.2 hp), next_rotate_one hp]

/-- `prev_at` on a point outside the tail of the sequence. -/
theorem prevAt_of_not_mem {x y0 y : α} {p : List α} (h : x ∉ p) :
    prevAt x y0 y p = if x = y0 then last y p else x := by
  induction p generalizing y with
  | nil => rfl
  | cons z p ih =>
    have hxz : x ≠ z := fun e => h (List.mem_cons.2 (Or.inl e))
    have h' : x ∉ p := fun hm => h (List.mem_cons_of_mem _ hm)
    simp [prevAt, hxz, ih h']

/-- `prev_at` on a point in the tail of the sequence does not depend on the head `y0`. -/
theorem prevAt_of_mem {x y0 y1 y : α} {p : List α} (h : x ∈ p) :
    prevAt x y0 y p = prevAt x y1 y p := by
  induction p generalizing y with
  | nil => simp at h
  | cons z p ih =>
    by_cases hxz : x = z
    · simp [prevAt, hxz]
    · have h' : x ∈ p := (List.mem_cons.1 h).resolve_left hxz
      simp [prevAt, hxz, ih h']

/-- `prev_at` on a sequence extended at the end (helper for math-comp `prev_rot`). -/
theorem prevAt_concat (x y0 y z : α) (p : List α) :
    prevAt x y0 y (p ++ [z]) =
      if x ∈ p then prevAt x y0 y p else if x = z then last y p else if x = y0 then z else x := by
  induction p generalizing y with
  | nil => by_cases hxz : x = z <;> simp [prevAt, hxz]
  | cons w p ih =>
    rw [List.cons_append, prevAt, ih]
    by_cases hxw : x = w <;> simp [hxw, prevAt]

/-- math-comp `prev_rot` for a rotation by one item. -/
theorem prev_rotate_one {a : α} {l : List α} (h : (a :: l).Nodup) (x : α) :
    prev (l ++ [a]) x = prev (a :: l) x := by
  cases l with
  | nil => rfl
  | cons b l =>
    have ha : a ∉ b :: l := (List.nodup_cons.1 h).1
    have hb : b ∉ l := (List.nodup_cons.1 (List.nodup_cons.1 h).2).1
    have hab : a ≠ b := fun e => ha (List.mem_cons.2 (Or.inl e))
    have hal : a ∉ l := fun e => ha (List.mem_cons_of_mem _ e)
    show prevAt x b b (l ++ [a]) = prevAt x a a (b :: l)
    rw [prevAt_concat]
    by_cases hx : x ∈ l
    · have hxb : x ≠ b := fun e => hb (e ▸ hx)
      simp [hx, hxb, prevAt, prevAt_of_mem (y0 := b) (y1 := a) (y := b) hx]
    · by_cases hxa : x = a
      · subst hxa
        simp [hal, hab, prevAt, prevAt_of_not_mem hal]
      · by_cases hxb : x = b
        · subst hxb
          simp [hb, hxa, prevAt]
        · simp [hx, hxa, hxb, prevAt, prevAt_of_not_mem hx]

/-- math-comp `prev_rot`. -/
theorem prev_rotate {p : List α} (hp : p.Nodup) (n : ℕ) (x : α) :
    prev (p.rotate n) x = prev p x := by
  rw [List.rotate_eq_rotate']
  induction n generalizing p with
  | zero => rw [List.rotate'_zero]
  | succ n ih =>
    cases p with
    | nil => rw [List.rotate'_nil]
    | cons a l => rw [List.rotate'_cons_succ, ih (List.nodup_append_comm.2 hp), prev_rotate_one hp]

end NextPrev

/-- Two lists with the same items and the same length are simultaneously duplicate-free
(math-comp `eq_uniq`). -/
theorem nodup_iff_of_mem_iff {l₁ l₂ : List α} (hl : l₁.length = l₂.length)
    (hm : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁.Nodup ↔ l₂.Nodup := by
  classical
  have hf : l₁.toFinset = l₂.toFinset := Finset.ext fun x => by simp [hm x]
  have hd : l₁.dedup.length = l₂.dedup.length := by
    rw [← List.card_toFinset, ← List.card_toFinset, hf]
  rw [List.nodup_iff_length_dedup_eq, List.nodup_iff_length_dedup_eq, hd, hl]

namespace Hypermap

variable {D : Type u}

/-! ### Bridges and loops -/

section BridgeAndLoopLess

variable (G : Hypermap D)

/-- math-comp `bridgeless G` (and its boolean version `bridgelessb G`): no face contains both
ends of an E-link. -/
def Bridgeless : Prop := ¬ ∃ x, G.cface x (G.edge x)

/-- math-comp `bridgeless_cface`. -/
theorem bridgeless_cface (hG : G.Bridgeless) (x : D) : ¬ G.cface x (G.edge x) :=
  fun h => hG ⟨x, h⟩

/-- math-comp `loopless G`: no node contains both ends of an E-link. -/
def Loopless : Prop := ¬ ∃ x, G.cnode x (G.edge x)

variable [Finite D]

/-- math-comp `bridgeless_dual`. -/
theorem bridgeless_dual : G.dual.Bridgeless ↔ G.Loopless := by
  have key : ∀ x y, G.dual.cface x y ↔ G.cnode x y := fun x y =>
    fconnect_inverse (f := G.node) (g := fun a => G.face (G.edge a)) G.nodeK G.edgeK
  unfold Bridgeless Loopless
  rw [not_iff_not]
  constructor
  · rintro ⟨x, hx⟩
    rw [key, dual_edge] at hx
    refine ⟨G.node (G.face x), ?_⟩
    rw [G.faceK]
    exact G.cnodeC.1 hx
  · rintro ⟨y, hy⟩
    refine ⟨G.edge y, ?_⟩
    rw [key, dual_edge, G.edgeK]
    exact G.cnodeC.1 hy

/-- math-comp `bridgeless_mirror`. -/
theorem bridgeless_mirror : G.mirror.Bridgeless ↔ G.Bridgeless := by
  have key : ∀ x y, G.mirror.cface x y ↔ G.cface x y := fun x y =>
    fconnect_inverse (f := G.face) (g := fun a => G.edge (G.node a)) G.faceK G.nodeK
  unfold Bridgeless
  rw [not_iff_not]
  constructor
  · rintro ⟨x, hx⟩
    rw [key, mirror_edge] at hx
    -- `hx : cface x (face (node x))`
    refine ⟨G.node x, ?_⟩
    have h1 : G.cface (G.edge (G.node x)) x := by
      have := fconnect1 G.face (G.edge (G.node x))
      rwa [G.nodeK] at this
    exact connect_trans (G.cfaceC.1 ((G.cface1r _ _).2 hx)) (G.cfaceC.1 h1)
  · rintro ⟨y, hy⟩
    refine ⟨G.face (G.edge y), ?_⟩
    rw [key, mirror_edge, G.edgeK]
    -- `cface (face (edge y)) (face y)`
    exact (G.cface1 _ _).1 ((G.cface1r _ _).1 (G.cfaceC.1 hy))

end BridgeAndLoopLess

/-! ### Arity, face bands, projections and simple paths -/

section FacePaths

variable (G : Hypermap D)

/-- math-comp `arity`: the face order of a dart, i.e., the size of its face. -/
noncomputable abbrev arity (x : D) : ℕ := order G.face x

/-- math-comp `fband p`: the darts that lie in the same face as some dart of `p`. -/
def fband (p : List D) : Set D := {x | ∃ y ∈ p, G.cface x y}

/-- math-comp `kernel p`: the complement of `fband p`. It is only used when `p` is the outer ring
of a configuration. -/
def kernel (p : List D) : Set D := (G.fband p)ᶜ

/-- math-comp `simple p`: `p` is face-simple, no two darts of `p` lie in the same face. -/
def Simple (p : List D) : Prop := (p.map (froot G.face)).Nodup

/-- math-comp `scycle e p` (and its boolean version `scycleb e p`): `p` is a simple `e`-cycle. -/
def SCycle (e : D → D → Prop) (p : List D) : Prop := cycle e p ∧ G.Simple p

/-- math-comp `sfcycle f p` (a notation for `scycle (frel f) p`): `p` is a simple `f`-cycle. -/
abbrev SFCycle (f : D → D) (p : List D) : Prop := G.SCycle (frel f) p

/-- math-comp `simple_rec p`: the recursive characterization of `simple p`. -/
def SimpleRec : List D → Prop
  | [] => True
  | x :: p => x ∉ G.fband p ∧ SimpleRec p

open Classical in
/-- math-comp `fproj p x`: the first dart of `p` in the face of `x`, if any, else
`froot G.face x`; this is the math-comp `nth (froot face x) p (find (cface x) p)`. -/
noncomputable def fproj (p : List D) (x : D) : D :=
  (p.find? fun y => decide (G.cface x y)).getD (froot G.face x)

/-- Membership in `fband` (math-comp `fband p x = has (cface x) p`). -/
theorem mem_fband {p : List D} {x : D} : x ∈ G.fband p ↔ ∃ y ∈ p, G.cface x y := Iff.rfl

/-- math-comp `ring_fband`. -/
theorem ring_fband (p : List D) : ∀ x ∈ p, x ∈ G.fband p := fun x hx => ⟨x, hx, connect_refl x⟩

/-- math-comp `fband_cons`. -/
theorem fband_cons (x : D) (p : List D) (y : D) :
    y ∈ G.fband (x :: p) ↔ G.cface y x ∨ y ∈ G.fband p := by
  simp only [mem_fband, List.mem_cons, exists_eq_or_imp]

/-- math-comp `fband_cat`. -/
theorem fband_cat (p1 p2 : List D) (x : D) :
    x ∈ G.fband (p1 ++ p2) ↔ x ∈ G.fband p1 ∨ x ∈ G.fband p2 := by
  simp only [mem_fband, List.mem_append, or_and_right, exists_or]

/-- math-comp `fband_rcons`. -/
theorem fband_rcons (x : D) (p : List D) (y : D) :
    y ∈ G.fband (p ++ [x]) ↔ G.cface y x ∨ y ∈ G.fband p := by
  rw [fband_cat, or_comm, fband_cons]
  simp only [mem_fband, List.not_mem_nil, false_and, exists_false, or_false]

/-- math-comp `kernel_off_ring`. -/
theorem kernel_off_ring (p : List D) : G.kernel p ⊆ {x | x ∉ p} :=
  fun x hx hp => hx (G.ring_fband p x hp)

/-- math-comp `simple_uniq`. -/
theorem simple_uniq {p : List D} (hp : G.Simple p) : p.Nodup := List.Nodup.of_map _ hp

/-- math-comp `scycle_cycle`. -/
theorem scycle_cycle {e : D → D → Prop} {p : List D} (hp : G.SCycle e p) : cycle e p := hp.1

/-- math-comp `scycle_simple`. -/
theorem scycle_simple {e : D → D → Prop} {p : List D} (hp : G.SCycle e p) : G.Simple p := hp.2

/-- math-comp `scycle_uniq`. -/
theorem scycle_uniq {e : D → D → Prop} {p : List D} (hp : G.SCycle e p) : p.Nodup :=
  G.simple_uniq hp.2

/-- math-comp `scycle_ucycle` (a coercion in math-comp). -/
theorem scycle_ucycle {e : D → D → Prop} {p : List D} (hp : G.SCycle e p) : UCycle e p :=
  ⟨hp.1, G.scycle_uniq hp⟩

/-- `fproj` on the empty sequence is the face root (by definition in math-comp). -/
theorem fproj_nil (x : D) : G.fproj [] x = froot G.face x := rfl

/-- math-comp `simple_catC`. -/
theorem simple_catC (p1 p2 : List D) : G.Simple (p1 ++ p2) ↔ G.Simple (p2 ++ p1) := by
  unfold Simple
  rw [List.map_append, List.map_append, List.nodup_append_comm]

/-- math-comp `simple_catCA`. -/
theorem simple_catCA (p1 p2 p3 : List D) :
    G.Simple (p1 ++ (p2 ++ p3)) ↔ G.Simple (p2 ++ (p1 ++ p3)) := by
  unfold Simple
  exact ((List.perm_append_comm_assoc p1 p2 p3).map _).nodup_iff

/-- math-comp `fband_rot`. -/
theorem fband_rot (n : ℕ) (p : List D) : G.fband (p.rotate n) = G.fband p := by
  ext x
  simp only [mem_fband, List.mem_rotate]

/-- math-comp `simple_rot`. -/
theorem simple_rot (n : ℕ) (p : List D) : G.Simple (p.rotate n) ↔ G.Simple p := by
  unfold Simple
  rw [List.map_rotate, List.nodup_rotate]

/-- math-comp `rot_scycle`. -/
theorem rot_scycle (n : ℕ) (e : D → D → Prop) (p : List D) :
    G.SCycle e (p.rotate n) ↔ G.SCycle e p := by
  unfold SCycle
  rw [cycle_rotate, simple_rot]

/-- math-comp `simple_rev`. -/
theorem simple_rev (p : List D) : G.Simple p.reverse ↔ G.Simple p := by
  unfold Simple
  rw [List.map_reverse, List.nodup_reverse]

/-- math-comp `fband_rev`. -/
theorem fband_rev (p : List D) : G.fband p.reverse = G.fband p := by
  ext x
  simp only [mem_fband, List.mem_reverse]

variable [Finite D]

/-- math-comp `arity_cface`. -/
theorem arity_cface {x y : D} (h : G.cface x y) : G.arity x = G.arity y :=
  order_congr (G.same_cface h)

/-- math-comp `arity_iter_face`. -/
theorem arity_iter_face (n : ℕ) (x : D) : G.arity (G.face^[n] x) = G.arity x :=
  (G.arity_cface (fconnect_iterate _ x n)).symm

/-- math-comp `arity_face`. -/
theorem arity_face (x : D) : G.arity (G.face x) = G.arity x := G.arity_iter_face 1 x

/-- math-comp `iter_face_arity`. -/
theorem iter_face_arity (x : D) : G.face^[G.arity x] x = x := iter_order G.faceI x

/-- math-comp `iter_face_subn`. -/
theorem iter_face_subn {n : ℕ} {x : D} (h : n ≤ G.arity x) :
    G.face^[G.arity x - n] (G.face^[n] x) = x := by
  rw [← iterate_add_apply, Nat.sub_add_cancel h, iter_face_arity]

/-- math-comp `arity_mirror`. -/
theorem arity_mirror (x : D) : G.mirror.arity x = G.arity x :=
  order_inverse (f := G.face) (g := fun a => G.edge (G.node a)) G.faceK G.nodeK x

/-- math-comp `fbandF`. -/
theorem fbandF (p : List D) : Closed (frel G.face) (G.fband p) := by
  rintro x _ rfl
  exact exists_congr fun y => and_congr_right fun _ => G.cface1 x y

/-- math-comp `kernelF`. -/
theorem kernelF (p : List D) : Closed (frel G.face) (G.kernel p) := (G.fbandF p).compl

/-- math-comp `rootP` for faces. -/
theorem froot_face_eq_iff {x y : D} : froot G.face x = froot G.face y ↔ G.cface x y :=
  root_eq_iff G.cface_sym

open Classical in
/-- math-comp `fproj_cons`. -/
theorem fproj_cons (x : D) (p : List D) (y : D) :
    G.fproj (x :: p) y = if G.cface x y then x else G.fproj p y := by
  unfold fproj
  rw [List.find?_cons]
  by_cases h : G.cface x y
  · have h' : G.cface y x := G.cfaceC.1 h
    simp [h, h']
  · have h' : ¬ G.cface y x := fun h' => h (G.cfaceC.1 h')
    simp [h, h']

/-- The default value of `fproj`. -/
theorem fproj_of_not_mem {p : List D} {x : D} (hx : x ∉ G.fband p) :
    G.fproj p x = froot G.face x := by
  induction p with
  | nil => rfl
  | cons y p ih =>
    rw [fband_cons, not_or] at hx
    rw [fproj_cons, ite_eq_right fun h => hx.1 (G.cfaceC.1 h), ih hx.2]

/-- math-comp `fprojP`. -/
theorem fprojP {p : List D} {x : D} (hx : x ∈ G.fband p) :
    G.fproj p x ∈ p ∧ G.cface x (G.fproj p x) := by
  induction p with
  | nil =>
    obtain ⟨y, hy, -⟩ := hx
    simp at hy
  | cons y p ih =>
    rw [fproj_cons]
    split_ifs with h
    · exact ⟨List.mem_cons_self, G.cfaceC.1 h⟩
    · have hx' : x ∈ G.fband p :=
        ((G.fband_cons y p x).1 hx).resolve_left fun h' => h (G.cfaceC.1 h')
      obtain ⟨h1, h2⟩ := ih hx'
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

/-- math-comp `fproj_cface`. -/
theorem fproj_cface (p : List D) {x y : D} (h : G.cface x y) : G.fproj p x = G.fproj p y := by
  induction p with
  | nil => exact (G.froot_face_eq_iff).2 h
  | cons z p ih =>
    rw [fproj_cons, fproj_cons, ih]
    have hzz : G.cface z x ↔ G.cface z y := G.cface_sym.same_r h z
    by_cases hzx : G.cface z x
    · rw [ite_eq_left hzx, ite_eq_left (hzz.1 hzx)]
    · rw [ite_eq_right hzx, ite_eq_right (fun h' => hzx (hzz.2 h'))]

/-- math-comp `simple_cons`. -/
theorem simple_cons (x : D) (p : List D) : G.Simple (x :: p) ↔ x ∉ G.fband p ∧ G.Simple p := by
  unfold Simple
  rw [List.map_cons, List.nodup_cons]
  apply and_congr_left'
  apply not_congr
  rw [List.mem_map]
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, (G.froot_face_eq_iff).1 hxy.symm⟩
  · rintro ⟨y, hy, hxy⟩
    exact ⟨y, hy, ((G.froot_face_eq_iff).2 hxy).symm⟩

/-- math-comp `simple_recI`. -/
theorem simple_recI (p : List D) : G.Simple p ↔ G.SimpleRec p := by
  induction p with
  | nil => exact ⟨fun _ => trivial, fun _ => List.nodup_nil⟩
  | cons x p ih => rw [simple_cons, ih]; rfl

/-- math-comp `simple_fproj`. -/
theorem simple_fproj {p : List D} (hp : G.Simple p) : ∀ x ∈ p, G.fproj p x = x := by
  induction p with
  | nil => intro x hx; simp at hx
  | cons y p ih =>
    rw [simple_cons] at hp
    intro x hx
    rw [fproj_cons]
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ite_eq_left (connect_refl _)
    · rw [ite_eq_right fun h => hp.1 ⟨x, hx, h⟩]
      exact ih hp.2 x hx

/-- math-comp `scycle_fproj`. -/
theorem scycle_fproj {e : D → D → Prop} {p : List D} (hp : G.SCycle e p) :
    ∀ x ∈ p, G.fproj p x = x :=
  G.simple_fproj hp.2

/-- math-comp `simple_cface`. -/
theorem simple_cface {p : List D} (hp : G.Simple p) :
    ∀ x ∈ p, ∀ y ∈ p, G.cface x y → x = y := by
  intro x hx y hy hxy
  rw [← G.simple_fproj hp x hx, G.fproj_cface p hxy, G.simple_fproj hp y hy]

/-- math-comp `scycle_cface`. -/
theorem scycle_cface {e : D → D → Prop} {p : List D} (hp : G.SCycle e p) :
    ∀ x ∈ p, ∀ y ∈ p, G.cface x y → x = y :=
  G.simple_cface hp.2

/-- math-comp `simple_fcard_fband`. -/
theorem simple_fcard_fband {p : List D} (hp : G.Simple p) :
    fcard G.face (G.fband p) = p.length := by
  have hs := G.cface_sym
  have himg : comp (frel G.face) '' G.fband p = comp (frel G.face) '' {x | x ∈ p} := by
    ext c
    simp only [Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨x, ⟨y, hy, hxy⟩, rfl⟩
      exact ⟨y, hy, ((comp_eq_iff hs).2 hxy).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, G.ring_fband p y hy, rfl⟩
  show (comp (frel G.face) '' G.fband p).ncard = _
  rw [himg, Set.InjOn.ncard_image, ncard_mem_of_nodup (G.simple_uniq hp)]
  intro x hx y hy hxy
  exact G.simple_cface hp x hx y hy ((comp_eq_iff hs).1 hxy)

/-- math-comp `scycle_fcard_fband`. -/
theorem scycle_fcard_fband {e : D → D → Prop} {p : List D} (hp : G.SCycle e p) :
    fcard G.face (G.fband p) = p.length :=
  G.simple_fcard_fband hp.2

open Classical in
/-- math-comp `predI_cface_simple`: a simple sequence meets the face of `x` at most once. -/
theorem predI_cface_simple (x : D) {p : List D} (hp : G.Simple p) :
    {y | G.cface x y ∧ y ∈ p}.ncard = if x ∈ G.fband p then 1 else 0 := by
  split_ifs with hx
  · obtain ⟨y, hy, hxy⟩ := hx
    rw [Set.ncard_eq_one]
    refine ⟨y, Set.ext fun z => ?_⟩
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hxz, hz⟩
      exact G.simple_cface hp z hz y hy ((G.same_cface hxz y).1 hxy)
    · rintro rfl
      exact ⟨hxy, hy⟩
  · have : {y | G.cface x y ∧ y ∈ p} = ∅ :=
      Set.eq_empty_of_forall_notMem fun y ⟨hxy, hy⟩ => hx ⟨y, hy, hxy⟩
    rw [this, Set.ncard_empty]

/-- math-comp `fband_nseq`. -/
theorem fband_nseq {x y : D} (h : G.cface x y) (n : ℕ) :
    G.fband (List.replicate n x) = G.fband (List.replicate n y) := by
  ext z
  simp only [mem_fband, List.mem_replicate]
  constructor
  · rintro ⟨w, ⟨hn, rfl⟩, hzw⟩
    exact ⟨y, ⟨hn, rfl⟩, connect_trans hzw h⟩
  · rintro ⟨w, ⟨hn, rfl⟩, hzw⟩
    exact ⟨x, ⟨hn, rfl⟩, connect_trans hzw (G.cfaceC.1 h)⟩

open Classical in
/-- math-comp `fproj_cat`. -/
theorem fproj_cat (p1 p2 : List D) (x : D) :
    G.fproj (p1 ++ p2) x = G.fproj (if x ∈ G.fband p1 then p1 else p2) x := by
  induction p1 with
  | nil =>
    have : x ∉ G.fband [] := fun ⟨y, hy, _⟩ => by simp at hy
    rw [ite_eq_right this, List.nil_append]
  | cons y p1 ih =>
    rw [List.cons_append, fproj_cons, ih]
    by_cases hyx : G.cface y x
    · have : x ∈ G.fband (y :: p1) := (G.fband_cons y p1 x).2 (Or.inl (G.cfaceC.1 hyx))
      rw [ite_eq_left hyx, ite_eq_left this, fproj_cons, ite_eq_left hyx]
    · by_cases hx : x ∈ G.fband p1
      · have : x ∈ G.fband (y :: p1) := (G.fband_cons y p1 x).2 (Or.inr hx)
        rw [ite_eq_right hyx, ite_eq_left hx, ite_eq_left this, fproj_cons, ite_eq_right hyx]
      · have : x ∉ G.fband (y :: p1) := by
          rw [fband_cons, not_or]
          exact ⟨fun h => hyx (G.cfaceC.1 h), hx⟩
        rw [ite_eq_right hyx, ite_eq_right hx, ite_eq_right this]

/-- math-comp `has_fband_sym`. -/
theorem has_fband_sym (p1 p2 : List D) :
    (∃ x ∈ p2, x ∈ G.fband p1) ↔ (∃ x ∈ p1, x ∈ G.fband p2) := by
  constructor <;>
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨y, hy, x, hx, G.cfaceC.1 hxy⟩

/-- math-comp `simple_cat`. -/
theorem simple_cat (p1 p2 : List D) :
    G.Simple (p1 ++ p2) ↔ G.Simple p1 ∧ ¬ (∃ x ∈ p2, x ∈ G.fband p1) ∧ G.Simple p2 := by
  have key : (∀ a ∈ p1.map (froot G.face), ∀ b ∈ p2.map (froot G.face), a ≠ b) ↔
      ¬ ∃ x ∈ p2, x ∈ G.fband p1 := by
    constructor
    · rintro h ⟨x, hx, y, hy, hxy⟩
      exact h _ (List.mem_map_of_mem hy) _ (List.mem_map_of_mem hx)
        ((G.froot_face_eq_iff).2 (G.cfaceC.1 hxy))
    · rintro h a ha b hb hab
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
      exact h ⟨x, hx, y, hy, G.cfaceC.1 ((G.froot_face_eq_iff).1 hab)⟩
  unfold Simple
  rw [List.map_append, List.nodup_append, key]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h3, h2⟩
  · rintro ⟨h1, h3, h2⟩
    exact ⟨h1, h2, h3⟩

/-- math-comp `simple_rcons`. -/
theorem simple_rcons (x : D) (p : List D) :
    G.Simple (p ++ [x]) ↔ x ∉ G.fband p ∧ G.Simple p := by
  rw [simple_catC]
  exact G.simple_cons x p

/-- math-comp `fproj_rot`. -/
theorem fproj_rot (n : ℕ) {p : List D} (hp : G.Simple p) (x : D) :
    G.fproj (p.rotate n) x = G.fproj p x := by
  by_cases hx : x ∈ G.fband p
  · obtain ⟨h1, h2⟩ := G.fprojP hx
    generalize G.fproj p x = y at h1 h2 ⊢
    rw [G.fproj_cface _ h2, G.simple_fproj ((G.simple_rot n p).2 hp) y (List.mem_rotate.2 h1)]
  · rw [G.fproj_of_not_mem hx, G.fproj_of_not_mem (by rwa [fband_rot])]

/-- math-comp `eq_simple`. -/
theorem eq_simple {p q : List D} (hf : G.fband p = G.fband q) (hl : p.length = q.length) :
    G.Simple p ↔ G.Simple q := by
  have key : ∀ {p q : List D}, G.fband p = G.fband q →
      ∀ c, c ∈ p.map (froot G.face) → c ∈ q.map (froot G.face) := by
    intro p q h c hc
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hc
    have : y ∈ G.fband q := h ▸ G.ring_fband p y hy
    obtain ⟨z, hz, hyz⟩ := this
    exact List.mem_map.2 ⟨z, hz, ((G.froot_face_eq_iff).2 hyz).symm⟩
  exact nodup_iff_of_mem_iff (by rw [List.length_map, List.length_map, hl])
    fun c => ⟨key hf c, key hf.symm c⟩

end FacePaths

/-- math-comp `simple_map`. -/
theorem simple_map {D' : Type*} [Finite D] [Finite D'] {G : Hypermap D} {G' : Hypermap D'}
    {h : D → D'} (hF : ∀ x y, G'.cface (h x) (h y) ↔ G.cface x y) (p : List D) :
    G'.Simple (p.map h) ↔ G.Simple p := by
  induction p with
  | nil => exact ⟨fun _ => List.nodup_nil, fun _ => List.nodup_nil⟩
  | cons x p ih =>
    rw [List.map_cons, simple_cons, simple_cons, ih]
    apply and_congr_left'
    apply not_congr
    simp only [mem_fband, List.mem_map]
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, hxa⟩
      exact ⟨a, ha, (hF x a).1 hxa⟩
    · rintro ⟨a, ha, hxa⟩
      exact ⟨h a, ⟨a, ha, rfl⟩, (hF x a).2 hxa⟩

/-! ### Special geometries: plain, cubic, precubic and pentagonal maps -/

section SpecialMaps

variable (G : Hypermap D)

/-- math-comp `plainb A`: all edges meeting `A` have size 2. -/
def PlainOn (A : Set D) : Prop := A ⊆ orderSet G.edge 2

/-- math-comp `plain G`: all edges (E-cycles) have size 2. -/
def Plain : Prop := G.PlainOn Set.univ

/-- math-comp `cubicb A`: all nodes meeting `A` have size 3. -/
def CubicOn (A : Set D) : Prop := A ⊆ orderSet G.node 3

/-- math-comp `cubic G`: all nodes (N-cycles) have size 3. -/
def Cubic : Prop := G.CubicOn Set.univ

/-- math-comp `precubic G`: all nodes have size at most 3 (math-comp states it as
`G \subset [pred x | order node x <= 3]`). -/
def Precubic : Prop := ∀ x, order G.node x ≤ 3

/-- math-comp `pentagonal G`: all faces have size at least 5. -/
def Pentagonal : Prop := ∀ x, 4 < G.arity x

/-- math-comp `quasicubic r`: all nodes not contained in `r` have size 3. -/
def Quasicubic (r : List D) : Prop := G.CubicOn {x | x ∉ r}

/-- math-comp `precubic_leq`. -/
theorem precubic_leq (hG : G.Precubic) (x : D) : order G.node x ≤ 3 := hG x

/-- math-comp `cubic_precubic`. -/
theorem cubic_precubic (hG : G.Cubic) : G.Precubic := fun x => le_of_eq (hG (Set.mem_univ x))

variable [Finite D]

/-- math-comp `plainP`. -/
theorem plainP {A : Set D} : G.PlainOn A ↔ ∀ x ∈ A, G.edge (G.edge x) = x ∧ G.edge x ≠ x := by
  constructor
  · intro hA x hx
    have ho : order G.edge x = 2 := hA hx
    refine ⟨?_, fun h => ?_⟩
    · have := iter_order G.edgeI x
      rw [ho] at this
      exact this
    · have h1 : order G.edge x = 1 :=
        order_cycle (p := [x]) (by show path (frel G.edge) x [x]; exact ⟨h, trivial⟩)
          (List.nodup_singleton x) List.mem_cons_self
      omega
  · intro hA x hx
    obtain ⟨h1, h2⟩ := hA x hx
    show order G.edge x = 2
    refine order_cycle (p := [x, G.edge x]) ?_ ?_ List.mem_cons_self
    · show path (frel G.edge) x [G.edge x, x]
      exact ⟨rfl, h1, trivial⟩
    · refine List.nodup_cons.2 ⟨fun h => h2 (List.mem_singleton.1 h).symm, List.nodup_singleton _⟩

/-- math-comp `plain_eq`. -/
theorem plain_eq (hG : G.Plain) (x : D) : G.edge (G.edge x) = x :=
  ((G.plainP).1 hG x (Set.mem_univ x)).1

/-- math-comp `plain_eq'`. -/
theorem plain_eq' (hG : G.Plain) (x : D) : G.node (G.face x) = G.edge x := by
  calc G.node (G.face x) = G.edge (G.edge (G.node (G.face x))) := (G.plain_eq hG _).symm
    _ = G.edge x := by rw [G.faceK]

/-- math-comp `plain_neq`. -/
theorem plain_neq (hG : G.Plain) (x : D) : G.edge x ≠ x :=
  ((G.plainP).1 hG x (Set.mem_univ x)).2

/-- math-comp `plain_orbit`. -/
theorem plain_orbit (hG : G.Plain) (x y : D) : G.cedge x y ↔ y ∈ [x, G.edge x] := by
  have hc : fcycle G.edge [x, G.edge x] := by
    show path (frel G.edge) x [G.edge x, x]
    exact ⟨rfl, G.plain_eq hG x, trivial⟩
  exact fconnect_cycle hc List.mem_cons_self

/-- math-comp `cubicP`. -/
theorem cubicP {A : Set D} :
    G.CubicOn A ↔ ∀ x ∈ A, G.node (G.node (G.node x)) = x ∧ G.node x ≠ x := by
  constructor
  · intro hA x hx
    have ho : order G.node x = 3 := hA hx
    refine ⟨?_, fun h => ?_⟩
    · have := iter_order G.nodeI x
      rw [ho] at this
      exact this
    · have h1 : order G.node x = 1 :=
        order_cycle (p := [x]) (by show path (frel G.node) x [x]; exact ⟨h, trivial⟩)
          (List.nodup_singleton x) List.mem_cons_self
      omega
  · intro hA x hx
    obtain ⟨h1, h2⟩ := hA x hx
    have h3 : G.node (G.node x) ≠ x := by
      intro h
      have := congrArg G.node h
      rw [h1] at this
      exact h2 this.symm
    have h4 : G.node x ≠ G.node (G.node x) := fun h => h2 (G.nodeI h).symm
    show order G.node x = 3
    refine order_cycle (p := [x, G.node x, G.node (G.node x)]) ?_ ?_ List.mem_cons_self
    · show path (frel G.node) x [G.node x, G.node (G.node x), x]
      exact ⟨rfl, rfl, h1, trivial⟩
    · simp [Ne.symm h2, Ne.symm h3, h4]

/-- math-comp `cubic_eq`. -/
theorem cubic_eq (hG : G.Cubic) (x : D) : G.node (G.node (G.node x)) = x :=
  ((G.cubicP).1 hG x (Set.mem_univ x)).1

/-- math-comp `cubic_eq'`. -/
theorem cubic_eq' (hG : G.Cubic) (x : D) : G.node (G.node x) = G.face (G.edge x) := by
  calc G.node (G.node x) = G.node (G.node (G.node (G.face (G.edge x)))) := by rw [G.edgeK]
    _ = G.face (G.edge x) := G.cubic_eq hG _

/-- math-comp `cubic_neq`. -/
theorem cubic_neq (hG : G.Cubic) (x : D) : G.node x ≠ x :=
  ((G.cubicP).1 hG x (Set.mem_univ x)).2

/-- math-comp `cubic_orbit`. -/
theorem cubic_orbit (hG : G.Cubic) (x y : D) :
    G.cnode x y ↔ y ∈ [x, G.node x, G.node (G.node x)] := by
  have hc : fcycle G.node [x, G.node x, G.node (G.node x)] := by
    show path (frel G.node) x [G.node x, G.node (G.node x), x]
    exact ⟨rfl, rfl, G.cubic_eq hG x, trivial⟩
  exact fconnect_cycle hc List.mem_cons_self

/-- math-comp `quasicubic_eq`. -/
theorem quasicubic_eq {r : List D} (hG : G.Quasicubic r) (x : D) (hx : x ∉ r) :
    G.node (G.node (G.node x)) = x :=
  ((G.cubicP).1 hG x hx).1

end SpecialMaps

/-! ### Records of geometrical assumptions -/

section Records

variable (G : Hypermap D)

/-- math-comp `planar_bridgeless`: the requirement for the four color theorem. -/
structure PlanarBridgeless [Fintype D] : Prop where
  /-- math-comp `planar_bridgeless_is_planar`. -/
  planar : G.Planar
  /-- math-comp `planar_bridgeless_is_bridgeless`. -/
  bridgeless : G.Bridgeless

/-- math-comp `plain_cubic`: required by quiz, quiztree, part. -/
structure PlainCubic : Prop where
  /-- math-comp `plain_cubic_is_plain`. -/
  plain : G.Plain
  /-- math-comp `plain_cubic_is_cubic`. -/
  cubic : G.Cubic

/-- math-comp `plain_cubic_connected`: required for the special Euler formula. -/
structure PlainCubicConnected : Prop extends G.PlainCubic where
  /-- math-comp `plain_cubic_connected_is_connected`. -/
  connected : G.Connected

/-- math-comp `planar_plain_cubic_connected`: required by discharge. -/
structure PlanarPlainCubicConnected [Fintype D] : Prop extends G.PlainCubicConnected where
  /-- math-comp `planar_plain_cubic_connected_is_planar`. -/
  planar : G.Planar

/-- math-comp `plain_cubic_pentagonal`: required by part, redpart, hubcap. -/
structure PlainCubicPentagonal : Prop extends G.PlainCubic where
  /-- math-comp `plain_cubic_pentagonal_is_pentagonal`. -/
  pentagonal : G.Pentagonal

/-- math-comp `planar_bridgeless_plain`: factored intermediate signature. -/
structure PlanarBridgelessPlain [Fintype D] : Prop extends G.PlanarBridgeless where
  /-- math-comp `planar_bridgeless_plain_is_plain`. -/
  plain : G.Plain

/-- math-comp `planar_bridgeless_plain_connected`: required by revsnip. -/
structure PlanarBridgelessPlainConnected [Fintype D] : Prop extends G.PlanarBridgelessPlain where
  /-- math-comp `planar_bridgeless_plain_connected_is_connected`. -/
  connected : G.Connected

/-- math-comp `planar_bridgeless_plain_precubic`: the inductive assumption. -/
structure PlanarBridgelessPlainPrecubic [Fintype D] : Prop extends G.PlanarBridgelessPlain where
  /-- math-comp `planar_bridgeless_plain_precubic_is_precubic`. -/
  precubic : G.Precubic

variable (r : List D)

/-- math-comp `plain_quasicubic r`: required by quiz. -/
structure PlainQuasicubic : Prop where
  /-- math-comp `plain_quasicubic_is_plain`. -/
  plain : G.Plain
  /-- math-comp `plain_quasicubic_is_quasicubic`. -/
  quasicubic : G.Quasicubic r

/-- math-comp `ucycle_plain_quasicubic r`: intermediate common base. -/
structure UCyclePlainQuasicubic : Prop extends G.PlainQuasicubic r where
  /-- math-comp `ucycle_plain_quasicubic_is_ucycle`: `r` is a duplicate-free N-cycle. -/
  ucycle : UCycle (frel G.node) r

/-- math-comp `ucycle_planar_plain_quasicubic r`: required by kempe. -/
structure UCyclePlanarPlainQuasicubic [Fintype D] : Prop extends G.UCyclePlainQuasicubic r where
  /-- math-comp `ucycle_planar_plain_quasicubic_is_planar`. -/
  planar : G.Planar

/-- math-comp `ucycle_plain_quasicubic_connected r`: required for the special Euler formula. -/
structure UCyclePlainQuasicubicConnected : Prop extends G.UCyclePlainQuasicubic r where
  /-- math-comp `ucycle_plain_quasicubic_connected_is_connected`. -/
  connected : G.Connected

/-- math-comp `scycle_planar_bridgeless_plain_quasicubic_connected r`: required by embed and
redpart. -/
structure SCyclePlanarBridgelessPlainQuasicubicConnected [Fintype D] : Prop
    extends G.UCyclePlainQuasicubicConnected r where
  /-- math-comp `scycle_planar_bridgeless_plain_quasicubic_connected_is_simple`. -/
  simple : G.Simple r
  /-- math-comp `scycle_planar_bridgeless_plain_quasicubic_connected_is_planar`. -/
  planar : G.Planar
  /-- math-comp `scycle_planar_bridgeless_plain_quasicubic_connected_is_bridgeless`. -/
  bridgeless : G.Bridgeless

variable {G r}

/-- math-comp `scycle_planar_bridgeless_plain_quasicubic_connected_is_scycle` (a coercion in
math-comp): `r` is a simple N-cycle. -/
theorem SCyclePlanarBridgelessPlainQuasicubicConnected.scycle [Fintype D]
    (h : G.SCyclePlanarBridgelessPlainQuasicubicConnected r) : G.SFCycle G.node r :=
  ⟨h.ucycle.1, h.simple⟩

/-- math-comp `scycle_planar_bridgeless_plain_quasicubic_connected_pbpc_base` (a coercion in
math-comp). -/
theorem SCyclePlanarBridgelessPlainQuasicubicConnected.toPlanarBridgelessPlainConnected
    [Fintype D] (h : G.SCyclePlanarBridgelessPlainQuasicubicConnected r) :
    G.PlanarBridgelessPlainConnected :=
  ⟨⟨⟨h.planar, h.bridgeless⟩, h.plain⟩, h.connected⟩

end Records

/-! ### The special forms of the Euler formula -/

section Euler

variable (G : Hypermap D) [Fintype D]

/-- math-comp `quasicubic_Euler`: the special form of the Euler formula for plain quasicubic
connected maps. Here `if r = [] then 0 else 1` is math-comp's `~~ nilp r`, the number of node
cycles of `r`. -/
theorem quasicubic_euler {r : List D} (hG : G.UCyclePlainQuasicubicConnected r) :
    G.Planar ↔ 6 * ((if r = [] then 0 else 1) + fcard G.face Set.univ) =
      Fintype.card D + (2 * r.length + 12) := by
  have hs := G.cnode_sym
  have hE : fcard G.edge Set.univ * 2 = Fintype.card D := by
    rw [fcard_order_set G.edgeI hG.plain closed_univ, Set.ncard_univ, Nat.card_eq_fintype_card]
  have hclr : Closed (frel G.node) {x | x ∈ r} :=
    Closed.of_forward hs fun x y hxy hx => (fconnect_cycle hG.ucycle.1 hx).1 (connect_of_rel hxy)
  have hNn : fcard G.node Set.univ = fcard G.node {x | x ∈ r} + fcard G.node {x | x ∉ r} :=
    nComp_compl hclr
  have hb : fcard G.node {x | x ∈ r} = if r = [] then 0 else 1 := by
    split_ifs with hr
    · subst hr
      simp only [List.not_mem_nil, Set.ofPred_false, nComp_empty]
    · obtain ⟨x, r1, rfl⟩ := List.exists_cons_of_ne_nil hr
      have : {y | y ∈ x :: r1} = comp (frel G.node) x :=
        Set.ext fun y => (fconnect_cycle hG.ucycle.1 List.mem_cons_self).symm
      rw [this]
      exact nComp_comp hs x
  have hnn : fcard G.node {x | x ∉ r} * 3 = {x | x ∉ r}.ncard :=
    fcard_order_set G.nodeI hG.quasicubic hclr.compl
  have hcard : {x | x ∈ r}.ncard + {x | x ∉ r}.ncard = Fintype.card D := by
    rw [← Nat.card_eq_fintype_card]
    exact Set.ncard_add_ncard_compl _
  have hr : {x | x ∈ r}.ncard = r.length := ncard_mem_of_nodup hG.ucycle.2
  have hC : nComp G.glink Set.univ = 1 := hG.connected
  have hEven := G.evenGenus
  unfold EvenGenus eulerLhs eulerRhs at hEven
  unfold Planar
  generalize (if r = [] then 0 else 1) = b at hb ⊢
  omega

/-- math-comp `cubic_Euler`: the special form of the Euler formula for plain cubic connected
maps. -/
theorem cubic_euler (hG : G.PlainCubicConnected) :
    G.Planar ↔ 6 * fcard G.face Set.univ = Fintype.card D + 12 := by
  have h := G.quasicubic_euler (r := [])
    ⟨⟨⟨hG.plain, fun x _ => hG.cubic (Set.mem_univ x)⟩, trivial, List.nodup_nil⟩, hG.connected⟩
  simpa using h

end Euler

/-! ### Mirror and dual images of the special geometries -/

section MirrorSpecials

variable (G : Hypermap D) [Finite D]

/-- math-comp `plain_dual`. -/
theorem plain_dual : G.dual.Plain ↔ G.Plain := by
  have key : ∀ x, order G.dual.edge x = order G.edge x := fun x =>
    order_inverse (f := G.edge) (g := fun a => G.node (G.face a)) G.edgeK G.faceK x
  constructor
  · intro h x _
    show order G.edge x = 2
    rw [← key]
    exact h (Set.mem_univ x)
  · intro h x _
    show order G.dual.edge x = 2
    rw [key]
    exact h (Set.mem_univ x)

/-- math-comp `plain_mirror`. -/
theorem plain_mirror : G.mirror.Plain ↔ G.Plain := by
  constructor
  · intro h x _
    show order G.edge x = 2
    have : order G.mirror.edge (G.face (G.edge x)) = 2 := h (Set.mem_univ _)
    rwa [order_mirror_edge, G.edgeK] at this
  · intro h x _
    show order G.mirror.edge x = 2
    rw [order_mirror_edge]
    exact h (Set.mem_univ _)

/-- `mirror` has the same node orbits (math-comp `order_finv nodeI`). -/
theorem order_mirror_node (x : D) : order G.mirror.node x = order G.node x :=
  order_inverse (f := G.node) (g := fun a => G.face (G.edge a)) G.nodeK G.edgeK x

/-- math-comp `cubic_mirror`. -/
theorem cubic_mirror : G.mirror.Cubic ↔ G.Cubic := by
  constructor
  · intro h x _
    show order G.node x = 3
    rw [← G.order_mirror_node]
    exact h (Set.mem_univ x)
  · intro h x _
    show order G.mirror.node x = 3
    rw [G.order_mirror_node]
    exact h (Set.mem_univ x)

/-- math-comp `precubic_mirror`. -/
theorem precubic_mirror : G.mirror.Precubic ↔ G.Precubic := by
  unfold Precubic
  simp only [G.order_mirror_node]

end MirrorSpecials

/-! ### R-links, adjacency and chordless rings -/

section Adj

variable (G : Hypermap D)

/-- math-comp `rlink x y`: `y` is in the same face as `edge x`. -/
def rlink (x y : D) : Prop := G.cface (G.edge x) y

/-- math-comp `srpath x0 x p`: `x :: p` is an R-path whose last dart is R-linked to `x0`, and
in which no dart lies in the face of a dart that follows its successor (in a bridgeless map,
for the R-cycle `x0 :: p` this is exactly face-simplicity, see `srcycleI`). -/
def SRPath (x0 : D) : D → List D → Prop
  | x, [] => G.cface (G.edge x) x0
  | x, y :: p => G.cface (G.edge x) y ∧ (∀ z ∈ p, ¬ G.cface x z) ∧ SRPath x0 y p

/-- math-comp `srcycle r`: `r` is a simple R-cycle (a "ring"). -/
def SRCycle : List D → Prop
  | [] => True
  | x :: p => G.SRPath x x p

/-- math-comp `rlink_connected a`: `a` is R-path connected, with paths included in `a`. -/
def RLinkConnected (a : Set D) : Prop :=
  ∀ x ∈ a, ∀ y ∈ a, ∃ p, path G.rlink (G.node (G.face x)) (p ++ [y]) ∧ ∀ z ∈ p, z ∈ a

/-- math-comp `adj x y`: `x` and `y` belong to adjacent faces, i.e., `rlink z y` for some `z`
in the face (orbit) of `x`. -/
def adj (x y : D) : Prop := ∃ z ∈ orbit G.face x, G.rlink z y

open Classical in
/-- math-comp `chordless r`: no non-consecutive darts of the cycle `r` belong to adjacent faces.
math-comp states it as `r \subset [pred x | [disjoint adj x & non_adj_r x]]`, where
`non_adj_r x` is `r` minus `prev r x` and `next r x`. -/
def Chordless (r : List D) : Prop :=
  ∀ x ∈ r, ∀ y ∈ r, G.adj x y → y = prev r x ∨ y = next r x

/-- math-comp `insertE p`: `[e1, edge e1, ..., en, edge en]` for `p = [e1, ..., en]`; this is
the edge closure of `p` when `G` is plain. -/
def insertE : List D → List D
  | [] => []
  | x :: p => x :: G.edge x :: insertE p

/-- math-comp `rlinkE`. -/
theorem rlinkE (x : D) : G.rlink x (G.edge x) := connect_refl _

/-- math-comp `insertE_seqb`. -/
theorem insertE_seqb (b : Bool) (x : D) :
    G.insertE (List.replicate b.toNat x) =
      List.replicate b.toNat x ++ List.replicate b.toNat (G.edge x) := by
  cases b <;> rfl

/-- math-comp `size_insertE`. -/
theorem size_insertE (p : List D) : (G.insertE p).length = 2 * p.length := by
  induction p with
  | nil => rfl
  | cons x p ih =>
    simp only [insertE, List.length_cons, ih]
    omega

/-- math-comp `insertE_cat`. -/
theorem insertE_cat (p1 p2 : List D) : G.insertE (p1 ++ p2) = G.insertE p1 ++ G.insertE p2 := by
  induction p1 with
  | nil => rfl
  | cons x p1 ih => simp only [List.cons_append, insertE, ih]

/-- `insertE` commutes with `take` (helper for math-comp `insertE_rot`). -/
theorem insertE_take (k : ℕ) (p : List D) : G.insertE (p.take k) = (G.insertE p).take (2 * k) := by
  induction p generalizing k with
  | nil => simp [insertE]
  | cons x p ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [List.take_succ_cons, insertE, insertE, ih, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
        List.take_succ_cons, List.take_succ_cons]

/-- `insertE` commutes with `drop` (helper for math-comp `insertE_rot`). -/
theorem insertE_drop (k : ℕ) (p : List D) : G.insertE (p.drop k) = (G.insertE p).drop (2 * k) := by
  induction p generalizing k with
  | nil => simp [insertE]
  | cons x p ih =>
    cases k with
    | zero => rfl
    | succ k =>
      rw [List.drop_succ_cons, insertE, ih, show 2 * (k + 1) = 2 * k + 1 + 1 by ring,
        List.drop_succ_cons, List.drop_succ_cons]

/-- math-comp `insertE_rot`. -/
theorem insertE_rot (n : ℕ) (p : List D) :
    G.insertE (p.rotate n) = (G.insertE p).rotate (2 * n) := by
  rw [List.rotate_eq_drop_append_take_mod, List.rotate_eq_drop_append_take_mod, insertE_cat,
    size_insertE, Nat.mul_mod_mul_left, insertE_drop, insertE_take]

/-- `Chordless` computed with an arbitrary decidable equality on the darts. -/
theorem chordless_iff [DecidableEq D] {r : List D} :
    G.Chordless r ↔ ∀ x ∈ r, ∀ y ∈ r, G.adj x y → y = prev r x ∨ y = next r x := by
  unfold Chordless
  convert Iff.rfl

open Classical in
/-- math-comp `chordless_rot`. -/
theorem chordless_rot {r : List D} (hr : r.Nodup) (n : ℕ) :
    G.Chordless (r.rotate n) ↔ G.Chordless r := by
  unfold Chordless
  simp only [List.mem_rotate, next_rotate hr, prev_rotate hr]

variable [Finite D]

/-- math-comp `rlinkFr`. -/
theorem rlinkFr {y1 y2 : D} (h : G.cface y1 y2) (x : D) : G.rlink x y1 ↔ G.rlink x y2 :=
  G.cface_sym.same_r h (G.edge x)

/-- math-comp `srcycleI`: in a bridgeless map, the simple R-cycles are the rings. -/
theorem srcycleI (hG : G.Bridgeless) (r : List D) : G.SCycle G.rlink r ↔ G.SRCycle r := by
  cases r with
  | nil => exact ⟨fun _ => trivial, fun _ => ⟨trivial, List.nodup_nil⟩⟩
  | cons x0 p =>
    show path G.rlink x0 (p ++ [x0]) ∧ G.Simple (x0 :: p) ↔ G.SRPath x0 x0 p
    rw [simple_recI]
    show path G.rlink x0 (p ++ [x0]) ∧ (x0 ∉ G.fband p ∧ G.SimpleRec p) ↔ G.SRPath x0 x0 p
    suffices h : ∀ x, path G.rlink x (p ++ [x0]) ∧ (x ∉ G.fband p ∧ G.SimpleRec p) ↔
        G.SRPath x0 x p from h x0
    induction p with
    | nil =>
      intro x
      show (G.rlink x x0 ∧ True) ∧ (x ∉ G.fband [] ∧ True) ↔ G.cface (G.edge x) x0
      have : x ∉ G.fband [] := fun ⟨y, hy, _⟩ => by simp at hy
      exact ⟨fun h => h.1.1, fun h => ⟨⟨h, trivial⟩, this, trivial⟩⟩
    | cons y p ih =>
      intro x
      show (G.rlink x y ∧ path G.rlink y (p ++ [x0])) ∧
          (x ∉ G.fband (y :: p) ∧ (y ∉ G.fband p ∧ G.SimpleRec p)) ↔
        G.cface (G.edge x) y ∧ (∀ z ∈ p, ¬ G.cface x z) ∧ G.SRPath x0 y p
      rw [← ih y]
      constructor
      · rintro ⟨⟨hxy, hp⟩, hx, hy, hr⟩
        exact ⟨hxy, fun z hz hxz => hx ((G.fband_cons _ _ _).2 (Or.inr ⟨z, hz, hxz⟩)), hp, hy, hr⟩
      · rintro ⟨hxy, hx, hp, hy, hr⟩
        refine ⟨⟨hxy, hp⟩, ?_, hy, hr⟩
        rw [fband_cons]
        rintro (h | ⟨z, hz, hxz⟩)
        · exact G.bridgeless_cface hG x (connect_trans h (G.cfaceC.1 hxy))
        · exact hx z hz hxz

/-- math-comp `simplify_rlink`: an R-path can be shortened to a simple R-path with the same
endpoints, that visits only darts of the original path. -/
theorem simplify_rlink {x : D} {p : List D} (hp : path G.rlink x p) :
    ∃ p', (path G.rlink x p' ∧ G.Simple p') ∧
      last x p = last x p' ∧ (p = [] ↔ p' = []) ∧ ∀ y ∈ p', y ∈ p := by
  suffices h : ∀ n (x : D) (p : List D), p.length < n → path G.rlink x p →
      ∃ p', (path G.rlink x p' ∧ G.Simple p') ∧
        last x p = last x p' ∧ (p = [] ↔ p' = []) ∧ ∀ y ∈ p', y ∈ p from
    h _ x p (Nat.lt_succ_self _) hp
  intro n
  induction n with
  | zero => intro x p hn; omega
  | succ n ih =>
    intro x p hn hp
    cases p with
    | nil => exact ⟨[], ⟨trivial, List.nodup_nil⟩, rfl, Iff.rfl, fun _ h => h⟩
    | cons y p =>
      obtain ⟨hxy, hyp⟩ := hp
      by_cases hy : y ∈ G.fband p
      · obtain ⟨z, hz, hyz⟩ := hy
        obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hz
        have hxz : path G.rlink x (z :: p2) := ⟨(G.rlinkFr hyz x).1 hxy, path.of_append_cons hyp⟩
        have hlt : (z :: p2).length < n := by
          simp only [List.length_cons, List.length_append] at hn ⊢
          omega
        obtain ⟨q, hq, hlq, hnq, hsub⟩ := ih x (z :: p2) hlt hxz
        refine ⟨q, hq, ?_, ?_, ?_⟩
        · rw [← hlq, last_cons, last_append, last_cons, last_cons]
        · have : q ≠ [] := fun h => List.cons_ne_nil z p2 (hnq.2 h)
          exact ⟨fun h => absurd h (List.cons_ne_nil _ _), fun h => absurd h this⟩
        · intro w hw
          have := hsub w hw
          simp only [List.mem_cons, List.mem_append] at this ⊢
          tauto
      · obtain ⟨q, ⟨hq, hqs⟩, hlq, -, hsub⟩ :=
          ih y p (by simp only [List.length_cons] at hn; omega) hyp
        refine ⟨y :: q, ⟨⟨hxy, hq⟩, (G.simple_cons y q).2 ⟨?_, hqs⟩⟩, hlq, ?_, ?_⟩
        · rintro ⟨w, hw, hyw⟩
          exact hy ⟨w, hsub w hw, hyw⟩
        · exact ⟨fun h => absurd h (List.cons_ne_nil _ _), fun h => absurd h (List.cons_ne_nil _ _)⟩
        · intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hsub w hw)

/-- math-comp `adjP`. -/
theorem adjP {x y : D} : G.adj x y ↔ ∃ z, G.cface x z ∧ G.rlink z y :=
  exists_congr fun _ => and_congr_left' (fconnect_orbit G.faceI).symm

/-- math-comp `rlink_adj`. -/
theorem rlink_adj {x y : D} (h : G.rlink x y) : G.adj x y := G.adjP.2 ⟨x, connect_refl x, h⟩

/-- math-comp `adjE`. -/
theorem adjE (x : D) : G.adj x (G.edge x) := G.rlink_adj (G.rlinkE x)

/-- math-comp `adjF`. -/
theorem adjF {x1 x2 : D} (h : G.cface x1 x2) (y : D) : G.adj x1 y ↔ G.adj x2 y := by
  rw [adjP, adjP]
  exact exists_congr fun z => and_congr_left' (G.same_cface h z)

/-- math-comp `adjFr`. -/
theorem adjFr {y1 y2 : D} (h : G.cface y1 y2) (x : D) : G.adj x y1 ↔ G.adj x y2 := by
  rw [adjP, adjP]
  exact exists_congr fun z => and_congr_right' (G.rlinkFr h z)

/-- math-comp `adjF1`. -/
theorem adjF1 (x y : D) : G.adj x y ↔ G.adj (G.face x) y := G.adjF (fconnect1 _ x) y

/-- math-comp `adjF1r`. -/
theorem adjF1r (x y : D) : G.adj x y ↔ G.adj x (G.face y) := G.adjFr (fconnect1 _ y) x

/-- math-comp `adjN`. -/
theorem adjN (x : D) : G.adj (G.node x) x := by
  have := (G.adjF1r (G.node x) (G.edge (G.node x))).1 (G.adjE (G.node x))
  rwa [G.nodeK] at this

/-- math-comp `adjC`: `adj` is symmetric in a plain map. -/
theorem adjC (hG : G.Plain) (x y : D) : G.adj x y ↔ G.adj y x := by
  have key : ∀ x y, G.adj x y → G.adj y x := by
    intro x y h
    obtain ⟨z, hxz, hzy⟩ := G.adjP.1 h
    refine G.adjP.2 ⟨G.edge z, G.cfaceC.1 hzy, ?_⟩
    show G.cface (G.edge (G.edge z)) x
    rw [G.plain_eq hG]
    exact G.cfaceC.1 hxz
  exact ⟨key x y, key y x⟩

/-- math-comp `no_adj_adj`. -/
theorem no_adj_adj {x y1 y2 : D} (h1 : ¬ G.adj x y1) (h2 : G.adj x y2) : ¬ G.cface y1 y2 :=
  fun h => h1 ((G.adjFr h x).2 h2)

/-- math-comp `adj_no_cface`. -/
theorem adj_no_cface (hG : G.Bridgeless) {x y : D} (h : G.adj x y) : ¬ G.cface x y := by
  obtain ⟨z, hxz, hzy⟩ := G.adjP.1 h
  intro hxy
  exact G.bridgeless_cface hG z
    (connect_trans (connect_trans (G.cfaceC.1 hxz) hxy) (G.cfaceC.1 hzy))

/-- math-comp `mem_insertE`. -/
theorem mem_insertE (hG : G.Plain) (p : List D) (x : D) :
    x ∈ G.insertE p ↔ ∃ y ∈ p, G.cedge x y := by
  induction p with
  | nil => simp [insertE]
  | cons y p ih =>
    have h1 : G.cedge x y ↔ x = y ∨ x = G.edge y := by
      rw [G.cedgeC, G.plain_orbit hG, List.mem_cons, List.mem_singleton]
    rw [insertE, List.mem_cons, List.mem_cons, ih]
    simp only [List.mem_cons, exists_eq_or_imp, h1, or_assoc]

end Adj

end Hypermap

end FourColor
