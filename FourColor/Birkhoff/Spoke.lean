/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Birkhoff.Valid

/-!
# Consequences of the Birkhoff theorem: spoke rings and pentagonality (port of `birkhoff.v`,
section `Birkhoff`, from `nontrivial_cycle2` to the end)

For a minimal counter-example `G` (`cexG : G.MinimalCounterExample`):

* `G.spoke y` : the dart on the first ring of faces surrounding a central hub face, that
  corresponds to a dart `y` in that hub (`= face (edge y)`) (math-comp `spoke`).
* `G.spokeRing x` : the (contour) ring obtained by mapping `spoke` on the reverse face cycle at
  `x` (math-comp `spoke_ring x`); it is simple (a ring), and chordless in a minimal
  counter-example (`chordless_spoke_ring`).
* `G.Adj01 y z` : `y` and `z` belong to the same face or to adjacent faces (math-comp `adj01`).
* `G.min_arity` : the faces of a minimal counter-example have at least five sides, and
  `minimal_counter_example_is_plain_cubic_pentagonal` packages this as a
  `PlainCubicPentagonal` record.

## Porting notes

* The section hypothesis `geoG : minimal_counter_example G` is the explicit argument `cexG`; the
  section variable `x` of section `SpokeRing` is an explicit argument of the lemmas that use it.
* `nontrivial_ring m r = false` becomes `¬ G.NontrivialRing m r`; `fcard face (predI (adj y)
  (adj x))` is `fcard G.face {z | G.adj y z ∧ G.adj x z}`.
* The index computations of the Coq proofs (`find`, `nth`, `rot_to`, `prev_nth`) use the
  `getElem` lemmas of Mathlib's `List.next`/`List.prev` (`List.next_getElem`,
  `List.prev_getElem`); the final case analyses on the ring positions are decided by `omega`
  or `decide`.
* The math-comp lemmas on `next`/`prev` used here (`mem_next`, `mem_prev`, `next_prev`,
  `prev_next`, `next_map`, `next_rev`, `next_cycle`, `prev_cycle`, `cycle_from_next`) are
  private in `FourColor.Patch`, `FourColor.Snip` and `FourColor.Revsnip`; they are reproved
  here as private lemmas, in the same way.
-/

namespace FourColor

open Function

universe u

/-! ### Cyclic successor and predecessor (private copies, as in `FourColor.Revsnip`) -/

section NextPrev

variable {α β : Type*} [DecidableEq α]

private theorem next_of_not_mem {p : List α} {x : α} (h : x ∉ p) : next p x = x := by
  cases p with
  | nil => rfl
  | cons y p => exact nextAt_of_not_mem h

private theorem prev_of_not_mem {p : List α} {x : α} (h : x ∉ p) : prev p x = x := by
  cases p with
  | nil => rfl
  | cons y p =>
    show prevAt x y y p = x
    rw [prevAt_of_not_mem (fun hm => h (List.mem_cons_of_mem _ hm)),
      ite_eq_right (fun e => h (List.mem_cons.2 (Or.inl e)))]

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

private theorem next_eq_listNext {p : List α} {x : α} (hx : x ∈ p) :
    next p x = p.next x hx := by
  cases p with
  | nil => simp at hx
  | cons y p =>
    show nextAt x y y p = _
    rw [nextAt_eq_nextOr hx]
    rfl

omit [DecidableEq α] in
private theorem last_eq_getLast (z : α) (p : List α) :
    last z p = (z :: p).getLast (List.cons_ne_nil z p) := by
  induction p generalizing z with
  | nil => rfl
  | cons w p ih => rw [last_cons, ih w, List.getLast_cons_cons]

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

/-- math-comp `mem_prev`. -/
private theorem mem_prev {p : List α} (hp : p.Nodup) {x : α} : prev p x ∈ p ↔ x ∈ p := by
  by_cases hx : x ∈ p
  · rw [prev_eq_listPrev hp hx]
    exact ⟨fun _ => hx, fun _ => List.prev_mem _ _ _⟩
  · rw [prev_of_not_mem hx]

/-- math-comp `prev_next`. -/
private theorem prev_next {p : List α} (hp : p.Nodup) (x : α) : prev p (next p x) = x := by
  by_cases hx : x ∈ p
  · rw [prev_eq_listPrev hp (mem_next.2 hx)]
    simp only [next_eq_listNext hx]
    exact List.prev_next p hp x hx
  · rw [next_of_not_mem hx, prev_of_not_mem hx]

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
    (x : α) : next (p.map f) (f x) = f (next p x) := by
  cases p with
  | nil => rfl
  | cons y p => exact nextAt_map hf x y y p

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

/-- math-comp `cycle_from_next`. -/
private theorem cycle_from_next {e : α → α → Prop} {p : List α} (hp : p.Nodup)
    (h : ∀ x ∈ p, e x (next p x)) : cycle e p := by
  cases p with
  | nil => trivial
  | cons y p => exact path_from_nextAt hp h

/-- `next` on positions (math-comp `next_nth`). -/
private theorem next_getElem' {p : List α} (hp : p.Nodup) {i : ℕ} (hi : i < p.length) :
    next p p[i] = p[(i + 1) % p.length]'(Nat.mod_lt _ (by omega)) := by
  rw [next_eq_listNext (List.getElem_mem hi)]
  exact List.next_getElem p hp i hi

/-- `prev` on positions (math-comp `prev_nth`). -/
private theorem prev_getElem' {p : List α} (hp : p.Nodup) {i : ℕ} (hi : i < p.length) :
    prev p p[i] = p[(i + (p.length - 1)) % p.length]'(Nat.mod_lt _ (by omega)) := by
  rw [prev_eq_listPrev hp (List.getElem_mem hi)]
  exact List.prev_getElem p hp i hi

/-- The successor position, without `%`. -/
private theorem succ_mod_eq {n i : ℕ} (hi : i < n) :
    (i + 1) % n = if i + 1 = n then 0 else i + 1 := by
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

/-- The predecessor position, without `%`. -/
private theorem pred_mod_eq {n i : ℕ} (hi : i < n) :
    (i + (n - 1)) % n = if i = 0 then n - 1 else i - 1 := by
  split_ifs with h
  · subst h
    rw [Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [show i + (n - 1) = (i - 1) + n by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)

/-- In a duplicate-free sequence, `next` in terms of positions. -/
private theorem eq_next_iff {p : List α} (hp : p.Nodup) {i j : ℕ} (hi : i < p.length)
    (hj : j < p.length) : p[j] = next p p[i] ↔ j = if i + 1 = p.length then 0 else i + 1 := by
  rw [next_getElem' hp hi, hp.getElem_inj_iff]
  simp only [succ_mod_eq hi]

/-- In a duplicate-free sequence, `prev` in terms of positions. -/
private theorem eq_prev_iff {p : List α} (hp : p.Nodup) {i j : ℕ} (hi : i < p.length)
    (hj : j < p.length) : p[j] = prev p p[i] ↔ j = if i = 0 then p.length - 1 else i - 1 := by
  rw [prev_getElem' hp hi, hp.getElem_inj_iff]
  simp only [pred_mod_eq hi]

end NextPrev

namespace Hypermap

section Birkhoff

variable {D : Type u} [Fintype D] [DecidableEq D] {G : Hypermap D}

/-- The Birkhoff theorem for rings of size at most `4` (math-comp `Birkhoff`, with
`size r == 5` false). -/
theorem birkhoff_lt5 (cexG : G.MinimalCounterExample) {r : List D} (hr5 : r.length < 5)
    (hr : G.SCycle G.rlink r) : ¬ G.NontrivialRing 0 r := by
  have h := G.birkhoff cexG hr5.le hr
  rwa [beq_eq_false_iff_ne.2 hr5.ne] at h

omit [DecidableEq D] in
/-- math-comp `nontrivial_cycle2`. -/
theorem nontrivial_cycle2 (cexG : G.MinimalCounterExample) {x y : D}
    (Ur : G.SCycle G.rlink [x, y]) (y'ex : G.edge x ≠ y) : G.NontrivialRing 0 [x, y] := by
  have hpl := cexG.plain
  have hcub := cexG.cubic
  have hbr := cexG.bridgeless
  have hGp : G.Planar := cexG.planar
  have hxy : G.cface (G.edge x) y := Ur.1.1
  have hyx : G.cface (G.edge y) x := Ur.1.2.1
  rw [G.nontrivial0P]
  refine ⟨⟨G.node x, ((G.diskN_node _) x (G.node x) rfl).1
    (G.mem_diskN_of_mem _ List.mem_cons_self), ?_⟩, ⟨G.node (G.edge x), ?_, ?_⟩⟩
  · rintro ⟨z, hz, hnz⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · -- `x = face (edge (node x))`
      apply G.bridgeless_cface hbr (G.node z)
      rw [G.cface1r]
      rwa [G.nodeK]
    · -- `face (edge x) = node (node x)`
      apply G.bridgeless_cface hbr (G.node (G.node x))
      have h1 : G.cface (G.edge x) (G.node x) := connect_trans hxy (G.cfaceC.1 hnz)
      rw [← G.nodeK (G.node x), ← G.cface1r, G.cface1, ← G.cubic_eq' hcub] at h1
      exact h1
  · intro h
    have h' : G.edge x ∈ G.diskN [x, y] := ((G.diskN_node _) _ _ rfl).2 h
    rcases (G.diskN_E _ _).1 h' with hr | hE
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with h1 | h1
      · exact G.plain_neq hpl x h1
      · exact y'ex h1
    · have := ((G.diskE_edge hGp Ur) x (G.edge x) rfl).2 hE
      exact this.2 List.mem_cons_self
  · rintro ⟨z, hz, hnz⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · -- `node (node (edge z)) = face z`
      have hn : G.node (G.node (G.edge z)) = G.face z := by
        rw [G.cubic_eq' hcub, G.plain_eq hpl]
      apply G.bridgeless_cface hbr (G.face z)
      rw [← G.nodeK (G.node (G.edge z)), hn, ← G.cface1] at hnz
      rw [← G.cface1]
      exact G.cfaceC.1 hnz
    · apply G.bridgeless_cface hbr (G.node (G.edge x))
      have h1 : G.cface (G.edge x) (G.node (G.edge x)) := connect_trans hxy (G.cfaceC.1 hnz)
      have h2 : G.cface (G.face (G.edge (G.node (G.edge x)))) (G.node (G.edge x)) := by
        rw [G.nodeK]
        exact h1
      rw [← G.cface1] at h2
      exact G.cfaceC.1 h2

/-- math-comp `double_dart`. -/
theorem double_dart (cexG : G.MinimalCounterExample) {x y : D} (xFy : G.cface x y)
    (exFey : G.cface (G.edge x) (G.edge y)) : x = y := by
  by_contra y'x
  have hpl := cexG.plain
  have Ur : G.SCycle G.rlink [x, G.edge y] := by
    rw [G.srcycleI cexG.bridgeless]
    refine ⟨exFey, by simp, ?_⟩
    show G.cface (G.edge (G.edge y)) x
    rw [G.plain_eq hpl]
    exact G.cfaceC.1 xFy
  exact G.birkhoff_lt5 cexG (by simp) Ur
    (G.nontrivial_cycle2 cexG Ur fun h => y'x (G.edgeI h))

/-! ### The spoke ring (math-comp section `SpokeRing`) -/

/-- math-comp `spoke y`: the dart on the first ring of faces surrounding the hub face of `y`,
that corresponds to `y` (`face (edge y)`). -/
def spoke (y : D) : D := G.face (G.edge y)

omit [DecidableEq D] in
/-- math-comp `inj_spoke`. -/
theorem inj_spoke : Injective G.spoke := fun _ _ h => G.edgeI (G.faceI h)

/-- math-comp `spoke_ring x`: the ring obtained by mapping `spoke` on the reverse face cycle
at `x`. -/
noncomputable def spokeRing (x : D) : List D := (orbit G.face x).reverse.map G.spoke

omit [DecidableEq D] in
/-- math-comp `mem_spoke_ring`. -/
theorem mem_spoke_ring {x y : D} : y ∈ G.spokeRing x ↔ G.cface x (G.node y) := by
  have hy : y = G.spoke (G.node y) := (G.nodeK y).symm
  conv_lhs => rw [hy]
  rw [spokeRing, List.mem_map_of_injective G.inj_spoke, List.mem_reverse,
    ← fconnect_orbit G.faceI]

omit [DecidableEq D] in
/-- The spoke ring is duplicate-free. -/
theorem spoke_ring_uniq (x : D) : (G.spokeRing x).Nodup :=
  (List.nodup_reverse.2 (orbit_uniq G.faceI x)).map G.inj_spoke

/-- math-comp `next_spoke_ring`. -/
theorem next_spoke_ring (cexG : G.MinimalCounterExample) {x y : D} (ry : y ∈ G.spokeRing x) :
    next (G.spokeRing x) y = G.face (G.spoke y) := by
  have hp := orbit_uniq G.faceI x
  have cycFp := CfMap.cycle_orbit G.faceI x
  have hny : G.node y ∈ orbit G.face x := (fconnect_orbit G.faceI).1 (G.mem_spoke_ring.1 ry)
  have hy : y = G.spoke (G.node y) := (G.nodeK y).symm
  have h1 : G.face (prev (orbit G.face x) (G.node y)) = G.node y := prev_cycle cycFp hny
  have h2 : prev (orbit G.face x) (G.node y) = G.edge (G.node (G.node y)) := by
    conv_rhs => rw [← h1]
    rw [G.faceK]
  calc next (G.spokeRing x) y = next (G.spokeRing x) (G.spoke (G.node y)) := by rw [← hy]
    _ = G.spoke (prev (orbit G.face x) (G.node y)) := by
        rw [spokeRing, next_map G.inj_spoke, next_rev hp]
    _ = G.face (G.spoke y) := by
        rw [h2, spoke, G.plain_eq cexG.plain, G.cubic_eq' cexG.cubic, spoke]

/-- math-comp `scycle_spoke_ring`. -/
theorem scycle_spoke_ring (cexG : G.MinimalCounterExample) (x : D) :
    G.SCycle G.rlink (G.spokeRing x) := by
  refine ⟨cycle_from_next (G.spoke_ring_uniq x) fun y ry => ?_, ?_⟩
  · rw [G.next_spoke_ring cexG ry]
    show G.cface (G.edge y) (G.face (G.face (G.edge y)))
    rw [← G.cface1r, ← G.cface1r]
  · show ((G.spokeRing x).map (froot G.face)).Nodup
    rw [spokeRing, List.map_map]
    refine (List.nodup_reverse.2 (orbit_uniq G.faceI x)).map_on fun y hy z hz hyz => ?_
    rw [List.mem_reverse, ← fconnect_orbit G.faceI] at hy hz
    have h : G.cface (G.spoke y) (G.spoke z) := G.froot_face_eq_iff.1 hyz
    rw [spoke, spoke, ← G.cface1, ← G.cface1r] at h
    exact G.double_dart cexG (connect_trans (G.cfaceC.1 hy) hz) h

/-- math-comp `diskF_spoke_ring`. -/
theorem diskF_spoke_ring (cexG : G.MinimalCounterExample) (x y : D) :
    y ∈ G.diskF (G.spokeRing x) ↔ G.cface x y := by
  have hbr := cexG.bridgeless
  constructor
  · rintro ⟨⟨z, rz, zDy⟩, rF'y⟩
    -- the darts reachable from `face (edge z)` by `dlink` steps
    suffices h : ∀ w, connect (G.dlink (G.spokeRing x)) (G.face (G.edge z)) w →
        G.cface x w ∨ w ∈ G.spokeRing x ∨ ∃ z' ∈ G.spokeRing x, w = G.face (G.edge z') by
      rcases h y zDy with h | h | ⟨z', rz', rfl⟩
      · exact h
      · exact absurd (G.ring_fband _ y h) rF'y
      · refine absurd ⟨G.face (G.face (G.edge z')), ?_, fconnect1 _ _⟩ rF'y
        rw [← spoke, ← G.next_spoke_ring cexG rz']
        exact mem_next.2 rz'
    intro w hw
    induction hw with
    | refl => exact Or.inr (Or.inr ⟨z, rz, rfl⟩)
    | @tail w w' _ hstep ih =>
      obtain ⟨r'w, hc⟩ := hstep
      rcases ih with xFw | rw | ⟨z', rz', rfl⟩
      · rcases hc with hw' | hw'
        · exact Or.inr (Or.inl (G.mem_spoke_ring.2 (hw' ▸ xFw)))
        · exact Or.inl (hw' ▸ (G.cface1r _ _).1 xFw)
      · exact absurd rw r'w
      · rcases hc with hw' | hw'
        · left
          rw [← G.cubic_eq' cexG.cubic] at hw'
          rw [← G.nodeI hw']
          exact G.mem_spoke_ring.1 rz'
        · right; left
          rw [← hw', ← spoke, ← G.next_spoke_ring cexG rz']
          exact mem_next.2 rz'
  · intro xFy
    refine ⟨?_, ?_⟩
    · -- `y = node (face (edge y))` and `face (edge y)` is on the ring
      have h : G.face (G.edge y) ∈ G.spokeRing x := by
        rw [G.mem_spoke_ring, G.edgeK]
        exact xFy
      exact ((G.diskN_node _) _ _ (G.edgeK y)).1 (G.mem_diskN_of_mem _ h)
    · rintro ⟨z, rz, yFz⟩
      apply G.bridgeless_cface hbr (G.node z)
      have h1 : G.cface (G.node z) z :=
        connect_trans (G.cfaceC.1 (G.mem_spoke_ring.1 rz)) (connect_trans xFy yFz)
      have h2 : G.cface (G.node z) (G.face (G.edge (G.node z))) := by
        rw [G.nodeK]
        exact h1
      exact (G.cface1r _ _).2 h2

/-- math-comp `chordless_spoke_ring`. -/
theorem chordless_spoke_ring (cexG : G.MinimalCounterExample) (x : D) :
    G.Chordless (G.spokeRing x) := by
  have hbr := cexG.bridgeless
  have hpl := cexG.plain
  have hG := cexG.toPlanarBridgelessPlainConnected
  have scycRr := G.scycle_spoke_ring cexG x
  have Ur := G.spoke_ring_uniq x
  refine G.chordless_iff.2 fun y1 ry1 y2 ry2 y1Ay2 => ?_
  by_contra hne
  push Not at hne
  obtain ⟨ry1'y2, ry1''y2⟩ := hne
  obtain ⟨z, y1Fz, ezFy2⟩ := G.adjP.1 y1Ay2
  have ezFy2 : G.cface (G.edge z) y2 := ezFy2
  have xFny1 := G.mem_spoke_ring.1 ry1
  have xFny2 := G.mem_spoke_ring.1 ry2
  have ny2Fny1 : G.cface (G.node y2) (G.node y1) := connect_trans (G.cfaceC.1 xFny2) xFny1
  set q := [G.node y2, G.edge z, G.edge (G.node y1)] with hq
  have scycRq : G.SCycle G.rlink q := by
    rw [G.srcycleI hbr]
    refine ⟨?_, ?_, ?_, by simp, ?_⟩
    · show G.cface (G.edge (G.node y2)) (G.edge z)
      rw [G.cface1, G.nodeK]
      exact G.cfaceC.1 ezFy2
    · intro w hw hw'
      simp only [List.mem_singleton] at hw
      subst hw
      exact G.bridgeless_cface hbr (G.node y1) (connect_trans (G.cfaceC.1 ny2Fny1) hw')
    · show G.cface (G.edge (G.edge z)) (G.edge (G.node y1))
      rw [G.plain_eq hpl, G.cface1r, G.nodeK]
      exact G.cfaceC.1 y1Fz
    · show G.cface (G.edge (G.edge (G.node y1))) (G.node y2)
      rw [G.plain_eq hpl]
      exact G.cfaceC.1 ny2Fny1
  apply G.birkhoff_lt5 cexG (by simp [hq]) scycRq
  rw [G.nontrivial0P]
  -- the dart `t = prev r y1`, inside `q`
  set t := G.node (G.edge (G.node y1)) with ht
  have Dt : t = prev (G.spokeRing x) y1 := by
    set P := prev (G.spokeRing x) y1 with hP
    have rP : P ∈ G.spokeRing x := (mem_prev Ur).2 ry1
    have h1 : G.face (G.face (G.edge P)) = y1 := by
      rw [← spoke, ← G.next_spoke_ring cexG rP, hP, next_prev Ur]
    rw [ht, ← h1, G.faceK, G.edgeK]
  have rt : t ∈ G.spokeRing x := by rw [Dt]; exact (mem_prev Ur).2 ry1
  have xFnt := G.mem_spoke_ring.1 rt
  refine ⟨⟨t, ((G.diskN_node q) _ _ rfl).1 (G.mem_diskN_of_mem q (by simp [hq])), ?_⟩,
    ⟨G.node (G.node y1), ?_, ?_⟩⟩
  · rintro ⟨w, hw, tFw⟩
    simp only [hq, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · apply G.bridgeless_cface hbr (G.node t)
      have h1 : G.cface (G.node t) t :=
        connect_trans (G.cfaceC.1 xFnt) (connect_trans xFny2 (G.cfaceC.1 tFw))
      have h2 : G.cface (G.node t) (G.face (G.edge (G.node t))) := by
        rw [G.nodeK]
        exact h1
      exact (G.cface1r _ _).2 h2
    · exact ry1'y2 ((G.scycle_cface scycRr _ ry2 _ rt
        (G.cfaceC.1 (connect_trans tFw ezFy2))).trans Dt)
    · apply G.bridgeless_cface hbr t
      have h2 : G.cface t (G.face (G.edge t)) := by
        rw [ht, G.nodeK]
        exact tFw
      exact (G.cface1r _ _).2 h2
  · intro h
    have h' : G.node y1 ∈ G.diskN q := ((G.diskN_node q) _ _ rfl).2 h
    rw [← G.plain_eq hpl (G.node y1)] at h'
    exact G.diskN_edge_ring hG scycRq (G.size_proper_ring (by simp [hq])) (by simp [hq]) h'
  · rintro ⟨w, hw, nnFw⟩
    simp only [hq, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · apply G.bridgeless_cface hbr (G.node (G.node y1))
      have h1 : G.cface (G.node y1) (G.node (G.node y1)) :=
        connect_trans (G.cfaceC.1 ny2Fny1) (G.cfaceC.1 nnFw)
      have h2 : G.cface (G.face (G.edge (G.node (G.node y1)))) (G.node (G.node y1)) := by
        rw [G.nodeK]
        exact h1
      exact G.cfaceC.1 ((G.cface1 _ _).2 h2)
    · have rn : next (G.spokeRing x) y1 ∈ G.spokeRing x := mem_next.2 ry1
      have h1 : G.cface (next (G.spokeRing x) y1) y2 := by
        rw [G.next_spoke_ring cexG ry1, spoke, ← G.cubic_eq' cexG.cubic]
        exact connect_trans ((G.cface1 _ _).1 nnFw) ezFy2
      exact ry1''y2 (G.scycle_cface scycRr _ rn _ ry2 h1).symm
    · apply G.bridgeless_cface hbr y1
      rw [G.cubic_eq' cexG.cubic, ← G.cface1] at nnFw
      have h1 := (G.cface1 _ _).1 (G.cfaceC.1 nnFw)
      rw [G.nodeK] at h1
      exact h1

omit [Fintype D] [DecidableEq D] in
/-- math-comp `size_spoke_ring`. -/
theorem size_spoke_ring (x : D) : (G.spokeRing x).length = G.arity x := by
  rw [spokeRing, List.length_map, List.length_reverse, length_orbit]

/-- The coloring of the proof of `min_arity` on the faces of the spoke ring (by position `i` in
a ring of size `n`): math-comp's
`if (i == 2) && (size r == 3) then Color3 else if pred2 0 2 i then Color1 else Color2`. -/
private def minArityColor (n i : ℕ) : Color :=
  if i = 2 ∧ n = 3 then Color3 else if i = 0 ∨ i = 2 then Color1 else Color2

private theorem minArityColor_ne0 (n i : ℕ) : minArityColor n i ≠ Color0 := by
  unfold minArityColor
  split_ifs <;> decide

private theorem minArityColor_adj_fin : ∀ n i1 i2 : Fin 5, 2 ≤ n.val → i1.val < n.val →
    i2.val < n.val → (i2.val = (if i1.val = 0 then n.val - 1 else i1.val - 1) ∨
      i2.val = (if i1.val + 1 = n.val then 0 else i1.val + 1)) →
    minArityColor n.val i1.val ≠ minArityColor n.val i2.val := by
  decide

/-- The final case analysis of `min_arity`: the colors of consecutive faces differ. -/
private theorem minArityColor_adj (n : ℕ) (hn : n < 5) (hn2 : 2 ≤ n) (i1 : ℕ) (hi1 : i1 < n)
    (i2 : ℕ) (hi2 : i2 < n)
    (h : i2 = (if i1 = 0 then n - 1 else i1 - 1) ∨ i2 = (if i1 + 1 = n then 0 else i1 + 1)) :
    minArityColor n i1 ≠ minArityColor n i2 :=
  minArityColor_adj_fin ⟨n, hn⟩ ⟨i1, by omega⟩ ⟨i2, by omega⟩ hn2 hi1 hi2 h

/-- math-comp `min_arity`: the faces of a minimal counter-example have at least five sides. -/
theorem min_arity (cexG : G.MinimalCounterExample) (x : D) : 4 < G.arity x := by
  classical
  have hbr := cexG.bridgeless
  have scycRr := G.scycle_spoke_ring cexG x
  have Ur := G.spoke_ring_uniq x
  by_contra hle
  push Not at hle
  rw [← G.size_spoke_ring] at hle
  by_cases hFC : ∃ y, y ∈ G.diskFC (G.spokeRing x)
  · exact G.birkhoff_lt5 cexG (by omega) scycRr ((G.nontrivial0P _).2
      ⟨⟨x, (G.diskF_spoke_ring cexG x x).2 (connect_refl x)⟩, hFC⟩)
  push Not at hFC
  -- the darts outside the hub face are in the faces of the spoke ring
  have rF : ∀ y, ¬ G.cface x y → y ∈ G.fband (G.spokeRing x) := by
    intro y xF'y
    by_contra rF'y
    apply hFC y
    refine ⟨fun dNy => xF'y ((G.diskF_spoke_ring cexG x y).1 ⟨dNy, rF'y⟩), rF'y⟩
  set r := G.spokeRing x with hr
  set n := r.length with hn
  let idx : D → ℕ := fun y => r.findIdx fun z => decide (G.cface y z)
  let k : D → Color := fun y => if G.cface x y then Color0 else minArityColor n (idx y)
  have idx_lt : ∀ y, y ∈ G.fband r → idx y < n := fun y ⟨z, rz, yFz⟩ =>
    List.findIdx_lt_length_of_exists ⟨z, rz, decide_eq_true yFz⟩
  have idx_F : ∀ y (h : y ∈ G.fband r), G.cface y (r[idx y]'(idx_lt y h)) := fun y h =>
    of_decide_eq_true (List.findIdx_getElem (w := idx_lt y h))
  apply cexG.noncolorable
  refine ⟨k, fun y => ?_, fun y => ?_⟩
  · by_cases xFy : G.cface x y
    · have xF'ey : ¬ G.cface x (G.edge y) := fun h =>
        G.bridgeless_cface hbr y (connect_trans (G.cfaceC.1 xFy) h)
      simp only [k, xFy, xF'ey, ↓reduceIte]
      exact minArityColor_ne0 _ _
    by_cases xFey : G.cface x (G.edge y)
    · simp only [k, xFy, xFey, ↓reduceIte]
      exact (minArityColor_ne0 _ _).symm
    simp only [k, xFy, xFey, ↓reduceIte]
    have rFy := rF y xFy
    have rFey := rF _ xFey
    have hi1 := idx_lt y rFy
    have hi2 := idx_lt _ rFey
    have z1Az2 : G.adj (r[idx y]'hi1) (r[idx (G.edge y)]'hi2) :=
      G.adjP.2 ⟨y, G.cfaceC.1 (idx_F y rFy), idx_F _ rFey⟩
    have hn2 : 2 ≤ n := by
      by_contra hn2
      obtain ⟨z, hz⟩ : ∃ z, r = [z] :=
        List.length_eq_one_iff.1 (by omega)
      rw [hz] at scycRr
      exact G.bridgeless_cface hbr z (G.cfaceC.1 scycRr.1.1)
    have hch := (G.chordless_iff.1 (G.chordless_spoke_ring cexG x)) _ (List.getElem_mem hi1) _
      (List.getElem_mem hi2) z1Az2
    rw [eq_prev_iff Ur hi1 hi2, eq_next_iff Ur hi1 hi2] at hch
    exact (minArityColor_adj n (by omega) hn2 _ hi1 _ hi2 hch).symm
  · have e1 : (fun z => decide (G.cface (G.face y) z)) = fun z => decide (G.cface y z) :=
      funext fun z => decide_eq_decide.2 (G.cface1 y z).symm
    have hF : G.cface x (G.face y) ↔ G.cface x y := (G.cface1r x y).symm
    simp only [k, idx, e1]
    by_cases h : G.cface x y
    · rw [ite_eq_left (hF.2 h), ite_eq_left h]
    · rw [ite_eq_right (mt hF.1 h), ite_eq_right h]

omit [DecidableEq D] in
/-- math-comp `fband_spoke_ring`. -/
theorem fband_spoke_ring (x y : D) : y ∈ G.fband (G.spokeRing x) ↔ G.adj x y := by
  constructor
  · rintro ⟨z, rz, yFz⟩
    refine G.adjP.2 ⟨G.node z, G.mem_spoke_ring.1 rz, ?_⟩
    show G.cface (G.edge (G.node z)) y
    have h : G.cface (G.edge (G.node z)) z := by
      have := fconnect1 G.face (G.edge (G.node z))
      rwa [G.nodeK] at this
    exact connect_trans h (G.cfaceC.1 yFz)
  · intro xAy
    obtain ⟨z, xFz, zRy⟩ := G.adjP.1 xAy
    refine ⟨G.face (G.edge z), ?_, ?_⟩
    · rw [G.mem_spoke_ring, G.edgeK]
      exact xFz
    · exact (G.cface1r _ _).1 (G.cfaceC.1 zRy)

/-- math-comp `adj11_edge`. -/
theorem adj11_edge (cexG : G.MinimalCounterExample) {x y : D} (xAy : G.adj x y)
    (xAey : G.adj x (G.edge y)) : y ∈ G.spokeRing x ∨ G.edge y ∈ G.spokeRing x := by
  have hpl := cexG.plain
  have Ur := G.spoke_ring_uniq x
  obtain ⟨z, rz, yFz⟩ := (G.fband_spoke_ring x y).2 xAy
  obtain ⟨t, rt, eyFt⟩ := (G.fband_spoke_ring x _).2 xAey
  by_contra h
  push Not at h
  obtain ⟨r'y, r'ey⟩ := h
  have zAt : G.adj z t := (G.adjFr eyFt z).1 ((G.adjF yFz _).1 (G.adjE y))
  rcases (G.chordless_iff.1 (G.chordless_spoke_ring cexG x)) z rz t rt zAt with Dt | Dt
  · -- `z = next t`
    have Dz : z = G.face (G.face (G.edge t)) := by
      rw [← spoke, ← G.next_spoke_ring cexG rt, Dt, next_prev Ur]
    rw [Dz, ← G.cface1r, ← G.cface1r] at yFz
    have h2 : G.cface (G.edge (G.edge y)) (G.edge t) := by rw [G.plain_eq hpl]; exact yFz
    exact r'ey ((G.double_dart cexG eyFt h2) ▸ rt)
  · rw [Dt, G.next_spoke_ring cexG rz, spoke, ← G.cface1r, ← G.cface1r] at eyFt
    exact r'y ((G.double_dart cexG yFz eyFt) ▸ rz)

/-- math-comp `fcard_adj_adj`. -/
theorem fcard_adj_adj (cexG : G.MinimalCounterExample) {x y : D} (xAy : G.adj x y) :
    fcard G.face {z | G.adj y z ∧ G.adj x z} = 2 := by
  have hpl := cexG.plain
  have scycRr := G.scycle_spoke_ring cexG x
  have Ur := G.spoke_ring_uniq x
  obtain ⟨y1, ry1, yFy1⟩ := (G.fband_spoke_ring x y).2 xAy
  have r_xA : ∀ z ∈ G.spokeRing x, G.adj x z := fun z rz =>
    (G.adjF (G.mem_spoke_ring.1 rz) z).2 (G.adjN z)
  set z1 := prev (G.spokeRing x) y1 with hz1
  set z2 := next (G.spokeRing x) y1 with hz2
  have rz1 : z1 ∈ G.spokeRing x := (mem_prev Ur).2 ry1
  have rz2 : z2 ∈ G.spokeRing x := mem_next.2 ry1
  have yAz1 : G.adj y z1 :=
    (G.adjF yFy1 _).2 ((G.adjC hpl _ _).1 (G.rlink_adj (prev_cycle scycRr.1 ry1)))
  have yAz2 : G.adj y z2 := (G.adjF yFy1 _).2 (G.rlink_adj (next_cycle scycRr.1 ry1))
  -- `z1` and `z2` are in different faces, since the ring has more than two darts
  have z1F'z2 : ¬ G.cface z1 z2 := by
    intro h
    have e := G.scycle_cface scycRr _ rz1 _ rz2 h
    have hn := G.min_arity cexG x
    rw [← G.size_spoke_ring] at hn
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ry1
    rw [hz1, hz2, prev_getElem' Ur hi, next_getElem' Ur hi, Ur.getElem_inj_iff,
      pred_mod_eq hi, succ_mod_eq hi] at e
    split_ifs at e <;> omega
  -- every face adjacent to `x` and `y` is the face of `z1` or of `z2`
  have hS : ∀ t, G.adj y t → G.adj x t → G.cface t z1 ∨ G.cface t z2 := by
    intro t yAt xAt
    obtain ⟨t1, rt1, tFt1⟩ := (G.fband_spoke_ring x t).2 xAt
    have y1At1 : G.adj y1 t1 := (G.adjFr tFt1 _).1 ((G.adjF yFy1 _).1 yAt)
    rcases (G.chordless_iff.1 (G.chordless_spoke_ring cexG x)) y1 ry1 t1 rt1 y1At1 with h | h
    · rw [h] at tFt1
      exact Or.inl tFt1
    · rw [h] at tFt1
      exact Or.inr tFt1
  have hs := G.cface_sym
  show (comp (frel G.face) '' {z | G.adj y z ∧ G.adj x z}).ncard = 2
  have himg : comp (frel G.face) '' {z | G.adj y z ∧ G.adj x z} =
      {comp (frel G.face) z1, comp (frel G.face) z2} := by
    ext c
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨t, ⟨yAt, xAt⟩, rfl⟩
      rcases hS t yAt xAt with h | h
      · exact Or.inl ((comp_eq_iff hs).2 h)
      · exact Or.inr ((comp_eq_iff hs).2 h)
    · rintro (rfl | rfl)
      · exact ⟨z1, ⟨yAz1, r_xA z1 rz1⟩, rfl⟩
      · exact ⟨z2, ⟨yAz2, r_xA z2 rz2⟩, rfl⟩
  rw [himg, Set.ncard_pair]
  exact fun h => z1F'z2 ((comp_eq_iff hs).1 h)

/-- math-comp `adj01 y z`: `y` and `z` belong to the same face or to adjacent faces. -/
def Adj01 (y z : D) : Prop := G.cface y z ∨ G.adj y z

/-- math-comp `adj12_edge`. -/
theorem adj12_edge (cexG : G.MinimalCounterExample) {x y z : D} (xAy : G.adj x y)
    (xAz : G.adj x z) (zAey : G.adj z (G.edge y)) : G.Adj01 z y ∨ G.Adj01 x (G.edge y) := by
  have hbr := cexG.bridgeless
  have hpl := cexG.plain
  have hG := cexG.toPlanarBridgelessPlainConnected
  obtain ⟨y1, ry1, yFy1⟩ := (G.fband_spoke_ring x y).2 xAy
  obtain ⟨z1, rz1, zFz1⟩ := (G.fband_spoke_ring x z).2 xAz
  obtain ⟨x1, zFx1, ex1Fey⟩ := G.adjP.1 zAey
  have eyFex1 : G.cface (G.edge y) (G.edge x1) := G.cfaceC.1 ex1Fey
  by_contra h
  simp only [Adj01] at h
  push Not at h
  obtain ⟨⟨zF'y, zA'y⟩, ⟨xF'ey, xA'ey⟩⟩ := h
  have z1F'y : ¬ G.cface z1 y := fun h => zF'y (connect_trans zFz1 h)
  have z1Fx1 : G.cface z1 x1 := connect_trans (G.cfaceC.1 zFz1) zFx1
  have z1A'y : ¬ G.adj z1 y := fun h => zA'y ((G.adjF zFz1 y).2 h)
  have xFny1 := G.mem_spoke_ring.1 ry1
  have xFnz1 := G.mem_spoke_ring.1 rz1
  -- `edge (node w)` is in the face of `w`
  have enF : ∀ w, G.cface (G.edge (G.node w)) w := fun w => by
    have := fconnect1 G.face (G.edge (G.node w))
    rwa [G.nodeK] at this
  set q := [y, G.edge x1, G.edge (G.node z1), G.node y1] with hq
  have scycRq : G.SCycle G.rlink q := by
    rw [G.srcycleI hbr]
    refine ⟨eyFex1, ?_, ?_, ?_, ?_, by simp, ?_⟩
    · intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · intro h
        exact z1F'y (G.cfaceC.1 (connect_trans h (enF z1)))
      · intro h
        exact G.adj_no_cface hbr (G.adjN y1) (G.cfaceC.1 (connect_trans (G.cfaceC.1 yFy1) h))
    · show G.cface (G.edge (G.edge x1)) (G.edge (G.node z1))
      rw [G.plain_eq hpl]
      exact connect_trans (G.cfaceC.1 z1Fx1) (G.cfaceC.1 (enF z1))
    · intro w hw h
      simp only [List.mem_singleton] at hw
      subst hw
      exact xF'ey (connect_trans xFny1 (G.cfaceC.1 (connect_trans eyFex1 h)))
    · show G.cface (G.edge (G.edge (G.node z1))) (G.node y1)
      rw [G.plain_eq hpl]
      exact connect_trans (G.cfaceC.1 xFnz1) xFny1
    · show G.cface (G.edge (G.node y1)) y
      exact connect_trans (enF y1) (G.cfaceC.1 yFy1)
  apply G.birkhoff_lt5 cexG (by simp [hq]) scycRq
  rw [G.nontrivial0P]
  refine ⟨⟨G.node (G.node y1), ((G.diskN_node q) _ _ rfl).1
    (G.mem_diskN_of_mem q (by simp [hq])), ?_⟩, ⟨G.node (G.node z1), ?_, ?_⟩⟩
  · rintro ⟨w, hw, hw'⟩
    simp only [hq, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · apply G.bridgeless_cface hbr y1
      have h : G.cface y1 (G.node (G.node y1)) := connect_trans (G.cfaceC.1 yFy1) (G.cfaceC.1 hw')
      rw [G.cubic_eq' cexG.cubic, ← G.cface1r] at h
      exact h
    · have xAnn : G.adj x (G.node (G.node y1)) :=
        (G.adjF xFny1 _).2 ((G.adjC hpl _ _).1 (G.adjN (G.node y1)))
      exact G.no_adj_adj xA'ey xAnn (G.cfaceC.1 (connect_trans hw' (G.cfaceC.1 eyFex1)))
    · have yAnn : G.adj y (G.node (G.node y1)) := by
        rw [G.adjF yFy1, G.cubic_eq' cexG.cubic, ← G.adjF1r]
        exact G.adjE y1
      have yA'z1 : ¬ G.adj y z1 := fun h => z1A'y ((G.adjC hpl _ _).1 h)
      exact G.no_adj_adj yA'z1 yAnn (connect_trans (G.cfaceC.1 (enF z1)) (G.cfaceC.1 hw'))
    · exact G.adj_no_cface hbr (G.adjN (G.node y1)) hw'
  · intro h
    have h' : G.node z1 ∈ G.diskN q := ((G.diskN_node q) _ _ rfl).2 h
    rw [← G.plain_eq hpl (G.node z1)] at h'
    exact G.diskN_edge_ring hG scycRq (G.size_proper_ring (by simp [hq])) (by simp [hq]) h'
  · rintro ⟨w, hw, hw'⟩
    simp only [hq, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · rw [G.cubic_eq' cexG.cubic, ← G.cface1] at hw'
      exact G.no_adj_adj z1A'y (G.adjE z1) (G.cfaceC.1 hw')
    · have xAnn : G.adj x (G.node (G.node z1)) :=
        (G.adjF xFnz1 _).2 ((G.adjC hpl _ _).1 (G.adjN (G.node z1)))
      exact G.no_adj_adj xA'ey xAnn (G.cfaceC.1 (connect_trans hw' (G.cfaceC.1 eyFex1)))
    · apply G.bridgeless_cface hbr z1
      have h : G.cface z1 (G.node (G.node z1)) := connect_trans (G.cfaceC.1 (enF z1))
        (G.cfaceC.1 hw')
      rw [G.cubic_eq' cexG.cubic, ← G.cface1r] at h
      exact h
    · apply G.bridgeless_cface hbr (G.node (G.node z1))
      have h1 : G.cface (G.node z1) (G.node (G.node z1)) :=
        connect_trans (G.cfaceC.1 xFnz1) (connect_trans xFny1 (G.cfaceC.1 hw'))
      exact G.cfaceC.1 (connect_trans (enF (G.node z1)) h1)

/-- math-comp `fcard_adj_max`. -/
theorem fcard_adj_max (cexG : G.MinimalCounterExample) {x y : D} (xF'y : ¬ G.cface x y) :
    fcard G.face {z | G.adj y z ∧ G.adj x z} ≤ 2 := by
  have hpl := cexG.plain
  have hbr := cexG.bridgeless
  have Ur := G.spoke_ring_uniq x
  by_cases xAy : G.adj x y
  · exact (G.fcard_adj_adj cexG xAy).le
  by_contra hgt
  push Not at hgt
  have hs := G.cface_sym
  obtain ⟨c1, c2, c3, ⟨z1, ⟨yAz1, xAz1⟩, rfl⟩, ⟨z2, ⟨yAz2, xAz2⟩, rfl⟩,
    ⟨z3, ⟨yAz3, xAz3⟩, rfl⟩, h12, h13, h23⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 hgt
  have z1F'z2 : ¬ G.cface z1 z2 := fun h => h12 ((comp_eq_iff hs).2 h)
  have z1F'z3 : ¬ G.cface z1 z3 := fun h => h13 ((comp_eq_iff hs).2 h)
  have z2F'z3 : ¬ G.cface z2 z3 := fun h => h23 ((comp_eq_iff hs).2 h)
  -- two faces adjacent to both `x` and `y` are adjacent
  have cross_adj : ∀ z t, ¬ G.cface z t → G.adj x z → G.adj x t → G.adj y z → G.adj y t →
      G.adj z t := by
    intro z t zF't xAz xAt yAz yAt
    obtain ⟨u, yFu, uRt⟩ := G.adjP.1 yAt
    have uRt : G.cface (G.edge u) t := uRt
    have xAeu : G.adj x (G.edge u) := (G.adjFr uRt x).2 xAt
    have zAeeu : G.adj z (G.edge (G.edge u)) := by
      rw [G.plain_eq hpl, G.adjC hpl]
      exact (G.adjF yFu z).1 yAz
    rcases G.adj12_edge cexG xAeu xAz zAeeu with h | h
    · rcases h with h | h
      · exact absurd (connect_trans h uRt) zF't
      · exact (G.adjFr uRt z).1 h
    · rw [Adj01, G.plain_eq hpl] at h
      rcases h with h | h
      · exact absurd (connect_trans h (G.cfaceC.1 yFu)) xF'y
      · exact absurd ((G.adjFr yFu x).2 h) xAy
  have z1Az2 := cross_adj z1 z2 z1F'z2 xAz1 xAz2 yAz1 yAz2
  have z1Az3 := cross_adj z1 z3 z1F'z3 xAz1 xAz3 yAz1 yAz3
  have z2Az3 := cross_adj z2 z3 z2F'z3 xAz2 xAz3 yAz2 yAz3
  -- the faces of `z1`, `z2`, `z3` on the spoke ring
  obtain ⟨t1, rt1, zFt1⟩ := (G.fband_spoke_ring x z1).2 xAz1
  obtain ⟨t2, rt2, zFt2⟩ := (G.fband_spoke_ring x z2).2 xAz2
  obtain ⟨t3, rt3, zFt3⟩ := (G.fband_spoke_ring x z3).2 xAz3
  have tA : ∀ {z t z' t'}, G.cface z t → G.cface z' t' → G.adj z z' → G.adj t t' :=
    fun h h' hA => (G.adjFr h' _).1 ((G.adjF h _).1 hA)
  have tF : ∀ {z t z' t'}, G.cface z t → G.cface z' t' → ¬ G.cface z z' → t ≠ t' :=
    fun h h' hF e => hF (connect_trans h (e ▸ G.cfaceC.1 h'))
  have hch := G.chordless_iff.1 (G.chordless_spoke_ring cexG x)
  have hn := G.min_arity cexG x
  rw [← G.size_spoke_ring] at hn
  obtain ⟨i1, hi1, rfl⟩ := List.getElem_of_mem rt1
  obtain ⟨i2, hi2, rfl⟩ := List.getElem_of_mem rt2
  obtain ⟨i3, hi3, rfl⟩ := List.getElem_of_mem rt3
  have d12 := tF zFt1 zFt2 z1F'z2
  have d13 := tF zFt1 zFt3 z1F'z3
  have d23 := tF zFt2 zFt3 z2F'z3
  rw [Ne, Ur.getElem_inj_iff] at d12 d13 d23
  have c12 := hch _ (List.getElem_mem hi1) _ (List.getElem_mem hi2) (tA zFt1 zFt2 z1Az2)
  have c13 := hch _ (List.getElem_mem hi1) _ (List.getElem_mem hi3) (tA zFt1 zFt3 z1Az3)
  have c23 := hch _ (List.getElem_mem hi2) _ (List.getElem_mem hi3) (tA zFt2 zFt3 z2Az3)
  rw [eq_prev_iff Ur hi1 hi2, eq_next_iff Ur hi1 hi2] at c12
  rw [eq_prev_iff Ur hi1 hi3, eq_next_iff Ur hi1 hi3] at c13
  rw [eq_prev_iff Ur hi2 hi3, eq_next_iff Ur hi2 hi3] at c23
  split_ifs at c12 c13 c23 <;> omega

end Birkhoff

/-- math-comp `minimal_counter_example_is_plain_cubic_pentagonal`: a minimal counter-example is
plain, cubic and pentagonal. -/
theorem minimal_counter_example_is_plain_cubic_pentagonal {D : Type u} [Fintype D]
    [DecidableEq D] {G : Hypermap D} (cexG : G.MinimalCounterExample) : G.PlainCubicPentagonal :=
  ⟨⟨cexG.plain, cexG.cubic⟩, G.min_arity cexG⟩

/-- math-comp coercion `minimal_counter_example_is_plain_cubic_pentagonal`, for dot
notation. -/
theorem MinimalCounterExample.toPlainCubicPentagonal {D : Type u} [Fintype D] [DecidableEq D]
    {G : Hypermap D} (cexG : G.MinimalCounterExample) : G.PlainCubicPentagonal :=
  minimal_counter_example_is_plain_cubic_pentagonal cexG

end Hypermap

end FourColor
