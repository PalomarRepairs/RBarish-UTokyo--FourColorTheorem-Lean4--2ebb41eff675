/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Geometry
import FourColor.CfMap.Prog

/-!
# Pointed maps and their rings (port of `cfmap.v`, section `CpRing`)

* `PointedMap`       : a hypermap bundled with its (finite, decidable) dart type and a
  reference dart (math-comp `pointed_map`, with coercions `pointee` and `pointer`).
* `G.cpring x`       : the ring (reverse N-cycle) of the remainder hypermap of a configuration,
  given a reference point `x` on that ring; unless it is trivial, `G.cpring x` starts with
  `G.node x :: x :: ...` (math-comp `cpring`).
* `G.ProperCpring x` : `x ≠ G.node x`, so `G.cpring x` is nontrivial (of size > 1)
  (math-comp `proper_cpring`).
* `G.LongCpring x`   : `G.face (G.edge x) ≠ G.node x`, so `G.cpring x` has size > 2
  (math-comp `long_cpring`).

We also prove a few general facts about trajectories and orbits (math-comp `fpathP`,
`cycle_orbit`, ...), in the namespace `FourColor.CfMap`.
-/

namespace FourColor

open Function CfMap

universe u

/-- math-comp `pointed_map`: a hypermap (math-comp `pointee`) on a finite dart type with
decidable equality, together with a reference dart (math-comp `pointer`). -/
structure PointedMap : Type (u + 1) where
  /-- The dart type (math-comp's dart `finType` of the `pointee`). -/
  D : Type u
  /-- The dart type is finite. -/
  [fintype : Fintype D]
  /-- The dart type has decidable equality. -/
  [decEq : DecidableEq D]
  /-- math-comp `pointee`: the hypermap. -/
  pointee : Hypermap D
  /-- math-comp `pointer`: the reference dart. -/
  pointer : D

attribute [instance] PointedMap.fintype PointedMap.decEq

/-! ### Trajectories and orbits -/

namespace CfMap

variable {α : Type*} {f : α → α}

/-- The trajectory `[f x, f (f x), ...]` is an `f`-path from `x`. -/
theorem fpath_iterate (f : α → α) (x : α) (n : ℕ) : fpath f x (List.iterate f (f x) n) := by
  induction n generalizing x with
  | zero => trivial
  | succ n ih => exact ⟨rfl, ih (f x)⟩

/-- math-comp `last_traject`. -/
theorem last_iterate (f : α → α) (x : α) (n : ℕ) : last x (List.iterate f (f x) n) = f^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [List.iterate, last_cons, ih, iterate_succ_apply]

/-- math-comp `fpathP`: an `f`-path from `x` is the trajectory of `f x`. -/
theorem fpath_iff_iterate {x : α} {p : List α} :
    fpath f x p ↔ p = List.iterate f (f x) p.length := by
  induction p generalizing x with
  | nil => simp
  | cons y p ih =>
    simp only [path_cons, List.length_cons, List.iterate, List.cons.injEq]
    constructor
    · rintro ⟨h, hp⟩
      subst h
      exact ⟨rfl, ih.1 hp⟩
    · rintro ⟨rfl, hp⟩
      exact ⟨rfl, ih.2 hp⟩

/-- A trajectory of length `m + 1`, reversed. -/
theorem reverse_iterate_succ (f : α → α) (a : α) (m : ℕ) :
    (List.iterate f a (m + 1)).reverse = f^[m] a :: (List.iterate f a m).reverse := by
  rw [List.iterate_add, List.reverse_append]
  rfl

/-- math-comp `cycle_orbit`. -/
theorem cycle_orbit [Finite α] (hf : Injective f) (x : α) : fcycle f (orbit f x) := by
  obtain ⟨n, hn⟩ : ∃ n, order f x = n + 1 := Nat.exists_eq_succ_of_ne_zero (order_pos hf x).ne'
  have hx : f^[n + 1] x = x := hn ▸ iter_order hf x
  rw [orbit, hn, List.iterate]
  show path (frel f) x (List.iterate f (f x) n ++ [x])
  rw [path_concat, last_iterate]
  refine ⟨fpath_iterate f x n, ?_⟩
  show f (f^[n] x) = x
  rw [← iterate_succ_apply' f n x]
  exact hx

/-- An injection on a finite type has order `1` at `x` iff `x` is a fixpoint. -/
theorem order_eq_one_iff [Finite α] (hf : Injective f) {x : α} : order f x = 1 ↔ f x = x := by
  rw [order_eq_minimalPeriod hf, minimalPeriod_eq_one_iff_isFixedPt]
  rfl

/-- An injection on a finite type has order at most `2` at `x` iff `f (f x) = x`. -/
theorem order_le_two_iff [Finite α] (hf : Injective f) {x : α} : order f x ≤ 2 ↔ f (f x) = x := by
  have hpos := order_pos hf x
  rw [order_eq_minimalPeriod hf] at hpos ⊢
  have key : f (f x) = x ↔ IsPeriodicPt f 2 x := Iff.rfl
  rw [key, isPeriodicPt_iff_minimalPeriod_dvd]
  constructor
  · intro h
    rcases (by omega : minimalPeriod f x = 1 ∨ minimalPeriod f x = 2) with h' | h' <;> rw [h']
    exact one_dvd 2
  · intro h
    exact Nat.le_of_dvd (by norm_num) h

end CfMap

namespace Hypermap

variable {D : Type u} (G : Hypermap D)

/-! ### The ring of a pointed map (math-comp section `CpRing`) -/

section CpRing

/-- math-comp `cpring x0`: the ring (reverse N-cycle) of the remainder hypermap of a
configuration, given a reference point `x0` on that ring. -/
noncomputable def cpring (x0 : D) : List D := (orbit G.node (G.node (G.node x0))).reverse

/-- math-comp `proper_cpring x0`: `x0 ≠ node x0`, so `cpring x0` has size > 1. -/
def ProperCpring (x0 : D) : Prop := x0 ≠ G.node x0

/-- math-comp `long_cpring x0`: `face (edge x0) ≠ node x0`, so `cpring x0` has size > 2. -/
def LongCpring (x0 : D) : Prop := G.face (G.edge x0) ≠ G.node x0

/-- `ProperCpring` is decidable (math-comp's `proper_cpring` is boolean). -/
instance [DecidableEq D] (x0 : D) : Decidable (G.ProperCpring x0) :=
  inferInstanceAs (Decidable (_ ≠ _))

/-- `LongCpring` is decidable (math-comp's `long_cpring` is boolean). -/
instance [DecidableEq D] (x0 : D) : Decidable (G.LongCpring x0) :=
  inferInstanceAs (Decidable (_ ≠ _))

variable [Finite D] (x0 : D)

/-- math-comp `cpring_uniq`. -/
theorem cpring_uniq : (G.cpring x0).Nodup := List.nodup_reverse.2 (orbit_uniq G.nodeI _)

/-- math-comp `mem_cpring`. -/
theorem mem_cpring {x : D} : x ∈ G.cpring x0 ↔ G.cnode x0 x := by
  rw [cpring, List.mem_reverse, ← fconnect_orbit G.nodeI]
  exact ((G.cnode1 x0 x).trans (G.cnode1 _ x)).symm

/-- The node orbit of `node (node x0)` is that of `x0`. -/
theorem order_node_node_node : order G.node (G.node (G.node x0)) = order G.node x0 :=
  order_congr fun z => ((G.cnode1 x0 z).trans (G.cnode1 _ z)).symm

/-- math-comp `size_cpring`. -/
theorem size_cpring : (G.cpring x0).length = order G.node x0 := by
  rw [cpring, List.length_reverse, length_orbit, order_node_node_node]

/-- The ring as a reversed trajectory. -/
theorem cpring_eq_iterate :
    G.cpring x0 = (List.iterate G.node (G.node (G.node x0)) (order G.node x0)).reverse := by
  rw [cpring, orbit, order_node_node_node]

/-- `node^[order node x0] x0 = x0`. -/
theorem iter_order_node : G.node^[order G.node x0] x0 = x0 := iter_order G.nodeI x0

/-- math-comp `size_proper_cpring`. -/
theorem size_proper_cpring : G.ProperCpring x0 ↔ 1 < (G.cpring x0).length := by
  rw [size_cpring, ProperCpring]
  have hpos := order_pos G.nodeI x0
  have h1 := order_eq_one_iff G.nodeI (x := x0)
  constructor
  · intro h
    by_contra hle
    exact h (h1.1 (by omega)).symm
  · intro h hx
    have := h1.2 hx.symm
    omega

/-- math-comp `size_long_cpring`. -/
theorem size_long_cpring : G.LongCpring x0 ↔ 2 < (G.cpring x0).length := by
  rw [size_cpring, LongCpring, Ne, ← G.eq_node_iff, not_iff_comm, not_lt,
    order_le_two_iff G.nodeI, eq_comm]

/-- math-comp `cycle_rev_cpring`. -/
theorem cycle_rev_cpring : fcycle G.node (G.cpring x0).reverse := by
  rw [cpring, List.reverse_reverse]
  exact cycle_orbit G.nodeI _

/-- math-comp `ucycle_rev_cpring`. -/
theorem ucycle_rev_cpring : UCycle (frel G.node) (G.cpring x0).reverse :=
  ⟨G.cycle_rev_cpring x0, List.nodup_reverse.2 (G.cpring_uniq x0)⟩

omit [Finite D] in
/-- math-comp `cpring_def`: `cpring x0` is the only duplicate-free reverse N-cycle that starts
with `node x0` (math-comp states the head condition as `if p is x :: _ then x = node x0 else
False`). -/
theorem cpring_def {p : List D} (hp : p.head? = some (G.node x0))
    (hu : UCycle (frel G.node) p.reverse) : G.cpring x0 = p := by
  obtain ⟨hcyc, hnd⟩ := hu
  cases p with
  | nil => simp at hp
  | cons y p' =>
    simp only [List.head?_cons, Option.some.injEq] at hp
    subst hp
    have hnx0 : G.node x0 ∈ (G.node x0 :: p').reverse := by simp
    have hnnx0 : G.node (G.node x0) ∈ (G.node x0 :: p').reverse :=
      (fconnect_cycle hcyc hnx0).1 (fconnect1 _ _)
    have hord := order_cycle hcyc hnd hnnx0
    have hpath := (cycle_iff_path x0 _).1 hcyc
    rw [List.reverse_cons, last_concat, ← List.reverse_cons] at hpath
    have := fpath_iff_iterate.1 hpath
    rw [cpring, orbit, hord, ← this, List.reverse_reverse]

omit [Finite D] in
/-- Iterating `node` from `node (node x0)`. -/
theorem iter_node_node_node (k : ℕ) : G.node^[k] (G.node (G.node x0)) = G.node^[k + 2] x0 :=
  (iterate_add_apply G.node k 2 x0).symm

/-- The items of the ring: the `i`-th item of `cpring x0` is `node^[order node x0 - i + 1] x0`
(so `cpring x0 = [node x0, x0, face (edge x0), ...]`). -/
theorem getElem?_cpring {i : ℕ} (hi : i < order G.node x0) :
    (G.cpring x0)[i]? = some (G.node^[order G.node x0 - i + 1] x0) := by
  rw [cpring_eq_iterate, List.getElem?_reverse (by simpa using hi), List.length_iterate,
    List.getElem?_iterate _ _ _ _ (by omega), iter_node_node_node]
  congr 2
  omega

/-- math-comp `head_cpring`. -/
theorem head_cpring : G.cpring x0 = G.node x0 :: (G.cpring x0).tail := by
  obtain ⟨m, hm⟩ : ∃ m, order G.node x0 = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (order_pos G.nodeI x0).ne'
  have hx := G.iter_order_node x0
  rw [hm] at hx
  have e1 : G.node^[m] (G.node (G.node x0)) = G.node x0 := by
    rw [iter_node_node_node, show m + 2 = (m + 1) + 1 from rfl, iterate_succ_apply', hx]
  rw [cpring_eq_iterate, hm, reverse_iterate_succ, e1, List.tail_cons]

/-- math-comp `head_long_cpring`. -/
theorem head_long_cpring (h : G.LongCpring x0) :
    G.cpring x0 = G.node x0 :: x0 :: G.face (G.edge x0) :: (G.cpring x0).drop 3 := by
  have h3 := (G.size_long_cpring x0).1 h
  rw [size_cpring] at h3
  obtain ⟨m, hm⟩ : ∃ m, order G.node x0 = m + 2 + 1 := ⟨order G.node x0 - 3, by omega⟩
  have hx := G.iter_order_node x0
  rw [hm] at hx
  have e1 : G.node^[m + 2] (G.node (G.node x0)) = G.node x0 := by
    rw [iter_node_node_node, show m + 2 + 2 = (m + 2 + 1) + 1 from rfl, iterate_succ_apply', hx]
  have e2 : G.node^[m + 1] (G.node (G.node x0)) = x0 := by
    rw [iter_node_node_node, show m + 1 + 2 = m + 2 + 1 from rfl, hx]
  have e3 : G.node^[m] (G.node (G.node x0)) = G.face (G.edge x0) := by
    rw [iter_node_node_node]
    exact ((G.eq_node_iff).1 (by rw [← iterate_succ_apply' G.node (m + 2), hx])).symm
  rw [cpring_eq_iterate, hm, reverse_iterate_succ, reverse_iterate_succ, reverse_iterate_succ,
    e1, e2, e3]
  simp

/-- math-comp `head_proper_cpring`. -/
theorem head_proper_cpring (h : G.ProperCpring x0) :
    G.cpring x0 = G.node x0 :: x0 :: (G.cpring x0).drop 2 := by
  have h2 := (G.size_proper_cpring x0).1 h
  rw [size_cpring] at h2
  obtain ⟨m, hm⟩ : ∃ m, order G.node x0 = m + 1 + 1 := ⟨order G.node x0 - 2, by omega⟩
  have hx := G.iter_order_node x0
  rw [hm] at hx
  have e1 : G.node^[m + 1] (G.node (G.node x0)) = G.node x0 := by
    rw [iter_node_node_node, show m + 1 + 2 = (m + 1 + 1) + 1 from rfl, iterate_succ_apply', hx]
  have e2 : G.node^[m] (G.node (G.node x0)) = x0 := by
    rw [iter_node_node_node, show m + 2 = m + 1 + 1 from rfl, hx]
  rw [cpring_eq_iterate, hm, reverse_iterate_succ, reverse_iterate_succ, e1, e2]
  simp

end CpRing

end Hypermap

end FourColor
