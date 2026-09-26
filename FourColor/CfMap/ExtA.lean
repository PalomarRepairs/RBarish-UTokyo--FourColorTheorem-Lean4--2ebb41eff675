/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfMap.Ring

/-!
# Ring rotations and neighbor merging (port of `cfmap.v`, section `ExtConfig`, part 1)

Given a reference dart `x0` in a hypermap `G`:

* `G.ecpR n0 x0` : the pointed map with reference dart `node^-n0 x0`, which implements an
  `R n0` step at dart `x0` (math-comp `ecpR`); the rotation is the identity when `n0` exceeds
  the ring size.
* `G.ecpA x0`    : a pointed map that implements an `A` step at `x0` (math-comp `ecpA`): it
  merges the two ring neighbors of the face of `x0`.
* `G.icpR n0 x0`, `G.icpA x0` : the (identity) injections of `G` into these maps.

math-comp's `fun_base h f f' b` ("`f (h x)` and `h (f' x)` agree outside `b`") is stated
explicitly.  Merging neighbors trivially produces a plain graph, but otherwise it has very few
properties; fortunately, we only need the preservation of face connectivity, since we only use
the merge to build contract coloring maps. To make sure this property is always true, we must
check whether the neighbors are already merged, in which case we need to create a hyperedge to
avoid the creation of a separate component. The merge operation breaks both the `cface` and
`edge` relation, but in the right direction for `cface` (the resulting map is more connected
than the base one) and it preserves the `adj` relation, which is enough for coloring.
-/

namespace FourColor

open Function CfMap

universe u

namespace CfMap

variable {α : Type*}

/-- Two relations that agree on the items of `belast x p` have the same paths from `x` along
`p` (math-comp `eq_path_in`/`map_path` for the identity injection). -/
theorem path_congr_belast {e e' : α → α → Prop} {x : α} {p : List α}
    (h : ∀ z ∈ belast x p, ∀ w, e z w ↔ e' z w) : path e x p ↔ path e' x p := by
  induction p generalizing x with
  | nil => simp
  | cons y p ih =>
    simp only [belast_cons, List.mem_cons, forall_eq_or_imp] at h
    simp only [path_cons, h.1 y, ih h.2]

/-- Two relations that agree on the items of `L.dropLast`, and link the start points `a` and
`b` to the same items, have the same paths along `L`. -/
theorem path_congr_dropLast {e e' : α → α → Prop} {a b : α} {L : List α}
    (h0 : ∀ w, e a w ↔ e' b w) (h : ∀ z ∈ L.dropLast, ∀ w, e z w ↔ e' z w) :
    path e a L ↔ path e' b L := by
  induction L generalizing a b with
  | nil => simp
  | cons y L ih =>
    cases L with
    | nil => simp [h0 y]
    | cons y' L =>
      simp only [List.dropLast_cons_cons, List.mem_cons, forall_eq_or_imp] at h
      simp only [path_cons] at ih ⊢
      rw [h0 y, ← ih (h.1) h.2]

/-- In a duplicate-free `x :: p`, the last item does not occur in `belast x p`. -/
theorem last_not_mem_belast {x : α} {p : List α} (hu : (x :: p).Nodup) :
    last x p ∉ belast x p := by
  rw [lastI x p, List.nodup_append] at hu
  intro h
  exact hu.2.2 _ h _ (List.mem_singleton_self _) rfl

end CfMap

namespace Hypermap

variable {D : Type u} [Fintype D] [DecidableEq D] (G : Hypermap D)

/-! ### Reverse ring rotation -/

section EcpR

variable (n0 : ℕ) (x0 : D)

/-- math-comp `ecpR n0 x0`: the pointed map `G` with reference dart `node^-n0 x0`
(`iter (order node x0 - n0) node x0`). Note that the map construction matches the ring rotation
for arbitrary `n0` (it is the identity if `n0 ≥ order node x0`). -/
noncomputable abbrev ecpR : PointedMap := ⟨D, G, G.node^[order G.node x0 - n0] x0⟩

/-- math-comp `icpR`: the (identity) injection of `G` into `ecpR n0 x0`. -/
abbrev icpR (x : D) : (G.ecpR n0 x0).D := x

/-- math-comp `cpring_ecpR`. -/
theorem cpring_ecpR :
    (G.ecpR n0 x0).pointee.cpring (G.ecpR n0 x0).pointer = rot n0 (G.cpring x0) := by
  show G.cpring (G.node^[order G.node x0 - n0] x0) = rot n0 (G.cpring x0)
  have hlen := G.size_cpring x0
  rcases Nat.lt_or_ge n0 (order G.node x0) with h | h
  · apply G.cpring_def
    · rw [head?_rot (by omega), G.getElem?_cpring x0 h, ← iterate_succ_apply' G.node]
    · rw [reverse_rot]
      obtain ⟨hc, hu⟩ := G.ucycle_rev_cpring x0
      exact ⟨(cycle_rotr _ _).2 hc, nodup_rot.2 hu⟩
  · rw [show order G.node x0 - n0 = 0 by omega, iterate_zero_apply,
      rot_oversize (by rw [hlen]; exact h)]

/-- math-comp `size_cpring_ecpR`. -/
theorem size_cpring_ecpR :
    ((G.ecpR n0 x0).pointee.cpring (G.ecpR n0 x0).pointer).length = (G.cpring x0).length := by
  rw [cpring_ecpR, length_rot]

/-- math-comp `cubic_ecpR`. -/
theorem cubic_ecpR (cubicG : G.Quasicubic (G.cpring x0).reverse) :
    (G.ecpR n0 x0).pointee.Quasicubic
      ((G.ecpR n0 x0).pointee.cpring (G.ecpR n0 x0).pointer).reverse := by
  rw [cpring_ecpR]
  intro x hx
  apply cubicG
  simp only [Set.mem_ofPred_eq, List.mem_reverse, mem_rot] at hx ⊢
  exact hx

end EcpR

/-! ### Merging neighbors -/

section EcpA

variable (x0 : D)

open Classical in
/-- math-comp `ecpA_edge`. -/
noncomputable def ecpAEdge (x : D) : D :=
  if ¬ G.cface (G.edge x0) (G.node x0) then G.edge x
  else if x = x0 then G.edge (G.node (G.node x0))
  else if x = G.node (G.node x0) then G.edge x0 else G.edge x

/-- math-comp `ecpA_node`. -/
def ecpANode (x : D) : D :=
  if x = G.node x0 then x0 else if G.node x = x0 then G.node (G.node x0) else G.node x

open Classical in
/-- math-comp `ecpA_face`. -/
noncomputable def ecpAFace (x : D) : D :=
  if G.cface (G.edge x0) (G.node x0) then G.face x
  else if x = G.edge x0 then G.node x0
  else if G.face x = G.node x0 then G.face (G.edge x0) else G.face x

omit [DecidableEq D] in
/-- `face (edge z) = node x0` iff `z = node (node x0)`. -/
private theorem face_edge_eq_node_iff (z : D) :
    G.face (G.edge z) = G.node x0 ↔ z = G.node (G.node x0) := by
  constructor
  · intro h
    rw [← G.edgeK z, h]
  · rintro rfl
    exact G.nodeK _

omit [DecidableEq D] in
/-- `node y = x0` iff `y = face (edge x0)`. -/
private theorem node_eq_iff (y : D) : G.node y = x0 ↔ y = G.face (G.edge x0) := by
  rw [eq_comm, G.eq_node_iff, eq_comm]

/-- math-comp `ecpA_subproof`. -/
theorem ecpA_subproof (x : D) : G.ecpANode x0 (G.ecpAFace x0 (G.ecpAEdge x0 x)) = x := by
  have hfe := face_edge_eq_node_iff G x0
  by_cases hc : G.cface (G.edge x0) (G.node x0)
  · have hF : ∀ y, G.ecpAFace x0 y = G.face y := fun y => by simp [ecpAFace, hc]
    rw [hF]
    by_cases hx : x = x0
    · have : G.ecpAEdge x0 x = G.edge (G.node (G.node x0)) := by simp [ecpAEdge, hc, hx]
      rw [this, G.nodeK, ecpANode, ite_eq_left rfl, hx]
    · by_cases hx' : x = G.node (G.node x0)
      · subst hx'
        have : G.ecpAEdge x0 (G.node (G.node x0)) = G.edge x0 := by simp [ecpAEdge, hc, hx]
        rw [this, ecpANode, ite_eq_right (fun h => hx ((hfe x0).1 h).symm),
          ite_eq_left (G.edgeK x0)]
      · have : G.ecpAEdge x0 x = G.edge x := by simp [ecpAEdge, hc, hx, hx']
        rw [this, ecpANode, ite_eq_right (fun h => hx' ((hfe x).1 h)), G.edgeK, ite_eq_right hx]
  · have hE : ∀ y, G.ecpAEdge x0 y = G.edge y := fun y => by simp [ecpAEdge, hc]
    rw [hE]
    by_cases hx : x = x0
    · rw [hx, ecpAFace, ite_eq_right hc, ite_eq_left rfl, ecpANode, ite_eq_left rfl]
    · have hex : G.edge x ≠ G.edge x0 := fun h => hx (G.edgeI h)
      by_cases hx' : x = G.node (G.node x0)
      · rw [ecpAFace, ite_eq_right hc, ite_eq_right hex, ite_eq_left ((hfe x).2 hx'), ecpANode,
          ite_eq_right (fun h => hx (hx'.trans ((hfe x0).1 h).symm)), ite_eq_left (G.edgeK x0), hx']
      · rw [ecpAFace, ite_eq_right hc, ite_eq_right hex, ite_eq_right (fun h => hx' ((hfe x).1 h)),
          ecpANode, ite_eq_right (fun h => hx' ((hfe x).1 h)), G.edgeK, ite_eq_right hx]

/-- math-comp `ecpA_map`. -/
noncomputable def ecpAMap : Hypermap D :=
  ⟨G.ecpAEdge x0, G.ecpANode x0, G.ecpAFace x0, G.ecpA_subproof x0⟩

/-- math-comp `ecpA x0`: the pointed map that implements an `A` step at `x0`. -/
noncomputable abbrev ecpA : PointedMap :=
  ⟨D, G.ecpAMap x0, (G.ecpAMap x0).face ((G.ecpAMap x0).edge (G.face (G.edge x0)))⟩

/-- math-comp `icpA`: the (identity) injection of `G` into `ecpA x0`. -/
abbrev icpA (x : D) : (G.ecpA x0).D := x

/-- The edge permutation of `ecpA x0`. -/
@[simp] theorem ecpA_edge_apply (x : D) : (G.ecpA x0).pointee.edge x = G.ecpAEdge x0 x := rfl
/-- The node permutation of `ecpA x0`. -/
@[simp] theorem ecpA_node_apply (x : D) : (G.ecpA x0).pointee.node x = G.ecpANode x0 x := rfl
/-- The face permutation of `ecpA x0`. -/
@[simp] theorem ecpA_face_apply (x : D) : (G.ecpA x0).pointee.face x = G.ecpAFace x0 x := rfl

/-- The `node` of the reference dart of `ecpA x0` is `face (edge x0)`. -/
theorem node_ecpA : (G.ecpA x0).pointee.node (G.ecpA x0).pointer = G.face (G.edge x0) :=
  (G.ecpAMap x0).edgeK _

/-- math-comp `baseN_ecpA`: `node` is unchanged outside `node x0` and `face (edge x0)`. -/
theorem baseN_ecpA (x y : D) (hx : ¬ (G.icpA x0 x = G.node x0 ∨ G.icpA x0 x = G.face (G.edge x0))) :
    (G.ecpA x0).pointee.node (G.icpA x0 x) = G.icpA x0 y ↔ G.node x = y := by
  show G.ecpANode x0 x = y ↔ G.node x = y
  have hx' : ¬ (x = G.node x0 ∨ x = G.face (G.edge x0)) := hx
  rw [not_or] at hx'
  rw [ecpANode, ite_eq_right hx'.1, ite_eq_right (fun h => hx'.2 ((node_eq_iff G x0 x).1 h))]

omit [DecidableEq D] in
/-- A ring of size at most `2`. -/
theorem cpring_small (h : ¬ G.LongCpring x0) :
    (G.ProperCpring x0 ∧ G.cpring x0 = [G.node x0, x0]) ∨
      (¬ G.ProperCpring x0 ∧ G.cpring x0 = [G.node x0]) := by
  have hle : (G.cpring x0).length ≤ 2 := not_lt.1 ((G.size_long_cpring x0).not.1 h)
  by_cases hp : G.ProperCpring x0
  · left
    refine ⟨hp, ?_⟩
    have h2 := (G.size_proper_cpring x0).1 hp
    have hc := G.head_proper_cpring x0 hp
    have : (G.cpring x0).drop 2 = [] := List.drop_eq_nil_of_le hle
    rw [this] at hc
    exact hc
  · right
    refine ⟨hp, ?_⟩
    have h1 : (G.cpring x0).length ≤ 1 := not_lt.1 ((G.size_proper_cpring x0).not.1 hp)
    have hc := G.head_cpring x0
    have : (G.cpring x0).tail = [] := by
      rw [← List.length_eq_zero_iff, List.length_tail]; omega
    rw [this] at hc
    exact hc

/-- math-comp `cpring_ecpA`. -/
theorem cpring_ecpA :
    (G.ecpA x0).pointee.cpring (G.ecpA x0).pointer =
      if G.LongCpring x0 then (G.cpring x0).tail.tail else G.cpring x0 := by
  have hnp := G.node_ecpA x0
  have hnd := G.cpring_uniq x0
  have hcyc := G.cycle_rev_cpring x0
  by_cases hl : G.LongCpring x0
  · rw [ite_eq_left hl]
    have hc := G.head_long_cpring x0 hl
    generalize (G.cpring x0).drop 3 = r at hc
    rw [hc] at hnd hcyc ⊢
    simp only [List.tail_cons]
    have hnx0 : G.node x0 ∉ r := fun h => by simp_all
    have hfex0 : G.face (G.edge x0) ∉ r := fun h => by simp_all
    apply (G.ecpA x0).pointee.cpring_def
    · rw [hnp]; rfl
    · refine ⟨?_, List.nodup_reverse.2 hnd.of_cons.of_cons⟩
      -- the node cycle of `G` along the ring, and that of `ecpA x0` along its tail
      rw [List.reverse_cons, cycle_iff_path (G.face (G.edge x0)), last_concat]
      have hG : path (frel G.node) (G.node x0) (r.reverse ++ [G.face (G.edge x0)]) := by
        have h1 : cycle (frel G.node) ((r.reverse ++ [G.face (G.edge x0)]) ++ [x0, G.node x0]) := by
          simpa using hcyc
        rw [cycle_iff_path x0, last_append, last_cons, last_cons, last_nil, path_append] at h1
        exact h1.1
      have hfn : (G.ecpA x0).pointee.node (G.face (G.edge x0)) = G.node (G.node x0) := by
        show G.ecpANode x0 _ = _
        rw [ecpANode, ite_eq_right hl, ite_eq_left (G.edgeK x0)]
      refine (path_congr_dropLast (e := frel (G.ecpA x0).pointee.node) (e' := frel G.node)
        (fun w => ?_) (fun z hz w => ?_)).2 hG
      · show (G.ecpA x0).pointee.node (G.face (G.edge x0)) = w ↔ G.node (G.node x0) = w
        rw [hfn]
      · rw [List.dropLast_concat, List.mem_reverse] at hz
        exact G.baseN_ecpA x0 z w (by
          rintro (h | h)
          · exact hnx0 (h ▸ hz)
          · exact hfex0 (h ▸ hz))
  · rw [ite_eq_right hl]
    have hfe : G.face (G.edge x0) = G.node x0 := not_not.1 hl
    rcases G.cpring_small x0 hl with ⟨hp, hc⟩ | ⟨hp, hc⟩
    · rw [hc]
      apply (G.ecpA x0).pointee.cpring_def
      · rw [hnp, hfe]; rfl
      · refine ⟨?_, ?_⟩
        · show (G.ecpA x0).pointee.node x0 = G.node x0 ∧ (G.ecpA x0).pointee.node (G.node x0) = x0 ∧ True
          refine ⟨?_, ?_, trivial⟩
          · show G.ecpANode x0 x0 = G.node x0
            rw [ecpANode, ite_eq_right hp, ite_eq_right (Ne.symm hp)]
          · show G.ecpANode x0 (G.node x0) = x0
            rw [ecpANode, ite_eq_left rfl]
        · simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
          exact List.nodup_cons.2 ⟨fun h => hp (List.mem_singleton.1 h), List.nodup_singleton _⟩
    · rw [hc]
      have hx : x0 = G.node x0 := not_not.1 hp
      apply (G.ecpA x0).pointee.cpring_def
      · rw [hnp, hfe]; rfl
      · refine ⟨?_, List.nodup_singleton _⟩
        show (G.ecpA x0).pointee.node (G.node x0) = G.node x0 ∧ True
        refine ⟨?_, trivial⟩
        show G.ecpANode x0 (G.node x0) = G.node x0
        rw [ecpANode, ite_eq_left rfl, ← hx]

/-- math-comp `size_cpring_ecpA`. -/
theorem size_cpring_ecpA :
    ((G.ecpA x0).pointee.cpring (G.ecpA x0).pointer).length = sub2ifgt2 (G.cpring x0).length := by
  rw [cpring_ecpA]
  split_ifs with h
  · rw [G.head_long_cpring x0 h]
    simp [sub2ifgt2]
  · have := (G.size_long_cpring x0).not.1 h
    generalize (G.cpring x0).length = n at this ⊢
    rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl <;> rfl

/-- math-comp `baseF_ecpA`: `face` is unchanged outside `edge x0` and `edge (node (node x0))`. -/
theorem baseF_ecpA (x y : D)
    (hx : ¬ (G.icpA x0 x = G.edge x0 ∨ G.icpA x0 x = G.edge (G.node (G.node x0)))) :
    (G.ecpA x0).pointee.face (G.icpA x0 x) = G.icpA x0 y ↔ G.face x = y := by
  show G.ecpAFace x0 x = y ↔ G.face x = y
  have hx' : ¬ (x = G.edge x0 ∨ x = G.edge (G.node (G.node x0))) := hx
  rw [not_or] at hx'
  have h2 : G.face x ≠ G.node x0 := fun h => hx'.2 (G.face_eq_iff.1 h)
  unfold ecpAFace
  split_ifs <;> simp_all

/-- math-comp `ecpA_merge`: the merged neighbors are in the same face of `ecpA x0`. -/
theorem ecpA_merge :
    (G.ecpA x0).pointee.cface ((G.ecpA x0).pointee.node (G.ecpA x0).pointer)
      (G.icpA x0 (G.node x0)) := by
  rw [node_ecpA]
  by_cases hc : G.cface (G.edge x0) (G.node x0)
  · have hF : ∀ y, (G.ecpA x0).pointee.face y = G.face y := fun y => by
      show G.ecpAFace x0 y = G.face y
      simp [ecpAFace, hc]
    exact (fconnect_congr hF).2 ((G.cface1 _ _).1 hc)
  · have h1 : G.cface (G.node x0) (G.edge (G.node (G.node x0))) := by
      rw [G.cface1r, G.nodeK]
    obtain ⟨p, hp, hl⟩ := connect_iff_path.1 h1
    obtain ⟨p', hp', hu, -, hl'⟩ := shortenP hp
    rw [hl] at hl'
    have hbase : ∀ z ∈ belast (G.node x0) p', ∀ w,
        (G.ecpA x0).pointee.face z = w ↔ G.face z = w := by
      intro z hz w
      apply G.baseF_ecpA x0 z w
      rintro (h | h)
      · have := path_connect hp' (mem_belast hz)
        exact hc (G.cfaceC.1 (h ▸ this))
      · exact last_not_mem_belast hu (hl' ▸ h ▸ hz)
    have hp'' : fpath (G.ecpA x0).pointee.face (G.node x0) p' := (path_congr_belast hbase).2 hp'
    have hstep : (G.ecpA x0).pointee.face (G.edge (G.node (G.node x0))) = G.face (G.edge x0) := by
      show G.ecpAFace x0 _ = _
      rw [ecpAFace, ite_eq_right hc, ite_eq_right, ite_eq_left (G.nodeK _)]
      intro h
      have h' := G.edgeI h
      apply hc
      have := G.nodeK (G.node x0)
      rw [h'] at this
      exact connect_of_rel this
    have : (G.ecpA x0).pointee.cface (G.node x0) (G.face (G.edge x0)) :=
      connect_trans (path_connect hp'' (hl' ▸ mem_last _ _)) (connect_of_rel hstep)
    exact (G.ecpA x0).pointee.cfaceC.1 this

/-- math-comp `sub_cface_icpA`. -/
theorem sub_cface_icpA {x y : D} (h : G.cface x y) :
    (G.ecpA x0).pointee.cface (G.icpA x0 x) (G.icpA x0 y) := by
  have hm := G.ecpA_merge x0
  rw [node_ecpA] at hm
  refine connect_sub (fun a b hab => ?_) h
  subst hab
  by_cases hc : G.cface (G.edge x0) (G.node x0)
  · exact connect_of_rel (show G.ecpAFace x0 a = G.face a by simp [ecpAFace, hc])
  · by_cases ha : a = G.edge x0
    · subst ha
      have h1 : (G.ecpA x0).pointee.face (G.edge x0) = G.node x0 := by
        show G.ecpAFace x0 _ = _
        simp [ecpAFace, hc]
      exact connect_trans (connect_of_rel h1) ((G.ecpA x0).pointee.cfaceC.1 hm)
    · by_cases hfa : G.face a = G.node x0
      · have h1 : (G.ecpA x0).pointee.face a = G.face (G.edge x0) := by
          show G.ecpAFace x0 _ = _
          simp [ecpAFace, hc, ha, hfa]
        rw [hfa]
        exact connect_trans (connect_of_rel h1) hm
      · exact connect_of_rel (show G.ecpAFace x0 a = G.face a by simp [ecpAFace, hc, ha, hfa])

/-- math-comp `cface_icpA`. -/
theorem cface_icpA (x y : D) :
    (G.ecpA x0).pointee.cface (G.icpA x0 x) (G.icpA x0 y) ↔
      G.cface x y ∨ (x ∈ G.fband [G.face (G.edge x0), G.node x0] ∧
        y ∈ G.fband [G.face (G.edge x0), G.node x0]) := by
  set a := G.fband [G.face (G.edge x0), G.node x0] with ha
  have hex0 : G.edge x0 ∈ a := ⟨G.face (G.edge x0), List.mem_cons_self, fconnect1 _ _⟩
  have hennx0 : G.edge (G.node (G.node x0)) ∈ a :=
    ⟨G.node x0, by simp, by rw [G.cface1, G.nodeK]⟩
  have key : ∀ x y, x ∉ a → ((G.ecpA x0).pointee.cface x y ↔ G.cface x y) := by
    intro x y hx
    have hbase : ∀ x' y' : D, id x' ∈ aᶜ →
        ((G.ecpA x0).pointee.face (id x') = id y' ↔ G.face x' = y') := by
      intro x' y' hx'
      apply G.baseF_ecpA x0 x' y'
      rintro (h | h)
      · exact hx' (by rw [show id x' = G.edge x0 from h]; exact hex0)
      · exact hx' (by rw [show id x' = G.edge (G.node (G.node x0)) from h]; exact hennx0)
    refine (connect_iff_of_base (e := frel (G.ecpA x0).pointee.face) (e' := frel G.face)
      (h := id) injective_id (a := aᶜ) ?_ ?_ hbase hx).symm
    · intro u v huv hu
      have huv' : G.face u = v := (hbase u v hu).1 huv
      subst huv'
      exact fun h => hu (((G.fbandF _) u _ rfl).2 h)
    · intro u _
      exact ⟨u, rfl⟩
  by_cases hx : x ∈ a
  · by_cases hy : y ∈ a
    · simp only [hx, hy, and_self, or_true, iff_true]
      obtain ⟨t, ht, hxt⟩ := hx
      obtain ⟨t', ht', hyt'⟩ := hy
      have hm := G.ecpA_merge x0
      rw [node_ecpA] at hm
      have hxt' := G.sub_cface_icpA x0 hxt
      have hyt'' := G.sub_cface_icpA x0 hyt'
      have htt' : (G.ecpA x0).pointee.cface t t' := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht ht'
        rcases ht with rfl | rfl <;> rcases ht' with rfl | rfl
        · exact connect_refl _
        · exact hm
        · exact (G.ecpA x0).pointee.cfaceC.1 hm
        · exact connect_refl _
      exact connect_trans hxt' (connect_trans htt' ((G.ecpA x0).pointee.cfaceC.1 hyt''))
    · simp only [hy, and_false, or_false]
      rw [(G.ecpA x0).pointee.cfaceC, G.cfaceC]
      exact key y x hy
  · simp only [hx, false_and, or_false]
    exact key x y hx

/-- math-comp `sub_adj_icpA`. -/
theorem sub_adj_icpA {x y : D} (h : G.adj x y) :
    (G.ecpA x0).pointee.adj (G.icpA x0 x) (G.icpA x0 y) := by
  obtain ⟨z, hxz, hzy⟩ := G.adjP.1 h
  refine (G.ecpA x0).pointee.adjP.2 ⟨z, G.sub_cface_icpA x0 hxz, ?_⟩
  show (G.ecpA x0).pointee.cface (G.ecpAEdge x0 z) y
  by_cases hc : G.cface (G.edge x0) (G.node x0)
  · have hennx0 : G.cface (G.edge (G.node (G.node x0))) (G.edge x0) := by
      rw [G.cface1, G.nodeK]; exact G.cfaceC.1 hc
    by_cases hz : z = x0
    · subst hz
      have : G.ecpAEdge z z = G.edge (G.node (G.node z)) := by simp [ecpAEdge, hc]
      rw [this]
      exact G.sub_cface_icpA z (connect_trans hennx0 hzy)
    · by_cases hz' : z = G.node (G.node x0)
      · subst hz'
        have : G.ecpAEdge x0 (G.node (G.node x0)) = G.edge x0 := by simp [ecpAEdge, hc, hz]
        rw [this]
        exact G.sub_cface_icpA x0 (connect_trans (G.cfaceC.1 hennx0) hzy)
      · have : G.ecpAEdge x0 z = G.edge z := by simp [ecpAEdge, hc, hz, hz']
        rw [this]
        exact G.sub_cface_icpA x0 hzy
  · have : G.ecpAEdge x0 z = G.edge z := by simp [ecpAEdge, hc]
    rw [this]
    exact G.sub_cface_icpA x0 hzy

end EcpA

end Hypermap

end FourColor
