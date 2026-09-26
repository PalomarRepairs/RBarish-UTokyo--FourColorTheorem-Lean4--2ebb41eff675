/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfMap.ExtUN

/-!
# Composite construction steps (port of `cfmap.v`, section `CompExtConfig`)

Given a reference dart `x0` in a hypermap `G`:

* `G.ecpR' x0` : a pointed map that implements an `R'` step at `x0` (math-comp `ecpR'`,
  `ecpR ((order node x0).-1) x0`).
* `G.ecpK x0`  : a pointed map that implements a `K` step at `x0` (math-comp `ecpK`,
  `ecpR 1 (ecpN ecpR')`).
* `G.ecpY x0`  : a pointed map that implements a `Y` step at `x0` (math-comp `ecpY`,
  `ecpN (ecpU x0)`).
* `G.ecpH x0`  : a pointed map that implements an `H` step at `x0` (math-comp `ecpH`,
  `ecpN ecpY`).
* `G.icpR' x0`, `G.icpK x0`, `G.icpY x0`, `G.icpH x0` : the injections of `G` into these maps.

math-comp's `sumor` results `fband_icpY`, `fband_icpH` are stated as disjunctions.
-/

namespace FourColor

open Function CfMap EcpDart

universe u

namespace Hypermap

variable {D : Type u} [Fintype D] [DecidableEq D] (G : Hypermap D)

section CompExtConfig

variable (x0 : D)

/-! ### The `R'` and `K` steps -/

/-- math-comp `ecpR'`: the pointed map that implements an `R'` step (a single-step reverse
rotation) at `x0`. -/
noncomputable abbrev ecpR' : PointedMap := G.ecpR (order G.node x0 - 1) x0

/-- math-comp `icpR'`. -/
noncomputable abbrev icpR' (x : D) : (G.ecpR' x0).D := G.icpR (order G.node x0 - 1) x0 x

omit [DecidableEq D] in
/-- math-comp `ecpR'_eq`: the reference dart of `ecpR' x0` is `node x0`. -/
theorem ecpR'_eq [DecidableEq D] : (G.ecpR' x0).pointer = G.node x0 := by
  show G.node^[order G.node x0 - (order G.node x0 - 1)] x0 = G.node x0
  rw [Nat.sub_sub_self (order_pos G.nodeI x0)]
  rfl

/-- math-comp `ecpK`: the pointed map that implements a `K` step at `x0`
(`ecpR 1 (ecpN ecpR')`). -/
noncomputable abbrev ecpK : PointedMap :=
  (G.ecpN (G.ecpR' x0).pointer).pointee.ecpR 1 (G.ecpN (G.ecpR' x0).pointer).pointer

/-- math-comp `icpK`: the injection of `G` into `ecpK x0`
(`icpR 1 (ecpN ecpR') (icpN ecpR' (icpR' x))`). -/
noncomputable abbrev icpK (x : D) : (G.ecpK x0).D :=
  (G.ecpN (G.ecpR' x0).pointer).pointee.icpR 1 (G.ecpN (G.ecpR' x0).pointer).pointer
    (G.icpN (G.ecpR' x0).pointer (G.icpR' x0 x))

/-- math-comp `size_cpring_ecpK`. -/
theorem size_cpring_ecpK :
    ((G.ecpK x0).pointee.cpring (G.ecpK x0).pointer).length = (G.cpring x0).length - 2 + 1 := by
  rw [size_cpring_ecpR, size_cpring_ecpN, size_cpring_ecpR]

/-- math-comp `icpK_inj`. -/
theorem icpK_inj : Injective (G.icpK x0) := ecp_inj

/-- math-comp `icpK_edge`. -/
theorem icpK_edge (x : D) : G.icpK x0 (G.edge x) = (G.ecpK x0).pointee.edge (G.icpK x0 x) := rfl

/-- The `node` of the reference dart of `ecpK x0` is the reference dart `X` of the `N` step. -/
theorem node_ecpK :
    (G.ecpK x0).pointee.node (G.ecpK x0).pointer = (G.ecpN (G.ecpR' x0).pointer).pointer := by
  show (G.ecpN (G.ecpR' x0).pointer).pointee.node
    ((G.ecpN (G.ecpR' x0).pointer).pointee.ecpR 1 (G.ecpN (G.ecpR' x0).pointer).pointer).pointer = _
  rw [ecpR1_eq, Hypermap.edgeK]

/-- math-comp `cpring_ecpK`. -/
theorem cpring_ecpK :
    (G.ecpK x0).pointee.cpring (G.ecpK x0).pointer =
      (G.ecpK x0).pointee.node (G.ecpK x0).pointer :: ((G.cpring x0).drop 2).map (G.icpK x0) := by
  rw [node_ecpK, cpring_ecpR, rot1_cpring_ecpN, cpring_ecpR]
  congr 3
  rw [show order G.node x0 - 1 = (G.cpring x0).length - 1 by rw [size_cpring]]
  exact rot_rotr 1 (G.cpring x0)

/-- math-comp `cface_icpK`. -/
theorem cface_icpK (x y : D) :
    (G.ecpK x0).pointee.cface (G.icpK x0 x) (G.icpK x0 y) ↔ G.cface x y :=
  G.cface_icpN _ x y

/-- math-comp `adj_icpK`: the adjacencies of `ecpK x0` between darts of `G` are those of `G`,
plus those between the faces of `edge x0` and of `node x0`. -/
theorem adj_icpK (x y : D) :
    (G.ecpK x0).pointee.adj (G.icpK x0 x) (G.icpK x0 y) ↔
      G.adj x y ∨ (G.cface (G.edge x0) x ∧ G.cface (G.node x0) y) ∨
        (G.cface (G.edge x0) y ∧ G.cface (G.node x0) x) := by
  refine (G.adj_icpN _ x y).trans ?_
  rw [G.ecpR'_eq, G.nodeK]

/-- math-comp `sub_adj_icpK`. -/
theorem sub_adj_icpK {x y : D} (h : G.adj x y) :
    (G.ecpK x0).pointee.adj (G.icpK x0 x) (G.icpK x0 y) :=
  (G.adj_icpK x0 x y).2 (Or.inl h)

/-- math-comp `cface_node_ecpK`. -/
theorem cface_node_ecpK :
    (G.ecpK x0).pointee.cface ((G.ecpK x0).pointee.node (G.ecpK x0).pointer)
      (G.icpK x0 (G.node x0)) := by
  rw [node_ecpK]
  have := G.cface_ecpN (G.ecpR' x0).pointer
  rw [← G.ecpR'_eq x0]
  exact this

/-- math-comp `cface_ecpK`. -/
theorem cface_ecpK :
    (G.ecpK x0).pointee.cface (G.ecpK x0).pointer (G.icpK x0 (G.face (G.edge x0))) := by
  have hp : (G.ecpK x0).pointer = (G.ecpN (G.ecpR' x0).pointer).pointee.face
      ((G.ecpN (G.ecpR' x0).pointer).pointee.edge IcpX) := ecpR1_eq _ _
  rw [hp]
  show (G.ecpNMap (G.ecpR' x0).pointer).cface
    (G.ecpNFace (G.ecpR' x0).pointer IcpXe) (Icp (G.face (G.edge x0)))
  generalize hy : (G.ecpR' x0).pointer = y
  have hy' : y = G.node x0 := hy ▸ G.ecpR'_eq x0
  subst hy'
  by_cases hl : G.LongCpring (G.node x0)
  · rw [ecpNFace, ite_eq_left hl, G.nodeK]
  · rw [ecpNFace, ite_eq_right hl]
    apply connect_of_rel
    show Icp (G.node x0) = Icp (G.face (G.edge x0))
    have h1 : G.face (G.edge (G.node x0)) = G.node (G.node x0) := not_not.1 hl
    rw [G.nodeK] at h1
    have h2 : G.face (G.edge (G.node (G.node x0))) = G.node x0 := G.nodeK _
    rw [← h1] at h2
    rw [h2]

/-- math-comp `fband_icpK`. -/
theorem fband_icpK (u : (G.ecpK x0).D) : ∃ x, (G.ecpK x0).pointee.cface u (G.icpK x0 x) :=
  G.fband_icpN _ u

/-! ### The `Y` step -/

/-- The ring of `ecpU x0` is long. -/
theorem long_ecpU : (G.ecpU x0).pointee.LongCpring (G.ecpU x0).pointer := by
  show G.ecpUFace x0 (G.ecpEdge IcpX) ≠ G.ecpUNode x0 IcpX
  simp [ecpEdge, ecpUFace, ecpUNode]

/-- The ring of `ecpU x0` is proper. -/
theorem proper_ecpU : (G.ecpU x0).pointee.ProperCpring (G.ecpU x0).pointer := by
  show IcpX ≠ G.ecpUNode x0 IcpX
  simp [ecpUNode]

/-- math-comp `ecpY`: the pointed map that implements a `Y` step at `x0` (`ecpN (ecpU x0)`). -/
abbrev ecpY : PointedMap := (G.ecpU x0).pointee.ecpN (G.ecpU x0).pointer

/-- math-comp `plain_ecpY`. -/
theorem plain_ecpY (plainG : G.Plain) : (G.ecpY x0).pointee.Plain :=
  (G.ecpU x0).pointee.plain_ecpN _ (G.plain_ecpU x0 plainG)

/-- math-comp `cubic_ecpY`. -/
theorem cubic_ecpY (cubicG : G.Quasicubic (G.cpring x0).reverse) :
    (G.ecpY x0).pointee.Quasicubic
      ((G.ecpY x0).pointee.cpring (G.ecpY x0).pointer).reverse :=
  (G.ecpU x0).pointee.cubic_ecpN _ (G.cubic_ecpU x0 cubicG) (G.proper_ecpU x0)

/-- math-comp `size_cpring_ecpY`. -/
theorem size_cpring_ecpY :
    ((G.ecpY x0).pointee.cpring (G.ecpY x0).pointer).length = (G.cpring x0).length + 1 := by
  rw [size_cpring_ecpN, size_cpring_ecpU]
  omega

/-- math-comp `planar_ecpY`. -/
theorem planar_ecpY (planarG : G.Planar) (plainG : G.Plain)
    (cubicG : G.Quasicubic (G.cpring x0).reverse) (ccG : G.Connected) :
    (G.ecpY x0).pointee.Planar :=
  (G.ecpU x0).pointee.planar_ecpN _ (G.planar_ecpU x0 planarG plainG cubicG ccG)
    (G.plain_ecpU x0 plainG) (G.cubic_ecpU x0 cubicG) (G.connected_ecpU x0 ccG) (G.proper_ecpU x0)

/-- math-comp `connected_ecpY`. -/
theorem connected_ecpY (ccG : G.Connected) : (G.ecpY x0).pointee.Connected :=
  (G.ecpU x0).pointee.connected_ecpN _ (G.connected_ecpU x0 ccG)

/-- math-comp `icpY`: the injection of `G` into `ecpY x0`. -/
abbrev icpY (x : D) : (G.ecpY x0).D := (G.ecpU x0).pointee.icpN _ (G.icpU x0 x)

/-- math-comp `icpY_inj`. -/
theorem icpY_inj : Injective (G.icpY x0) := fun _ _ h => Icp.inj (Icp.inj h)

/-- math-comp `icpY_edge`. -/
theorem icpY_edge (x : D) : G.icpY x0 (G.edge x) = (G.ecpY x0).pointee.edge (G.icpY x0 x) := rfl

/-- math-comp `icpY_node`. -/
theorem icpY_node (x : D) (hx : x ∉ [G.node x0, x0]) :
    G.icpY x0 (G.node x) = (G.ecpY x0).pointee.node (G.icpY x0 x) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  have h2 : G.node x ≠ G.node x0 := fun h => hx.2 (G.nodeI h)
  show Icp (Icp (G.node x)) = (G.ecpUMap x0).ecpNNode IcpX (Icp (Icp x))
  simp [ecpNNode, ecpUNode, hx.1, h2]

/-- math-comp `drop2_cpring_ecpY`. -/
theorem drop2_cpring_ecpY :
    ((G.ecpY x0).pointee.cpring (G.ecpY x0).pointer).drop 2 = (G.cpring x0).tail.map (G.icpY x0) := by
  rw [cpring_ecpN, ite_eq_left (G.long_ecpU x0), cpring_ecpU]
  simp only [List.drop_succ_cons, List.drop_zero, List.drop_one, ← List.map_tail, List.map_map]
  rfl

/-- The ring of `ecpY x0` is proper. -/
theorem proper_ecpY : (G.ecpY x0).pointee.ProperCpring (G.ecpY x0).pointer := by
  rw [size_proper_cpring, size_cpring_ecpY]
  have := G.size_cpring x0
  have := order_pos G.nodeI x0
  omega

/-- math-comp `cpring_ecpY`. -/
theorem cpring_ecpY :
    (G.ecpY x0).pointee.cpring (G.ecpY x0).pointer =
      (G.ecpY x0).pointee.node (G.ecpY x0).pointer :: (G.ecpY x0).pointer ::
        (G.cpring x0).tail.map (G.icpY x0) := by
  rw [head_proper_cpring _ _ (G.proper_ecpY x0), drop2_cpring_ecpY]

/-- math-comp `cface_icpY`. -/
theorem cface_icpY (x y : D) :
    (G.ecpY x0).pointee.cface (G.icpY x0 x) (G.icpY x0 y) ↔ G.cface x y :=
  ((G.ecpU x0).pointee.cface_icpN _ _ _).trans (G.cface_icpU x0 x y)

/-- math-comp `adj_icpY`. -/
theorem adj_icpY (x y : D) :
    (G.ecpY x0).pointee.adj (G.icpY x0 x) (G.icpY x0 y) ↔ G.adj x y := by
  refine ((G.ecpU x0).pointee.adj_icpN _ _ _).trans ?_
  rw [G.cface_ecpU x0, G.cface_ecpU x0, G.adj_icpU x0]
  simp

/-- The face of the `node` of the reference dart of `ecpY x0` is `node x0`. -/
theorem face_node_ecpY :
    (G.ecpY x0).pointee.face ((G.ecpY x0).pointee.node (G.ecpY x0).pointer) =
      G.icpY x0 (G.node x0) := by
  show (G.ecpUMap x0).ecpNFace IcpX ((G.ecpUMap x0).ecpNNode IcpX IcpX) = Icp (Icp (G.node x0))
  rw [ecpNNode, ite_eq_left (G.long_ecpU x0)]
  simp [ecpNFace, ecpUFace, ecpEdge, ecpUNode]

/-- math-comp `cface_node_ecpY`. -/
theorem cface_node_ecpY :
    (G.ecpY x0).pointee.cface ((G.ecpY x0).pointee.node (G.ecpY x0).pointer)
      (G.icpY x0 (G.node x0)) :=
  connect_of_rel (G.face_node_ecpY x0)

/-- The face of the reference dart of `ecpY x0` is `[X, face X]`. -/
theorem fcycle_ecpY :
    fcycle (G.ecpY x0).pointee.face
      [(G.ecpY x0).pointer, (G.ecpY x0).pointee.face (G.ecpY x0).pointer] := by
  show (G.ecpUMap x0).ecpNFace IcpX IcpX = _ ∧
    (G.ecpUMap x0).ecpNFace IcpX ((G.ecpUMap x0).ecpNFace IcpX IcpX) = IcpX ∧ True
  simp [ecpNFace, ecpUFace, ecpEdge, ecpUNode]

/-- math-comp `cface_ecpY`. -/
theorem cface_ecpY (u : (G.ecpY x0).D) :
    (G.ecpY x0).pointee.cface (G.ecpY x0).pointer u ↔
      u ∈ [(G.ecpY x0).pointer, (G.ecpY x0).pointee.face (G.ecpY x0).pointer] :=
  fconnect_cycle (G.fcycle_ecpY x0) List.mem_cons_self

/-- The face of `edge X` in `ecpY x0` is `x0`. -/
theorem face_edge_ecpY (x0gt1 : G.ProperCpring x0) :
    (G.ecpY x0).pointee.face ((G.ecpY x0).pointee.edge (G.ecpY x0).pointer) = G.icpY x0 x0 := by
  show (G.ecpUMap x0).ecpNFace IcpX IcpXe = Icp (Icp x0)
  rw [ecpNFace, ite_eq_left (G.long_ecpU x0)]
  have : x0 ≠ G.node x0 := x0gt1
  simp [ecpUFace, ecpEdge, this, G.nodeK]

/-- The face of `edge (face X)` in `ecpY x0` is `node x0`. -/
theorem face_edge_face_ecpY :
    (G.ecpY x0).pointee.face ((G.ecpY x0).pointee.edge
      ((G.ecpY x0).pointee.face (G.ecpY x0).pointer)) = G.icpY x0 (G.node x0) := by
  show (G.ecpUMap x0).ecpNFace IcpX ((G.ecpUMap x0).ecpEdge ((G.ecpUMap x0).ecpNFace IcpX IcpX)) =
    Icp (Icp (G.node x0))
  simp [ecpNFace, ecpUFace, ecpEdge, ecpUNode]

/-- math-comp `adj_ecpY`. -/
theorem adj_ecpY (x0gt1 : G.ProperCpring x0) (u : (G.ecpY x0).D) :
    (G.ecpY x0).pointee.adj (G.ecpY x0).pointer u ↔
      u ∈ (G.ecpY x0).pointee.fband ([G.node x0, x0].map (G.icpY x0)) := by
  set M := (G.ecpY x0).pointee
  have h1 := G.face_edge_ecpY x0 x0gt1
  have h2 := G.face_edge_face_ecpY x0
  rw [M.adjP, M.mem_fband]
  constructor
  · rintro ⟨v, hv, hvu⟩
    rw [G.cface_ecpY x0 v] at hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    have hvu' := M.cfaceC.1 ((M.cface1 _ _).1 hvu)
    rcases hv with rfl | rfl
    · rw [h1] at hvu'
      exact ⟨G.icpY x0 x0, by simp, hvu'⟩
    · rw [h2] at hvu'
      exact ⟨G.icpY x0 (G.node x0), by simp, hvu'⟩
  · rintro ⟨w, hw, huw⟩
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · refine ⟨M.face (G.ecpY x0).pointer, fconnect1 _ _, ?_⟩
      exact (M.cface1 _ _).2 (by rw [h2]; exact M.cfaceC.1 huw)
    · refine ⟨(G.ecpY x0).pointer, connect_refl _, ?_⟩
      exact (M.cface1 _ _).2 (by rw [h1]; exact M.cfaceC.1 huw)

/-- math-comp `fband_icpY`. -/
theorem fband_icpY (u : (G.ecpY x0).D) :
    (∃ x, (G.ecpY x0).pointee.cface u (G.icpY x0 x)) ∨
      (G.ecpY x0).pointee.cface (G.ecpY x0).pointer u := by
  set M := (G.ecpY x0).pointee
  obtain ⟨v, hv⟩ := (G.ecpU x0).pointee.fband_icpN _ u
  rcases G.fband_icpU x0 v with ⟨x, hx⟩ | hX
  · exact Or.inl ⟨x, connect_trans hv (((G.ecpU x0).pointee.cface_icpN _ _ _).2 hx)⟩
  · right
    have h1 : M.cface (G.ecpY x0).pointer (Icp IcpX) := fconnect1 _ _
    exact connect_trans h1 (connect_trans (((G.ecpU x0).pointee.cface_icpN _ _ _).2 hX)
      (M.cfaceC.1 hv))

omit [Fintype D] in
/-- An `N` step preserves bridgelessness, provided the new edge is not a bridge. -/
private theorem bridgeless_ecpN_of [Fintype D] {x0 : D} (bridge'G : G.Bridgeless)
    (hX : ¬ (G.ecpN x0).pointee.cface (G.ecpN x0).pointer
      ((G.ecpN x0).pointee.edge (G.ecpN x0).pointer)) :
    (G.ecpN x0).pointee.Bridgeless := by
  set M := (G.ecpN x0).pointee
  rintro ⟨u, hu⟩
  match u, hu with
  | IcpX, hu => exact hX hu
  | IcpXe, hu => exact hX (M.cfaceC.1 hu)
  | Icp x, hu => exact G.bridgeless_cface bridge'G x ((G.cface_icpN x0 x (G.edge x)).1 hu)

/-- math-comp `bridgeless_ecpY`. -/
theorem bridgeless_ecpY (bridge'G : G.Bridgeless) : (G.ecpY x0).pointee.Bridgeless := by
  apply (G.ecpU x0).pointee.bridgeless_ecpN_of (G.bridgeless_ecpU x0 bridge'G)
  rw [G.cface_ecpY x0]
  show IcpXe ∉ [IcpX, (G.ecpUMap x0).ecpNFace IcpX IcpX]
  simp [ecpNFace]

/-! ### The `H` step -/

/-- The ring of `ecpY x0` is long when that of `x0` is proper. -/
theorem long_ecpY (x0gt1 : G.ProperCpring x0) :
    (G.ecpY x0).pointee.LongCpring (G.ecpY x0).pointer := by
  rw [size_long_cpring, size_cpring_ecpY]
  have := (G.size_proper_cpring x0).1 x0gt1
  omega

/-- math-comp `ecpH`: the pointed map that implements an `H` step at `x0` (`ecpN ecpY`). -/
abbrev ecpH : PointedMap := (G.ecpY x0).pointee.ecpN (G.ecpY x0).pointer

/-- math-comp `plain_ecpH`. -/
theorem plain_ecpH (plainG : G.Plain) : (G.ecpH x0).pointee.Plain :=
  (G.ecpY x0).pointee.plain_ecpN _ (G.plain_ecpY x0 plainG)

/-- math-comp `cubic_ecpH`. -/
theorem cubic_ecpH (cubicG : G.Quasicubic (G.cpring x0).reverse) :
    (G.ecpH x0).pointee.Quasicubic
      ((G.ecpH x0).pointee.cpring (G.ecpH x0).pointer).reverse :=
  (G.ecpY x0).pointee.cubic_ecpN _ (G.cubic_ecpY x0 cubicG) (G.proper_ecpY x0)

/-- math-comp `size_cpring_ecpH`. -/
theorem size_cpring_ecpH :
    ((G.ecpH x0).pointee.cpring (G.ecpH x0).pointer).length = (G.cpring x0).length := by
  rw [size_cpring_ecpN, size_cpring_ecpY]
  have := G.size_cpring x0
  have := order_pos G.nodeI x0
  omega

/-- math-comp `planar_ecpH`. -/
theorem planar_ecpH (planarG : G.Planar) (plainG : G.Plain)
    (cubicG : G.Quasicubic (G.cpring x0).reverse) (ccG : G.Connected) :
    (G.ecpH x0).pointee.Planar :=
  (G.ecpY x0).pointee.planar_ecpN _ (G.planar_ecpY x0 planarG plainG cubicG ccG)
    (G.plain_ecpY x0 plainG) (G.cubic_ecpY x0 cubicG) (G.connected_ecpY x0 ccG)
    (G.proper_ecpY x0)

/-- math-comp `connected_ecpH`. -/
theorem connected_ecpH (ccG : G.Connected) : (G.ecpH x0).pointee.Connected :=
  (G.ecpY x0).pointee.connected_ecpN _ (G.connected_ecpY x0 ccG)

/-- math-comp `icpH`: the injection of `G` into `ecpH x0`. -/
abbrev icpH (x : D) : (G.ecpH x0).D := (G.ecpY x0).pointee.icpN _ (G.icpY x0 x)

/-- math-comp `icpH_inj`. -/
theorem icpH_inj : Injective (G.icpH x0) := fun _ _ h => G.icpY_inj x0 (Icp.inj h)

/-- math-comp `icpH_edge`. -/
theorem icpH_edge (x : D) : G.icpH x0 (G.edge x) = (G.ecpH x0).pointee.edge (G.icpH x0 x) := rfl

/-- math-comp `icpH_node`. -/
theorem icpH_node (x : D) (hx : x ∉ [G.node x0, x0, G.face (G.edge x0)]) :
    G.icpH x0 (G.node x) = (G.ecpH x0).pointee.node (G.icpH x0 x) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  have e1 := G.icpY_node x0 x (by simp [h1, h2])
  have h4 : G.node x ≠ G.node x0 := fun h => h2 (G.nodeI h)
  have h5 : G.node x ≠ x0 := fun h => h3 (by rw [← h, G.nodeK])
  have e2 := G.icpY_node x0 (G.node x) (by simp [h4, h5])
  show Icp (G.icpY x0 (G.node x)) =
    (G.ecpY x0).pointee.ecpNNode (G.ecpY x0).pointer (Icp (G.icpY x0 x))
  rw [ecpNNode, ite_eq_right (by simp), ← e1, ← e2, ite_eq_right (by simp)]

/-- math-comp `cface_icpH`. -/
theorem cface_icpH (x y : D) :
    (G.ecpH x0).pointee.cface (G.icpH x0 x) (G.icpH x0 y) ↔ G.cface x y :=
  ((G.ecpY x0).pointee.cface_icpN _ _ _).trans (G.cface_icpY x0 x y)

/-- The face of the reference dart of `ecpY x0`. -/
theorem face_ecpY : (G.ecpY x0).pointee.face (G.ecpY x0).pointer = Icp IcpX := rfl

/-- math-comp `adj_icpH`. -/
theorem adj_icpH (x y : D) :
    (G.ecpH x0).pointee.adj (G.icpH x0 x) (G.icpH x0 y) ↔ G.adj x y := by
  refine ((G.ecpY x0).pointee.adj_icpN _ _ _).trans ?_
  rw [G.cface_ecpY x0, G.cface_ecpY x0, G.adj_icpY x0, face_ecpY]
  simp

/-- math-comp `drop2_cpring_ecpH`. -/
theorem drop2_cpring_ecpH :
    ((G.ecpH x0).pointee.cpring (G.ecpH x0).pointer).drop 2 =
      ((G.cpring x0).drop 2).map (G.icpH x0) := by
  rw [cpring_ecpN]
  split_ifs with hl
  · simp only [List.drop_succ_cons, List.drop_zero]
    rw [show ((G.ecpY x0).pointee.cpring (G.ecpY x0).pointer).drop 3 =
      (((G.ecpY x0).pointee.cpring (G.ecpY x0).pointer).drop 2).drop 1 by
        rw [List.drop_drop], drop2_cpring_ecpY]
    rw [← List.map_drop, List.map_map, List.drop_one,
      show (G.cpring x0).tail.tail = (G.cpring x0).drop 2 by
        rcases G.cpring x0 with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> rfl]
    rfl
  · have hle := (size_long_cpring _ _).not.1 hl
    rw [size_cpring_ecpY] at hle
    have : (G.cpring x0).drop 2 = [] := List.drop_eq_nil_of_le (by omega)
    rw [this]
    rfl

/-- The ring of `ecpH x0` is proper when that of `x0` is. -/
theorem proper_ecpH (x0gt1 : G.ProperCpring x0) :
    (G.ecpH x0).pointee.ProperCpring (G.ecpH x0).pointer := by
  rw [size_proper_cpring, size_cpring_ecpH]
  exact (G.size_proper_cpring x0).1 x0gt1

/-- math-comp `cpring_ecpH`. -/
theorem cpring_ecpH (x0gt1 : G.ProperCpring x0) :
    (G.ecpH x0).pointee.cpring (G.ecpH x0).pointer =
      (G.ecpH x0).pointee.node (G.ecpH x0).pointer :: (G.ecpH x0).pointer ::
        ((G.cpring x0).drop 2).map (G.icpH x0) := by
  rw [head_proper_cpring _ _ (G.proper_ecpH x0 x0gt1), drop2_cpring_ecpH]

/-- The `node` of the reference dart of `ecpY x0`. -/
theorem node_ecpY : (G.ecpY x0).pointee.node (G.ecpY x0).pointer = Icp IcpXe := by
  show (G.ecpUMap x0).ecpNNode IcpX IcpX = _
  rw [ecpNNode, ite_eq_left (G.long_ecpU x0)]
  rfl

/-- The face of the reference dart of `ecpH x0`. -/
theorem face_ecpH : (G.ecpH x0).pointee.face (G.ecpH x0).pointer = Icp IcpX := rfl

/-- The edge of the face of the edge of the reference dart of `ecpY x0`. -/
private theorem edge_face_edge_ecpY (x0gt1 : G.ProperCpring x0) :
    (G.ecpY x0).pointee.edge ((G.ecpY x0).pointee.face ((G.ecpY x0).pointee.edge
      (G.ecpY x0).pointer)) = Icp (Icp (G.edge x0)) := by
  rw [G.face_edge_ecpY x0 x0gt1]
  rfl

/-- The edge of the node of the reference dart of `ecpY x0`. -/
private theorem edge_node_ecpY :
    (G.ecpY x0).pointee.edge ((G.ecpY x0).pointee.node (G.ecpY x0).pointer) = Icp IcpX := by
  rw [G.node_ecpY x0]
  rfl

/-- The second dart of the face of the reference dart of `ecpH x0`. -/
theorem face_face_ecpH (x0gt1 : G.ProperCpring x0) :
    (G.ecpH x0).pointee.face ((G.ecpH x0).pointee.face (G.ecpH x0).pointer) = Icp (Icp IcpX) := by
  show (G.ecpY x0).pointee.ecpNFace (G.ecpY x0).pointer (Icp IcpX) = _
  rw [ecpNFace, ite_eq_right (by rw [G.edge_face_edge_ecpY x0 x0gt1]; simp),
    ite_eq_right (by rw [G.edge_node_ecpY x0]; simp)]
  rfl

/-- The face of the reference dart of `ecpH x0` is a triangle. -/
theorem face_face_face_ecpH (x0gt1 : G.ProperCpring x0) :
    (G.ecpH x0).pointee.face ((G.ecpH x0).pointee.face
      ((G.ecpH x0).pointee.face (G.ecpH x0).pointer)) = (G.ecpH x0).pointer := by
  rw [G.face_face_ecpH x0 x0gt1]
  show (G.ecpY x0).pointee.ecpNFace (G.ecpY x0).pointer (Icp (Icp IcpX)) = IcpX
  rw [ecpNFace, ite_eq_right (by rw [G.edge_face_edge_ecpY x0 x0gt1]; simp),
    ite_eq_left (by rw [G.edge_node_ecpY x0])]

/-- math-comp `cface_node_ecpH`. -/
theorem cface_node_ecpH (x0gt1 : G.ProperCpring x0) :
    (G.ecpH x0).pointee.cface ((G.ecpH x0).pointee.node (G.ecpH x0).pointer)
      (G.icpH x0 (G.node x0)) := by
  apply connect_of_rel
  show (G.ecpY x0).pointee.ecpNFace (G.ecpY x0).pointer
    ((G.ecpY x0).pointee.ecpNNode (G.ecpY x0).pointer IcpX) = Icp (G.icpY x0 (G.node x0))
  rw [ecpNNode, ite_eq_left (G.long_ecpY x0 x0gt1), ecpNFace, G.face_node_ecpY x0,
    ite_eq_right, ite_eq_right]
  · rw [G.edge_node_ecpY x0, G.node_ecpY x0]; simp
  · rw [G.edge_face_edge_ecpY x0 x0gt1, G.node_ecpY x0]; simp

/-- math-comp `cface_ecpH`. -/
theorem cface_ecpH (x0gt1 : G.ProperCpring x0) (u : (G.ecpH x0).D) :
    (G.ecpH x0).pointee.cface (G.ecpH x0).pointer u ↔
      u ∈ [(G.ecpH x0).pointer, (G.ecpH x0).pointee.face (G.ecpH x0).pointer,
        (G.ecpH x0).pointee.face ((G.ecpH x0).pointee.face (G.ecpH x0).pointer)] := by
  have hc : fcycle (G.ecpH x0).pointee.face
      [(G.ecpH x0).pointer, (G.ecpH x0).pointee.face (G.ecpH x0).pointer,
        (G.ecpH x0).pointee.face ((G.ecpH x0).pointee.face (G.ecpH x0).pointer)] :=
    ⟨rfl, rfl, G.face_face_face_ecpH x0 x0gt1, trivial⟩
  exact fconnect_cycle hc List.mem_cons_self

/-- math-comp `adj_ecpH`. -/
theorem adj_ecpH (x0gt1 : G.ProperCpring x0) (u : (G.ecpH x0).D) :
    (G.ecpH x0).pointee.adj (G.ecpH x0).pointer u ↔
      u ∈ (G.ecpH x0).pointee.fband ([G.node x0, x0, G.face (G.edge x0)].map (G.icpH x0)) := by
  set M := (G.ecpH x0).pointee with hM
  set Y := (G.ecpY x0).pointee with hY
  rw [M.adjF1]
  obtain ⟨v, hv⟩ := Y.fband_icpN (G.ecpY x0).pointer u
  rw [M.adjFr hv, (M.fbandF _).connect_iff hv]
  show M.adj (Y.icpN _ (G.ecpY x0).pointer) (Y.icpN _ v) ↔ _
  rw [Y.adj_icpN, G.edge_face_edge_ecpY x0 x0gt1]
  have hn : ¬ Y.cface (G.icpY x0 (G.edge x0)) (G.ecpY x0).pointer := by
    intro h
    have := (G.cface_ecpY x0 _).1 (Y.cfaceC.1 h)
    rw [face_ecpY] at this
    simp at this
  have hfe : Y.cface (G.icpY x0 (G.edge x0)) v ↔ Y.cface v (G.icpY x0 (G.face (G.edge x0))) := by
    rw [Y.cfaceC]
    exact Y.cface_sym.same_r ((G.cface_icpY x0 _ _).2 (fconnect1 _ _)) v
  have key : ∀ w, M.cface (Y.icpN (G.ecpY x0).pointer v) (G.icpH x0 w) ↔ Y.cface v (G.icpY x0 w) :=
    fun w => Y.cface_icpN _ _ _
  change Y.adj (G.ecpY x0).pointer v ∨
      (Y.cface (G.icpY x0 (G.edge x0)) (G.ecpY x0).pointer ∧ Y.cface (G.ecpY x0).pointer v) ∨
      (Y.cface (G.icpY x0 (G.edge x0)) v ∧ Y.cface (G.ecpY x0).pointer (G.ecpY x0).pointer) ↔ _
  rw [G.adj_ecpY x0 x0gt1, hfe]
  simp only [hn, false_and, false_or, connect_refl, and_true, Hypermap.mem_fband,
    List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, key]
  tauto

/-- math-comp `fband_icpH`. -/
theorem fband_icpH (u : (G.ecpH x0).D) :
    (∃ x, (G.ecpH x0).pointee.cface u (G.icpH x0 x)) ∨
      (G.ecpH x0).pointee.cface (G.ecpH x0).pointer u := by
  set M := (G.ecpH x0).pointee
  obtain ⟨v, hv⟩ := (G.ecpY x0).pointee.fband_icpN _ u
  rcases G.fband_icpY x0 v with ⟨x, hx⟩ | hX
  · exact Or.inl ⟨x, connect_trans hv (((G.ecpY x0).pointee.cface_icpN _ _ _).2 hx)⟩
  · right
    have h1 : M.cface (G.ecpH x0).pointer (Icp (G.ecpY x0).pointer) := fconnect1 _ _
    exact connect_trans h1 (connect_trans (((G.ecpY x0).pointee.cface_icpN _ _ _).2 hX)
      (M.cfaceC.1 hv))

/-- math-comp `bridgeless_ecpH`. -/
theorem bridgeless_ecpH (bridge'G : G.Bridgeless) (x0gt1 : G.ProperCpring x0) :
    (G.ecpH x0).pointee.Bridgeless := by
  apply (G.ecpY x0).pointee.bridgeless_ecpN_of (G.bridgeless_ecpY x0 bridge'G)
  have := G.cface_ecpH x0 x0gt1
  simp only [ecpH] at this
  rw [this, G.face_face_ecpH x0 x0gt1]
  show IcpXe ∉ [IcpX, Icp IcpX, Icp (Icp IcpX)]
  simp

end CompExtConfig

end Hypermap

end FourColor
