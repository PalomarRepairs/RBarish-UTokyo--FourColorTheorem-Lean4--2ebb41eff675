/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfMap.ExtA

/-!
# The two basic extension constructions (port of `cfmap.v`, section `ExtConfig`, part 2)

Given a reference dart `x0` in a hypermap `G`:

* `EcpDart D`  : the darts of `G` plus two new darts `IcpX` and `IcpXe` (math-comp `ecp_dart`);
  the two basic extension constructions both add an edge pair `{IcpX, IcpXe}`, so they share
  this underlying dart type.
* `G.ecpU x0`  : a pointed map that implements a `U` step at `x0` (math-comp `ecpU`): it adds a
  new face, with no junctions (a U-shaped loop).
* `G.ecpN x0`  : a pointed map that implements an `N` step at `x0` (math-comp `ecpN`): the `N`
  step is a `K` step applied immediately to the left of the ring head.
* `G.icpU x0`, `G.icpN x0` : the injections of `G` into these maps.

The `K` step is obtained below by composition with `R` steps, and the `H` and `Y` steps by
composition with a `U` step (see `FourColor/CfMap/CompExt.lean`).

math-comp's `fun_adjunction h f f' a` (for `f = f' = face`) is stated as the conjunction of its
two fields `rel_unit` and `rel_functor`; math-comp's `sumor` results `fband_icpU`, ... are stated
as disjunctions.
-/

namespace FourColor

open Function CfMap

universe u

namespace CfMap

variable {α β : Type*}

/-- Paths along an injection, with possibly different start points: if `e` links `a` to the
image of `y` iff `e'` links `b` to `y`, and `e` and `e'` agree along the image of `L.dropLast`,
then the `e`-paths from `a` along `L.map h` are the `e'`-paths from `b` along `L` (a variant of
math-comp `map_path`). -/
theorem path_map_congr {h : β → α} {e : α → α → Prop} {e' : β → β → Prop}
    {a : α} {b : β} {L : List β} (h0 : ∀ y, e a (h y) ↔ e' b y)
    (hl : ∀ z ∈ L.dropLast, ∀ y, e (h z) (h y) ↔ e' z y) :
    path e a (L.map h) ↔ path e' b L := by
  induction L generalizing a b with
  | nil => simp
  | cons y L ih =>
    cases L with
    | nil => simp [h0 y]
    | cons y' L =>
      simp only [List.dropLast_cons_cons, List.mem_cons, forall_eq_or_imp] at hl
      simp only [List.map_cons, path_cons] at ih ⊢
      rw [h0 y, ← ih hl.1 hl.2]

/-- Transport of `connect` along a map that sends links to paths. -/
theorem connect_map {e : α → α → Prop} {e' : β → β → Prop} (f : α → β)
    (h : ∀ a b, e a b → connect e' (f a) (f b)) {x y : α} (hxy : connect e x y) :
    connect e' (f x) (f y) := by
  induction hxy with
  | refl => exact connect_refl _
  | tail _ hbc ih => exact connect_trans ih (h _ _ hbc)

/-- A relation all of whose points are connected to a single point has a single component. -/
theorem nComp_univ_eq_one {e : α → α → Prop} (hs : ConnectSym e) (z : α)
    (h : ∀ u, connect e z u) : nComp e Set.univ = 1 := by
  have : (Set.univ : Set α) = comp e z := Set.ext fun u => ⟨fun _ => h u, fun _ => trivial⟩
  rw [this, nComp_comp hs]

/-- Two sets that are connected to each other have the same number of components (a form of
math-comp `adjunction_n_comp`, for the `rel_unit` part). -/
theorem nComp_eq_of_connect {e : α → α → Prop} (hs : ConnectSym e) {A B : Set α}
    (h1 : ∀ x ∈ A, ∃ y ∈ B, connect e x y) (h2 : ∀ y ∈ B, ∃ x ∈ A, connect e y x) :
    nComp e A = nComp e B := by
  unfold nComp
  congr 1
  ext c
  simp only [Set.mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := h1 x hx
    exact ⟨y, hy, ((comp_eq_iff hs).2 hxy).symm⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, hx, hyx⟩ := h2 y hy
    exact ⟨x, hx, ((comp_eq_iff hs).2 hyx).symm⟩

end CfMap

/-! ### The extended dart type -/

/-- math-comp `ecp_dart A`: the darts of `A` plus two new darts `IcpX` and `IcpXe`. We use a
special purpose concrete type, rather than the general sum, so that case analysis is better
behaved. -/
inductive EcpDart (A : Type u) : Type u
  /-- The new dart `X`, the reference dart of the extended map. -/
  | IcpX : EcpDart A
  /-- The new dart `Xe = edge X`. -/
  | IcpXe : EcpDart A
  /-- The injection of the old darts. -/
  | Icp : A → EcpDart A
  deriving DecidableEq

namespace EcpDart

variable {A : Type u}

/-- math-comp `ecp_inj`. -/
theorem ecp_inj : Injective (@Icp A) := fun _ _ h => Icp.inj h

/-- math-comp `ecp_encode`. -/
def ecpEncode : EcpDart A → Option (Option A)
  | IcpX => none
  | IcpXe => some none
  | Icp x => some (some x)

/-- math-comp `ecp_decode`. -/
def ecpDecode : Option (Option A) → EcpDart A
  | none => IcpX
  | some none => IcpXe
  | some (some x) => Icp x

/-- math-comp `ecp_cancel`. -/
theorem ecp_cancel : LeftInverse (@ecpDecode A) ecpEncode := by
  intro u; cases u <;> rfl

/-- The encoding of `EcpDart A` as `Option (Option A)` (math-comp's `can_type ecp_cancel`). -/
def ecpEquiv : EcpDart A ≃ Option (Option A) where
  toFun := ecpEncode
  invFun := ecpDecode
  left_inv := ecp_cancel
  right_inv := by rintro (_ | _ | _) <;> rfl

/-- math-comp's `finType` structure on `ecp_dart` (`CanIsFinite ecp_cancel`); the `eqType`
structure (math-comp `ecp_eq`, `ecp_eqP`) is the derived `DecidableEq` instance. -/
instance [Fintype A] : Fintype (EcpDart A) := Fintype.ofEquiv _ ecpEquiv.symm

/-- math-comp `card_ecp`. -/
theorem card_ecp [Fintype A] : Fintype.card (EcpDart A) = Fintype.card A + 2 := by
  rw [Fintype.card_congr ecpEquiv, Fintype.card_option, Fintype.card_option]

end EcpDart

open EcpDart

namespace Hypermap

variable {D : Type u} [Fintype D] [DecidableEq D] (G : Hypermap D)

/-! ### The `U` and `N` steps -/

section EcpUN

variable (x0 : D)

omit [DecidableEq D] in
/-- `node y = x0` iff `y = face (edge x0)`. -/
private theorem node_eq_iff' (y : D) : G.node y = x0 ↔ y = G.face (G.edge x0) := by
  rw [eq_comm, G.eq_node_iff, eq_comm]

/-- math-comp `ecp_edge`: the edge permutation shared by `ecpU` and `ecpN`. -/
def ecpEdge : EcpDart D → EcpDart D
  | IcpX => IcpXe
  | IcpXe => IcpX
  | Icp x => Icp (G.edge x)

/-- math-comp `ecpU_node`. -/
def ecpUNode : EcpDart D → EcpDart D
  | IcpX => IcpXe
  | IcpXe => Icp (G.node (G.node x0))
  | Icp y => if y = G.node x0 then IcpX else Icp (G.node y)

/-- math-comp `ecpU_face`. -/
def ecpUFace : EcpDart D → EcpDart D
  | IcpX => IcpX
  | IcpXe => Icp (G.node x0)
  | Icp y => if G.face y = G.node x0 then IcpXe else Icp (G.face y)

omit [Fintype D] in
/-- math-comp `ecpU_subproof`. -/
theorem ecpU_subproof (u : EcpDart D) : G.ecpUNode x0 (G.ecpUFace x0 (G.ecpEdge u)) = u := by
  cases u with
  | IcpX => simp [ecpEdge, ecpUFace, ecpUNode]
  | IcpXe => rfl
  | Icp x =>
    simp only [ecpEdge, ecpUFace]
    by_cases h : G.face (G.edge x) = G.node x0
    · rw [ite_eq_left h, ecpUNode, ← h, G.edgeK]
    · rw [ite_eq_right h, ecpUNode, ite_eq_right h, G.edgeK]

/-- math-comp `ecpU_map`. -/
def ecpUMap : Hypermap (EcpDart D) := ⟨G.ecpEdge, G.ecpUNode x0, G.ecpUFace x0, G.ecpU_subproof x0⟩

/-- math-comp `ecpU x0`: the pointed map that implements a `U` step at `x0`. -/
abbrev ecpU : PointedMap := ⟨EcpDart D, G.ecpUMap x0, IcpX⟩

/-- math-comp `icpU`: the injection of `G` into `ecpU x0`. -/
abbrev icpU (x : D) : (G.ecpU x0).D := Icp x

omit [Fintype D] in
/-- The edge permutation of `ecpU x0` (math-comp `ecp_edge`). -/
@[simp] theorem ecpUMap_edge (u : EcpDart D) : (G.ecpUMap x0).edge u = G.ecpEdge u := rfl
omit [Fintype D] in
/-- The node permutation of `ecpU x0` (math-comp `ecpU_node`). -/
@[simp] theorem ecpUMap_node (u : EcpDart D) : (G.ecpUMap x0).node u = G.ecpUNode x0 u := rfl
omit [Fintype D] in
/-- The face permutation of `ecpU x0` (math-comp `ecpU_face`). -/
@[simp] theorem ecpUMap_face (u : EcpDart D) : (G.ecpUMap x0).face u = G.ecpUFace x0 u := rfl

/-- math-comp `icpU_inj`. -/
theorem icpU_inj : Injective (G.icpU x0) := ecp_inj

/-- math-comp `icpU_edge`. -/
theorem icpU_edge (x : D) : G.icpU x0 (G.edge x) = (G.ecpU x0).pointee.edge (G.icpU x0 x) := rfl

/-- math-comp `ecpN_node`. -/
def ecpNNode : EcpDart D → EcpDart D
  | IcpX => if G.LongCpring x0 then Icp (G.node x0) else IcpX
  | IcpXe => Icp (G.face (G.edge x0))
  | Icp y => if y = x0 then IcpXe else if G.node (G.node y) = x0 then IcpX else Icp (G.node y)

/-- math-comp `ecpN_face`. -/
def ecpNFace : EcpDart D → EcpDart D
  | IcpX => Icp x0
  | IcpXe => if G.LongCpring x0 then Icp (G.face (G.edge (G.face (G.edge x0)))) else IcpX
  | Icp y =>
    if y = G.edge (G.face (G.edge x0)) then IcpXe
    else if y = G.edge (G.node x0) then IcpX else Icp (G.face y)

/-- math-comp `ecpN_subproof`. -/
theorem ecpN_subproof (u : EcpDart D) : G.ecpNNode x0 (G.ecpNFace x0 (G.ecpEdge u)) = u := by
  cases u with
  | IcpX =>
    simp only [ecpEdge, ecpNFace]
    by_cases hl : G.LongCpring x0
    · rw [ite_eq_left hl, ecpNNode]
      have h1 : G.face (G.edge (G.face (G.edge x0))) ≠ x0 := by
        intro h
        apply hl
        have := congrArg G.node h
        rw [G.edgeK] at this
        exact this
      rw [ite_eq_right h1, G.edgeK, G.edgeK, ite_eq_left rfl]
    · rw [ite_eq_right hl, ecpNNode, ite_eq_right hl]
  | IcpXe => simp [ecpEdge, ecpNFace, ecpNNode]
  | Icp x =>
    simp only [ecpEdge, ecpNFace]
    by_cases h1 : G.edge x = G.edge (G.face (G.edge x0))
    · rw [ite_eq_left h1, ecpNNode, G.edgeI h1]
    · rw [ite_eq_right h1]
      have h1' : x ≠ G.face (G.edge x0) := fun h => h1 (by rw [h])
      by_cases h2 : G.edge x = G.edge (G.node x0)
      · rw [ite_eq_left h2, ecpNNode, G.edgeI h2]
        have hl : G.LongCpring x0 := fun h => h1' (by rw [G.edgeI h2, h])
        rw [ite_eq_left hl]
      · rw [ite_eq_right h2, ecpNNode, G.edgeK]
        have h2' : x ≠ G.node x0 := fun h => h2 (by rw [h])
        have h3 : G.face (G.edge x) ≠ x0 := by
          intro h
          apply h2'
          rw [← G.edgeK x, h]
        rw [ite_eq_right h3, ite_eq_right (fun h => h1' ((node_eq_iff' G x0 x).1 h))]

/-- math-comp `ecpN_map`. -/
def ecpNMap : Hypermap (EcpDart D) := ⟨G.ecpEdge, G.ecpNNode x0, G.ecpNFace x0, G.ecpN_subproof x0⟩

/-- math-comp `ecpN x0`: the pointed map that implements an `N` step at `x0`. -/
abbrev ecpN : PointedMap := ⟨EcpDart D, G.ecpNMap x0, IcpX⟩

/-- math-comp `icpN`: the injection of `G` into `ecpN x0`. -/
abbrev icpN (x : D) : (G.ecpN x0).D := Icp x

/-- The edge permutation of `ecpN x0` (math-comp `ecp_edge`). -/
@[simp] theorem ecpNMap_edge (u : EcpDart D) : (G.ecpNMap x0).edge u = G.ecpEdge u := rfl
/-- The node permutation of `ecpN x0` (math-comp `ecpN_node`). -/
@[simp] theorem ecpNMap_node (u : EcpDart D) : (G.ecpNMap x0).node u = G.ecpNNode x0 u := rfl
/-- The face permutation of `ecpN x0` (math-comp `ecpN_face`). -/
@[simp] theorem ecpNMap_face (u : EcpDart D) : (G.ecpNMap x0).face u = G.ecpNFace x0 u := rfl

/-- math-comp `icpN_inj`. -/
theorem icpN_inj : Injective (G.icpN x0) := ecp_inj

/-- math-comp `icpN_edge`. -/
theorem icpN_edge (x : D) : G.icpN x0 (G.edge x) = (G.ecpN x0).pointee.edge (G.icpN x0 x) := rfl

omit [DecidableEq D] in
/-- A map with the `ecp_edge` edge permutation of a plain map is plain. -/
theorem plain_of_ecpEdge [DecidableEq D] {H : Hypermap (EcpDart D)} (hE : ∀ u, H.edge u = G.ecpEdge u)
    (plainG : G.Plain) : H.Plain := by
  unfold Plain
  rw [plainP]
  rintro (_ | _ | x) -
  · simp [hE, ecpEdge]
  · simp [hE, ecpEdge]
  · simp only [hE, ecpEdge, ne_eq, Icp.injEq]
    exact ⟨G.plain_eq plainG x, G.plain_neq plainG x⟩

/-- math-comp `plain_ecpU`. -/
theorem plain_ecpU (plainG : G.Plain) : (G.ecpU x0).pointee.Plain :=
  G.plain_of_ecpEdge (fun _ => rfl) plainG

/-- math-comp `plain_ecpN`. -/
theorem plain_ecpN (plainG : G.Plain) : (G.ecpN x0).pointee.Plain :=
  G.plain_of_ecpEdge (fun _ => rfl) plainG

/-- math-comp `baseN_ecpU`: `node` is unchanged outside `node x0`. -/
theorem baseN_ecpU (x y : D) (hx : G.icpU x0 x ≠ Icp (G.node x0)) :
    (G.ecpU x0).pointee.node (G.icpU x0 x) = G.icpU x0 y ↔ G.node x = y := by
  have hx' : x ≠ G.node x0 := fun h => hx (by rw [h])
  show G.ecpUNode x0 (Icp x) = Icp y ↔ _
  rw [ecpUNode, ite_eq_right hx', Icp.injEq]

/-- math-comp `icpU_node`. -/
theorem icpU_node (x : D) (hx : x ∉ [G.node x0]) :
    G.icpU x0 (G.node x) = (G.ecpU x0).pointee.node (G.icpU x0 x) := by
  have hx' : x ≠ G.node x0 := fun h => hx (by simp [h])
  show Icp (G.node x) = G.ecpUNode x0 (Icp x)
  rw [ecpUNode, ite_eq_right hx']

/-- math-comp `cpring_ecpU`. -/
theorem cpring_ecpU :
    (G.ecpU x0).pointee.cpring (G.ecpU x0).pointer =
      (G.ecpU x0).pointee.node (G.ecpU x0).pointer :: (G.ecpU x0).pointer ::
        (G.cpring x0).map (G.icpU x0) := by
  apply (G.ecpU x0).pointee.cpring_def
  · rfl
  have ht := G.head_cpring x0
  generalize (G.cpring x0).tail = t at ht
  have hnd := G.cpring_uniq x0
  have hcyc := G.cycle_rev_cpring x0
  rw [ht] at hnd hcyc
  have hnt : G.node x0 ∉ t := (List.nodup_cons.1 hnd).1
  show UCycle (frel (G.ecpUMap x0).node) (IcpXe :: IcpX :: (G.cpring x0).map Icp).reverse
  rw [ht]
  refine ⟨?_, ?_⟩
  · have hrev : ((IcpXe :: IcpX :: (G.node x0 :: t).map Icp).reverse : List (EcpDart D)) =
        ((t.reverse ++ [G.node x0]).map Icp) ++ [IcpX, IcpXe] := by simp
    rw [hrev, cycle_iff_path IcpXe, last_append, last_cons, last_cons, last_nil, path_append]
    have hG : path (frel G.node) (G.node x0) (t.reverse ++ [G.node x0]) := by
      have := (cycle_iff_path x0 _).1 hcyc
      rwa [List.reverse_cons, last_concat] at this
    have h1 := (path_map_congr (h := Icp) (e := frel (G.ecpUMap x0).node) (e' := frel G.node)
      (a := IcpXe) (b := G.node x0) (L := t.reverse ++ [G.node x0])
      (fun y => by
        show G.ecpUNode x0 IcpXe = Icp y ↔ G.node (G.node x0) = y
        simp [ecpUNode])
      (fun z hz y => by
        rw [List.dropLast_concat, List.mem_reverse] at hz
        have hz' : z ≠ G.node x0 := fun h => hnt (h ▸ hz)
        show G.ecpUNode x0 (Icp z) = Icp y ↔ G.node z = y
        simp [ecpUNode, hz'])).2 hG
    refine ⟨h1, ?_⟩
    rw [List.map_append, List.map_singleton, last_concat]
    show G.ecpUNode x0 (Icp (G.node x0)) = IcpX ∧ G.ecpUNode x0 IcpX = IcpXe ∧ True
    simp [ecpUNode]
  · rw [List.nodup_reverse, List.nodup_cons, List.nodup_cons]
    exact ⟨by simp, by simp, hnd.map ecp_inj⟩

/-- math-comp `size_cpring_ecpU`. -/
theorem size_cpring_ecpU :
    ((G.ecpU x0).pointee.cpring (G.ecpU x0).pointer).length = (G.cpring x0).length + 2 := by
  rw [cpring_ecpU]
  simp

/-- math-comp `cubic_ecpU`. -/
theorem cubic_ecpU (cubicG : G.Quasicubic (G.cpring x0).reverse) :
    (G.ecpU x0).pointee.Quasicubic
      ((G.ecpU x0).pointee.cpring (G.ecpU x0).pointer).reverse := by
  rw [cpring_ecpU]
  unfold Quasicubic
  rw [cubicP]
  intro u hu
  simp only [Set.mem_ofPred_eq, List.mem_reverse, List.mem_cons, List.mem_map, not_or] at hu
  obtain ⟨h1, h2, h3⟩ := hu
  cases u with
  | IcpX => exact absurd rfl h2
  | IcpXe => exact absurd rfl h1
  | Icp x =>
    have hx : x ∉ G.cpring x0 := fun h => h3 ⟨x, h, rfl⟩
    obtain ⟨hn3, hn1⟩ := (G.cubicP).1 cubicG x (by simpa using hx)
    have hxc : ¬ G.cnode x0 x := fun h => hx ((G.mem_cpring x0).2 h)
    have e1 : x ≠ G.node x0 := fun h => hxc (h ▸ fconnect1 _ _)
    have e2 : G.node x ≠ G.node x0 := fun h => hxc (G.nodeI h ▸ connect_refl _)
    have e3 : G.node (G.node x) ≠ G.node x0 := fun h =>
      hxc (G.cnodeC.1 (connect_of_rel (G.nodeI h)))
    show G.ecpUNode x0 (G.ecpUNode x0 (G.ecpUNode x0 (Icp x))) = Icp x ∧ G.ecpUNode x0 (Icp x) ≠ Icp x
    simp only [ecpUNode, ite_eq_right e1, ite_eq_right e2, ite_eq_right e3, hn3, ne_eq, Icp.injEq]
    exact ⟨trivial, hn1⟩

/-- math-comp `baseN_ecpN`: `node` is unchanged outside `x0` and
`face (edge (face (edge x0)))`. -/
theorem baseN_ecpN (x y : D)
    (hx : ¬ (G.icpN x0 x = Icp x0 ∨ G.icpN x0 x = Icp (G.face (G.edge (G.face (G.edge x0)))))) :
    (G.ecpN x0).pointee.node (G.icpN x0 x) = G.icpN x0 y ↔ G.node x = y := by
  have hx' : ¬ (x = x0 ∨ x = G.face (G.edge (G.face (G.edge x0)))) := by
    rintro (h | h) <;> exact hx (by simp [h])
  rw [not_or] at hx'
  have h2 : G.node (G.node x) ≠ x0 := by
    intro h
    apply hx'.2
    rw [← node_eq_iff', ← node_eq_iff', h]
  show G.ecpNNode x0 (Icp x) = Icp y ↔ _
  rw [ecpNNode, ite_eq_right hx'.1, ite_eq_right h2, Icp.injEq]

/-- math-comp `cpring_ecpN`. -/
theorem cpring_ecpN :
    (G.ecpN x0).pointee.cpring (G.ecpN x0).pointer =
      if G.LongCpring x0 then
        G.icpN x0 (G.node x0) :: (G.ecpN x0).pointer :: ((G.cpring x0).drop 3).map (G.icpN x0)
      else [(G.ecpN x0).pointer] := by
  by_cases hl : G.LongCpring x0
  · rw [ite_eq_left hl]
    apply (G.ecpN x0).pointee.cpring_def
    · show some (Icp (G.node x0)) = some (G.ecpNNode x0 IcpX)
      rw [ecpNNode, ite_eq_left hl]
    have hc := G.head_long_cpring x0 hl
    have hnd := G.cpring_uniq x0
    have hcyc := G.cycle_rev_cpring x0
    show UCycle (frel (G.ecpNMap x0).node)
      (Icp (G.node x0) :: IcpX :: ((G.cpring x0).drop 3).map Icp).reverse
    generalize (G.cpring x0).drop 3 = r at hc ⊢
    rw [hc] at hnd hcyc
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
    obtain ⟨⟨hn1, -, hn3⟩, ⟨-, hx2⟩, -, hr⟩ := hnd
    refine ⟨?_, ?_⟩
    · have hrev : ((Icp (G.node x0) :: IcpX :: r.map Icp).reverse : List (EcpDart D)) =
          r.reverse.map Icp ++ [IcpX, Icp (G.node x0)] := by simp
      rw [hrev, cycle_iff_path (Icp (G.node x0)), last_append, last_cons, last_cons, last_nil,
        path_append]
      have hG : path (frel G.node) (G.node x0)
          (r.reverse ++ [G.face (G.edge x0), x0, G.node x0]) := by
        have h1 : cycle (frel G.node) (r.reverse ++ [G.face (G.edge x0), x0, G.node x0]) := by
          simpa using hcyc
        rw [cycle_iff_path x0, last_append, last_cons, last_cons, last_cons, last_nil] at h1
        exact h1
      rw [path_append] at hG
      obtain ⟨hG1, hG2⟩ := hG
      have hnp : (G.node x0 :: r.reverse).Nodup :=
        List.nodup_cons.2 ⟨by simpa using hn3, List.nodup_reverse.2 hr⟩
      have hx0p : x0 ∉ G.node x0 :: r.reverse := by
        simp only [List.mem_cons, List.mem_reverse, not_or]
        exact ⟨Ne.symm hn1, hx2⟩
      have hzf : last (G.node x0) r.reverse = G.face (G.edge (G.face (G.edge x0))) :=
        (node_eq_iff' G (G.face (G.edge x0)) _).1 hG2.1
      refine ⟨?_, ?_⟩
      · refine (path_map_base (h := Icp) (e := frel (G.ecpNMap x0).node) (e' := frel G.node)
          (b := fun u => u = Icp x0 ∨ u = Icp (G.face (G.edge (G.face (G.edge x0)))))
          (fun x y hx => G.baseN_ecpN x0 x y hx) ?_).2 hG1
        intro y hy hb
        simp only [Icp.injEq] at hb
        rcases hb with rfl | rfl
        · exact hx0p (mem_belast hy)
        · exact last_not_mem_belast hnp (hzf ▸ hy)
      · rw [last_map Icp, hzf]
        show G.ecpNNode x0 (Icp (G.face (G.edge (G.face (G.edge x0))))) = IcpX ∧
          G.ecpNNode x0 IcpX = Icp (G.node x0) ∧ True
        have hz0 : G.face (G.edge (G.face (G.edge x0))) ≠ x0 := by
          rw [← hzf]
          intro h
          have := mem_last (G.node x0) r.reverse
          rw [h] at this
          exact hx0p this
        refine ⟨?_, ?_, trivial⟩
        · simp [ecpNNode, hz0, G.edgeK]
        · rw [ecpNNode, ite_eq_left hl]
    · rw [List.nodup_reverse, List.nodup_cons, List.nodup_cons]
      refine ⟨?_, by simp, hr.map ecp_inj⟩
      simp only [List.mem_cons, reduceCtorEq, List.mem_map, Icp.injEq, false_or, not_exists,
        not_and]
      exact fun y hy h => hn3 (h ▸ hy)
  · rw [ite_eq_right hl]
    apply (G.ecpN x0).pointee.cpring_def
    · show some IcpX = some (G.ecpNNode x0 IcpX)
      rw [ecpNNode, ite_eq_right hl]
    · refine ⟨?_, List.nodup_singleton _⟩
      show G.ecpNNode x0 IcpX = IcpX ∧ True
      rw [ecpNNode, ite_eq_right hl]
      exact ⟨rfl, trivial⟩

/-- math-comp `rot1_cpring_ecpN`. -/
theorem rot1_cpring_ecpN :
    rot 1 ((G.ecpN x0).pointee.cpring (G.ecpN x0).pointer) =
      (G.ecpN x0).pointer :: ((rot 1 (G.cpring x0)).drop 2).map (G.icpN x0) := by
  rw [cpring_ecpN]
  split_ifs with hl
  · have hc := G.head_long_cpring x0 hl
    generalize (G.cpring x0).drop 3 = r at hc ⊢
    rw [hc]
    simp [rot_one_cons]
  · have hle : (G.cpring x0).length ≤ 2 := not_lt.1 ((G.size_long_cpring x0).not.1 hl)
    have : (rot 1 (G.cpring x0)).drop 2 = [] := List.drop_eq_nil_of_le (by simpa using hle)
    rw [this]
    simp [rot]

/-- math-comp `size_cpring_ecpN`. -/
theorem size_cpring_ecpN :
    ((G.ecpN x0).pointee.cpring (G.ecpN x0).pointer).length = (G.cpring x0).length - 2 + 1 := by
  have := congrArg List.length (G.rot1_cpring_ecpN x0)
  rw [length_rot] at this
  rw [this]
  simp

/-- math-comp `cubic_ecpN`. -/
theorem cubic_ecpN (cubicG : G.Quasicubic (G.cpring x0).reverse) (x0gt1 : G.ProperCpring x0) :
    (G.ecpN x0).pointee.Quasicubic
      ((G.ecpN x0).pointee.cpring (G.ecpN x0).pointer).reverse := by
  unfold Quasicubic
  rw [cubicP]
  intro u hu
  simp only [Set.mem_ofPred_eq, List.mem_reverse] at hu
  rw [← mem_rot (n := 1), rot1_cpring_ecpN] at hu
  simp only [List.mem_cons, List.mem_map, not_or] at hu
  obtain ⟨hu1, hu2⟩ := hu
  have hfx0 : G.face (G.edge x0) ≠ x0 := by
    intro h
    apply x0gt1
    have := G.edgeK x0
    rw [h] at this
    exact this.symm
  -- the new cubic node `[edge X, face (edge x0), x0]`
  have n1 : G.ecpNNode x0 IcpXe = Icp (G.face (G.edge x0)) := rfl
  have n2 : G.ecpNNode x0 (Icp (G.face (G.edge x0))) = Icp x0 := by
    rw [ecpNNode, ite_eq_right hfx0, G.edgeK, ite_eq_right (Ne.symm x0gt1)]
  have n3 : G.ecpNNode x0 (Icp x0) = IcpXe := by rw [ecpNNode, ite_eq_left rfl]
  -- off the ring, `node` is unchanged
  have hoff : ∀ y, ¬ G.cnode x0 y → G.ecpNNode x0 (Icp y) = Icp (G.node y) := by
    intro y hy
    have h1 : y ≠ x0 := fun h => hy (h ▸ connect_refl _)
    have h2 : G.node (G.node y) ≠ x0 := fun h =>
      hy (G.cnodeC.1 (h ▸ fconnect_iterate G.node y 2))
    rw [ecpNNode, ite_eq_right h1, ite_eq_right h2]
  have hoff1 : ∀ y, ¬ G.cnode x0 y → ¬ G.cnode x0 (G.node y) :=
    fun y hy h => hy ((G.cnode1r x0 y).2 h)
  show G.ecpNNode x0 (G.ecpNNode x0 (G.ecpNNode x0 u)) = u ∧ G.ecpNNode x0 u ≠ u
  cases u with
  | IcpX => exact absurd rfl hu1
  | IcpXe => rw [n1, n2, n3]; exact ⟨rfl, by simp⟩
  | Icp x =>
    by_cases hx1 : x = G.face (G.edge x0)
    · rw [hx1, n2, n3, n1]; exact ⟨rfl, fun h => hfx0 (Icp.inj h).symm⟩
    by_cases hx2 : x = x0
    · rw [hx2, n3, n1, n2]; exact ⟨rfl, by simp⟩
    -- `x` is not on the ring of `G`
    have hxc : ¬ G.cnode x0 x := by
      intro h
      have hx := (G.mem_cpring x0).2 h
      by_cases hl : G.LongCpring x0
      · have hc := G.head_long_cpring x0 hl
        generalize (G.cpring x0).drop 3 = r at hc
        have h' : ((rot 1 (G.cpring x0)).drop 2) = r ++ [G.node x0] := by
          rw [hc]; simp [rot_one_cons]
        rw [hc] at hx
        rw [h'] at hu2
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx hu2
        rcases hx with h1 | h1 | h1 | h1
        · exact hu2 ⟨x, Or.inr h1, rfl⟩
        · exact hx2 h1
        · exact hx1 h1
        · exact hu2 ⟨x, Or.inl h1, rfl⟩
      · have hfe : G.face (G.edge x0) = G.node x0 := not_not.1 hl
        rcases G.cpring_small x0 hl with ⟨-, hc⟩ | ⟨-, hc⟩ <;> rw [hc] at hx <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        · rcases hx with h1 | h1
          · exact hx1 (h1.trans hfe.symm)
          · exact hx2 h1
        · exact hx1 (hx.trans hfe.symm)
    obtain ⟨hn3, hn1⟩ := (G.cubicP).1 cubicG x (by simpa [G.mem_cpring] using hxc)
    rw [hoff x hxc, hoff _ (hoff1 x hxc), hoff _ (hoff1 _ (hoff1 x hxc)), hn3]
    exact ⟨rfl, by simpa using hn1⟩

/-- math-comp `connected_ecpU`. -/
theorem connected_ecpU (ccG : G.Connected) : (G.ecpU x0).pointee.Connected := by
  set M := (G.ecpU x0).pointee
  have hs := M.glinkC
  apply nComp_univ_eq_one hs IcpX
  have GXe : M.gcomp IcpX IcpXe := connect_of_rel (M.glinkE _)
  have Gnnx0 : M.gcomp IcpX (Icp (G.node (G.node x0))) :=
    connect_trans GXe (connect_of_rel (M.glinkN IcpXe))
  rintro (_ | _ | x)
  · exact connect_refl _
  · exact GXe
  · obtain ⟨p, hp, hl⟩ := G.connected_clink ccG x (G.node (G.node x0))
    induction p generalizing x with
    | nil => rw [show x = G.node (G.node x0) from hl]; exact Gnnx0
    | cons y p ih =>
      obtain ⟨hxy, hyp⟩ := hp
      have Gy := ih y hyp hl
      rcases hxy with hxy | hxy
      · by_cases hy : y = G.node x0
        · rw [hxy, hy]; exact Gnnx0
        · have h1 : M.node (Icp y) = Icp x := by
            show G.ecpUNode x0 (Icp y) = Icp x
            rw [ecpUNode, ite_eq_right hy, hxy]
          exact connect_trans Gy (connect_of_rel (h1 ▸ M.glinkN _))
      · by_cases hx : G.face x = G.node x0
        · have h1 : M.face (Icp x) = IcpXe := by
            show G.ecpUFace x0 (Icp x) = IcpXe
            rw [ecpUFace, ite_eq_left hx]
          exact connect_trans GXe (hs _ _ (connect_of_rel (h1 ▸ M.glinkF _)))
        · have h1 : M.face (Icp x) = Icp y := by
            show G.ecpUFace x0 (Icp x) = Icp y
            rw [ecpUFace, ite_eq_right hx, hxy]
          exact connect_trans Gy (hs _ _ (connect_of_rel (h1 ▸ M.glinkF _)))

/-- math-comp `connected_ecpN`. -/
theorem connected_ecpN (ccG : G.Connected) : (G.ecpN x0).pointee.Connected := by
  set M := (G.ecpN x0).pointee
  have hs := M.glinkC
  apply nComp_univ_eq_one hs IcpX
  have GXe : M.gcomp IcpX IcpXe := connect_of_rel (M.glinkE _)
  have Gx0 : M.gcomp IcpX (Icp x0) := connect_of_rel (M.glinkF _)
  have Gfex0 : M.gcomp IcpX (Icp (G.face (G.edge x0))) :=
    connect_trans GXe (connect_of_rel (M.glinkN IcpXe))
  have Gnx0 : M.gcomp IcpX (Icp (G.node x0)) := by
    by_cases hl : G.LongCpring x0
    · have h1 : M.node IcpX = Icp (G.node x0) := by
        show G.ecpNNode x0 IcpX = _
        rw [ecpNNode, ite_eq_left hl]
      exact connect_of_rel (h1 ▸ M.glinkN _)
    · rw [← not_not.1 hl]; exact Gfex0
  rintro (_ | _ | x)
  · exact connect_refl _
  · exact GXe
  · obtain ⟨p, hp, hl⟩ := G.connected_clink ccG x x0
    induction p generalizing x with
    | nil => rw [show x = x0 from hl]; exact Gx0
    | cons y p ih =>
      obtain ⟨hxy, hyp⟩ := hp
      have Gy := ih y hyp hl
      rcases hxy with hxy | hxy
      · by_cases hy : y = x0
        · rw [hxy, hy]; exact Gnx0
        · by_cases hy' : G.node (G.node y) = x0
          · rw [← hxy] at hy'
            rw [(node_eq_iff' G x0 x).1 hy']; exact Gfex0
          · have h1 : M.node (Icp y) = Icp x := by
              show G.ecpNNode x0 (Icp y) = Icp x
              rw [ecpNNode, ite_eq_right hy, ite_eq_right hy', hxy]
            exact connect_trans Gy (connect_of_rel (h1 ▸ M.glinkN _))
      · by_cases hx1 : x = G.edge (G.face (G.edge x0))
        · have h1 : M.face (Icp x) = IcpXe := by
            show G.ecpNFace x0 (Icp x) = IcpXe
            rw [ecpNFace, ite_eq_left hx1]
          exact connect_trans GXe (hs _ _ (connect_of_rel (h1 ▸ M.glinkF _)))
        · by_cases hx2 : x = G.edge (G.node x0)
          · have h1 : M.face (Icp x) = IcpX := by
              show G.ecpNFace x0 (Icp x) = IcpX
              rw [ecpNFace, ite_eq_right hx1, ite_eq_left hx2]
            exact hs _ _ (connect_of_rel (h1 ▸ M.glinkF _))
          · have h1 : M.face (Icp x) = Icp y := by
              show G.ecpNFace x0 (Icp x) = Icp y
              rw [ecpNFace, ite_eq_right hx1, ite_eq_right hx2, hxy]
            exact connect_trans Gy (hs _ _ (connect_of_rel (h1 ▸ M.glinkF _)))

/-- math-comp `cface_ecpU`: the new face of `ecpU x0` is the singleton `X`. -/
theorem cface_ecpU (u : (G.ecpU x0).D) :
    (G.ecpU x0).pointee.cface (G.ecpU x0).pointer u ↔ u = (G.ecpU x0).pointer := by
  have hc : fcycle (G.ecpU x0).pointee.face [IcpX] := ⟨rfl, trivial⟩
  exact (fconnect_cycle hc (List.mem_singleton_self _)).trans List.mem_singleton

/-- math-comp `closedF_ecpU`. -/
theorem closedF_ecpU :
    Closed (frel (G.ecpU x0).pointee.face) {u | u ≠ (G.ecpU x0).pointer} := by
  intro u v huv
  simp only [Set.mem_ofPred_eq, ne_eq]
  have h := (G.cface_ecpU x0 v).1
  constructor
  · intro hu hv
    apply hu
    have : (G.ecpU x0).pointee.face u = (G.ecpU x0).pointee.face IcpX := by rw [huv, hv]; rfl
    exact (G.ecpU x0).pointee.faceI this
  · intro hv hu
    apply hv
    subst hu
    exact h (connect_of_rel huv)

/-- math-comp `adjnF_ecpU`: the faces of `ecpU x0` other than `X` are those of `G` (math-comp's
`fun_adjunction icpU face face (predC1 ecpU)`, as its two fields `rel_unit` and
`rel_functor`). -/
theorem adjnF_ecpU :
    (∀ u, u ≠ (G.ecpU x0).pointer → ∃ x, (G.ecpU x0).pointee.cface u (G.icpU x0 x)) ∧
    ∀ x y, G.icpU x0 x ≠ (G.ecpU x0).pointer →
      (G.cface x y ↔ (G.ecpU x0).pointee.cface (G.icpU x0 x) (G.icpU x0 y)) := by
  set M := (G.ecpU x0).pointee
  refine ⟨?_, fun x y _ => ⟨fun hxy => ?_, fun hxy => ?_⟩⟩
  · rintro (_ | _ | x) hu
    · exact absurd rfl hu
    · exact ⟨G.node x0, connect_of_rel rfl⟩
    · exact ⟨x, connect_refl _⟩
  · refine connect_map (e := frel G.face) Icp (fun a b hab => ?_) hxy
    subst hab
    by_cases ha : G.face a = G.node x0
    · have h1 : M.face (Icp a) = IcpXe := by
        show G.ecpUFace x0 (Icp a) = IcpXe
        rw [ecpUFace, ite_eq_left ha]
      have h2 : M.face IcpXe = Icp (G.face a) := by
        show G.ecpUFace x0 IcpXe = _
        rw [ecpUFace, ha]
      exact connect_trans (connect_of_rel h1) (connect_of_rel h2)
    · exact connect_of_rel (show G.ecpUFace x0 (Icp a) = Icp (G.face a) by
        rw [ecpUFace, ite_eq_right ha])
  · let h : EcpDart D → D := fun v => match v with
      | IcpX => G.node x0
      | IcpXe => G.node x0
      | Icp z => z
    have key : ∀ v, connect (frel M.face) (Icp x) v → v ≠ IcpX ∧ G.cface x (h v) := by
      intro v hv
      induction hv with
      | refl => exact ⟨by simp, connect_refl _⟩
      | @tail b c _ hbc ih =>
        obtain ⟨hne, hc⟩ := ih
        subst hbc
        match b, hne, hc with
        | IcpXe, _, hc =>
          exact ⟨by simp [M, ecpUFace], hc⟩
        | Icp z, _, hc =>
          by_cases hz : G.face z = G.node x0
          · have h1 : M.face (Icp z) = IcpXe := by
              show G.ecpUFace x0 (Icp z) = IcpXe
              rw [ecpUFace, ite_eq_left hz]
            rw [h1]
            refine ⟨by simp, ?_⟩
            show G.cface x (G.node x0)
            rw [← hz]
            exact connect_trans hc (fconnect1 _ _)
          · have h1 : M.face (Icp z) = Icp (G.face z) := by
              show G.ecpUFace x0 (Icp z) = _
              rw [ecpUFace, ite_eq_right hz]
            rw [h1]
            exact ⟨by simp, connect_trans hc (fconnect1 _ _)⟩
    exact (key _ hxy).2

/-- math-comp `cface_icpU`. -/
theorem cface_icpU (x y : D) :
    (G.ecpU x0).pointee.cface (G.icpU x0 x) (G.icpU x0 y) ↔ G.cface x y :=
  ((G.adjnF_ecpU x0).2 x y (by simp)).symm

/-- math-comp `adj_ecpU`. -/
theorem adj_ecpU (u : (G.ecpU x0).D) :
    (G.ecpU x0).pointee.adj (G.ecpU x0).pointer u ↔
      u ∈ (G.ecpU x0).pointee.fband [G.icpU x0 (G.node x0)] := by
  set M := (G.ecpU x0).pointee
  rw [M.adjP, M.mem_fband]
  simp only [List.mem_singleton, exists_eq_left]
  constructor
  · rintro ⟨z, hz, hzu⟩
    rw [(G.cface_ecpU x0 z).1 hz] at hzu
    -- `rlink X u` is `cface Xe u`, and `face Xe = node x0`
    have := (M.cface1 _ _).1 hzu
    exact M.cfaceC.1 this
  · intro hu
    refine ⟨IcpX, connect_refl _, ?_⟩
    exact (M.cface1 IcpXe u).2 (M.cfaceC.1 hu)

/-- math-comp `adj_icpU`. -/
theorem adj_icpU (x y : D) :
    (G.ecpU x0).pointee.adj (G.icpU x0 x) (G.icpU x0 y) ↔ G.adj x y := by
  set M := (G.ecpU x0).pointee
  rw [M.adjP, G.adjP]
  constructor
  · rintro ⟨z, hxz, hzy⟩
    match z, hxz, hzy with
    | IcpX, hxz, _ =>
      have := (G.cface_ecpU x0 _).1 (M.cfaceC.1 hxz)
      exact absurd this (by simp)
    | IcpXe, _, hzy =>
      have := (G.cface_ecpU x0 _).1 hzy
      exact absurd this (by simp)
    | Icp z, hxz, hzy =>
      exact ⟨z, (G.cface_icpU x0 x z).1 hxz, (G.cface_icpU x0 _ y).1 hzy⟩
  · rintro ⟨z, hxz, hzy⟩
    exact ⟨Icp z, (G.cface_icpU x0 x z).2 hxz, (G.cface_icpU x0 _ y).2 hzy⟩

/-- math-comp `fband_icpU`. -/
theorem fband_icpU (u : (G.ecpU x0).D) :
    (∃ x, (G.ecpU x0).pointee.cface u (G.icpU x0 x)) ∨
      (G.ecpU x0).pointee.cface (G.ecpU x0).pointer u := by
  by_cases hu : u = IcpX
  · right; rw [hu]
  · left; exact (G.adjnF_ecpU x0).1 u hu

/-- math-comp `bridgeless_ecpU`. -/
theorem bridgeless_ecpU (bridge'G : G.Bridgeless) : (G.ecpU x0).pointee.Bridgeless := by
  set M := (G.ecpU x0).pointee
  rintro ⟨u, hu⟩
  match u, hu with
  | IcpX, hu =>
    have := (G.cface_ecpU x0 _).1 hu
    exact absurd this (by simp [M, ecpEdge])
  | IcpXe, hu =>
    have := (G.cface_ecpU x0 _).1 (M.cfaceC.1 hu)
    exact absurd this (by simp)
  | Icp x, hu =>
    exact G.bridgeless_cface bridge'G x ((G.cface_icpU x0 x (G.edge x)).1 hu)

/-- math-comp `planar_ecpU`. -/
theorem planar_ecpU (planarG : G.Planar) (plainG : G.Plain)
    (cubicG : G.Quasicubic (G.cpring x0).reverse) (ccG : G.Connected) :
    (G.ecpU x0).pointee.Planar := by
  set M := (G.ecpU x0).pointee
  have oFX : fcard M.face Set.univ = fcard G.face Set.univ + 1 := by
    show nComp (frel M.face) Set.univ = _
    rw [nComp_compl (G.closedF_ecpU x0)]
    have h1 : nComp (frel M.face) {u : EcpDart D | u ≠ IcpX}ᶜ = 1 := by
      have : {u : EcpDart D | u ≠ IcpX}ᶜ = comp (frel M.face) IcpX := by
        ext u
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_not, mem_comp]
        exact (G.cface_ecpU x0 u).symm
      rw [this, nComp_comp M.cface_sym]
    have h2 : nComp (frel M.face) {u : EcpDart D | u ≠ IcpX} =
        nComp (frel M.face) (Set.range Icp) := by
      apply nComp_eq_of_connect M.cface_sym
      · intro u hu
        obtain ⟨x, hx⟩ := (G.adjnF_ecpU x0).1 u hu
        exact ⟨Icp x, ⟨x, rfl⟩, hx⟩
      · rintro _ ⟨x, rfl⟩
        exact ⟨Icp x, by simp, connect_refl _⟩
    have h3 : nComp (frel M.face) (Set.range Icp) = nComp (frel G.face) Set.univ := by
      rw [nComp_adjunction M.cface_sym G.cface_sym Icp (subset_refl _)
        (fun x y _ _ => (G.cface_icpU x0 x y).symm), Set.preimage_range]
    change nComp (frel M.face) {u : EcpDart D | u ≠ IcpX} + nComp (frel M.face) _ = _
    rw [h1, h2, h3]
  have geoX : M.UCyclePlainQuasicubicConnected (M.cpring (G.ecpU x0).pointer).reverse :=
    ⟨⟨⟨G.plain_ecpU x0 plainG, G.cubic_ecpU x0 cubicG⟩, M.ucycle_rev_cpring _⟩,
      G.connected_ecpU x0 ccG⟩
  have geoG : G.UCyclePlainQuasicubicConnected (G.cpring x0).reverse :=
    ⟨⟨⟨plainG, cubicG⟩, G.ucycle_rev_cpring x0⟩, ccG⟩
  have hG := (G.quasicubic_euler geoG).1 planarG
  rw [M.quasicubic_euler geoX]
  have hne : (G.cpring x0).reverse ≠ [] := by rw [G.head_cpring x0]; simp
  have hneX : (M.cpring (G.ecpU x0).pointer).reverse ≠ [] := by
    rw [G.cpring_ecpU x0]; simp
  rw [ite_eq_right hne] at hG
  rw [ite_eq_right hneX, oFX, List.length_reverse, G.size_cpring_ecpU x0]
  rw [List.length_reverse] at hG
  have hcard : Fintype.card (G.ecpU x0).D = Fintype.card D + 2 := card_ecp
  rw [hcard]
  omega

/-- math-comp `cface_ecpN`. -/
theorem cface_ecpN : (G.ecpN x0).pointee.cface (G.ecpN x0).pointer (G.icpN x0 x0) :=
  fconnect1 _ _

/-- The face of `edge (face (edge x0))` in `ecpN x0` is `edge X`. -/
private theorem face_ecpN_efe :
    (G.ecpN x0).pointee.face (G.icpN x0 (G.edge (G.face (G.edge x0)))) = IcpXe := by
  show G.ecpNFace x0 (Icp (G.edge (G.face (G.edge x0)))) = IcpXe
  rw [ecpNFace, ite_eq_left rfl]

/-- math-comp `adjnF_ecpN`: the faces of `ecpN x0` are those of `G` (math-comp's
`fun_adjunction icpN face face ecpN`, as its two fields `rel_unit` and `rel_functor`). -/
theorem adjnF_ecpN :
    (∀ u, ∃ x, (G.ecpN x0).pointee.cface u (G.icpN x0 x)) ∧
    ∀ x y, (G.cface x y ↔ (G.ecpN x0).pointee.cface (G.icpN x0 x) (G.icpN x0 y)) := by
  set M := (G.ecpN x0).pointee
  have hXe := G.face_ecpN_efe x0
  refine ⟨?_, fun x y => ⟨fun hxy => ?_, fun hxy => ?_⟩⟩
  · rintro (_ | _ | x)
    · exact ⟨x0, fconnect1 _ _⟩
    · exact ⟨G.edge (G.face (G.edge x0)), M.cfaceC.1 (connect_of_rel hXe)⟩
    · exact ⟨x, connect_refl _⟩
  · refine connect_map (e := frel G.face) Icp (fun a b hab => ?_) hxy
    subst hab
    by_cases ha1 : a = G.edge (G.face (G.edge x0))
    · have h1 : M.face (Icp a) = IcpXe := by rw [ha1]; exact hXe
      by_cases hl : G.LongCpring x0
      · have h2 : M.face IcpXe = Icp (G.face a) := by
          show G.ecpNFace x0 IcpXe = _
          rw [ecpNFace, ite_eq_left hl, ha1]
        exact connect_trans (connect_of_rel h1) (connect_of_rel h2)
      · have h2 : M.face IcpXe = IcpX := by
          show G.ecpNFace x0 IcpXe = _
          rw [ecpNFace, ite_eq_right hl]
        have h3 : M.face IcpX = Icp (G.face a) := by
          show Icp x0 = Icp (G.face a)
          rw [ha1, not_not.1 hl, G.nodeK]
        exact connect_trans (connect_of_rel h1)
          (connect_trans (connect_of_rel h2) (connect_of_rel h3))
    · by_cases ha2 : a = G.edge (G.node x0)
      · have h1 : M.face (Icp a) = IcpX := by
          show G.ecpNFace x0 (Icp a) = IcpX
          rw [ecpNFace, ite_eq_right ha1, ite_eq_left ha2]
        have h3 : M.face IcpX = Icp (G.face a) := by
          show Icp x0 = Icp (G.face a)
          rw [ha2, G.nodeK]
        exact connect_trans (connect_of_rel h1) (connect_of_rel h3)
      · exact connect_of_rel (show G.ecpNFace x0 (Icp a) = Icp (G.face a) by
          rw [ecpNFace, ite_eq_right ha1, ite_eq_right ha2])
  · let h : EcpDart D → D := fun v => match v with
      | IcpX => x0
      | IcpXe => G.edge (G.face (G.edge x0))
      | Icp z => z
    have key : ∀ v, connect (frel M.face) (Icp x) v → G.cface x (h v) := by
      intro v hv
      induction hv with
      | refl => exact connect_refl _
      | @tail b c _ hbc ih =>
        subst hbc
        match b, ih with
        | IcpX, ih => exact ih
        | IcpXe, ih =>
          by_cases hl : G.LongCpring x0
          · have : M.face IcpXe = Icp (G.face (G.edge (G.face (G.edge x0)))) := by
              show G.ecpNFace x0 IcpXe = _
              rw [ecpNFace, ite_eq_left hl]
            rw [this]
            exact connect_trans ih (fconnect1 _ _)
          · have : M.face IcpXe = IcpX := by
              show G.ecpNFace x0 IcpXe = _
              rw [ecpNFace, ite_eq_right hl]
            rw [this]
            refine connect_trans ih (connect_of_rel ?_)
            show G.face (G.edge (G.face (G.edge x0))) = x0
            rw [not_not.1 hl, G.nodeK]
        | Icp z, ih =>
          by_cases hz1 : z = G.edge (G.face (G.edge x0))
          · have : M.face (Icp z) = IcpXe := by rw [hz1]; exact hXe
            rw [this]
            show G.cface x (G.edge (G.face (G.edge x0)))
            rw [← hz1]
            exact ih
          · by_cases hz2 : z = G.edge (G.node x0)
            · have : M.face (Icp z) = IcpX := by
                show G.ecpNFace x0 (Icp z) = IcpX
                rw [ecpNFace, ite_eq_right hz1, ite_eq_left hz2]
              rw [this]
              refine connect_trans ih (connect_of_rel ?_)
              show G.face z = x0
              rw [hz2, G.nodeK]
            · have : M.face (Icp z) = Icp (G.face z) := by
                show G.ecpNFace x0 (Icp z) = Icp (G.face z)
                rw [ecpNFace, ite_eq_right hz1, ite_eq_right hz2]
              rw [this]
              exact connect_trans ih (fconnect1 _ _)
    exact key _ hxy

/-- math-comp `cface_icpN`. -/
theorem cface_icpN (x y : D) :
    (G.ecpN x0).pointee.cface (G.icpN x0 x) (G.icpN x0 y) ↔ G.cface x y :=
  ((G.adjnF_ecpN x0).2 x y).symm

/-- math-comp `adj_icpN`: the adjacencies of `ecpN x0` between darts of `G` are those of `G`,
plus those between the faces of `edge (face (edge x0))` and of `x0`. -/
theorem adj_icpN (x y : D) :
    (G.ecpN x0).pointee.adj (G.icpN x0 x) (G.icpN x0 y) ↔
      G.adj x y ∨ (G.cface (G.edge (G.face (G.edge x0))) x ∧ G.cface x0 y) ∨
        (G.cface (G.edge (G.face (G.edge x0))) y ∧ G.cface x0 x) := by
  set M := (G.ecpN x0).pointee
  have hXe : M.cface IcpXe (Icp (G.edge (G.face (G.edge x0)))) :=
    M.cfaceC.1 (connect_of_rel (G.face_ecpN_efe x0))
  have hX : M.cface IcpX (Icp x0) := fconnect1 _ _
  rw [M.adjP, G.adjP]
  constructor
  · rintro ⟨z, hxz, hzy⟩
    match z, hxz, hzy with
    | IcpX, hxz, hzy =>
      have h1 : G.cface x x0 := (G.cface_icpN x0 x x0).1 (connect_trans hxz hX)
      have h2 : G.cface (G.edge (G.face (G.edge x0))) y :=
        (G.cface_icpN x0 _ y).1 (connect_trans (M.cfaceC.1 hXe) hzy)
      exact Or.inr (Or.inr ⟨h2, G.cfaceC.1 h1⟩)
    | IcpXe, hxz, hzy =>
      have h1 : G.cface x (G.edge (G.face (G.edge x0))) :=
        (G.cface_icpN x0 _ _).1 (connect_trans hxz hXe)
      have h2 : G.cface x0 y := (G.cface_icpN x0 x0 y).1 (connect_trans (M.cfaceC.1 hX) hzy)
      exact Or.inr (Or.inl ⟨G.cfaceC.1 h1, h2⟩)
    | Icp z, hxz, hzy =>
      exact Or.inl ⟨z, (G.cface_icpN x0 x z).1 hxz, (G.cface_icpN x0 _ y).1 hzy⟩
  · rintro (⟨z, hxz, hzy⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨Icp z, (G.cface_icpN x0 x z).2 hxz, (G.cface_icpN x0 _ y).2 hzy⟩
    · refine ⟨IcpXe, connect_trans ((G.cface_icpN x0 x _).2 (G.cfaceC.1 h1)) (M.cfaceC.1 hXe), ?_⟩
      exact connect_trans hX ((G.cface_icpN x0 x0 y).2 h2)
    · refine ⟨IcpX, connect_trans ((G.cface_icpN x0 x x0).2 (G.cfaceC.1 h2)) (M.cfaceC.1 hX), ?_⟩
      exact connect_trans hXe ((G.cface_icpN x0 _ y).2 h1)

/-- math-comp `sub_adj_icpN`. -/
theorem sub_adj_icpN {x y : D} (h : G.adj x y) :
    (G.ecpN x0).pointee.adj (G.icpN x0 x) (G.icpN x0 y) :=
  (G.adj_icpN x0 x y).2 (Or.inl h)

/-- math-comp `fband_icpN`. -/
theorem fband_icpN (u : (G.ecpN x0).D) : ∃ x, (G.ecpN x0).pointee.cface u (G.icpN x0 x) :=
  (G.adjnF_ecpN x0).1 u

/-- math-comp `planar_ecpN`. -/
theorem planar_ecpN (planarG : G.Planar) (plainG : G.Plain)
    (cubicG : G.Quasicubic (G.cpring x0).reverse) (ccG : G.Connected)
    (x0gt1 : G.ProperCpring x0) : (G.ecpN x0).pointee.Planar := by
  set M := (G.ecpN x0).pointee
  have oFX : fcard M.face Set.univ = fcard G.face Set.univ := by
    show nComp (frel M.face) Set.univ = _
    have h2 : nComp (frel M.face) Set.univ = nComp (frel M.face) (Set.range Icp) := by
      apply nComp_eq_of_connect M.cface_sym
      · intro u _
        obtain ⟨x, hx⟩ := (G.adjnF_ecpN x0).1 u
        exact ⟨Icp x, ⟨x, rfl⟩, hx⟩
      · rintro _ ⟨x, rfl⟩
        exact ⟨Icp x, trivial, connect_refl _⟩
    rw [h2, nComp_adjunction M.cface_sym G.cface_sym Icp (subset_refl _)
      (fun x y _ _ => (G.cface_icpN x0 x y).symm), Set.preimage_range]
  have geoX : M.UCyclePlainQuasicubicConnected (M.cpring (G.ecpN x0).pointer).reverse :=
    ⟨⟨⟨G.plain_ecpN x0 plainG, G.cubic_ecpN x0 cubicG x0gt1⟩, M.ucycle_rev_cpring _⟩,
      G.connected_ecpN x0 ccG⟩
  have geoG : G.UCyclePlainQuasicubicConnected (G.cpring x0).reverse :=
    ⟨⟨⟨plainG, cubicG⟩, G.ucycle_rev_cpring x0⟩, ccG⟩
  have hG := (G.quasicubic_euler geoG).1 planarG
  rw [M.quasicubic_euler geoX]
  have hne : (G.cpring x0).reverse ≠ [] := by rw [G.head_cpring x0]; simp
  have hneX : (M.cpring (G.ecpN x0).pointer).reverse ≠ [] := by
    rw [List.reverse_ne_nil_iff, ← List.length_pos_iff, G.size_cpring_ecpN x0]; omega
  have h2 := (G.size_proper_cpring x0).1 x0gt1
  rw [ite_eq_right hne, List.length_reverse] at hG
  rw [ite_eq_right hneX, oFX, List.length_reverse, G.size_cpring_ecpN x0]
  have hcard : Fintype.card (G.ecpN x0).D = Fintype.card D + 2 := card_ecp
  rw [hcard]
  omega

end EcpUN

omit [DecidableEq D] in
/-- math-comp `ecpR1_eq`: the reference dart of `ecpR 1 x0` is `face (edge x0)`. -/
theorem ecpR1_eq [DecidableEq D] (x0 : D) : (G.ecpR 1 x0).pointer = G.face (G.edge x0) := by
  show G.node^[order G.node x0 - 1] x0 = _
  apply (node_eq_iff' G x0 _).1
  rw [← iterate_succ_apply' G.node, Nat.succ_eq_add_one,
    Nat.sub_add_cancel (order_pos G.nodeI x0), G.iter_order_node]

end Hypermap

end FourColor
