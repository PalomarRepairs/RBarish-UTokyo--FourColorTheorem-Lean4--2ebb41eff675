/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Geometry
import FourColor.Chromogram
import FourColor.Walkup.Genus

/-!
# Colorings, colorable maps, ring traces and configurations  (port of `coloring.v`)

Hypermap, graph and contract colorings, colorable maps, ring traces, valid contracts, and the
definition of the special maps used in the proof: minimal counter example, C-reducible, and
embeddable. For `G : Hypermap D`, `k : D → Color`, and `cc r : List D`:

* `G.Coloring k`          : `k` is a map coloring: `k` assigns the same color to each dart in a
  face cycle of `G`, but a different color to the ends of each edge link, hence to adjacent
  faces (Coq `coloring`).
* `G.FourColorable`       : `G` has a map coloring (Coq `four_colorable`); it is decidable for
  finite maps (instance `decideColorable`, Coq `decide_colorable`).
* `G.GraphColoring k`, `G.GraphFourColorable` : the node (vertex) versions (Coq
  `graph_coloring`, `graph_four_colorable`).
* `G.MinimalCounterExample` : `G` is a minimal counter-example to the finite hypermap four
  color theorem: a non-four-colorable planar bridgeless plain and precubic hypermap, such that
  all such hypermaps with fewer darts are four-colorable (Coq `minimal_counter_example`). We
  show immediately that such a `G` must be cubic (`minimal_counter_example_is_cubic`).
* `G.CcColoring cc k`     : assuming `G` is a plain map, `k` is a contract map coloring for the
  contract `cc`: `k` assigns the same color to faces adjacent via an E-link `(x, edge x)`, for
  `x ∈ cc`, but different colors to other adjacent faces (Coq `cc_coloring`).
* `G.CcColorable cc`      : there is a contract map coloring for `cc` (Coq `cc_colorable`).
* `G.RingTrace r et`      : there is a map coloring `k` such that `et` is the edge coloring
  trace of `r.map k` (Coq `ring_trace`).
* `G.CcRingTrace cc r et` : there is a contract coloring for `cc` with trace `et` on `r`
  (Coq `cc_ring_trace`).
* `G.GoodRingArity x`     : the arity (face size) of `x` is between 3 and 6 (Coq
  `good_ring_arity`).
* `G.AtRadius2 A x y`     : `x` and `y` are both adjacent to some common `z ∈ A` (Coq
  `at_radius2`).
* `G.Radius2 A`           : `A` has radius 2, i.e., there is an `x ∈ A` such that
  `G.AtRadius2 A x y` holds for all `y ∈ A` (Coq `radius2`).
* `G.Embeddable r`        : `G` is an embeddable configuration with perimeter `r`: `G` is
  planar, bridgeless, connected, plain, and `r`-quasicubic for the simple N-cycle `r`, while
  `GoodRingArity` holds on `r` and `G.kernel r` has radius 2 (Coq `embeddable`).
* `G.Sparse p`            : `p` is node-simple: no two darts of `p` belong to the same node
  (Coq `sparse`).
* `G.Triad p x`           : `x` is a triad for `p`: at least three of the faces around the face
  of `x` contain a dart `y` of `p`, but not all `y ∈ p` are adjacent to `x` (Coq `triad`).
* `G.ValidContract r cc`  : `cc` is a valid contract for the ring `r`: `cc` has size at most 4,
  and the edge completion of `cc` is disjoint from `r`, sparse, and has a triad if `cc` has
  size 4 (Coq `valid_contract`).
* `G.CReducible r cc`     : assuming `G` is a configuration with ring `r`, `G` is C-reducible
  with contract `cc`: `cc` is valid, and any contract ring trace for `cc` is in the Kempe
  co-closure of the set of ring traces of colorings of `G` (Coq `C_reducible`).
* `G.edgeCentral G' h`    : the darts `x` at which `h : D → D'` commutes with `edge` (Coq
  `edge_central h`).
* `G.Preembedding G' A h` : `h` is an embedding of the subset `A` of `G` into `G'`: in `A`, `h`
  commutes with face and preserves arity, `A` is included in the face-closure of its
  edge-central subset, which is R-link connected (Coq `preembedding`).

## Porting notes

* All the predicates are `Prop`s; the Coq boolean predicates (`good_ring_arity`, `at_radius2`,
  `radius2`, `sparse`, `triad`, `edge_central`) and the Coq `pred`s on darts are stated as
  `Prop`s or `Set`s, and their reflection lemmas (`at_radius2P`, `radius2P`) are `↔`.
* math-comp's `exists2 x, P x & Q x` is `∃ x, P x ∧ Q x`; `invariant f k =1 pred0` is
  `∀ x, k (f x) ≠ k x`, `invariant f k =1 G` is `∀ x, k (f x) = k x`.
* The minimality hypothesis of `MinimalCounterExample` quantifies over all hypermaps whose dart
  type lives in the same universe as `D`.
* The decidability lemmas `decide_ring_trace` and `decide_colorable` are the instances
  `decideRingTrace` and `decideColorable`, obtained by enumerating all functions
  `D → Color` (the Coq proof builds the search explicitly).
* `eqm` (equality of hypermaps up to extensionality) is plain equality, so `eqm_colorable` and
  `eqm_graph_colorable` are immediate.
* math-comp `rot` is `FourColor.rot` (from `Color.lean`).
-/

namespace FourColor

open Function

universe u v

/-- math-comp `fconnect_invariant`: a function invariant under `f` is constant on the
`f`-orbits. -/
private theorem fconnect_invariant {α β : Type*} {f : α → α} {k : α → β}
    (hk : ∀ x, k (f x) = k x) {x y : α} (h : fconnect f x y) : k y = k x := by
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    subst hbc
    rw [hk, ih]

namespace Hypermap

variable {D : Type u}

/-! ### Colorings -/

section Coloring

variable (G : Hypermap D)

/-- Coq `coloring k`: `k` is a map coloring of `G`, i.e., it assigns different colors to the
ends of each edge link, and the same color to each face cycle
(`invariant edge k =1 pred0 /\ invariant face k =1 G`). -/
def Coloring (k : D → Color) : Prop :=
  (∀ x, k (G.edge x) ≠ k x) ∧ ∀ x, k (G.face x) = k x

/-- Coq `coloring_inj`: composing a coloring with an injection of colors gives a coloring. -/
theorem coloring_inj {h : Color → Color} (hh : Injective h) {k : D → Color} (hk : G.Coloring k) :
    G.Coloring (h ∘ k) :=
  ⟨fun x e => hk.1 x (hh e), fun x => congrArg h (hk.2 x)⟩

/-- A coloring is constant on faces (Coq `fconnect_invariant` applied to a coloring). -/
theorem coloring_cface {k : D → Color} (hk : G.Coloring k) {x y : D} (h : G.cface x y) :
    k x = k y :=
  (fconnect_invariant hk.2 h).symm

/-- Coq `ring_trace r et`: there is a map coloring `k` such that `et` is the trace of the
perimeter coloring `r.map k`. -/
def RingTrace (r : List D) (et : Colseq) : Prop := ∃ k, G.Coloring k ∧ et = trace (r.map k)

/-- Coq `four_colorable G`: `G` has a map coloring. -/
def FourColorable : Prop := ∃ k, G.Coloring k

/-- Coq `colorable_bridgeless`. -/
theorem colorable_bridgeless (hG : G.FourColorable) : G.Bridgeless := by
  rintro ⟨x, hx⟩
  obtain ⟨k, hk⟩ := hG
  exact hk.1 x (G.coloring_cface hk hx).symm

/-- Coq `graph_coloring k`: `k` assigns different colors to the ends of each edge link, and the
same color to each node cycle. -/
def GraphColoring (k : D → Color) : Prop :=
  (∀ x, k (G.edge x) ≠ k x) ∧ ∀ x, k (G.node x) = k x

/-- Coq `graph_four_colorable G`: `G` has a graph coloring. -/
def GraphFourColorable : Prop := ∃ k, G.GraphColoring k

/-- Coq `cc_coloring cc k`: `k` is a contract map coloring for the contract `cc`: it assigns the
same color to the ends of the E-links of `insertE cc`, different colors to the ends of the
other E-links, and the same color to each face cycle
(`invariant edge k =i insertE cc /\ invariant face k =1 G`). -/
def CcColoring (cc : List D) (k : D → Color) : Prop :=
  (∀ x, k (G.edge x) = k x ↔ x ∈ G.insertE cc) ∧ ∀ x, k (G.face x) = k x

/-- Coq `cc_colorable cc`: there is a contract map coloring for `cc`. -/
def CcColorable (cc : List D) : Prop := ∃ k, G.CcColoring cc k

/-- Coq `cc_ring_trace cc r et`: there is a contract coloring for `cc` whose trace on `r`
is `et`. -/
def CcRingTrace (cc r : List D) (et : Colseq) : Prop :=
  ∃ k, G.CcColoring cc k ∧ et = trace (r.map k)

/-- A graph coloring is constant on nodes (Coq `fconnect_invariant` applied to a graph
coloring). -/
theorem graph_coloring_cnode {k : D → Color} (hk : G.GraphColoring k) {x y : D}
    (h : G.cnode x y) : k x = k y :=
  (fconnect_invariant hk.2 h).symm

/-- A contract coloring is constant on faces (Coq `fconnect_invariant` applied to a contract
coloring). -/
theorem cc_coloring_cface {cc : List D} {k : D → Color} (hk : G.CcColoring cc k) {x y : D}
    (h : G.cface x y) : k x = k y :=
  (fconnect_invariant hk.2 h).symm

end Coloring

/-! ### Colorings of the dual and mirror maps -/

section ColoringDual

variable (G : Hypermap D) [Finite D]

/-- Coq `coloring_dual`. -/
theorem coloring_dual (k : D → Color) : G.dual.Coloring k ↔ G.GraphColoring k := by
  constructor
  · rintro ⟨kE', kF'⟩
    refine ⟨fun x => ?_, fun x => ?_⟩
    · -- `x = node (face (edge x))`
      have h := kE' (G.edge x)
      rw [dual_edge, G.edgeK] at h
      exact fun e => h e.symm
    · have h := kF' (G.node x)
      rw [dual_face, G.nodeK] at h
      exact h.symm
  · rintro ⟨kE, kN⟩
    refine ⟨fun x => ?_, fun x => ?_⟩
    · have h := kE (G.node (G.face x))
      rw [G.faceK] at h
      rw [dual_edge]
      exact fun e => h e.symm
    · have h := kN (G.face (G.edge x))
      rw [dual_face]
      rw [G.edgeK] at h
      exact h.symm

/-- Coq `four_colorable_dual`. -/
theorem four_colorable_dual : G.dual.FourColorable ↔ G.GraphFourColorable :=
  exists_congr fun k => G.coloring_dual k

/-- Coq `coloring_mirror`. -/
theorem coloring_mirror {k : D → Color} (hk : G.mirror.Coloring k) : G.Coloring k := by
  obtain ⟨kE', kF'⟩ := hk
  have kF : ∀ x, k (G.face x) = k x := fun x => by
    have h := kF' (G.face x)
    rw [mirror_face, G.faceK] at h
    exact h.symm
  refine ⟨fun x e => ?_, kF⟩
  -- `kE'` at `face (edge x)`: `k (face x) ≠ k (face (edge x))`
  have h := kE' (G.face (G.edge x))
  rw [mirror_edge, G.edgeK, kF, kF] at h
  exact h e.symm

/-- Coq `colorable_mirror`. -/
theorem colorable_mirror (hG : G.mirror.FourColorable) : G.FourColorable := by
  obtain ⟨k, hk⟩ := hG
  exact ⟨k, G.coloring_mirror hk⟩

end ColoringDual

/-! ### Equal hypermaps -/

section EqmColorable

/-- Coq `eqm_colorable` (`eqm` is equality here). -/
theorem eqm_colorable {G G' : Hypermap D} (h : G = G') (hG : G.FourColorable) :
    G'.FourColorable :=
  h ▸ hG

/-- Coq `eqm_graph_colorable` (`eqm` is equality here). -/
theorem eqm_graph_colorable {G G' : Hypermap D} (h : G = G') (hG : G.GraphFourColorable) :
    G'.GraphFourColorable :=
  h ▸ hG

end EqmColorable

/-! ### Decidability of colorability -/

section DecideColorable

variable (G : Hypermap D) [Fintype D] [DecidableEq D]

/-- Coq `decide_ring_trace`: ring traces are decidable (used for case analysis in `birkhoff`).
Here all the colorings `D → Color` are enumerated. -/
instance decideRingTrace (r : List D) (et : Colseq) : Decidable (G.RingTrace r et) := by
  unfold RingTrace Coloring
  infer_instance

/-- Coq `decide_colorable`: four-colorability is decidable. -/
instance decideColorable : Decidable G.FourColorable := by
  unfold FourColorable Coloring
  infer_instance

end DecideColorable

/-! ### Minimal counter-examples -/

section MinimalCounterExample

variable (G : Hypermap D)

/-- Coq `minimal_counter_example G`: `G` is a minimal counter-example to the finite hypermap
four color theorem: a non-four-colorable planar bridgeless plain and precubic hypermap, such
that all such hypermaps with fewer darts are four-colorable. The minimality quantifies over the
hypermaps whose dart types live in the same universe as `D`. -/
structure MinimalCounterExample [Fintype D] : Prop extends G.PlanarBridgelessPlainPrecubic where
  /-- Coq `minimal_counter_example_is_noncolorable`. -/
  noncolorable : ¬ G.FourColorable
  /-- Coq `minimal_counter_example_is_minimal`. -/
  minimal : ∀ (D' : Type u) [Fintype D'] (G' : Hypermap D'),
    G'.PlanarBridgelessPlainPrecubic → Fintype.card D' < Fintype.card D → G'.FourColorable

/-- Coq `minimal_counter_example_is_cubic`: a minimal counter-example is cubic. -/
theorem minimal_counter_example_is_cubic [Fintype D] {G : Hypermap D}
    (cexG : G.MinimalCounterExample) : G.Cubic := by
  classical
  have F'eG := G.bridgeless_cface cexG.bridgeless
  have plainG : G.Plain := cexG.plain
  have nGle3 : G.Precubic := cexG.precubic
  -- `edge (node y)` is in the face of `y`
  have hFE : ∀ y, G.cface (G.edge (G.node y)) y := fun y => by
    have := fconnect1 G.face (G.edge (G.node y))
    rwa [G.nodeK] at this
  intro x _
  show order G.node x = 3
  by_contra n3'x
  have x'nx : G.node x ≠ x := by
    intro e
    apply F'eG x
    have := hFE x
    rw [e] at this
    exact G.cfaceC.1 this
  have nnx : G.node (G.node x) = x := by
    by_contra hnn
    apply n3'x
    have hle := nGle3 x
    have hpos := order_pos G.nodeI x
    have hit := iter_order G.nodeI x
    rcases (by omega : order G.node x = 1 ∨ order G.node x = 2 ∨ order G.node x = 3)
      with h | h | h
    · rw [h] at hit
      exact absurd hit x'nx
    · rw [h] at hit
      exact absurd hit hnn
    · exact h
  have hez : G.edge x ≠ x := G.plain_neq plainG x
  -- Remove the node `{x, node x}`: `G'` is `WalkupE x`, `G''` is `WalkupE unx` in `G'`.
  set unx : WDart x := ⟨G.node x, x'nx⟩ with hunx
  set G' : Hypermap (WDart x) := G.WalkupE x with hG'
  set G'' : Hypermap (WDart unx) := G'.WalkupE unx with hG''
  have Ih : Injective (fun w : WDart unx => w.1.1) := fun a b hab => Subtype.ext (Subtype.ext hab)
  have hF : ∀ w1 w2 : WDart unx, G''.cface w1 w2 ↔ G.cface w1.1.1 w2.1.1 := fun w1 w2 =>
    (fconnect_skip unx G'.faceI w1 w2).trans (fconnect_skip x G.faceI w1.1 w2.1)
  have hN : ∀ w1 w2 : WDart unx, G''.cnode w1 w2 ↔ G.cnode w1.1.1 w2.1.1 := fun w1 w2 =>
    (fconnect_skip unx G'.nodeI w1 w2).trans (fconnect_skip x G.nodeI w1.1 w2.1)
  have hN1 : ∀ w : WDart unx, (G''.node w).1.1 = G.node w.1.1 := by
    intro w
    have hy1 : w.1.1 ≠ x := w.1.2
    have hy2 : w.1.1 ≠ G.node x := fun e => w.2 (Subtype.ext e)
    have h1 : G.node w.1.1 ≠ x := fun e => hy2 (G.nodeI (e.trans nnx.symm))
    have h2 : G'.node w.1 ≠ unx := by
      intro e
      have e' := congrArg Subtype.val e
      rw [hG', WalkupE_node_val, skip1_of_ne x h1] at e'
      exact hy1 (G.nodeI e')
    rw [hG'', WalkupE_node_val, skip1_of_ne unx h2, hG', WalkupE_node_val, skip1_of_ne x h1]
  have ltG''G : Fintype.card (WDart unx) < Fintype.card D := by
    have c1 := card_S_Walkup x
    have c2 := card_S_Walkup unx
    omega
  -- `unx` is a node fixpoint of `G'`, so `G''` has edge permutation `skip edge`.
  have hglink : G'.glink unx unx := by
    refine Or.inr (Or.inl (Subtype.ext ?_))
    rw [hG', WalkupE_node_val]
    exact skip1_of_eq x nnx
  have hE' : ∀ u : WDart x, u.1 ≠ G.node x →
      (G'.edge u).1 = if G.edge u.1 = x then G.edge (G.node x) else G.edge u.1 := by
    intro u hu
    have h1 : G.face (G.edge u.1) ≠ x := fun e =>
      hu ((G.edgeK u.1).symm.trans (congrArg G.node e))
    rw [hG', WalkupE_edge_val]
    split_ifs with h2
    · exact G.skipEdge1_of_edge x hez h1 h2
    · exact G.skipEdge1_of_ne x hez h1 h2
  have hEunx : (G'.edge unx).1 = G.edge x := by
    rw [hG', WalkupE_edge_val]
    exact G.skipEdge1_of_face_edge x hez (G.nodeK x)
  have hE1 : ∀ w : WDart unx, (G''.edge w).1.1 =
      if G.edge w.1.1 = x then G.edge (G.node x)
      else if G.edge w.1.1 = G.node x then G.edge x else G.edge w.1.1 := by
    intro w
    have hw : w.1.1 ≠ G.node x := fun e => w.2 (Subtype.ext e)
    have e1 : G''.edge w = skip unx G'.edgeI w := G'.glink_fp_skip_edge unx hglink w
    rw [e1, skip_val]
    by_cases h2 : G'.edge w.1 = unx
    · rw [skip1_of_eq unx h2, hEunx]
      have h3 := congrArg Subtype.val h2
      rw [hE' w.1 hw] at h3
      split_ifs at h3 ⊢ with h4 h5
      · exact absurd h3 (G.plain_neq plainG _)
      · rfl
      · exact absurd h3 h5
    · rw [skip1_of_ne unx h2, hE' w.1 hw]
      have h3 : (G'.edge w.1).1 ≠ G.node x := fun e => h2 (Subtype.ext e)
      rw [hE' w.1 hw] at h3
      split_ifs at h3 ⊢ with h4 h5
      · rfl
      · exact absurd h5 h3
      · rfl
  -- `G''` is a smaller planar bridgeless plain precubic map.
  have plainG'' : G''.Plain := by
    refine (G''.plainP).2 fun w _ => ?_
    have hy1 : w.1.1 ≠ x := w.1.2
    have hy2 : w.1.1 ≠ G.node x := fun e => w.2 (Subtype.ext e)
    have key : (G''.edge (G''.edge w)).1.1 = w.1.1 ∧ (G''.edge w).1.1 ≠ w.1.1 := by
      rw [hE1 (G''.edge w), hE1 w]
      generalize w.1.1 = y at hy1 hy2 ⊢
      have ex : G.edge (G.edge x) = x := G.plain_eq plainG x
      have enx : G.edge (G.edge (G.node x)) = G.node x := G.plain_eq plainG (G.node x)
      have ey : G.edge (G.edge y) = y := G.plain_eq plainG y
      have hne : G.edge (G.node x) ≠ G.edge x := fun e => x'nx (G.edgeI e)
      by_cases h1 : G.edge y = x
      · have hy : y = G.edge x := by rw [← h1, ey]
        rw [ite_eq_left h1, enx, ite_eq_right x'nx, ite_eq_left rfl]
        exact ⟨hy.symm, hy ▸ hne⟩
      · by_cases h2 : G.edge y = G.node x
        · have hy : y = G.edge (G.node x) := by rw [← h2, ey]
          rw [ite_eq_right h1, ite_eq_left h2, ex, ite_eq_left rfl]
          exact ⟨hy.symm, hy ▸ hne.symm⟩
        · rw [ite_eq_right h1, ite_eq_right h2, ey, ite_eq_right hy1, ite_eq_right hy2]
          exact ⟨rfl, G.plain_neq plainG y⟩
    exact ⟨Subtype.ext (Subtype.ext key.1), fun e => key.2 (by rw [e])⟩
  have precubicG'' : G''.Precubic := by
    intro w
    calc order G''.node w = ((fun w : WDart unx => w.1.1) '' {v | G''.cnode w v}).ncard :=
          (Set.ncard_image_of_injective _ Ih).symm
      _ ≤ order G.node w.1.1 :=
          Set.ncard_le_ncard (by rintro _ ⟨v, hv, rfl⟩; exact (hN w v).1 hv)
      _ ≤ 3 := nGle3 _
  have bridgelessG'' : G''.Bridgeless := by
    rintro ⟨w, hw⟩
    have e : G''.node (G''.face (G''.edge w)) = w := G''.edgeK w
    have h1 : G''.cface (G''.node (G''.face (G''.edge w))) (G''.face (G''.edge w)) := by
      rw [e]
      exact (G''.cface1r w (G''.edge w)).1 hw
    have h2 := (hF _ _).1 h1
    rw [hN1] at h2
    apply F'eG (G.node (G''.face (G''.edge w)).1.1)
    exact (G.cface1r _ _).2 (by rw [G.nodeK]; exact h2)
  have hPBPP : G''.PlanarBridgelessPlainPrecubic :=
    { planar := planar_WalkupE G' unx (planar_WalkupE G x cexG.planar)
      bridgeless := bridgelessG''
      plain := plainG''
      precubic := precubicG'' }
  obtain ⟨k, kE, kF⟩ := cexG.minimal (WDart unx) G'' hPBPP ltG''G
  -- Extend the coloring `k` of `G''` to a coloring of `G`.
  apply cexG.noncolorable
  have kFF : ∀ w w', G''.cface w w' → k w = k w' := fun w w' h =>
    (fconnect_invariant kF h).symm
  have a'0P : ∀ y, (¬ ∃ w : WDart unx, G.cface y w.1.1) → y = x ∨ y = G.node x := by
    intro y hy
    by_contra hne
    rw [not_or] at hne
    exact hy ⟨⟨⟨y, hne.1⟩, fun e => hne.2 (congrArg Subtype.val e)⟩, connect_refl y⟩
  have a'F : ∀ y z, (¬ ∃ w : WDart unx, G.cface y w.1.1) → G.cface y z → y = z := by
    intro y z hy hyz
    have hz : ¬ ∃ w : WDart unx, G.cface z w.1.1 := fun ⟨w, hw⟩ =>
      hy ⟨w, connect_trans hyz hw⟩
    by_contra hne
    have hzn : z = G.node y := by
      rcases a'0P y hy with hy1 | hy1 <;> rcases a'0P z hz with hz1 | hz1
      · exact absurd (hy1.trans hz1.symm) hne
      · rw [hy1, hz1]
      · rw [hy1, hz1, nnx]
      · exact absurd (hy1.trans hz1.symm) hne
    rw [hzn] at hyz
    exact F'eG (G.node y) (G.cfaceC.1 (connect_trans (hFE y) hyz))
  let k' : D → Color := fun y =>
    if hy : ∃ w : WDart unx, G.cface y w.1.1 then k hy.choose else ccons false (decide (y = x))
  have k'_pos : ∀ y (hy : ∃ w : WDart unx, G.cface y w.1.1), k' y = k hy.choose :=
    fun y hy => dite_eq_left hy
  have k'_neg : ∀ y, (¬ ∃ w : WDart unx, G.cface y w.1.1) → k' y = ccons false (decide (y = x)) :=
    fun y hy => dite_eq_right hy
  have k'F : ∀ y z, G.cface y z → k' y = k' z := by
    intro y z hyz
    by_cases hy : ∃ w : WDart unx, G.cface y w.1.1
    · have hz : ∃ w : WDart unx, G.cface z w.1.1 :=
        ⟨hy.choose, connect_trans (G.cfaceC.1 hyz) hy.choose_spec⟩
      rw [k'_pos y hy, k'_pos z hz]
      apply kFF
      rw [hF]
      exact connect_trans (G.cfaceC.1 hy.choose_spec) (connect_trans hyz hz.choose_spec)
    · rw [a'F y z hy hyz]
  have k'E : ∀ y, y ≠ x → y ≠ G.node x → k' y ≠ k' (G.edge y) := by
    intro y x'y nx'y
    let w : WDart unx := ⟨⟨y, x'y⟩, fun e => nx'y (congrArg Subtype.val e)⟩
    have Dfey : G.face (G.edge y) = (G''.face (G''.edge w)).1.1 := by
      apply G.nodeI
      rw [G.edgeK, ← hN1, G''.edgeK]
    rw [k'F (G.edge y) (G.face (G.edge y)) (fconnect1 _ _)]
    have hy : ∃ w : WDart unx, G.cface y w.1.1 := ⟨w, connect_refl y⟩
    have hfey : ∃ w : WDart unx, G.cface (G.face (G.edge y)) w.1.1 :=
      ⟨G''.face (G''.edge w), by rw [Dfey]⟩
    rw [k'_pos y hy, k'_pos _ hfey]
    intro e
    apply kE w
    rw [← kF (G''.edge w)]
    have e1 : k w = k hy.choose := kFF _ _ ((hF w hy.choose).2 hy.choose_spec)
    have e2 : k (G''.face (G''.edge w)) = k hfey.choose :=
      kFF _ _ ((hF _ _).2 (by rw [← Dfey]; exact hfey.choose_spec))
    rw [e2, ← e, ← e1]
  -- The node `{x, node x}` is not on a face of `G''` when its edges are "folded".
  have hfn : ∀ y, G.face y ≠ G.node y := fun y e => by
    apply F'eG (G.node y)
    have h1 : G.cface (G.edge (G.node y)) (G.node y) :=
      connect_trans (hFE y) (by rw [← e]; exact fconnect1 G.face y)
    exact G.cfaceC.1 h1
  have hfxn : ∀ a, (a = x ∨ a = G.node x) →
      (G.face (G.edge a) = x ∨ G.face (G.edge a) = G.node x) := by
    intro a ha
    rcases ha with ha | ha
    · right
      rw [ha]
      have := G.nodeK (G.node x)
      rwa [nnx] at this
    · left
      rw [ha]
      exact G.nodeK x
  have noP : ∀ y, (y = x ∨ y = G.node x) → (G.edge y = x ∨ G.edge y = G.node x) →
      ¬ ∃ w : WDart unx, G.cface y w.1.1 := by
    rintro y Dy Dey ⟨w, hw⟩
    have hfy : G.face y = x ∨ G.face y = G.node x := by
      have := hfxn (G.edge y) Dey
      rwa [G.plain_eq plainG] at this
    have hfy' : G.face y = y := by
      by_contra hne
      apply hfn y
      rcases Dy with Dy | Dy <;> rcases hfy with hfy | hfy
      · exact absurd (hfy.trans Dy.symm) hne
      · rw [hfy, Dy]
      · rw [hfy, Dy, nnx]
      · exact absurd (hfy.trans Dy.symm) hne
    have hwy : w.1.1 = y := by
      obtain ⟨n, hn⟩ := fconnect_iff_iterate.1 hw
      rw [← hn]
      exact Function.iterate_fixed hfy' n
    rcases Dy with Dy | Dy
    · exact w.1.2 (hwy.trans Dy)
    · exact w.2 (Subtype.ext (hwy.trans Dy))
  refine ⟨k', fun y => ?_, fun y => (k'F y (G.face y) (fconnect1 _ y)).symm⟩
  by_cases Dy : y = x ∨ y = G.node x
  swap
  · rw [not_or] at Dy
    exact (k'E y Dy.1 Dy.2).symm
  have eey := G.plain_eq plainG y
  by_cases Dey : G.edge y = x ∨ G.edge y = G.node x
  swap
  · rw [not_or] at Dey
    have := k'E (G.edge y) Dey.1 Dey.2
    rwa [eey] at this
  have ny := noP y Dy Dey
  have ney := noP (G.edge y) Dey (by rw [eey]; exact Dy)
  rw [k'_neg y ny, k'_neg _ ney]
  rcases Dy with Dy | Dy
  · have hey : G.edge y ≠ x := by rw [Dy]; exact hez
    rw [decide_eq_false hey, decide_eq_true Dy]
    decide
  · have hey : G.edge y = x := a'F (G.edge y) x ney (by rw [Dy]; exact hFE x)
    have hyx : y ≠ x := by rw [Dy]; exact x'nx
    rw [decide_eq_true hey, decide_eq_false hyx]
    decide

/-- Coq `minimal_counter_example_is_cubic` (a coercion in Coq). -/
theorem MinimalCounterExample.cubic [Fintype D] {G : Hypermap D}
    (cexG : G.MinimalCounterExample) : G.Cubic :=
  minimal_counter_example_is_cubic cexG

/-- Coq `minimal_counter_example_mirror`: used for symmetry disposition, and flipped
configuration match. -/
theorem minimal_counter_example_mirror [Fintype D] {G : Hypermap D}
    (cexG : G.MinimalCounterExample) : G.mirror.MinimalCounterExample where
  planar := (G.planar_mirror).2 cexG.planar
  bridgeless := (G.bridgeless_mirror).2 cexG.bridgeless
  plain := (G.plain_mirror).2 cexG.plain
  precubic := (G.precubic_mirror).2 cexG.precubic
  noncolorable := fun h => cexG.noncolorable (G.colorable_mirror h)
  minimal := cexG.minimal

end MinimalCounterExample

/-! ### Configuration properties

We state and prove separately the geometrical and semantic requirements on configurations.
The former (`Embeddable`) are established by the quiz construction; the latter (`CReducible`)
by the reducibility check.

The geometrical requirements are that configuration maps must be plain quasicubic planar
bridgeless maps with a simple ring, that satisfy two additional conditions: the ring faces
arities must be in the 3..6 range, and the kernel must have radius 2. These two additional
properties are used in `embed.v` to extend a partial hypermap morphism into an embedding. -/

section ConfigurationProperties

variable (G : Hypermap D)

/-- Coq `good_ring_arity x`: the arity of `x` is 3, 4, 5 or 6 (Coq `pred4 3 4 5 6`). -/
def GoodRingArity (x : D) : Prop :=
  G.arity x = 3 ∨ G.arity x = 4 ∨ G.arity x = 5 ∨ G.arity x = 6

/-- `GoodRingArity` as an interval condition. -/
theorem goodRingArity_iff (x : D) : G.GoodRingArity x ↔ 3 ≤ G.arity x ∧ G.arity x ≤ 6 := by
  unfold GoodRingArity
  omega

/-! #### Radius 2

Since our configuration maps have at most one "bridge" face, we can use a slightly more
restrictive definition of "radius 2": we insist that every region is exactly two adj "hops"
away from the center rather than just "at most two" (the extra requirement will always be met,
because we can always take a detour through an adjacent spoke). The weaker definition is more
complex, and in particular it's easier to check the stricter condition using the configuration
data. -/

/-- Coq `at_radius2 A x y`: `x` and `y` are both adjacent to some common `z ∈ A`
(`~~ [disjoint adj y & [predI adj x & A]]`). -/
def AtRadius2 (A : Set D) (x y : D) : Prop := ∃ z, G.adj y z ∧ G.adj x z ∧ z ∈ A

/-- Coq `at_radius2P`. -/
theorem at_radius2P [Finite D] {A : Set D} (hA : Closed (frel G.face) A) {x y : D} :
    G.AtRadius2 A x y ↔
      ∃ x' y', (G.cface x x' ∧ G.cface y y') ∧ (G.edge x' ∈ A ∧ G.cface (G.edge x') (G.edge y')) := by
  constructor
  · rintro ⟨z, hyz, hxz, hzA⟩
    obtain ⟨y', yFy', y'Rz⟩ := G.adjP.1 hyz
    obtain ⟨x', xFx', x'Rz⟩ := G.adjP.1 hxz
    exact ⟨x', y', ⟨xFx', yFy'⟩, (hA.connect_iff x'Rz).2 hzA,
      connect_trans x'Rz (G.cfaceC.1 y'Rz)⟩
  · rintro ⟨x', y', ⟨xFx', yFy'⟩, hA', ex'Fey'⟩
    exact ⟨G.edge x', G.adjP.2 ⟨y', yFy', G.cfaceC.1 ex'Fey'⟩,
      G.adjP.2 ⟨x', xFx', connect_refl _⟩, hA'⟩

/-- Coq `radius2 A`: `A` has radius 2, there is a center `x ∈ A` such that `at_radius2 A x y`
for all `y ∈ A` (`~~ [disjoint A & [pred x | A \subset at_radius2 x]]`). -/
def Radius2 (A : Set D) : Prop := ∃ x ∈ A, ∀ y ∈ A, G.AtRadius2 A x y

/-- Coq `radius2P`. -/
theorem radius2P {A : Set D} : G.Radius2 A ↔ ∃ x ∈ A, ∀ y ∈ A, G.AtRadius2 A x y := Iff.rfl

/-- Coq `embeddable r`: `G` is an embeddable configuration with perimeter `r`. -/
structure Embeddable [Fintype D] (r : List D) : Prop
    extends G.SCyclePlanarBridgelessPlainQuasicubicConnected r where
  /-- Coq `embeddable_ring`: all the faces of the ring have arity 3..6. -/
  ring : ∀ x ∈ r, G.GoodRingArity x
  /-- Coq `embeddable_kernel`: the kernel has radius 2. -/
  kernel : G.Radius2 (G.kernel r)

/-- Coq `sparse p`: `p` is node-simple, no two darts of `p` belong to the same node. Coq
defines it as `simple (p : seq (permF G))`; since `permF G` has face permutation `node`, this is
`(p.map (froot G.node)).Nodup` (see `sparse_iff_simple_permF`), which we take as the definition
so that no finiteness assumption is needed to state it. -/
def Sparse (p : List D) : Prop := (p.map (froot G.node)).Nodup

/-- `sparse p` is `simple p` in `permF G` (the Coq definition of `sparse`). -/
theorem sparse_iff_simple_permF [Finite D] (p : List D) : G.Sparse p ↔ G.permF.Simple p := Iff.rfl

/-- Coq `sparse_cons`. -/
theorem sparse_cons [Finite D] (x : D) (p : List D) :
    G.Sparse (x :: p) ↔ (¬ ∃ y ∈ p, G.cnode x y) ∧ G.Sparse p :=
  G.permF.simple_cons x p

/-- Coq `sparse_catC`. -/
theorem sparse_catC (p1 p2 : List D) : G.Sparse (p1 ++ p2) ↔ G.Sparse (p2 ++ p1) := by
  unfold Sparse
  rw [List.map_append, List.map_append, List.nodup_append_comm]

/-- Coq `sparse_catCA`. -/
theorem sparse_catCA (p1 p2 p3 : List D) :
    G.Sparse (p1 ++ (p2 ++ p3)) ↔ G.Sparse (p2 ++ (p1 ++ p3)) :=
  ((List.perm_append_comm_assoc p1 p2 p3).map _).nodup_iff

/-- Coq `sparse_rot` (with the math-comp `rot`). -/
theorem sparse_rot (n0 : ℕ) (p : List D) : G.Sparse (rot n0 p) ↔ G.Sparse p :=
  ((perm_rot n0 p).map _).nodup_iff

open Classical in
/-- Coq `triad p x`: at least three of the faces around the face of `x` contain a dart of `p`
(i.e., more than two darts `y` of the face of `x` have `edge y` in the face band of `p`), but
not all darts of `p` are adjacent to `x`. -/
def Triad (p : List D) (x : D) : Prop :=
  2 < (orbit G.face x).countP (fun y => decide (G.edge y ∈ G.fband p)) ∧ ¬ ∀ y ∈ p, G.adj x y

/-- Coq `valid_contract r cc`: `cc` is a valid contract for the ring `r`. -/
structure ValidContract (r cc : List D) : Prop where
  /-- Coq `valid_contract_is_off_ring`: `[disjoint r & insertE cc]`. -/
  off_ring : List.Disjoint r (G.insertE cc)
  /-- Coq `valid_contract_is_sparse`. -/
  sparse : G.Sparse (G.insertE cc)
  /-- Coq `valid_contract_size`: `pred4 1 2 3 4 (size cc)`. -/
  size : cc.length = 1 ∨ cc.length = 2 ∨ cc.length = 3 ∨ cc.length = 4
  /-- Coq `valid_contract_triad`: a contract of size 4 has a triad in the kernel. -/
  triad : cc.length = 4 → ∃ x ∈ G.kernel r, G.Triad (G.insertE cc) x

/-- Coq `C_reducible r cc`: `G` is C-reducible with contract `cc` and ring `r`. -/
structure CReducible (r cc : List D) : Prop extends G.ValidContract r cc where
  /-- Coq `C_reducible_coclosure`. -/
  coclosure : ∀ et : Colseq, G.CcRingTrace cc r.reverse et →
    KempeCoclosure (G.RingTrace r.reverse) et

end ConfigurationProperties

/-! ### Preembeddings

The properties of the partial morphism constructed in quiz, and extended to an embedding in
embed. The morphism is only defined on the kernel of the configuration. On this subset, it
should be a strict morphism for face and arity. The darts on which it commutes with edge should
form an R-link-connected cover of the kernel, up to `cface`. -/

section Preembedding

variable {D' : Type v} (G : Hypermap D) (G' : Hypermap D')

/-- Coq `edge_central h`: the darts `x` such that `h (edge x) = edge (h x)`. -/
def edgeCentral (h : D → D') : Set D := {x | h (G.edge x) = G'.edge (h x)}

/-- Coq `edge_central_edge`. -/
theorem edge_central_edge [Finite D] [Finite D'] (hG : G.Plain) (hG' : G'.Plain) (h : D → D')
    (x : D) : G.edge x ∈ G.edgeCentral G' h ↔ x ∈ G.edgeCentral G' h := by
  show h (G.edge (G.edge x)) = G'.edge (h (G.edge x)) ↔ h (G.edge x) = G'.edge (h x)
  rw [G.plain_eq hG]
  constructor
  · intro e
    rw [e, G'.plain_eq hG']
  · intro e
    rw [e, G'.plain_eq hG']

/-- Coq `preembedding A h`: `h` is a partial embedding of `G` into `G'`, defined on `A`. -/
structure Preembedding (A : Set D) (h : D → D') : Prop where
  /-- Coq `preembedding_face`: `{in A, {morph h : x / face x}}`. -/
  face : ∀ x ∈ A, h (G.face x) = G'.face (h x)
  /-- Coq `preembedding_arity`: `{in A, {mono h : x / order face x}}`. -/
  arity : ∀ x ∈ A, G'.arity (h x) = G.arity x
  /-- Coq `preembedding_cover`: `A \subset fclosure face edge_central`. -/
  cover : A ⊆ fclosure G.face (G.edgeCentral G' h)
  /-- Coq `preembedding_rlinked`: `rlink_connected [predI A & edge_central]`. -/
  rlinked : G.RLinkConnected (A ∩ G.edgeCentral G' h)

/-- Coq `preembedding_simple_path`. -/
theorem preembedding_simple_path [Finite D] {A : Set D} {h : D → D'}
    (hh : G.Preembedding G' A h) (hA : Closed (frel G.face) A) {x y : D} (hx : G.edge x ∈ A)
    (hy : y ∈ A) :
    ∃ p, (path G.rlink x p ∧ G.cface (last x p) y ∧ p ≠ []) ∧
      (G.Simple p ∧ ∀ z ∈ p, z ∈ A ∩ G.edgeCentral G' h) := by
  obtain ⟨z, zcE, exFz⟩ := hh.cover hx
  obtain ⟨t, tcE, yFt⟩ := hh.cover hy
  have Bz : z ∈ A ∩ G.edgeCentral G' h := ⟨(hA.connect_iff exFz).1 hx, zcE⟩
  have Bt : t ∈ A ∩ G.edgeCentral G' h := ⟨(hA.connect_iff yFt).1 hy, tcE⟩
  obtain ⟨p, nfzRp, Bp⟩ := hh.rlinked z Bz t Bt
  have xRp : path G.rlink x (p ++ [t]) := by
    generalize p ++ [t] = l at nfzRp ⊢
    cases l with
    | nil => trivial
    | cons a l =>
      obtain ⟨h1, h2⟩ := nfzRp
      refine ⟨?_, h2⟩
      change G.cface (G.edge (G.node (G.face z))) a at h1
      rw [G.faceK] at h1
      exact connect_trans exFz h1
  obtain ⟨q, ⟨xRq, Uq⟩, Eq, Eq0, sqp⟩ := G.simplify_rlink xRp
  refine ⟨q, ⟨xRq, ?_, fun hq => ?_⟩, Uq, fun u hu => ?_⟩
  · rw [← Eq, last_concat]
    exact G.cfaceC.1 yFt
  · exact List.append_ne_nil_of_right_ne_nil p (List.cons_ne_nil t []) (Eq0.2 hq)
  · rcases List.mem_append.1 (sqp u hu) with hu' | hu'
    · exact Bp u hu'
    · rw [List.mem_singleton.1 hu']
      exact Bt

end Preembedding

end Hypermap

end FourColor
