/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Coloring

/-!
# The cube construction  (port of `cube.v`)

Reduction of the coloring problem to cubic maps; since this is not the inductive case, we can
construct a larger map:

* `G.cube` : a cubic plain hypermap that is planar and bridgeless iff the hypermap `G` is, and
  is four-colorable only if `G` is (Coq `cube G`). Each dart in `G` splits into six darts in
  `G.cube`; there is a face in `G.cube` for each face, node and edge in `G`.
* `CubeTag` : the type of the tag that flags the six different copies of each dart in
  `G.cube` (Coq `cube_tag`); the darts of `G.cube` are the pairs `CubeDart D = CubeTag × D`
  (Coq `cube_dart`).

## Porting notes

* The Coq `cube` is `locked`; here it is a plain definition, with the `rfl` lemmas `cube_edge`,
  `cube_node`, `cube_face`.
* The Coq boolean equations `planar cube = planar G` and `bridgeless cube = bridgeless G` are
  `↔`.
* The section-local Coq definitions and lemmas (`aQe`, `aQn`, `aQf`, `qfAe`, `qfAn`, `qfAf`,
  ...) become private lemmas about the three face classes of the cube: the "edge" faces (tag
  `CTe`), the "node" faces (tag `CTfe`) and the "face" faces (the other four tags). The
  adjunctions used by Coq for the component counts are replaced by direct projections.
-/

namespace FourColor

open Function

universe u

/-- Coq `cube_tag`: the six copies of each dart in the cube construction. -/
inductive CubeTag : Type where
  /-- Coq `CTn`. -/
  | CTn
  /-- Coq `CTen`. -/
  | CTen
  /-- Coq `CTf`. -/
  | CTf
  /-- Coq `CTnf`. -/
  | CTnf
  /-- Coq `CTe`. -/
  | CTe
  /-- Coq `CTfe`. -/
  | CTfe
  deriving DecidableEq, Repr, Inhabited

export CubeTag (CTn CTen CTf CTnf CTe CTfe)

/-- Coq `cube_tag_enum`: an enumeration of the cube tags. -/
def cubeTagEnum : List CubeTag := [CTn, CTen, CTf, CTnf, CTe, CTfe]

/-- Coq `cube_tag_code`: the index of a tag in `cubeTagEnum`. -/
def cubeTagCode : CubeTag → ℕ
  | CTn => 0
  | CTen => 1
  | CTf => 2
  | CTnf => 3
  | CTe => 4
  | CTfe => 5

/-- Coq `cube_tag_codeK`: `cubeTagCode` is a code for the cube tags
(`cancel cube_tag_code (nth CTn cube_tag_enum)`). -/
theorem cube_tag_codeK (o : CubeTag) : cubeTagEnum.getD (cubeTagCode o) CTn = o := by
  cases o <;> rfl

/-- Coq `cube_tag_enumP` (math-comp `Finite.axiom cube_tag_enum`): each tag occurs exactly
once in `cubeTagEnum`. -/
theorem cube_tag_enumP (o : CubeTag) : cubeTagEnum.count o = 1 := by
  cases o <;> decide

/-- The finite type of cube tags (Coq `isFinite.Build cube_tag cube_tag_enumP`). -/
instance : Fintype CubeTag where
  elems := ⟨↑cubeTagEnum, by decide⟩
  complete o := by cases o <;> decide

/-- There are six cube tags. -/
theorem card_cubeTag : Fintype.card CubeTag = 6 := rfl

/-- Coq `cube_dart`: the darts of the cube map, six copies of each dart. -/
abbrev CubeDart (D : Type u) : Type u := CubeTag × D

namespace Hypermap

variable {D : Type u}

section Cube

variable (G : Hypermap D)

/-- Coq `cube_edge`. -/
def cubeEdge : CubeDart D → CubeDart D
  | (CTen, x) => (CTnf, G.edge x)
  | (CTf, x) => (CTe, G.node (G.face x))
  | (CTnf, x) => (CTen, G.node (G.face x))
  | (CTe, x) => (CTf, G.edge x)
  | (CTfe, x) => (CTn, x)
  | (CTn, x) => (CTfe, x)

/-- Coq `cube_node`. -/
def cubeNode : CubeDart D → CubeDart D
  | (CTn, x) => (CTen, G.node x)
  | (CTen, x) => (CTfe, x)
  | (CTf, x) => (CTnf, G.edge x)
  | (CTnf, x) => (CTe, G.node (G.face x))
  | (CTe, x) => (CTf, x)
  | (CTfe, x) => (CTn, G.face (G.edge x))

/-- Coq `cube_face`. -/
def cubeFace : CubeDart D → CubeDart D
  | (CTn, x) => (CTen, x)
  | (CTen, x) => (CTf, x)
  | (CTf, x) => (CTnf, x)
  | (CTnf, x) => (CTn, G.face x)
  | (CTe, x) => (CTe, G.edge x)
  | (CTfe, x) => (CTfe, G.node x)

variable [Finite D]

/-- Coq `cube_cancel3`. -/
theorem cube_cancel3 (u : CubeDart D) : G.cubeNode (G.cubeFace (G.cubeEdge u)) = u := by
  obtain ⟨o, x⟩ := u
  cases o <;> simp [cubeEdge, cubeFace, cubeNode, G.edgeK, G.faceK, G.nodeK]

/-- Coq `cube G`: the cube map of `G`, a plain cubic map with a face for each face, node and
edge of `G`. -/
def cube : Hypermap (CubeDart D) where
  edge := G.cubeEdge
  node := G.cubeNode
  face := G.cubeFace
  edgeK := G.cube_cancel3

@[simp] theorem cube_edge : G.cube.edge = G.cubeEdge := rfl
@[simp] theorem cube_node : G.cube.node = G.cubeNode := rfl
@[simp] theorem cube_face : G.cube.face = G.cubeFace := rfl

/-- Coq `plain_cube`. -/
theorem plain_cube : G.cube.Plain := by
  refine (G.cube.plainP).2 fun u _ => ?_
  obtain ⟨o, x⟩ := u
  cases o <;> simp [cubeEdge, G.edgeK, G.faceK]

/-- Coq `cubic_cube`. -/
theorem cubic_cube : G.cube.Cubic := by
  refine (G.cube.cubicP).2 fun u _ => ?_
  obtain ⟨o, x⟩ := u
  cases o <;> simp [cubeNode, G.edgeK, G.faceK, G.nodeK]

/-! ### The three kinds of faces of the cube

The faces of `G.cube` are of three kinds: the faces of the darts tagged `CTe` follow the edges
of `G` (Coq `aQe`), those of the darts tagged `CTfe` follow the nodes of `G` (Coq `aQn`), and
those of the darts with the other four tags follow the faces of `G` (Coq `aQf`). -/

/-- Coq `qFaQe`: the darts tagged `CTe` form a union of faces. -/
private theorem closed_aQe : Closed (frel G.cube.face) {u : CubeDart D | u.1 = CTe} := by
  rintro ⟨o, x⟩ _ rfl
  cases o <;> simp [cubeFace]

/-- Coq `qFaQn`: the darts tagged `CTfe` form a union of faces. -/
private theorem closed_aQn : Closed (frel G.cube.face) {u : CubeDart D | u.1 = CTfe} := by
  rintro ⟨o, x⟩ _ rfl
  cases o <;> simp [cubeFace]

private theorem cube_face_iter_e (n : ℕ) (x : D) :
    G.cube.face^[n] (CTe, x) = (CTe, G.edge^[n] x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, iterate_succ_apply]; exact ih (G.edge x)

private theorem cube_face_iter_fe (n : ℕ) (x : D) :
    G.cube.face^[n] (CTfe, x) = (CTfe, G.node^[n] x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, iterate_succ_apply]; exact ih (G.node x)

private theorem cube_face_iter_nf (n : ℕ) (x : D) :
    G.cube.face^[4 * n] (CTnf, x) = (CTnf, G.face^[n] x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [show 4 * (n + 1) = 4 * n + 4 by ring, iterate_add_apply, iterate_succ_apply]
    exact ih (G.face x)

/-- Coq `qfAe`: the faces of the `CTe` darts are the edges of `G`. -/
private theorem cube_cface_e (x y : D) : G.cube.cface (CTe, x) (CTe, y) ↔ G.cedge x y := by
  change fconnect G.cube.face (CTe, x) (CTe, y) ↔ fconnect G.edge x y
  rw [fconnect_iff_iterate, fconnect_iff_iterate]
  simp only [cube_face_iter_e, Prod.mk.injEq, true_and]

/-- Coq `qfAn`: the faces of the `CTfe` darts are the nodes of `G`. -/
private theorem cube_cface_fe (x y : D) : G.cube.cface (CTfe, x) (CTfe, y) ↔ G.cnode x y := by
  change fconnect G.cube.face (CTfe, x) (CTfe, y) ↔ fconnect G.node x y
  rw [fconnect_iff_iterate, fconnect_iff_iterate]
  simp only [cube_face_iter_fe, Prod.mk.injEq, true_and]

/-- The darts of a face of the third kind lie over a single face of `G`. -/
private theorem cube_cface_proj {u v : CubeDart D} (hu : u.1 ≠ CTe ∧ u.1 ≠ CTfe)
    (huv : G.cube.cface u v) : G.cface u.2 v.2 := by
  have key : ∀ v, G.cube.cface u v → (v.1 ≠ CTe ∧ v.1 ≠ CTfe) ∧ G.cface u.2 v.2 := by
    intro v huv
    induction huv with
    | refl => exact ⟨hu, connect_refl _⟩
    | @tail w w' _ hbc ih =>
      subst hbc
      obtain ⟨⟨h1, h2⟩, h3⟩ := ih
      obtain ⟨o, y⟩ := w
      cases o
      · exact ⟨⟨by simp [cubeFace], by simp [cubeFace]⟩, h3⟩
      · exact ⟨⟨by simp [cubeFace], by simp [cubeFace]⟩, h3⟩
      · exact ⟨⟨by simp [cubeFace], by simp [cubeFace]⟩, h3⟩
      · exact ⟨⟨by simp [cubeFace], by simp [cubeFace]⟩, connect_trans h3 (fconnect1 _ _)⟩
      · exact (h1 rfl).elim
      · exact (h2 rfl).elim
  exact (key v huv).2

/-- The dart `(o, x)` of a face of the third kind is on the face of `(CTnf, x)`. -/
private theorem cube_cface_nf_self {o : CubeTag} (ho : o ≠ CTe ∧ o ≠ CTfe) (x : D) :
    G.cube.cface (o, x) (CTnf, x) := by
  have f1 : ∀ u, G.cube.cface u (G.cube.face u) := fun u => fconnect1 _ u
  cases o
  · exact connect_trans (f1 _) (connect_trans (f1 _) (f1 (CTf, x)))
  · exact connect_trans (f1 _) (f1 (CTf, x))
  · exact f1 (CTf, x)
  · exact connect_refl _
  · exact (ho.1 rfl).elim
  · exact (ho.2 rfl).elim

/-- Coq `qfAf`: the faces of the third kind are the faces of `G`. -/
private theorem cube_cface_nf (x y : D) : G.cube.cface (CTnf, x) (CTnf, y) ↔ G.cface x y := by
  constructor
  · exact G.cube_cface_proj (u := (CTnf, x)) ⟨nofun, nofun⟩
  · intro h
    obtain ⟨n, rfl⟩ := fconnect_iff_iterate.1 h
    rw [← cube_face_iter_nf]
    exact fconnect_iterate _ _ _

/-- The first two kinds of faces are distinct from the third kind. -/
private theorem cube_cface_tag {u v : CubeDart D} (huv : G.cube.cface u v) :
    (u.1 = CTe ↔ v.1 = CTe) ∧ (u.1 = CTfe ↔ v.1 = CTfe) :=
  ⟨(G.closed_aQe).connect_iff huv, (G.closed_aQn).connect_iff huv⟩

/-! ### Genus, planarity, bridges and colorings of the cube -/

/-- Counting components on the two sides of a closed set. -/
private theorem nComp_inter_diff {α : Type*} [Finite α] {e : α → α → Prop} {a b : Set α}
    (hb : Closed e b) : nComp e a = nComp e (a ∩ b) + nComp e (a \ b) := by
  rw [nComp, nComp, nComp, ← Set.ncard_union_eq]
  · rw [← Set.image_union, Set.inter_union_sdiff]
  · rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have : connect e y x := by
      have : x ∈ comp e y := by rw [hxy]; exact connect_refl x
      exact this
    exact hy.2 ((hb.connect_iff this).2 hx.2)

/-- Components meeting `a` are those meeting a subset `b` of representatives. -/
private theorem nComp_eq_of_rep {α : Type*} {e : α → α → Prop} (hs : ConnectSym e)
    {a b : Set α} (hba : b ⊆ a) (hrep : ∀ x ∈ a, ∃ y ∈ b, connect e x y) :
    nComp e a = nComp e b := by
  unfold nComp
  congr 1
  ext c
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hxy⟩ := hrep x hx
    exact ⟨y, hy, (comp_eq_iff hs).2 (hs _ _ hxy)⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hba hy, rfl⟩

/-- A `glink` step of the cube projects to a (short) `glink` path of `G`. -/
private theorem cube_glink_proj {u v : CubeDart D} (h : G.cube.glink u v) :
    G.gcomp u.2 v.2 := by
  have gE : ∀ x, G.gcomp x (G.edge x) := fun x => connect_of_rel (G.glinkE x)
  have gN : ∀ x, G.gcomp x (G.node x) := fun x => connect_of_rel (G.glinkN x)
  have gF : ∀ x, G.gcomp x (G.face x) := fun x => connect_of_rel (G.glinkF x)
  obtain ⟨o, x⟩ := u
  rcases h with rfl | rfl | rfl <;> cases o <;>
    first
    | exact connect_refl _
    | exact gE x
    | exact gN x
    | exact gF x
    | exact connect_trans (gF x) (gN _)
    | exact connect_trans (gE x) (gF _)

/-- A `glink` step of `G` lifts to a `glink` path of the cube, between `CTnf` darts. -/
private theorem cube_glink_lift {x y : D} (h : G.glink x y) :
    G.cube.gcomp (CTnf, x) (CTnf, y) := by
  have qE : ∀ u, G.cube.gcomp u (G.cube.edge u) := fun u => connect_of_rel (G.cube.glinkE u)
  have qN : ∀ u, G.cube.gcomp u (G.cube.node u) := fun u => connect_of_rel (G.cube.glinkN u)
  have qFF : ∀ {u v}, G.cube.cface u v → G.cube.gcomp u v := fun h => G.cube.gcomp_of_cface h
  rcases h with rfl | rfl | rfl
  · -- `(CTnf, x)` is on the face of `(CTen, x)`, whose edge is `(CTnf, edge x)`
    have h1 := qFF (G.cube_cface_nf_self (o := CTen) ⟨by decide, by decide⟩ x)
    exact connect_trans (G.cube.glinkC _ _ h1) (qE (CTen, x))
  · -- `(CTnf, x)` is on the face of `(CTn, x)`, whose node `(CTen, node x)` is on the face of
    -- `(CTnf, node x)`
    have h1 := qFF (G.cube_cface_nf_self (o := CTn) ⟨by decide, by decide⟩ x)
    have h2 := qFF (G.cube_cface_nf_self (o := CTen) ⟨by decide, by decide⟩ (G.node x))
    exact connect_trans (G.cube.glinkC _ _ h1) (connect_trans (qN (CTn, x)) h2)
  · exact qFF ((G.cube_cface_nf x (G.face x)).2 (fconnect1 _ x))

/-- Coq `cube_colorable`. -/
theorem cube_colorable (h : G.cube.FourColorable) : G.FourColorable := by
  obtain ⟨k, kE, kF⟩ := h
  refine ⟨fun x => k (CTnf, x), fun x e => ?_, fun x => ?_⟩
  · -- `edge (CTen, x) = (CTnf, edge x)`, and `(CTen, x)` is on the face of `(CTnf, x)`
    apply kE (CTen, x)
    have h1 : k (CTf, x) = k (CTen, x) := kF (CTen, x)
    have h2 : k (CTnf, x) = k (CTf, x) := kF (CTf, x)
    show k (CTnf, G.edge x) = k (CTen, x)
    rw [← h1, ← h2]
    exact e
  · have h1 : k (CTnf, G.face x) = k (CTf, G.face x) := kF (CTf, G.face x)
    have h2 : k (CTf, G.face x) = k (CTen, G.face x) := kF (CTen, G.face x)
    have h3 : k (CTen, G.face x) = k (CTn, G.face x) := kF (CTn, G.face x)
    have h4 : k (CTn, G.face x) = k (CTnf, x) := kF (CTnf, x)
    exact h1.trans (h2.trans (h3.trans h4))

/-- Coq `bridgeless_cube`. -/
theorem bridgeless_cube : G.cube.Bridgeless ↔ G.Bridgeless := by
  have hen : ∀ x, G.cube.cface (CTen, x) (CTnf, x) := fun x =>
    G.cube_cface_nf_self ⟨by decide, by decide⟩ x
  constructor
  · rintro hQ ⟨x, hx⟩
    exact hQ ⟨(CTen, x), connect_trans (hen x) ((G.cube_cface_nf x (G.edge x)).2 hx)⟩
  · rintro hG ⟨⟨o, x⟩, hu⟩
    have htag := G.cube_cface_tag hu
    cases o
    · exact nomatch htag.2.2 rfl
    · -- `edge (CTen, x) = (CTnf, edge x)`
      have h1 : G.cube.cface (CTnf, x) (CTnf, G.edge x) :=
        connect_trans (G.cube.cfaceC.1 (hen x)) hu
      exact hG ⟨x, (G.cube_cface_nf x (G.edge x)).1 h1⟩
    · exact nomatch htag.1.2 rfl
    · -- `edge (CTnf, x) = (CTen, node (face x))`, and `edge (node (face x)) = x`
      have h1 : G.cube.cface (CTnf, x) (CTnf, G.node (G.face x)) :=
        connect_trans hu (hen (G.node (G.face x)))
      have h2 := (G.cube_cface_nf x (G.node (G.face x))).1 h1
      refine hG ⟨G.node (G.face x), G.cfaceC.1 ?_⟩
      rw [G.faceK]
      exact h2
    · exact nomatch htag.1.1 rfl
    · exact nomatch htag.2.1 rfl

end Cube

section CubeGenus

variable (G : Hypermap D) [Fintype D]

/-- Coq `genus_cube`. -/
theorem genus_cube : G.cube.genus = G.genus := by
  have hsQ := G.cube.cface_sym
  -- The cube has six darts per dart of `G`, three per edge and two per node.
  have oQ : Fintype.card (CubeDart D) = 6 * Fintype.card D := by
    rw [Fintype.card_prod, card_cubeTag]
  have oEQ : fcard G.cube.edge Set.univ * 2 = Fintype.card (CubeDart D) := by
    rw [fcard_order_set G.cube.edgeI G.plain_cube closed_univ, Set.ncard_univ,
      Nat.card_eq_fintype_card]
  have oNQ : fcard G.cube.node Set.univ * 3 = Fintype.card (CubeDart D) := by
    rw [fcard_order_set G.cube.nodeI G.cubic_cube closed_univ, Set.ncard_univ,
      Nat.card_eq_fintype_card]
  -- The faces of the cube are the edges, nodes and faces of `G`.
  have oFeQ : nComp (frel G.cube.face) {u : CubeDart D | u.1 = CTe} = fcard G.edge Set.univ := by
    have hcod : {u : CubeDart D | u.1 = CTe} ⊆ Set.range (fun x => (CTe, x)) := by
      rintro ⟨o, x⟩ (hu : o = CTe)
      exact ⟨x, by rw [hu]⟩
    rw [nComp_adjunction hsQ G.cedge_sym (fun x => (CTe, x)) hcod
      (fun x y _ _ => (G.cube_cface_e x y).symm)]
    show nComp (frel G.edge) _ = nComp (frel G.edge) Set.univ
    congr 1
    exact Set.eq_univ_of_forall fun _ => rfl
  have oFnQ : nComp (frel G.cube.face) ({u : CubeDart D | u.1 = CTe}ᶜ ∩ {u | u.1 = CTfe}) =
      fcard G.node Set.univ := by
    have hset : ∀ u : CubeDart D, u ∈ {u : CubeDart D | u.1 = CTe}ᶜ ∩ {u | u.1 = CTfe} ↔
        u ∈ {u : CubeDart D | u.1 = CTfe} := fun u =>
      ⟨fun h => h.2, fun (h : u.1 = CTfe) => ⟨(fun h' => nomatch h.symm.trans h'), h⟩⟩
    rw [nComp_congr_set hset]
    have hcod : {u : CubeDart D | u.1 = CTfe} ⊆ Set.range (fun x => (CTfe, x)) := by
      rintro ⟨o, x⟩ (hu : o = CTfe)
      exact ⟨x, by rw [hu]⟩
    rw [nComp_adjunction hsQ G.cnode_sym (fun x => (CTfe, x)) hcod
      (fun x y _ _ => (G.cube_cface_fe x y).symm)]
    show nComp (frel G.node) _ = nComp (frel G.node) Set.univ
    congr 1
    exact Set.eq_univ_of_forall fun _ => rfl
  have oFfQ : nComp (frel G.cube.face) ({u : CubeDart D | u.1 = CTe}ᶜ \ {u | u.1 = CTfe}) =
      fcard G.face Set.univ := by
    have hba : {u : CubeDart D | u.1 = CTnf} ⊆ {u : CubeDart D | u.1 = CTe}ᶜ \ {u | u.1 = CTfe} :=
      fun u (hu : u.1 = CTnf) => ⟨(fun h => nomatch hu.symm.trans h),
        (fun h => nomatch hu.symm.trans h)⟩
    have hrep : ∀ u ∈ {u : CubeDart D | u.1 = CTe}ᶜ \ {u | u.1 = CTfe},
        ∃ v ∈ {u : CubeDart D | u.1 = CTnf}, G.cube.cface u v :=
      fun u hu => ⟨(CTnf, u.2), rfl, G.cube_cface_nf_self ⟨hu.1, hu.2⟩ u.2⟩
    rw [nComp_eq_of_rep hsQ hba hrep]
    have hcod : {u : CubeDart D | u.1 = CTnf} ⊆ Set.range (fun x => (CTnf, x)) := by
      rintro ⟨o, x⟩ (hu : o = CTnf)
      exact ⟨x, by rw [hu]⟩
    rw [nComp_adjunction hsQ G.cface_sym (fun x => (CTnf, x)) hcod
      (fun x y _ _ => (G.cube_cface_nf x y).symm)]
    show nComp (frel G.face) _ = nComp (frel G.face) Set.univ
    congr 1
    exact Set.eq_univ_of_forall fun _ => rfl
  have oFQ : fcard G.cube.face Set.univ = G.eulerRhs := by
    show nComp (frel G.cube.face) Set.univ = G.eulerRhs
    rw [nComp_compl (G.closed_aQe), nComp_inter_diff (a := {u : CubeDart D | u.1 = CTe}ᶜ)
      (G.closed_aQn), oFeQ, oFnQ, oFfQ]
    rfl
  -- The cube has as many components as `G`.
  have oGQ : nComp G.cube.glink Set.univ = nComp G.glink Set.univ := by
    have hrep : ∀ u ∈ (Set.univ : Set (CubeDart D)),
        ∃ v ∈ {u : CubeDart D | u.1 = CTnf}, G.cube.gcomp u v := by
      rintro ⟨o, x⟩ -
      refine ⟨(CTnf, x), rfl, ?_⟩
      cases o
      · exact G.cube.gcomp_of_cface (G.cube_cface_nf_self (o := CTn) ⟨nofun, nofun⟩ x)
      · exact G.cube.gcomp_of_cface (G.cube_cface_nf_self (o := CTen) ⟨nofun, nofun⟩ x)
      · exact G.cube.gcomp_of_cface (G.cube_cface_nf_self (o := CTf) ⟨nofun, nofun⟩ x)
      · exact connect_refl _
      · -- `node (CTe, x) = (CTf, x)`
        exact connect_trans (connect_of_rel (G.cube.glinkN (CTe, x)))
          (G.cube.gcomp_of_cface (G.cube_cface_nf_self (o := CTf) ⟨nofun, nofun⟩ x))
      · -- `edge (CTfe, x) = (CTn, x)`
        exact connect_trans (connect_of_rel (G.cube.glinkE (CTfe, x)))
          (G.cube.gcomp_of_cface (G.cube_cface_nf_self (o := CTn) ⟨nofun, nofun⟩ x))
    have hcod : {u : CubeDart D | u.1 = CTnf} ⊆ Set.range (fun x => (CTnf, x)) := by
      rintro ⟨o, x⟩ (hu : o = CTnf)
      exact ⟨x, by rw [hu]⟩
    have hfun : ∀ x y : D, (CTnf, x) ∈ {u : CubeDart D | u.1 = CTnf} →
        (CTnf, y) ∈ {u : CubeDart D | u.1 = CTnf} →
        (G.gcomp x y ↔ G.cube.gcomp (CTnf, x) (CTnf, y)) := by
      intro x y hx hy
      clear hx hy
      constructor
      · intro h
        induction h with
        | refl => exact connect_refl _
        | tail _ hbc ih => exact connect_trans ih (G.cube_glink_lift hbc)
      · intro h
        have key : ∀ v, G.cube.gcomp (CTnf, x) v → G.gcomp x v.2 := by
          intro v hv
          induction hv with
          | refl => exact connect_refl _
          | tail _ hbc ih => exact connect_trans ih (G.cube_glink_proj hbc)
        exact key _ h
    rw [nComp_eq_of_rep G.cube.glinkC (Set.subset_univ _) hrep,
      nComp_adjunction G.cube.glinkC G.glinkC (fun x => (CTnf, x)) hcod hfun]
    congr 1
    exact Set.eq_univ_of_forall fun _ => rfl
  have hL : G.cube.eulerLhs = 2 * nComp G.glink Set.univ + 6 * Fintype.card D := by
    unfold eulerLhs
    rw [oGQ, oQ]
  have hR : G.cube.eulerRhs =
      fcard G.cube.edge Set.univ + (fcard G.cube.node Set.univ + G.eulerRhs) := by
    rw [← oFQ]
    rfl
  unfold genus
  rw [hL, hR]
  unfold eulerLhs
  omega

/-- Coq `planar_cube`. -/
theorem planar_cube : G.cube.Planar ↔ G.Planar := by
  unfold Planar
  rw [genus_cube]

end CubeGenus

end Hypermap

end FourColor
