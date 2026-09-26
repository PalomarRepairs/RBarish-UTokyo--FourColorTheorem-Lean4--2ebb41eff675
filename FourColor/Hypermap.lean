/-
Copyright (c) 2026. Lean 4 port of the planarity part of the Coq/Rocq formal proof
of the Four Color Theorem by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.FinGraph

/-!
# Hypermaps  (port of `hypermap.v`)

A (finite) hypermap is a triplet of functions `edge`, `node`, `face` over a finite type of
darts, that are mutually inverse in the sense that their composite is the identity:
`node (face (edge x)) = x`.  This data is equivalent to an arbitrary pair of permutations, but
the three function presentation better supports symmetries.  In particular, the
generalizations of the Euler and genus formulae to hypermaps are completely symmetric.

We define:

* `Hypermap D`      : hypermaps with darts in `D` (math-comp `hypermap`; the dart type is a
  parameter here rather than a field, and finiteness is assumed where needed).
* `G.cedge`, `G.cnode`, `G.cface` : the transitive closures of `edge`, `node`, `face`.
* `G.glink x y`     : `y` is the image of `x` by one of the three permutations.
* `G.gcomp`         : the connected components of `glink`.
* `G.clink x y`     : either `x = node y` or `face x = y` (a reverse N-link or an F-link).
* `G.Connected`     : `G` has exactly one `glink` component.
* `G.eulerLhs`      : `2 * (number of components) + (number of darts)`.
* `G.eulerRhs`      : `(number of edges) + (number of nodes) + (number of faces)`.
* `G.genus`         : `(eulerLhs - eulerRhs) / 2`.
* `G.EvenGenus`     : no truncation occurs in the genus formula (always true, see `Jordan.lean`).
* `G.Planar`        : the "Euler formula" planarity condition, `G.genus = 0`.
* `G.MoebiusPath q` : `q` is a Moebius path: a non-trivial duplicate-free C-path `x :: p`
  with additional "cross" N-links from `x` to `p` and from a dart `y` at or before `node x`
  in `p` to the last dart of `p`.
* `G.Jordan`        : the hypermap "Jordan curve theorem" planarity condition: `G` has no
  Moebius paths.
* `G.permN`, `G.permF`, `G.dual`, `G.mirror` : the derived hypermaps, with proofs that they
  preserve connectivity, genus and planarity (and that `dual` and `mirror` preserve the
  Jordan property).

math-comp writes `finv f` for the inverse of an injective function on a finite type.  For
hypermaps these inverses are explicit: `finv edge = node ∘ face`, `finv node = face ∘ edge`,
`finv face = edge ∘ node`; we use these composites directly.
-/

namespace FourColor

open Function

universe u

/-- A hypermap on the dart type `D`: three functions whose composite is the identity
(math-comp `hypermap`, with `edgeK : cancel3 edge node face`). -/
@[ext]
structure Hypermap (D : Type u) where
  /-- The first permutation. -/
  edge : D → D
  /-- The second permutation. -/
  node : D → D
  /-- The third permutation. -/
  face : D → D
  /-- The triangular identity `node ∘ face ∘ edge = id` (math-comp `edgeK`). -/
  edgeK : ∀ x, node (face (edge x)) = x

namespace Hypermap

variable {D : Type u}

/-! ### Basic identities -/

section FiniteMap

variable (G : Hypermap D)

/-- math-comp `edgeI`. -/
theorem edgeI : Injective G.edge := by
  intro x y h
  have := congrArg (fun z => G.node (G.face z)) h
  simpa only [G.edgeK] using this

variable [Finite D]

/-- math-comp `faceK`. -/
theorem faceK (x : D) : G.edge (G.node (G.face x)) = x :=
  (LeftInverse.rightInverse_of_surjective (f := fun y => G.node (G.face y)) (g := G.edge)
    G.edgeK (Finite.injective_iff_surjective.1 G.edgeI)) x

/-- math-comp `faceI`. -/
theorem faceI : Injective G.face := by
  intro x y h
  have := congrArg (fun z => G.edge (G.node z)) h
  simpa only [G.faceK] using this

/-- math-comp `nodeK`. -/
theorem nodeK (x : D) : G.face (G.edge (G.node x)) = x :=
  (LeftInverse.rightInverse_of_surjective (f := fun y => G.edge (G.node y)) (g := G.face)
    G.faceK (Finite.injective_iff_surjective.1 G.faceI)) x

/-- math-comp `nodeI`. -/
theorem nodeI : Injective G.node := by
  intro x y h
  have := congrArg (fun z => G.face (G.edge z)) h
  simpa only [G.nodeK] using this

/-- `x = node y` iff `y = finv node x = face (edge x)`. -/
theorem eq_node_iff {x y : D} : x = G.node y ↔ G.face (G.edge x) = y := by
  constructor
  · rintro rfl; exact G.nodeK y
  · rintro rfl; exact (G.edgeK x).symm

/-- `face x = y` iff `x = finv face y = edge (node y)`. -/
theorem face_eq_iff {x y : D} : G.face x = y ↔ x = G.edge (G.node y) := by
  constructor
  · rintro rfl; exact (G.faceK x).symm
  · rintro rfl; exact G.nodeK y

/-- `edge x = y` iff `x = finv edge y = node (face y)`. -/
theorem edge_eq_iff {x y : D} : G.edge x = y ↔ x = G.node (G.face y) := by
  constructor
  · rintro rfl; exact (G.edgeK x).symm
  · rintro rfl; exact G.faceK y

end FiniteMap

section Orbits

variable (G : Hypermap D)

/-- math-comp `cedge`: the edge cycles. -/
abbrev cedge : D → D → Prop := fconnect G.edge

/-- math-comp `cnode`: the node cycles. -/
abbrev cnode : D → D → Prop := fconnect G.node

/-- math-comp `cface`: the face cycles. -/
abbrev cface : D → D → Prop := fconnect G.face

variable [Finite D]

theorem cedge_sym : ConnectSym (frel G.edge) := fconnect_sym G.edgeI
theorem cnode_sym : ConnectSym (frel G.node) := fconnect_sym G.nodeI
theorem cface_sym : ConnectSym (frel G.face) := fconnect_sym G.faceI

/-- math-comp `cedgeC`. -/
theorem cedgeC {x y : D} : G.cedge x y ↔ G.cedge y x := fconnect_comm G.edgeI
/-- math-comp `cnodeC`. -/
theorem cnodeC {x y : D} : G.cnode x y ↔ G.cnode y x := fconnect_comm G.nodeI
/-- math-comp `cfaceC`. -/
theorem cfaceC {x y : D} : G.cface x y ↔ G.cface y x := fconnect_comm G.faceI

/-- math-comp `same_cedge`. -/
theorem same_cedge {x y : D} (h : G.cedge x y) (z : D) : G.cedge x z ↔ G.cedge y z :=
  G.cedge_sym.same h z
/-- math-comp `same_cnode`. -/
theorem same_cnode {x y : D} (h : G.cnode x y) (z : D) : G.cnode x z ↔ G.cnode y z :=
  G.cnode_sym.same h z
/-- math-comp `same_cface`. -/
theorem same_cface {x y : D} (h : G.cface x y) (z : D) : G.cface x z ↔ G.cface y z :=
  G.cface_sym.same h z

/-- math-comp `cedge1`. -/
theorem cedge1 (x y : D) : G.cedge x y ↔ G.cedge (G.edge x) y := same_fconnect1 G.edgeI x y
/-- math-comp `cedge1r`. -/
theorem cedge1r (x y : D) : G.cedge x y ↔ G.cedge x (G.edge y) := same_fconnect1_r G.edgeI x y
/-- math-comp `cnode1`. -/
theorem cnode1 (x y : D) : G.cnode x y ↔ G.cnode (G.node x) y := same_fconnect1 G.nodeI x y
/-- math-comp `cnode1r`. -/
theorem cnode1r (x y : D) : G.cnode x y ↔ G.cnode x (G.node y) := same_fconnect1_r G.nodeI x y
/-- math-comp `cface1`. -/
theorem cface1 (x y : D) : G.cface x y ↔ G.cface (G.face x) y := same_fconnect1 G.faceI x y
/-- math-comp `cface1r`. -/
theorem cface1r (x y : D) : G.cface x y ↔ G.cface x (G.face y) := same_fconnect1_r G.faceI x y

end Orbits

/-! ### Components -/

section Components

variable (G : Hypermap D)

/-- math-comp `glink`: `y` is the image of `x` by one of the three permutations. -/
def glink (x y : D) : Prop := G.edge x = y ∨ G.node x = y ∨ G.face x = y

theorem glinkE (x : D) : G.glink x (G.edge x) := Or.inl rfl
theorem glinkN (x : D) : G.glink x (G.node x) := Or.inr (Or.inl rfl)
theorem glinkF (x : D) : G.glink x (G.face x) := Or.inr (Or.inr rfl)

/-- math-comp `gcomp`: the connected components of `G`. -/
abbrev gcomp : D → D → Prop := connect G.glink

theorem gcomp_of_cedge {x y : D} (h : G.cedge x y) : G.gcomp x y :=
  connect_mono (fun _ _ hab => Or.inl hab) h
theorem gcomp_of_cnode {x y : D} (h : G.cnode x y) : G.gcomp x y :=
  connect_mono (fun _ _ hab => Or.inr (Or.inl hab)) h
theorem gcomp_of_cface {x y : D} (h : G.cface x y) : G.gcomp x y :=
  connect_mono (fun _ _ hab => Or.inr (Or.inr hab)) h

/-- math-comp `glinkC`. -/
theorem glinkC [Finite D] : ConnectSym G.glink := by
  apply connectSym_of_rev
  rintro x _ (rfl | rfl | rfl)
  · exact G.gcomp_of_cedge ((G.cedgeC).1 (fconnect1 _ x))
  · exact G.gcomp_of_cnode ((G.cnodeC).1 (fconnect1 _ x))
  · exact G.gcomp_of_cface ((G.cfaceC).1 (fconnect1 _ x))

/-- math-comp `connected G`: `G` has exactly one `glink` component. -/
def Connected : Prop := nComp G.glink Set.univ = 1

end Components

/-! ### Genus and planarity -/

section Genus

variable (G : Hypermap D) [Fintype D]

/-- math-comp `Euler_lhs`: `2 * (number of components) + (number of darts)`. -/
noncomputable def eulerLhs : ℕ := 2 * nComp G.glink Set.univ + Fintype.card D

/-- math-comp `Euler_rhs`: `(number of edges) + (number of nodes) + (number of faces)`. -/
noncomputable def eulerRhs : ℕ :=
  fcard G.edge Set.univ + (fcard G.node Set.univ + fcard G.face Set.univ)

/-- math-comp `genus`: the smallest genus of an oriented surface in which `G` embeds. -/
noncomputable def genus : ℕ := (G.eulerLhs - G.eulerRhs) / 2

/-- math-comp `even_genus`: no truncation occurs in the genus formula. -/
def EvenGenus : Prop := G.eulerLhs = 2 * G.genus + G.eulerRhs

/-- math-comp `planar`: the "Euler formula" planarity condition, `G` has genus `0`. -/
def Planar : Prop := G.genus = 0

end Genus

/-! ### Contour links and the Jordan property -/

section Jordan

variable (G : Hypermap D)

/-- math-comp `clink` (in its `clinkP` form): there is either a reverse N-link or an F-link
from `x` to `y`.  math-comp defines `clink := relU (frel (finv node)) (frel face)`. -/
def clink (x y : D) : Prop := x = G.node y ∨ G.face x = y

/-- math-comp `clinkN`. -/
theorem clinkN (x : D) : G.clink (G.node x) x := Or.inl rfl

/-- math-comp `clinkF`. -/
theorem clinkF (x : D) : G.clink x (G.face x) := Or.inr rfl

variable [Finite D]

/-- math-comp `clinkC`. -/
theorem clinkC : ConnectSym G.clink := by
  apply connectSym_of_rev
  rintro x y (rfl | rfl)
  · -- from `y` back to `node y`, following reverse N-links (`finv node = face ∘ edge`)
    have h1 : fconnect (fun a => G.face (G.edge a)) y (G.node y) :=
      (fconnect_inverse (f := G.node) (g := fun a => G.face (G.edge a)) G.nodeK G.edgeK).2
        (fconnect1 _ y)
    exact connect_mono (fun a b hab => Or.inl ((G.eq_node_iff).2 hab)) h1
  · exact connect_mono (fun a b hab => Or.inr hab) ((G.cfaceC).1 (fconnect1 _ x))

theorem gcomp_of_clink {x y : D} (h : G.clink x y) : G.gcomp x y := by
  rcases h with rfl | rfl
  · have h2 : G.glink (G.edge (G.node y)) y := by
      have := G.glinkF (G.edge (G.node y)); rwa [G.nodeK] at this
    exact connect_trans (connect_of_rel (G.glinkE _)) (connect_of_rel h2)
  · exact connect_of_rel (G.glinkF _)

theorem connect_clink_of_glink {x y : D} (h : G.glink x y) : connect G.clink x y := by
  rcases h with rfl | rfl | rfl
  · -- `x = node (face (edge x))`, then back from `face (edge x)` to `edge x`
    have h1 : G.clink x (G.face (G.edge x)) := Or.inl (G.edgeK x).symm
    exact connect_trans (connect_of_rel h1) (G.clinkC _ _ (connect_of_rel (G.clinkF _)))
  · exact G.clinkC _ _ (connect_of_rel (G.clinkN _))
  · exact connect_of_rel (G.clinkF _)

/-- math-comp `clink_glink`. -/
theorem clink_glink (x y : D) : connect G.clink x y ↔ G.gcomp x y :=
  ⟨connect_sub fun _ _ h => G.gcomp_of_clink h, connect_sub fun _ _ h => G.connect_clink_of_glink h⟩

/-- math-comp `connected_clink`. -/
theorem connected_clink (hG : G.Connected) (x y : D) :
    ∃ p, path G.clink x p ∧ last x p = y := by
  rw [← connect_iff_path, G.clink_glink]
  exact connect_of_nComp_eq_one G.glinkC hG (Set.mem_univ x) (Set.mem_univ y)

/-- math-comp `Moebius_path`: `x :: p` is a non-trivial duplicate-free C-path, with
additional "cross" N-links from `x` to `p` and from a dart `y` at or before `node x` in `p`
to the last dart of `p` (i.e. `mem2 p y (node x)` with `node y = last x p`; here
`y = finv node (last x p) = face (edge (last x p))`). -/
def MoebiusPath : List D → Prop
  | [] => False
  | x :: p => (x :: p).Nodup ∧ path G.clink x p ∧ mem2 p (G.face (G.edge (last x p))) (G.node x)

/-- math-comp `Jordan`: the hypermap "Jordan curve theorem" planarity condition,
`G` has no Moebius paths. -/
def Jordan : Prop := ∀ q, ¬ G.MoebiusPath q

end Jordan

/-! ### Derived maps -/

section DerivedMaps

variable (G : Hypermap D) [Finite D]

/-! #### Left permutation (edge → node) -/

/-- math-comp `permN`: the hypermap with permutations `node`, `face`, `edge`. -/
def permN : Hypermap D where
  edge := G.node
  node := G.face
  face := G.edge
  edgeK := G.nodeK

@[simp] theorem permN_edge : G.permN.edge = G.node := rfl
@[simp] theorem permN_node : G.permN.node = G.face := rfl
@[simp] theorem permN_face : G.permN.face = G.edge := rfl

/-- math-comp `gcomp_permN`. -/
theorem gcomp_permN (x y : D) : G.permN.gcomp x y ↔ G.gcomp x y :=
  connect_congr fun a b => by
    show G.node a = b ∨ G.face a = b ∨ G.edge a = b ↔ G.edge a = b ∨ G.node a = b ∨ G.face a = b
    exact or_assoc.symm.trans or_comm

/-- math-comp `connected_permN`. -/
theorem connected_permN : G.permN.Connected ↔ G.Connected := by
  unfold Connected
  rw [nComp_congr G.gcomp_permN]

/-- math-comp `genus_permN`. -/
theorem genus_permN [Fintype D] : G.permN.genus = G.genus := by
  unfold genus eulerLhs eulerRhs
  rw [nComp_congr G.gcomp_permN, permN_edge, permN_node, permN_face]
  omega

/-- math-comp `planar_permN`. -/
theorem planar_permN [Fintype D] : G.permN.Planar ↔ G.Planar := by
  unfold Planar
  rw [genus_permN]

/-! #### Right permutation (edge → face) -/

/-- math-comp `permF`: the hypermap with permutations `face`, `edge`, `node`. -/
def permF : Hypermap D where
  edge := G.face
  node := G.edge
  face := G.node
  edgeK := G.faceK

@[simp] theorem permF_edge : G.permF.edge = G.face := rfl
@[simp] theorem permF_node : G.permF.node = G.edge := rfl
@[simp] theorem permF_face : G.permF.face = G.node := rfl

/-- math-comp `gcomp_permF`. -/
theorem gcomp_permF (x y : D) : G.permF.gcomp x y ↔ G.gcomp x y :=
  connect_congr fun a b => by
    show G.face a = b ∨ G.edge a = b ∨ G.node a = b ↔ G.edge a = b ∨ G.node a = b ∨ G.face a = b
    exact or_comm.trans or_assoc

/-- math-comp `connected_permF`. -/
theorem connected_permF : G.permF.Connected ↔ G.Connected := by
  unfold Connected
  rw [nComp_congr G.gcomp_permF]

/-- math-comp `genus_permF`. -/
theorem genus_permF [Fintype D] : G.permF.genus = G.genus := by
  unfold genus eulerLhs eulerRhs
  rw [nComp_congr G.gcomp_permF, permF_edge, permF_node, permF_face]
  omega

/-- math-comp `planar_permF`. -/
theorem planar_permF [Fintype D] : G.permF.Planar ↔ G.Planar := by
  unfold Planar
  rw [genus_permF]

/-! #### Dual: invert all functions, and transpose node and face -/

/-- math-comp `hypermap_dualP`. -/
theorem dual_edgeK (x : D) : G.edge (G.node (G.face (G.edge (G.node (G.face x))))) = x := by
  rw [G.nodeK (G.face x), G.faceK]

/-- math-comp `dual`: the hypermap with permutations `finv edge = node ∘ face`,
`finv face = edge ∘ node` and `finv node = face ∘ edge`. -/
def dual : Hypermap D where
  edge x := G.node (G.face x)
  node x := G.edge (G.node x)
  face x := G.face (G.edge x)
  edgeK := G.dual_edgeK

@[simp] theorem dual_edge (x : D) : G.dual.edge x = G.node (G.face x) := rfl
@[simp] theorem dual_node (x : D) : G.dual.node x = G.edge (G.node x) := rfl
@[simp] theorem dual_face (x : D) : G.dual.face x = G.face (G.edge x) := rfl

/-- math-comp `clink_dual`. -/
theorem clink_dual (x y : D) : G.dual.clink x y ↔ G.clink x y := by
  show x = G.edge (G.node y) ∨ G.face (G.edge x) = y ↔ x = G.node y ∨ G.face x = y
  exact (or_congr G.face_eq_iff.symm G.eq_node_iff.symm).trans or_comm

/-- math-comp `gcomp_dual`. -/
theorem gcomp_dual (x y : D) : G.dual.gcomp x y ↔ G.gcomp x y := by
  rw [← G.dual.clink_glink, ← G.clink_glink]
  exact connect_congr G.clink_dual

/-- math-comp `connected_dual`. -/
theorem connected_dual : G.dual.Connected ↔ G.Connected := by
  unfold Connected
  rw [nComp_congr G.gcomp_dual]

/-- math-comp `genus_dual`. -/
theorem genus_dual [Fintype D] : G.dual.genus = G.genus := by
  -- `dual` permutes the inverses of `edge`, `face` and `node` (math-comp `fcard_finv`)
  have hE : fcard G.dual.edge Set.univ = fcard G.edge Set.univ :=
    nComp_congr (fun _ _ => fconnect_inverse (f := G.edge) (g := G.dual.edge) G.edgeK G.faceK) _
  have hN : fcard G.dual.node Set.univ = fcard G.face Set.univ :=
    nComp_congr (fun _ _ => fconnect_inverse (f := G.face) (g := G.dual.node) G.faceK G.nodeK) _
  have hF : fcard G.dual.face Set.univ = fcard G.node Set.univ :=
    nComp_congr (fun _ _ => fconnect_inverse (f := G.node) (g := G.dual.face) G.nodeK G.edgeK) _
  unfold genus eulerLhs eulerRhs
  rw [nComp_congr G.gcomp_dual, hE, hN, hF]
  omega

/-- math-comp `planar_dual`. -/
theorem planar_dual [Fintype D] : G.dual.Planar ↔ G.Planar := by
  unfold Planar
  rw [genus_dual]

/-- math-comp `Jordan_dual`: a sanity check on the symmetry of the Jordan property. -/
theorem jordan_dual (hG : G.Jordan) : G.dual.Jordan := by
  rintro (_ | ⟨x, p⟩) hM
  · exact hM
  obtain ⟨Up, xCp, hm⟩ := hM
  replace xCp : path G.clink x p := (path_congr G.clink_dual).1 xCp
  -- in `dual G`, `finv node (last x p) = face (last x p)` and `node x = finv face x`
  rw [dual_edge, dual_face, G.faceK, dual_node] at hm
  generalize Lp : last x p = y at hm
  obtain ⟨p1, s, rfl, hs⟩ := mem2_iff.1 hm
  obtain ⟨p2, p3, rfl, Lp2⟩ := splitPl hs
  rw [last_append, last_cons, last_append, Lp2] at Lp
  rw [path_append, path_cons, path_append, Lp2] at xCp
  obtain ⟨xCp1, hl1, yCp2, xCp3⟩ := xCp
  have Up' : (p3 ++ (G.face y :: p2) ++ x :: p1).Nodup := by
    have hperm : List.Perm ((x :: p1) ++ ((G.face y :: p2) ++ p3))
        ((p3 ++ (G.face y :: p2)) ++ (x :: p1)) :=
      List.perm_append_comm.trans (List.perm_append_comm.append_right _)
    exact hperm.nodup_iff.1 Up
  cases p3 with
  | nil =>
    -- `y = finv face x`, so `face y = x` occurs twice
    rw [last_nil] at Lp
    subst Lp
    rw [G.nodeK] at Up'
    have hx1 : x ∈ [] ++ (x :: p2) := by simp
    have hx2 : x ∈ x :: p1 := List.mem_cons_self
    exact List.disjoint_of_nodup_append Up' hx1 hx2
  | cons z p3 =>
    rw [last_cons] at Lp
    obtain ⟨hz, zCp3⟩ := xCp3
    rcases hl1 with Lp1 | Dy
    · rcases hz with Dnz | Dz
      · -- `z :: p3 ++ (face y :: p2) ++ x :: p1` is a Moebius path of `G`
        apply hG (z :: (p3 ++ (G.face y :: p2) ++ x :: p1))
        have hl3 : last z (p3 ++ (G.face y :: p2)) = G.edge (G.node x) := by
          rw [last_append, Lp, last_cons, Lp2]
        have hl : last z (p3 ++ (G.face y :: p2) ++ x :: p1) = G.node (G.face y) := by
          rw [last_append, last_cons, Lp1]
        refine ⟨Up', ?_, ?_⟩
        · refine path_append.2 ⟨path_append.2 ⟨zCp3, ?_⟩, ?_⟩
          · rw [Lp]
            exact (path_cons _ _ _ _).2 ⟨G.clinkF y, yCp2⟩
          · rw [hl3]
            exact (path_cons _ _ _ _).2 ⟨Or.inr (G.nodeK x), xCp1⟩
        · rw [hl, G.nodeK, ← Dnz, ← Lp2, List.append_assoc, mem2_append]
          exact Or.inr (Or.inr (mem2_cons_self.2 (List.mem_append_left _ (mem_last _ _))))
      · -- `z = face (finv face x) = x` occurs twice
        rw [G.nodeK] at Dz
        subst Dz
        have hx1 : x ∈ (x :: p3) ++ (G.face y :: p2) := by simp
        have hx2 : x ∈ x :: p1 := List.mem_cons_self
        exact List.disjoint_of_nodup_append Up' hx1 hx2
    · -- `last x p1 = y = last z p3` occurs twice
      have Dy' : last x p1 = y := G.faceI Dy
      have hy1 : y ∈ (z :: p3) ++ (G.face y :: p2) := by
        rw [← Lp]; exact List.mem_append_left _ (mem_last z p3)
      have hy2 : y ∈ x :: p1 := by rw [← Dy']; exact mem_last x p1
      exact List.disjoint_of_nodup_append Up' hy1 hy2

/-! #### Mirror: invert node and face in place, garble edge -/

/-- math-comp `hypermap_mirrorP`. -/
theorem mirror_edgeK (x : D) : G.face (G.edge (G.edge (G.node (G.face (G.node x))))) = x := by
  rw [G.faceK (G.node x), G.nodeK]

/-- math-comp `mirror`: the hypermap with permutations `face ∘ node`, `finv node = face ∘ edge`
and `finv face = edge ∘ node`. -/
def mirror : Hypermap D where
  edge x := G.face (G.node x)
  node x := G.face (G.edge x)
  face x := G.edge (G.node x)
  edgeK := G.mirror_edgeK

@[simp] theorem mirror_edge (x : D) : G.mirror.edge x = G.face (G.node x) := rfl
@[simp] theorem mirror_node (x : D) : G.mirror.node x = G.face (G.edge x) := rfl
@[simp] theorem mirror_face (x : D) : G.mirror.face x = G.edge (G.node x) := rfl

/-- math-comp `cnode_mirror`. -/
theorem cnode_mirror (x y : D) : G.mirror.cnode x y ↔ G.cnode x y :=
  fconnect_inverse (f := G.node) (g := G.mirror.node) G.nodeK G.edgeK

/-- math-comp `cface_mirror`. -/
theorem cface_mirror (x y : D) : G.mirror.cface x y ↔ G.cface x y :=
  fconnect_inverse (f := G.face) (g := G.mirror.face) G.faceK G.nodeK

/-- Orbits are transported along a map `φ` that semi-conjugates `f` to `g`. -/
private theorem fconnect_semiconj {α β : Type*} {f : α → α} {g : β → β} (φ : α → β)
    (h : ∀ a, φ (f a) = g (φ a)) {a b : α} (hab : fconnect f a b) :
    fconnect g (φ a) (φ b) := by
  induction hab with
  | refl => exact connect_refl _
  | @tail c d _ hcd ih =>
    have hstep : g (φ c) = φ d := by rw [← h]; exact congrArg φ hcd
    exact Relation.ReflTransGen.tail ih hstep

/-- The mirror edge permutation `face ∘ node` is conjugate by `face` to `finv edge = node ∘ face`,
so `face` maps the `edge`-orbits of `G` onto the `edge`-orbits of `mirror G` (math-comp
`mirror_edge_adj`). -/
private theorem fconnect_mirror_edge (a b : D) :
    fconnect G.mirror.edge (G.face a) (G.face b) ↔ fconnect G.edge a b := by
  rw [← fconnect_inverse (f := G.edge) (g := fun c => G.node (G.face c)) G.edgeK G.faceK]
  constructor
  · intro h
    have h' := fconnect_semiconj (f := G.mirror.edge) (g := fun c => G.node (G.face c))
      (fun c => G.edge (G.node c))
      (fun c => by
        show G.edge (G.node (G.face (G.node c))) = G.node (G.face (G.edge (G.node c)))
        rw [G.faceK, G.edgeK]) h
    simpa only [G.faceK] using h'
  · intro h
    exact fconnect_semiconj (g := G.mirror.edge) G.face (fun _ => rfl) h

/-- math-comp `order_mirror_edge`. -/
theorem order_mirror_edge (x : D) : order G.mirror.edge x = order G.edge (G.node x) := by
  have hset : {y | fconnect G.mirror.edge x y} = G.face '' {y | fconnect G.edge (G.node x) y} := by
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro h
      refine ⟨G.edge (G.node y), ?_, G.nodeK y⟩
      have h' := (fconnect_mirror_edge G (G.edge (G.node x)) (G.edge (G.node y))).1
        (by rw [G.nodeK, G.nodeK]; exact h)
      exact connect_trans (fconnect1 G.edge (G.node x)) h'
    · rintro ⟨b, hb, rfl⟩
      have h' := (fconnect_mirror_edge G (G.edge (G.node x)) b).2 ((G.cedge1 (G.node x) b).1 hb)
      rwa [G.nodeK] at h'
  unfold order
  rw [hset, Set.ncard_image_of_injective _ G.faceI]

/-- math-comp `clink_mirror`. -/
theorem clink_mirror (x y : D) : G.mirror.clink x y ↔ G.clink y x := by
  show x = G.face (G.edge y) ∨ G.edge (G.node x) = y ↔ y = G.node x ∨ G.face y = x
  exact or_congr (eq_comm.trans G.eq_node_iff.symm) (eq_comm.trans G.face_eq_iff.symm)

/-- math-comp `gcomp_mirror`. -/
theorem gcomp_mirror (x y : D) : G.mirror.gcomp x y ↔ G.gcomp x y := by
  rw [← G.mirror.clink_glink, ← G.clink_glink]
  exact (connect_congr G.clink_mirror).trans (connect_flip_iff G.clinkC)

/-- math-comp `connected_mirror`. -/
theorem connected_mirror : G.mirror.Connected ↔ G.Connected := by
  unfold Connected
  rw [nComp_congr G.gcomp_mirror]

/-- math-comp `genus_mirror`. -/
theorem genus_mirror [Fintype D] : G.mirror.genus = G.genus := by
  have hE : fcard G.mirror.edge Set.univ = fcard G.edge Set.univ := by
    have hinj : Injective G.mirror.edge := fun a b h => G.nodeI (G.faceI h)
    have h := nComp_adjunction (a := Set.univ) (fconnect_sym hinj) G.cedge_sym G.face
      (fun y _ => ⟨G.edge (G.node y), G.nodeK y⟩)
      (fun a b _ _ => (fconnect_mirror_edge G a b).symm)
    rw [Set.preimage_univ] at h
    exact h
  have hN : fcard G.mirror.node Set.univ = fcard G.node Set.univ :=
    nComp_congr G.cnode_mirror _
  have hF : fcard G.mirror.face Set.univ = fcard G.face Set.univ :=
    nComp_congr G.cface_mirror _
  unfold genus eulerLhs eulerRhs
  rw [nComp_congr G.gcomp_mirror, hE, hN, hF]

/-- math-comp `planar_mirror`. -/
theorem planar_mirror [Fintype D] : G.mirror.Planar ↔ G.Planar := by
  unfold Planar
  rw [genus_mirror]

/-- math-comp `Jordan_mirror`: the mirror symmetry of the Jordan condition. -/
theorem jordan_mirror (hG : G.Jordan) : G.mirror.Jordan := by
  rintro (_ | ⟨x, q⟩) hM
  · exact hM
  obtain ⟨Up, xCq, hm⟩ := hM
  rcases List.eq_nil_or_concat q with rfl | ⟨p, z, rfl⟩
  · exact hm
  rw [List.concat_eq_append] at Up xCq hm
  -- in `mirror G`, `finv node (last x q) = node z` and `node x = finv node x`
  rw [last_concat, mirror_edge, mirror_face, G.faceK, mirror_node] at hm
  have nz'x : G.face (G.edge x) ∉ [z] := by
    rw [List.mem_singleton]
    intro h
    have hxz : x = G.node z := G.eq_node_iff.2 h
    exact (List.nodup_cons.1 Up).1 (hxz ▸ mem2l hm)
  rw [mem2r_append nz'x] at hm
  obtain ⟨p1, p2, rfl, hfx⟩ := mem2_iff.1 hm
  -- the reversed path `z :: rev (x :: p)` is a Moebius path of `G`
  apply hG (z :: (x :: (p1 ++ G.node z :: p2)).reverse)
  refine ⟨?_, ?_, ?_⟩
  · rw [← List.reverse_concat, List.nodup_reverse, List.cons_append]
    exact Up
  · have h1 : path (fun a b => G.clink b a) x (p1 ++ G.node z :: p2 ++ [z]) :=
      (path_congr G.clink_mirror).1 xCq
    have h2 := (path_reverse (e := G.clink)).2 h1
    rwa [last_concat, belast_concat] at h2
  · have hl : last z (x :: (p1 ++ G.node z :: p2)).reverse = x := by
      rw [List.reverse_cons, last_concat]
    have hsplit : x :: (p1 ++ G.node z :: p2) = (x :: p1) ++ (G.node z :: p2) := rfl
    rw [hl, hsplit, List.reverse_append, mem2_append]
    left
    rw [List.reverse_cons, mem2_append]
    rcases List.mem_cons.1 hfx with h | h
    · rw [h]
      exact Or.inr (Or.inr (mem2_singleton.2 ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inl ⟨List.mem_reverse.2 h, List.mem_singleton_self _⟩)

end DerivedMaps

/-! ### Equal hypermaps

math-comp's `eqm` (extensional equality of hypermaps on the same darts) is plain equality here,
thanks to function extensionality; `eqm_connected`, `eqm_genus`, `eqm_planar` and `eqm_sym`
are therefore immediate. -/

section EqualHypermap

/-- math-comp `dual_inv`. -/
theorem dual_dual [Finite D] (G : Hypermap D) : G.dual.dual = G := by
  refine Hypermap.ext ?_ ?_ ?_ <;> funext x
  · exact congrArg G.edge (G.edgeK x)
  · exact congrArg G.node (G.nodeK x)
  · exact congrArg G.face (G.faceK x)

/-- math-comp `mirror_inv`. -/
theorem mirror_mirror [Finite D] (G : Hypermap D) : G.mirror.mirror = G := by
  refine Hypermap.ext ?_ ?_ ?_ <;> funext x
  · exact congrArg G.edge (G.edgeK x)
  · exact G.faceK (G.node x)
  · exact congrArg G.face (G.edgeK x)

end EqualHypermap

end Hypermap

end FourColor
