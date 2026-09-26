/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfContract.Prog
import FourColor.Coloring
import FourColor.CfMap

/-!
# Configuration contracts (port of `cfcontract.v`, kernel edge transversal)

Recall that in `coloring.v` contracts are represented as lists of darts that form a transversal
of the edges deleted by the contract.  The contract annotation of a configuration represents
this list by a list of indices of the darts in a transversal of all the kernel edges of the map
constructed by the configuration program, `ctrenum cp`.  Out-of-bounds indices are ignored, so
contracts are always off-ring by construction.

The kernel edge transversal lists the edges in the reverse order they become kernel edges
during the construction.  Each `Y` step adds a single edge, the "foot" of the `Y`, except the
initial `Y` step (after this step all edges are still ring edges; this initial `Y` is actually
at the end of the construction program, which is interpreted right-to-left).  Each `H` step
adds three edges: the right and left "feet" of the `H`, and the horizontal crossbar, in that
order, by convention; thus in the (reverse order) list they appear in the "crossbar, left,
right" order.

* `ctrenum cp`     : a transversal sequence of the kernel edges of `cpmap cp` (math-comp
  `ctrenum`).
* `cfcontract cf`  : a transversal of the contract edges of `cfmap cf` (math-comp
  `cfcontract`).
-/

namespace FourColor

open Function CfMap EcpDart Hypermap

/-- math-comp `ctrenum cp`: a transversal sequence of the kernel (non-ring) edges of
`cpmap cp`, in the reverse order of their creation. -/
noncomputable def ctrenum : (cp : Cprog) → List (cpmap cp).D
  | .R _ :: cp => ctrenum cp
  | [.Y] => []
  | .Y :: cp =>
    ((cpmap cp).pointee.node (cpmap cp).pointer :: ctrenum cp).map
      ((cpmap cp).pointee.icpY (cpmap cp).pointer)
  | .H :: cp =>
    ((cpmap cp).pointee.ecpH (cpmap cp).pointer).pointee.face
        ((cpmap cp).pointee.ecpH (cpmap cp).pointer).pointer ::
      ((cpmap cp).pointee.node (cpmap cp).pointer :: (cpmap cp).pointer :: ctrenum cp).map
        ((cpmap cp).pointee.icpH (cpmap cp).pointer)
  | _ => []

/-- `ctrenum` of an `R n` step (by definition). -/
theorem ctrenum_R (n : ℕ) (cp : Cprog) : ctrenum (.R n :: cp) = ctrenum cp := rfl

/-- `ctrenum` of the initial `Y` step (by definition). -/
theorem ctrenum_Y_nil : ctrenum [.Y] = [] := rfl

/-- `ctrenum` of a non-initial `Y` step. -/
theorem ctrenum_Y {cp : Cprog} (h : cp ≠ []) :
    ctrenum (.Y :: cp) =
      ((cpmap cp).pointee.node (cpmap cp).pointer :: ctrenum cp).map
        ((cpmap cp).pointee.icpY (cpmap cp).pointer) := by
  cases cp with
  | nil => exact absurd rfl h
  | cons s cp => rfl

/-- `ctrenum` of an `H` step (by definition). -/
theorem ctrenum_H (cp : Cprog) :
    ctrenum (.H :: cp) =
      ((cpmap cp).pointee.ecpH (cpmap cp).pointer).pointee.face
          ((cpmap cp).pointee.ecpH (cpmap cp).pointer).pointer ::
        ((cpmap cp).pointee.node (cpmap cp).pointer :: (cpmap cp).pointer :: ctrenum cp).map
          ((cpmap cp).pointee.icpH (cpmap cp).pointer) := rfl

/-- math-comp `size_ctrenum`. -/
theorem size_ctrenum (cp : Cprog) : (ctrenum cp).length = ctrmsize cp := by
  induction cp with
  | nil => rfl
  | cons s cp ih =>
    cases s with
    | R n => exact ih
    | Y =>
      cases cp with
      | nil => rfl
      | cons s' cp' =>
        show List.length (α := ((cpmap (s' :: cp')).pointee.ecpY (cpmap (s' :: cp')).pointer).D)
          (List.map _ ((cpmap (s' :: cp')).pointee.node (cpmap (s' :: cp')).pointer ::
            ctrenum (s' :: cp'))) = ctrmsize (s' :: cp') + 1
        rw [List.length_map, List.length_cons, ih]
    | H =>
      show (List.length (α := ((cpmap cp).pointee.ecpH (cpmap cp).pointer).D) (_ :: List.map _
        ((cpmap cp).pointee.node (cpmap cp).pointer :: (cpmap cp).pointer :: ctrenum cp))) =
          ctrmsize cp + 3
      rw [List.length_cons, List.length_map, List.length_cons, List.length_cons, ih]
    | _ => rfl

/-- math-comp `cfcontract cf`: a transversal of the contract edges of `cfmap cf`. -/
noncomputable def cfcontract (cf : Config) : List (cfmap cf).D :=
  mask (cfcontractMask cf) (ctrenum cf.cfprog)

namespace CfContract

section InsertE

variable {D : Type*} (G : Hypermap D)

/-- Membership in `insertE p`, for any hypermap (math-comp `mem_insertE` without plainness). -/
theorem mem_insertE_iff (p : List D) (x : D) :
    x ∈ G.insertE p ↔ ∃ y ∈ p, x = y ∨ x = G.edge y := by
  induction p with
  | nil => simp [insertE]
  | cons y p ih =>
    rw [insertE, List.mem_cons, List.mem_cons, ih]
    simp only [List.mem_cons, exists_eq_or_imp, or_assoc]

/-- `insertE` as a `flatMap`. -/
theorem insertE_eq_flatMap (p : List D) : G.insertE p = p.flatMap fun x => [x, G.edge x] := by
  induction p with
  | nil => rfl
  | cons x p ih => rw [insertE, ih, List.flatMap_cons]; rfl

/-- `insertE` preserves permutations. -/
theorem insertE_perm {p q : List D} (h : p.Perm q) : (G.insertE p).Perm (G.insertE q) := by
  rw [insertE_eq_flatMap, insertE_eq_flatMap]
  exact h.flatMap_right _

/-- `insertE` commutes with a map that commutes with `edge` (math-comp `insertE_icpY`,
`insertE_icpH`, in general form). -/
theorem insertE_map {D' : Type*} (M : Hypermap D') (i : D → D')
    (hi : ∀ x, M.edge (i x) = i (G.edge x))
    (p : List D) : M.insertE (p.map i) = (G.insertE p).map i := by
  induction p with
  | nil => rfl
  | cons x p ih => simp only [List.map_cons, insertE, ih, hi]

/-- Membership in the `insertE` of a list made of darts outside the image of an injection,
followed by a mapped list. -/
theorem mem_insertE_map {D' : Type*} (M : Hypermap D') (i : D → D') (hinj : Function.Injective i)
    (hi : ∀ x, M.edge (i x) = i (G.edge x)) (A : List D')
    (hA : ∀ z ∈ A, ∀ x, i x ≠ z ∧ i x ≠ M.edge z)
    (p : List D) (x : D) : i x ∈ M.insertE (A ++ p.map i) ↔ x ∈ G.insertE p := by
  rw [M.insertE_cat, List.mem_append, insertE_map G M i hi, List.mem_map]
  constructor
  · rintro (h | ⟨y, hy, hxy⟩)
    · obtain ⟨z, hz, h1 | h1⟩ := (CfContract.mem_insertE_iff M A (i x)).1 h
      · exact absurd h1 (hA z hz x).1
      · exact absurd h1 (hA z hz x).2
    · rw [← hinj hxy]; exact hy
  · intro h; exact Or.inr ⟨x, h, rfl⟩

end InsertE

section Darts

variable {D : Type*} [Fintype D] [DecidableEq D] (G : Hypermap D) (x0 : D)

/-- The reference dart of `ecpU x0` is the new dart `X`. -/
theorem ecpU_pointer : (G.ecpU x0).pointer = IcpX := rfl
/-- The reference dart of `ecpY x0` is the new dart `X`. -/
theorem ecpY_pointer : (G.ecpY x0).pointer = IcpX := rfl
/-- The reference dart of `ecpH x0` is the new dart `X`. -/
theorem ecpH_pointer : (G.ecpH x0).pointer = IcpX := rfl
/-- The injection `icpU` (by definition). -/
theorem icpU_eq (x : D) : G.icpU x0 x = Icp x := rfl
/-- The injection `icpY` (by definition). -/
theorem icpY_eq (x : D) : G.icpY x0 x = Icp (Icp x) := rfl
/-- The injection `icpH` (by definition). -/
theorem icpH_eq (x : D) : G.icpH x0 x = Icp (Icp (Icp x)) := rfl

/-- The `node` of the reference dart of `ecpH x0` (for a proper ring). -/
theorem node_ecpH (x0gt1 : G.ProperCpring x0) :
    (G.ecpH x0).pointee.node (G.ecpH x0).pointer = Icp (Icp IcpXe) := by
  show (G.ecpY x0).pointee.ecpNNode (G.ecpY x0).pointer IcpX = _
  rw [ecpNNode, ite_eq_left (G.long_ecpY x0 x0gt1), G.node_ecpY x0]

/-- The face of `edge X` in `ecpH x0` is that of `face (edge x0)` (for a long ring). -/
theorem face_edge_ecpH (x0gt1 : G.ProperCpring x0) (hl : G.LongCpring x0) :
    (G.ecpH x0).pointee.face ((G.ecpH x0).pointee.edge (G.ecpH x0).pointer) =
      G.icpH x0 (G.face (G.edge x0)) := by
  show (G.ecpY x0).pointee.ecpNFace (G.ecpY x0).pointer IcpXe = _
  rw [ecpNFace, ite_eq_left (G.long_ecpY x0 x0gt1), G.face_edge_ecpY x0 x0gt1]
  have h1 : G.edge x0 ≠ G.edge (G.node x0) := fun h => x0gt1 (G.edgeI h)
  have h2 : G.face (G.edge x0) ≠ G.node x0 := hl
  show Icp ((G.ecpUMap x0).ecpNFace IcpX (Icp (Icp (G.edge x0)))) = Icp (Icp (Icp _))
  simp [ecpNFace, ecpUFace, ecpEdge, ecpUNode, h1, h2]

/-- The face of `edge (face X)` in `ecpH x0` is that of `x0`. -/
theorem face_edge_face_ecpH (x0gt1 : G.ProperCpring x0) :
    (G.ecpH x0).pointee.face ((G.ecpH x0).pointee.edge
      ((G.ecpH x0).pointee.face (G.ecpH x0).pointer)) = G.icpH x0 x0 := by
  show (G.ecpY x0).pointee.ecpNFace (G.ecpY x0).pointer (Icp IcpXe) = _
  have h1 : ((G.ecpY x0).pointee.edge ((G.ecpY x0).pointee.face
      ((G.ecpY x0).pointee.edge (G.ecpY x0).pointer))) ≠ IcpXe := by
    rw [G.face_edge_ecpY x0 x0gt1]; simp [icpY_eq, ecpEdge]
  have h2 : (G.ecpY x0).pointee.edge ((G.ecpY x0).pointee.node (G.ecpY x0).pointer) ≠ IcpXe := by
    rw [G.node_ecpY x0]; simp [ecpEdge]
  rw [ecpNFace, ite_eq_right (Ne.symm h1), ite_eq_right (Ne.symm h2)]
  exact congrArg Icp (G.face_edge_ecpY x0 x0gt1)

end Darts

end CfContract

namespace Hypermap

variable {D : Type*} [Fintype D] [DecidableEq D] (G : Hypermap D) (x0 : D)

/-- math-comp `insertE_icpY`. -/
theorem insertE_icpY (p : List D) :
    (G.ecpY x0).pointee.insertE (p.map (G.icpY x0)) = (G.insertE p).map (G.icpY x0) :=
  CfContract.insertE_map G _ _ (fun x => (G.icpY_edge x0 x).symm) p

/-- math-comp `insertE_icpH`. -/
theorem insertE_icpH (p : List D) :
    (G.ecpH x0).pointee.insertE (p.map (G.icpH x0)) = (G.insertE p).map (G.icpH x0) :=
  CfContract.insertE_map G _ _ (fun x => (G.icpH_edge x0 x).symm) p

end Hypermap

/-! ### Helpers on masks and rings -/

namespace CfContract

variable {α β : Type*}

/-- math-comp `size_mask`. -/
theorem length_mask {m : List Bool} {s : List α} (h : m.length = s.length) :
    (mask m s).length = m.countP id := by
  induction s generalizing m with
  | nil => cases m with
    | nil => rfl
    | cons b m => simp at h
  | cons x s ih => cases m with
    | nil => simp at h
    | cons b m =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      cases b <;> simp [ih h]

/-- Rotating by the length of a prefix. -/
theorem rot_append_length (A B : List α) : CfMap.rot A.length (A ++ B) = B ++ A := by
  simp [CfMap.rot]

/-- math-comp `mask_rot`. -/
theorem mask_rot {m : List Bool} {s : List α} (h : m.length = s.length) (n : ℕ) :
    mask (CfMap.rot n m) (CfMap.rot n s) = CfMap.rot ((m.take n).countP id) (mask m s) := by
  rcases Nat.le_total n s.length with hn | hn
  · have h1 : (m.drop n).length = (s.drop n).length := by simp [h]
    have h2 : (m.take n).length = (s.take n).length := by simp [h]
    rw [CfMap.rot, CfMap.rot, mask_cat h1,
      show mask m s = mask (m.take n) (s.take n) ++ mask (m.drop n) (s.drop n) by
        rw [← mask_cat h2, List.take_append_drop, List.take_append_drop],
      ← length_mask h2, rot_append_length]
  · rw [CfMap.rot_oversize hn, CfMap.rot_oversize (h ▸ hn), List.take_of_length_le (h ▸ hn),
      ← length_mask h, CfMap.rot_length]

/-- Membership in a mask of a mapped list. -/
theorem mem_mask_map {f : α → β} {m : List Bool} {s : List α} {z : β} :
    z ∈ mask m (s.map f) ↔ ∃ w ∈ mask m s, f w = z := by
  rw [← map_mask, List.mem_map]

/-- `insertE` membership only depends on membership. -/
theorem mem_insertE_congr {D : Type*} (G : Hypermap D) {p q : List D}
    (h : ∀ x, x ∈ p ↔ x ∈ q)
    (x : D) : x ∈ G.insertE p ↔ x ∈ G.insertE q := by
  rw [CfContract.mem_insertE_iff G, CfContract.mem_insertE_iff G]
  simp only [h]

/-- Contract colorings only depend on the members of the contract. -/
theorem ccColoring_congr {D : Type*} (G : Hypermap D) {p q : List D}
    (h : ∀ x, x ∈ p ↔ x ∈ q)
    {k : D → Color} (hk : G.CcColoring p k) : G.CcColoring q k :=
  ⟨fun x => (hk.1 x).trans (mem_insertE_congr G h x), hk.2⟩

/-- The restriction of a contract coloring along an injection that commutes with `edge` and
preserves faces, for contracts whose members are either images or darts that are neither
images nor edges of images. -/
theorem ccColoring_restrict {D D' : Type*} [Finite D'] {G : Hypermap D} {M : Hypermap D'}
    (i : D → D') (hinj : Function.Injective i) (hiE : ∀ x, M.edge (i x) = i (G.edge x))
    (hiF : ∀ x, M.cface (i x) (i (G.face x))) {cc' : List D'} {cc : List D} {A : List D'}
    (hA : ∀ z ∈ A, ∀ x, i x ≠ z ∧ i x ≠ M.edge z)
    (h1 : ∀ z ∈ cc', z ∈ A ∨ ∃ w ∈ cc, z = i w)
    (h2 : ∀ w ∈ cc, i w ∈ cc') {k : D' → Color} (hk : M.CcColoring cc' k) :
    G.CcColoring cc (k ∘ i) := by
  refine ⟨fun x => ?_, fun x => (M.cc_coloring_cface hk (hiF x)).symm⟩
  show k (i (G.edge x)) = k (i x) ↔ _
  rw [← hiE, hk.1 (i x), CfContract.mem_insertE_iff M, CfContract.mem_insertE_iff G]
  constructor
  · rintro ⟨z, hz, hxz⟩
    rcases h1 z hz with hzA | ⟨w, hw, rfl⟩
    · rcases hxz with e | e
      · exact absurd e (hA z hzA x).1
      · exact absurd e (hA z hzA x).2
    · refine ⟨w, hw, ?_⟩
      rcases hxz with e | e
      · exact Or.inl (hinj e)
      · rw [hiE] at e; exact Or.inr (hinj e)
  · rintro ⟨w, hw, e | e⟩
    · exact ⟨i w, h2 w hw, Or.inl (by rw [e])⟩
    · exact ⟨i w, h2 w hw, Or.inr (by rw [e, hiE])⟩

/-- The shape of the contracts of `Y` and `H` steps: the new darts `n1`, `n2` (selected by
`b1`, `b2`) and `N` (selected by `B`), and the images of the contract `cc` of the previous map. -/
theorem mem_shape (i : α → β) (b1 b2 : Bool) (n1 n2 : β) (mr mc bP B : List Bool)
    (L e P : List α)
    (N : List β) (hB : B.length = N.length) (hP : bP.length = P.length) (z : β) :
    z ∈ mask (b1 :: b2 :: mr) (n1 :: n2 :: L.map i) ++
        mask (B ++ bP ++ mc) (N ++ (P ++ e).map i) ↔
      z ∈ mask [b1, b2] [n1, n2] ++ mask B N ∨
        z ∈ (mask (bP ++ mr) (P ++ L) ++ mask mc e).map i := by
  have e1 : mask (b1 :: b2 :: mr) (n1 :: n2 :: L.map i) =
      mask [b1, b2] [n1, n2] ++ mask mr (L.map i) :=
    mask_cat (m1 := [b1, b2]) (s1 := [n1, n2]) rfl
  have e2 : mask (B ++ bP ++ mc) (N ++ (P ++ e).map i) =
      mask B N ++ (mask bP (P.map i) ++ mask mc (e.map i)) := by
    rw [List.append_assoc, mask_cat hB, List.map_append, mask_cat (by simp [hP])]
  rw [e1, e2, mask_cat hP, ← map_mask, ← map_mask, ← map_mask]
  simp only [List.mem_append, List.map_append]
  tauto

/-- Membership in the `insertE` of a contract of the shape of `mem_shape`, for a dart that is
neither an image nor the image of an edge. -/
theorem mem_insertE_new {D D' : Type*} {G : Hypermap D} {M : Hypermap D'} (i : D → D')
    (hiE : ∀ x, M.edge (i x) = i (G.edge x)) {cc' A : List D'} {cc : List D}
    (hcc : ∀ y, y ∈ cc' ↔ y ∈ A ∨ y ∈ cc.map i) {z : D'}
    (hz : ∀ x, z ≠ i x ∧ z ≠ i (G.edge x)) :
    z ∈ M.insertE cc' ↔ z ∈ M.insertE A := by
  rw [CfContract.mem_insertE_iff M, CfContract.mem_insertE_iff M]
  constructor
  · rintro ⟨y, hy, hzy⟩
    rcases (hcc y).1 hy with hy | hy
    · exact ⟨y, hy, hzy⟩
    · obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy
      rw [hiE] at hzy
      rcases hzy with e | e
      · exact absurd e (hz w).1
      · exact absurd e (hz w).2
  · rintro ⟨y, hy, hzy⟩
    exact ⟨y, (hcc y).2 (Or.inl hy), hzy⟩

variable {D : Type*} [Finite D] (G : Hypermap D)

/-- The ring as a path of `node⁻¹`, closed back to its head. -/
theorem ring_path (x0 : D) :
    path (fun a b => G.node b = a) (G.node x0) ((G.cpring x0).tail ++ [G.node x0]) := by
  have hc : cycle (frel G.node) (G.cpring x0).reverse := G.cycle_rev_cpring x0
  rw [G.head_cpring x0, List.reverse_cons, cycle_iff_path (G.node x0), last_concat] at hc
  have := (path_reverse (e := frel G.node) (x := G.node x0)
    (p := (G.cpring x0).tail ++ [G.node x0])).1
  rw [last_concat, belast_concat, List.reverse_cons] at this
  exact this hc

/-- The third item of the ring is `face (edge x0)` (or the ring has only two items and
`face (edge x0) = node x0`). -/
theorem headD_drop2 (x0 : D) {β : Type*} (h : D → β) :
    (((G.cpring x0).drop 2).map h).headD (h (G.node x0)) = h (G.face (G.edge x0)) := by
  by_cases hl : G.LongCpring x0
  · rw [G.head_long_cpring x0 hl]
    rfl
  · have h1 : G.face (G.edge x0) = G.node x0 := not_not.1 hl
    have hle : (G.cpring x0).length ≤ 2 := not_lt.1 ((G.size_long_cpring x0).not.1 hl)
    rw [List.drop_eq_nil_of_le hle, h1]
    rfl

/-- Contracted ring edges: along a `node⁻¹` path, a coloring invariant on the faces and on the
contracted edges gives its first uncontracted dart the color of the first dart (or of the end of
the path if all the darts are contracted). -/
theorem chain (h : D → Color) (hF : ∀ x, h (G.face x) = h x) :
    ∀ (p : List D) (x z : D) (m : List Bool), path (fun a b => G.node b = a) x (p ++ [z]) →
      m.length = p.length + 1 → (∀ w ∈ mask m (x :: p), h (G.edge w) = h w) →
      h x = ((mask (m.map not) (x :: p)).map h).headD (h z) := by
  intro p
  induction p with
  | nil =>
    intro x z m hp hm hE
    match m, hm with
    | [b], _ =>
      cases b
      · rfl
      · simp only [List.nil_append, path_cons, path_nil, and_true] at hp
        have := hE x (by simp)
        simp only [List.map_cons, List.map_nil, Bool.not_true, mask_false_cons, mask_nil_right,
          List.headD_nil]
        rw [← this, ← hF (G.edge x), ← hp, G.nodeK]
  | cons y p ih =>
    intro x z m hp hm hE
    match m, hm with
    | b :: m', hm =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hm
      cases b
      · rfl
      · simp only [List.cons_append, path_cons] at hp
        have hx := hE x (by simp)
        simp only [List.map_cons, Bool.not_true, mask_false_cons]
        rw [← ih y z m' hp.2 hm (fun w hw => hE w (by simp [hw])), ← hx, ← hF (G.edge x),
          ← hp.1,
          G.nodeK]

/-- The ring of the map of the program `[Y]`. -/
theorem cpring_ecpY_cpmap0 :
    (cpmap0.ecpY true).pointee.cpring (cpmap0.ecpY true).pointer =
      [Icp IcpXe, IcpX, Icp (Icp true)] := by
  rw [cpring_ecpY, cpring0, node_ecpY]
  rfl

end CfContract

/-- math-comp `uniq_ctrenum`: the ring and the kernel edge transversal of a configuration map
list all its edges exactly once. -/
theorem uniq_ctrenum {cp : Cprog} (h : configProg cp) :
    ((cpmap cp).pointee.insertE
      ((cpmap cp).pointee.cpring (cpmap cp).pointer ++ ctrenum cp)).Nodup := by
  induction cp with
  | nil => simp [configProg] at h
  | cons s cp ih =>
    set G := (cpmap cp).pointee with hG
    set x0 := (cpmap cp).pointer with hx0
    cases s with
    | R n =>
      show (G.insertE ((G.ecpR n x0).pointee.cpring (G.ecpR n x0).pointer ++ ctrenum cp)).Nodup
      rw [cpring_ecpR]
      refine (CfContract.insertE_perm G ?_).nodup_iff.2 (ih h)
      refine List.Perm.append_right _ ?_
      rw [CfMap.rot]
      exact List.perm_append_comm.trans (by rw [List.take_append_drop])
    | Y =>
      cases cp with
      | nil =>
        show ((cpmap0.ecpY true).pointee.insertE
          ((cpmap0.ecpY true).pointee.cpring (cpmap0.ecpY true).pointer ++
            ([] : List (cpmap0.ecpY true).D))).Nodup
        rw [cpring_ecpY, cpring0, node_ecpY]
        decide
      | cons s' cp' =>
        have ih' := ih h
        show ((G.ecpY x0).pointee.insertE ((G.ecpY x0).pointee.cpring (G.ecpY x0).pointer ++
          (G.node x0 :: ctrenum (s' :: cp')).map (G.icpY x0))).Nodup
        rw [cpring_ecpY, node_ecpY, List.cons_append, List.cons_append, ← List.map_append]
        simp only [insertE]
        rw [G.insertE_icpY]
        have hperm : ((G.cpring x0).tail ++ G.node x0 :: ctrenum (s' :: cp')).Perm
            (G.cpring x0 ++ ctrenum (s' :: cp')) := by
          conv_rhs => rw [G.head_cpring x0]
          exact List.perm_middle
        have hnd := ((CfContract.insertE_perm G hperm).nodup_iff.2 ih').map (G.icpY_inj x0)
        simp [List.nodup_cons, hnd, ecpEdge]
    | H =>
      have hcub := config_prog_cubic (show configProg cp from h)
      have hp := cpmap_proper hcub
      have ih' := ih h
      show ((G.ecpH x0).pointee.insertE ((G.ecpH x0).pointee.cpring (G.ecpH x0).pointer ++
        ((G.ecpH x0).pointee.face (G.ecpH x0).pointer ::
          (G.node x0 :: x0 :: ctrenum cp).map (G.icpH x0)))).Nodup
      rw [G.cpring_ecpH x0 hp, CfContract.node_ecpH G x0 hp, face_ecpH, List.cons_append,
        List.cons_append]
      simp only [insertE]
      rw [insertE_cat]
      simp only [insertE]
      rw [G.insertE_icpH, G.insertE_icpH]
      refine ((((List.perm_middle.trans (List.Perm.cons _ List.perm_middle)).cons _).cons _).cons
        _ |>.cons _).nodup_iff.2 ?_
      rw [← List.map_append]
      have hperm2 : ((G.cpring x0).drop 2 ++ (G.node x0 :: x0 :: ctrenum cp)).Perm
          (G.cpring x0 ++ ctrenum cp) := by
        conv_rhs => rw [G.head_proper_cpring x0 hp]
        exact List.perm_middle.trans (List.Perm.cons _ List.perm_middle)
      have hnd := ((CfContract.insertE_perm G hperm2).nodup_iff.2 ih').map (G.icpH_inj x0)
      rw [G.insertE_cat, List.map_append] at hnd
      simp [List.nodup_cons, hnd, ecpEdge]
    | _ => simp [configProg] at h

end FourColor
