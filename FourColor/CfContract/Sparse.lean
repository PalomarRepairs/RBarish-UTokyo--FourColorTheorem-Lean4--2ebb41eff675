/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfContract.Enum

/-!
# Configuration contracts (port of `cfcontract.v`, `sparse_cfctr`)

`sparse_cfctr`: if `cfctr mr mc cp` succeeds, the contract selected by `mr` (on the ring, via
the `edge`s of the ring darts) and `mc` (on the kernel edge transversal `ctrenum cp`), together
with the reference dart of `cpmap cp`, is sparse (node-simple).

The proof is by induction on `cp`, one lemma per construction step (`sparseCtr_R`,
`sparseCtr_Y0`, `sparseCtr_Y`, `sparseCtr_H`).  For the `Y` and `H` steps, we first show that
the reference dart, the new node(s) of the step and the images of the contract of the previous
map form a sparse list (math-comp's `sparse (pointer :: map icp (...))`), then that the contract
of the new map is a sub-permutation of this list up to node classes.
-/

namespace FourColor

open Function CfMap EcpDart Hypermap

namespace CfContract

variable {α : Type*}

/-- A sub-permutation of a list without duplicates has no duplicates. -/
theorem nodup_of_subperm {l₁ l₂ : List α} (h : l₁.Subperm l₂) (h2 : l₂.Nodup) :
    l₁.Nodup := by
  obtain ⟨l, hl, hs⟩ := List.subperm_iff.1 h
  exact (hl.nodup_iff.2 h2).sublist hs

variable {D : Type*} [Fintype D] [DecidableEq D] (G : Hypermap D)

omit [DecidableEq D] in
/-- Darts in the same node have the same node root. -/
theorem froot_node_eq {x y : D} (h : G.cnode x y) : froot G.node x = froot G.node y :=
  (root_eq_iff G.cnode_sym).2 h

omit [DecidableEq D] in
/-- math-comp `sparse` as a pairwise condition. -/
theorem sparse_iff_pairwise (p : List D) :
    G.Sparse p ↔ p.Pairwise (fun a b => ¬ G.cnode a b) := by
  unfold Sparse
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact List.Pairwise.iff (fun a b => by rw [Ne, root_eq_iff G.cnode_sym])

omit [Fintype D] [DecidableEq D] in
/-- Sparseness is transferred by a sub-permutation of the node roots. -/
theorem sparse_of_subperm {p q : List D}
    (h : (p.map (froot G.node)).Subperm (q.map (froot G.node))) (hq : G.Sparse q) : G.Sparse p :=
  nodup_of_subperm h hq

omit [Fintype D] [DecidableEq D] in
/-- The empty list is sparse. -/
theorem sparse_nil : G.Sparse [] := List.nodup_nil

/-- The rotation `CfMap.rot` is a permutation. -/
theorem perm_rot (n : ℕ) (l : List α) : (CfMap.rot n l).Perm l := by
  rw [CfMap.rot]
  exact List.perm_append_comm.trans (by rw [List.take_append_drop])

end CfContract

namespace CfContract

/-- The statement of `sparse_cfctr` for the program `cp` (for the induction). -/
def SparseCtr (cp : Cprog) : Prop :=
  ∀ (mr mc : List Bool), mr.length = cprsize cp → mc.length = ctrmsize cp →
    ∀ cpc, cfctr mr mc cp = some cpc →
      (cpmap cp).pointee.Sparse ((cpmap cp).pointer ::
        ((mask mr ((cpmap cp).pointee.cpring (cpmap cp).pointer)).map (cpmap cp).pointee.edge ++
          (cpmap cp).pointee.insertE (mask mc (ctrenum cp))))

/-- `sparse_cfctr` for an `R n` step. -/
theorem sparseCtr_R (n : ℕ) {cp : Cprog} (ih : SparseCtr cp) : SparseCtr (.R n :: cp) := by
  intro mr mc hmr hmc cpc h
  set G := (cpmap cp).pointee with hG
  set x0 := (cpmap cp).pointer with hx0
  show G.Sparse ((G.ecpR n x0).pointer ::
    ((mask mr ((G.ecpR n x0).pointee.cpring (G.ecpR n x0).pointer)).map G.edge ++
      G.insertE (mask mc (ctrenum cp))))
  rw [cfctr_R] at h
  obtain ⟨cpc0, hc0, -⟩ := Option.map_eq_some_iff.1 h
  have hmr' : mr.length = cprsize cp := hmr
  have hlen : (CfMap.rotr n mr).length = (G.cpring x0).length := by
    rw [CfMap.length_rotr, size_ring_cpmap]; exact hmr'
  have IH := ih (CfMap.rotr n mr) mc (by rw [CfMap.length_rotr]; exact hmr') hmc cpc0 hc0
  refine sparse_of_subperm G (List.Perm.subperm ?_) IH
  rw [cpring_ecpR, List.map_cons, List.map_cons,
    froot_node_eq G (G.cnodeC.1 (fconnect_iterate G.node x0 _))]
  refine List.Perm.cons _ (List.Perm.map _ (List.Perm.append_right _ (List.Perm.map _ ?_)))
  conv_lhs => rw [← CfMap.rot_rotr n mr]
  rw [mask_rot (by rw [hlen]) n]
  exact perm_rot _ _

/-- `sparse_cfctr` for the initial `Y` step. -/
theorem sparseCtr_Y0 : SparseCtr [.Y] := by
  intro mr mc hmr hmc cpc h
  have hmr' : mr.length = 3 := hmr
  have hmc' : mc.length = 0 := hmc
  set M := (cpmap0.ecpY true).pointee with hM
  show M.Sparse ((cpmap0.ecpY true).pointer ::
    ((mask mr (M.cpring (cpmap0.ecpY true).pointer)).map M.edge ++
      M.insertE (mask mc ([] : List (cpmap0.ecpY true).D))))
  have hmem : ∀ u, M.cnode IcpX u ↔ u ∈ [Icp IcpXe, IcpX, Icp (Icp true)] := fun u => by
    rw [← cpring_ecpY_cpmap0]; exact (M.mem_cpring _).symm
  rw [cpring_ecpY_cpmap0, ecpY_pointer]
  have hE1 : M.edge (Icp IcpXe) = Icp IcpX := rfl
  have hE2 : M.edge IcpX = IcpXe := rfl
  have hE3 : M.edge (Icp (Icp true)) = Icp (Icp false) := rfl
  match mr, mc, hmr', hmc' with
  | [b1, b2, b3], [], _, _ =>
    rw [cfctr_Y_nil] at h
    by_cases hnsp : nsp b1 b2 b3 = true
    · rw [ite_eq_left hnsp] at h; cases h
    cases b1 <;> cases b2 <;> cases b3 <;> simp [nsp] at hnsp <;>
      simp [M.sparse_cons, hmem, insertE, sparse_nil, hE1, hE2, hE3]

section StepY

variable {s : Cpstep} {cp : Cprog}

/-- `sparse_cfctr` for a non-initial `Y` step. -/
theorem sparseCtr_Y (ih : SparseCtr (s :: cp)) : SparseCtr (.Y :: s :: cp) := by
  intro mr mc hmr hmc cpc h
  set G := (cpmap (s :: cp)).pointee with hG
  set x0 := (cpmap (s :: cp)).pointer with hx0
  show (G.ecpY x0).pointee.Sparse ((G.ecpY x0).pointer ::
    ((mask mr ((G.ecpY x0).pointee.cpring (G.ecpY x0).pointer)).map (G.ecpY x0).pointee.edge ++
      (G.ecpY x0).pointee.insertE (mask mc ((G.node x0 :: ctrenum (s :: cp)).map (G.icpY x0)))))
  have hcp : configProg (s :: cp) := by have := cfctr_config_prog h; exact this
  have hp : G.ProperCpring x0 := cpmap_proper (config_prog_cubic hcp)
  set M := (G.ecpY x0).pointee with hM
  set i := G.icpY x0 with hi
  set e := ctrenum (s :: cp) with he
  set t := (G.cpring x0).tail with ht
  have hr : G.cpring x0 = G.node x0 :: t := G.head_cpring x0
  have hmemX : ∀ u, M.cnode IcpX u ↔ u ∈ Icp IcpXe :: IcpX :: t.map i := fun u => by
    rw [← G.node_ecpY x0, ← ecpY_pointer G x0, ← cpring_ecpY]
    exact (M.mem_cpring _).symm
  rw [cpring_ecpY, node_ecpY, ecpY_pointer, ← ht, ← hi]
  have hlen : (G.cpring x0).length = cprsize (s :: cp) := size_ring_cpmap _
  rcases mr with _ | ⟨b1, _ | ⟨b2, mr⟩⟩
  · simp [cprsize] at hmr
  · simp only [cprsize, List.length_cons, List.length_nil] at hmr
    have := (G.size_proper_cpring x0).1 hp
    omega
  rcases mc with _ | ⟨b3, mc⟩
  · simp [ctrmsize] at hmc
  have hmr' : (b3 :: mr).length = cprsize (s :: cp) := by
    simp only [cprsize, List.length_cons] at hmr ⊢; omega
  have hmc' : mc.length = ctrmsize (s :: cp) := by
    simp only [ctrmsize, List.length_cons] at hmc ⊢; omega
  rw [cfctr_Y_cons] at h
  by_cases hnsp : nsp b1 b2 b3 = true
  · rw [ite_eq_left hnsp] at h; cases h
  rw [ite_eq_right hnsp] at h
  obtain ⟨cpc0, hc0, -⟩ := Option.map_eq_some_iff.1 h
  have IH := ih (b3 :: mr) mc hmr' hmc' cpc0 hc0
  change G.Sparse (x0 :: ((mask (b3 :: mr) (G.cpring x0)).map G.edge ++ G.insertE (mask mc e)))
    at IH
  rw [hr] at IH
  set p := (mask (b3 :: mr) (G.node x0 :: t)).map G.edge ++ G.insertE (mask mc e) with hpdef
  rw [G.sparse_cons] at IH
  obtain ⟨hr'p, hsp⟩ := IH
  have hoff : ∀ y ∈ p, y ∉ G.cpring x0 := fun y hy hyr =>
    hr'p ⟨y, hy, (G.mem_cpring x0).1 hyr⟩
  have hcn : ∀ y, y ∉ G.cpring x0 → ∀ z, M.cnode (i y) (i z) ↔ G.cnode y z :=
    fun y hy z => cnode_injcp (cp1 := [.Y]) rfl (s :: cp) y hy z
  have hnd := G.cpring_uniq x0
  rw [hr] at hnd
  -- the reference dart, the new node, and the images of the previous contract
  have hKL : M.Sparse (IcpX :: i (G.node x0) :: p.map i) := by
    rw [M.sparse_cons, M.sparse_cons]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨u, hu, hXu⟩
      rw [hmemX] at hXu
      simp only [List.mem_cons, List.mem_map] at hu hXu
      rcases hu with rfl | ⟨y, hy, rfl⟩
      · rcases hXu with h1 | h1 | ⟨z, hz, h1⟩
        · simp [hi, icpY_eq] at h1
        · simp [hi, icpY_eq] at h1
        · rw [G.icpY_inj x0 h1] at hz; exact (List.nodup_cons.1 hnd).1 hz
      · rcases hXu with h1 | h1 | ⟨z, hz, h1⟩
        · simp [hi, icpY_eq] at h1
        · simp [hi, icpY_eq] at h1
        · rw [G.icpY_inj x0 h1] at hz
          exact hoff y hy (by rw [hr]; exact List.mem_cons_of_mem _ hz)
    · rintro ⟨u, hu, h⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hu
      have h2 := (hcn y (hoff y hy) _).1 (M.cnodeC.1 h)
      exact hoff y hy ((G.mem_cpring x0).2 (connect_trans (fconnect1 _ _) (G.cnodeC.1 h2)))
    · rw [sparse_iff_pairwise, List.pairwise_map]
      rw [sparse_iff_pairwise] at hsp
      exact hsp.imp_of_mem (fun {a b} ha _ hab h' => hab ((hcn a (hoff a ha) b).1 h'))
  -- the node classes of the new contract edges
  have hF1 : froot M.node (M.edge (Icp IcpXe)) = froot M.node (i (G.node x0)) := by
    refine froot_node_eq M (connect_trans (fconnect1 _ _) ?_)
    have : M.node (M.edge (Icp IcpXe)) = IcpXe := by
      show (G.ecpUMap x0).ecpNNode IcpX (Icp IcpX) = IcpXe
      simp [ecpNNode]
    rw [this]
    exact fconnect1 _ _
  have hF2 : froot M.node (M.edge IcpX) = froot M.node (i (G.node x0)) :=
    froot_node_eq M (fconnect1 _ _)
  have hME : (mask mr (t.map i)).map M.edge = ((mask mr t).map G.edge).map i := by
    rw [← map_mask, List.map_map, List.map_map]; rfl
  have hKE : M.insertE (mask mc (e.map i)) = (G.insertE (mask mc e)).map i := by
    rw [← map_mask]; exact G.insertE_icpY x0 _
  have hEi : ∀ y, M.edge (i y) = i (G.edge y) := fun y => rfl
  refine sparse_of_subperm M ?_ hKL
  rw [hpdef, List.map_append]
  cases b1 <;> cases b2 <;> cases b3 <;> simp [nsp] at hnsp <;>
    simp only [mask_true_cons, mask_false_cons, List.map_cons, List.cons_append, insertE, hME,
      hKE, hF1, hF2, hEi, List.map_append]
  · -- `(F, F, F)`
    exact (List.Sublist.cons_cons _ (List.Sublist.cons _ (List.Sublist.refl _))).subperm
  · -- `(F, F, T)`
    exact (List.Perm.cons _ (List.perm_middle.trans (List.Perm.cons _ List.perm_middle))).subperm
  · -- `(F, T, F)`
    exact List.Subperm.refl _
  · -- `(T, F, F)`
    exact List.Subperm.refl _

end StepY

section StepH

variable {cp : Cprog}

/-- Moving two items out of the middle of a list. -/
theorem perm_middle2 {β : Type*} (a b : β) (L1 L2 : List β) :
    (L1 ++ a :: b :: L2).Perm (a :: b :: (L1 ++ L2)) :=
  List.perm_middle.trans (List.Perm.cons _ List.perm_middle)

/-- `sparse_cfctr` for an `H` step. -/
theorem sparseCtr_H (ih : SparseCtr cp) : SparseCtr (.H :: cp) := by
  intro mr mc hmr hmc cpc h
  set G := (cpmap cp).pointee with hG
  set x0 := (cpmap cp).pointer with hx0
  show (G.ecpH x0).pointee.Sparse ((G.ecpH x0).pointer ::
    ((mask mr ((G.ecpH x0).pointee.cpring (G.ecpH x0).pointer)).map (G.ecpH x0).pointee.edge ++
      (G.ecpH x0).pointee.insertE (mask mc ((G.ecpH x0).pointee.face (G.ecpH x0).pointer ::
        (G.node x0 :: x0 :: ctrenum cp).map (G.icpH x0)))))
  have hcp : configProg cp := by have := cfctr_config_prog h; exact this
  have hp : G.ProperCpring x0 := cpmap_proper (config_prog_cubic hcp)
  set M := (G.ecpH x0).pointee with hM
  set i := G.icpH x0 with hi
  set e := ctrenum cp with he
  set t := (G.cpring x0).drop 2 with ht
  have hr : G.cpring x0 = G.node x0 :: x0 :: t := G.head_proper_cpring x0 hp
  have hmemX : ∀ u, M.cnode IcpX u ↔ u ∈ Icp (Icp IcpXe) :: IcpX :: t.map i := fun u => by
    rw [← CfContract.node_ecpH G x0 hp, ← ecpH_pointer G x0, ← G.cpring_ecpH x0 hp]
    exact (M.mem_cpring _).symm
  rw [G.cpring_ecpH x0 hp, CfContract.node_ecpH G x0 hp, ecpH_pointer, face_ecpH, ← ht, ← hi]
  have hlen : (G.cpring x0).length = cprsize cp := size_ring_cpmap _
  have hlt : t.length + 2 = cprsize cp := by rw [← hlen, hr]; rfl
  rcases mr with _ | ⟨b1, _ | ⟨b2, mr⟩⟩
  · simp only [cprsize, List.length_nil] at hmr; omega
  · simp only [cprsize, List.length_cons, List.length_nil] at hmr; omega
  rcases mc with _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, mc⟩⟩⟩
  · simp [ctrmsize] at hmc
  · simp [ctrmsize] at hmc
  · simp [ctrmsize] at hmc
  have hmr' : (b4 :: b5 :: mr).length = cprsize cp := by
    simp only [cprsize, List.length_cons] at hmr ⊢; omega
  have hmc' : mc.length = ctrmsize cp := by
    simp only [ctrmsize, List.length_cons] at hmc ⊢; omega
  rw [cfctr_H] at h
  by_cases hnsp : (nsp b3 b1 b4 || nsp b3 b2 b5) = true
  · rw [ite_eq_left hnsp] at h; cases h
  rw [ite_eq_right hnsp] at h
  by_cases hall : (b1 && (b2 && mr.all id)) = true
  · rw [ite_eq_left hall] at h; cases h
  rw [ite_eq_right hall] at h
  obtain ⟨cpc0, hc0, -⟩ := Option.map_eq_some_iff.1 h
  have IH := ih (b4 :: b5 :: mr) mc hmr' hmc' cpc0 hc0
  change G.Sparse (x0 :: ((mask (b4 :: b5 :: mr) (G.cpring x0)).map G.edge ++
    G.insertE (mask mc e))) at IH
  rw [hr] at IH
  set p := (mask (b4 :: b5 :: mr) (G.node x0 :: x0 :: t)).map G.edge ++ G.insertE (mask mc e)
    with hpdef
  rw [G.sparse_cons] at IH
  obtain ⟨hr'p, hsp⟩ := IH
  have hoff : ∀ y ∈ p, y ∉ G.cpring x0 := fun y hy hyr =>
    hr'p ⟨y, hy, (G.mem_cpring x0).1 hyr⟩
  have hcn : ∀ y, y ∉ G.cpring x0 → ∀ z, M.cnode (i y) (i z) ↔ G.cnode y z :=
    fun y hy z => cnode_injcp (cp1 := [.H]) rfl cp y hy z
  have hnd := G.cpring_uniq x0
  rw [hr] at hnd
  have hp' : x0 ≠ G.node x0 := hp
  have hlU : (G.ecpUMap x0).LongCpring IcpX := G.long_ecpU x0
  -- the node of `i (node x0)` is the triangle of the new darts `edge nX`, `edge fX`
  have hN3 : M.node (i (G.node x0)) = Icp (Icp IcpX) := by
    show ((G.ecpUMap x0).ecpNMap IcpX).ecpNNode IcpX (Icp (Icp (Icp (G.node x0)))) = _
    simp [ecpNNode, ecpUNode]
  have hN4 : M.node (Icp (Icp IcpX)) = Icp IcpXe := by
    show ((G.ecpUMap x0).ecpNMap IcpX).ecpNNode IcpX (Icp (Icp IcpX)) = _
    simp [ecpNNode, ecpUFace, ecpEdge]
  have hN5 : M.node (Icp IcpXe) = i (G.node x0) := by
    show ((G.ecpUMap x0).ecpNMap IcpX).ecpNNode IcpX (Icp IcpXe) = _
    simp [ecpNNode, ecpUNode, ecpUFace, ecpEdge, hi, icpH_eq]
  have hcyc : fcycle M.node [i (G.node x0), Icp (Icp IcpX), Icp IcpXe] :=
    ⟨hN3, hN4, hN5, trivial⟩
  have hmemN : ∀ u, M.cnode (i (G.node x0)) u ↔
      u ∈ [i (G.node x0), Icp (Icp IcpX), Icp IcpXe] := fun u =>
    fconnect_cycle hcyc List.mem_cons_self
  -- the node of `i x0` contains `face X` and `edge X`
  have hN1 : M.node (i x0) = Icp IcpX := by
    show ((G.ecpUMap x0).ecpNMap IcpX).ecpNNode IcpX (Icp (Icp (Icp x0))) = _
    simp [ecpNNode, ecpUNode, hlU, hp']
  have hN2 : M.node (Icp IcpX) = IcpXe := by
    show ((G.ecpUMap x0).ecpNMap IcpX).ecpNNode IcpX (Icp IcpX) = _
    simp [ecpNNode]
  -- the reference dart, the new node, `i x0` and the images of the previous contract
  have hKL : M.Sparse (IcpX :: i (G.node x0) :: i x0 :: p.map i) := by
    rw [M.sparse_cons, M.sparse_cons, M.sparse_cons]
    have hx0t : x0 ∉ t := (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).1
    have hnx0t : G.node x0 ∉ t := fun h => (List.nodup_cons.1 hnd).1 (List.mem_cons_of_mem _ h)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro ⟨u, hu, hXu⟩
      rw [hmemX] at hXu
      simp only [List.mem_cons, List.mem_map] at hu hXu
      rcases hu with rfl | rfl | ⟨y, hy, rfl⟩ <;> rcases hXu with h1 | h1 | ⟨z, hz, h1⟩ <;>
        first
        | (simp [hi, icpH_eq] at h1; done)
        | (rw [G.icpH_inj x0 h1] at hz; first
            | exact hnx0t hz
            | exact hx0t hz
            | exact hoff _ hy
                (by rw [hr]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)))
    · rintro ⟨u, hu, h⟩
      rw [hmemN] at h
      simp only [List.mem_cons, List.mem_map, List.not_mem_nil, or_false] at hu h
      rcases hu with rfl | ⟨y, hy, rfl⟩ <;> rcases h with h1 | h1 | h1 <;>
        first
        | (simp [hi, icpH_eq] at h1; done)
        | exact hp' (G.icpH_inj x0 h1)
        | exact hoff _ hy (by rw [G.icpH_inj x0 h1, hr]; exact List.mem_cons_self)
    · rintro ⟨u, hu, h⟩
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hu
      have h2 := (hcn y (hoff y hy) x0).1 (M.cnodeC.1 h)
      exact hoff y hy ((G.mem_cpring x0).2 (G.cnodeC.1 h2))
    · rw [sparse_iff_pairwise, List.pairwise_map]
      rw [sparse_iff_pairwise] at hsp
      exact hsp.imp_of_mem (fun {a b} ha _ hab h' => hab ((hcn a (hoff a ha) b).1 h'))
  -- the node classes of the new contract edges
  have hFa1 : froot M.node (M.edge (Icp (Icp IcpXe))) = froot M.node (i (G.node x0)) := by
    refine (froot_node_eq M ?_).symm
    show M.cnode (i (G.node x0)) (Icp (Icp IcpX))
    rw [← hN3]; exact fconnect1 _ _
  have hFa2 : froot M.node (M.edge (Icp IcpX)) = froot M.node (i (G.node x0)) := by
    refine (froot_node_eq M ?_).symm
    show M.cnode (i (G.node x0)) (Icp IcpXe)
    rw [← hN4, ← hN3]; exact connect_trans (fconnect1 _ _) (fconnect1 _ _)
  have hFb1 : froot M.node (M.edge IcpX) = froot M.node (i x0) := by
    refine (froot_node_eq M ?_).symm
    show M.cnode (i x0) IcpXe
    rw [← hN2, ← hN1]; exact connect_trans (fconnect1 _ _) (fconnect1 _ _)
  have hFb2 : froot M.node (Icp IcpX) = froot M.node (i x0) := by
    refine (froot_node_eq M ?_).symm
    rw [← hN1]; exact fconnect1 _ _
  have hME : (mask mr (t.map i)).map M.edge = ((mask mr t).map G.edge).map i := by
    rw [← map_mask, List.map_map, List.map_map]; rfl
  have hKE : M.insertE (mask mc (e.map i)) = (G.insertE (mask mc e)).map i := by
    rw [← map_mask]; exact G.insertE_icpH x0 _
  have hEi : ∀ y, M.edge (i y) = i (G.edge y) := fun y => rfl
  refine sparse_of_subperm M ?_ hKL
  rw [hpdef, List.map_append]
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> simp [nsp] at hnsp <;>
    simp only [mask_true_cons, mask_false_cons, List.map_cons, List.cons_append,
      insertE, hME, hKE, hFa1, hFa2, hFb1, hFb2, hEi, List.map_append]
  · -- `(F, F, F, F, F)`
    exact (List.Sublist.cons_cons _ (List.Sublist.cons _ (List.Sublist.cons _
      (List.Sublist.refl _)))).subperm
  · -- `(F, F, F, F, T)`
    exact ((List.Perm.cons _ (perm_middle2 _ _ _ _)).subperm).trans
      (List.Sublist.cons_cons _ (List.Sublist.cons _ (List.Sublist.refl _))).subperm
  · -- `(F, F, F, T, F)`
    exact ((List.Perm.cons _ (perm_middle2 _ _ _ _)).subperm).trans
      (List.Sublist.cons_cons _ (List.Sublist.cons_cons _ (List.Sublist.cons _
        (List.Sublist.refl _)))).subperm
  · -- `(F, F, F, T, T)`
    refine (List.Perm.cons _ ?_).subperm
    refine (perm_middle2 _ _ _ _).trans (List.Perm.cons _ ?_)
    exact (List.Perm.cons _ (perm_middle2 _ _ _ _)).trans (List.Perm.swap _ _ _)
  · -- `(F, F, T, F, F)`
    exact (List.Perm.cons _ ((perm_middle2 _ _ _ _).trans (List.Perm.swap _ _ _))).subperm
  · -- `(F, T, F, F, F)`
    exact (List.Sublist.cons_cons _ (List.Sublist.cons _ (List.Sublist.refl _))).subperm
  · -- `(F, T, F, T, F)`
    refine (List.Perm.cons _ ?_).subperm
    refine (List.Perm.cons _ (perm_middle2 _ _ _ _)).trans ?_
    exact (List.Perm.swap _ _ _)
  · -- `(T, F, F, F, F)`
    exact (List.Sublist.cons_cons _ (List.Sublist.cons_cons _ (List.Sublist.cons _
      (List.Sublist.refl _)))).subperm
  · -- `(T, F, F, F, T)`
    exact (List.Perm.cons _ (List.Perm.cons _ (perm_middle2 _ _ _ _))).subperm
  · -- `(T, T, F, F, F)`
    exact List.Subperm.refl _

end StepH

end CfContract

/-- math-comp `sparse_cfctr`.  (math-comp states it with the boolean implication
`cfctr mr mc cp ==> sparse (G :: cc)`.) -/
theorem sparse_cfctr {mr mc : List Bool} {cp : Cprog}
    (hmr : mr.length = cprsize cp) (hmc : mc.length = ctrmsize cp)
    {cpc : Cprog} (h : cfctr mr mc cp = some cpc) :
    (cpmap cp).pointee.Sparse ((cpmap cp).pointer ::
      ((mask mr ((cpmap cp).pointee.cpring (cpmap cp).pointer)).map (cpmap cp).pointee.edge ++
        (cpmap cp).pointee.insertE (mask mc (ctrenum cp)))) := by
  suffices hall : ∀ cp, CfContract.SparseCtr cp from hall cp mr mc hmr hmc cpc h
  intro cp
  induction cp with
  | nil =>
    intro mr mc _ _ cpc h
    exact absurd (cfctr_config_prog h) (by simp [configProg])
  | cons s cp ih =>
    cases s with
    | R n => exact CfContract.sparseCtr_R n ih
    | Y =>
      cases cp with
      | nil => exact CfContract.sparseCtr_Y0
      | cons s' cp' => exact CfContract.sparseCtr_Y ih
    | H => exact CfContract.sparseCtr_H ih
    | _ =>
      intro mr mc _ _ cpc h
      exact absurd (cfctr_config_prog h) (by simp [configProg])

end FourColor
