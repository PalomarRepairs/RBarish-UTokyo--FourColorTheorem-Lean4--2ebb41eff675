/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfContract.Ext

/-!
# Configuration contracts (port of `cfcontract.v`, `cfctr_correct`)

`cfctr_correct`: if `cfctr mr mc cp = some cpc`, then every contract coloring of `cpmap cp` for
the contract selected by `mr` (on the ring) and `mc` (on the kernel edge transversal
`ctrenum cp`) induces on the uncontracted ring edges the ring coloring of a coloring of
`cpmap cpc`.

The proof is by induction on `cp`, one lemma per construction step (`ctrCorrect_R`,
`ctrCorrect_Y0`, `ctrCorrect_Y`, `ctrCorrect_H`); the colorings of the contracted maps are
built with the extension lemmas of `FourColor/CfContract/Ext.lean`.
-/

namespace FourColor

open Function CfMap EcpDart Hypermap

namespace CfContract

/-- The statement of `cfctr_correct` for the program `cp` (for the induction). -/
def CtrCorrect (cp : Cprog) : Prop :=
  ∀ (mr mc : List Bool), mr.length = cprsize cp → mc.length = ctrmsize cp →
    ∀ k : (cpmap cp).D → Color,
      (cpmap cp).pointee.CcColoring
        (mask mr ((cpmap cp).pointee.cpring (cpmap cp).pointer) ++ mask mc (ctrenum cp)) k →
      ∀ cpc, cfctr mr mc cp = some cpc →
        ∃ k', (cpmap cpc).pointee.Coloring k' ∧
          ((cpmap cpc).pointee.cpring (cpmap cpc).pointer).map k' =
            (mask (mr.map not) ((cpmap cp).pointee.cpring (cpmap cp).pointer)).map k

/-- `cfctr_correct` for an `R n` step. -/
theorem ctrCorrect_R (n : ℕ) {cp : Cprog} (ih : CtrCorrect cp) : CtrCorrect (.R n :: cp) := by
  intro mr mc hmr hmc
  set G := (cpmap cp).pointee with hG
  set x0 := (cpmap cp).pointer with hx0
  show ∀ k : (cpmap cp).D → Color,
    G.CcColoring (mask mr ((G.ecpR n x0).pointee.cpring (G.ecpR n x0).pointer) ++
      mask mc (ctrenum cp)) k → ∀ cpc, cfctr mr mc (.R n :: cp) = some cpc →
    ∃ k', (cpmap cpc).pointee.Coloring k' ∧
      ((cpmap cpc).pointee.cpring (cpmap cpc).pointer).map k' =
        (mask (mr.map not) ((G.ecpR n x0).pointee.cpring (G.ecpR n x0).pointer)).map k
  intro k hk cpc h
  rw [cfctr_R] at h
  obtain ⟨cpc0, hc0, rfl⟩ := Option.map_eq_some_iff.1 h
  have hmr' : mr.length = cprsize cp := hmr
  rw [cpring_ecpR] at hk ⊢
  have hlen : (CfMap.rotr n mr).length = (G.cpring x0).length := by
    rw [CfMap.length_rotr, size_ring_cpmap]; exact hmr'
  have hk2 : G.CcColoring (mask (CfMap.rotr n mr) (G.cpring x0) ++ mask mc (ctrenum cp)) k := by
    refine ccColoring_congr G (fun x => ?_) hk
    rw [List.mem_append, List.mem_append, ← mem_mask_rot hlen n, CfMap.rot_rotr]
  obtain ⟨k', hk', hE⟩ :=
    ih (CfMap.rotr n mr) mc (by rw [CfMap.length_rotr]; exact hmr') hmc k hk2 cpc0 hc0
  refine ⟨k', hk', ?_⟩
  set Gc := (cpmap cpc0).pointee with hGc
  set y0 := (cpmap cpc0).pointer with hy0
  change ((Gc.ecpR _ y0).pointee.cpring (Gc.ecpR _ y0).pointer).map k' = _
  rw [cpring_ecpR, CfMap.map_rot, hE]
  conv_rhs => rw [← CfMap.rot_rotr n mr, CfMap.map_rot]
  rw [mask_rot (by simp [hlen]) n, CfMap.map_rot]
  have hc : ((CfMap.rotr n mr).take n).countP (fun b => !b) =
      (((CfMap.rotr n mr).map not).take n).countP id := by
    rw [← List.map_take, List.countP_map]; rfl
  rw [hc]

/-- `cfctr_correct` for the initial `Y` step. -/
theorem ctrCorrect_Y0 : CtrCorrect [.Y] := by
  intro mr mc hmr hmc
  have hmr' : mr.length = 3 := hmr
  have hmc' : mc.length = 0 := hmc
  show ∀ k : (cpmap0.ecpY true).D → Color,
    (cpmap0.ecpY true).pointee.CcColoring
      (mask mr ((cpmap0.ecpY true).pointee.cpring (cpmap0.ecpY true).pointer) ++
        mask mc ([] : List (cpmap0.ecpY true).D)) k → ∀ cpc, cfctr mr mc [.Y] = some cpc →
    ∃ k', (cpmap cpc).pointee.Coloring k' ∧
      ((cpmap cpc).pointee.cpring (cpmap cpc).pointer).map k' =
        (mask (mr.map not) ((cpmap0.ecpY true).pointee.cpring (cpmap0.ecpY true).pointer)).map k
  intro k hk cpc h
  rw [cpring_ecpY_cpmap0] at hk ⊢
  set M := (cpmap0.ecpY true).pointee with hM
  match mr, mc, hmr', hmc' with
  | [b1, b2, b3], [], _, _ =>
    rw [cfctr_Y_nil] at h
    rw [mask_nil_left, List.append_nil] at hk
    -- the face of `node X` contains `icpY (node true)`
    have kn : k (Icp IcpXe) = k (Icp (Icp false)) :=
      M.cc_coloring_cface hk (cpmap0.cface_node_ecpY true)
    have kX : k IcpX = k (Icp IcpX) := by
      have := hk.2 (M.edge (Icp IcpXe))
      rw [show M.face (M.edge (Icp IcpXe)) = IcpX from M.nodeK IcpX] at this
      exact this
    cases b1 <;> cases b2 <;> cases b3 <;> simp [nsp] at h <;> subst h
    · -- `(F, F, F)`: no contraction
      refine ⟨k, ⟨fun x e => ?_, hk.2⟩, ?_⟩
      · have := (hk.1 x).1 e
        cases this
      · show (M.cpring (cpmap0.ecpY true).pointer).map k = _
        rw [cpring_ecpY_cpmap0]
        rfl
    · -- `(F, F, T)`: contract the base edge
      refine ⟨fun b : Bool => k (if b then IcpX else Icp IcpXe), ⟨fun b => ?_, fun b => rfl⟩,
        ?_⟩
      · have hne : k (Icp IcpX) ≠ k (Icp IcpXe) := by
          intro e
          have := (hk.1 (Icp IcpXe)).1 e
          simp [insertE, hM, ecpEdge] at this
        cases b
        · exact fun e => hne (kX ▸ e)
        · exact fun e => hne (kX ▸ e.symm)
      · show (cpmap0.cpring true).map _ = _
        rw [cpring0]
        rfl
    · -- `(F, T, F)`
      refine ⟨fun b : Bool => k (Icp (Icp b)), ⟨fun b e => ?_, fun b => rfl⟩, ?_⟩
      · have := (hk.1 (Icp (Icp b))).1 e
        simp [insertE, hM, ecpEdge] at this
      · show (cpmap0.cpring true).map _ = _
        rw [cpring0]
        show [k (Icp (Icp false)), k (Icp (Icp true))] = [k (Icp IcpXe), k (Icp (Icp true))]
        rw [kn]
    · -- `(T, F, F)`
      refine ⟨fun b : Bool => k (Icp (Icp b)), ⟨fun b e => ?_, fun b => rfl⟩, ?_⟩
      · have := (hk.1 (Icp (Icp b))).1 e
        simp [insertE, hM, ecpEdge] at this
      · show (cpmap0.cpring true).map _ = _
        rw [cpring0]
        show [k (Icp (Icp false)), k (Icp (Icp true))] = [k IcpX, k (Icp (Icp true))]
        have := (hk.1 (Icp IcpXe)).2 (by simp [insertE])
        change k (Icp IcpX) = k (Icp IcpXe) at this
        rw [kX, ← kn, this]

/-- `cfctr_correct` for a non-initial `Y` step. -/
theorem ctrCorrect_Y {s : Cpstep} {cp : Cprog} (ih : CtrCorrect (s :: cp)) :
    CtrCorrect (.Y :: s :: cp) := by
  intro mr mc hmr hmc
  set G := (cpmap (s :: cp)).pointee with hG
  set x0 := (cpmap (s :: cp)).pointer with hx0
  show ∀ k : (G.ecpY x0).D → Color,
    (G.ecpY x0).pointee.CcColoring (mask mr ((G.ecpY x0).pointee.cpring (G.ecpY x0).pointer) ++
      mask mc ((G.node x0 :: ctrenum (s :: cp)).map (G.icpY x0))) k →
    ∀ cpc, cfctr mr mc (.Y :: s :: cp) = some cpc →
    ∃ k', (cpmap cpc).pointee.Coloring k' ∧
      ((cpmap cpc).pointee.cpring (cpmap cpc).pointer).map k' =
        (mask (mr.map not) ((G.ecpY x0).pointee.cpring (G.ecpY x0).pointer)).map k
  intro k hk cpc h
  have hcp : configProg (s :: cp) := by have := cfctr_config_prog h; exact this
  have hp : G.ProperCpring x0 := cpmap_proper (config_prog_cubic hcp)
  set M := (G.ecpY x0).pointee with hM
  set i := G.icpY x0 with hi
  set e := ctrenum (s :: cp) with he
  set t := (G.cpring x0).tail with ht
  have hr : G.cpring x0 = G.node x0 :: t := G.head_cpring x0
  rw [cpring_ecpY, node_ecpY, ecpY_pointer] at hk ⊢
  have hlen : (G.cpring x0).length = cprsize (s :: cp) := size_ring_cpmap _
  have hlt : t.length + 1 = cprsize (s :: cp) := by rw [← hlen, hr]; rfl
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
  obtain ⟨cpc0, hc0, rfl⟩ := Option.map_eq_some_iff.1 h
  -- the contract of `G` induced by that of `ecpY`
  have hsh := fun z => mem_shape i b1 b2 (Icp IcpXe) IcpX mr mc [b3] [] t e [G.node x0] []
    rfl rfl z
  simp only [List.nil_append, List.singleton_append, List.append_nil, mask_nil_left] at hsh
  have hA : ∀ z ∈ mask [b1, b2] [(Icp IcpXe : (G.ecpY x0).D), IcpX],
      ∀ x, i x ≠ z ∧ i x ≠ M.edge z := by
    intro z hz x
    rcases List.mem_cons.1 (mem_of_mem_mask hz) with rfl | hz
    · simp [hi, icpY_eq, hM, ecpEdge]
    · rw [List.mem_singleton.1 hz]; simp [hi, icpY_eq, hM, ecpEdge]
  have hres : G.CcColoring (mask (b3 :: mr) (G.node x0 :: t) ++ mask mc e) (k ∘ i) :=
    ccColoring_restrict i (G.icpY_inj x0) (fun x => rfl)
      (fun x => (G.cface_icpY x0 _ _).2 (fconnect1 _ _)) hA
      (fun z hz => by
        rcases (hsh z).1 hz with h1 | h1
        · exact Or.inl h1
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h1; exact Or.inr ⟨w, hw, rfl⟩)
      (fun w hw => (hsh _).2 (Or.inr (List.mem_map_of_mem hw))) hk
  rw [← hr] at hres
  obtain ⟨h', hh', Eh⟩ := ih (b3 :: mr) mc hmr' hmc' (k ∘ i) hres cpc0 hc0
  rw [hr] at hres Eh
  set Gc := (cpmap cpc0).pointee with hGc
  set y0 := (cpmap cpc0).pointer with hy0
  have hpc : Gc.ProperCpring y0 := coloring_proper hh' y0
  have hrc : Gc.cpring y0 = Gc.node y0 :: y0 :: (Gc.cpring y0).drop 2 :=
    Gc.head_proper_cpring y0 hpc
  -- facts about `k`
  have hnew : ∀ z : (G.ecpY x0).D, (∀ x, z ≠ i x ∧ z ≠ i (G.edge x)) →
      (k (M.edge z) = k z ↔ z ∈ M.insertE (mask [b1, b2] [Icp IcpXe, IcpX])) := by
    intro z hz
    rw [hk.1 z]
    exact mem_insertE_new i (fun x => rfl) hsh hz
  have kn : k (Icp IcpXe) = k (i (G.node x0)) := by
    have := M.cc_coloring_cface hk (G.cface_node_ecpY x0)
    rwa [node_ecpY] at this
  have kX : k IcpX = k (M.edge (Icp IcpXe)) := by
    have := hk.2 (M.edge (Icp IcpXe))
    rw [show M.face (M.edge (Icp IcpXe)) = IcpX from M.nodeK IcpX] at this
    exact this
  have kXe : k (M.edge IcpX) = k (i x0) := by
    rw [← hk.2 (M.edge IcpX)]
    exact congrArg k (G.face_edge_ecpY x0 hp)
  -- the chain of contracted ring edges
  have hEr : ∀ w ∈ mask (b3 :: mr) (G.node x0 :: t), (k ∘ i) (G.edge w) = (k ∘ i) w :=
    fun w hw => (hres.1 w).2
      ((mem_insertE_iff G _ w).2 ⟨w, List.mem_append_left _ hw, Or.inl rfl⟩)
  have hpath := ring_path G x0
  rw [← ht] at hpath
  have hch := chain G (k ∘ i) (fun x => hres.2 x) t (G.node x0) (G.node x0) (b3 :: mr) hpath
    (hmr'.trans hlt.symm) hEr
  have hmap : ∀ m : List Bool, (mask m (t.map i)).map k = (mask m t).map (k ∘ i) := fun m => by
    rw [← map_mask, List.map_map]
  cases b1 <;> cases b2 <;> cases b3 <;> simp [nsp] at hnsp
  · -- `(F, F, F)`: a `Y` step
    have hnX : k (M.edge (Icp IcpXe)) ≠ k (Icp IcpXe) := fun e' => by
      have := (hnew _ (by simp [hi, icpY_eq])).1 e'
      simp [insertE, hM] at this
    have hX : k (M.edge IcpX) ≠ k IcpX := fun e' => by
      have := (hnew _ (by simp [hi, icpY_eq])).1 e'
      simp [insertE, hM] at this
    simp only [List.map_cons, Bool.not_false, mask_true_cons] at Eh
    rw [hrc, List.map_cons, List.map_cons] at Eh
    obtain ⟨E1, E2⟩ := List.cons_eq_cons.1 Eh
    -- `h' y0` is the color of `x0`
    have ht' : t = x0 :: (G.cpring x0).drop 2 := by
      rw [ht, G.head_proper_cpring x0 hp]; rfl
    have hpath' : path (fun a b => G.node b = a) x0 ((G.cpring x0).drop 2 ++ [G.node x0]) := by
      rw [ht', List.cons_append, path_cons] at hpath; exact hpath.2
    have hlm : mr.length = ((G.cpring x0).drop 2).length + 1 := by
      simp only [List.length_cons] at hmr'
      rw [ht'] at hlt; simp only [List.length_cons] at hlt; omega
    have hch2 := chain G (k ∘ i) (fun x => hres.2 x) _ x0 (G.node x0) mr hpath' hlm
      (fun w hw => hEr w (by rw [ht'] at *; simpa using hw))
    rw [← ht', ← E2] at hch2
    have hc1 : h' (Gc.node y0) ≠ k IcpX := by
      rw [E1]; show k (i (G.node x0)) ≠ k IcpX
      rw [← kn, kX]; exact fun e' => hnX e'.symm
    have hc2 : h' y0 ≠ k IcpX := by
      rw [show h' y0 = k (i x0) from hch2.symm, ← kXe]; exact hX
    obtain ⟨k', hk'c, hk'i, hk'X⟩ := coloring_ecpY Gc y0 hh' (k IcpX) hc1 hc2
    refine ⟨k', hk'c, ?_⟩
    change ((Gc.ecpY y0).pointee.cpring (Gc.ecpY y0).pointer).map k' = _
    have kn' : k' ((Gc.ecpY y0).pointee.node (Gc.ecpY y0).pointer) = h' (Gc.node y0) := by
      rw [face_inv_cface hk'c.2 (Gc.cface_node_ecpY y0), hk'i]
    rw [cpring_ecpY, hrc, ← ht]
    simp only [List.map_cons, List.tail_cons, Bool.not_false, mask_true_cons]
    rw [kn', hk'X, E1, hk'i, List.map_map, show k' ∘ Gc.icpY y0 = h' from funext hk'i, E2, hmap,
      kn]
    rfl
  · -- `(F, F, T)`: a `U` step
    have hnX : k (M.edge (Icp IcpXe)) ≠ k (Icp IcpXe) := fun e' => by
      have := (hnew _ (by simp [hi, icpY_eq])).1 e'
      simp [insertE, hM] at this
    simp only [List.map_cons, Bool.not_true, mask_false_cons] at Eh hch
    rw [← Eh, hrc] at hch
    simp only [List.map_cons, List.headD_cons] at hch
    have hc : h' (Gc.node y0) ≠ k IcpX := by
      rw [← hch]; show k (i (G.node x0)) ≠ k IcpX
      rw [← kn, kX]; exact fun e' => hnX e'.symm
    obtain ⟨k', hk'c, hk'i, hk'X⟩ := coloring_ecpU Gc y0 hh' (k IcpX) hc
    refine ⟨k', hk'c, ?_⟩
    change ((Gc.ecpU y0).pointee.cpring (Gc.ecpU y0).pointer).map k' = _
    have kn' : k' ((Gc.ecpU y0).pointee.node (Gc.ecpU y0).pointer) = h' (Gc.node y0) := by
      rw [← hk'i]; exact (hk'c.2 IcpXe).symm
    rw [cpring_ecpU, ← ht]
    simp only [List.map_cons, Bool.not_false, mask_true_cons]
    rw [kn', hk'X, List.map_map, show k' ∘ Gc.icpU y0 = h' from funext hk'i, Eh, hmap, ← hch,
      kn]
    rfl
  · -- `(F, T, F)`: no new step
    refine ⟨h', hh', ?_⟩
    change (Gc.cpring y0).map h' = _
    simp only [List.map_cons, Bool.not_false, Bool.not_true, mask_true_cons, mask_false_cons]
      at Eh ⊢
    rw [Eh, ← ht, hmap, kn]
    rfl
  · -- `(T, F, F)`: no new step
    have hnX : k (M.edge (Icp IcpXe)) = k (Icp IcpXe) :=
      (hnew _ (by simp [hi, icpY_eq])).2 (by simp [insertE])
    refine ⟨h', hh', ?_⟩
    change (Gc.cpring y0).map h' = _
    simp only [List.map_cons, Bool.not_false, Bool.not_true, mask_true_cons, mask_false_cons]
      at Eh ⊢
    rw [Eh, ← ht, hmap, kX, hnX, kn]
    rfl

/-- `cfctr_correct` for an `H` step. -/
theorem ctrCorrect_H {cp : Cprog} (ih : CtrCorrect cp) : CtrCorrect (.H :: cp) := by
  intro mr mc hmr hmc
  set G := (cpmap cp).pointee with hG
  set x0 := (cpmap cp).pointer with hx0
  show ∀ k : (G.ecpH x0).D → Color,
    (G.ecpH x0).pointee.CcColoring (mask mr ((G.ecpH x0).pointee.cpring (G.ecpH x0).pointer) ++
      mask mc ((G.ecpH x0).pointee.face (G.ecpH x0).pointer ::
        (G.node x0 :: x0 :: ctrenum cp).map (G.icpH x0))) k →
    ∀ cpc, cfctr mr mc (.H :: cp) = some cpc →
    ∃ k', (cpmap cpc).pointee.Coloring k' ∧
      ((cpmap cpc).pointee.cpring (cpmap cpc).pointer).map k' =
        (mask (mr.map not) ((G.ecpH x0).pointee.cpring (G.ecpH x0).pointer)).map k
  intro k hk cpc h
  have hcp : configProg cp := by have := cfctr_config_prog h; exact this
  have hp : G.ProperCpring x0 := cpmap_proper (config_prog_cubic hcp)
  have hl : G.LongCpring x0 := cfmap_long hcp
  set M := (G.ecpH x0).pointee with hM
  set i := G.icpH x0 with hi
  set e := ctrenum cp with he
  set t := (G.cpring x0).drop 2 with ht
  have hr : G.cpring x0 = G.node x0 :: x0 :: t := G.head_proper_cpring x0 hp
  have hr3 : t = G.face (G.edge x0) :: (G.cpring x0).drop 3 := by
    rw [ht, G.head_long_cpring x0 hl]; rfl
  rw [G.cpring_ecpH x0 hp, CfContract.node_ecpH G x0 hp, ecpH_pointer, face_ecpH, ← ht] at hk
  rw [G.cpring_ecpH x0 hp, CfContract.node_ecpH G x0 hp, ecpH_pointer, ← ht]
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
  have hlm : mr.length = t.length := by simp only [List.length_cons] at hmr'; omega
  rw [cfctr_H] at h
  by_cases hnsp : (nsp b3 b1 b4 || nsp b3 b2 b5) = true
  · rw [ite_eq_left hnsp] at h; cases h
  rw [ite_eq_right hnsp] at h
  by_cases hall : (b1 && (b2 && mr.all id)) = true
  · rw [ite_eq_left hall] at h; cases h
  rw [ite_eq_right hall] at h
  obtain ⟨cpc0, hc0, rfl⟩ := Option.map_eq_some_iff.1 h
  -- the contract of `G` induced by that of `ecpH`
  have hsh := fun z => mem_shape i b1 b2 (Icp (Icp IcpXe)) IcpX mr mc [b4, b5] [b3] t e
    [G.node x0, x0] [Icp IcpX] rfl rfl z
  simp only [List.cons_append, List.nil_append] at hsh
  have hA : ∀ z ∈ mask [b1, b2] [(Icp (Icp IcpXe) : (G.ecpH x0).D), IcpX] ++
      mask [b3] [Icp IcpX],
      ∀ x, i x ≠ z ∧ i x ≠ M.edge z := by
    intro z hz x
    rw [List.mem_append] at hz
    rcases hz with hz | hz
    · rcases List.mem_cons.1 (mem_of_mem_mask hz) with rfl | hz
      · simp [hi, icpH_eq, hM, ecpEdge]
      · rw [List.mem_singleton.1 hz]; simp [hi, icpH_eq, hM, ecpEdge]
    · rw [List.mem_singleton.1 (mem_of_mem_mask hz)]; simp [hi, icpH_eq, hM, ecpEdge]
  have hres : G.CcColoring (mask (b4 :: b5 :: mr) (G.node x0 :: x0 :: t) ++ mask mc e) (k ∘ i) :=
    ccColoring_restrict i (G.icpH_inj x0) (fun x => rfl)
      (fun x => (G.cface_icpH x0 _ _).2 (fconnect1 _ _)) hA
      (fun z hz => by
        rcases (hsh z).1 hz with h1 | h1
        · exact Or.inl h1
        · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h1; exact Or.inr ⟨w, hw, rfl⟩)
      (fun w hw => (hsh _).2 (Or.inr (List.mem_map_of_mem hw))) hk
  rw [← hr] at hres
  obtain ⟨h', hh', Eh⟩ := ih (b4 :: b5 :: mr) mc hmr' hmc' (k ∘ i) hres cpc0 hc0
  rw [hr] at hres Eh
  set Gc := (cpmap cpc0).pointee with hGc
  set y0 := (cpmap cpc0).pointer with hy0
  have hpc : Gc.ProperCpring y0 := coloring_proper hh' y0
  have hrc : Gc.cpring y0 = Gc.node y0 :: y0 :: (Gc.cpring y0).drop 2 :=
    Gc.head_proper_cpring y0 hpc
  -- facts about `k`
  have hnew : ∀ z : (G.ecpH x0).D, (∀ x, z ≠ i x ∧ z ≠ i (G.edge x)) →
      (k (M.edge z) = k z ↔
        z ∈ M.insertE (mask [b1, b2] [Icp (Icp IcpXe), IcpX] ++ mask [b3] [Icp IcpX])) := by
    intro z hz
    rw [hk.1 z]
    exact mem_insertE_new i (fun x => rfl) hsh hz
  have kn : k (Icp (Icp IcpXe)) = k (i (G.node x0)) := by
    have := M.cc_coloring_cface hk (G.cface_node_ecpH x0 hp)
    rwa [CfContract.node_ecpH G x0 hp] at this
  have kX : k IcpX = k (M.edge (Icp (Icp IcpXe))) := by
    have := hk.2 (M.edge (Icp (Icp IcpXe)))
    rw [show M.face (M.edge (Icp (Icp IcpXe))) = IcpX by
      rw [← CfContract.node_ecpH G x0 hp]; exact M.nodeK IcpX] at this
    exact this
  have kfX : k (Icp IcpX) = k IcpX := hk.2 IcpX
  have kXe : k (M.edge IcpX) = k (i (G.face (G.edge x0))) := by
    rw [← hk.2 (M.edge IcpX)]
    exact congrArg k (CfContract.face_edge_ecpH G x0 hp hl)
  have kfXe : k (M.edge (Icp IcpX)) = k (i x0) := by
    rw [← hk.2 (M.edge (Icp IcpX))]
    exact congrArg k (CfContract.face_edge_face_ecpH G x0 hp)
  have hzN : ∀ x, (Icp (Icp IcpXe) : (G.ecpH x0).D) ≠ i x ∧
      (Icp (Icp IcpXe) : (G.ecpH x0).D) ≠ i (G.edge x) := by simp [hi, icpH_eq]
  have hzX : ∀ x, (IcpX : (G.ecpH x0).D) ≠ i x ∧ (IcpX : (G.ecpH x0).D) ≠ i (G.edge x) := by
    simp [hi, icpH_eq]
  have hzfX : ∀ x, (Icp IcpX : (G.ecpH x0).D) ≠ i x ∧
      (Icp IcpX : (G.ecpH x0).D) ≠ i (G.edge x) := by simp [hi, icpH_eq]
  -- the chain of contracted ring edges
  have hEr : ∀ w ∈ mask (b4 :: b5 :: mr) (G.node x0 :: x0 :: t),
      (k ∘ i) (G.edge w) = (k ∘ i) w :=
    fun w hw => (hres.1 w).2
      ((mem_insertE_iff G _ w).2 ⟨w, List.mem_append_left _ hw, Or.inl rfl⟩)
  have hpath := ring_path G x0
  rw [hr, List.tail_cons, hr3, List.cons_append, path_cons, List.cons_append, path_cons] at hpath
  have hcht := chain G (k ∘ i) (fun x => hres.2 x) _ _ (G.node x0) mr hpath.2.2
    (by rw [hlm, hr3]; rfl) (fun w hw => hEr w (by
      rw [← hr3] at hw; exact mem_mask_cons.2 (Or.inr (mem_mask_cons.2 (Or.inr hw)))))
  rw [← hr3] at hcht
  have hn0 : b4 = true → (k ∘ i) x0 = (k ∘ i) (G.node x0) := fun hb => by
    have := hEr (G.node x0) (mem_mask_cons.2 (Or.inl ⟨hb, rfl⟩))
    rw [← this, ← hres.2 (G.edge (G.node x0)), G.nodeK]
  have hx0' : b5 = true → (k ∘ i) (G.face (G.edge x0)) = (k ∘ i) x0 := fun hb => by
    have := hEr x0 (mem_mask_cons.2 (Or.inr (mem_mask_cons.2 (Or.inl ⟨hb, rfl⟩))))
    rw [← this, hres.2]
  have hmap : ∀ m : List Bool, (mask m (t.map i)).map k = (mask m t).map (k ∘ i) := fun m => by
    rw [← map_mask, List.map_map]
  have hfe_of : ∀ L : List Bool, (Gc.cpring y0).map h' = (k ∘ i) (G.node x0) :: (k ∘ i) x0 ::
      (mask (mr.map not) t).map (k ∘ i) →
      h' (Gc.node y0) = (k ∘ i) (G.node x0) ∧ h' y0 = (k ∘ i) x0 ∧
      ((Gc.cpring y0).drop 2).map h' = (mask (mr.map not) t).map (k ∘ i) ∧
      h' (Gc.face (Gc.edge y0)) = (k ∘ i) (G.face (G.edge x0)) := by
    intro _ Eh
    rw [hrc, List.map_cons, List.map_cons] at Eh
    obtain ⟨E1, E2⟩ := List.cons_eq_cons.1 Eh
    obtain ⟨E2, E3⟩ := List.cons_eq_cons.1 E2
    refine ⟨E1, E2, E3, ?_⟩
    rw [← headD_drop2 Gc y0 h', E3, E1, ← hcht]
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> simp [nsp] at hnsp
  · -- `(F, F, F, F, F)`: an `H` step
    have hnX : k (M.edge (Icp (Icp IcpXe))) ≠ k (Icp (Icp IcpXe)) := fun e' => by
      have := (hnew _ hzN).1 e'; simp [insertE, hM] at this
    have hX : k (M.edge IcpX) ≠ k IcpX := fun e' => by
      have := (hnew _ hzX).1 e'; simp [insertE, hM] at this
    have hfX : k (M.edge (Icp IcpX)) ≠ k (Icp IcpX) := fun e' => by
      have := (hnew _ hzfX).1 e'; simp [insertE, hM] at this
    simp only [List.map_cons, Bool.not_false, mask_true_cons] at Eh
    obtain ⟨E1, E2, E3, hfe⟩ := hfe_of [] Eh
    have hc1 : h' (Gc.node y0) ≠ k IcpX := by
      rw [E1]; show k (i (G.node x0)) ≠ k IcpX
      rw [← kn, kX]; exact fun e' => hnX e'.symm
    have hc2 : h' y0 ≠ k IcpX := by
      rw [E2]; show k (i x0) ≠ k IcpX
      rw [← kfXe, ← kfX]; exact hfX
    have hc3 : h' (Gc.face (Gc.edge y0)) ≠ k IcpX := by
      rw [hfe]; show k (i (G.face (G.edge x0))) ≠ k IcpX
      rw [← kXe]; exact hX
    obtain ⟨k', hk'c, hk'i, hk'X⟩ := coloring_ecpH Gc y0 hh' (k IcpX) hc1 hc2 hc3
    refine ⟨k', hk'c, ?_⟩
    change ((Gc.ecpH y0).pointee.cpring (Gc.ecpH y0).pointer).map k' = _
    have kn' : k' ((Gc.ecpH y0).pointee.node (Gc.ecpH y0).pointer) = h' (Gc.node y0) := by
      rw [face_inv_cface hk'c.2 (Gc.cface_node_ecpH y0 hpc), hk'i]
    rw [Gc.cpring_ecpH y0 hpc]
    simp only [List.map_cons, Bool.not_false, mask_true_cons]
    rw [kn', hk'X, E1, List.map_map, show k' ∘ Gc.icpH y0 = h' from funext hk'i, E3, hmap, kn]
    rfl
  · -- `(F, F, F, F, T)`: a `Y` step
    have hnX : k (M.edge (Icp (Icp IcpXe))) ≠ k (Icp (Icp IcpXe)) := fun e' => by
      have := (hnew _ hzN).1 e'; simp [insertE, hM] at this
    have hX : k (M.edge IcpX) ≠ k IcpX := fun e' => by
      have := (hnew _ hzX).1 e'; simp [insertE, hM] at this
    simp only [List.map_cons, Bool.not_false, Bool.not_true, mask_true_cons, mask_false_cons] at Eh
    rw [hrc, List.map_cons, List.map_cons] at Eh
    obtain ⟨E1, E2⟩ := List.cons_eq_cons.1 Eh
    have hy : h' y0 = (k ∘ i) (G.face (G.edge x0)) := by rw [hcht, ← E2]; rfl
    have hc1 : h' (Gc.node y0) ≠ k IcpX := by
      rw [E1]; show k (i (G.node x0)) ≠ k IcpX
      rw [← kn, kX]; exact fun e' => hnX e'.symm
    have hc2 : h' y0 ≠ k IcpX := by
      rw [hy]; show k (i (G.face (G.edge x0))) ≠ k IcpX
      rw [← kXe]; exact hX
    obtain ⟨k', hk'c, hk'i, hk'X⟩ := coloring_ecpY Gc y0 hh' (k IcpX) hc1 hc2
    refine ⟨k', hk'c, ?_⟩
    change ((Gc.ecpY y0).pointee.cpring (Gc.ecpY y0).pointer).map k' = _
    have kn' : k' ((Gc.ecpY y0).pointee.node (Gc.ecpY y0).pointer) = h' (Gc.node y0) := by
      rw [face_inv_cface hk'c.2 (Gc.cface_node_ecpY y0), hk'i]
    rw [cpring_ecpY, hrc]
    simp only [List.map_cons, List.tail_cons, Bool.not_false, mask_true_cons]
    rw [kn', hk'X, E1, hk'i, List.map_map, show k' ∘ Gc.icpY y0 = h' from funext hk'i, E2, hmap,
      kn]
    rfl
  · -- `(F, F, F, T, F)`: a `Y` step
    have hnX : k (M.edge (Icp (Icp IcpXe))) ≠ k (Icp (Icp IcpXe)) := fun e' => by
      have := (hnew _ hzN).1 e'; simp [insertE, hM] at this
    have hX : k (M.edge IcpX) ≠ k IcpX := fun e' => by
      have := (hnew _ hzX).1 e'; simp [insertE, hM] at this
    simp only [List.map_cons, Bool.not_false, Bool.not_true, mask_true_cons, mask_false_cons] at Eh
    rw [hrc, List.map_cons, List.map_cons] at Eh
    obtain ⟨E1, E2⟩ := List.cons_eq_cons.1 Eh
    rw [hn0 rfl] at E1
    have hy : h' y0 = (k ∘ i) (G.face (G.edge x0)) := by rw [hcht, ← E2]; rfl
    have hc1 : h' (Gc.node y0) ≠ k IcpX := by
      rw [E1]; show k (i (G.node x0)) ≠ k IcpX
      rw [← kn, kX]; exact fun e' => hnX e'.symm
    have hc2 : h' y0 ≠ k IcpX := by
      rw [hy]; show k (i (G.face (G.edge x0))) ≠ k IcpX
      rw [← kXe]; exact hX
    obtain ⟨k', hk'c, hk'i, hk'X⟩ := coloring_ecpY Gc y0 hh' (k IcpX) hc1 hc2
    refine ⟨k', hk'c, ?_⟩
    change ((Gc.ecpY y0).pointee.cpring (Gc.ecpY y0).pointer).map k' = _
    have kn' : k' ((Gc.ecpY y0).pointee.node (Gc.ecpY y0).pointer) = h' (Gc.node y0) := by
      rw [face_inv_cface hk'c.2 (Gc.cface_node_ecpY y0), hk'i]
    rw [cpring_ecpY, hrc]
    simp only [List.map_cons, List.tail_cons, Bool.not_false, mask_true_cons]
    rw [kn', hk'X, E1, hk'i, List.map_map, show k' ∘ Gc.icpY y0 = h' from funext hk'i, E2, hmap,
      kn]
    rfl
  · -- `(F, F, F, T, T)`: a `U` step
    have hX : k (M.edge IcpX) ≠ k IcpX := fun e' => by
      have := (hnew _ hzX).1 e'; simp [insertE, hM] at this
    simp only [List.map_cons, Bool.not_true, mask_false_cons] at Eh
    have hn : h' (Gc.node y0) = (k ∘ i) (G.face (G.edge x0)) := by
      rw [hcht, ← Eh, hrc]; rfl
    have hc : h' (Gc.node y0) ≠ k IcpX := by
      rw [hn]; show k (i (G.face (G.edge x0))) ≠ k IcpX
      rw [← kXe]; exact hX
    obtain ⟨k', hk'c, hk'i, hk'X⟩ := coloring_ecpU Gc y0 hh' (k IcpX) hc
    refine ⟨k', hk'c, ?_⟩
    change ((Gc.ecpU y0).pointee.cpring (Gc.ecpU y0).pointer).map k' = _
    have kn' : k' ((Gc.ecpU y0).pointee.node (Gc.ecpU y0).pointer) = h' (Gc.node y0) := by
      rw [← hk'i]; exact (hk'c.2 IcpXe).symm
    rw [cpring_ecpU]
    simp only [List.map_cons, Bool.not_false, mask_true_cons]
    rw [kn', hk'X, List.map_map, show k' ∘ Gc.icpU y0 = h' from funext hk'i, Eh, hmap, hn,
      hx0' rfl, hn0 rfl, kn]
    rfl
  · -- `(F, F, T, F, F)`: no new step
    have hfX : k (M.edge (Icp IcpX)) = k (Icp IcpX) := (hnew _ hzfX).2 (by simp [insertE])
    refine ⟨h', hh', ?_⟩
    change (Gc.cpring y0).map h' = _
    simp only [List.map_cons, Bool.not_false, mask_true_cons] at Eh ⊢
    rw [Eh, hmap, kn, ← kfX, ← hfX, kfXe]
    rfl
  · -- `(F, T, F, F, F)`: a `K` step
    have hnX : k (M.edge (Icp (Icp IcpXe))) ≠ k (Icp (Icp IcpXe)) := fun e' => by
      have := (hnew _ hzN).1 e'; simp [insertE, hM, ecpEdge] at this
    have hX : k (M.edge IcpX) = k IcpX := (hnew _ hzX).2 (by simp [insertE])
    simp only [List.map_cons, Bool.not_false, mask_true_cons] at Eh
    obtain ⟨E1, -, E3, hfe⟩ := hfe_of [] Eh
    have hc : h' (Gc.edge y0) ≠ h' (Gc.node y0) := by
      rw [← hh'.2 (Gc.edge y0), hfe, E1]
      show k (i (G.face (G.edge x0))) ≠ k (i (G.node x0))
      rw [← kXe, hX, ← kn, kX]; exact hnX
    obtain ⟨k', hk'c, hk'i⟩ := coloring_ecpK Gc y0 hh' hc
    refine ⟨k', hk'c, ?_⟩
    change ((Gc.ecpK y0).pointee.cpring (Gc.ecpK y0).pointer).map k' = _
    have kn' : k' ((Gc.ecpK y0).pointee.node (Gc.ecpK y0).pointer) = h' (Gc.node y0) := by
      rw [face_inv_cface hk'c.2 (Gc.cface_node_ecpK y0), hk'i]
    rw [Gc.cpring_ecpK y0]
    simp only [List.map_cons, Bool.not_false, Bool.not_true, mask_true_cons, mask_false_cons]
    rw [kn', E1, List.map_map, show k' ∘ Gc.icpK y0 = h' from funext hk'i, E3, hmap, kn]
    rfl
  · -- `(F, T, F, T, F)`: no new step
    refine ⟨h', hh', ?_⟩
    change (Gc.cpring y0).map h' = _
    simp only [List.map_cons, Bool.not_false, Bool.not_true, mask_true_cons, mask_false_cons]
      at Eh ⊢
    rw [Eh, hmap, kn, hn0 rfl]
    rfl
  · -- `(T, F, F, F, F)`: a `K` step
    have hnX : k (M.edge (Icp (Icp IcpXe))) = k (Icp (Icp IcpXe)) :=
      (hnew _ hzN).2 (by simp [insertE])
    have hX : k (M.edge IcpX) ≠ k IcpX := fun e' => by
      have := (hnew _ hzX).1 e'; simp [insertE, hM, ecpEdge] at this
    simp only [List.map_cons, Bool.not_false, mask_true_cons] at Eh
    obtain ⟨E1, -, E3, hfe⟩ := hfe_of [] Eh
    have hc : h' (Gc.edge y0) ≠ h' (Gc.node y0) := by
      rw [← hh'.2 (Gc.edge y0), hfe, E1]
      show k (i (G.face (G.edge x0))) ≠ k (i (G.node x0))
      rw [← kXe, ← kn, ← hnX, ← kX]; exact hX
    obtain ⟨k', hk'c, hk'i⟩ := coloring_ecpK Gc y0 hh' hc
    refine ⟨k', hk'c, ?_⟩
    change ((Gc.ecpK y0).pointee.cpring (Gc.ecpK y0).pointer).map k' = _
    have kn' : k' ((Gc.ecpK y0).pointee.node (Gc.ecpK y0).pointer) = h' (Gc.node y0) := by
      rw [face_inv_cface hk'c.2 (Gc.cface_node_ecpK y0), hk'i]
    rw [Gc.cpring_ecpK y0]
    simp only [List.map_cons, Bool.not_false, Bool.not_true, mask_true_cons, mask_false_cons]
    rw [kn', E1, List.map_map, show k' ∘ Gc.icpK y0 = h' from funext hk'i, E3, hmap, kX, hnX, kn]
    rfl
  · -- `(T, F, F, F, T)`: no new step
    have hnX : k (M.edge (Icp (Icp IcpXe))) = k (Icp (Icp IcpXe)) :=
      (hnew _ hzN).2 (by simp [insertE])
    refine ⟨h', hh', ?_⟩
    change (Gc.cpring y0).map h' = _
    simp only [List.map_cons, Bool.not_false, Bool.not_true, mask_true_cons, mask_false_cons]
      at Eh ⊢
    rw [Eh, hmap, kX, hnX, kn]
    rfl
  · -- `(T, T, F, F, F)`: an `A` step
    have hnX : k (M.edge (Icp (Icp IcpXe))) = k (Icp (Icp IcpXe)) :=
      (hnew _ hzN).2 (by simp [insertE])
    have hX : k (M.edge IcpX) = k IcpX := (hnew _ hzX).2 (by simp [insertE])
    simp only [List.map_cons, Bool.not_false, mask_true_cons] at Eh
    obtain ⟨E1, -, E3, hfe⟩ := hfe_of [] Eh
    have hall' : ∃ b ∈ mr, b = false := by simpa using hall
    have hlong : Gc.LongCpring y0 := by
      rw [size_long_cpring, hrc]
      have h1 : 0 < ((Gc.cpring y0).drop 2).length := by
        rw [← List.length_map (f := h'), E3, List.length_map,
          length_mask (by rw [List.length_map, hlm]), List.countP_pos_iff]
        obtain ⟨b, hb, rfl⟩ := hall'
        exact ⟨true, List.mem_map.2 ⟨false, hb, rfl⟩, rfl⟩
      simp only [List.length_cons]; omega
    have hA : h' (Gc.node y0) = h' (Gc.face (Gc.edge y0)) := by
      rw [hfe, E1]
      show k (i (G.node x0)) = k (i (G.face (G.edge x0)))
      rw [← kn, ← kXe, hX, kX, hnX]
    refine ⟨h', coloring_ecpA Gc y0 hh' hA, ?_⟩
    change ((Gc.ecpA y0).pointee.cpring (Gc.ecpA y0).pointer).map h' = _
    rw [cpring_ecpA, ite_eq_left hlong, hrc]
    simp only [List.tail_cons, List.map_cons, Bool.not_true, mask_false_cons]
    rw [E3, hmap]

end CfContract

/-- math-comp `cfctr_correct`.  (math-comp states the conclusion as
`if cfctr mr mc cp is Some cpc then ... else True`.) -/
theorem cfctr_correct {mr mc : List Bool} {cp : Cprog}
    (hmr : mr.length = cprsize cp) (hmc : mc.length = ctrmsize cp)
    {k : (cpmap cp).D → Color}
    (hk : (cpmap cp).pointee.CcColoring
      (mask mr ((cpmap cp).pointee.cpring (cpmap cp).pointer) ++ mask mc (ctrenum cp)) k)
    {cpc : Cprog} (h : cfctr mr mc cp = some cpc) :
    ∃ k', (cpmap cpc).pointee.Coloring k' ∧
      ((cpmap cpc).pointee.cpring (cpmap cpc).pointer).map k' =
        (mask (mr.map not) ((cpmap cp).pointee.cpring (cpmap cp).pointer)).map k := by
  suffices hall : ∀ cp, CfContract.CtrCorrect cp from hall cp mr mc hmr hmc k hk cpc h
  intro cp
  induction cp with
  | nil =>
    intro mr mc _ _ k _ cpc h
    exact absurd (cfctr_config_prog h) (by simp [configProg])
  | cons s cp ih =>
    cases s with
    | R n => exact CfContract.ctrCorrect_R n ih
    | Y =>
      cases cp with
      | nil => exact CfContract.ctrCorrect_Y0
      | cons s' cp' => exact CfContract.ctrCorrect_Y ih
    | H => exact CfContract.ctrCorrect_H ih
    | _ =>
      intro mr mc _ _ k _ cpc h
      exact absurd (cfctr_config_prog h) (by simp [configProg])

end FourColor
