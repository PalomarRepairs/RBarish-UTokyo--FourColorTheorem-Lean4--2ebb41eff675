/-
Copyright (c) 2026. Lean 4 port of the planarity part of the Coq/Rocq formal proof
of the Four Color Theorem by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Walkup.Basic

/-!
# The Walkup construction: connected components  (port of `walkup.v`, part 3)

Counting the connected components of `WalkupE z`, leading to `euler_lhs_WalkupE` (the
left-hand side of the Euler formula for `WalkupE z`, in terms of that of `G`), and the
key geometric fact `disconnected_cross_edge`: removing a non-degenerate dart `z` can only
disconnect its component if `z` and `node z` lie on the same edge cycle.
-/

namespace FourColor

open Function

universe u

namespace Hypermap

variable {D : Type u} [Fintype D] [DecidableEq D] (G : Hypermap D) (z : D)

omit [DecidableEq D] in
/-- math-comp local `z_barb_z`. -/
theorem zBarb_iff : G.ZBarb z ↔ G.edge z = z ∧ G.node z = z ∧ G.face z = z := by
  constructor
  · intro h
    have hf : G.face z = z := h _ (G.clinkF z)
    have hfe : G.face (G.edge z) = z := h (G.face (G.edge z)) (Or.inl (G.edgeK z).symm)
    have he : G.edge z = z := G.faceI (hfe.trans hf.symm)
    refine ⟨he, ?_, hf⟩
    have := G.edgeK z
    rwa [he, hf] at this
  · rintro ⟨-, hn, hf⟩ y (hy | hy)
    · exact G.nodeI (hy.symm.trans hn.symm)
    · exact hy.symm.trans hf

/-- math-comp local `clink_at_G'`: a C-link of `G` between two darts other than `z` is a
C-link of `WalkupE z`. -/
private theorem clink_Walkup_of_clink {u v : WDart z} (h : G.clink u.1 v.1) :
    (G.WalkupE z).clink u v := by
  rw [clink_WalkupE_iff]
  rcases h with h | h
  · left
    rw [skip1_of_ne z (fun h' => u.2 (h.trans h'))]
    exact h
  · right
    rw [skip1_of_ne z (fun h' => v.2 (h.symm.trans h'))]
    exact h

/-- math-comp local `clink_at_G`: C-paths of `WalkupE z` project to C-paths of `G`. -/
theorem connect_clink_val {u v : WDart z} (h : connect (G.WalkupE z).clink u v) :
    connect G.clink u.1 v.1 := by
  induction h with
  | refl => exact connect_refl _
  | @tail b c _ hbc ih =>
    refine connect_trans ih ?_
    rw [clink_WalkupE_iff] at hbc
    rcases hbc with h | h
    · by_cases hn : G.node c.1 = z
      · -- the link skipped over `z`: `b = node z` and `z = node c`
        rw [skip1_of_eq z hn] at h
        have h1 : G.clink b.1 z := Or.inl h
        have h2 : G.clink z c.1 := Or.inl hn.symm
        exact connect_trans (connect_of_rel h1) (connect_of_rel h2)
      · rw [skip1_of_ne z hn] at h
        exact connect_of_rel (Or.inl h)
    · by_cases hf : G.face b.1 = z
      · -- the link skipped over `z`: `face b = z` and `face z = c`
        rw [skip1_of_eq z hf] at h
        have h1 : G.clink b.1 z := Or.inr hf
        have h2 : G.clink z c.1 := Or.inr h
        exact connect_trans (connect_of_rel h1) (connect_of_rel h2)
      · rw [skip1_of_ne z hf] at h
        exact connect_of_rel (Or.inr h)

/-- math-comp local `z_comp_preimage`. -/
theorem zComp_preimage (v : WDart z) : v ∈ G.zComp z ↔ connect G.clink z v.1 := by
  constructor
  · rintro ⟨w, hw, hvw⟩
    have h1 : connect G.clink v.1 w.1 := G.connect_clink_val z hvw
    exact connect_trans (connect_of_rel hw) (G.clinkC _ _ h1)
  · intro h
    obtain ⟨p₀, hp₀, hl₀⟩ := connect_iff_path.1 h
    obtain ⟨p, hp, hu, -, hl⟩ := shortenP hp₀
    rw [hl₀] at hl
    cases p with
    | nil => exact absurd hl.symm v.2
    | cons x p =>
      have hz : z ∉ x :: p := (List.nodup_cons.1 hu).1
      have hxz : x ≠ z := fun h => hz (h ▸ List.mem_cons_self)
      have hpz : z ∉ p := fun h => hz (List.mem_cons_of_mem _ h)
      obtain ⟨q, hq⟩ := Walkup_seq z hpz
      let w : WDart z := ⟨x, hxz⟩
      refine ⟨w, hp.1, (G.WalkupE z).clinkC _ _ (connect_iff_path.2 ⟨q, ?_, ?_⟩)⟩
      · have h2 : path G.clink w.1 (q.map Subtype.val) := by rw [hq]; exact hp.2
        rw [path_map] at h2
        exact h2.mono fun a b h => G.clink_Walkup_of_clink z h
      · apply Subtype.ext
        rw [← last_map Subtype.val w q, hq]
        exact hl

/-- math-comp local `z_barb_comp`. -/
theorem zBarb_comp : G.ZBarb z ↔ nComp (G.WalkupE z).clink (G.zComp z) = 0 := by
  rw [nComp_eq_zero, Set.eq_empty_iff_forall_notMem]
  constructor
  · rintro h v ⟨w, hw, -⟩
    exact w.2 (h _ hw)
  · intro h y hy
    by_contra hyz
    exact h ⟨y, hyz⟩ (subset_closure (e := (G.WalkupE z).clink) _ hy)

/-- The key step of math-comp local `disconnected_cross_edge` (after its `without loss`):
if `z` is degenerate or not a cross edge, a C-neighbour `u` of `z` is connected in
`WalkupE z` to `w = face z`. -/
private theorem gcomp_Walkup_face (hz : G.glink z z ∨ ¬ G.crossEdge z) {u w : WDart z}
    (hu : G.clink z u.1) (hw : G.face z = w.1) : (G.WalkupE z).gcomp u w := by
  rcases hu with hu | hu
  · have Du : G.face (G.edge z) = u.1 := G.eq_node_iff.1 hu
    by_cases hez : G.edge z = z
    · have : u = w := Subtype.ext (by rw [← Du, hez, hw])
      subst this
      exact connect_refl _
    · let v : WDart z := ⟨G.edge z, hez⟩
      have hfv : (G.WalkupE z).face v = u := by
        apply Subtype.ext
        rw [WalkupE_face_val, skip1_of_ne z (by rw [Du]; exact u.2)]
        exact Du
      have hcz : ¬ G.crossEdge z := by
        rcases hz with hz | hz
        · exfalso
          rcases hz with h | h | h
          · exact hez h
          · apply u.2
            rw [← Du]
            exact G.eq_node_iff.1 h.symm
          · exact w.2 (hw.symm.trans h)
        · exact hz
      have hnw : ((G.WalkupE z).node w).1 = G.node (G.face z) := by
        rw [WalkupE_node_val, ← hw, skip1_of_ne z]
        intro h
        exact hez (G.edge_eq_iff.2 h.symm)
      have hc : (G.WalkupE z).cedge v ((G.WalkupE z).node w) :=
        G.not_cross_edge_Walkup z hcz rfl hnw
      have h1 : (G.WalkupE z).gcomp u v := by
        rw [← hfv]
        exact (G.WalkupE z).glinkC _ _ (connect_of_rel ((G.WalkupE z).glinkF v))
      have h2 : (G.WalkupE z).gcomp v ((G.WalkupE z).node w) :=
        (G.WalkupE z).gcomp_of_cedge hc
      have h3 : (G.WalkupE z).gcomp ((G.WalkupE z).node w) w :=
        (G.WalkupE z).glinkC _ _ (connect_of_rel ((G.WalkupE z).glinkN w))
      exact connect_trans h1 (connect_trans h2 h3)
  · have : u = w := Subtype.ext (hu.symm.trans hw)
    subst this
    exact connect_refl _

/-- math-comp local `disconnected_cross_edge`, main step: if `z` is degenerate or not a
cross edge, all the C-neighbours of `z` are connected in `WalkupE z`. -/
private theorem gcomp_Walkup_clink (hz : G.glink z z ∨ ¬ G.crossEdge z) {u w : WDart z}
    (hu : G.clink z u.1) (hw : G.clink z w.1) : (G.WalkupE z).gcomp u w := by
  rcases hw with hw | hw
  · rcases hu with hu | hu
    · have : u = w := Subtype.ext (G.nodeI (hu.symm.trans hw))
      subst this
      exact connect_refl _
    · exact (G.WalkupE z).glinkC _ _ (G.gcomp_Walkup_face z hz (Or.inl hw) hu)
  · exact G.gcomp_Walkup_face z hz hu hw

/-- math-comp local `disconnected_cross_edge`, contrapositive form. -/
private theorem nComp_zComp_le_one (hz : G.glink z z ∨ ¬ G.crossEdge z) :
    nComp (G.WalkupE z).clink (G.zComp z) ≤ 1 := by
  by_cases hb : G.ZBarb z
  · rw [(G.zBarb_comp z).1 hb]
    omega
  · unfold ZBarb at hb
    push Not at hb
    obtain ⟨x, hx, hxz⟩ := hb
    let u : WDart z := ⟨x, hxz⟩
    have hcomp : G.zComp z = comp (G.WalkupE z).clink u := by
      ext v
      rw [mem_comp]
      constructor
      · rintro ⟨w, hw, hvw⟩
        have h1 := ((G.WalkupE z).clink_glink u w).2 (G.gcomp_Walkup_clink z hz hx hw)
        exact connect_trans h1 ((G.WalkupE z).clinkC _ _ hvw)
      · intro huv
        exact ⟨u, hx, (G.WalkupE z).clinkC _ _ huv⟩
    rw [hcomp, nComp_comp (G.WalkupE z).clinkC]

/-- math-comp local `disconnected_cross_edge`. -/
theorem disconnected_cross_edge (h : G.Disconnected z) : ¬ G.glink z z ∧ G.crossEdge z := by
  by_contra hc
  have hz : G.glink z z ∨ ¬ G.crossEdge z := by
    by_cases h1 : G.glink z z
    · exact Or.inl h1
    · exact Or.inr fun h2 => hc ⟨h1, h2⟩
  have := G.nComp_zComp_le_one z hz
  unfold Disconnected at h
  omega

/-- math-comp local `not_cross_connected`. -/
theorem not_cross_connected (h : ¬ G.crossEdge z) : ¬ G.Disconnected z :=
  fun hd => h (G.disconnected_cross_edge z hd).2

/-- math-comp local `n_comp_glink_Walkup`. -/
theorem nComp_glink_Walkup :
    G.nCompZ z (G.Disconnected z) + nComp (G.WalkupE z).glink Set.univ
      = nComp G.glink Set.univ + 1 := by
  rw [← nComp_congr G.clink_glink Set.univ, ← nComp_congr (G.WalkupE z).clink_glink Set.univ]
  -- split along the C-component `a` of `z`
  let a : Set D := comp G.clink z
  have ha : Closed G.clink a := closed_comp G.clinkC z
  have ha' : Closed (G.WalkupE z).clink (Subtype.val ⁻¹' a) := fun u v huv =>
    ha.connect_iff (G.connect_clink_val z (connect_of_rel huv))
  rw [nComp_compl ha, nComp_compl ha', nComp_comp G.clinkC z]
  -- outside of `a`, the C-links of `G` and `WalkupE z` coincide
  have hadj : nComp G.clink aᶜ = nComp (G.WalkupE z).clink (Subtype.val ⁻¹' a)ᶜ := by
    have hza : z ∈ a := connect_refl z
    have hnz : G.node z ∈ a := G.clinkC _ _ (connect_of_rel (G.clinkN z))
    have henz : G.edge (G.node z) ∈ a :=
      G.clinkC _ _ (connect_of_rel (show G.clink (G.edge (G.node z)) z from Or.inr (G.nodeK z)))
    have hcod : aᶜ ⊆ Set.range (Subtype.val : WDart z → D) := fun x hx =>
      ⟨⟨x, fun h => hx (h ▸ hza)⟩, rfl⟩
    rw [nComp_adjunction G.clinkC (G.WalkupE z).clinkC Subtype.val hcod, Set.preimage_compl]
    intro x' y' hx' _
    refine connect_iff_of_base Subtype.val_injective (fun x y hxy hx => (ha.compl x y hxy).1 hx)
      hcod (fun x' y' hx' => G.base_clink_Walkup z ?_ ?_) hx'
    · intro h
      exact hx' (h ▸ henz)
    · intro h
      exact hx' (h ▸ hnz)
  have hzc : nComp (G.WalkupE z).clink (Subtype.val ⁻¹' a) =
      nComp (G.WalkupE z).clink (G.zComp z) :=
    nComp_congr_set fun v => (G.zComp_preimage z v).symm
  rw [hadj, hzc]
  suffices h2 : G.nCompZ z (G.Disconnected z) + nComp (G.WalkupE z).clink (G.zComp z) = 2 by
    omega
  by_cases hd : G.Disconnected z
  · obtain ⟨hg, -⟩ := G.disconnected_cross_edge z hd
    have hz0 : G.nCompZ z (G.Disconnected z) = 0 := by
      unfold nCompZ
      rw [ite_eq_right hg, ite_eq_left hd]
    rw [hz0, zero_add]
    -- `zComp` is the closure of the two C-neighbours `face (edge z)` and `face z` of `z`
    have hnz : G.node z ≠ z := fun h => hg (Or.inr (Or.inl h))
    have hfz : G.face z ≠ z := fun h => hg (Or.inr (Or.inr h))
    have hfez : G.face (G.edge z) ≠ z := fun h => hnz (G.eq_node_iff.2 h).symm
    have hS : Subtype.val ⁻¹' {y | G.clink z y} =
        ({⟨G.face (G.edge z), hfez⟩, ⟨G.face z, hfz⟩} : Set (WDart z)) := by
      ext w
      simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_insert_iff,
        Set.mem_singleton_iff, Subtype.ext_iff]
      unfold clink
      rw [G.eq_node_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h.symm
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr h.symm
    have hle : nComp (G.WalkupE z).clink (G.zComp z) ≤ 2 := by
      unfold zComp
      rw [hS]
      exact nComp_closure2_le (G.WalkupE z).clinkC _ _
    unfold Disconnected at hd
    omega
  · by_cases h0 : nComp (G.WalkupE z).clink (G.zComp z) = 0
    · have hb := (G.zBarb_comp z).2 h0
      have hg : G.glink z z := Or.inl ((G.zBarb_iff z).1 hb).1
      unfold nCompZ
      rw [ite_eq_left hg, ite_eq_left hb, h0]
    · have hb : ¬ G.ZBarb z := fun hb => h0 ((G.zBarb_comp z).1 hb)
      have h1 : nComp (G.WalkupE z).clink (G.zComp z) = 1 := by
        unfold Disconnected at hd
        omega
      unfold nCompZ
      rw [h1]
      by_cases hg : G.glink z z
      · rw [ite_eq_left hg, ite_eq_right hb]
      · rw [ite_eq_right hg, ite_eq_right hd]

/-- math-comp local `Euler_lhs_WalkupE`. -/
theorem euler_lhs_WalkupE :
    2 * G.nCompZ z (G.Disconnected z) + (G.WalkupE z).eulerLhs = G.eulerLhs + 1 := by
  have h1 := G.nComp_glink_Walkup z
  have h2 := card_S_Walkup z
  unfold eulerLhs
  omega

end Hypermap

end FourColor
