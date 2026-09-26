/-
Copyright (c) 2026. Lean 4 port of the planarity part of the Coq/Rocq formal proof
of the Four Color Theorem by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Walkup.Basic

/-!
# The Walkup construction: edge cycles  (port of `walkup.v`, part 2)

Counting the edge cycles of `WalkupE z`, leading to `euler_rhs_WalkupE` (the right-hand side
of the Euler formula for `WalkupE z`, in terms of that of `G`).
-/

namespace FourColor

open Function

universe u

namespace Hypermap

variable {D : Type u} [Fintype D] [DecidableEq D]

section Skip

variable (z : D) {f : D → D}

omit [Fintype D] in
/-- math-comp `fconnect_skip`. -/
theorem fconnect_skip (hf : Injective f) (u v : WDart z) :
    fconnect (skip z hf) u v ↔ fconnect f u.1 v.1 := by
  constructor
  · -- Each `skip` step is one or two `f` steps.
    intro h
    induction h with
    | refl => exact connect_refl _
    | tail hab hbc ih =>
      rename_i w w'
      subst hbc
      refine connect_trans ih ?_
      by_cases hw : f w.1 = z
      · rw [skip_val, skip1_of_eq z hw]
        exact connect_trans (connect_of_rel hw) (connect_of_rel rfl)
      · rw [skip_val, skip1_of_ne z hw]
        exact connect_of_rel rfl
  · -- Strong induction on the number `n` of `f` steps.
    intro h
    obtain ⟨n, hn⟩ := fconnect_iff_iterate.1 h
    clear h
    induction n using Nat.strong_induction_on generalizing u with
    | _ n ih =>
      cases n with
      | zero => obtain rfl : u = v := Subtype.ext hn; exact connect_refl _
      | succ m =>
        rw [iterate_succ_apply] at hn
        by_cases hfu : f u.1 = z
        · -- The two `f` steps through `z` are merged into one `skip` step.
          cases m with
          | zero => exact absurd (hn.symm.trans hfu) v.2
          | succ k =>
            rw [hfu, iterate_succ_apply] at hn
            have hs : (skip z hf u).1 = f z := skip1_of_eq z hfu
            exact Relation.ReflTransGen.head rfl
              (ih k (by omega) (skip z hf u) (by rw [hs]; exact hn))
        · have hs : (skip z hf u).1 = f u.1 := skip1_of_ne z hfu
          exact Relation.ReflTransGen.head rfl
            (ih m (by omega) (skip z hf u) (by rw [hs]; exact hn))

open Classical in
/-- math-comp `fcard_skip`. -/
theorem fcard_skip (hf : Injective f) :
    (if f z = z then 1 else 0) + fcard (skip z hf) Set.univ = fcard f Set.univ := by
  have hs := fconnect_sym hf
  have hs' := fconnect_sym (inj_skip z hf)
  -- Split both counts along the `f`-orbit `a` of `z` (and its preimage).
  have ha : Closed (frel f) (comp (frel f) z) := closed_comp hs z
  have ha' : Closed (frel (skip z hf)) (Subtype.val ⁻¹' comp (frel f) z) := by
    refine Closed.of_forward hs' fun x y hxy hx => ?_
    exact connect_trans hx ((fconnect_skip z hf x y).1 (connect_of_rel hxy))
  -- Outside `a`, the orbits of `f` and `skip z hf` correspond.
  have hadj : nComp (frel f) (comp (frel f) z)ᶜ
      = nComp (frel (skip z hf)) (Subtype.val ⁻¹' comp (frel f) z)ᶜ := by
    rw [← Set.preimage_compl]
    refine nComp_adjunction hs hs' Subtype.val (fun x hx => ?_) fun x' y' _ _ => ?_
    · have hxz : x ≠ z := by rintro rfl; exact hx (connect_refl _)
      exact ⟨⟨x, hxz⟩, rfl⟩
    · exact fconnect_skip z hf x' y'
  show _ + nComp (frel (skip z hf)) Set.univ = nComp (frel f) Set.univ
  rw [nComp_compl ha, nComp_compl ha', nComp_comp hs z, hadj]
  suffices (if f z = z then 1 else 0) + nComp (frel (skip z hf)) (Subtype.val ⁻¹' comp (frel f) z)
      = 1 by omega
  split_ifs with hfz
  · -- The orbit of `z` is `{z}`, and disappears.
    have : Subtype.val ⁻¹' comp (frel f) z = (∅ : Set (WDart z)) := by
      ext u
      simp only [Set.mem_preimage, mem_comp, Set.mem_empty_iff_false, iff_false]
      intro hu
      obtain ⟨n, hn⟩ := fconnect_iff_iterate.1 hu
      exact u.2 (hn.symm.trans (iterate_fixed hfz n))
    rw [this, nComp_empty]
  · -- The orbit of `z` loses `z`, and remains a single orbit, that of `f z`.
    have : Subtype.val ⁻¹' comp (frel f) z = comp (frel (skip z hf)) ⟨f z, hfz⟩ := by
      ext u
      exact (same_fconnect1 hf z u.1).trans (fconnect_skip z hf ⟨f z, hfz⟩ u).symm
    rw [this, nComp_comp hs']

end Skip

section SkipEdge

variable (G : Hypermap D) (z : D)

omit [DecidableEq D] in
/-- `skip_edge_domain z` is closed under `edge`. -/
private theorem edge_mem_edom {x : D} (hx : x ∈ G.skipEdgeDomain z) :
    G.edge x ∈ G.skipEdgeDomain z := by
  rcases hx with h | h
  · exact Or.inl ((G.cedge1 x z).1 h)
  · exact Or.inr ((G.cedge1 x _).1 h)

omit [DecidableEq D] in
/-- math-comp local `eCedom` (in forward form): the complement of `skip_edge_domain z` is
closed under `edge`. -/
private theorem edge_not_mem_edom {x : D} (hx : x ∉ G.skipEdgeDomain z) :
    G.edge x ∉ G.skipEdgeDomain z := by
  intro h
  apply hx
  rcases h with h | h
  · exact Or.inl ((G.cedge1 x z).2 h)
  · exact Or.inr ((G.cedge1 x _).2 h)

omit [DecidableEq D] in
private theorem mem_edom_nfz : G.node (G.face z) ∈ G.skipEdgeDomain z :=
  Or.inl (connect_of_rel (G.faceK z))

omit [Fintype D] [DecidableEq D] in
private theorem mem_edom_nz : G.node z ∈ G.skipEdgeDomain z := Or.inr (connect_refl _)

omit [Fintype D] [DecidableEq D] in
private theorem ne_of_not_mem_edom {x : D} (hx : x ∉ G.skipEdgeDomain z) : x ≠ z := by
  rintro rfl
  exact hx (Or.inl (connect_refl _))

/-- math-comp `same_cskip_edge` (via the local adjunction `adj_edom`). -/
theorem same_cskip_edge {u v : WDart z} (hu : u.1 ∉ G.skipEdgeDomain z) :
    (G.WalkupE z).cedge u v ↔ G.cedge u.1 v.1 := by
  refine connect_iff_of_base (e := frel G.edge) (e' := frel (G.WalkupE z).edge)
    (a := (G.skipEdgeDomain z)ᶜ) Subtype.val_injective (fun x y hxy hx => ?_) (fun x hx => ?_)
    (fun x' y' hx' => ?_) hu
  · exact hxy ▸ G.edge_not_mem_edom z hx
  · exact ⟨⟨x, G.ne_of_not_mem_edom z hx⟩, rfl⟩
  · refine G.base_skip_edge z (fun h => hx' ?_) (fun h => hx' ?_)
    · rw [h]; exact G.mem_edom_nfz z
    · rw [h]; exact G.mem_edom_nz z

omit [DecidableEq D] in
/-- `node (face z) ≠ z` when `edge z ≠ z` (math-comp `z'nfz`). -/
private theorem nfz_ne (hez : G.edge z ≠ z) : G.node (G.face z) ≠ z := by
  intro h
  have := G.faceK z
  rw [h] at this
  exact hez this

/-- A single edge step of `G` between two darts of `WalkupE z` is an edge connection of
`WalkupE z`, when `¬ cross_edge z` (the step case of math-comp `sub_cskip_edge`). -/
private theorem cskip_edge_step (hz : ¬ G.crossEdge z) (hez : G.edge z ≠ z) {x y : WDart z}
    (h : G.edge x.1 = y.1) : (G.WalkupE z).cedge x y := by
  by_cases hfy : G.face y.1 = z
  · -- `skipEdge x = edge z`, which is connected to `node (face y) = node (face z)`, whose
    -- `WalkupE z` edge successor is `y`.
    have hx' : ((G.WalkupE z).edge x).1 = G.edge z :=
      G.skipEdge1_of_face_edge z hez (by rw [h]; exact hfy)
    have hy' : ((G.WalkupE z).node ((G.WalkupE z).face y)).1 = G.node (G.face z) := by
      rw [WalkupE_node_val, WalkupE_face_val, skip1_of_eq z hfy, skip1_of_ne z (G.nfz_ne z hez)]
    refine connect_trans (connect_of_rel rfl)
      (connect_trans (G.not_cross_edge_Walkup z hz hx' hy') (connect_of_rel ?_))
    exact (G.WalkupE z).faceK y
  · apply connect_of_rel
    apply Subtype.ext
    show G.skipEdge1 z x.1 = y.1
    rw [G.skipEdge1_of_ne z hez (by rw [h]; exact hfy) (by rw [h]; exact y.2), h]

/-- An edge step of `G` into `z` is replaced by an edge connection of `WalkupE z` to
`edge z`, when `¬ cross_edge z` (the `z` case of math-comp `sub_cskip_edge`). -/
private theorem cskip_edge_step_z (hz : ¬ G.crossEdge z) (hez : G.edge z ≠ z) {x : WDart z}
    (h : G.edge x.1 = z) : (G.WalkupE z).cedge x ⟨G.edge z, hez⟩ :=
  (G.WalkupE z).cedgeC.1 (G.not_cross_edge_Walkup z hz rfl ((G.edge_eq_iff).1 h))

/-- math-comp `sub_cskip_edge`. -/
theorem sub_cskip_edge {u v : WDart z} (hz : ¬ G.crossEdge z) (h : G.cedge u.1 v.1) :
    (G.WalkupE z).cedge u v := by
  by_cases hez : G.edge z = z
  · -- `z` is an edge fixpoint, so `skipEdge = skip edge`.
    exact (fconnect_congr (G.glink_fp_skip_edge z (Or.inl hez))).2
      ((fconnect_skip z G.edgeI u v).2 h)
  · -- Follow the edge path of `G` from `u`, jumping from `z` to `edge z`.
    have key : ∀ y, G.cedge u.1 y → (∀ hy : y ≠ z, (G.WalkupE z).cedge u ⟨y, hy⟩) ∧
        (y = z → (G.WalkupE z).cedge u ⟨G.edge z, hez⟩) := by
      intro y hy
      induction hy with
      | refl => exact ⟨fun _ => connect_refl _, fun h => absurd h u.2⟩
      | tail hab hbc ih =>
        rename_i w w'
        by_cases hw : w = z
        · subst hbc
          refine ⟨fun hw' => ?_, fun _ => ih.2 hw⟩
          have : (⟨G.edge w, hw'⟩ : WDart z) = ⟨G.edge z, hez⟩ := Subtype.ext (congrArg G.edge hw)
          rw [this]
          exact ih.2 hw
        · refine ⟨fun hw' => ?_, fun hw' => ?_⟩
          · exact connect_trans (ih.1 hw)
              (G.cskip_edge_step z hz hez (x := ⟨w, hw⟩) (y := ⟨w', hw'⟩) hbc)
          · exact connect_trans (ih.1 hw)
              (G.cskip_edge_step_z z hz hez (x := ⟨w, hw⟩) (hbc.trans hw'))
    exact (key v.1 h).1 v.2

/-- The main case of math-comp `cskip_edge_merge`: `u` is on the edge cycle of `z`. -/
private theorem cskip_edge_merge_aux (hz : ¬ G.crossEdge z) {u v : WDart z}
    (hu : G.cedge u.1 z) (hv : v.1 ∈ G.skipEdgeDomain z) : (G.WalkupE z).cedge u v := by
  rcases hv with hv | hv
  · exact G.sub_cskip_edge z hz (connect_trans hu ((G.cedgeC).1 hv))
  · have hez : G.edge z ≠ z := by
      intro hez
      obtain ⟨n, hn⟩ := fconnect_iff_iterate.1 ((G.cedgeC).1 hu)
      exact u.2 (hn.symm.trans (iterate_fixed hez n))
    have hfz : G.face z ≠ z := by
      intro hfz
      apply hz
      have : G.edge (G.node z) = z := by have := G.faceK z; rwa [hfz] at this
      exact (G.cedge1r z (G.node z)).2 ((congrArg (G.cedge z) this).mpr (connect_refl z))
    -- Go from `u` to `node (face z)`, then from its `WalkupE z` edge successor
    -- `edge (node z)` to `v`.
    let w : WDart z := ⟨G.node (G.face z), G.nfz_ne z hez⟩
    have huw : (G.WalkupE z).cedge u w :=
      G.sub_cskip_edge z hz ((G.cedge1r _ _).2 (by rw [G.faceK]; exact hu))
    have hw' : ((G.WalkupE z).edge w).1 = G.edge (G.node z) := by
      show G.skipEdge1 z (G.node (G.face z)) = _
      exact G.skipEdge1_of_edge z hez (by rw [G.faceK]; exact hfz) (G.faceK z)
    have hwv : (G.WalkupE z).cedge w v := by
      refine ((G.WalkupE z).cedge1 w v).2 ((G.WalkupE z).cedgeC.1 (G.sub_cskip_edge z hz ?_))
      rw [hw']
      exact (G.cedge1r _ _).1 hv
    exact connect_trans huw hwv

/-- math-comp `cskip_edge_merge`. -/
theorem cskip_edge_merge {u v : WDart z} (hz : ¬ G.crossEdge z)
    (hu : u.1 ∈ G.skipEdgeDomain z) :
    (G.WalkupE z).cedge u v ↔ v.1 ∈ G.skipEdgeDomain z := by
  constructor
  · intro huv
    by_contra hv
    have h1 : G.cedge v.1 u.1 := (G.same_cskip_edge z hv).1 ((G.WalkupE z).cedgeC.1 huv)
    exact mem_of_connect_of_forward (e := frel G.edge) (a := (G.skipEdgeDomain z)ᶜ)
      (fun x y hxy hx => hxy ▸ G.edge_not_mem_edom z hx) h1 hv hu
  · intro hv
    -- Without loss of generality `u` is on the edge cycle of `z`.
    rcases hu with hu | hu
    · exact G.cskip_edge_merge_aux z hz hu hv
    · rcases hv with hv | hv
      · exact (G.WalkupE z).cedgeC.1 (G.cskip_edge_merge_aux z hz hv (Or.inr hu))
      · exact G.sub_cskip_edge z hz (connect_trans hu ((G.cedgeC).1 hv))

/-- If `cross_edge z` holds and `z` is not degenerate, then `node (face z)` and `node z` lie on
different edge cycles of `WalkupE z`: the arc of the edge cycle of `G` from `edge z` to `node z`
becomes an edge cycle of `WalkupE z`, which does not contain `node (face z)` (the cross-edge
case in the proof of math-comp `fcard_skip_edge`). -/
private theorem not_cskip_edge_cross (hc : G.crossEdge z) (hez : G.edge z ≠ z)
    (hnz : G.node z ≠ z) (hfz : G.face z ≠ z) {w w1 : WDart z}
    (hw : w.1 = G.node (G.face z)) (hw1 : w1.1 = G.node z) :
    ¬ (G.WalkupE z).cedge w w1 := by
  intro hww1
  -- A duplicate-free edge path from `node (face z)` to `node z`; it starts with `z, edge z`.
  obtain ⟨p0, hp0, hl0⟩ := connect_iff_path.1
    (connect_trans (connect_of_rel (G.faceK z)) hc : G.cedge (G.node (G.face z)) (G.node z))
  obtain ⟨p, hp, hnd, -, hl⟩ := shortenP hp0
  rw [hl0] at hl
  rcases p with _ | ⟨y, _ | ⟨y1, p⟩⟩
  · exact hfz (G.nodeI hl)
  · exact hnz (hl.symm.trans (hp.1.symm.trans (G.faceK z)))
  obtain ⟨hy, hy1, hp⟩ := hp
  have hy' : y = z := hy.symm.trans (G.faceK z)
  rw [hy'] at hy1 hnd
  subst hy1
  rw [last_cons, last_cons] at hl
  rw [List.nodup_cons, List.nodup_cons] at hnd
  obtain ⟨hnfz, hzp, hnd⟩ := hnd
  have hnfz' : G.node (G.face z) ∉ G.edge z :: p := fun h => hnfz (List.mem_cons_of_mem _ h)
  -- Lift the arc `edge z :: p` to `WalkupE z`.
  obtain ⟨q, hq⟩ := Walkup_seq z hzp
  rcases q with _ | ⟨ew, q⟩
  · simp at hq
  rw [List.map_cons, List.cons.injEq] at hq
  obtain ⟨hew, hq⟩ := hq
  -- It is an edge cycle of `WalkupE z`: `skipEdge` agrees with `edge` along the arc, and
  -- maps its last dart `node z` back to `edge z`.
  have hcyc : fcycle (G.WalkupE z).edge (ew :: q) := by
    show cycle (frel (G.WalkupE z).edge) (ew :: q)
    rw [cycle_cons, path_concat]
    constructor
    · have hpq : path (frel G.edge) ew.1 (q.map Subtype.val) := by rw [hq, hew]; exact hp
      refine (path_map_base (b := fun x => x = G.node (G.face z) ∨ x = G.node z) ?_ ?_).1 hpq
      · intro x y hx
        rw [not_or] at hx
        exact G.base_skip_edge z hx.1 hx.2
      · intro y hy hb
        have hy' : y.1 ∈ belast (G.edge z) p := by
          rw [← hew, ← hq, belast_map]; exact List.mem_map_of_mem hy
        rcases hb with hb | hb
        · exact hnfz' (by rw [← hb]; exact mem_belast hy')
        · rw [lastI (G.edge z) p, List.nodup_append, hl] at hnd
          exact hnd.2.2 _ hy' _ (List.mem_singleton_self _) hb
    · apply Subtype.ext
      show G.skipEdge1 z (last ew q).1 = ew.1
      rw [← last_map Subtype.val ew q, hq, hew, hl]
      exact G.skipEdge1_of_face_edge z hez (G.nodeK z)
  -- `node z` is on this cycle, but `node (face z)` is not.
  have hmap : (ew :: q).map Subtype.val = G.edge z :: p := by rw [List.map_cons, hq, hew]
  have hmem : ∀ x : WDart z, x ∈ ew :: q ↔ x.1 ∈ G.edge z :: p := fun x => by
    rw [← hmap, List.mem_map_of_injective Subtype.val_injective]
  have hw1q : w1 ∈ ew :: q := by
    rw [hmem, hw1, ← hl]
    exact mem_last _ _
  have hwq : w ∈ ew :: q := (fconnect_cycle hcyc hw1q).1 ((G.WalkupE z).cedgeC.1 hww1)
  rw [hmem, hw] at hwq
  exact hnfz' hwq

open Classical in
/-- math-comp local `fcard_skip_edge`. -/
theorem fcard_skip_edge :
    (if G.glink z z then (if G.edge z = z then 1 else 0) + 1
      else (if G.crossEdge z then 0 else 2)) + fcard (G.WalkupE z).edge Set.univ
      = fcard G.edge Set.univ + 1 := by
  by_cases hg : G.glink z z
  · -- `z` is degenerate: `skipEdge = skip edge`.
    rw [ite_eq_left hg]
    have h1 : fcard (G.WalkupE z).edge Set.univ = fcard (skip z G.edgeI) Set.univ :=
      nComp_congr (fun _ _ => fconnect_congr (G.glink_fp_skip_edge z hg)) Set.univ
    rw [h1, ← fcard_skip z G.edgeI]
    omega
  rw [ite_eq_right hg]
  have hez : G.edge z ≠ z := fun h => hg (Or.inl h)
  have hnz : G.node z ≠ z := fun h => hg (Or.inr (Or.inl h))
  have hfz : G.face z ≠ z := fun h => hg (Or.inr (Or.inr h))
  have hsym := G.cedge_sym
  have hsym' := (G.WalkupE z).cedge_sym
  let w : WDart z := ⟨G.node (G.face z), G.nfz_ne z hez⟩
  let w1 : WDart z := ⟨G.node z, hnz⟩
  -- `skip_edge_domain z` is edge-closed in `G`, and so is its preimage in `WalkupE z`.
  have hC : Closed (frel G.edge) (G.skipEdgeDomain z) :=
    Closed.of_forward hsym fun x y hxy hx => hxy ▸ G.edge_mem_edom z hx
  have hC' : Closed (frel (G.WalkupE z).edge) (Subtype.val ⁻¹' G.skipEdgeDomain z) := by
    refine Closed.of_forward hsym' fun x y hxy hx => ?_
    subst hxy
    show G.skipEdge1 z x.1 ∈ G.skipEdgeDomain z
    unfold skipEdge1
    split_ifs
    · exact G.edge_mem_edom z hx
    · exact Or.inl ((G.cedgeC).1 (fconnect1 _ z))
    · exact Or.inr ((G.cedgeC).1 (fconnect1 _ _))
    · exact G.edge_mem_edom z hx
  -- Outside the domain, the edge cycles are unchanged (math-comp local `adj_edom`).
  have hadj : nComp (frel G.edge) (G.skipEdgeDomain z)ᶜ
      = nComp (frel (G.WalkupE z).edge) (Subtype.val ⁻¹' G.skipEdgeDomain z)ᶜ := by
    rw [← Set.preimage_compl]
    refine nComp_adjunction hsym hsym' Subtype.val (fun x hx => ?_) fun x' y' hx' _ => ?_
    · exact ⟨⟨x, G.ne_of_not_mem_edom z hx⟩, rfl⟩
    · exact G.same_cskip_edge z hx'
  -- The domain is the edge closure of `{z, node z}` in `G` ...
  have hdom : G.skipEdgeDomain z = closure (frel G.edge) {z, G.node z} := by
    ext x
    constructor
    · rintro (h | h)
      · exact ⟨z, Set.mem_insert _ _, h⟩
      · exact ⟨G.node z, Set.mem_insert_of_mem _ rfl, h⟩
    · rintro ⟨y, hy, h⟩
      rcases hy with rfl | rfl
      · exact Or.inl h
      · exact Or.inr h
  -- ... and its preimage is the edge closure of `{node (face z), node z}` in `WalkupE z`.
  have hdom' : Subtype.val ⁻¹' G.skipEdgeDomain z
      = closure (frel (G.WalkupE z).edge) {w, w1} := by
    ext u
    constructor
    · intro hu
      -- Follow the edge path of `G` from `u` to `node (face z)` or `node z`; it can only
      -- leave `WalkupE z` edge connectivity at one of these two darts.
      have key : ∀ x y, G.cedge x y → (y = G.node (G.face z) ∨ y = G.node z) →
          ∀ u : WDart z, u.1 = x →
            ∃ v ∈ ({w, w1} : Set (WDart z)), (G.WalkupE z).cedge u v := by
        intro x y hxy hy
        induction hxy using Relation.ReflTransGen.head_induction_on with
        | refl =>
          intro u hu
          refine ⟨u, ?_, connect_refl _⟩
          rcases hy with hy | hy
          · exact Or.inl (Subtype.ext (hu.trans hy))
          · exact Or.inr (Subtype.ext (hu.trans hy))
        | head hxx' hrest ih =>
          rename_i x x'
          intro u hu
          by_cases h1 : x' = z
          · refine ⟨u, Or.inl (Subtype.ext ?_), connect_refl _⟩
            rw [hu]; exact (G.edge_eq_iff).1 (hxx'.trans h1)
          by_cases h2 : G.face x' = z
          · refine ⟨u, Or.inr (Subtype.ext ?_), connect_refl _⟩
            rw [hu]; exact (G.eq_node_iff).2 (by rw [hxx']; exact h2)
          obtain ⟨v, hv, hx'v⟩ := ih ⟨x', h1⟩ rfl
          refine ⟨v, hv, connect_trans (connect_of_rel (Subtype.ext ?_)) hx'v⟩
          show G.skipEdge1 z u.1 = x'
          rw [hu, G.skipEdge1_of_ne z hez (by rw [hxx']; exact h2) (by rw [hxx']; exact h1), hxx']
      rcases hu with hu | hu
      · exact key _ _ ((G.cedge1r _ _).2 (by rw [G.faceK]; exact hu)) (Or.inl rfl) u rfl
      · exact key _ _ hu (Or.inr rfl) u rfl
    · rintro ⟨v, hv, huv⟩
      refine (hC'.connect_iff huv).2 ?_
      rcases hv with rfl | rfl
      · exact G.mem_edom_nfz z
      · exact G.mem_edom_nz z
  -- `cross_edge z` decides between 1 and 2 edge cycles in `G`, and between 2 and 1 in
  -- `WalkupE z`.
  have hn : nComp (frel G.edge) (G.skipEdgeDomain z) = if G.crossEdge z then 1 else 2 := by
    rw [hdom]
    split_ifs with hc
    · exact nComp_closure2_of_connect hsym hc
    · exact nComp_closure2_of_not_connect hsym hc
  have hn' : nComp (frel (G.WalkupE z).edge) (Subtype.val ⁻¹' G.skipEdgeDomain z)
      = if G.crossEdge z then 2 else 1 := by
    rw [hdom']
    split_ifs with hc
    · exact nComp_closure2_of_not_connect hsym' (G.not_cskip_edge_cross z hc hez hnz hfz rfl rfl)
    · exact nComp_closure2_of_connect hsym'
        ((G.cskip_edge_merge z hc (G.mem_edom_nfz z)).2 (G.mem_edom_nz z))
  show _ + nComp (frel (G.WalkupE z).edge) Set.univ = nComp (frel G.edge) Set.univ + 1
  rw [nComp_compl hC, nComp_compl hC', hn, hn', hadj]
  split_ifs <;> omega

omit [DecidableEq D] in
/-- math-comp local `z_barb_z` (also proved as `zBarb_iff` in `Walkup/Comp.lean`, which this
file cannot import). -/
private theorem zBarb_iff_fixed : G.ZBarb z ↔ G.edge z = z ∧ G.node z = z ∧ G.face z = z := by
  constructor
  · intro h
    have hfz : G.face z = z := h _ (G.clinkF z)
    have hez : G.edge z = z :=
      G.faceI ((h (G.face (G.edge z)) (Or.inl (G.edgeK z).symm)).trans hfz.symm)
    refine ⟨hez, ?_, hfz⟩
    have := G.edgeK z
    rwa [hez, hfz] at this
  · rintro ⟨-, hnz, hfz⟩ y (hy | hy)
    · exact G.nodeI (hy.symm.trans hnz.symm)
    · exact hy.symm.trans hfz

/-- math-comp local `Euler_rhs_WalkupE`. -/
theorem euler_rhs_WalkupE :
    2 * G.nCompZ z (G.crossEdge z) + (G.WalkupE z).eulerRhs = G.eulerRhs + 1 := by
  have hE := G.fcard_skip_edge z
  have hN := fcard_skip z G.nodeI
  have hF := fcard_skip z G.faceI
  have hZ := G.zBarb_iff_fixed z
  -- If two of `edge z = z`, `node z = z`, `face z = z` hold, then so does the third.
  have h1 : G.edge z = z → G.node z = z → G.face z = z := fun hez hnz => by
    have := G.edgeK z
    rw [hez] at this
    exact G.nodeI (this.trans hnz.symm)
  have h2 : G.edge z = z → G.face z = z → G.node z = z := fun hez hfz => by
    have := G.edgeK z
    rwa [hez, hfz] at this
  have h3 : G.node z = z → G.face z = z → G.edge z = z := fun hnz hfz => by
    have := G.faceK z
    rwa [hfz, hnz] at this
  -- The node and face permutations of `WalkupE z` are `skip node` and `skip face`.
  show 2 * G.nCompZ z (G.crossEdge z) + (fcard (G.WalkupE z).edge Set.univ
      + (fcard (skip z G.nodeI) Set.univ + fcard (skip z G.faceI) Set.univ))
      = fcard G.edge Set.univ + (fcard G.node Set.univ + fcard G.face Set.univ) + 1
  unfold nCompZ
  by_cases hg : G.glink z z
  · rw [ite_eq_left hg] at hE ⊢
    by_cases hzb : G.ZBarb z
    · obtain ⟨hez, hnz, hfz⟩ := hZ.1 hzb
      rw [ite_eq_left hzb]
      rw [ite_eq_left hez] at hE
      rw [ite_eq_left hnz] at hN
      rw [ite_eq_left hfz] at hF
      omega
    · -- Exactly one of `edge z = z`, `node z = z`, `face z = z` holds.
      rw [ite_eq_right hzb]
      have hnot : ¬ (G.edge z = z ∧ G.node z = z ∧ G.face z = z) := fun h => hzb (hZ.2 h)
      rcases hg with hez | hnz | hfz
      · rw [ite_eq_left hez] at hE
        rw [ite_eq_right fun (hnz : G.node z = z) => hnot ⟨hez, hnz, h1 hez hnz⟩] at hN
        rw [ite_eq_right fun (hfz : G.face z = z) => hnot ⟨hez, h2 hez hfz, hfz⟩] at hF
        omega
      · rw [ite_eq_right fun (hez : G.edge z = z) => hnot ⟨hez, hnz, h1 hez hnz⟩] at hE
        rw [ite_eq_left hnz] at hN
        rw [ite_eq_right fun (hfz : G.face z = z) => hnot ⟨h3 hnz hfz, hnz, hfz⟩] at hF
        omega
      · rw [ite_eq_right fun (hez : G.edge z = z) => hnot ⟨hez, h2 hez hfz, hfz⟩] at hE
        rw [ite_eq_right fun (hnz : G.node z = z) => hnot ⟨h3 hnz hfz, hnz, hfz⟩] at hN
        rw [ite_eq_left hfz] at hF
        omega
  · rw [ite_eq_right hg] at hE ⊢
    rw [ite_eq_right fun h => hg (Or.inr (Or.inl h))] at hN
    rw [ite_eq_right fun h => hg (Or.inr (Or.inr h))] at hF
    split_ifs at hE ⊢ <;> omega

end SkipEdge

end Hypermap

end FourColor
