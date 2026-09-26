/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfContract.Ext
import FourColor.Engine.Succ

/-!
# Ring traces along construction steps (port of `cfcolor.v`, correctness part)

`cfcolor.v` proves that its coloring iterator `cpcolor1 s` computes, from the ring traces of a
pointed map `G`, the ring traces of the map obtained from `G` by the construction step `s`
(`cpcolor1U_correct`, `cpcolor1K_correct`, `cpcolor1A_correct`, `cpcolor1R_correct`,
`cpcolor1R'_correct`, and through `cpexpand`/`injcp_expand` for `Y` and `H`).  Here the
iterator is replaced by its set-level form `Engine.cpsucc` (`Engine/Succ.lean`), and the
correctness is stated as one equivalence per step, for an arbitrary hypermap `G` with reference
dart `x0`:

`(ecpX x0).RingTrace (cpring (ecpX x0)) t ↔ ∃ t0, G.RingTrace (cpring x0) t0 ∧ t ∈ cpsucc X t0`.

* (→) restricts a coloring of the extended map along the injection (math-comp `gcol_cface`,
  `gcol_adj`: `Hypermap.coloring_restrict`);
* (←) extends a coloring of `G` (the `k'` constructions of the Coq proofs, factored in
  `CfContract/Ext.lean`).

The `Y` and `H` steps are handled directly (with the ring lemmas `cpring_ecpY`, `cpring_ecpH`)
rather than through `cpexpand`.  The ctree parts of `cfcolor.v` (`cpbranch`, `cpcolor0`,
`cpcolor`, `ctree_mem_cpcolor`) are not ported.

Main results: `Hypermap.ringTrace_ecpR`, `ringTrace_ecpR'`, `ringTrace_ecpU`, `ringTrace_ecpK`,
`ringTrace_ecpY`, `ringTrace_ecpH`, `ringTrace_ecpA`, and `ringTrace_cpmap0` for the base map.
-/

namespace FourColor

open Function EcpDart Engine

/-! ### Color-level facts (the case analyses of `cpcolor1` on the colors) -/

/-- The two colorings of the new face of a `Y` step. -/

private theorem colors_Y : ∀ a b c : Color, a ≠ b → c ≠ a → c ≠ b →
    (addc a c = permc Eperm231 (addc a b) ∧ addc c b = permc Eperm312 (addc a b)) ∨
    (addc a c = permc Eperm312 (addc a b) ∧ addc c b = permc Eperm231 (addc a b)) := by
  decide

/-- The two colorings of the new face of a `Y` step (existence). -/
private theorem colors_Y' : ∀ a b : Color, a ≠ b →
    (∃ c, c ≠ a ∧ c ≠ b ∧ addc a c = permc Eperm231 (addc a b) ∧
      addc c b = permc Eperm312 (addc a b)) ∧
    (∃ c, c ≠ a ∧ c ≠ b ∧ addc a c = permc Eperm312 (addc a b) ∧
      addc c b = permc Eperm231 (addc a b)) := by
  decide

/-- The colorings of the new face of an `H` step. -/
private theorem colors_H : ∀ a b c d : Color, a ≠ b → b ≠ d → c ≠ a → c ≠ b → c ≠ d →
    (addc a b = addc b d →
      (addc a c = permc Eperm231 (addc a b) ∧ addc c d = permc Eperm231 (addc a b)) ∨
      (addc a c = permc Eperm312 (addc a b) ∧ addc c d = permc Eperm312 (addc a b))) ∧
    (addc a b ≠ addc b d → addc a c = addc b d ∧ addc c d = addc a b) := by
  decide

/-- The colorings of the new face of an `H` step (existence). -/
private theorem colors_H' : ∀ a b d : Color, a ≠ b → b ≠ d →
    (addc a b = addc b d →
      (∃ c, c ≠ a ∧ c ≠ b ∧ c ≠ d ∧ addc a c = permc Eperm231 (addc a b) ∧
        addc c d = permc Eperm231 (addc a b)) ∧
      (∃ c, c ≠ a ∧ c ≠ b ∧ c ≠ d ∧ addc a c = permc Eperm312 (addc a b) ∧
        addc c d = permc Eperm312 (addc a b))) ∧
    (addc a b ≠ addc b d →
      ∃ c, c ≠ a ∧ c ≠ b ∧ c ≠ d ∧ addc a c = addc b d ∧ addc c d = addc a b) := by
  decide


namespace Hypermap

variable {D : Type*} [Fintype D] [DecidableEq D] (G : Hypermap D)

omit [DecidableEq D] in
/-- Restriction of a coloring along a map `i` that preserves faces and adjacency (math-comp
`gcol_cface`, `gcol_adj`, stated for one step rather than along `injcp`). -/
theorem coloring_restrict {D' : Type*} [Fintype D'] (M : Hypermap D') (i : D → D')
    {k : D' → Color} (hk : M.Coloring k) (hcf : ∀ x y, G.cface x y → M.cface (i x) (i y))
    (hadj : ∀ x y, G.adj x y → M.adj (i x) (i y)) : G.Coloring (k ∘ i) :=
  ⟨fun x => Ne.symm (CfContract.coloring_adj hk (hadj _ _ (G.adjE x))),
   fun x => (M.coloring_cface hk (hcf _ _ (fconnect1 G.face x))).symm⟩

variable (x0 : D)

/-- The ring after its first two darts `node x0`, `x0`, followed by `node x0`, starts with
`face (edge x0)`. -/
private theorem cpring_drop2_append (hp : G.ProperCpring x0) :
    ∃ w, (G.cpring x0).drop 2 ++ [G.node x0] = G.face (G.edge x0) :: w := by
  by_cases hl : G.LongCpring x0
  · rw [G.head_long_cpring x0 hl]
    exact ⟨_, rfl⟩
  · rcases G.cpring_small x0 hl with ⟨_, h⟩ | ⟨h, _⟩
    · rw [h]
      refine ⟨[], ?_⟩
      have : G.face (G.edge x0) = G.node x0 := not_not.1 hl
      simp [this]
    · exact absurd hp h

/-- The ring trace of a proper ring, in terms of the colors of `node x0`, `x0`,
`face (edge x0)` (a form of math-comp `trace_cpring_eq`). -/
private theorem ring_colors (hp : G.ProperCpring x0) (k : D → Color) :
    ∃ w, ((G.cpring x0).drop 2).map k ++ [k (G.node x0)] = k (G.face (G.edge x0)) :: w ∧
      trace ((G.cpring x0).map k) = addc (k (G.node x0)) (k x0) ::
        addc (k x0) (k (G.face (G.edge x0))) :: pairmap addc (k (G.face (G.edge x0))) w := by
  obtain ⟨w, hw⟩ := G.cpring_drop2_append x0 hp
  have hw' := congrArg (List.map k) hw
  simp only [List.map_append, List.map_cons, List.map_nil] at hw'
  refine ⟨_, hw', ?_⟩
  conv_lhs => rw [G.head_proper_cpring x0 hp]
  rw [List.map_cons, List.map_cons, trace_cons, List.cons_append, hw', pairmap_cons, pairmap_cons]


omit [DecidableEq D] in
/-- math-comp `coloring_proper_cpring`: the ring of a colorable map is proper. -/
theorem coloring_proper_cpring {k : D → Color} (hk : G.Coloring k) : G.ProperCpring x0 :=
  CfContract.coloring_proper hk x0

/-- math-comp `trace_cpring_eq`. -/
theorem trace_cpring_eq {k : D → Color} (hk : G.Coloring k) :
    trace ((G.cpring x0).map k) = addc (k (G.node x0)) (k x0) ::
      addc (k x0) (k (G.face (G.edge x0))) ::
        ptrace (((G.cpring x0).drop 2 ++ [G.node x0]).map k) := by
  obtain ⟨w, hw, ht⟩ := G.ring_colors x0 (G.coloring_proper_cpring x0 hk) k
  rw [ht, List.map_append, List.map_cons, List.map_nil, hw]
  rfl

/-! ### `U` -/

/-- The ring trace of `ecpU x0`. -/
private theorem trace_ecpU {k' : (G.ecpU x0).D → Color}
    (hF : ∀ u, k' ((G.ecpU x0).pointee.face u) = k' u) :
    trace (((G.ecpU x0).pointee.cpring (G.ecpU x0).pointer).map k') =
      addc (k' (G.icpU x0 (G.node x0))) (k' (G.ecpU x0).pointer) ::
      addc (k' (G.ecpU x0).pointer) (k' (G.icpU x0 (G.node x0))) ::
      trace ((G.cpring x0).map (k' ∘ G.icpU x0)) := by
  have e : k' ((G.ecpU x0).pointee.node (G.ecpU x0).pointer) = k' (G.icpU x0 (G.node x0)) :=
    (hF IcpXe).symm
  rw [G.cpring_ecpU x0, List.map_cons, List.map_cons, e, List.map_map, G.head_cpring x0]
  simp only [List.map_cons, trace_cons, List.cons_append, pairmap_cons, Function.comp_apply]

/-- The ring traces of `ecpU x0` (math-comp `cpcolor1U_correct`). -/
theorem ringTrace_ecpU (t : Colseq) :
    (G.ecpU x0).pointee.RingTrace ((G.ecpU x0).pointee.cpring (G.ecpU x0).pointer) t ↔
      ∃ t0, G.RingTrace (G.cpring x0) t0 ∧ t ∈ cpsucc .U t0 := by
  constructor
  · rintro ⟨k', hk', rfl⟩
    refine ⟨_, ⟨k' ∘ G.icpU x0, G.coloring_restrict _ _ hk'
      (fun x y h => (G.cface_icpU x0 x y).2 h) (fun x y h => (G.adj_icpU x0 x y).2 h), rfl⟩, ?_⟩
    rw [G.trace_ecpU x0 hk'.2]
    have hne : k' (G.ecpU x0).pointer ≠ k' (G.icpU x0 (G.node x0)) :=
      CfContract.coloring_adj hk'
        ((G.adj_ecpU x0 _).2 ⟨_, List.mem_singleton_self _, connect_refl _⟩)
    generalize k' (G.ecpU x0).pointer = c at hne
    generalize k' (G.icpU x0 (G.node x0)) = a at hne
    simp only [cpsucc, List.mem_cons, List.cons.injEq, List.not_mem_nil, and_true, or_false]
    revert a c
    decide
  · rintro ⟨t0, ⟨k, hk, rfl⟩, ht⟩
    have he : ∃ e, e ≠ Color0 ∧ t = e :: e :: trace ((G.cpring x0).map k) := by
      simp only [cpsucc, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl
      · exact ⟨Color1, by decide, rfl⟩
      · exact ⟨Color2, by decide, rfl⟩
      · exact ⟨Color3, by decide, rfl⟩
    obtain ⟨e, he, rfl⟩ := he
    obtain ⟨k', hk', hki, hkX⟩ := CfContract.coloring_ecpU G x0 hk (addc (k (G.node x0)) e)
      (fun h => he (by simpa using (congrArg (addc (k (G.node x0))) h).symm))
    refine ⟨k', hk', ?_⟩
    rw [G.trace_ecpU x0 hk'.2, hkX, hki, show k' ∘ G.icpU x0 = k from funext hki]
    simp [addcC (addc _ _)]


/-! ### `K` -/

/-- The ring trace of `ecpK x0`. -/
private theorem trace_ecpK {k' : (G.ecpK x0).D → Color}
    (hF : ∀ u, k' ((G.ecpK x0).pointee.face u) = k' u) :
    trace (((G.ecpK x0).pointee.cpring (G.ecpK x0).pointer).map k') =
      trace ((G.node x0 :: (G.cpring x0).drop 2).map (k' ∘ G.icpK x0)) := by
  rw [G.cpring_ecpK x0, List.map_cons, List.map_cons, List.map_map,
    CfContract.face_inv_cface hF (G.cface_node_ecpK x0)]
  rfl

/-- The ring traces of `ecpK x0` (math-comp `cpcolor1K_correct`). -/
theorem ringTrace_ecpK (t : Colseq) :
    (G.ecpK x0).pointee.RingTrace ((G.ecpK x0).pointee.cpring (G.ecpK x0).pointer) t ↔
      ∃ t0, G.RingTrace (G.cpring x0) t0 ∧ t ∈ cpsucc .K t0 := by
  -- the common computation
  have key : ∀ k : D → Color, G.Coloring k →
      (k (G.edge x0) ≠ k (G.node x0) → trace ((G.node x0 :: (G.cpring x0).drop 2).map k) ∈
        cpsucc .K (trace ((G.cpring x0).map k))) ∧
      ∀ t, t ∈ cpsucc .K (trace ((G.cpring x0).map k)) →
        k (G.edge x0) ≠ k (G.node x0) ∧ t = trace ((G.node x0 :: (G.cpring x0).drop 2).map k) := by
    intro k hk
    obtain ⟨w, hw, ht⟩ := G.ring_colors x0 (CfContract.coloring_proper hk x0) k
    have hd : k (G.face (G.edge x0)) = k (G.edge x0) := hk.2 _
    rw [ht, List.map_cons, trace_cons, hw, pairmap_cons, hd]
    generalize pairmap addc (k (G.edge x0)) w = P
    generalize k (G.edge x0) = d
    generalize k (G.node x0) = a
    generalize k x0 = b
    simp only [cpsucc]
    have c1 : ∀ a b d : Color, d ≠ a →
        addc a b ≠ addc b d ∧ addc (addc a b) (addc b d) = addc a d := by decide
    have c2 : ∀ a b d : Color, addc a b ≠ addc b d → d ≠ a := by decide
    refine ⟨fun h => ?_, fun t ht => ?_⟩
    · rw [ite_eq_right (c1 a b d h).1, (c1 a b d h).2]
      exact List.mem_singleton_self _
    · split_ifs at ht with h
      · simp at ht
      · rw [List.mem_singleton] at ht
        exact ⟨c2 _ _ _ h, ht.trans (by rw [(c1 _ _ _ (c2 _ _ _ h)).2])⟩
  constructor
  · rintro ⟨k', hk', rfl⟩
    have hk := G.coloring_restrict _ _ hk'
      (fun x y h => (G.cface_icpK x0 x y).2 h) (fun x y h => G.sub_adj_icpK x0 h)
    refine ⟨_, ⟨_, hk, rfl⟩, ?_⟩
    rw [G.trace_ecpK x0 hk'.2]
    refine (key _ hk).1 (CfContract.coloring_adj hk' ((G.adj_icpK x0 _ _).2 ?_))
    exact Or.inr (Or.inl ⟨connect_refl _, connect_refl _⟩)
  · rintro ⟨t0, ⟨k, hk, rfl⟩, ht⟩
    obtain ⟨hne, rfl⟩ := (key k hk).2 t ht
    obtain ⟨k', hk', hki⟩ := CfContract.coloring_ecpK G x0 hk hne
    refine ⟨k', hk', ?_⟩
    rw [G.trace_ecpK x0 hk'.2, show k' ∘ G.icpK x0 = k from funext hki]


omit [DecidableEq D] in
/-- In a coloring, `node x0` and `x0` have different colors. -/
private theorem coloring_node_ne {k : D → Color} (hk : G.Coloring k) : k x0 ≠ k (G.node x0) := by
  have := hk.1 (G.node x0)
  rwa [← hk.2, G.nodeK] at this

omit [Fintype D] [DecidableEq D] in
/-- In a coloring, `x0` and `face (edge x0)` have different colors. -/
private theorem coloring_fe_ne {k : D → Color} (hk : G.Coloring k) : k (G.face (G.edge x0)) ≠ k x0 := by
  rw [hk.2]
  exact hk.1 x0

/-! ### `Y` -/

/-- The ring trace of `ecpY x0`. -/
private theorem trace_ecpY {k' : (G.ecpY x0).D → Color}
    (hF : ∀ u, k' ((G.ecpY x0).pointee.face u) = k' u) :
    trace (((G.ecpY x0).pointee.cpring (G.ecpY x0).pointer).map k') =
      trace (k' (G.icpY x0 (G.node x0)) :: k' (G.ecpY x0).pointer ::
        ((G.cpring x0).tail).map (k' ∘ G.icpY x0)) := by
  rw [G.cpring_ecpY x0, List.map_cons, List.map_cons, List.map_map,
    CfContract.face_inv_cface hF (G.cface_node_ecpY x0)]

/-- The ring traces of `ecpY x0` (math-comp `cpcolor1_correct` for a `Y` step, through
`cpexpand` and `injcp_expand`). -/
theorem ringTrace_ecpY (t : Colseq) :
    (G.ecpY x0).pointee.RingTrace ((G.ecpY x0).pointee.cpring (G.ecpY x0).pointer) t ↔
      ∃ t0, G.RingTrace (G.cpring x0) t0 ∧ t ∈ cpsucc .Y t0 := by
  have key : ∀ k : D → Color, G.Coloring k →
      (∀ c, c ≠ k (G.node x0) → c ≠ k x0 → trace (k (G.node x0) :: c :: (G.cpring x0).tail.map k)
        ∈ cpsucc .Y (trace ((G.cpring x0).map k))) ∧
      ∀ t, t ∈ cpsucc .Y (trace ((G.cpring x0).map k)) →
        ∃ c, c ≠ k (G.node x0) ∧ c ≠ k x0 ∧
          t = trace (k (G.node x0) :: c :: (G.cpring x0).tail.map k) := by
    intro k hk
    have hp := CfContract.coloring_proper hk x0
    have hab := G.coloring_node_ne x0 hk
    obtain ⟨w, hw, ht⟩ := G.ring_colors x0 hp k
    have htail : (G.cpring x0).tail = x0 :: (G.cpring x0).drop 2 := by
      conv_lhs => rw [G.head_proper_cpring x0 hp]
      rfl
    rw [ht, htail, List.map_cons]
    simp only [trace_cons, List.cons_append, hw, pairmap_cons]
    generalize pairmap addc (k (G.face (G.edge x0))) w = P
    generalize k (G.face (G.edge x0)) = d
    generalize k (G.node x0) = a at hab ⊢
    generalize k x0 = b at hab ⊢
    simp only [cpsucc, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨fun c h1 h2 => ?_, fun t ht => ?_⟩
    · rcases colors_Y a b c (Ne.symm hab) h1 h2 with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · left; rw [e1, e2]
      · right; rw [e1, e2]
    · obtain ⟨⟨c1, h11, h12, e11, e12⟩, ⟨c2, h21, h22, e21, e22⟩⟩ := colors_Y' a b (Ne.symm hab)
      rcases ht with rfl | rfl
      · exact ⟨c1, h11, h12, by rw [e11, e12]⟩
      · exact ⟨c2, h21, h22, by rw [e21, e22]⟩
  constructor
  · rintro ⟨k', hk', rfl⟩
    have hk := G.coloring_restrict _ _ hk'
      (fun x y h => (G.cface_icpY x0 x y).2 h) (fun x y h => (G.adj_icpY x0 x y).2 h)
    have hp := CfContract.coloring_proper hk x0
    refine ⟨_, ⟨_, hk, rfl⟩, ?_⟩
    rw [G.trace_ecpY x0 hk'.2]
    refine (key _ hk).1 _ (CfContract.coloring_adj hk' ((G.adj_ecpY x0 hp _).2 ?_))
      (CfContract.coloring_adj hk' ((G.adj_ecpY x0 hp _).2 ?_))
    · exact ⟨_, by simp, connect_refl _⟩
    · exact ⟨_, by simp, connect_refl _⟩
  · rintro ⟨t0, ⟨k, hk, rfl⟩, ht⟩
    obtain ⟨c, h1, h2, rfl⟩ := (key k hk).2 t ht
    obtain ⟨k', hk', hki, hkX⟩ := CfContract.coloring_ecpY G x0 hk c (Ne.symm h1) (Ne.symm h2)
    refine ⟨k', hk', ?_⟩
    rw [G.trace_ecpY x0 hk'.2, show k' ∘ G.icpY x0 = k from funext hki, hki, hkX]

/-! ### `H` -/

/-- The ring trace of `ecpH x0`. -/
private theorem trace_ecpH (hp : G.ProperCpring x0) {k' : (G.ecpH x0).D → Color}
    (hF : ∀ u, k' ((G.ecpH x0).pointee.face u) = k' u) :
    trace (((G.ecpH x0).pointee.cpring (G.ecpH x0).pointer).map k') =
      trace (k' (G.icpH x0 (G.node x0)) :: k' (G.ecpH x0).pointer ::
        ((G.cpring x0).drop 2).map (k' ∘ G.icpH x0)) := by
  rw [G.cpring_ecpH x0 hp, List.map_cons, List.map_cons, List.map_map,
    CfContract.face_inv_cface hF (G.cface_node_ecpH x0 hp)]

/-- The ring traces of `ecpH x0` (math-comp `cpcolor1_correct` for an `H` step, through
`cpexpand` and `injcp_expand`). -/
theorem ringTrace_ecpH (t : Colseq) :
    (G.ecpH x0).pointee.RingTrace ((G.ecpH x0).pointee.cpring (G.ecpH x0).pointer) t ↔
      ∃ t0, G.RingTrace (G.cpring x0) t0 ∧ t ∈ cpsucc .H t0 := by
  have key : ∀ k : D → Color, G.Coloring k →
      (∀ c, c ≠ k (G.node x0) → c ≠ k x0 → c ≠ k (G.face (G.edge x0)) →
        trace (k (G.node x0) :: c :: ((G.cpring x0).drop 2).map k)
          ∈ cpsucc .H (trace ((G.cpring x0).map k))) ∧
      ∀ t, t ∈ cpsucc .H (trace ((G.cpring x0).map k)) →
        ∃ c, c ≠ k (G.node x0) ∧ c ≠ k x0 ∧ c ≠ k (G.face (G.edge x0)) ∧
          t = trace (k (G.node x0) :: c :: ((G.cpring x0).drop 2).map k) := by
    intro k hk
    have hp := CfContract.coloring_proper hk x0
    have hab := G.coloring_node_ne x0 hk
    have hbd := G.coloring_fe_ne x0 hk
    obtain ⟨w, hw, ht⟩ := G.ring_colors x0 hp k
    rw [ht]
    simp only [trace_cons, List.cons_append, hw, pairmap_cons]
    generalize pairmap addc (k (G.face (G.edge x0))) w = P
    generalize k (G.face (G.edge x0)) = d at hbd ⊢
    generalize k (G.node x0) = a at hab ⊢
    generalize k x0 = b at hab hbd ⊢
    have hab' := Ne.symm hab
    have hbd' := Ne.symm hbd
    simp only [cpsucc]
    refine ⟨fun c h1 h2 h3 => ?_, fun t ht => ?_⟩
    · obtain ⟨H1, H2⟩ := colors_H a b c d hab' hbd' h1 h2 h3
      split_ifs with h
      · rcases H1 h with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2]; simp
        · rw [e1, e2]; simp
      · obtain ⟨e1, e2⟩ := H2 h
        rw [e1, e2]; simp
    · obtain ⟨H1, H2⟩ := colors_H' a b d hab' hbd'
      split_ifs at ht with h
      · obtain ⟨⟨c1, h11, h12, h13, e11, e12⟩, ⟨c2, h21, h22, h23, e21, e22⟩⟩ := H1 h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · exact ⟨c1, h11, h12, h13, by rw [e11, e12]⟩
        · exact ⟨c2, h21, h22, h23, by rw [e21, e22]⟩
      · obtain ⟨c, h1, h2, h3, e1, e2⟩ := H2 h
        rw [List.mem_singleton] at ht
        exact ⟨c, h1, h2, h3, by rw [ht, e1, e2]⟩
  constructor
  · rintro ⟨k', hk', rfl⟩
    have hk := G.coloring_restrict _ _ hk'
      (fun x y h => (G.cface_icpH x0 x y).2 h) (fun x y h => (G.adj_icpH x0 x y).2 h)
    have hp := CfContract.coloring_proper hk x0
    refine ⟨_, ⟨_, hk, rfl⟩, ?_⟩
    rw [G.trace_ecpH x0 hp hk'.2]
    refine (key _ hk).1 _ (CfContract.coloring_adj hk' ((G.adj_ecpH x0 hp _).2 ?_))
      (CfContract.coloring_adj hk' ((G.adj_ecpH x0 hp _).2 ?_))
      (CfContract.coloring_adj hk' ((G.adj_ecpH x0 hp _).2 ?_))
    · exact ⟨_, by simp, connect_refl _⟩
    · exact ⟨_, by simp, connect_refl _⟩
    · exact ⟨_, by simp, connect_refl _⟩
  · rintro ⟨t0, ⟨k, hk, rfl⟩, ht⟩
    have hp := CfContract.coloring_proper hk x0
    obtain ⟨c, h1, h2, h3, rfl⟩ := (key k hk).2 t ht
    obtain ⟨k', hk', hki, hkX⟩ :=
      CfContract.coloring_ecpH G x0 hk c (Ne.symm h1) (Ne.symm h2) (Ne.symm h3)
    refine ⟨k', hk', ?_⟩
    rw [G.trace_ecpH x0 hp hk'.2, show k' ∘ G.icpH x0 = k from funext hki, hki, hkX]


/-! ### `A` -/

/-- An `A` step has at most one successor trace. -/
private theorem cpsucc_A_subsingleton {t0 t t' : Colseq} (h : t ∈ cpsucc .A t0)
    (h' : t' ∈ cpsucc .A t0) : t = t' := by
  rcases t0 with _ | ⟨e1, _ | ⟨e2, et'⟩⟩ <;> simp only [cpsucc] at h h'
  · simp at h
  · simp at h
  · split_ifs at h h' <;> simp_all

/-- The ring traces of `ecpA x0` (math-comp `cpcolor1A_correct`). -/
theorem ringTrace_ecpA (t : Colseq) :
    (G.ecpA x0).pointee.RingTrace ((G.ecpA x0).pointee.cpring (G.ecpA x0).pointer) t ↔
      ∃ t0, G.RingTrace (G.cpring x0) t0 ∧ t ∈ cpsucc .A t0 := by
  have key : ∀ k : D → Color, G.Coloring k → k (G.node x0) = k (G.face (G.edge x0)) →
      trace (((G.ecpA x0).pointee.cpring (G.ecpA x0).pointer).map k) ∈
        cpsucc .A (trace ((G.cpring x0).map k)) := by
    intro k hk hc
    have hp := CfContract.coloring_proper hk x0
    obtain ⟨w, hw, ht⟩ := G.ring_colors x0 hp k
    rw [G.cpring_ecpA x0]
    split_ifs with hl
    · have htt : (G.cpring x0).tail.tail = (G.cpring x0).drop 2 := by
        rcases G.cpring x0 with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> rfl
      have hlen := (G.size_long_cpring x0).1 hl
      rw [htt, ht]
      cases hR : ((G.cpring x0).drop 2).map k with
      | nil =>
        exfalso
        have := congrArg List.length hR
        simp at this
        omega
      | cons d' R' =>
        rw [hR] at hw
        simp only [List.cons_append, List.cons.injEq] at hw
        obtain ⟨rfl, rfl⟩ := hw
        rw [trace_cons, hc]
        generalize k (G.face (G.edge x0)) = d
        generalize k x0 = b
        simp only [cpsucc]
        rw [ite_eq_left (addcC d b)]
        rcases R' with _ | ⟨x, R''⟩ <;> simp
    · have hd2 : (G.cpring x0).drop 2 = [] := by
        rcases G.cpring_small x0 hl with ⟨_, h⟩ | ⟨h, _⟩
        · rw [h]; rfl
        · exact absurd hp h
      rw [hd2] at hw
      simp only [List.map_nil, List.nil_append, List.cons.injEq] at hw
      obtain ⟨hw1, rfl⟩ := hw
      rw [ht]
      simp [cpsucc, hw1]
      exact addcC _ _
  have hcond : ∀ k : D → Color, G.Coloring k → ∀ t, t ∈ cpsucc .A (trace ((G.cpring x0).map k)) →
      k (G.node x0) = k (G.face (G.edge x0)) := by
    intro k hk t ht
    obtain ⟨w, -, ht0⟩ := G.ring_colors x0 (CfContract.coloring_proper hk x0) k
    rw [ht0] at ht
    simp only [cpsucc] at ht
    split_ifs at ht with h
    · have c : ∀ a b d : Color, addc a b = addc b d → a = d := by decide
      exact c _ _ _ h
    · simp at ht
  constructor
  · rintro ⟨k', hk', rfl⟩
    have hk := G.coloring_restrict _ (G.icpA x0) hk'
      (fun x y h => G.sub_cface_icpA x0 h) (fun x y h => G.sub_adj_icpA x0 h)
    refine ⟨_, ⟨_, hk, rfl⟩, key _ hk ?_⟩
    refine (G.ecpA x0).pointee.coloring_cface hk' ((G.cface_icpA x0 _ _).2 (Or.inr ⟨?_, ?_⟩))
    · exact ⟨G.node x0, by simp, connect_refl _⟩
    · exact ⟨G.face (G.edge x0), by simp, connect_refl _⟩
  · rintro ⟨t0, ⟨k, hk, rfl⟩, ht⟩
    have hc := hcond k hk t ht
    exact ⟨k, CfContract.coloring_ecpA G x0 hk hc, cpsucc_A_subsingleton ht (key k hk hc)⟩

/-! ### `R` and `R'` -/

/-- The ring traces of `ecpR n x0` (math-comp `cpcolor1R_correct`). -/
theorem ringTrace_ecpR (n : ℕ) (t : Colseq) :
    (G.ecpR n x0).pointee.RingTrace ((G.ecpR n x0).pointee.cpring (G.ecpR n x0).pointer) t ↔
      ∃ t0, G.RingTrace (G.cpring x0) t0 ∧ t ∈ cpsucc (.R n) t0 := by
  rw [G.cpring_ecpR n x0]
  simp only [cpsucc, List.mem_singleton]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨k, hk, rfl⟩, by rw [CfMap.map_rot]; exact trace_rot n _⟩
  · rintro ⟨t0, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, by rw [CfMap.map_rot]; exact (trace_rot n _).symm⟩

/-- The ring traces of `ecpR' x0` (math-comp `cpcolor1R'_correct`). -/
theorem ringTrace_ecpR' (t : Colseq) :
    (G.ecpR' x0).pointee.RingTrace ((G.ecpR' x0).pointee.cpring (G.ecpR' x0).pointer) t ↔
      ∃ t0, G.RingTrace (G.cpring x0) t0 ∧ t ∈ cpsucc .R' t0 := by
  show (G.ecpR (order G.node x0 - 1) x0).pointee.RingTrace
    ((G.ecpR (order G.node x0 - 1) x0).pointee.cpring (G.ecpR (order G.node x0 - 1) x0).pointer) t
    ↔ _
  rw [G.cpring_ecpR _ x0]
  have hlen : ∀ k : D → Color, (trace ((G.cpring x0).map k)).length = order G.node x0 := by
    intro k
    rw [size_trace, List.length_map, size_cpring]
  have h2 : ∀ k : D → Color, G.Coloring k → 1 < order G.node x0 := by
    intro k hk
    rw [← G.size_cpring x0]
    exact (G.size_proper_cpring x0).1 (CfContract.coloring_proper hk x0)
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨_, ⟨k, hk, rfl⟩, ?_⟩
    simp only [cpsucc]
    rw [ite_eq_right (by rw [hlen]; have := h2 k hk; omega), List.mem_singleton, CfMap.map_rot,
      rotr, hlen]
    exact trace_rot _ _
  · rintro ⟨t0, ⟨k, hk, rfl⟩, ht⟩
    simp only [cpsucc] at ht
    rw [ite_eq_right (by rw [hlen]; have := h2 k hk; omega), List.mem_singleton, rotr, hlen] at ht
    refine ⟨k, hk, ?_⟩
    rw [ht, CfMap.map_rot]
    exact (trace_rot _ _).symm

end Hypermap

/-! ### The base map -/

/-- The ring traces of the base map `cpmap0` (a single edge), pointed at `true` (the base case
of math-comp `cpcolor0_correct`). -/
theorem ringTrace_cpmap0 (t : Colseq) :
    cpmap0.RingTrace (cpmap0.cpring true) t ↔ t ∈ baseTraces := by
  rw [cpring0]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have h : k false ≠ k true := hk.1 true
    show trace [k false, k true] ∈ baseTraces
    generalize k false = p at h ⊢
    generalize k true = q at h ⊢
    revert p q
    decide
  · intro h
    have hcol : ∀ e, e ≠ Color0 → cpmap0.Coloring (fun b => if b then e else Color0) := by
      intro e he
      refine ⟨fun b => ?_, fun b => rfl⟩
      cases b
      · exact he
      · exact Ne.symm he
    simp only [baseTraces, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨_, hcol Color1 (by decide), by decide⟩
    · exact ⟨_, hcol Color2 (by decide), by decide⟩
    · exact ⟨_, hcol Color3 (by decide), by decide⟩

end FourColor
