/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfContract.Enum

/-!
# Configuration contracts: extending colorings along construction steps

The proof of math-comp `cfctr_correct` extends a coloring `h'` of a map `Gc` to the map
obtained from `Gc` by one construction step (`U`, `Y`, `H`, `K` or `A`), with a prescribed
color `c0` for the new face (math-comp's `k' u := oapp h' c0 [pick x | cface u (icp x)]`).
This file factors out these constructions:

* `CfContract.exists_face_ext` : the face-invariant extension `k'` of `h'` along an injection;
* `CfContract.coloring_ext`, `CfContract.coloring_ext0` : when this extension is a coloring;
* `CfContract.coloring_ecpU`, `coloring_ecpY`, `coloring_ecpH`, `coloring_ecpK`,
  `coloring_ecpA` : the instances for the construction steps.
-/

namespace FourColor

open Function CfMap EcpDart Hypermap

namespace CfContract

variable {D D' : Type*} [Fintype D] [DecidableEq D]

omit [Fintype D] [DecidableEq D] in
/-- A face-invariant function is constant on faces (math-comp `fconnect_invariant`). -/
theorem face_inv_cface {G : Hypermap D} {k : D → Color} (hk : ∀ x, k (G.face x) = k x)
    {x y : D} (h : G.cface x y) : k x = k y := by
  induction h with
  | refl => rfl
  | tail _ hbc ih =>
    rw [ih, ← hbc, hk]

omit [DecidableEq D] in
/-- The ends of an adjacency have different colors. -/
theorem coloring_adj {G : Hypermap D} {k : D → Color} (hk : G.Coloring k) {x y : D}
    (h : G.adj x y) : k x ≠ k y := by
  obtain ⟨z, hxz, hzy⟩ := G.adjP.1 h
  intro e
  apply hk.1 z
  rw [face_inv_cface hk.2 hzy, ← e, face_inv_cface hk.2 hxz]

omit [DecidableEq D] in
/-- math-comp `coloring_proper_cpring` (in a stronger form): in a colorable map, every ring is
proper. -/
theorem coloring_proper {G : Hypermap D} {k : D → Color} (hk : G.Coloring k) (x : D) :
    G.ProperCpring x := by
  intro hx
  have h1 : G.face (G.edge x) = x := by
    calc G.face (G.edge x) = G.face (G.edge (G.node x)) := by rw [← hx]
      _ = x := G.nodeK x
  apply hk.1 x
  rw [← hk.2 (G.edge x), h1]

omit [DecidableEq D] in
/-- The face-invariant extension of `h'` along `i`, with default color `c0` (math-comp
`k' u := oapp h' c0 [pick x | cface u (icp x)]`). -/
theorem exists_face_ext [Fintype D'] [DecidableEq D'] (M : Hypermap D') (i : D → D')
    (h' : D → Color) (c0 : Color) (hF : ∀ x y, M.cface (i x) (i y) → h' x = h' y) :
    ∃ k' : D' → Color, (∀ u, k' (M.face u) = k' u) ∧ (∀ x, k' (i x) = h' x) ∧
      (∀ u, (∀ x, ¬ M.cface u (i x)) → k' u = c0) ∧
        (∀ u x, M.cface u (i x) → k' u = h' x) := by
  classical
  let k' : D' → Color := fun u => if hu : ∃ x, M.cface u (i x) then h' hu.choose else c0
  have hpos : ∀ u x, M.cface u (i x) → k' u = h' x := by
    intro u x hux
    have hu : ∃ x, M.cface u (i x) := ⟨x, hux⟩
    simp only [k', dite_eq_left hu]
    exact hF _ _ (connect_trans (M.cfaceC.1 hu.choose_spec) hux)
  refine ⟨k', fun u => ?_, fun x => hpos _ _ (connect_refl _), fun u hu => ?_, hpos⟩
  · by_cases hu : ∃ x, M.cface u (i x)
    · obtain ⟨x, hx⟩ := hu
      rw [hpos u x hx, hpos (M.face u) x ((M.cface1 u (i x)).1 hx)]
    · have hfu : ¬ ∃ x, M.cface (M.face u) (i x) := fun ⟨x, hx⟩ =>
        hu ⟨x, (M.cface1 u (i x)).2 hx⟩
      simp only [k', dite_eq_right hu, dite_eq_right hfu]
  · have : ¬ ∃ x, M.cface u (i x) := fun ⟨x, hx⟩ => hu x hx
    simp only [k', dite_eq_right this]

omit [DecidableEq D] in
/-- Extension of a coloring along a construction step that adds a new face (the face of `X`). -/
theorem coloring_ext [Fintype D'] [DecidableEq D'] (G : Hypermap D)
    (M : Hypermap D') (i : D → D') (X : D') (L : List D) {h' : D → Color} (hh' : G.Coloring h')
    (c0 : Color) (hcf : ∀ x y, M.cface (i x) (i y) → G.cface x y)
    (hadj : ∀ x y, M.adj (i x) (i y) → h' x ≠ h' y)
    (hband : ∀ u, (∃ x, M.cface u (i x)) ∨ M.cface X u)
    (hXi : ∀ x, ¬ M.cface X (i x))
    (hadjX : ∀ u, M.adj X u → ∃ a ∈ L, M.cface u (i a))
    (hee : ∀ u, M.cface X (M.edge u) → M.edge (M.edge u) = u)
    (hc0 : ∀ a ∈ L, h' a ≠ c0) :
    ∃ k', M.Coloring k' ∧ (∀ x, k' (i x) = h' x) ∧ k' X = c0 := by
  obtain ⟨k', kF, ki, k0, kpos⟩ :=
    exists_face_ext M i h' c0 (fun x y h => face_inv_cface hh'.2 (hcf x y h))
  have kX : ∀ u, M.cface X u → k' u = c0 := fun u hu =>
    k0 u (fun x hx => hXi x (connect_trans hu hx))
  have hXcase : ∀ u, M.cface X u → k' (M.edge u) ≠ k' u := by
    intro u hu
    rw [kX u hu]
    have hadj' : M.adj X (M.edge u) := (M.adjF (M.cfaceC.1 hu) _).1 (M.adjE u)
    obtain ⟨a, ha, hea⟩ := hadjX _ hadj'
    rw [kpos _ a hea]
    exact hc0 a ha
  refine ⟨k', ⟨fun u => ?_, kF⟩, ki, kX X (connect_refl _)⟩
  rcases hband u with ⟨x, hx⟩ | hu
  · rcases hband (M.edge u) with ⟨y, hy⟩ | heu
    · rw [kpos u x hx, kpos _ y hy]
      have : M.adj (i x) (i y) := (M.adjFr hy _).1 ((M.adjF hx _).1 (M.adjE u))
      exact (hadj x y this).symm
    · have := hXcase _ heu
      rw [hee u heu] at this
      exact fun e => this e.symm
  · exact hXcase u hu

omit [DecidableEq D] in
/-- Extension of a coloring along a construction step that adds no new face. -/
theorem coloring_ext0 [Fintype D'] [DecidableEq D'] (G : Hypermap D)
    (M : Hypermap D') (i : D → D') {h' : D → Color} (hh' : G.Coloring h')
    (hcf : ∀ x y, M.cface (i x) (i y) → G.cface x y)
    (hadj : ∀ x y, M.adj (i x) (i y) → h' x ≠ h' y)
    (hband : ∀ u, ∃ x, M.cface u (i x)) :
    ∃ k', M.Coloring k' ∧ ∀ x, k' (i x) = h' x := by
  obtain ⟨k', kF, ki, -, kpos⟩ :=
    exists_face_ext M i h' Color0 (fun x y h => face_inv_cface hh'.2 (hcf x y h))
  refine ⟨k', ⟨fun u => ?_, kF⟩, ki⟩
  obtain ⟨x, hx⟩ := hband u
  obtain ⟨y, hy⟩ := hband (M.edge u)
  rw [kpos u x hx, kpos _ y hy]
  have : M.adj (i x) (i y) := (M.adjFr hy _).1 ((M.adjF hx _).1 (M.adjE u))
  exact (hadj x y this).symm

variable (G : Hypermap D) (x0 : D)

/-- Extension of a coloring to `ecpU x0` (math-comp `cfctr_correct`, `k'` for a `U` step). -/
theorem coloring_ecpU {h' : D → Color} (hh' : G.Coloring h') (c0 : Color)
    (hc : h' (G.node x0) ≠ c0) :
    ∃ k', (G.ecpU x0).pointee.Coloring k' ∧ (∀ x, k' (G.icpU x0 x) = h' x) ∧
      k' (G.ecpU x0).pointer = c0 := by
  refine coloring_ext G (G.ecpU x0).pointee (G.icpU x0) (G.ecpU x0).pointer [G.node x0] hh' c0
    (fun x y h => (G.cface_icpU x0 x y).1 h)
    (fun x y h => coloring_adj hh' ((G.adj_icpU x0 x y).1 h)) (G.fband_icpU x0)
    (fun x h => ?_) (fun u h => ?_) (fun u h => ?_) (by simpa using hc)
  · have := (G.cface_ecpU x0 _).1 h
    simp at this
  · obtain ⟨y, hy, hu⟩ := (G.adj_ecpU x0 u).1 h
    rw [List.mem_singleton] at hy
    exact ⟨G.node x0, List.mem_singleton_self _, hy ▸ hu⟩
  · have h1 := (G.cface_ecpU x0 _).1 h
    match u, h1 with
    | IcpXe, _ => rfl

/-- Extension of a coloring to `ecpY x0` (math-comp `cfctr_correct`, `k'` for a `Y` step). -/
theorem coloring_ecpY {h' : D → Color} (hh' : G.Coloring h') (c0 : Color)
    (hc1 : h' (G.node x0) ≠ c0) (hc2 : h' x0 ≠ c0) :
    ∃ k', (G.ecpY x0).pointee.Coloring k' ∧ (∀ x, k' (G.icpY x0 x) = h' x) ∧
      k' (G.ecpY x0).pointer = c0 := by
  have hp := coloring_proper hh' x0
  refine coloring_ext G (G.ecpY x0).pointee (G.icpY x0) (G.ecpY x0).pointer [G.node x0, x0] hh'
    c0 (fun x y h => (G.cface_icpY x0 x y).1 h)
    (fun x y h => coloring_adj hh' ((G.adj_icpY x0 x y).1 h)) (G.fband_icpY x0)
    (fun x h => ?_) (fun u h => ?_) (fun u h => ?_) (by simp [hc1, hc2])
  · have := (G.cface_ecpY x0 _).1 h
    rw [face_ecpY] at this
    simp [icpY_eq] at this
  · obtain ⟨y, hy, hu⟩ := (G.adj_ecpY x0 hp u).1 h
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨G.node x0, by simp, hu⟩
    · exact ⟨x0, by simp, hu⟩
  · have h1 := (G.cface_ecpY x0 _).1 h
    rw [face_ecpY] at h1
    match u, h1 with
    | IcpXe, _ => rfl
    | Icp IcpXe, _ => rfl

/-- Extension of a coloring to `ecpH x0` (math-comp `cfctr_correct`, `k'` for an `H` step). -/
theorem coloring_ecpH {h' : D → Color} (hh' : G.Coloring h') (c0 : Color)
    (hc1 : h' (G.node x0) ≠ c0) (hc2 : h' x0 ≠ c0) (hc3 : h' (G.face (G.edge x0)) ≠ c0) :
    ∃ k', (G.ecpH x0).pointee.Coloring k' ∧ (∀ x, k' (G.icpH x0 x) = h' x) ∧
      k' (G.ecpH x0).pointer = c0 := by
  have hp := coloring_proper hh' x0
  refine coloring_ext G (G.ecpH x0).pointee (G.icpH x0) (G.ecpH x0).pointer
    [G.node x0, x0, G.face (G.edge x0)] hh' c0 (fun x y h => (G.cface_icpH x0 x y).1 h)
    (fun x y h => coloring_adj hh' ((G.adj_icpH x0 x y).1 h)) (G.fband_icpH x0)
    (fun x h => ?_) (fun u h => ?_) (fun u h => ?_) (by simp [hc1, hc2, hc3])
  · have := (G.cface_ecpH x0 hp _).1 h
    rw [G.face_face_ecpH x0 hp, face_ecpH] at this
    simp [icpH_eq] at this
  · obtain ⟨y, hy, hu⟩ := (G.adj_ecpH x0 hp u).1 h
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨G.node x0, by simp, hu⟩
    · exact ⟨x0, by simp, hu⟩
    · exact ⟨G.face (G.edge x0), by simp, hu⟩
  · have h1 := (G.cface_ecpH x0 hp _).1 h
    rw [G.face_face_ecpH x0 hp, face_ecpH] at h1
    match u, h1 with
    | IcpXe, _ => rfl
    | Icp IcpXe, _ => rfl
    | Icp (Icp IcpXe), _ => rfl

/-- Extension of a coloring to `ecpK x0` (math-comp `cfctr_correct`, `k'` for a `K` step). -/
theorem coloring_ecpK {h' : D → Color} (hh' : G.Coloring h')
    (hc : h' (G.edge x0) ≠ h' (G.node x0)) :
    ∃ k', (G.ecpK x0).pointee.Coloring k' ∧ ∀ x, k' (G.icpK x0 x) = h' x := by
  refine coloring_ext0 G (G.ecpK x0).pointee (G.icpK x0) hh'
    (fun x y h => (G.cface_icpK x0 x y).1 h) (fun x y h => ?_) (G.fband_icpK x0)
  rcases (G.adj_icpK x0 x y).1 h with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact coloring_adj hh' h
  · rw [← face_inv_cface hh'.2 h1, ← face_inv_cface hh'.2 h2]
    exact hc
  · rw [← face_inv_cface hh'.2 h1, ← face_inv_cface hh'.2 h2]
    exact fun e => hc e.symm

/-- A coloring of `G` that agrees on the faces of `node x0` and `face (edge x0)` is a coloring of
`ecpA x0` (math-comp `cfctr_correct`, case `A`). -/
theorem coloring_ecpA {h' : D → Color} (hh' : G.Coloring h')
    (hc : h' (G.node x0) = h' (G.face (G.edge x0))) : (G.ecpA x0).pointee.Coloring h' := by
  classical
  have hfe : h' (G.edge x0) = h' (G.node x0) := by rw [hc, hh'.2]
  have e1 : h' (G.edge (G.node (G.node x0))) = h' (G.node x0) := by
    rw [← hh'.2 (G.edge (G.node (G.node x0))), G.nodeK]
  refine ⟨fun x => ?_, fun x => ?_⟩
  · show h' (G.ecpAEdge x0 x) ≠ h' x
    by_cases h1 : G.cface (G.edge x0) (G.node x0)
    · by_cases h2 : x = x0
      · rw [h2, ecpAEdge, ite_eq_right (not_not.2 h1), ite_eq_left rfl, e1, ← hfe]
        exact hh'.1 x0
      · by_cases h3 : x = G.node (G.node x0)
        · rw [h3, ecpAEdge, ite_eq_right (not_not.2 h1), ite_eq_right (h3 ▸ h2), ite_eq_left rfl,
            hfe, ← e1]
          exact hh'.1 _
        · rw [ecpAEdge, ite_eq_right (not_not.2 h1), ite_eq_right h2, ite_eq_right h3]
          exact hh'.1 x
    · rw [ecpAEdge, ite_eq_left h1]
      exact hh'.1 x
  · show h' (G.ecpAFace x0 x) = h' x
    by_cases h1 : G.cface (G.edge x0) (G.node x0)
    · rw [ecpAFace, ite_eq_left h1]
      exact hh'.2 x
    · by_cases h2 : x = G.edge x0
      · rw [h2, ecpAFace, ite_eq_right h1, ite_eq_left rfl]
        exact hfe.symm
      · by_cases h3 : G.face x = G.node x0
        · rw [ecpAFace, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, ← hc, ← h3, hh'.2]
        · rw [ecpAFace, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
          exact hh'.2 x

end CfContract

end FourColor
