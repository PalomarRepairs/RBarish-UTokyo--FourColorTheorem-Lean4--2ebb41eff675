/-
Copyright (c) 2026. Lean 4 port of the planarity part of the Coq/Rocq formal proof
of the Four Color Theorem by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Walkup.Genus

/-!
# Planar hypermaps have the Jordan property  (port of `jordan.v`, `planar_Jordan`)

To prove the Jordan path planarity property we consider a minimal counter example `G`,
planar (in the Euler formula sense) but containing a Moebius path `p` from `x` to `node t`
for some darts `x` and `t`. Then `p` (hence `G`) must contain at least three darts, and the
Euler formula rules out `#|G| = 3`. We use Walkup transforms to construct smaller maps with
Moebius paths. In detail, we suppress
 1) a dart not in `p`, with an E-transform
 2) `x` with an E-transform if `x` is followed by an N-link (i.e., `x = node y`)
 3) `y = face x` with an F-transform, if `y` is followed by an N-link.
 4) `y` with an E-transform, if `y != t` (by 3), `z = face y`)
 5) `y` with an N-transform, if `y != node x`
 6) `z` with an E-transform, if `z` is followed by an F-link in `p`
 7) `z` with an F-transform, otherwise (`z` is followed by an N-link in `p`)

## Implementation notes

The minimal counter example is replaced by a strong induction on the number of darts, over all
finite dart types; the case analysis itself is the private lemma `jordan_step`, which assumes
the Jordan property for all the Walkup transforms of `G`. The local lemmas `liftE`, `liftN`,
`liftF` of the Coq proof, which lift a C-path of `G` to a C-path of a Walkup map, share the
generic induction `lift_path`. A Moebius path of a Walkup map is always built with
`moebius_of_val`, which reduces its three conditions to statements about the underlying darts
of `G`.
-/

namespace FourColor

open Function

universe u

namespace Hypermap

variable {D : Type u}

section Lift

variable {z : D}

/-- A path of `e` avoiding `z`, whose targets avoid `b`, lifts to an `e'`-path of darts of
`WDart z` provided single links lift. This is the common part of the local lemmas `liftE`,
`liftN`, `liftF` of math-comp `planar_Jordan`. -/
private theorem lift_path {e : D → D → Prop} {e' : WDart z → WDart z → Prop}
    {b : D → Prop} (h : ∀ u v : WDart z, ¬ b v.1 → e u.1 v.1 → e' u v) :
    ∀ (p : List D) (x : D) (hx : x ≠ z), (∀ y ∈ p, y ≠ z ∧ ¬ b y) → path e x p →
      ∃ q : List (WDart z), q.map Subtype.val = p ∧ path e' ⟨x, hx⟩ q := by
  intro p
  induction p with
  | nil => intro x hx _ _; exact ⟨[], rfl, trivial⟩
  | cons y p ih =>
    intro x hx hp hxp
    have hy := hp y List.mem_cons_self
    obtain ⟨q, hq, hpq⟩ := ih y hy.1 (fun w hw => hp w (List.mem_cons_of_mem _ hw)) hxp.2
    exact ⟨⟨y, hy.1⟩ :: q, by simp [hq], h ⟨x, hx⟩ ⟨y, hy.1⟩ hy.2 hxp.1, hpq⟩

variable [Fintype D] [DecidableEq D] (G : Hypermap D)

/-- C-links of `G` between darts other than `z` are C-links of `WalkupE z` (the link step of
the local lemma `liftE` of math-comp `planar_Jordan`). -/
private theorem clink_liftE (u v : WDart z) (h : G.clink u.1 v.1) :
    (G.WalkupE z).clink u v := by
  rw [clink_WalkupE_iff]
  rcases h with h | h
  · left
    rw [skip1_of_ne z (h ▸ u.2 : G.node v.1 ≠ z)]
    exact h
  · right
    rw [skip1_of_ne z (h ▸ v.2 : G.face u.1 ≠ z)]
    exact h

/-- C-links of `G` between darts other than `z`, not ending at `face z`, are C-links of
`WalkupN z` (the link step of the local lemma `liftN` of math-comp `planar_Jordan`). -/
private theorem clink_liftN (u v : WDart z) (hv : v.1 ≠ G.face z) (h : G.clink u.1 v.1) :
    (G.WalkupN z).clink u v := by
  simp only [clink, Subtype.ext_iff, WalkupN_node_val, WalkupN_face_val]
  rcases h with h | h
  · left
    have hn : G.node v.1 ≠ z := h ▸ u.2
    by_cases hnz : G.permN.edge z = z
    · rw [G.permN.skipEdge1_of_edge_fixed z hnz]; exact h
    · have h1 : G.permN.face (G.permN.edge v.1) ≠ z := by
        intro h1
        apply hv
        have : G.face (G.edge (G.node v.1)) = G.face z := congrArg G.face h1
        rw [G.nodeK] at this
        exact this
      rw [G.permN.skipEdge1_of_ne z hnz h1 hn]; exact h
  · right
    rw [skip1_of_ne z (h ▸ v.2 : G.face u.1 ≠ z)]
    exact h

/-- C-links of `G` between darts other than `z`, not ending at `face (edge z)`, are C-links
of `WalkupF z` (the link step of the local lemma `liftF` of math-comp `planar_Jordan`). -/
private theorem clink_liftF (u v : WDart z) (hv : v.1 ≠ G.face (G.edge z))
    (h : G.clink u.1 v.1) : (G.WalkupF z).clink u v := by
  simp only [clink, Subtype.ext_iff, WalkupF_node_val, WalkupF_face_val]
  rcases h with h | h
  · left
    rw [skip1_of_ne z (h ▸ u.2 : G.node v.1 ≠ z)]
    exact h
  · right
    by_cases hfz : G.permF.edge z = z
    · rw [G.permF.skipEdge1_of_edge_fixed z hfz]; exact h
    · have h1 : G.permF.face (G.permF.edge u.1) ≠ z := by
        simp only [permF_edge, permF_face]
        intro h1
        rw [h] at h1
        exact hv ((G.eq_node_iff).1 h1.symm).symm
      have h2 : G.permF.edge u.1 ≠ z := by simp only [permF_edge]; rw [h]; exact v.2
      rw [G.permF.skipEdge1_of_ne z hfz h1 h2]; exact h

/-- The local lemma `liftE` of math-comp `planar_Jordan`: a C-path of `G` avoiding `z` lifts
to a C-path of `WalkupE z`. -/
private theorem liftE {x : D} (hx : x ≠ z) {p : List D} (hp : z ∉ p) (hxp : path G.clink x p) :
    ∃ q : List (WDart z), q.map Subtype.val = p ∧ path (G.WalkupE z).clink ⟨x, hx⟩ q :=
  lift_path (b := fun _ => False) (fun u v _ h => G.clink_liftE u v h) p x hx
    (fun _ hy => ⟨fun h => hp (h ▸ hy), not_false⟩) hxp

/-- The local lemma `liftN` of math-comp `planar_Jordan`: a C-path of `G` avoiding `z`, whose
tail avoids `face z`, lifts to a C-path of `WalkupN z`. -/
private theorem liftN {x : D} (hx : x ≠ z) {p : List D} (hp : z ∉ p) (hfp : G.face z ∉ p)
    (hxp : path G.clink x p) :
    ∃ q : List (WDart z), q.map Subtype.val = p ∧ path (G.WalkupN z).clink ⟨x, hx⟩ q :=
  lift_path (b := fun y => y = G.face z) (fun u v hv h => G.clink_liftN u v hv h) p x hx
    (fun _ hy => ⟨fun h => hp (h ▸ hy), fun h => hfp (h ▸ hy)⟩) hxp

/-- The local lemma `liftF` of math-comp `planar_Jordan`: a C-path of `G` avoiding `z`, whose
tail avoids `face (edge z)`, lifts to a C-path of `WalkupF z`. -/
private theorem liftF {x : D} (hx : x ≠ z) {p : List D} (hp : z ∉ p)
    (hfp : G.face (G.edge z) ∉ p) (hxp : path G.clink x p) :
    ∃ q : List (WDart z), q.map Subtype.val = p ∧ path (G.WalkupF z).clink ⟨x, hx⟩ q :=
  lift_path (b := fun y => y = G.face (G.edge z)) (fun u v hv h => G.clink_liftF u v hv h)
    p x hx (fun _ hy => ⟨fun h => hp (h ▸ hy), fun h => hfp (h ▸ hy)⟩) hxp

end Lift

section Step

variable [Fintype D]

/-- A Moebius path of a hypermap `H` on the darts of a Walkup map, from facts about the
underlying darts: `w` is the dart such that `last u q = H.node w`. -/
private theorem moebius_of_val {z : D} (H : Hypermap (WDart z)) {u : WDart z}
    {q : List (WDart z)} (w : WDart z) (hnd : (u.1 :: q.map Subtype.val).Nodup)
    (hp : path H.clink u q) (hl : (last u q).1 = (H.node w).1)
    (hm : mem2 (q.map Subtype.val) w.1 (H.node u).1) : H.MoebiusPath (u :: q) := by
  refine ⟨List.Nodup.of_map Subtype.val hnd, hp, ?_⟩
  rw [(H.eq_node_iff).1 (Subtype.ext hl)]
  exact (mem2_map Subtype.val_injective).1 hm

/-- The local lemma `oG1` of math-comp `planar_Jordan`: on a dart type `{x, y, z}`, an
injective function with `f x = y` and `f y = z` is a single cycle. -/
private theorem fcard_three {x y z : D} (hxyz : ∀ w, w = x ∨ w = y ∨ w = z) (z'x : x ≠ z)
    (z'y : y ≠ z) {f : D → D} (hf : Injective f) (hfx : f x = y) (hfy : f y = z) :
    f z = x ∧ fcard f Set.univ = 1 := by
  have hfz : f z = x := by
    rcases hxyz (f z) with h | h | h
    · exact h
    · exact absurd (hf (h.trans hfx.symm)).symm z'x
    · exact absurd (hf (h.trans hfy.symm)).symm z'y
  refine ⟨hfz, ?_⟩
  have h1 : nComp (frel f) Set.univ = nComp (frel f) (comp (frel f) x) := by
    apply nComp_congr_set
    intro w
    simp only [Set.mem_univ, mem_comp, true_iff]
    rcases hxyz w with rfl | rfl | rfl
    · exact connect_refl _
    · exact connect_of_rel hfx
    · exact connect_trans (connect_of_rel hfx) (connect_of_rel hfy)
  show nComp (frel f) Set.univ = 1
  rw [h1, nComp_comp (fconnect_sym hf)]

variable [DecidableEq D] (G : Hypermap D)

/-- The inductive step of math-comp `planar_Jordan`: a planar hypermap `G` all of whose Walkup
transforms have the Jordan property has the Jordan property. The seven cases follow the
module documentation. -/
private theorem jordan_step (hG : G.Planar) (IHe : ∀ z, (G.WalkupE z).Jordan)
    (IHn : ∀ z, (G.WalkupN z).Jordan) (IHf : ∀ z, (G.WalkupF z).Jordan) : G.Jordan := by
  rintro (_ | ⟨x, p⟩) hq
  · exact hq
  obtain ⟨hnd, hxp, ptnx⟩ := hq
  generalize ht : G.face (G.edge (last x p)) = t at ptnx
  have Lp : last x p = G.node t := by rw [← ht, G.edgeK]
  clear ht
  -- 1) all darts are on `x :: p`: otherwise suppress a dart not in `p` with an E-transform
  have sGp : ∀ w, w ∈ x :: p := by
    intro z
    by_contra xp'z
    have z'x : x ≠ z := fun h => xp'z (h ▸ List.mem_cons_self)
    have p'z : z ∉ p := fun h => xp'z (List.mem_cons_of_mem _ h)
    have z't : t ≠ z := fun h => p'z (h ▸ mem2l ptnx)
    have z'nt : G.node t ≠ z := by
      intro h; apply xp'z; rw [← h, ← Lp]; exact mem_last x p
    have z'nx : G.node x ≠ z := fun h => p'z (h ▸ mem2r ptnx)
    obtain ⟨q, Dq, uCq⟩ := G.liftE z'x p'z hxp
    refine IHe z _ (moebius_of_val _ ⟨t, z't⟩ (by rw [Dq]; exact hnd) uCq ?_ ?_)
    · rw [← last_map Subtype.val, Dq, WalkupE_node_val, skip1_of_ne z z'nt]
      exact Lp
    · rw [Dq, WalkupE_node_val, skip1_of_ne z z'nx]
      exact ptnx
  -- `p = y :: p`
  obtain _ | ⟨y, p⟩ := p
  · exact ptnx
  obtain ⟨xCy, yCp⟩ := hxp
  simp only [last_cons] at Lp
  have yp'x : x ∉ y :: p := (List.nodup_cons.1 hnd).1
  have x'y : y ≠ x := fun h => yp'x (h ▸ List.mem_cons_self)
  have x't : t ≠ x := fun h => yp'x (h ▸ mem2l ptnx)
  have x'nt : G.node t ≠ x := by
    intro h; apply yp'x; rw [← h, ← Lp]; exact mem_last y p
  -- `p = y :: z :: p`; the case `p = [y]` contradicts `mem2 [y] t (node x)`
  obtain _ | ⟨z, p⟩ := p
  · rw [mem2_singleton] at ptnx
    simp only [last_nil] at Lp
    exact x't (G.nodeI (ptnx.2.trans Lp)).symm
  simp only [last_cons] at Lp
  have Uxyzp := hnd
  simp only [List.nodup_cons, List.mem_cons, not_or] at Uxyzp
  obtain ⟨⟨-, z'x, p'x⟩, ⟨z'y, p'y⟩, p'z, Up⟩ := Uxyzp
  have zp'y : y ∉ z :: p := (List.nodup_cons.1 (List.nodup_cons.1 hnd).2).1
  have y'nt : G.node t ≠ y := by
    intro h; apply zp'y; rw [← h, ← Lp]; exact mem_last z p
  -- 2) `face x = y`: otherwise suppress `x` with an E-transform
  have Dfx : G.face x = y := by
    rcases xCy with Dny | Dfx
    · exfalso
      obtain ⟨q, Dq, uCq⟩ := G.liftE x'y (fun h => yp'x (List.mem_cons_of_mem _ h)) yCp
      refine IHe x _ (moebius_of_val _ ⟨t, x't⟩ (by rw [Dq]; exact (List.nodup_cons.1 hnd).2)
        uCq ?_ ?_)
      · rw [← last_map Subtype.val, Dq, WalkupE_node_val, skip1_of_ne x x'nt]
        exact Lp
      · rw [Dq, WalkupE_node_val, skip1_of_eq x Dny.symm]
        have y't : y ≠ t := by
          intro h; apply x'nt; rw [← h]; exact Dny.symm
        exact (mem2_cons_of_ne y't).1 ptnx
    · exact Dfx
  obtain ⟨yCz, zCp⟩ := yCp
  -- 3) `face y = z`: otherwise suppress `y` with an F-transform
  have Dfy : G.face y = z := by
    rcases yCz with Dnz | Dfy
    · exfalso
      have hfey : G.face (G.edge y) = z := by rw [Dnz, G.nodeK]
      obtain ⟨q, Dq, vCq⟩ :=
        G.liftF (z := y) (Ne.symm z'y) p'y (by rw [hfey]; exact p'z) zCp
      have nx'y : G.node x ≠ y := fun h => z'x (G.nodeI (h.trans Dnz))
      -- the dart `w` of `WalkupF y` with `node w = last (z :: p)` is `t`, or `z` if `t = y`
      obtain ⟨w, hw1, hw2⟩ : ∃ w : WDart y,
          skip1 y G.node w.1 = G.node t ∧ mem2 (z :: p) w.1 (G.node x) := by
        by_cases hty : t = y
        · refine ⟨⟨z, Ne.symm z'y⟩, ?_, ?_⟩
          · rw [skip1_of_eq y Dnz.symm, hty]
          · rw [hty] at ptnx
            rw [mem2_cons_self]
            exact (List.mem_cons.1 ((mem2_cons_self).1 ptnx)).resolve_left nx'y
        · exact ⟨⟨t, hty⟩, skip1_of_ne y y'nt, (mem2_cons_of_ne (Ne.symm hty)).1 ptnx⟩
      have hfy : G.permF.edge y ≠ y := fun h => x'y (G.faceI (h.trans Dfx.symm))
      have h1 : G.permF.face (G.permF.edge x) ≠ y := by
        show G.node (G.face x) ≠ y
        rw [Dfx]; intro h; exact z'y (G.nodeI (h.trans Dnz))
      refine IHf y (⟨x, Ne.symm x'y⟩ :: ⟨z, Ne.symm z'y⟩ :: q)
        (moebius_of_val _ w ?_ ⟨?_, vCq⟩ ?_ ?_)
      · simp only [List.map_cons, Dq, List.nodup_cons, List.mem_cons, not_or]
        exact ⟨⟨z'x, p'x⟩, p'z, Up⟩
      · right
        apply Subtype.ext
        rw [WalkupF_face_val, G.permF.skipEdge1_of_edge y hfy h1 Dfx]
        exact hfey
      · rw [← last_map Subtype.val, List.map_cons, Dq, WalkupF_node_val, hw1]
        exact Lp
      · rw [List.map_cons, Dq, WalkupF_node_val, skip1_of_ne y nx'y]
        exact hw2
    · exact Dfy
  -- 4) `t = y`: otherwise suppress `y` with an E-transform
  have Dt : t = y := by
    by_contra y't
    obtain ⟨q, Dq, vCq⟩ := G.liftE (z := y) (Ne.symm z'y) p'y zCp
    have hm : mem2 (z :: p) t (G.node x) := (mem2_cons_of_ne (Ne.symm y't)).1 ptnx
    have nx'y : G.node x ≠ y := by
      intro h; apply zp'y; rw [← h]; exact mem2r hm
    refine IHe y (⟨x, Ne.symm x'y⟩ :: ⟨z, Ne.symm z'y⟩ :: q)
      (moebius_of_val _ ⟨t, y't⟩ ?_ ⟨?_, vCq⟩ ?_ ?_)
    · simp only [List.map_cons, Dq, List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨z'x, p'x⟩, p'z, Up⟩
    · rw [clink_WalkupE_iff]
      right
      rw [skip1_of_eq y Dfx, Dfy]
    · rw [← last_map Subtype.val, List.map_cons, Dq, WalkupE_node_val, skip1_of_ne y y'nt]
      exact Lp
    · rw [List.map_cons, Dq, WalkupE_node_val, skip1_of_ne y nx'y]
      exact hm
  subst t
  have p_nx : G.node x ∈ y :: z :: p := mem2_cons_self.1 ptnx
  clear ptnx
  -- 5) `node x = y`: otherwise suppress `y` with an N-transform
  have Dnx : G.node x = y := by
    by_contra y'nx
    obtain ⟨q, Dq, vCq⟩ := G.liftN (z := y) (Ne.symm z'y) p'y (by rw [Dfy]; exact p'z) zCp
    refine IHn y (⟨x, Ne.symm x'y⟩ :: ⟨z, Ne.symm z'y⟩ :: q)
      (moebius_of_val _ ⟨z, Ne.symm z'y⟩ ?_ ⟨?_, vCq⟩ ?_ ?_)
    · simp only [List.map_cons, Dq, List.nodup_cons, List.mem_cons, not_or]
      exact ⟨⟨z'x, p'x⟩, p'z, Up⟩
    · right
      apply Subtype.ext
      rw [WalkupN_face_val, skip1_of_eq y Dfx, Dfy]
    · have h1 : G.permN.face (G.permN.edge z) = y := by
        show G.edge (G.node z) = y
        rw [← Dfy, G.faceK]
      rw [← last_map Subtype.val, List.map_cons, Dq, WalkupN_node_val,
        G.permN.skipEdge1_of_face_edge y y'nt h1]
      exact Lp
    · have h1 : G.permN.face (G.permN.edge x) ≠ y := by
        show G.edge (G.node x) ≠ y
        intro h; apply z'x; rw [← Dfy, ← h, G.nodeK]
      rw [List.map_cons, Dq, WalkupN_node_val, G.permN.skipEdge1_of_ne y y'nt h1 y'nx,
        mem2_cons_self]
      exact (List.mem_cons.1 p_nx).resolve_left y'nx
  obtain _ | ⟨t, p⟩ := p
  · -- the case `#|G| = 3`, excluded by the Euler formula: `G` is a single edge, node and
    -- face cycle `x ↦ y ↦ z ↦ x`, so its genus is its (positive) number of components
    simp only [last_nil] at Lp
    have hxyz : ∀ w, w = x ∨ w = y ∨ w = z := by
      intro w
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using sGp w
    obtain ⟨hfz, hff⟩ := fcard_three hxyz z'x z'y G.faceI Dfx Dfy
    obtain ⟨hnz, hfn⟩ := fcard_three hxyz z'x z'y G.nodeI Dnx Lp.symm
    have hex : G.edge x = y := by rw [← hnz, ← Dfy, G.faceK]
    have hey : G.edge y = z := by rw [← Dnx, ← hfz, G.faceK]
    have hfe := (fcard_three hxyz z'x z'y G.edgeI hex hey).2
    have oG : Fintype.card D = 3 := by
      rw [← Finset.card_univ, Finset.card_eq_three]
      refine ⟨x, y, z, Ne.symm x'y, z'x, z'y, ?_⟩
      ext w
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      exact hxyz w
    have hc : 0 < nComp G.glink Set.univ := nComp_pos.2 ⟨x, Set.mem_univ x⟩
    unfold Planar genus eulerLhs eulerRhs at hG
    rw [hfe, hfn, hff, oG] at hG
    omega
  -- `p = y :: z :: t :: p`
  obtain ⟨zCt, tCp⟩ := zCp
  simp only [last_cons] at Lp
  have t'z : t ≠ z := fun h => p'z (h ▸ List.mem_cons_self)
  have p't : t ∉ p := (List.nodup_cons.1 Up).1
  have z'ny : G.node y ≠ z := by
    intro h; apply p'z; rw [← h, ← Lp]; exact mem_last t p
  have Uxytp : (x :: y :: t :: p).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd ⊢
    exact ⟨⟨hnd.1.1, hnd.1.2.2.1, hnd.1.2.2.2⟩, ⟨hnd.2.1.2.1, hnd.2.1.2.2⟩, hnd.2.2.2⟩
  -- 6) `node t = z`: otherwise suppress `z` with an E-transform
  have Dnt : G.node t = z := by
    rcases zCt with Dnt | Dfz
    · exact Dnt.symm
    · exfalso
      obtain ⟨q, Dq, wCq⟩ := G.liftE t'z (fun h => p'z (List.mem_cons_of_mem _ h)) tCp
      refine IHe z (⟨x, z'x⟩ :: ⟨y, z'y⟩ :: ⟨t, t'z⟩ :: q)
        (moebius_of_val _ ⟨y, z'y⟩ ?_ ⟨?_, ?_, wCq⟩ ?_ ?_)
      · simpa only [List.map_cons, Dq] using Uxytp
      · rw [clink_WalkupE_iff]
        right
        rw [skip1_of_ne z (by rw [Dfx]; exact z'y)]
        exact Dfx
      · rw [clink_WalkupE_iff]
        right
        rw [skip1_of_eq z Dfy]
        exact Dfz
      · rw [← last_map Subtype.val, List.map_cons, List.map_cons, Dq, WalkupE_node_val,
          skip1_of_ne z z'ny]
        exact Lp
      · rw [List.map_cons, List.map_cons, Dq, WalkupE_node_val,
          skip1_of_ne z (by rw [Dnx]; exact z'y), Dnx]
        exact mem2_cons_self.2 List.mem_cons_self
  -- 7) suppress `z` with an F-transform
  have hfez : G.face (G.edge z) = t := by rw [← Dnt, G.nodeK]
  obtain ⟨q, Dq, wCq⟩ := G.liftF t'z (fun h => p'z (List.mem_cons_of_mem _ h))
    (by rw [hfez]; exact p't) tCp
  have hfz : G.permF.edge z ≠ z := fun h => z'y (G.faceI (Dfy.trans h.symm))
  refine IHf z (⟨x, z'x⟩ :: ⟨y, z'y⟩ :: ⟨t, t'z⟩ :: q)
    (moebius_of_val _ ⟨y, z'y⟩ ?_ ⟨?_, ?_, wCq⟩ ?_ ?_)
  · simpa only [List.map_cons, Dq] using Uxytp
  · have h1 : G.permF.face (G.permF.edge x) ≠ z := by
      show G.node (G.face x) ≠ z
      rw [Dfx]; exact z'ny
    have h2 : G.permF.edge x ≠ z := by
      show G.face x ≠ z
      rw [Dfx]; exact z'y
    right
    apply Subtype.ext
    rw [WalkupF_face_val, G.permF.skipEdge1_of_ne z hfz h1 h2]
    exact Dfx
  · have h1 : G.permF.face (G.permF.edge y) ≠ z := by
      show G.node (G.face y) ≠ z
      rw [Dfy]; intro h; exact t'z (G.nodeI (Dnt.trans h.symm))
    right
    apply Subtype.ext
    rw [WalkupF_face_val, G.permF.skipEdge1_of_edge z hfz h1 Dfy]
    exact hfez
  · rw [← last_map Subtype.val, List.map_cons, List.map_cons, Dq, WalkupF_node_val,
      skip1_of_ne z z'ny]
    exact Lp
  · rw [List.map_cons, List.map_cons, Dq, WalkupF_node_val,
      skip1_of_ne z (by rw [Dnx]; exact z'y), Dnx]
    exact mem2_cons_self.2 List.mem_cons_self

end Step

/-- math-comp `planar_Jordan`. -/
theorem jordan_of_planar [Fintype D] (G : Hypermap D) (hG : G.Planar) : G.Jordan := by
  classical
  suffices h : ∀ (n : ℕ) (D : Type u) [Fintype D] [DecidableEq D] (G : Hypermap D),
      Fintype.card D ≤ n → G.Planar → G.Jordan from h _ D G le_rfl hG
  intro n
  induction n with
  | zero =>
    intro D _ _ G hn _ q hq
    have : IsEmpty D := Fintype.card_eq_zero_iff.1 (Nat.le_zero.1 hn)
    rcases q with _ | ⟨x, _⟩
    · exact hq
    · exact isEmptyElim x
  | succ n ih =>
    intro D _ _ G hn hG
    have hcard (z : D) : Fintype.card (WDart z) ≤ n := by
      have := card_S_Walkup z
      omega
    exact jordan_step G hG (fun z => ih _ _ (hcard z) (G.planar_WalkupE z hG))
      (fun z => ih _ _ (hcard z) (G.planar_WalkupN z hG))
      (fun z => ih _ _ (hcard z) (G.planar_WalkupF z hG))

end Hypermap

end FourColor
