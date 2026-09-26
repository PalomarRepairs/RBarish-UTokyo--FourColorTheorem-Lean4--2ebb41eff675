/-
Copyright (c) 2026. Lean 4 port of the planarity part of the Coq/Rocq formal proof
of the Four Color Theorem by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Walkup.Basic

/-!
# The "tree" lemma  (port of `jordan.v`, `Euler_tree`)

This is a more precise reformulation of the central argument of the graph theoretical proof
of Euler's formula: a connected map with only one face has no cycles so it must be a tree
and contain one terminal node. Our refined version states that every hyperedge contains
either a dart linked to a different hyperedge (dual to a different face), or a degenerate
dart (analogue to a terminal node). Since in either case the `WalkupE` transform
suppressing the dart preserves the genus formula this immediately gives a proof of the
Euler formula; the additional precision is used in the correctness proof of the
reducibility check.

As in the graph theoretical proof, we assume both conditions fail for a given hyperedge and
construct a Moebius path, our analogue of a contour that violates the Jordan curve theorem:
 1) We pick a maximal face-simple arc `x :: p` whose last dart `z1` lies in the same face as
    `node (face x)`, the dart preceding `x` in the hyperedge.
 2) We construct a (dart-simple) contour `face x :: q1` along `p`, that ends at
    `node (face x)`. As this contour is a concatenation of F-cycles, together with the
    F-cycle arc from `face z1` to `node (face x)`, `z1 -- face z1` is the only F-link
    leading into `face x :: q1`.
 3) We construct the arc `face x :: p2` from `face x` to `node (face x)`. This arc does not
    contain `z1`: it is disjoint from `x :: p1` because `x :: p1` is face-simple and `x` is
    non-degenerate. Note that `face x` is on the hyperedge because `node (face x)` is.
 4) Finally we try to extend the contour `face x :: q1` along the reverse of `p2`, until we
    hit `face x :: q1` (this must surely happen as `p2` ends in `face x`). The only F-links
    in this extension originate in `face x :: p2` so by 2) this extension must reach `q1`
    with a reverse N-link; pruning loops in the extension thus yields a Moebius C-path,
    which contradicts the Jordan assumption.

The Coq proof expresses face-simplicity with the canonical face roots `froot face`
(`simple p := uniq (map (froot face) p)`); here we use the equivalent
`List.Pairwise (fun a b => ¬ cface a b)`, and replace the statement
`map rf q =i map rf (x :: p1)` about the faces met by a contour by the (only needed)
inclusion "every dart of `q` shares a face with a dart of `x :: p1`".
-/

namespace FourColor

open Function

universe u

namespace Hypermap

variable {D : Type u}

/-! ### Auxiliary sequence facts -/

/-- If `last x p = y` then `y` is an item of `x :: p`. -/
private theorem mem_of_last_eq {α : Type*} {x y : α} {p : List α} (h : last x p = y) :
    y ∈ x :: p := by
  subst h
  exact mem_last x p

/-- math-comp `mem2_last` (`mem2 s x (last y0 s) = (x \in s)`), direction `←`. -/
private theorem mem2_last_of_mem {α : Type*} {y z : α} {s : List α} (h : z ∈ s) :
    mem2 s z (last y s) := by
  cases s with
  | nil => simp at h
  | cons a s => exact mem2_last.2 h

section EulerTree

variable (G : Hypermap D)

/-- Face-simple sequences: no two items lie on the same face cycle (math-comp's
`simple p := uniq (map (froot face) p)`, anticipating `geometry.v`). -/
private abbrev FaceSimple (p : List D) : Prop := List.Pairwise (fun a b => ¬ G.cface a b) p

variable [Finite D]

/-- Step 1 of math-comp `Euler_tree`: an edge path `x :: p` that is not face-simple contains
a face-simple arc `x' :: p1` whose last dart `z1` lies on the face of `node (face x')`,
the dart preceding `x'` on its edge cycle. -/
private theorem euler_tree_arc {x : D} {p : List D} (hp : fpath G.edge x p)
    (hns : ¬ G.FaceSimple (x :: p)) :
    ∃ x', G.cedge (last x p) x' ∧ ∃ p1, fpath G.edge x' p1 ∧ G.FaceSimple (x' :: p1) ∧
      G.cface (last x' p1) (G.node (G.face x')) := by
  induction p generalizing x with
  | nil => exact absurd (List.pairwise_singleton _ _) hns
  | cons y p ih =>
    obtain ⟨hxy, hyp⟩ := hp
    have hxy : G.edge x = y := hxy
    by_cases hs : G.FaceSimple (y :: p)
    · -- `x` shares a face with some dart `b` of the face-simple arc `y :: p`
      obtain ⟨b, hb, hxb⟩ : ∃ b ∈ y :: p, G.cface x b := by
        by_contra hb
        push Not at hb
        exact hns (List.pairwise_cons.2 ⟨hb, hs⟩)
      refine ⟨y, G.cedgeC.1 (path_connect hyp (mem_last y p)), ?_⟩
      obtain ⟨p1, p2, rfl, hl⟩ := splitPl hb
      refine ⟨p1, (path_append.1 hyp).1, ?_, ?_⟩
      · exact hs.sublist ((List.sublist_append_left p1 p2).cons_cons y)
      · rw [hl, ← hxy, G.edgeK]
        exact G.cfaceC.1 hxb
    · exact ih hyp hs

/-- Step 2 of math-comp `Euler_tree`: the dart-simple contour `face x :: q1` along a
face-simple edge arc `x :: p1` whose last dart `z1` lies on the face of `z`. The contour
ends at `z`, only meets the faces of `x :: p1`, and the only F-links leading into it
start at `z1` or inside it. -/
private theorem euler_tree_contour (z : D) :
    ∀ (p1 : List D) (x : D), fpath G.edge x p1 → G.FaceSimple (x :: p1) →
      G.cface (last x p1) z →
      ∃ q1, path G.clink (G.face x) q1 ∧ last (G.face x) q1 = z ∧
        (G.face x :: q1).Nodup ∧ (∀ t ∈ G.face x :: q1, ∃ b ∈ x :: p1, G.cface t b) ∧
        ∀ y, G.face y ∈ G.face x :: q1 → y ∈ belast (last x p1) (G.face x :: q1) := by
  intro p1
  induction p1 with
  | nil =>
    intro x _ _ hxz
    obtain ⟨q0, hq0, hlq0⟩ := connect_iff_path.1 ((G.cface1 x z).1 hxz)
    obtain ⟨q, hq, hqu, -, hlq⟩ := shortenP hq0
    refine ⟨q, hq.mono fun a b h => Or.inr h, hlq.trans hlq0, hqu, ?_, ?_⟩
    · intro t ht
      exact ⟨x, List.mem_singleton_self x, G.cfaceC.1 ((G.cface1 x t).2 (path_connect hq ht))⟩
    · intro y hy
      rw [last_nil, belast_cons]
      by_cases hyx : y = x
      · rw [hyx]
        exact List.mem_cons_self
      · have hfy : G.face y ∈ q := by
          rcases List.mem_cons.1 hy with h | h
          · exact absurd (G.faceI h) hyx
          · exact h
        obtain ⟨r1, r2, rfl⟩ := List.append_of_mem hfy
        have h1 : last (G.face x) r1 = y := G.faceI (path_append.1 hq).2.1
        rw [belast_append, belast_cons, h1]
        exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
  | cons y p ih =>
    intro x hp hs hz
    obtain ⟨hxy, hyp⟩ := hp
    have hxy : G.edge x = y := hxy
    obtain ⟨hxs, hys⟩ := List.pairwise_cons.1 hs
    obtain ⟨q2, hq2, hlq2, hq2u, hq2f, hq2z⟩ := ih y hyp hys hz
    -- the face cycle `face x :: q1` of `x`, ending at `x`
    obtain ⟨q0, hq0, hlq0⟩ := connect_iff_path.1 ((G.cface1 x x).1 (connect_refl x))
    obtain ⟨q1, hq1, hq1u, -, hlq1⟩ := shortenP hq0
    rw [hlq0] at hlq1
    have hcyc : fcycle G.face (G.face x :: q1) :=
      (cycle_cons _ _ _).2 (path_concat.2 ⟨hq1, congrArg G.face hlq1⟩)
    have hq1x : ∀ t, G.cface x t ↔ t ∈ G.face x :: q1 := fun t =>
      fconnect_cycle hcyc (mem_of_last_eq hlq1)
    refine ⟨q1 ++ G.face y :: q2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [path_append, hlq1]
      refine ⟨hq1.mono fun a b h => Or.inr h, Or.inl ?_, hq2⟩
      rw [← hxy, G.edgeK]
    · rw [last_append, hlq1, last_cons, hlq2]
    · rw [← List.cons_append, List.nodup_append]
      refine ⟨hq1u, hq2u, ?_⟩
      intro a ha b hb hab
      subst hab
      obtain ⟨c, hc, hac⟩ := hq2f a hb
      exact hxs c hc (connect_trans ((hq1x a).2 ha) hac)
    · intro t ht
      rw [← List.cons_append, List.mem_append] at ht
      rcases ht with ht | ht
      · exact ⟨x, List.mem_cons_self, G.cfaceC.1 ((hq1x t).2 ht)⟩
      · obtain ⟨c, hc, htc⟩ := hq2f t ht
        exact ⟨c, List.mem_cons_of_mem _ hc, htc⟩
    · intro t ht
      rw [← List.cons_append, List.mem_append] at ht
      rw [last_cons, belast_cons, belast_append, hlq1, belast_cons]
      rcases ht with ht | ht
      · have htx : t ∈ G.face x :: q1 := (hq1x t).1 ((G.cface1r x t).2 ((hq1x _).2 ht))
        rw [lastI (G.face x) q1, hlq1, List.mem_append, List.mem_singleton] at htx
        rcases htx with h | rfl
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self)
      · have h := hq2z t ht
        rw [belast_cons] at h
        rcases List.mem_cons.1 h with h | h
        · rw [h]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_cons_of_mem _ h))

/-- Steps 2-4 of math-comp `Euler_tree`: if no dart on the edge cycle of `x` is degenerate
or fails `crossEdge`, then a face-simple edge arc `x :: p1` ending on the face of
`node (face x)` yields a Moebius path. -/
private theorem euler_tree_contra (hG : G.Jordan) {x : D}
    (tree_x : ∀ y, G.cedge x y → ¬ G.clink y y ∧ G.crossEdge y) {p1 : List D}
    (hp1 : fpath G.edge x p1) (hs1 : G.FaceSimple (x :: p1))
    (hl1 : G.cface (last x p1) (G.node (G.face x))) : False := by
  -- Step 2: the contour `face x :: q1`, from `face x` to `node (face x)`
  obtain ⟨q1, hq1, hlq1, hq1u, -, hz1q1⟩ :=
    euler_tree_contour G (G.node (G.face x)) p1 x hp1 hs1 hl1
  have hnfx_mem : G.node (G.face x) ∈ G.face x :: q1 := mem_of_last_eq hlq1
  -- `face x` is not on the arc `x :: p1`
  have hp1fx : G.face x ∉ x :: p1 := by
    intro h
    rcases List.mem_cons.1 h with h | h
    · exact (tree_x x (connect_refl x)).1 (Or.inr h)
    · exact (List.pairwise_cons.1 hs1).1 _ h (fconnect1 G.face x)
  have xEnfx : G.cedge x (G.node (G.face x)) :=
    (G.cedge1r x _).2 (by rw [G.faceK])
  -- the edge cycle of `x` is closed under `node`, hence contains `face x`
  have xEfx : G.cedge x (G.face x) :=
    mem_of_connect_of_forward (a := {b | G.cedge x b})
      (fun a b (hab : G.node a = b) (ha : G.cedge x a) =>
        (hab ▸ connect_trans ha (tree_x a ha).2 : G.cedge x b))
      (G.cnodeC.1 (fconnect1 G.node (G.face x))) xEnfx
  have hfx_nfx : G.face x ≠ G.node (G.face x) := fun h =>
    (tree_x _ xEnfx).1 (Or.inl (congrArg G.node h))
  -- Step 3: the edge arc `face x :: p2`, from `face x` to `node (face x)`, avoiding `z1`
  obtain ⟨p2, hp2, hlp2, hz1p2⟩ : ∃ p2, fpath G.edge (G.face x) p2 ∧
      last (G.face x) p2 = G.node (G.face x) ∧ last x p1 ∉ p2 := by
    have hz1n : G.cedge (last x p1) (G.node (G.face x)) :=
      connect_trans (G.cedgeC.1 (path_connect hp1 (mem_last x p1))) xEnfx
    obtain ⟨p0, hp0, hlp0⟩ := connect_iff_path.1 hz1n
    obtain ⟨p, hp, hpu, -, hlp⟩ := shortenP hp0
    rw [hlp0] at hlp
    have hcyc : cycle (frel G.edge) (x :: (p1 ++ p)) := by
      rw [cycle_cons, List.append_assoc, path_append, path_concat, hlp]
      exact ⟨hp1, hp, G.faceK x⟩
    have hfxp : G.face x ∈ x :: (p1 ++ p) :=
      (fconnect_cycle hcyc List.mem_cons_self).1 xEfx
    have hfxp' : G.face x ∈ p := by
      rcases List.mem_cons.1 hfxp with h | h
      · exact absurd (by rw [h]; exact List.mem_cons_self) hp1fx
      · rcases List.mem_append.1 h with h | h
        · exact absurd (List.mem_cons_of_mem _ h) hp1fx
        · exact h
    obtain ⟨r1, r2, rfl⟩ := List.append_of_mem hfxp'
    refine ⟨r2, path.of_append_cons hp, ?_, ?_⟩
    · rw [last_append, last_cons] at hlp
      exact hlp
    · intro h
      exact (List.nodup_cons.1 hpu).1 (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  -- Step 4: extend the contour backwards along `p2`, avoiding `face x :: q1`
  have key : ∀ (r : List D) (y : D), fpath G.edge y r → last y r = G.node (G.face x) →
      last x p1 ∉ r → ∃ q2, path G.clink (G.node (G.face x)) q2 ∧
        last (G.node (G.face x)) q2 = y ∧ ∀ t ∈ q2, t ∉ G.face x :: q1 := by
    intro r
    induction r with
    | nil =>
      intro y _ hy _
      exact ⟨[], trivial, hy.symm, by simp⟩
    | cons w r ih =>
      intro y hr hlr hz1r
      obtain ⟨hyw, hr⟩ := hr
      have hyw : G.edge y = w := hyw
      subst hyw
      have hey : G.edge y ≠ last x p1 := fun h => hz1r (by rw [← h]; exact List.mem_cons_self)
      obtain ⟨q2, hq2, hlq2, hq2a⟩ :=
        ih (G.edge y) hr hlr (fun h => hz1r (List.mem_cons_of_mem _ h))
      -- walk back along the node cycle of `y`, from `face (edge y)` to `y`
      have inner : ∀ (q : List D) (z : D), fpath G.node z q → last z q = G.face (G.edge y) →
          z ≠ G.node (G.face x) ∧ ∃ q2, path G.clink (G.node (G.face x)) q2 ∧
            last (G.node (G.face x)) q2 = z ∧ ∀ t ∈ q2, t ∉ G.face x :: q1 := by
        intro q
        induction q with
        | nil =>
          intro z _ hz
          have hz : z = G.face (G.edge y) := hz
          subst hz
          -- `face (edge y)` is not on the contour, as `edge y -- face (edge y)` would then
          -- be an F-link leading into it
          have hfey : G.face (G.edge y) ∉ G.face x :: q1 := by
            intro h
            have h1 := hz1q1 (G.edge y) h
            rw [belast_cons] at h1
            have h2 : G.edge y ∈ belast (G.face x) q1 := (List.mem_cons.1 h1).resolve_left hey
            rcases List.mem_cons.1 (mem_of_last_eq hlq2) with h3 | h3
            · have hu := hq1u
              rw [lastI (G.face x) q1, hlq1, List.nodup_append] at hu
              exact hu.2.2 _ h2 _ (List.mem_singleton_self _) h3
            · exact hq2a _ h3 (mem_belast h2)
          refine ⟨fun h => hfey (by rw [h]; exact hnfx_mem), q2 ++ [G.face (G.edge y)],
            ?_, last_concat _ _ _, ?_⟩
          · exact path_concat.2 ⟨hq2, by rw [hlq2]; exact G.clinkF _⟩
          · intro t ht
            rcases List.mem_append.1 ht with ht | ht
            · exact hq2a t ht
            · rw [List.mem_singleton.1 ht]
              exact hfey
        | cons w q ihq =>
          intro z hq hlq
          obtain ⟨hzw, hq⟩ := hq
          have hzw : G.node z = w := hzw
          subst hzw
          obtain ⟨hnz, q3, hq3, hlq3, hq3a⟩ := ihq (G.node z) hq hlq
          obtain ⟨q4, hq4, hq4u, hq4s, hlq4⟩ := shortenP hq3
          rw [hlq3] at hlq4
          have hq4a : ∀ t ∈ q4, t ∉ G.face x :: q1 := fun t ht => hq3a t (hq4s t ht)
          have hq4n := List.nodup_cons.1 hq4u
          -- `z` is not on the contour, otherwise `face x :: q1 ++ q4` is a Moebius path
          have hzq : z ∉ G.face x :: q1 := by
            intro hz
            rcases List.mem_cons.1 hz with hz | hz
            · exact hnz (by rw [hz])
            · apply hG (G.face x :: (q1 ++ q4))
              refine ⟨?_, ?_, ?_⟩
              · rw [← List.cons_append, List.nodup_append]
                exact ⟨hq1u, hq4n.2, fun a ha b hb hab => hq4a b hb (hab ▸ ha)⟩
              · rw [path_append, hlq1]
                exact ⟨hq1, hq4⟩
              · rw [last_append, hlq1, hlq4, G.nodeK, mem2r_append hq4n.1]
                have h := mem2_last_of_mem (y := G.face x) hz
                rwa [hlq1] at h
          refine ⟨fun h => hzq (by rw [h]; exact hnfx_mem), q4 ++ [z], ?_, last_concat _ _ _,
            ?_⟩
          · exact path_concat.2 ⟨hq4, by rw [hlq4]; exact G.clinkN z⟩
          · intro t ht
            rcases List.mem_append.1 ht with ht | ht
            · exact hq4a t ht
            · rw [List.mem_singleton.1 ht]
              exact hzq
      obtain ⟨q, hq, hlq⟩ := connect_iff_path.1
        ((G.cnode1r y (G.face (G.edge y))).2 (by rw [G.edgeK]))
      exact (inner q y hq hlq).2
  obtain ⟨q2, -, hlq2, hq2a⟩ := key p2 (G.face x) hp2 hlp2 hz1p2
  rcases List.mem_cons.1 (mem_of_last_eq hlq2) with h | h
  · exact hfx_nfx h
  · exact hq2a _ h List.mem_cons_self

end EulerTree

/-- math-comp `Euler_tree`: in a hypermap with the Jordan property, every edge cycle contains
a degenerate dart (`clink y y`) or a dart `y` whose node is on a different edge cycle
(`¬ crossEdge y`). -/
theorem euler_tree [Finite D] (G : Hypermap D) (x : D) (hG : G.Jordan) :
    ∃ y, G.cedge x y ∧ (G.clink y y ∨ ¬ G.crossEdge y) := by
  by_contra hcon
  push Not at hcon
  -- Step 1: a maximal face-simple arc `x1 :: p1` on the edge cycle of `x`, whose last dart
  -- lies on the face of `node (face x1)`
  obtain ⟨p0, hp0, hl0⟩ := connect_iff_path.1 (G.cedgeC.1 (fconnect1 G.edge x))
  have hns : ¬ G.FaceSimple (x :: G.edge x :: p0) := fun h =>
    (List.pairwise_cons.1 h).1 x (mem_of_last_eq hl0) (connect_refl x)
  obtain ⟨x1, hx1, p1, hp1, hs1, hl1⟩ := G.euler_tree_arc (p := G.edge x :: p0) ⟨rfl, hp0⟩ hns
  rw [last_cons, hl0] at hx1
  exact G.euler_tree_contra hG (fun y hy => hcon y (connect_trans hx1 hy)) hp1 hs1 hl1

end Hypermap

end FourColor
