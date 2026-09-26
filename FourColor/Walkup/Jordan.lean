/-
Copyright (c) 2026. Lean 4 port of the planarity part of the Coq/Rocq formal proof
of the Four Color Theorem by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Walkup.Basic

/-!
# The Walkup construction preserves the Jordan property  (port of `walkup.v`, part 5)

We prove here that the `WalkupE` step preserves the Jordan property, i.e., that any Moebius
path in `G' = WalkupE z` can be lifted to a Moebius path in `G`.

This is because N-links and F-links (and hence C-links) are mostly preserved by the
`G' → G` injection: the only possible discrepancy is that F- and N-links in `G'` may skip
over `z`. This can be fixed by inserting `z` in while lifting a Moebius C-path from `G'` to
`G`. However, we may need to do this twice, in which case part of the C-path needs to be
deleted in order to recover a duplicate-free path. The part to be deleted depends on the
position `z` is inserted, relative to the endpoints of the two explicit crossing N-links
prescribed by the Moebius predicate. This gives rise to 13 cases in the proof.

In more detail, besides the standard C-links (`clink`) of `G`, we consider two other kinds of
C-links in `G`: those projected from `G'`, which may skip over `z` (relation `wclink2` below),
and an intermediate kind (`wclink1`) which can only skip over `z` if it is a projected F-link.
We first consider the cases where the projected C-path is a `clink` or `wclink1` path
(`jordan_not_clink`, `jordan_not_clink1`); there we may need to insert `z` in the crossing
N-links or the main contour, but not both. In the other cases (`jordan_split`), the C-path
splits into two `wclink1` paths, the crossing N-links are N-links in `G`, and the part of the
path we have to delete if there is also an F-link skipping over `z` is determined by which
crossing link endpoint lies between the skipping N- and F-links (`jordan_xCp1`,
`jordan_final`).

Throughout, `t` stands for `finv node z = face (edge z)`, so that `node t = z` and
`clink z t`.
-/

namespace FourColor

open Function

universe u

/-! ### Duplicate-free sequences, via counting -/

section Count

variable {α : Type*} [DecidableEq α]

/-- A sequence whose item counts are bounded by those of a duplicate-free sequence is itself
duplicate-free (this subsumes math-comp `subseq_uniq`, `uniq_catC`, `uniq_catCA`, ...). -/
private theorem nodup_of_count_le {l l' : List α} (h : l'.Nodup)
    (hc : ∀ a, l.count a ≤ l'.count a) : l.Nodup :=
  List.nodup_iff_count_le_one.2 fun a => (hc a).trans (List.nodup_iff_count_le_one.1 h a)

/-- Two sub-sequences `l1`, `l2` that are disjoint parts of a duplicate-free sequence `l`
(as witnessed by counting) cannot share an item. -/
private theorem nodup_disj {l l1 l2 : List α} (h : l.Nodup) {a : α} (h1 : a ∈ l1) (h2 : a ∈ l2)
    (hc : l1.count a + l2.count a ≤ l.count a) : False := by
  have h0 := List.nodup_iff_count_le_one.1 h a
  have h1' := List.count_pos_iff.2 h1
  have h2' := List.count_pos_iff.2 h2
  omega

end Count

namespace Hypermap

variable {D : Type u} [Fintype D] [DecidableEq D] (G : Hypermap D) (z : D)

/-! ### Projected contour links -/

/-- The intermediate C-links of `G`, that may only skip over `z` along an F-link (math-comp
local `clink1` in the proof of `Jordan_WalkupE`). -/
private def wclink1 (x y : D) : Prop := x = G.node y ∨ skip1 z G.face x = y

/-- The C-links of `WalkupE z`, projected to `G` (math-comp local `clink2` in the proof of
`Jordan_WalkupE`). -/
private def wclink2 (x y : D) : Prop := x = skip1 z G.node y ∨ skip1 z G.face x = y

/-- `skip1 node` only differs from `node` at `t = finv node z`. -/
private theorem skip1_node_of_ne {t w : D} (nt_z : G.node t = z) (hw : w ≠ t) :
    skip1 z G.node w = G.node w :=
  skip1_of_ne z fun h => hw (G.nodeI (h.trans nt_z.symm))

/-- math-comp local `cpath1I` (in `Jordan_WalkupE`): a projected C-path that avoids
`t = finv node z` is a `wclink1` path. -/
private theorem cpath1I {t x : D} {p : List D} (nt_z : G.node t = z)
    (h : path (G.wclink2 z) x p) (ht : t ∉ p) : path (G.wclink1 z) x p := by
  refine path.mono_mem (fun a b _ hb hab => ?_) h
  rcases hab with hab | hab
  · left
    rw [hab, G.skip1_node_of_ne z nt_z fun h => ht (h ▸ hb)]
  · exact Or.inr hab

omit [Fintype D] in
/-- math-comp local `cpathI` (in `Jordan_WalkupE`): a `wclink1` path that avoids `face z`
is a C-path. -/
private theorem cpathI {x : D} {p : List D} (h : path (G.wclink1 z) x p) (hfz : G.face z ∉ p) :
    path G.clink x p := by
  refine path.mono_mem (fun a b _ hb hab => ?_) h
  rcases hab with hab | hab
  · exact Or.inl hab
  · right
    by_cases hfa : G.face a = z
    · rw [skip1_of_eq z hfa] at hab
      exact absurd (hab ▸ hb) hfz
    · rwa [skip1_of_ne z hfa] at hab

omit [Fintype D] in
/-- math-comp local `cpath1P` (in `Jordan_WalkupE`): a duplicate-free `wclink1` path that is
not a C-path goes through `face z`, and becomes a C-path if `z` is inserted before `face z`. -/
private theorem cpath1P {x : D} {p : List D} (h : path (G.wclink1 z) x p)
    (hn : ¬ path G.clink x p) (hU : p.Nodup) :
    ∃ p1 p2, G.face z ∈ p ∧ p = p1 ++ p2 ∧ last z p2 = last x p ∧
      path G.clink x (p1 ++ [z]) ∧ path G.clink z p2 := by
  have hfz : G.face z ∈ p := by
    by_contra hfz
    exact hn (G.cpathI z h hfz)
  obtain ⟨p1, p2, rfl⟩ := List.append_of_mem hfz
  rw [path_append, path_cons] at h
  obtain ⟨xCp1, p1Cfz, fzCp2⟩ := h
  have hp1 : G.face z ∉ p1 := fun h1 =>
    nodup_disj hU h1 (List.mem_singleton_self _)
      (by simp only [List.count_append, List.count_cons, List.count_nil]; omega)
  have hp2 : G.face z ∉ p2 := fun h2 =>
    nodup_disj hU (List.mem_singleton_self _) h2
      (by simp only [List.count_append, List.count_cons, List.count_nil]; omega)
  have xCp1' := G.cpathI z xCp1 hp1
  have fzCp2' := G.cpathI z fzCp2 hp2
  refine ⟨p1, G.face z :: p2, hfz, rfl, ?_, ?_, G.clinkF z, fzCp2'⟩
  · rw [last_append, last_cons, last_cons]
  · refine path_concat.2 ⟨xCp1', ?_⟩
    by_contra hc
    apply hn
    refine path_append.2 ⟨xCp1', ?_, fzCp2'⟩
    have hfl : G.face (last x p1) ≠ z := fun h' => hc (Or.inr h')
    rcases p1Cfz with h1 | h1
    · exact Or.inl h1
    · rw [skip1_of_ne z hfl] at h1
      exact Or.inr h1

omit [DecidableEq D] in
/-- A convenient form of the Jordan property: there is no duplicate-free C-path `x :: p`
ending at `node w`, with `node x` at or after `w` in `p`. -/
private theorem moebius_false (hG : G.Jordan) {x w : D} {p : List D} (hU : (x :: p).Nodup)
    (hP : path G.clink x p) (hL : last x p = G.node w) (hM : mem2 p w (G.node x)) : False :=
  hG (x :: p) ⟨hU, hP, by rw [hL, G.nodeK]; exact hM⟩

/-! ### The case analysis of `Jordan_WalkupE`

In the lemmas below, `x :: p` is the projection to `G` of a Moebius path of `WalkupE z`, whose
last item is `skip1 node y`. The hypotheses are the math-comp ones: `Uzp : uniq (z :: x :: p)`,
`xCp : path clink2 x p`, `pynx : mem2 p y (skip1 node x)`, `Lp : last x p = skip1 node y`. -/

/-- math-comp `Jordan_WalkupE`, claim `not_xCp`: the projected path is not a C-path of `G`
(otherwise `x :: p`, `z :: x :: p` or `x :: rcons p z` is a Moebius path of `G`). -/
private theorem jordan_not_clink (hG : G.Jordan) {t x y : D} {p : List D}
    (nt_z : G.node t = z) (Uzp : (z :: x :: p).Nodup) (hxy : x ≠ y)
    (pynx : mem2 p y (skip1 z G.node x)) (Lp : last x p = skip1 z G.node y)
    (xCp : path G.clink x p) : False := by
  by_cases hyt : y = t
  · subst hyt
    rw [skip1_of_eq z nt_z] at Lp
    rw [G.skip1_node_of_ne z nt_z hxy] at pynx
    exact G.moebius_false hG (w := y) (p := p ++ [z])
      (nodup_of_count_le Uzp fun a => by
        simp only [List.count_append, List.count_cons, List.count_nil]; omega)
      (path_concat.2 ⟨xCp, by rw [Lp]; exact G.clinkN z⟩)
      (by rw [last_concat]; exact nt_z.symm) (mem2_append.2 (Or.inl pynx))
  · rw [G.skip1_node_of_ne z nt_z hyt] at Lp
    by_cases hxt : x = t
    · subst hxt
      rw [skip1_of_eq z nt_z] at pynx
      exact G.moebius_false hG (x := z) (w := y) (p := x :: p) Uzp ⟨Or.inl nt_z.symm, xCp⟩ Lp
        (mem2_cons.2 (Or.inr pynx))
    · rw [G.skip1_node_of_ne z nt_z hxt] at pynx
      exact G.moebius_false hG (List.nodup_cons.1 Uzp).2 xCp Lp pynx

/-- math-comp `Jordan_WalkupE`, second claim `not_xCp`: the projected path is not even a
`wclink1` path of `G`. -/
private theorem jordan_not_clink1 (hG : G.Jordan) {t x y : D} {p : List D}
    (nt_z : G.node t = z) (Uzp : (z :: x :: p).Nodup) (hxy : x ≠ y)
    (pynx : mem2 p y (skip1 z G.node x)) (Lp : last x p = skip1 z G.node y)
    (xCp : path (G.wclink1 z) x p) : False := by
  have Up : p.Nodup := (List.nodup_cons.1 (List.nodup_cons.1 Uzp).2).2
  obtain ⟨p1, p2, -, rfl, Lp2, xCp1, zCp2⟩ :=
    G.cpath1P z xCp (G.jordan_not_clink z hG nt_z Uzp hxy pynx Lp) Up
  have U : (x :: (p1 ++ z :: p2)).Nodup := nodup_of_count_le Uzp fun a => by
    simp only [List.count_append, List.count_cons]; omega
  have hP : path G.clink x (p1 ++ z :: p2) := by
    rw [← List.singleton_append, ← List.append_assoc, path_append, last_concat]
    exact ⟨xCp1, zCp2⟩
  have hL : last x (p1 ++ z :: p2) = last x (p1 ++ p2) := by
    rw [last_append, last_cons, Lp2]
  by_cases hyt : y = t
  · subst hyt
    rw [skip1_of_eq z nt_z] at Lp
    rw [G.skip1_node_of_ne z nt_z hxy] at pynx
    by_cases hnx : G.node x ∈ p2
    · exact G.moebius_false hG (w := z) U hP (hL.trans Lp)
        (mem2_append.2 (Or.inr (Or.inr (mem2_cons_self.2 (List.mem_cons_of_mem _ hnx)))))
    · rw [mem2r_append hnx] at pynx
      exact G.moebius_false hG (w := y) (p := p1 ++ [z])
        (nodup_of_count_le Uzp fun a => by
          simp only [List.count_append, List.count_cons, List.count_nil]; omega)
        xCp1 (by rw [last_concat]; exact nt_z.symm) (mem2_append.2 (Or.inl pynx))
  · rw [G.skip1_node_of_ne z nt_z hyt] at Lp
    by_cases hxt : x = t
    · subst hxt
      rw [skip1_of_eq z nt_z] at pynx
      by_cases hyp1 : y ∈ p1
      · exact G.moebius_false hG U hP (hL.trans Lp)
          (by rw [nt_z]; exact mem2_append_of_mem hyp1 List.mem_cons_self)
      · rw [mem2l_append hyp1] at pynx
        exact G.moebius_false hG (x := z) (p := p2)
          (nodup_of_count_le Uzp fun a => by
            simp only [List.count_append, List.count_cons]; omega)
          zCp2 (Lp2.trans Lp) pynx
    · rw [G.skip1_node_of_ne z nt_z hxt] at pynx
      exact G.moebius_false hG U hP (hL.trans Lp) (mem2_splice1 pynx)

/-- math-comp `Jordan_WalkupE`, claim `xCp1`: once the projected path has been split as
`p1 ++ t :: p2`, its first part `x :: p1` is a C-path of `G`. -/
private theorem jordan_xCp1 (hG : G.Jordan) {t x y : D} {p1 p2 : List D}
    (nt_z : G.node t = z) (Uzp : (z :: x :: (p1 ++ t :: p2)).Nodup)
    (pynx : mem2 (p1 ++ t :: p2) y (G.node x)) (Lp1 : last x p1 = G.node z)
    (Lp2 : last t p2 = G.node y) (xCp1 : path (G.wclink1 z) x p1)
    (tCp2 : path (G.wclink1 z) t p2) : path G.clink x p1 := by
  by_contra hn
  have Up1 : p1.Nodup := nodup_of_count_le Uzp fun a => by
    simp only [List.count_append, List.count_cons]; omega
  obtain ⟨q1, q2, hfz, rfl, Lq2, xCq1, zCq2⟩ := G.cpath1P z xCp1 hn Up1
  rw [Lp1] at Lq2
  have zCt : G.clink z t := Or.inl nt_z.symm
  have tCp2' : path G.clink t p2 :=
    G.cpathI z tCp2 fun h => nodup_disj Uzp hfz h
      (by simp only [List.count_append, List.count_cons]; omega)
  have hzq1 : z ∈ q1 ++ [z] := List.mem_append_right _ (List.mem_singleton_self z)
  -- `node x` cannot be in `q2`, otherwise `x :: rcons q1 z ++ q2` is a Moebius path.
  have q2'nx : G.node x ∉ q2 := by
    intro hnx
    exact G.moebius_false hG (w := z) (p := (q1 ++ [z]) ++ q2)
      (nodup_of_count_le Uzp fun a => by
        simp only [List.count_append, List.count_cons, List.count_nil]; omega)
      (path_append.2 ⟨xCq1, by rw [last_concat]; exact zCq2⟩)
      (by rw [last_append, last_concat]; exact Lq2) (mem2_append_of_mem hzq1 hnx)
  -- `y` must be in `q2`, otherwise `x :: rcons q1 z ++ t :: p2` is a Moebius path.
  have q2y : y ∈ q2 := by
    by_contra hy
    rw [mem2lr_splice hy q2'nx] at pynx
    exact G.moebius_false hG (w := y) (p := (q1 ++ [z]) ++ t :: p2)
      (nodup_of_count_le Uzp fun a => by
        simp only [List.count_append, List.count_cons, List.count_nil]; omega)
      (path_append.2 ⟨xCq1, by rw [last_concat]; exact ⟨zCt, tCp2'⟩⟩)
      (by rw [last_append, last_concat, last_cons]; exact Lp2)
      (by rw [List.append_assoc, List.singleton_append]; exact mem2_splice1 pynx)
  have p2nx : G.node x ∈ t :: p2 := by
    have hyq1 : y ∉ q1 := fun h => nodup_disj Up1 h q2y
      (by simp only [List.count_append]; omega)
    rw [List.append_assoc, mem2l_append hyq1] at pynx
    exact (List.mem_append.1 (mem2r pynx)).resolve_left q2'nx
  -- Then `x :: rcons q1 z ++ (t :: p2) ++ y :: q22` is a Moebius path.
  obtain ⟨q21, q22, rfl⟩ := List.append_of_mem q2y
  rw [last_append, last_cons] at Lq2
  have yCq22 : path G.clink y q22 := path.of_append_cons zCq2
  exact G.moebius_false hG (w := z) (p := (q1 ++ [z]) ++ ((t :: p2) ++ y :: q22))
    (nodup_of_count_le Uzp fun a => by
      simp only [List.count_append, List.count_cons, List.count_nil]; omega)
    (path_append.2 ⟨xCq1, by
      rw [last_concat]
      exact path_append.2 ⟨⟨zCt, tCp2'⟩, by rw [last_cons, Lp2]; exact ⟨G.clinkN y, yCq22⟩⟩⟩)
    (by rw [last_append, last_append, last_cons]; exact Lq2)
    (mem2_append_of_mem hzq1 (List.mem_append_left _ p2nx))

/-- math-comp `Jordan_WalkupE`, final cases: the second part `t :: p2` of the projected path
has been split as `t :: rcons q1 z ++ q2` by `cpath1P`. -/
private theorem jordan_final (hG : G.Jordan) {t x y : D} {p1 q1 q2 : List D}
    (nt_z : G.node t = z) (Uzp : (z :: x :: (p1 ++ t :: (q1 ++ q2))).Nodup)
    (pynx : mem2 (p1 ++ t :: (q1 ++ q2)) y (G.node x)) (Lp1 : last x p1 = G.node z)
    (hyt : y ≠ t) (xCp1 : path G.clink x p1) (Lq2 : last z q2 = G.node y)
    (tCq1 : path G.clink t (q1 ++ [z])) (zCq2 : path G.clink z q2) : False := by
  -- `y` is not in `t :: q1`, otherwise `t :: rcons q1 z ++ q2` is a Moebius path.
  have q1'y : y ∉ t :: q1 := by
    intro hy
    have hyq1 : y ∈ q1 := (List.mem_cons.1 hy).resolve_left hyt
    refine G.moebius_false hG (w := y) (p := (q1 ++ [z]) ++ q2)
      (nodup_of_count_le Uzp fun a => by
        simp only [List.count_append, List.count_cons, List.count_nil]; omega)
      (path_append.2 ⟨tCq1, by rw [last_concat]; exact zCq2⟩)
      (by rw [last_append, last_concat]; exact Lq2) ?_
    rw [nt_z, List.append_assoc, List.singleton_append]
    exact mem2_append_of_mem hyq1 List.mem_cons_self
  -- `node x` is in `t :: q1`, otherwise `x :: p1 ++ z :: q2` is a Moebius path.
  have q1nx : G.node x ∈ t :: q1 := by
    by_contra hnx
    have pynx' : mem2 (p1 ++ q2) y (G.node x) := by
      rw [show p1 ++ t :: (q1 ++ q2) = p1 ++ (t :: q1) ++ q2 by simp] at pynx
      exact (mem2lr_splice q1'y hnx).1 pynx
    exact G.moebius_false hG (w := y) (p := p1 ++ z :: q2)
      (nodup_of_count_le Uzp fun a => by
        simp only [List.count_append, List.count_cons]; omega)
      (path_append.2 ⟨xCp1, by rw [Lp1]; exact ⟨G.clinkN z, zCq2⟩⟩)
      (by rw [last_append, last_cons]; exact Lq2) (mem2_splice1 pynx')
  -- Hence `y` is in `p1`.
  have p1y : y ∈ p1 := by
    have hnxq2 : G.node x ∉ q2 := fun h => nodup_disj Uzp q1nx h
      (by simp only [List.count_append, List.count_cons]; omega)
    rw [show p1 ++ t :: (q1 ++ q2) = (p1 ++ t :: q1) ++ q2 by simp,
      mem2r_append hnxq2] at pynx
    exact (List.mem_append.1 (mem2l pynx)).resolve_right q1'y
  -- Then `t :: q11 ++ (x :: p1) ++ z :: q2` is a Moebius path, where `last t q11 = node x`.
  obtain ⟨q11, q12, rfl, Lq11⟩ := splitPl q1nx
  have tCq11 : path G.clink t q11 := by
    rw [List.append_assoc] at tCq1
    exact path.take_of_append tCq1
  refine G.moebius_false hG (x := t) (w := y) (p := q11 ++ ((x :: p1) ++ z :: q2))
    (nodup_of_count_le Uzp fun a => by
      simp only [List.count_append, List.count_cons]; omega)
    (path_append.2 ⟨tCq11, by
      rw [Lq11]
      exact path_append.2 ⟨⟨G.clinkN x, xCp1⟩, by rw [last_cons, Lp1]; exact ⟨G.clinkN z, zCq2⟩⟩⟩)
    (by rw [last_append, last_append, last_cons]; exact Lq2) ?_
  rw [nt_z, ← List.append_assoc]
  exact mem2_append_of_mem (List.mem_append_right _ (List.mem_cons_of_mem _ p1y))
    List.mem_cons_self

/-- math-comp `Jordan_WalkupE`, the cases where the projected path goes through
`t = finv node z`, and has been split as `p1 ++ t :: p2`. -/
private theorem jordan_split (hG : G.Jordan) {t x y : D} {p1 p2 : List D}
    (nt_z : G.node t = z) (Uzp : (z :: x :: (p1 ++ t :: p2)).Nodup)
    (xCp : path (G.wclink2 z) x (p1 ++ t :: p2)) (pynx : mem2 (p1 ++ t :: p2) y (G.node x))
    (Lp : last x (p1 ++ t :: p2) = skip1 z G.node y)
    (not_xCp1 : ¬ path (G.wclink1 z) x (p1 ++ t :: p2)) : False := by
  rw [path_append, path_cons] at xCp
  obtain ⟨xCp1, p1Ct, tCp2⟩ := xCp
  have hp1t : t ∉ p1 := fun h => nodup_disj Uzp h (List.mem_singleton_self t)
    (by simp only [List.count_append, List.count_cons, List.count_nil]; omega)
  have hp2t : t ∉ p2 := fun h => nodup_disj Uzp (List.mem_singleton_self t) h
    (by simp only [List.count_append, List.count_cons, List.count_nil]; omega)
  have xCp1' := G.cpath1I z nt_z xCp1 hp1t
  have tCp2' := G.cpath1I z nt_z tCp2 hp2t
  have Lp1 : last x p1 = G.node z := by
    rcases p1Ct with h | h
    · rw [h, skip1_of_eq z nt_z]
    · exact (not_xCp1 (path_append.2 ⟨xCp1', Or.inr h, tCp2'⟩)).elim
  rw [last_append, last_cons] at Lp
  have hyt : y ≠ t := by
    rintro rfl
    rw [skip1_of_eq z nt_z] at Lp
    have h1 : G.node z ∈ x :: p1 := by rw [← Lp1]; exact mem_last x p1
    have h2 : G.node z ∈ y :: p2 := by rw [← Lp]; exact mem_last y p2
    exact nodup_disj Uzp h1 h2
      (by simp only [List.count_append, List.count_cons]; omega)
  rw [G.skip1_node_of_ne z nt_z hyt] at Lp
  have xCp1'' := G.jordan_xCp1 z hG nt_z Uzp pynx Lp1 Lp xCp1' tCp2'
  have Up2 : p2.Nodup := nodup_of_count_le Uzp fun a => by
    simp only [List.count_append, List.count_cons]; omega
  have zCt : G.clink z t := Or.inl nt_z.symm
  -- `t :: p2` is not a C-path, otherwise `x :: p1 ++ z :: t :: p2` is a Moebius path.
  have not_tCp2 : ¬ path G.clink t p2 := by
    intro tCp2''
    exact G.moebius_false hG (w := y) (p := p1 ++ z :: t :: p2)
      (nodup_of_count_le Uzp fun a => by
        simp only [List.count_append, List.count_cons]; omega)
      (path_append.2 ⟨xCp1'', by rw [Lp1]; exact ⟨G.clinkN z, zCt, tCp2''⟩⟩)
      (by rw [last_append, last_cons, last_cons]; exact Lp) (mem2_splice1 pynx)
  obtain ⟨q1, q2, -, rfl, Lq2, tCq1, zCq2⟩ := G.cpath1P z tCp2' not_tCp2 Up2
  rw [Lp] at Lq2
  exact G.jordan_final z hG nt_z Uzp pynx Lp1 hyt xCp1'' Lq2 tCq1 zCq2

/-- The core of math-comp `Jordan_WalkupE`, stated on the projection `x :: p` to `G` of a
Moebius path of `WalkupE z`. -/
private theorem jordan_main (hG : G.Jordan) {t x y : D} {p : List D} (nt_z : G.node t = z)
    (Uzp : (z :: x :: p).Nodup) (xCp : path (G.wclink2 z) x p)
    (pynx : mem2 p y (skip1 z G.node x)) (Lp : last x p = skip1 z G.node y) : False := by
  have hxp : x ∉ p := (List.nodup_cons.1 (List.nodup_cons.1 Uzp).2).1
  have hxy : x ≠ y := fun h => hxp (by rw [h]; exact mem2l pynx)
  have not_xCp1 : ¬ path (G.wclink1 z) x p := G.jordan_not_clink1 z hG nt_z Uzp hxy pynx Lp
  have p_t : t ∈ p := by
    by_contra h
    exact not_xCp1 (G.cpath1I z nt_z xCp h)
  have hxt : x ≠ t := fun h => hxp (by rw [h]; exact p_t)
  rw [G.skip1_node_of_ne z nt_z hxt] at pynx
  obtain ⟨p1, p2, rfl⟩ := List.append_of_mem p_t
  exact G.jordan_split z hG nt_z Uzp xCp pynx Lp not_xCp1

/-- math-comp `Jordan_WalkupE`. -/
theorem jordan_WalkupE (hG : G.Jordan) : (G.WalkupE z).Jordan := by
  rintro (_ | ⟨u, q⟩) hM
  · exact hM
  obtain ⟨Uq, uCq, qvnu⟩ := hM
  refine G.jordan_main z hG (G.edgeK z) (x := u.1) (p := q.map Subtype.val)
    (y := ((G.WalkupE z).face ((G.WalkupE z).edge (last u q))).1) ?_ ?_ ?_ ?_
  · refine List.nodup_cons.2 ⟨?_, ?_⟩
    · intro h
      simp only [List.mem_cons, List.mem_map] at h
      rcases h with h | ⟨v, _, hv⟩
      · exact u.2 h.symm
      · exact v.2 hv
    · have := Uq.map Subtype.val_injective
      rwa [List.map_cons] at this
  · refine (path_map (f := Subtype.val) (x := u) (p := q)).2 ?_
    exact path.mono (fun a b h => (G.clink_WalkupE_iff z a b).1 h) uCq
  · exact (mem2_map Subtype.val_injective).2 qvnu
  · rw [last_map]
    exact (congrArg Subtype.val ((G.WalkupE z).edgeK (last u q))).symm

end Hypermap

end FourColor
