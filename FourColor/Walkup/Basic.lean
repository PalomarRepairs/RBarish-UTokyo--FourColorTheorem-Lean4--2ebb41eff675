/-
Copyright (c) 2026. Lean 4 port of the planarity part of the Coq/Rocq formal proof
of the Four Color Theorem by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Hypermap

/-!
# The Walkup construction: definitions  (port of `walkup.v`, part 1)

The Walkup construction (as described by Stahl) removes a point `z` from the domain of a
hypermap, suppressing it from two of the three permutations.  The third permutation then
needs a slightly more complex adjustment to reestablish the triangular identity.  Because of
this asymmetry, there are actually three ways of applying the transformation, all of which
are used in the Jordan/Euler equivalence proof.

For `G : Hypermap D` and `z : D` we define

* `WDart z`         : the darts `{x // x ≠ z}` of the Walkup maps (math-comp local `tG'`).
* `skip1 z f`       : the function on `D` that follows `f`, skipping over `z`.
* `skip z hf`       : the corresponding function on `WDart z`, for `hf : Injective f`.
* `G.skipEdge1 z`, `G.skipEdge z` : an explicit inverse to `skip node ∘ skip face`.
* `G.WalkupE z`     : the hypermap with permutations `skipEdge`, `skip node`, `skip face`.
* `G.WalkupN z`     : the hypermap whose edge and face permutations are `skip edge`, `skip face`.
* `G.WalkupF z`     : the hypermap whose edge and node permutations are `skip edge`, `skip node`.
* `G.crossEdge z`   : `z` and `node z` are on the same edge cycle (math-comp `cross_edge`).
* `G.skipEdgeDomain z` : the darts whose edge cycles change in `WalkupE z`.

The genus/Euler-formula bookkeeping (math-comp local definitions `z_comp`, `z_barb`,
`disconnected`, `n_comp_z`) is also defined here, since it is shared between the files
`Walkup/Edge.lean`, `Walkup/Comp.lean` and `Walkup/Genus.lean`.
-/

namespace FourColor

open Function

universe u

namespace Hypermap

variable {D : Type u}

/-- The darts of the Walkup transforms that remove `z` (math-comp local `tG'`). -/
abbrev WDart (z : D) : Type u := {x : D // x ≠ z}

section Skip

variable [DecidableEq D] (z : D)

/-- math-comp `skip1 f`: follow `f`, skipping over `z`. -/
def skip1 (f : D → D) (x : D) : D := if f x = z then f z else f x

variable {f : D → D}

theorem skip1_of_eq {x : D} (h : f x = z) : skip1 z f x = f z := ite_eq_left h
theorem skip1_of_ne {x : D} (h : f x ≠ z) : skip1 z f x = f x := ite_eq_right h

/-- math-comp `skip_subproof`. -/
theorem skip1_ne (hf : Injective f) (u : WDart z) : skip1 z f u.1 ≠ z := by
  unfold skip1
  split_ifs with h
  · intro h'
    exact u.2 (hf (h.trans h'.symm))
  · exact h

/-- math-comp `skip`: the function on `{x // x ≠ z}` obtained from `f` by skipping over `z`;
its cycle representation is that of `f` with `z` removed. -/
def skip (hf : Injective f) (u : WDart z) : WDart z := ⟨skip1 z f u.1, skip1_ne z hf u⟩

@[simp] theorem skip_val (hf : Injective f) (u : WDart z) : (skip z hf u).1 = skip1 z f u.1 :=
  rfl

/-- math-comp `inj_skip`. -/
theorem inj_skip (hf : Injective f) : Injective (skip z hf) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  have h' : skip1 z f x = skip1 z f y := congrArg Subtype.val h
  unfold skip1 at h'
  apply Subtype.ext
  show x = y
  split_ifs at h' with h1 h2 h2
  · exact hf (h1.trans h2.symm)
  · exact absurd (hf h').symm hy
  · exact absurd (hf h') hx
  · exact hf h'

/-- math-comp `valE_skip`. -/
theorem valE_skip (hf : Injective f) {u v : WDart z} (h : v.1 = f u.1) : v = skip z hf u := by
  apply Subtype.ext
  simp only [skip_val, skip1]
  rw [ite_eq_right (h ▸ v.2)]
  exact h

/-- math-comp `base_skip`: `skip` agrees with `f` away from `finv f z`. -/
theorem base_skip (hf : Injective f) {u v : WDart z} (h : f u.1 ≠ z) :
    f u.1 = v.1 ↔ skip z hf u = v := by
  rw [Subtype.ext_iff, skip_val, skip1, ite_eq_right h]

end Skip

section WalkupE

variable [Fintype D] [DecidableEq D] (G : Hypermap D) (z : D)

/-- math-comp `skip_edge1`: the self-expanding function corresponding to `skipEdge`. -/
def skipEdge1 (x : D) : D :=
  if G.edge z = z then G.edge x
  else if G.face (G.edge x) = z then G.edge z
  else if G.edge x = z then G.edge (G.node z)
  else G.edge x

/-- math-comp `skip_edge_subproof`. -/
theorem skipEdge1_ne (u : WDart z) : G.skipEdge1 z u.1 ≠ z := by
  obtain ⟨x, hx⟩ := u
  simp only [skipEdge1]
  split_ifs with h1 h2 h3
  · intro h; exact hx (G.edgeI (h.trans h1.symm))
  · exact h1
  · intro h
    have : G.face (G.edge (G.node z)) = G.face z := congrArg G.face h
    rw [G.nodeK] at this
    exact h2 (by rw [h3]; exact this.symm)
  · exact h3

/-- math-comp `skip_edge`: an explicit inverse to `skip node ∘ skip face`. -/
def skipEdge (u : WDart z) : WDart z := ⟨G.skipEdge1 z u.1, G.skipEdge1_ne z u⟩

@[simp] theorem skipEdge_val (u : WDart z) : (G.skipEdge z u).1 = G.skipEdge1 z u.1 := rfl

omit [Fintype D] in
theorem skipEdge1_of_edge_fixed (hez : G.edge z = z) (x : D) : G.skipEdge1 z x = G.edge x := by
  simp only [skipEdge1, ite_eq_left hez]

omit [Fintype D] in
theorem skipEdge1_of_face_edge (hez : G.edge z ≠ z) {x : D} (h : G.face (G.edge x) = z) :
    G.skipEdge1 z x = G.edge z := by
  simp only [skipEdge1, ite_eq_right hez, ite_eq_left h]

omit [Fintype D] in
theorem skipEdge1_of_edge (hez : G.edge z ≠ z) {x : D} (h₁ : G.face (G.edge x) ≠ z)
    (h₂ : G.edge x = z) : G.skipEdge1 z x = G.edge (G.node z) := by
  simp only [skipEdge1, ite_eq_right hez, ite_eq_right h₁, ite_eq_left h₂]

omit [Fintype D] in
theorem skipEdge1_of_ne (hez : G.edge z ≠ z) {x : D} (h₁ : G.face (G.edge x) ≠ z)
    (h₂ : G.edge x ≠ z) : G.skipEdge1 z x = G.edge x := by
  simp only [skipEdge1, ite_eq_right hez, ite_eq_right h₁, ite_eq_right h₂]

/-- math-comp `skip_edgeK`. -/
theorem skipEdgeK (u : WDart z) : skip z G.nodeI (skip z G.faceI (G.skipEdge z u)) = u := by
  obtain ⟨x, hx⟩ := u
  apply Subtype.ext
  simp only [skip_val, skipEdge_val]
  by_cases hez : G.edge z = z
  · rw [G.skipEdge1_of_edge_fixed z hez]
    by_cases hfex : G.face (G.edge x) = z
    · have hnfz : G.node (G.face z) = z := by
        have := G.edgeK z; rwa [hez] at this
      rw [skip1_of_eq z hfex, skip1_of_eq z hnfz]
      have := G.edgeK x; rw [hfex] at this; exact this
    · rw [skip1_of_ne z hfex, skip1_of_ne z (by rw [G.edgeK]; exact hx), G.edgeK]
  · by_cases hfex : G.face (G.edge x) = z
    · rw [G.skipEdge1_of_face_edge z hez hfex]
      have hxnz : x = G.node z := by
        have := G.edgeK x; rw [hfex] at this; exact this.symm
      by_cases hfez : G.face (G.edge z) = z
      · exfalso
        have hnz : G.node z = z := by
          have := G.edgeK z; rwa [hfez] at this
        exact hx (hxnz.trans hnz)
      · rw [skip1_of_ne z hfez, skip1_of_eq z (G.edgeK z), hxnz]
    · by_cases hex : G.edge x = z
      · rw [G.skipEdge1_of_edge z hez hfex hex, skip1_of_eq z (G.nodeK z)]
        have hx' : x = G.node (G.face z) := by
          have := G.edgeK x; rw [hex] at this; exact this.symm
        have hnfz : G.node (G.face z) ≠ z := hx' ▸ hx
        rw [skip1_of_ne z hnfz, hx']
      · rw [G.skipEdge1_of_ne z hez hfex hex, skip1_of_ne z hfex,
          skip1_of_ne z (by rw [G.edgeK]; exact hx), G.edgeK]

/-- math-comp `WalkupE`: the hypermap obtained by removing `z` from the node and face cycles,
with the edge permutation adjusted to restore the triangular identity. -/
def WalkupE : Hypermap (WDart z) where
  edge := G.skipEdge z
  node := skip z G.nodeI
  face := skip z G.faceI
  edgeK := G.skipEdgeK z

@[simp] theorem WalkupE_edge_val (u : WDart z) : ((G.WalkupE z).edge u).1 = G.skipEdge1 z u.1 :=
  rfl
@[simp] theorem WalkupE_node_val (u : WDart z) : ((G.WalkupE z).node u).1 = skip1 z G.node u.1 :=
  rfl
@[simp] theorem WalkupE_face_val (u : WDart z) : ((G.WalkupE z).face u).1 = skip1 z G.face u.1 :=
  rfl

/-- math-comp `WalkupI`: `x` as a dart of the Walkup map, defaulting to `u` if `x = z`. -/
def WalkupI (u : WDart z) (x : D) : WDart z := if h : x = z then u else ⟨x, h⟩

omit [Fintype D] in
/-- math-comp `WalkupI_eq`. -/
theorem WalkupI_eq (u : WDart z) (x : D) : (WalkupI z u x).1 = if z = x then u.1 else x := by
  unfold WalkupI
  by_cases h : x = z
  · rw [dite_eq_left h, ite_eq_left h.symm]
  · rw [dite_eq_right h, ite_eq_right (Ne.symm h)]

omit [Fintype D] [DecidableEq D] in
/-- math-comp `Walkup_seq`: a sequence avoiding `z` lifts to the Walkup darts. -/
theorem Walkup_seq {p : List D} (hp : z ∉ p) : ∃ q : List (WDart z), q.map Subtype.val = p := by
  induction p with
  | nil => exact ⟨[], rfl⟩
  | cons x p ih =>
    simp only [List.mem_cons, not_or] at hp
    obtain ⟨q, hq⟩ := ih hp.2
    exact ⟨⟨x, Ne.symm hp.1⟩ :: q, by simp [hq]⟩

/-- math-comp `base_skip_edge`: `skipEdge` agrees with `edge` away from `node (face z)` and
`node z`. -/
theorem base_skip_edge {u v : WDart z} (h₁ : u.1 ≠ G.node (G.face z)) (h₂ : u.1 ≠ G.node z) :
    G.edge u.1 = v.1 ↔ G.skipEdge z u = v := by
  have key : G.skipEdge1 z u.1 = G.edge u.1 := by
    simp only [skipEdge1]
    split_ifs with h1 h2 h3
    · rfl
    · exact absurd (by have := G.edgeK u.1; rw [h2] at this; exact this.symm) h₂
    · exact absurd (by have := G.edgeK u.1; rw [h3] at this; exact this.symm) h₁
    · rfl
  rw [Subtype.ext_iff, skipEdge_val, key]

/-- math-comp `glink_fp_skip_edge`: if `z` is a fixed point of one of the permutations,
`skipEdge` is just `skip edge`. -/
theorem glink_fp_skip_edge (hz : G.glink z z) (u : WDart z) :
    G.skipEdge z u = skip z G.edgeI u := by
  obtain ⟨x, hx⟩ := u
  apply Subtype.ext
  simp only [skipEdge_val, skip_val, skipEdge1, skip1]
  rcases hz with hez | hnz | hfz
  · rw [ite_eq_left hez]
    split_ifs with h
    · rw [h, hez]
    · rfl
  · by_cases hez : G.edge z = z
    · rw [ite_eq_left hez]; split_ifs with h
      · rw [h, hez]
      · rfl
    rw [ite_eq_right hez]
    by_cases hfex : G.face (G.edge x) = z
    · exfalso
      have := G.edgeK x; rw [hfex, hnz] at this; exact hx this.symm
    rw [ite_eq_right hfex]
    split_ifs with hex
    · rw [hnz]
    · rfl
  · by_cases hez : G.edge z = z
    · rw [ite_eq_left hez]; split_ifs with h
      · rw [h, hez]
      · rfl
    rw [ite_eq_right hez]
    by_cases hfex : G.face (G.edge x) = z
    · rw [ite_eq_left hfex]
      have hex : G.edge x = z := G.faceI (hfex.trans hfz.symm)
      rw [ite_eq_left hex]
    · rw [ite_eq_right hfex]
      by_cases hex : G.edge x = z
      · exfalso; rw [hex, hfz] at hfex; exact hfex rfl
      · rw [ite_eq_right hex, ite_eq_right hex]

/-- The C-links of `WalkupE z`, in terms of the self-expanding functions. -/
theorem clink_WalkupE_iff (u v : WDart z) :
    (G.WalkupE z).clink u v ↔ (u.1 = skip1 z G.node v.1 ∨ skip1 z G.face u.1 = v.1) := by
  simp only [clink, Subtype.ext_iff, WalkupE_node_val, WalkupE_face_val]

/-- math-comp `base_clink_Walkup`: C-links of `WalkupE z` agree with those of `G` away from
`edge (node z)` and `node z`. -/
theorem base_clink_Walkup {u v : WDart z} (h₁ : u.1 ≠ G.edge (G.node z)) (h₂ : u.1 ≠ G.node z) :
    G.clink u.1 v.1 ↔ (G.WalkupE z).clink u v := by
  rw [clink_WalkupE_iff]
  have hf : skip1 z G.face u.1 = G.face u.1 := by
    unfold skip1
    rw [ite_eq_right]
    intro h
    exact h₁ ((G.face_eq_iff).1 h)
  rw [hf]
  unfold clink skip1
  split_ifs with hn
  · constructor
    · rintro (h | h)
      · exact absurd (h.trans hn) u.2
      · exact Or.inr h
    · rintro (h | h)
      · exact absurd h h₂
      · exact Or.inr h
  · exact Iff.rfl

/-- math-comp `card_Walkup`. -/
theorem card_Walkup : Fintype.card (WDart z) = Fintype.card D - 1 := by
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]

/-- math-comp `card_S_Walkup`. -/
theorem card_S_Walkup : Fintype.card D = Fintype.card (WDart z) + 1 := by
  rw [card_Walkup]
  have : 0 < Fintype.card D := Fintype.card_pos_iff.2 ⟨z⟩
  omega

end WalkupE

/-! ### The dual Walkup transforms -/

section DualWalkup

variable [Fintype D] [DecidableEq D] (G : Hypermap D) (z : D)

/-- math-comp `WalkupN`: the hypermap whose edge and face permutations are `skip edge` and
`skip face`. -/
def WalkupN : Hypermap (WDart z) := (G.permN.WalkupE z).permF

/-- math-comp `WalkupF`: the hypermap whose edge and node permutations are `skip edge` and
`skip node`. -/
def WalkupF : Hypermap (WDart z) := (G.permF.WalkupE z).permN

@[simp] theorem WalkupN_edge_val (u : WDart z) : ((G.WalkupN z).edge u).1 = skip1 z G.edge u.1 :=
  rfl
@[simp] theorem WalkupN_node_val (u : WDart z) :
    ((G.WalkupN z).node u).1 = G.permN.skipEdge1 z u.1 := rfl
@[simp] theorem WalkupN_face_val (u : WDart z) : ((G.WalkupN z).face u).1 = skip1 z G.face u.1 :=
  rfl

@[simp] theorem WalkupF_edge_val (u : WDart z) : ((G.WalkupF z).edge u).1 = skip1 z G.edge u.1 :=
  rfl
@[simp] theorem WalkupF_node_val (u : WDart z) : ((G.WalkupF z).node u).1 = skip1 z G.node u.1 :=
  rfl
@[simp] theorem WalkupF_face_val (u : WDart z) :
    ((G.WalkupF z).face u).1 = G.permF.skipEdge1 z u.1 := rfl

end DualWalkup

/-! ### Cross edges and the Euler bookkeeping -/

section Bookkeeping

variable (G : Hypermap D) (z : D)

/-- math-comp `cross_edge z`: `z` and `node z` are on the same edge cycle.  This edge cycle is
split in two in `WalkupE z` if `z` is not degenerate (`¬ glink z z`); conversely, if
`crossEdge z` does not hold or if `z` is degenerate, the genus is invariant. -/
def crossEdge : Prop := G.cedge z (G.node z)

/-- math-comp `skip_edge_domain z`: the darts on the edge cycles of `z` and `node z`, i.e.,
the domain of the edge cycles of `G` that change in `WalkupE z`. -/
def skipEdgeDomain : Set D := {x | G.cedge x z ∨ G.cedge x (G.node z)}

variable [Fintype D] [DecidableEq D]

/-- math-comp local `z_comp`: the darts of `WalkupE z` that are C-connected to a C-neighbour
of `z` in `G`. -/
def zComp : Set (WDart z) :=
  closure (G.WalkupE z).clink (Subtype.val ⁻¹' {y | G.clink z y})

/-- math-comp local `z_barb`: `z` is an isolated dart (its only C-neighbour is itself). -/
def ZBarb : Prop := ∀ y, G.clink z y → y = z

/-- math-comp local `disconnected`: removing `z` disconnects its component. -/
def Disconnected : Prop := 1 < nComp (G.WalkupE z).clink (G.zComp z)

open Classical in
/-- math-comp local `n_comp_z disc`. -/
noncomputable def nCompZ (disc : Prop) : ℕ :=
  if G.glink z z then (if G.ZBarb z then 1 else 0) + 1 else (if disc then 0 else 1)

/-- math-comp `not_cross_edge_Walkup` (a local lemma in `walkup.v`): if `z` and `node z` are
on different edge cycles, then `edge z` and `node (face z)` stay on the same edge cycle of
`WalkupE z`. -/
theorem not_cross_edge_Walkup {u v : WDart z} (hz : ¬ G.crossEdge z) (hu : u.1 = G.edge z)
    (hv : v.1 = G.node (G.face z)) : (G.WalkupE z).cedge u v := by
  have hez : G.edge z ≠ z := hu ▸ u.2
  -- A duplicate-free edge path from `edge z` to `z`.
  obtain ⟨p0, hp0, hl0⟩ := connect_iff_path.1 ((G.cedgeC).1 (fconnect1 G.edge z))
  obtain ⟨p, hp, hnd, -, hl⟩ := shortenP hp0
  rw [hl0] at hl
  -- Drop its last dart `z`; the remaining path ends at `node (face z)`.
  obtain ⟨p, rfl⟩ : ∃ p', p = p' ++ [z] := by
    rcases List.eq_nil_or_concat p with h | ⟨p', t, h⟩
    · subst h; exact absurd hl hez
    · rw [h, List.concat_eq_append, last_concat] at hl
      exact ⟨p', by rw [h, List.concat_eq_append, hl]⟩
  rw [path_concat] at hp
  obtain ⟨hp, hlast⟩ := hp
  have hlast' : last (G.edge z) p = G.node (G.face z) := (G.edge_eq_iff).1 hlast
  rw [← List.cons_append, List.nodup_append] at hnd
  obtain ⟨hnd, -, hzp⟩ := hnd
  have hzp : z ∉ p := fun h =>
    hzp z (List.mem_cons_of_mem _ h) z (List.mem_singleton_self z) rfl
  -- Before its end, the path avoids `node (face z)` (uniqueness) and `node z` (else
  -- `cross_edge z` would hold).
  have hb : ∀ y ∈ belast (G.edge z) p, ¬ (y = G.node (G.face z) ∨ y = G.node z) := by
    intro y hy hy'
    rcases hy' with rfl | rfl
    · rw [lastI (G.edge z) p, List.nodup_append, hlast'] at hnd
      exact hnd.2.2 _ hy _ (List.mem_singleton_self _) rfl
    · exact hz ((G.cedge1 z _).2 (path_connect hp (mem_belast hy)))
  -- Lift it to the Walkup map, where `skipEdge` agrees with `edge` along the path.
  obtain ⟨q, hq⟩ := Walkup_seq z hzp
  refine connect_iff_path.2 ⟨q, ?_, ?_⟩
  · have hpq : path (frel G.edge) u.1 (q.map Subtype.val) := by rw [hq, hu]; exact hp
    refine (path_map_base (b := fun x => x = G.node (G.face z) ∨ x = G.node z) ?_ ?_).1 hpq
    · intro x y hx
      rw [not_or] at hx
      exact G.base_skip_edge z hx.1 hx.2
    · intro y hy
      apply hb
      rw [← hu, ← hq, belast_map]
      exact List.mem_map_of_mem hy
  · apply Subtype.ext
    rw [← last_map Subtype.val u q, hq, hu, hlast', hv]

end Bookkeeping

end Hypermap

end FourColor
