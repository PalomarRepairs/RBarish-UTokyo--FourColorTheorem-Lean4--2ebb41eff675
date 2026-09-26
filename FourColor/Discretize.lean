/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Approx
import FourColor.GridMap
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Discretizing the coloring problem  (port of `discretize.v`)

Discretizing the coloring problem for an arbitrary finite map. We compute a finite hypermap
whose colorings induce colorings of the map, using the grid computation package.
The discrete approximation is constructed in five steps:
1. Enumerate the regions and adjacencies of `m0`, choosing a representative border point for
   each adjacency.
2. Construct disjoint rectangles covering the border points.
3. Construct approximations of the border rectangles.
4. Construct matte approximations of the regions that meet all the corresponding border
   rectangles.
5. Construct a hypermap from the mattes using the gridmap library.

Assuming a finite simple map `m0` in the real plane we define the following:

* `MapRepr n`     : the representation type for `n`-region transversals for `m0`
  (`Fin n → Point`).
* `MrProper m0 mr` : `mr` is a proper transversal, mapping different indices in `Fin n` to
  points in different regions of `m0`.
* `mrCover m0 mr` : the region covered by the regions of `m0` of the points of `mr`; the
  transversal `mr` covers all the regions of `m0` when `Subregion (cover m0) (mrCover m0 mr)`.

Now assuming a transversal `mr : MapRepr Nr` for some `Nr : ℕ`, we then define:

* `AbMrProper m0 mr b e i` : if the grid rectangle component of the scaled rectangle `b`
  witnesses adjacency at `e : AdjIndex Nr`, then the region of `m0` containing `mr i` meets
  `insetSrect b` if `i` is one of the components of `e`, and is altogether disjoint from `b`
  otherwise. Thus if this holds for all `i`, `b` properly witnesses an `m0` adjacency at `e`.
* `ProperSmatte m0 mr ab m i E` : `m` is a scaled matte approximation of the `m0` region
  containing `mr i`: `m` is included in this region, and meets `insetSrect (ab e)` for all `e`
  in `E` (that witness an adjacency).

Scaled mattes satisfying this latter predicate are built up from a pixel matte around `mr i`,
using the connectedness of the surrounding `m0` region to find a larger interpolating matte
contained in that region, that meets `ab e` for some `e` in `E`.

* `InterpolantAt z U V W` : the region `W` interpolates between `{z} ∪ U` and `V`.
* `smatteInterpolated U V` : the region that is the union of all scaled mattes `W`
  interpolating between the regions `U` and `V`.

## Coq → Lean names

| Coq | Lean |
|---|---|
| `map_repr`, `mr_proper`, `mr_cover`, `exists_map_repr` | `MapRepr`, `MrProper`, `mrCover`, `exists_map_repr` |
| `ab_mr_proper`, `ab_mr_proper_refine` | `AbMrProper`, `ab_mr_proper_refine` |
| section `Let mr_adj` | `MrAdj` |
| `exists_adjbox` | `exists_adjbox` |
| `interpolant_at`, `smatte_interpolated` | `InterpolantAt`, `smatteInterpolated` |
| `refine_smatte_interpolant`, `connected_matte` | same names |
| `proper_smatte`, `refine_smatte_proper`, `exists_smatte` | `ProperSmatte`, same names |
| `discretize_to_hypermap` | `discretize_to_hypermap` |

Lean-only helpers: `capRects` and `mem_capRects` (the `\big[cap_rect/r0]` folds of
`exists_adjbox`), `open_rectangle`, `mem_closure_of_mem`, `mem_iterate_refineRect`.

## Porting notes

* The section variables `m0 : map` and `fin_m0 : finite_simple_map m0` become an explicit
  argument `m0` of the definitions and a hypothesis `fin_m0 : FiniteSimpleMap m0` of the
  lemmas; the section variables `Nr`, `mr`, `mrP` (resp. `ab`, `abP`) of the sections
  `AdjRepr` (resp. `DiscrMatte`) are likewise explicit arguments.
* The Coq coercions from scaled rectangles, scaled mattes and rectangles to regions are the
  explicit functions `srectRegion`, `smatteRegion` and `inRectangle`. `[/\ A, B & C]` is
  `A ∧ B ∧ C`, `exists2 x, P & Q` is `∃ x, P ∧ Q`, `pred Er` is `AdjIndex Nr → Prop`.
* `exists_adjbox`: the Coq `arc` subtype `{e : Er | is_arc e}` (with `is_arc` a boolean
  reflection of `mr_adj`, obtained by excluded middle) is the subtype `{e // MrAdj m0 mr e}`,
  finite under classical decidability. The rectangle intersections
  `\big[cap_rect/ar0]_(i | i \notin v a) ar i` and `\big[cap_rect/ar0 a]_b ar1 b a` are folds
  `capRects` over lists; the first one is taken over all the indices `i` (for `i ∈ v a` the
  chosen rectangle `ar i` is harmless), which simplifies the proof. The proof of `ar1_inj`
  uses the equality of points `eq_of_meet_sep_rect` (available over `ℝ`).
* `discretize_to_hypermap` is stated as an existential over a dart
  type with its `Fintype` and `DecidableEq` instances (Coq's `hypermap` bundles its finite
  type of darts), and uses `exists_grid_map` from `FourColor.GridMap`. The Coq
  `without loss Ds1 : ... / s1 = s` step is the private lemma `discretize_core`, stated for a
  common scale.
-/

namespace FourColor.RealPlane

open Function FourColor.Hypermap

/-! ### Region transversals -/

section MapRepr

/-- Coq `map_repr n`: the representation type for `n`-region transversals. -/
abbrev MapRepr (n : ℕ) : Type := Fin n → Point

/-- Coq `mr_proper mr`: the transversal `mr` maps different indices to points in different
regions of `m0`. -/
def MrProper (m0 : Map) {n : ℕ} (mr : MapRepr n) : Prop :=
  ∀ i, cover m0 (mr i) ∧ ∀ j, m0 (mr i) (mr j) → i = j

/-- Coq `mr_cover mr`: the union of the regions of `m0` of the points of `mr`. -/
def mrCover (m0 : Map) {n : ℕ} (mr : MapRepr n) : Region :=
  fun z => ∃ i, m0 (mr i) z

/-- Coq `exists_map_repr`. -/
theorem exists_map_repr {m0 : Map} (fin_m0 : FiniteSimpleMap m0) :
    ∃ n, ∃ mr : MapRepr n, MrProper m0 mr ∧ Subregion (cover m0) (mrCover m0 mr) := by
  have m0sym : ∀ {z1 z2}, m0 z1 z2 → m0 z2 z1 := fin_m0.map_sym
  have m0tr : ∀ {z1 z2}, m0 z1 z2 → Subregion (m0 z2) (m0 z1) := fin_m0.map_trans
  obtain ⟨k, mr0, sm0r0⟩ := fin_m0.finite_simple_map_finite
  suffices H : ∀ k, ∃ n, ∃ mr : MapRepr n, MrProper m0 mr ∧
      ∀ z, (∃ i, i < k ∧ m0 (mr0 i) z) → mrCover m0 mr z by
    obtain ⟨n, mr, mrP, sr0mr⟩ := H k
    exact ⟨n, mr, mrP, fun z hz => sr0mr z (sm0r0 z hz)⟩
  intro k
  induction k with
  | zero =>
    refine ⟨0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    rintro z ⟨i, hi, -⟩
    exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    obtain ⟨n, mr, mrP, sr0mr⟩ := ih
    set t := mr0 k
    by_cases mr_t : cover m0 t → mrCover m0 mr t
    · refine ⟨n, mr, mrP, ?_⟩
      rintro z ⟨j, hj, m0jz⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
      · exact sr0mr z ⟨j, hj, m0jz⟩
      · obtain ⟨i, m0it⟩ := mr_t (m0tr m0jz _ (m0sym m0jz))
        exact ⟨i, m0tr m0it _ m0jz⟩
    · have ⟨t_cov, mr't⟩ : cover m0 t ∧ ¬ mrCover m0 mr t := by
        by_cases h : cover m0 t
        · exact ⟨h, fun h' => mr_t fun _ => h'⟩
        · exact absurd (fun h' => absurd h' h) mr_t
      refine ⟨n + 1, Fin.cons t mr, ?_, ?_⟩
      · intro i1
        refine Fin.cases ?_ (fun i => ?_) i1
        · refine ⟨t_cov, fun j1 => ?_⟩
          refine Fin.cases (fun _ => rfl) (fun j h => ?_) j1
          exact absurd ⟨j, m0sym h⟩ mr't
        · refine ⟨(mrP i).1, fun j1 => ?_⟩
          refine Fin.cases (fun h => ?_) (fun j h => ?_) j1
          · exact absurd ⟨i, h⟩ mr't
          · exact congrArg Fin.succ ((mrP i).2 j h)
      · rintro z ⟨j, hj, m0jz⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · obtain ⟨i, hi⟩ := sr0mr z ⟨j, hj, m0jz⟩
          exact ⟨i.succ, hi⟩
        · exact ⟨0, m0jz⟩

end MapRepr

/-! ### Small helpers -/

/-- Rectangles are open (not in Coq, where this is inlined). -/
theorem open_rectangle (r : Rectangle) : Open (inRectangle r) :=
  fun _ hz => ⟨r, hz, fun _ h => h⟩

/-- A point of a region is in its closure (not in Coq, where this is inlined). -/
theorem mem_closure_of_mem {r : Region} {z : Point} (hz : r z) : closure r z :=
  fun _ _ hu => ⟨z, hz, hu⟩

/-- The intersection of the rectangles of a list with a rectangle `r0` (Coq
`\big[cap_rect/r0]_(r <- l) r`). -/
noncomputable def capRects (l : List Rectangle) (r0 : Rectangle) : Rectangle :=
  l.foldr capRect r0

/-- Membership in `capRects l r0` (Coq `big_rec` with `mem_cap_rect`). -/
theorem mem_capRects (l : List Rectangle) (r0 : Rectangle) (z : Point) :
    inRectangle (capRects l r0) z ↔ inRectangle r0 z ∧ ∀ r ∈ l, inRectangle r z := by
  induction l with
  | nil => simp [capRects]
  | cons r l ih =>
    simp only [capRects, List.foldr_cons] at ih ⊢
    rw [mem_cap_rect, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

/-- Membership in an iterated refinement of a grid rectangle. -/
theorem mem_iterate_refineRect (n : ℕ) (r : GRect) (p : GPoint) :
    p ∈ refineRect^[n] r ↔ halfg^[n] p ∈ r := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply, ih, iterate_succ_apply', in_refine_rect]

/-! ### Adjacency boxes -/

section AdjRepr

variable {Nr : ℕ}

/-- Coq `ab_mr_proper b e i`: if the grid rectangle of `b` witnesses adjacency at `e`, then the
region of `m0` containing `mr i` meets `insetSrect b` if `i` is a component of `e`, and is
disjoint from `b` otherwise. -/
def AbMrProper (m0 : Map) (mr : MapRepr Nr) (b : ScaledRect) (e : AdjIndex Nr) (i : Fin Nr) :
    Prop :=
  GrProper b.2 → (i ∈ e → Meet (srectRegion (insetSrect b)) (m0 (mr i))) ∧
    (Meet (srectRegion b) (m0 (mr i)) → i ∈ e)

/-- Coq `ab_mr_proper_refine`. -/
theorem ab_mr_proper_refine {m0 : Map} {mr : MapRepr Nr} (s : ℕ) {b : ScaledRect}
    {e : AdjIndex Nr} {i : Fin Nr} (h : AbMrProper m0 mr b e i) :
    AbMrProper m0 mr (refineSrect s b) e i := by
  intro hb
  obtain ⟨ei_b, b_ei⟩ := h ((gr_proper_refine s b.2).1 hb)
  refine ⟨fun hi => ?_, fun ⟨z, hz, hm⟩ => b_ei ⟨z, (in_refine_srect s b z).1 hz, hm⟩⟩
  obtain ⟨z, hz, hm⟩ := ei_b hi
  exact ⟨z, in_refine_inset s hz, hm⟩

/-- Coq section `Let mr_adj e`: the regions of `mr e.1` and `mr e.2` are adjacent (and
`e.1 < e.2`, which always holds for an `AdjIndex`). -/
def MrAdj (m0 : Map) (mr : MapRepr Nr) (e : AdjIndex Nr) : Prop :=
  Adjacent m0 (mr e.fst) (mr e.snd) ∧ e.fst < e.snd

/-- Coq `exists_adjbox`. -/
theorem exists_adjbox {m0 : Map} (fin_m0 : FiniteSimpleMap m0) {mr : MapRepr Nr}
    (mrP : MrProper m0 mr) :
    ∃ ab : AdjBox Nr, AbProper ab ∧ (∃ s, ∀ e i, AbMrProper m0 mr (s, ab e) e i) ∧
      ∀ e, MrAdj m0 mr e → GrProper (ab e) := by
  classical
  have m0sym : ∀ {z1 z2}, m0 z1 z2 → m0 z2 z1 := fin_m0.map_sym
  have m0tr : ∀ {z1 z2}, m0 z1 z2 → Subregion (m0 z2) (m0 z1) := fin_m0.map_trans
  let Arc := {e : AdjIndex Nr // MrAdj m0 mr e}
  have hap : ∀ a : Arc, ∃ p, notCorner m0 p ∧ border m0 (mr a.1.fst) (mr a.1.snd) p :=
    fun a => a.2.1.2
  choose ap apP using hap
  let cl : Fin Nr → Region := fun i => closure (m0 (mr i))
  have apP1 : ∀ a : Arc, cl a.1.fst (ap a) := fun a => (apP a).2.1
  have apP2 : ∀ a : Arc, cl a.1.snd (ap a) := fun a => (apP a).2.2
  let ClA : Arc → Rectangle → Fin Nr → Prop := fun a r i => Meet (inRectangle r) (cl i) → i ∈ a.1
  have har : ∀ a i, ∃ r, ClA a r i ∧ inRectangle r (ap a) := by
    intro a i
    by_cases a_i : i ∈ a.1
    · exact ⟨sepRect (ap a) (ap a), fun _ => a_i, mem_sep_rect _ _⟩
    by_contra no_ar
    have cl_i : cl i (ap a) := by
      intro U openU hU
      obtain ⟨r, r_e, Ur⟩ := openU _ hU
      by_contra m0i'U
      refine no_ar ⟨r, ?_, r_e⟩
      rintro ⟨z, r_z, cl_z⟩
      exact absurd (cl_z U openU (Ur z r_z)) m0i'U
    obtain ⟨me, meP⟩ := (apP a).1
    have hk : ∀ j, cl j (ap a) → ∃ k, k < 2 ∧ m0 (me k) (mr j) := by
      intro j hj
      obtain ⟨k, hk, h, -⟩ := meP (mr j) ⟨(mrP j).1, hj⟩
      exact ⟨k, hk, h⟩
    have inj : ∀ j1 j2 k, m0 (me k) (mr j1) → m0 (me k) (mr j2) → j1 = j2 :=
      fun j1 j2 k h1 h2 => (mrP j1).2 j2 (m0tr (m0sym h1) _ h2)
    obtain ⟨k0, hk0, h0⟩ := hk i cl_i
    obtain ⟨k1, hk1, h1⟩ := hk a.1.fst (apP1 a)
    obtain ⟨k2, hk2, h2⟩ := hk a.1.snd (apP2 a)
    have ne1 : i ≠ a.1.fst := fun h => a_i (Or.inl h)
    have ne2 : i ≠ a.1.snd := fun h => a_i (Or.inr h)
    have ne3 := a.1.fst_ne_snd
    have : k0 = k1 ∨ k0 = k2 ∨ k1 = k2 := by omega
    rcases this with rfl | rfl | rfl
    · exact ne1 (inj _ _ _ h0 h1)
    · exact ne2 (inj _ _ _ h0 h2)
    · exact ne3 (inj _ _ _ h1 h2)
  choose ar ar_a ar_p using har
  -- Coq `ar0 a := \big[cap_rect/ar0]_(i | i \notin v a) ar i` (here over all `i`).
  let ar0 : Arc → Rectangle := fun a =>
    capRects ((List.finRange Nr).map (ar a)) (sepRect (ap a) (ap a))
  have ar0p : ∀ a, inRectangle (ar0 a) (ap a) := by
    intro a
    refine (mem_capRects _ _ _).2 ⟨mem_sep_rect _ _, ?_⟩
    simp only [List.mem_map, List.mem_finRange, true_and]
    rintro _ ⟨i, rfl⟩
    exact ar_p a i
  have ar0a : ∀ a i, ClA a (ar0 a) i := by
    rintro a i ⟨z, hz, cz⟩
    exact ar_a a i
      ⟨z, ((mem_capRects _ _ _).1 hz).2 _ (List.mem_map_of_mem (List.mem_finRange i)), cz⟩
  have ar1_inj : ∀ a b : Arc,
      Meet (inRectangle (sepRect (ap a) (ap b))) (inRectangle (sepRect (ap b) (ap a))) →
      a = b := by
    intro a b hab
    have e := eq_of_meet_sep_rect hab
    have a_clb : ∀ i, cl i (ap b) → i ∈ a.1 := by
      intro i h
      refine ar0a a i ⟨ap b, ?_, h⟩
      rw [← e]
      exact ar0p a
    have h1 := a_clb _ (apP1 b)
    have h2 := a_clb _ (apP2 b)
    obtain ⟨⟨af, as, al⟩, ha⟩ := a
    obtain ⟨⟨bf, bs, bl⟩, hb⟩ := b
    simp only [AdjIndex.mem_iff] at h1 h2
    have : bf = af ∧ bs = as := by
      simp only [Fin.ext_iff, Fin.lt_def] at h1 h2 al bl ⊢
      omega
    obtain ⟨rfl, rfl⟩ := this
    rfl
  -- Coq `ar a := \big[cap_rect/ar0 a]_b ar1 b a`.
  let ar' : Arc → Rectangle := fun a =>
    capRects ((Finset.univ : Finset Arc).toList.map fun b => sepRect (ap b) (ap a)) (ar0 a)
  have ar'_p : ∀ a, inRectangle (ar' a) (ap a) := by
    intro a
    refine (mem_capRects _ _ _).2 ⟨ar0p a, ?_⟩
    simp only [List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
    rintro _ ⟨b, rfl⟩
    exact mem_sep_rect _ _
  have ar'_a : ∀ a i, ClA a (ar' a) i := by
    rintro a i ⟨z, hz, cz⟩
    exact ar0a a i ⟨z, ((mem_capRects _ _ _).1 hz).1, cz⟩
  have ar1ar : ∀ a b z, inRectangle (ar' a) z → inRectangle (sepRect (ap b) (ap a)) z := by
    intro a b z hz
    refine ((mem_capRects _ _ _).1 hz).2 _ ?_
    exact List.mem_map_of_mem (Finset.mem_toList.2 (Finset.mem_univ b))
  have ar_inj : ∀ a b, Meet (inRectangle (ar' a)) (inRectangle (ar' b)) → a = b := by
    rintro a b ⟨z, ha, hb⟩
    exact ar1_inj a b ⟨z, ar1ar b a z hb, ar1ar a b z ha⟩
  have hab0 : ∀ a, ∃ b : ScaledRect, srectRegion (insetSrect b) (ap a) ∧
      Subregion (srectRegion b) (inRectangle (ar' a)) := fun a => approx_rect (ar'_p a)
  choose ab0 ab0ap ar_ab using hab0
  let r0 : GRect := ⟨1, 0, 1, 0⟩
  have not_r0 : ∀ p, p ∉ r0 := by
    intro p h
    simp only [mem_grect, r0] at h
    omega
  obtain ⟨s_, s, Ds⟩ : ∃ (s_ : Arc → ℕ) (s : ℕ), ∀ a, s = s_ a + (ab0 a).1 :=
    ⟨fun a => ∑ b ∈ Finset.univ.erase a, (ab0 b).1, ∑ a, (ab0 a).1,
      fun a => (Finset.sum_erase_add _ _ (Finset.mem_univ a)).symm⟩
  let abr : Arc → GRect := fun a => refineRect^[s_ a + 1] (ab0 a).2
  have hE : ∀ a, refineSrect (s_ a + 1) (ab0 a) = (s + 1, abr a) := by
    intro a
    refine Prod.ext ?_ rfl
    show s_ a + 1 + (ab0 a).1 = s + 1
    rw [Ds a]
    omega
  have ar_ab' : ∀ a z, srectRegion (s + 1, abr a) z → inRectangle (ar' a) z := by
    intro a z h
    rw [← hE a] at h
    exact ar_ab a z ((in_refine_srect _ _ z).1 h)
  obtain ⟨ab, abE1, abE2⟩ : ∃ ab : AdjBox Nr, (∀ e h, ab e = abr ⟨e, h⟩) ∧
      (∀ e, ¬ MrAdj m0 mr e → ab e = r0) :=
    ⟨fun e => if h : MrAdj m0 mr e then abr ⟨e, h⟩ else r0,
      fun _ h => dite_eq_left_of_eq_true (eq_true h), fun _ h => dite_eq_right_of_eq_false (eq_false h)⟩
  refine ⟨ab, ?_, ⟨s + 1, ?_⟩, ?_⟩
  · intro e f p he hf
    by_cases h1 : MrAdj m0 mr e
    · by_cases h2 : MrAdj m0 mr f
      · rw [abE1 e h1] at he
        rw [abE1 f h2] at hf
        have := ar_inj ⟨e, h1⟩ ⟨f, h2⟩ ⟨scalePoint (s + 1) p,
          ar_ab' _ _ ((mem_approx_scale _ _ _).2 he), ar_ab' _ _ ((mem_approx_scale _ _ _).2 hf)⟩
        exact congrArg Subtype.val this
      · rw [abE2 f h2] at hf
        exact absurd hf (not_r0 p)
    · rw [abE2 e h1] at he
      exact absurd he (not_r0 p)
  · intro e i hpr
    by_cases h : MrAdj m0 mr e
    · rw [abE1 e h] at hpr ⊢
      set a : Arc := ⟨e, h⟩ with ha
      refine ⟨fun e_i => ?_, ?_⟩
      · have cli_a : cl i (ap a) := by
          rcases e_i with rfl | rfl
          · exact apP1 a
          · exact apP2 a
        obtain ⟨p, Dp, a_p⟩ := (in_refine_srect 1 (insetSrect (ab0 a)) (ap a)).2 (ab0ap a)
        obtain ⟨r, r_a, p_r⟩ := rect_approx Dp
        obtain ⟨z, m0iz, r_z⟩ := cli_a (inRectangle r) (open_rectangle r) r_a
        obtain ⟨q, Dq, q_p⟩ := p_r z r_z
        have hz : srectRegion (insetSrect (refineSrect 1 (ab0 a))) z := by
          refine ⟨q, Dq, ?_⟩
          have a_p' : p ∈ refineRect (inset (ab0 a).2) := a_p
          rw [refine_inset] at a_p'
          exact insetP.1 a_p' q (gtouch_l p q q_p)
        have hz' := in_refine_inset (s_ a) hz
        have e2 : refineSrect (s_ a) (refineSrect 1 (ab0 a)) = (s + 1, abr a) := by
          refine Prod.ext ?_ rfl
          show s_ a + (1 + (ab0 a).1) = s + 1
          rw [Ds a]
          omega
        rw [e2] at hz'
        exact ⟨z, hz', m0iz⟩
      · rintro ⟨z, a_z, m0i_z⟩
        exact ar'_a a i ⟨z, ar_ab' a z a_z, mem_closure_of_mem m0i_z⟩
    · rw [abE2 e h] at hpr
      obtain ⟨p, hp⟩ := (gr_properP _).1 hpr
      exact absurd hp (not_r0 p)
  · intro e h
    rw [abE1 e h]
    obtain ⟨p, -, hp⟩ := ab0ap ⟨e, h⟩
    exact (gr_proper_refine _ _).2 ((gr_properP _).2 ⟨p, insetW _ p hp⟩)

end AdjRepr

/-! ### Interpolating mattes -/

section Interpolation

/-- Coq `interpolant_at z U V W`: the region `W` interpolates between `{z} ∪ U` and `V`. -/
def InterpolantAt (z : Point) (U V W : Region) : Prop :=
  W z ∧ Subregion U W ∧ Subregion W V

/-- Coq `smatte_interpolated U V`: the union of all scaled mattes interpolating between `U`
and `V`. -/
def smatteInterpolated (U V : Region) : Region :=
  fun z => ∃ m : ScaledMatte, InterpolantAt z U V (smatteRegion m)

/-- Coq `refine_smatte_interpolant`. -/
theorem refine_smatte_interpolant (s : ℕ) {U V : Region} {m : ScaledMatte} {z : Point}
    (h : InterpolantAt z U V (smatteRegion m)) :
    InterpolantAt z U V (smatteRegion (refineSmatte s m)) := by
  obtain ⟨mz, mU, Vm⟩ := h
  exact ⟨(in_refine_smatte s m z).2 mz, fun t ht => (in_refine_smatte s m t).2 (mU t ht),
    fun t ht => Vm t ((in_refine_smatte s m t).1 ht)⟩

/-- Coq `connected_matte`. -/
theorem connected_matte {U : Region} {m : ScaledMatte} (Uopen : Open U)
    (Uconnected : Connected U) (Um : Subregion (smatteRegion m) U) :
    Subregion U (smatteInterpolated (smatteRegion m) U) := by
  classical
  set U1 := smatteInterpolated (smatteRegion m) U with hU1
  let U2 : Region := fun z => U z ∧ ¬ U1 z
  have U12_U : Subregion U (union U1 U2) := fun z hz => by
    by_cases h : U1 z
    · exact Or.inl h
    · exact Or.inr ⟨hz, h⟩
  have U1_U : Meet U1 U := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ m.2.matte_ne
    have mz : smatteRegion m (scalePoint m.1 p) := (mem_approx_scale _ _ _).2 hp
    exact ⟨_, ⟨m, mz, fun _ h => h, Um⟩, Um _ mz⟩
  have U1open : Open U1 := by
    rintro z ⟨m1, m1z⟩
    have key : ∀ (n : ℕ) (m1 : ScaledMatte) (b : ScaledRect), b.1 = m1.1 →
        srectRegion (insetSrect b) z → Subregion (srectRegion b) U →
        InterpolantAt z (smatteRegion m) U (smatteRegion m1) →
        memApprox m1.1 {p | p ∈ m1.2 ∧ mcorner m1.2 p < n} z →
        ∃ u : Rectangle, inRectangle u z ∧ Subregion (inRectangle u) U1 := by
      intro n
      induction n with
      | zero =>
        rintro m1 b - - - - ⟨p, -, -, hn⟩
        exact absurd hn (Nat.not_lt_zero _)
      | succ n IHn =>
        rintro ⟨s, m1⟩ ⟨sb, b⟩ Db1 b_z Ub ⟨m1z, m1m, Um1⟩ ⟨p, Dp, m1p, m1n_p⟩
        simp only at Db1
        subst Db1
        change ApproxPoint sb z p at Dp
        change p ∈ m1 at m1p
        change mcorner m1 p < n + 1 at m1n_p
        by_cases p_inner : mcorner m1 p = 0
        · obtain ⟨r, r_z, p_r⟩ := rect_approx Dp
          refine ⟨r, r_z, fun t r_t => ⟨(sb, m1), ?_, m1m, Um1⟩⟩
          exact sub_mem_approx sb (fun q hq => mcorner0 m1 p m1p p_inner q hq) t (p_r t r_t)
        · have b_p : p ∈ inset b := by
            obtain ⟨q, Dq, hq⟩ := b_z
            rw [approx_point_inj Dp Dq]
            exact hq
          obtain ⟨p2, Dp2⟩ := approx_point_exists (sb + 1) z
          have Ep2 : halfg p2 = p := approx_point_inj (approx_halfg Dp2) Dp
          have m1p2 : halfg p2 ∈ m1 := Ep2 ▸ m1p
          obtain ⟨m2, ⟨m2m1, bm1m2⟩, ltm⟩ :=
            refine_mcorner m1 b p2 m1p2 (Ep2 ▸ b_p) (by rw [Ep2]; omega)
          rw [Ep2] at ltm
          have m2p2 : p2 ∈ m2 := m2m1 p2 m1p2
          refine IHn (sb + 1, m2) (refineSrect 1 (sb, b)) (Nat.add_comm 1 sb)
            (in_refine_inset 1 b_z) (fun t bt => Ub t ((in_refine_srect 1 _ t).1 bt))
            ⟨⟨p2, Dp2, m2p2⟩, ?_, ?_⟩ ⟨p2, Dp2, m2p2, show mcorner m2 p2 < n by omega⟩
          · intro t ht
            obtain ⟨q, Dq, hq⟩ := (in_refine_smatte 1 (sb, m1) t).2 (m1m t ht)
            refine ⟨q, (Nat.add_comm 1 sb) ▸ Dq, m2m1 q ((in_refine_matte m1 q).1 hq)⟩
          · rintro t ⟨q, Dq, hq⟩
            have Dq' := approx_halfg Dq
            rcases bm1m2 q hq with h | h
            · exact Ub t ⟨halfg q, Dq', h⟩
            · exact Um1 t ⟨halfg q, Dq', h⟩
    obtain ⟨r, r_z, Ur⟩ := Uopen z (m1z.2.2 z m1z.1)
    obtain ⟨b1, b1z, r_b1⟩ := approx_rect r_z
    have hi' := refine_smatte_interpolant b1.1 m1z
    obtain ⟨p, Dp, hp⟩ := hi'.1
    exact key (mcorner (refineSmatte b1.1 m1).2 p + 1) (refineSmatte b1.1 m1)
      (refineSrect m1.1 b1) (Nat.add_comm _ _) (in_refine_inset _ b1z)
      (fun t ht => Ur t (r_b1 t ((in_refine_srect _ _ t).1 ht))) hi'
      ⟨p, Dp, hp, Nat.lt_succ_self _⟩
  have U2open : Open U2 := by
    rintro z ⟨Uz, U1'z⟩
    obtain ⟨r, r_z, Ur⟩ := Uopen z Uz
    obtain ⟨b, b_z, r_b⟩ := approx_rect r_z
    suffices b'U1 : ¬ Meet (srectRegion b) U1 by
      obtain ⟨p, Dp, b_p⟩ := b_z
      obtain ⟨rp, rp_z, p_rp⟩ := rect_approx Dp
      refine ⟨rp, rp_z, fun t rp_t => ?_⟩
      have b_t : srectRegion b t :=
        sub_mem_approx _ (fun q hq => insetP.1 b_p q (gtouch_l p q hq)) t (p_rp t rp_t)
      exact ⟨Ur t (r_b t b_t), fun U1t => b'U1 ⟨t, b_t, U1t⟩⟩
    rintro ⟨t, b_t, m1, m1t⟩
    have key : ∀ (b : ScaledRect) (m1 : ScaledMatte), b.1 = m1.1 → CoarseIn (inGrect b.2) m1.2 →
        Subregion (srectRegion b) (inRectangle r) → srectRegion (insetSrect b) z →
        srectRegion b t → InterpolantAt t (smatteRegion m) U (smatteRegion m1) → False := by
      rintro ⟨s, b⟩ ⟨s', m1⟩ hs b_ref r_b ⟨p, Dp, b_p⟩ ⟨q, Dq, b_q⟩ ⟨m1t, m1m, Um1⟩
      simp only at hs
      subst hs
      have b_m1 : ∃ q ∈ m1, q ∈ b := by
        obtain ⟨q', Dq', hq'⟩ := m1t
        exact ⟨q, (approx_point_inj Dq Dq') ▸ hq', b_q⟩
      obtain ⟨xm, xmP, sxm, xm_p⟩ := coarse_extends_in m1 b b_ref b_m1 p b_p
      refine U1'z ⟨(s, xm), ⟨p, Dp, xm_p⟩, fun u hu => ?_, ?_⟩
      · exact sub_mem_approx s (fun q hq => in_extension m1 xmP q hq) u (m1m u hu)
      · rintro u ⟨q, Dq, hq⟩
        rcases sxm q hq with h | h
        · exact Ur u (r_b u ⟨q, Dq, h⟩)
        · exact Um1 u ⟨q, Dq, h⟩
    have coarse : CoarseIn (inGrect (refineSrect (m1.1 + 1) b).2) (refineSmatte (b.1 + 1) m1).2 := by
      show CoarseIn _ (refineMatte^[b.1 + 1] m1.2)
      rw [iterate_succ_apply']
      exact refine_matte_coarse _ _
    exact key (refineSrect (m1.1 + 1) b) (refineSmatte (b.1 + 1) m1)
      (show m1.1 + 1 + b.1 = b.1 + 1 + m1.1 by omega) coarse
      (fun v hv => r_b v ((in_refine_srect _ _ v).1 hv)) (in_refine_inset _ b_z)
      ((in_refine_srect _ _ t).2 b_t) (refine_smatte_interpolant _ m1t)
  intro z Uz
  rcases U12_U z Uz with h | h
  · exact h
  · obtain ⟨t, U1t, -, U1't⟩ := Uconnected U1 U2 U1open U2open U12_U U1_U ⟨z, h, Uz⟩
    exact absurd U1t U1't

end Interpolation

/-! ### Discretized mattes -/

section DiscrMatte

variable {Nr : ℕ}

/-- Coq `proper_smatte m i E`: the scaled matte `m` is included in the region of `m0`
containing `mr i`, and meets `insetSrect (ab e)` for all the `e` in `E` such that `ab e`
witnesses an adjacency. -/
def ProperSmatte (m0 : Map) (mr : MapRepr Nr) (ab : AdjIndex Nr → ScaledRect) (m : ScaledMatte)
    (i : Fin Nr) (E : AdjIndex Nr → Prop) : Prop :=
  Subregion (smatteRegion m) (m0 (mr i)) ∧
    ∀ e, E e → GrProper (ab e).2 → Meet (smatteRegion m) (srectRegion (insetSrect (ab e)))

/-- Coq `refine_smatte_proper`. -/
theorem refine_smatte_proper {m0 : Map} {mr : MapRepr Nr} {ab : AdjIndex Nr → ScaledRect}
    (s : ℕ) {m : ScaledMatte} {i : Fin Nr} {E : AdjIndex Nr → Prop}
    (h : ProperSmatte m0 mr ab m i E) : ProperSmatte m0 mr ab (refineSmatte s m) i E := by
  obtain ⟨ri_m, rm_ab⟩ := h
  refine ⟨fun z hz => ri_m z ((in_refine_smatte s m z).1 hz), fun e Ee he => ?_⟩
  obtain ⟨z, m_z, ab_z⟩ := rm_ab e Ee he
  exact ⟨z, (in_refine_smatte s m z).2 m_z, ab_z⟩

/-- Coq `exists_smatte`. -/
theorem exists_smatte {m0 : Map} (fin_m0 : FiniteSimpleMap m0) {mr : MapRepr Nr}
    (mrP : MrProper m0 mr) {ab : AdjIndex Nr → ScaledRect}
    (abP : ∀ e i, AbMrProper m0 mr (ab e) e i) :
    ∃ s, ∃ cm : Fin Nr → Matte, ∀ i, ProperSmatte m0 mr ab (s, cm i) i (fun e => i ∈ e) := by
  classical
  have hE : ∀ i (L : List (AdjIndex Nr)), (∀ e ∈ L, i ∈ e) →
      ∃ m, ProperSmatte m0 mr ab m i (· ∈ L) := by
    intro i L
    induction L with
    | nil =>
      intro _
      obtain ⟨r, r_i, m0i_r⟩ := fin_m0.simple_map_open (mr i) (mr i) (mrP i).1
      obtain ⟨⟨s, b⟩, ⟨p, p_i, b_p⟩, r_b⟩ := approx_rect r_i
      refine ⟨(s, pointMatte p), fun z ⟨q, Dq, hq⟩ => ?_, fun e he => absurd he List.not_mem_nil⟩
      have : q = p := List.mem_singleton.1 hq
      subst this
      exact m0i_r z (r_b z ⟨q, Dq, insetW _ q b_p⟩)
    | cons e L IH =>
      intro hL
      obtain ⟨m, m_i, m_E⟩ := IH (fun f hf => hL f (List.mem_cons_of_mem _ hf))
      by_cases ab_e : GrProper (ab e).2
      · obtain ⟨z, e_z, m0i_z⟩ := (abP e i ab_e).1 (hL e List.mem_cons_self)
        obtain ⟨m1, m1z, m1m, m0im1⟩ := connected_matte (fin_m0.simple_map_open _)
          (fin_m0.simple_map_connected _) m_i z m0i_z
        refine ⟨m1, m0im1, fun f hf hfp => ?_⟩
        rcases List.mem_cons.1 hf with rfl | hf
        · exact ⟨z, m1z, e_z⟩
        · obtain ⟨t, mt, abt⟩ := m_E f hf hfp
          exact ⟨t, m1m t mt, abt⟩
      · refine ⟨m, m_i, fun f hf hfp => ?_⟩
        rcases List.mem_cons.1 hf with rfl | hf
        · exact absurd hfp ab_e
        · exact m_E f hf hfp
  have hm : ∀ i, ∃ m, ProperSmatte m0 mr ab m i (fun e => i ∈ e) := by
    intro i
    obtain ⟨m, mP⟩ := hE i ((Finset.univ.filter fun e => i ∈ e).toList)
      (fun e he => by simpa using he)
    exact ⟨m, mP.1, fun e he => mP.2 e (by simpa using he)⟩
  choose m mP using hm
  obtain ⟨s_, s, Ds⟩ : ∃ (s_ : Fin Nr → ℕ) (s : ℕ), ∀ i, s = s_ i + (m i).1 :=
    ⟨fun i => ∑ j ∈ Finset.univ.erase i, (m j).1, ∑ i, (m i).1,
      fun i => (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm⟩
  refine ⟨s, fun i => (refineSmatte (s_ i) (m i)).2, fun i => ?_⟩
  have e : ((s, (refineSmatte (s_ i) (m i)).2) : ScaledMatte) = refineSmatte (s_ i) (m i) :=
    Prod.ext (Ds i) rfl
  rw [e]
  exact refine_smatte_proper _ (mP i)

end DiscrMatte

/-! ### The discretization theorem -/

/-- The main step of Coq's `discretize_to_hypermap`, after its `without loss Ds1 : ... / s1 = s`
reduction: the adjacency boxes and the mattes have the same scale `s`. -/
private theorem discretize_core {m0 : Map} (fin_m0 : FiniteSimpleMap m0) {Nr : ℕ}
    {mr : MapRepr Nr} (mrP : MrProper m0 mr) (mr_m0 : Subregion (cover m0) (mrCover m0 mr))
    {ab : AdjBox Nr} (abP : AbProper ab) (s : ℕ)
    (ab_mrP : ∀ e i, AbMrProper m0 mr (s, ab e) e i)
    (ab_m0 : ∀ e, MrAdj m0 mr e → GrProper (ab e)) {cm : CMatte Nr}
    (cmP : ∀ i, ProperSmatte m0 mr (fun e => (s, ab e)) (s, cm i) i (fun e => i ∈ e)) :
    ∃ (D : Type) (_ : Fintype D) (_ : DecidableEq D) (G : Hypermap D),
      G.PlanarBridgeless ∧ (G.FourColorable → ColorableWith 4 m0) := by
  classical
  have m0sym : ∀ {z1 z2}, m0 z1 z2 → m0 z2 z1 := fin_m0.map_sym
  have m0tr : ∀ {z1 z2}, m0 z1 z2 → Subregion (m0 z2) (m0 z1) := fin_m0.map_trans
  have m0tr_cl : ∀ {z t}, m0 z t → Subregion (closure (m0 t)) (closure (m0 z)) := by
    intro z t m0zt u t_u U openU hU
    obtain ⟨v, m0tv, Uv⟩ := t_u U openU hU
    exact ⟨v, m0tr m0zt v m0tv, Uv⟩
  have ab_cmP : ∀ e i, AbCmProper ab cm e i := by
    intro e i ab_e
    obtain ⟨m0i_cm, e_cmi⟩ := cmP i
    refine ⟨fun hi => ?_, fun ⟨p, cmi_p, ab_p⟩ => ?_⟩
    · obtain ⟨z, ⟨p, Dp, cm_p⟩, ⟨q, Dq, ab_q⟩⟩ := e_cmi e hi ab_e
      exact ⟨p, cm_p, (approx_point_inj Dp Dq) ▸ ab_q⟩
    · exact (ab_mrP e i ab_e).2 ⟨scalePoint s p, (mem_approx_scale _ _ _).2 ab_p,
        m0i_cm _ ((mem_approx_scale _ _ _).2 cmi_p)⟩
  have cmP' : CmProper cm := by
    rintro i j ⟨p, cmj_p, cmi_p⟩
    refine (mrP i).2 j ?_
    have hi : m0 (mr i) (scalePoint s p) := (cmP i).1 _ ((mem_approx_scale _ _ _).2 cmi_p)
    have hj : m0 (mr j) (scalePoint s p) := (cmP j).1 _ ((mem_approx_scale _ _ _).2 cmj_p)
    exact m0tr hi _ (m0sym hj)
  obtain ⟨D, iF, iD, G, hG, hcol⟩ := exists_grid_map abP cmP' ab_cmP
  refine ⟨D, iF, iD, G, hG, fun h4 => ?_⟩
  obtain ⟨k0, ab_k0'⟩ := hcol h4
  let k : Map := fun z t => ∃ i, m0 (mr i) z ∧ ∃ j, m0 (mr j) t ∧ k0 i = k0 j
  have mr_inj : ∀ {z t i j}, m0 z t → m0 (mr i) z → m0 (mr j) t → i = j :=
    fun {_ _ i j} m0zt m0iz m0jt => (mrP i).2 j (m0tr (m0tr m0iz _ m0zt) _ (m0sym m0jt))
  have m0cover : ∀ {z t}, m0 z t → cover m0 z := fun h => m0tr h _ (m0sym h)
  have key : ∀ z t i j, m0 (mr i) z → m0 (mr j) t → Adjacent m0 z t → i < j → k0 i ≠ k0 j := by
    intro z t i j m0iz m0jt adj ltij
    obtain ⟨m0'zt, u, cu, clz, clt⟩ := adj
    refine ab_k0' ⟨i, j, ltij⟩ (ab_m0 _ ⟨⟨fun m0ij => m0'zt ?_, u, cu,
      m0tr_cl m0iz u clz, m0tr_cl m0jt u clt⟩, ltij⟩)
    exact m0tr (m0sym m0iz) _ (m0tr m0ij _ m0jt)
  have hf : ∀ c : ℕ, ∃ z : Point, (∃ i, (k0 i : ℕ) = c) → ∃ j, (k0 j : ℕ) = c ∧ z = mr j := by
    intro c
    by_cases h : ∃ i, (k0 i : ℕ) = c
    · obtain ⟨j, hj⟩ := h
      exact ⟨mr j, fun _ => ⟨j, hj, rfl⟩⟩
    · exact ⟨⟨0, 0⟩, fun h' => absurd h' h⟩
  choose f hf using hf
  refine ⟨k, ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩, f, ?_⟩
  · rintro z t ⟨i, m0iz, j, m0jt, kij⟩
    exact ⟨j, m0jt, i, m0iz, kij.symm⟩
  · rintro z t ⟨i, m0iz, j, m0jt, kij⟩ t1 ⟨i1, m0i1t, j1, m0jt1, kj1⟩
    exact ⟨i, m0iz, j1, m0jt1, by rw [kij, mr_inj (m0cover (m0sym m0jt)) m0jt m0i1t, kj1]⟩
  · rintro z ⟨i, m0iz, -⟩
    exact m0cover (m0sym m0iz)
  · intro z t m0zt
    obtain ⟨i, m0iz⟩ := mr_m0 z (m0cover m0zt)
    exact ⟨i, m0iz, i, m0tr m0iz _ m0zt, rfl⟩
  · rintro z t adj ⟨i, m0iz, j, m0jt, kij⟩
    rcases lt_trichotomy i j with h | rfl | h
    · exact key z t i j m0iz m0jt adj h kij
    · exact adj.1 (m0tr (m0sym m0iz) _ m0jt)
    · obtain ⟨n, u, cu, c1, c2⟩ := adj
      exact key t z j i m0jt m0iz ⟨fun h' => n (m0sym h'), u, cu, c2, c1⟩ h kij.symm
  · rintro z ⟨i, m0iz, -⟩
    obtain ⟨j, kj, fj⟩ := hf _ ⟨i, rfl⟩
    refine ⟨k0 i, (k0 i).isLt, ?_⟩
    rw [fj]
    exact ⟨j, (mrP j).1, i, m0iz, Fin.ext kj⟩

/-- Coq `discretize_to_hypermap`: a finite simple map `m0` is four colorable if some planar
bridgeless hypermap is (Coq: `exists2 G, planar_bridgeless G & four_colorable G ->
colorable_with 4 m0`, with `G : hypermap` bundling its finite type of darts). -/
theorem discretize_to_hypermap {m0 : Map} (fin_m0 : FiniteSimpleMap m0) :
    ∃ (D : Type) (_ : Fintype D) (_ : DecidableEq D) (G : Hypermap D),
      G.PlanarBridgeless ∧ (G.FourColorable → ColorableWith 4 m0) := by
  obtain ⟨Nr, mr, mrP, mr_m0⟩ := exists_map_repr fin_m0
  obtain ⟨ab, abP, ⟨s, ab_mrP⟩, ab_m0⟩ := exists_adjbox fin_m0 mrP
  obtain ⟨s1, cm, cmP⟩ := exists_smatte fin_m0 mrP ab_mrP
  -- Coq `without loss Ds1 : s s1 ab cm abP ab_mrP ab_m0 cmP / s1 = s`.
  let s2 := s + s1
  let ab2 : AdjBox Nr := fun e => (refineSrect s1 (s, ab e)).2
  let cm2 : CMatte Nr := fun i => (refineSmatte s (s1, cm i)).2
  have e2 : ∀ e, refineSrect s1 (s, ab e) = (s2, ab2 e) := fun e => Prod.ext (Nat.add_comm _ _) rfl
  refine discretize_core fin_m0 mrP mr_m0 (ab := ab2) (cm := cm2) ?_ s2 ?_ ?_ ?_
  · intro e f p he hf
    exact abP e f (halfg^[s1] p) ((mem_iterate_refineRect _ _ _).1 he)
      ((mem_iterate_refineRect _ _ _).1 hf)
  · intro e i
    rw [← e2]
    exact ab_mr_proper_refine s1 (ab_mrP e i)
  · intro e h
    exact (gr_proper_refine _ _).2 (ab_m0 e h)
  · intro i
    obtain ⟨m0i_cm, cmi_ab⟩ := refine_smatte_proper (ab := fun e => (s, ab e)) s (cmP i)
    refine ⟨m0i_cm, fun e he hpr => ?_⟩
    obtain ⟨z, mi_z, ab_z⟩ := cmi_ab e he ((gr_proper_refine _ _).1 hpr)
    refine ⟨z, mi_z, ?_⟩
    have := in_refine_inset s1 ab_z
    rwa [e2] at this

end FourColor.RealPlane
