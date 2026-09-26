/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Snip
import FourColor.Matte

/-!
# The hypermap of a set of mattes  (port of `gridmap.v`)

The construction of a hypermap, from a finite set of disjoint mattes and a set of adjacency
boxes. These sets are simply represented by functions on the index type `Fin Nr`. The
construction starts by extending the mattes so that mattes that meet a common adjacency box
share a contour edge. Then we compute a bounding box for the mattes, and create a plain planar
connected hypermap by framing the bounding box. The matte rings then map to simple rings of
this map, with disjoint disks, so we can use the "snip" operation to turn them into node rings
(we need to operate in the dual map to make this work), by removing their interiors. Dualizing
the resulting hypermap gives us a map whose coloring solves the initial coloring problem.

All definitions here depend on the number `Nr` of matte regions; the matte index type is
`Fin Nr` (Coq `Ir := 'I_Nr`).

* `AdjIndex Nr`    : the adjacency index type, which consists of ordered pairs of matte
  indices `e.fst < e.snd` (Coq `adj_index`); `AdjIndex.mk i j ltij` is Coq's `AdjIndex i j ltij`,
  and `i ∈ e` means that `i` is one of the components of `e` (Coq `adj_incident`).
* `CMatte Nr`      : `Fin Nr → Matte`, the type for a set of `Nr` mattes (Coq `cmatte`).
* `AdjBox Nr`      : `AdjIndex Nr → GRect`, the type for a collection of adjacency boxes, i.e.,
  grid rectangles isolating matte adjacencies (Coq `adjbox`). Non-adjacency is represented by
  empty rectangles.
* `CmProper cm`    : the mattes in `cm` are pairwise disjoint (Coq `cm_proper`).
* `AbProper ab`    : the rectangles in `ab` are pairwise disjoint (Coq `ab_proper`).
* `AbCmProper ab cm e i` : if `ab` witnesses adjacency at `e`, then `cm i` meets the inside of
  `ab e` (specifically, `inset (ab e)`) if `i` is a component of `e` and is disjoint from
  `ab e` otherwise (Coq `ab_cm_proper`).
* `gridMapOf ab0P cm0P abcm0P` : a planar bridgeless hypermap that is four colorable only if a
  map with `Nr` regions and adjacencies described by `ab0` is (Coq `grid_map`).

The construction uses the following intermediate definitions:

* `cmExtend ab0P cm0P abcm0P` : a set of pairwise disjoint mattes that extend the `cm0` set to
  realize the `ab0` adjacencies as (`Madj`) matte adjacencies (Coq section `Let cm`).
* `cmBbox cm`      : a grid rectangle containing all the mattes of `cm` (Coq `cm_bbox`).
* `gmgrid bb`      : a list of all the grid darts in the `gedge` closure of the refined
  rectangle `bb` (Coq `gmgrid`).
* `GmDart bb`      : the (finite) subtype with extent `gmgrid bb`, which coerces to `GPoint`
  (Coq `gmdart`).
* `gmpick u s`     : some `GmDart` whose `GPoint` projection occurs in `s`, defaulting to `u`
  if `s` and `gmgrid` are disjoint (Coq `gmpick`).
* `gmdartMap bb`   : a hypermap with dart type `GmDart bb` (Coq `gmdart_map`), with
  permutations `gmEdge`, `gmNode`, `gmFace` (Coq `gmedge`, `gmnode`, `gmface`).
* `GmCutout cm E`  : the type of planar hypermaps that are the remainder left by removing from
  `gmdartMap (cmBbox cm)` (using `snip`) the interior of all mattes `cm i` for `i ∈ E`,
  alongside their embedding in `GmDart` and the border rings of the removed mattes, and the
  proof that this data satisfies the properties of a remainder map (Coq `gm_cutout`).

We construct an instance of `GmCutout cm Finset.univ` (`has_cutout`), and finally obtain
`gridMapOf` as the hypermap dual of its encapsulated hypermap.

## Coq → Lean names

| Coq | Lean |
|---|---|
| `adj_index`, `AdjIndex`, `pair_of_adj_index`, `adj_incident` | `AdjIndex`, `AdjIndex.mk`, `AdjIndex.pair`, `i ∈ e` |
| `adjbox`, `cmatte` | `AdjBox`, `CMatte` |
| `cm_proper`, `ab_proper`, `ab_cm_proper` | `CmProper`, `AbProper`, `AbCmProper` |
| `cm_extend_adj` | `cm_extend_adj` |
| section `Let cm`, `cmP`, `ab_cmP` | `cmExtend`, `cmExtend_proper`, `cmExtend_adj` |
| `cm_bbox`, `sub_cm_bbox`, `cm_bboxE` | `cmBbox`, `sub_cm_bbox`, `cm_bboxE` |
| `gmgrid`, `gmgridE`, `gmgrid_edge` | same names |
| `gmdart`, `gmval`, `Gmdart` | `GmDart`, `Subtype.val`, `Subtype.mk` |
| `gmedge`, `gmpick`, `gmface`, `gmnode` | `gmEdge`, `gmpick`, `gmFace`, `gmNode` |
| `gmedge2`, `gmedgeK`, `gmdart_map`, `gmdart_plain` | `gmedge2`, `gmedgeK`, `gmdartMap`, `gmdart_plain` |
| `gm_inner`, `val_gmnode`, `gm_inner_node`, `gm_inner_closed` | `gmInner`, same names |
| `card_gmdart`, `cface_end0g`, `fcard_gmface`, `fcard_gmnode` | same names |
| `gmdart_connected`, `gmdart_planar` | same names |
| `gmring`, `val_gmring`, `gm_disk_def`, `disjoint_gmdisk`, `gmring_cycle` | same names |
| `gm_cutout`, `GmCutout` | `GmCutout` (a structure) |
| `has_cutout` | `has_cutout` (`Nonempty`), `gmCutout` (the chosen instance) |
| `grid_map`, `planar_bridgeless_grid_map`, `grid_map_coloring` | `gridMapOf` (dart type `gridMapOfDart`), same names |

Lean-only additions: `AdjIndex.equiv`, `AdjIndex.mem_iff`, `AdjIndex.fst_ne_snd`, `grect0`
(Coq section `Let`), `grProper_iff`, `cmBbox_proper`, `grectE` (`cm_bboxE` for any proper
rectangle), `gmInsubd` (Coq `insubd` on `gmdart`), `val_gmEdge`, `val_gmFace`, `val_gmNode`,
`gmdartMap_edge`/`_node`/`_face`, `halfg_edge_node`, `gedge_gnode`, `halfg_gmnode`,
`mem_gmgrid_of_mring`, `mem_gmring`, `GmCutout.loopless` and `GmCutout.colorable` (the main
steps of `planar_bridgeless_grid_map` and `grid_map_coloring`), `colorIndex`,
`colorIndex_injective`, and `exists_grid_map` (`gridMapOf` packaged as an existential over a
dart type, the form `discretize_to_hypermap` needs).

## Porting notes

* The grid part of the construction (`gmgrid` to `gmdart_planar`) only depends on the bounding
  box, so it is stated for an arbitrary rectangle `bb : GRect` (Coq uses the section's
  `cm_bbox`), with the hypothesis `GrProper bb` where the Coq proof uses `cm_bboxE`'s positivity
  facts; `cmBbox cm` is always proper (`cm_bboxE`). Likewise, `cmBbox`, `gmring`, `GmCutout` and
  `has_cutout` take the set of mattes `cm` as an argument (Coq uses the section's `Let cm`), with
  the hypothesis `CmProper cm` where the Coq proof uses `cmP`. The section `Let cm` itself is
  `cmExtend ab0P cm0P abcm0P`, chosen from `cm_extend_adj` (an existential here).
* `gm_cutout` is a `Type`-valued inductive in Coq (with a bundled hypermap); here `GmCutout` is
  a structure with a field `D : Type` for the dart type (with its `Fintype`, `DecidableEq`
  instances) and `G : Hypermap D`; `has_cutout` states `Nonempty (GmCutout cm Finset.univ)`,
  and `gmCutout` picks an instance with `Classical.choice`. `E : pred Ir` becomes a `Finset`.
* `gridMapOf ab0P cm0P abcm0P` is a hypermap on the dart type `gridMapOfDart ab0P cm0P abcm0P`
  (an `abbrev`, so that its `Fintype` and `DecidableEq` instances are found). The fields of
  `GmCutout` are named (`planar`, `inj`, `edge_morph`, `cface_mono`, `node_morph`, `map_ring`,
  `ucycle_node`); Coq's constructor arguments are anonymous.
* `{morph h : x / edge x}` is `∀ x, h (edge x) = edge (h x)`; `{mono h : x y / cface x y}` is
  `∀ x y, cface (h x) (h y) ↔ cface x y`; `ufcycle node` is `UCycle (frel node)`.
* `grid_map_coloring` returns a coloring `k : Fin Nr → Fin 4` as in Coq (Coq's `'I_4`); the
  color of `i` is `colorIndex` of the color of any dart of the ring `r i` (Coq uses the
  `index` of the color in `[:: Color0; Color1; Color2]`, an equivalent injection).
* The proofs of `card_gmdart`, `fcard_gmface`, `fcard_gmnode` and `gmdart_connected` are
  restructured: they work with explicit coordinates (`omega`) rather than with Coq's
  `cm_bboxE` presentation of the box, and `fcard_gmface` counts the face orbits through the
  image of `end0g` instead of an adjunction. `gmdart_planar` only uses the lower bound
  `fcard_gmnode`, as in Coq.
-/

namespace FourColor

open Function GPoint Hypermap

/-! ### Matte and adjacency indices -/

section Indices

variable (Nr : ℕ)

/-- Coq `adj_index`: the ordered pairs `(i, j)` of matte indices with `i < j`. The Coq
constructor `AdjIndex i j ltij` is `AdjIndex.mk i j ltij`. -/
structure AdjIndex where
  /-- The first component (Coq `e.1`). -/
  fst : Fin Nr
  /-- The second component (Coq `e.2`). -/
  snd : Fin Nr
  /-- The components are ordered (Coq `valP e`). -/
  lt : fst < snd
  deriving DecidableEq

variable {Nr}

/-- `AdjIndex Nr` is the subtype `{ij : Fin Nr × Fin Nr // ij.1 < ij.2}` of Coq. -/
def AdjIndex.equiv : AdjIndex Nr ≃ {ij : Fin Nr × Fin Nr // ij.1 < ij.2} where
  toFun e := ⟨(e.fst, e.snd), e.lt⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite type instance of Coq's `adj_index`. -/
instance : Fintype (AdjIndex Nr) := Fintype.ofEquiv _ AdjIndex.equiv.symm

/-- Coq coercion `pair_of_adj_index`. -/
def AdjIndex.pair (e : AdjIndex Nr) : Fin Nr × Fin Nr := (e.fst, e.snd)

/-- Coq coercion `adj_incident e := pred2 e.1 e.2`: `i ∈ e` means that `i` is a component
of `e`. -/
instance : Membership (Fin Nr) (AdjIndex Nr) := ⟨fun e i => i = e.fst ∨ i = e.snd⟩

/-- Membership in an adjacency index, explicitly. -/
theorem AdjIndex.mem_iff {e : AdjIndex Nr} {i : Fin Nr} : i ∈ e ↔ i = e.fst ∨ i = e.snd :=
  Iff.rfl

instance (e : AdjIndex Nr) (i : Fin Nr) : Decidable (i ∈ e) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The components of an adjacency index are distinct. -/
theorem AdjIndex.fst_ne_snd (e : AdjIndex Nr) : e.fst ≠ e.snd := ne_of_lt e.lt

variable (Nr)

/-- Coq `adjbox`: a collection of adjacency boxes. -/
abbrev AdjBox : Type := AdjIndex Nr → GRect

/-- Coq `cmatte`: a set of `Nr` mattes. -/
abbrev CMatte : Type := Fin Nr → Matte

variable {Nr}

/-- Coq `cm_proper cm`: the mattes in `cm` are pairwise disjoint. -/
def CmProper (cm : CMatte Nr) : Prop := ∀ i j, (∃ p ∈ cm j, p ∈ cm i) → i = j

/-- Coq `ab_proper ab`: the rectangles in `ab` are pairwise disjoint. -/
def AbProper (ab : AdjBox Nr) : Prop := ∀ e f p, p ∈ ab e → p ∈ ab f → e = f

/-- Coq `ab_cm_proper ab cm e i`: if `ab` witnesses adjacency at `e`, then `cm i` meets
`inset (ab e)` if `i` is a component of `e`, and is disjoint from `ab e` otherwise. -/
def AbCmProper (ab : AdjBox Nr) (cm : CMatte Nr) (e : AdjIndex Nr) (i : Fin Nr) : Prop :=
  GrProper (ab e) → (i ∈ e → ∃ p ∈ cm i, p ∈ inset (ab e)) ∧ ((∃ p ∈ cm i, p ∈ ab e) → i ∈ e)

end Indices

/-! ### Extending the mattes to realize the adjacencies -/

section ExtendAdj

variable {Nr : ℕ} {ab0 : AdjBox Nr} {cm0 : CMatte Nr}

/-- Coq `cm_extend_adj`: the mattes `cm0` can be extended to pairwise disjoint mattes that are
adjacent (`Madj`) whenever `ab0` witnesses an adjacency. -/
theorem cm_extend_adj (ab0P : AbProper ab0) (cm0P : CmProper cm0)
    (abcm0P : ∀ e i, AbCmProper ab0 cm0 e i) :
    ∃ cm : CMatte Nr, CmProper cm ∧ ∀ e, GrProper (ab0 e) → Madj (cm e.fst) (cm e.snd) := by
  classical
  let ab : AdjBox Nr := fun e => refineRect (ab0 e)
  have abP : AbProper ab := fun e f p he hf =>
    ab0P e f (halfg p) ((in_refine_rect _ _).1 he) ((in_refine_rect _ _).1 hf)
  have ab0_adj : ∀ e, GrProper (ab0 e) ↔ GrProper (ab e) := fun e =>
    (gr_proper_refine 1 (ab0 e)).symm
  let apart : CMatte Nr → AdjIndex Nr → Prop := fun cm e =>
    GrProper (ab e) ∧ ¬ Madj (cm e.fst) (cm e.snd)
  let Inv : CMatte Nr → Prop := fun cm => ∀ e i, apart cm e →
    (i ∈ e → CoarseIn (ab e : GRegion) (cm i) ∧ ∃ p ∈ cm i, p ∈ inset (ab e)) ∧
      ((∃ p ∈ cm i, p ∈ ab e) → i ∈ e)
  suffices key : ∀ n, ∀ cm : CMatte Nr, (Finset.univ.filter (apart cm)).card < n → Inv cm →
      CmProper cm → ∃ cm : CMatte Nr, CmProper cm ∧
        ∀ e, GrProper (ab0 e) → Madj (cm e.fst) (cm e.snd) by
    refine key _ (fun i => refineMatte (cm0 i)) (Nat.lt_succ_self _) ?_ ?_
    · intro e i hap
      obtain ⟨b_m, e_i⟩ := abcm0P e i ((ab0_adj e).2 hap.1)
      refine ⟨fun hi => ⟨refine_matte_coarse _ _, ?_⟩, ?_⟩
      · obtain ⟨p, mp, bp⟩ := b_m hi
        refine ⟨2 • p, (in_refine_matte _ _).2 (by rwa [halfg_double]), ?_⟩
        have h1 : 2 • p ∈ refineRect (inset (ab0 e)) := by
          rw [in_refine_rect, halfg_double]; exact bp
        rw [refine_inset] at h1
        exact insetW _ _ h1
      · rintro ⟨p, mp, bp⟩
        exact e_i ⟨halfg p, (in_refine_matte _ _).1 mp, (in_refine_rect _ _).1 bp⟩
    · rintro i j ⟨p, mjp, mip⟩
      exact cm0P i j ⟨halfg p, (in_refine_matte _ _).1 mjp, (in_refine_matte _ _).1 mip⟩
  intro n
  induction n with
  | zero => intro cm h; omega
  | succ n IHn =>
    intro cm hle abcmP cmP
    by_cases hall : ∀ e, ¬ apart cm e
    · exact ⟨cm, cmP, fun e he => by_contra fun hm => hall e ⟨(ab0_adj e).1 he, hm⟩⟩
    push Not at hall
    obtain ⟨e, cm'e⟩ := hall
    have e1'2 := e.fst_ne_snd
    obtain ⟨cme_ab, ab_e⟩ : (∀ i, i ∈ e →
        CoarseIn (ab e : GRegion) (cm i) ∧ ∃ p ∈ cm i, p ∈ inset (ab e)) ∧
        ∀ i, (∃ p ∈ cm i, p ∈ ab e) → i ∈ e :=
      ⟨fun i => (abcmP e i cm'e).1, fun i => (abcmP e i cm'e).2⟩
    have cm1ab : ∃ p ∈ cm e.fst, p ∈ inset (ab e) := (cme_ab e.fst (Or.inl rfl)).2
    have cm2ref : CoarseIn (ab e : GRegion) (cm e.snd) := (cme_ab e.snd (Or.inr rfl)).1
    have cm2ab : ∃ p ∈ cm e.snd, p ∈ ab e := by
      obtain ⟨p, hp, hb⟩ := (cme_ab e.snd (Or.inr rfl)).2
      exact ⟨p, hp, insetW _ _ hb⟩
    have cm2'1 : ¬ ∃ q ∈ cm e.fst, q ∈ cm e.snd := fun h => e1'2 (cmP _ _ h).symm
    obtain ⟨cm2, ⟨cm2cm, ab_cm2⟩, cm12⟩ :=
      extend_madj (cm e.snd) (cm e.fst) (ab e) cm2ref cm2ab cm1ab cm2'1
    let xcm : CMatte Nr := Function.update cm e.snd cm2
    have xcm2 : xcm e.snd = cm2 := Function.update_self _ _ _
    have xcmo : ∀ i, i ≠ e.snd → xcm i = cm i := fun i hi => Function.update_of_ne hi _ _
    have xcm_e : ¬ apart xcm e := by
      rintro ⟨_, h⟩
      rw [xcm2, xcmo _ e1'2] at h
      exact h cm12
    have has'cm2 : ∀ i, i ≠ e.snd → ¬ ∃ p ∈ cm i, p ∈ cm2 := by
      rintro i e2'i ⟨p, mip, m2p⟩
      obtain ⟨m1'p, hp⟩ := ab_cm2 p m2p
      by_cases e1i : i = e.fst
      · subst e1i; exact m1'p mip
      · have ab'i : ¬ ∃ p ∈ cm i, p ∈ ab e := fun h => by
          rcases ab_e i h with h | h
          · exact e1i h
          · exact e2'i h
        have cm2'i : ¬ ∃ p ∈ cm i, p ∈ cm e.snd := fun ⟨q, hq1, hq2⟩ =>
          e2'i (cmP i e.snd ⟨q, hq2, hq1⟩)
        rcases hp with hp | hp
        · exact ab'i ⟨p, mip, hp⟩
        · exact cm2'i ⟨p, mip, hp⟩
    have madj_cm2 : ∀ i, i ≠ e.snd → Madj (cm i) (cm e.snd) → Madj (cm i) cm2 := by
      rintro i e2'i ⟨d, r2d, rid⟩
      refine ⟨d, ?_, rid⟩
      rw [(cm e.snd).in_mring, mem_gborder] at r2d
      rw [(cm i).in_mring, mem_gborder] at rid
      rw [cm2.in_mring, mem_gborder, gedge2] at *
      exact ⟨cm2cm _ r2d.1, fun h => has'cm2 i e2'i ⟨_, rid.1, h⟩⟩
    have xcm'cm' : ∀ f, apart xcm f → apart cm f := by
      rintro f ⟨hf, hm⟩
      refine ⟨hf, fun h => hm ?_⟩
      by_cases h1 : f.fst = e.snd
      · have h2 : f.snd ≠ e.snd := fun h2 => f.fst_ne_snd (h1.trans h2.symm)
        rw [h1, xcm2, xcmo _ h2]
        rw [h1] at h
        exact madj_sym.1 (madj_cm2 _ h2 (madj_sym.1 h))
      · rw [xcmo _ h1]
        by_cases h2 : f.snd = e.snd
        · rw [h2, xcm2]
          rw [h2] at h
          exact madj_cm2 _ h1 h
        · rw [xcmo _ h2]; exact h
    have xcmP : CmProper xcm := by
      rintro i j ⟨p, hj, hi⟩
      by_cases hie : i = e.snd <;> by_cases hje : j = e.snd
      · exact hie.trans hje.symm
      · subst hie
        rw [xcm2] at hi
        rw [xcmo _ hje] at hj
        exact absurd ⟨p, hj, hi⟩ (has'cm2 j hje)
      · subst hje
        rw [xcm2] at hj
        rw [xcmo _ hie] at hi
        exact absurd ⟨p, hi, hj⟩ (has'cm2 i hie)
      · rw [xcmo _ hie] at hi
        rw [xcmo _ hje] at hj
        exact cmP i j ⟨p, hj, hi⟩
    refine IHn xcm ?_ ?_ xcmP
    · refine lt_of_lt_of_le (Finset.card_lt_card ?_) (Nat.lt_succ_iff.1 hle)
      rw [Finset.ssubset_iff_of_subset]
      · exact ⟨e, Finset.mem_filter.2 ⟨Finset.mem_univ _, cm'e⟩,
          fun h => xcm_e (Finset.mem_filter.1 h).2⟩
      · intro f hf
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _, xcm'cm' f (Finset.mem_filter.1 hf).2⟩
    · intro f i xcm'f
      have bf'e : ∀ p, p ∈ ab e → p ∉ ab f := fun p he hf => by
        have := abP e f p he hf
        subst this
        exact xcm_e xcm'f
      obtain ⟨e2bf, bf_f⟩ := abcmP f i (xcm'cm' f xcm'f)
      by_cases hie : i = e.snd
      · subst hie
        rw [xcm2]
        refine ⟨fun hi => ?_, ?_⟩
        · obtain ⟨cm2ref_bf, cm2_bf⟩ := e2bf hi
          refine ⟨?_, ?_⟩
          · have IHpq : ∀ p q, p ∈ ab f → halfg q = halfg p → p ∈ cm2 → q ∈ cm2 := by
              intro p q bf_p Dpq cm2p
              rcases (ab_cm2 p cm2p).2 with h | h
              · exact absurd bf_p (bf'e p h)
              · exact cm2cm _ ((cm2ref_bf p q bf_p Dpq).2 h)
            intro p q bf_p Dpq
            have bf_q : q ∈ ab f := by
              show q ∈ refineRect (ab0 f)
              rw [in_refine_rect, Dpq, ← in_refine_rect]; exact bf_p
            exact ⟨IHpq q p bf_q Dpq.symm, IHpq p q bf_p Dpq⟩
          · obtain ⟨p, cm2p, bf_p⟩ := cm2_bf
            exact ⟨p, cm2cm _ cm2p, bf_p⟩
        · rintro ⟨p, cm2p, bf_p⟩
          rcases (ab_cm2 p cm2p).2 with h | h
          · exact absurd bf_p (bf'e p h)
          · exact bf_f ⟨p, h, bf_p⟩
      · rw [xcmo _ hie]
        exact ⟨e2bf, bf_f⟩

end ExtendAdj

/-! ### The extended mattes (Coq section `Let cm`) -/

section ExtendedMattes

variable {Nr : ℕ} {ab0 : AdjBox Nr} {cm0 : CMatte Nr}

/-- Coq section `Let cm`: the extended mattes, chosen from `cm_extend_adj`. -/
noncomputable def cmExtend (ab0P : AbProper ab0) (cm0P : CmProper cm0)
    (abcm0P : ∀ e i, AbCmProper ab0 cm0 e i) : CMatte Nr :=
  (cm_extend_adj ab0P cm0P abcm0P).choose

/-- Coq section `Let cmP`. -/
theorem cmExtend_proper (ab0P : AbProper ab0) (cm0P : CmProper cm0)
    (abcm0P : ∀ e i, AbCmProper ab0 cm0 e i) : CmProper (cmExtend ab0P cm0P abcm0P) :=
  (cm_extend_adj ab0P cm0P abcm0P).choose_spec.1

/-- Coq section `Let ab_cmP`. -/
theorem cmExtend_adj (ab0P : AbProper ab0) (cm0P : CmProper cm0)
    (abcm0P : ∀ e i, AbCmProper ab0 cm0 e i) (e : AdjIndex Nr) (he : GrProper (ab0 e)) :
    Madj (cmExtend ab0P cm0P abcm0P e.fst) (cmExtend ab0P cm0P abcm0P e.snd) :=
  (cm_extend_adj ab0P cm0P abcm0P).choose_spec.2 e he

end ExtendedMattes

/-! ### The bounding box -/

section BoundingBox

variable {Nr : ℕ}

/-- Coq section `Let grect0`: the unit rectangle containing the pixel `0`. -/
def grect0 : GRect := ⟨0, 1, 0, 1⟩

/-- Coq `cm_bbox`: a grid rectangle containing all the mattes of `cm` (and the pixel `0`). -/
def cmBbox (cm : CMatte Nr) : GRect :=
  ((List.finRange Nr).flatMap fun i => (cm i).mdisk).foldr extendGrect grect0

private theorem mem_foldr_extend_of_mem {r : GRect} {q : GPoint} (hq : q ∈ r) :
    ∀ l : List GPoint, q ∈ l.foldr extendGrect r
  | [] => hq
  | p :: l => in_extend_grect p _ q (Or.inr (mem_foldr_extend_of_mem hq l))

private theorem mem_foldr_extend {r : GRect} :
    ∀ {l : List GPoint} {q : GPoint}, q ∈ l → q ∈ l.foldr extendGrect r
  | p :: l, q, hq => by
    rcases List.mem_cons.1 hq with rfl | hq
    · exact in_extend_grect _ _ _ (Or.inl rfl)
    · exact in_extend_grect _ _ _ (Or.inr (mem_foldr_extend hq))

/-- Coq `sub_cm_bbox`. -/
theorem sub_cm_bbox (cm : CMatte Nr) (i : Fin Nr) : ∀ p, p ∈ cm i → p ∈ cmBbox cm := by
  intro p hp
  apply mem_foldr_extend
  exact List.mem_flatMap.2 ⟨i, List.mem_finRange i, hp⟩

/-- A proper rectangle, in coordinates (not in Coq). -/
theorem grProper_iff (r : GRect) : GrProper r ↔ r.xmin < r.xmax ∧ r.ymin < r.ymax := by
  simp only [GrProper, garea, gwidth, gheight, zwidth, CanonicallyOrderedAdd.mul_pos]
  omega

/-- The bounding box is proper (not in Coq; part of `cm_bboxE`). -/
theorem cmBbox_proper (cm : CMatte Nr) : GrProper (cmBbox cm) := by
  rw [gr_properP]
  exact ⟨0, mem_foldr_extend_of_mem (by simp [grect0, mem_grect]) _⟩

/-- Coq `cm_bboxE`, for an arbitrary proper rectangle. -/
theorem grectE (bb : GRect) (hbb : GrProper bb) :
    0 < (gwidth bb : ℤ) ∧ 0 < (gheight bb : ℤ) ∧ ∃ p0 : GPoint,
      (∀ x y : ℤ, p0 + ⟨x, y⟩ ∈ bb ↔ (0 ≤ x ∧ x < gwidth bb) ∧ (0 ≤ y ∧ y < gheight bb)) ∧
      ∀ p, p ∈ bb → ∃ x y : ℕ, p = p0 + ⟨x, y⟩ ∧ (x : ℤ) < gwidth bb ∧ (y : ℤ) < gheight bb := by
  rw [grProper_iff] at hbb
  have hw : (gwidth bb : ℤ) = bb.xmax - bb.xmin := by simp only [gwidth, zwidth]; omega
  have hh : (gheight bb : ℤ) = bb.ymax - bb.ymin := by simp only [gheight, zwidth]; omega
  refine ⟨by omega, by omega, ⟨bb.xmin, bb.ymin⟩, fun x y => ?_, fun p hp => ?_⟩
  · simp only [mem_grect, add_x, add_y, hw, hh]; omega
  · rw [mem_grect] at hp
    refine ⟨(p.x - bb.xmin).toNat, (p.y - bb.ymin).toNat, ?_, by omega, by omega⟩
    ext <;> simp <;> omega

/-- Coq `cm_bboxE`. -/
theorem cm_bboxE (cm : CMatte Nr) :
    0 < (gwidth (cmBbox cm) : ℤ) ∧ 0 < (gheight (cmBbox cm) : ℤ) ∧ ∃ p0 : GPoint,
      (∀ x y : ℤ, p0 + ⟨x, y⟩ ∈ cmBbox cm ↔
        (0 ≤ x ∧ x < gwidth (cmBbox cm)) ∧ (0 ≤ y ∧ y < gheight (cmBbox cm))) ∧
      ∀ p, p ∈ cmBbox cm → ∃ x y : ℕ,
        p = p0 + ⟨x, y⟩ ∧ (x : ℤ) < gwidth (cmBbox cm) ∧ (y : ℤ) < gheight (cmBbox cm) :=
  grectE _ (cmBbox_proper cm)

end BoundingBox

/-! ### The box hypermap

It would be tempting to form this hypermap from the darts contained in the bounding box, but
unfortunately this map is not bridgeless. We work around this issue by using the edge closure
of `gmgrid`. -/

section BoxMap

variable (bb : GRect)

/-- Coq `gmgrid`: the darts of the refined bounding box, and their `gedge` images. -/
def gmgrid : List GPoint :=
  let inner := enumGrect (refineRect bb)
  inner ++ inner.map gedge

/-- Coq `gmgridE`. -/
theorem gmgridE (d : GPoint) : d ∈ gmgrid bb ↔ halfg d ∈ bb ∨ halfg (gedge d) ∈ bb := by
  simp only [gmgrid, List.mem_append, List.mem_map, mem_enum_grect, in_refine_rect]
  refine or_congr Iff.rfl ⟨?_, fun h => ⟨gedge d, h, gedge2 d⟩⟩
  rintro ⟨a, ha, rfl⟩
  rwa [gedge2]

/-- Coq `gmgrid_edge`. -/
theorem gmgrid_edge (d : GPoint) : gedge d ∈ gmgrid bb ↔ d ∈ gmgrid bb := by
  rw [gmgridE, gmgridE, gedge2, or_comm]

/-- Coq `gmdart`: the darts of the box hypermap, the subtype of `gmgrid bb` (Coq `seq_sub`).
The Coq coercion `gmval` is `Subtype.val`, and the constructor `Gmdart d Gd` is `⟨d, Gd⟩`. -/
abbrev GmDart : Type := {d : GPoint // d ∈ gmgrid bb}

variable {bb}

/-- Coq `insubd u d`, on `GmDart`: `d` itself if it lies in `gmgrid`, `u` otherwise. -/
def gmInsubd (u : GmDart bb) (d : GPoint) : GmDart bb :=
  if h : d ∈ gmgrid bb then ⟨d, h⟩ else u

/-- Coq `gmedge`. -/
def gmEdge (u : GmDart bb) : GmDart bb := ⟨gedge u.1, (gmgrid_edge bb u.1).2 u.2⟩

/-- Coq `gmpick u s`: the last item of `s` that lies in `gmgrid`, defaulting to `u`. -/
def gmpick (u : GmDart bb) (s : List GPoint) : GmDart bb := s.foldl gmInsubd u

/-- Coq `gmface`. -/
def gmFace (u : GmDart bb) : GmDart bb := gmpick u (List.iterate gnode (gnode u.1) 3)

/-- Coq `gmnode`. -/
def gmNode (u : GmDart bb) : GmDart bb :=
  gmpick u ((List.iterate gnode (gnode u.1) 3).map gedge).reverse

@[simp] theorem val_gmEdge (u : GmDart bb) : (gmEdge u).1 = gedge u.1 := rfl

/-- The value of `gmFace` (not in Coq). -/
theorem val_gmFace (u : GmDart bb) : (gmFace u).1 =
    if gnode (gnode (gnode u.1)) ∈ gmgrid bb then gnode (gnode (gnode u.1))
    else if gnode (gnode u.1) ∈ gmgrid bb then gnode (gnode u.1)
    else if gnode u.1 ∈ gmgrid bb then gnode u.1 else u.1 := by
  simp only [gmFace, gmpick, List.iterate, List.foldl, gmInsubd]
  split_ifs <;> rfl

/-- The value of `gmNode` (not in Coq). -/
theorem val_gmNode (u : GmDart bb) : (gmNode u).1 =
    if gedge (gnode u.1) ∈ gmgrid bb then gedge (gnode u.1)
    else if gedge (gnode (gnode u.1)) ∈ gmgrid bb then gedge (gnode (gnode u.1))
    else if gedge (gnode (gnode (gnode u.1))) ∈ gmgrid bb then gedge (gnode (gnode (gnode u.1)))
    else u.1 := by
  simp only [gmNode, gmpick, List.iterate, List.map, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.foldl, gmInsubd]
  split_ifs <;> rfl

/-- Coq `gmedge2`. -/
theorem gmedge2 (u : GmDart bb) : gmEdge (gmEdge u) = u := Subtype.ext (gedge2 u.1)

/-- `halfg (gedge (gnode d)) = halfg d` (not in Coq). -/
theorem halfg_edge_node (d : GPoint) : halfg (gedge (gnode d)) = halfg d := by
  rw [← halfg_face, gnodeK]

/-- `gedge (gnode d)` is the inverse of `gface d` (not in Coq). -/
theorem gedge_gnode (d : GPoint) : gedge (gnode d) = gface (gface (gface d)) := by
  conv_lhs => rw [← gface4 d]
  exact gfaceK _

/-- Coq `gmedgeK`. -/
theorem gmedgeK (u : GmDart bb) : gmNode (gmFace (gmEdge u)) = u := by
  obtain ⟨d, Gd⟩ := u
  apply Subtype.ext
  set e := gedge d with he
  have ed : gedge e = d := gedge2 d
  have n4 : gnode (gnode (gnode (gnode e))) = e := gnode4 e
  have hn : gnode (gnode (gnode e)) ∈ gmgrid bb ∨ gnode e ∈ gmgrid bb := by
    rcases (gmgridE bb d).1 Gd with h | h
    · left
      have : gnode (gnode (gnode e)) = gface d := by
        rw [← gnodeK (gnode (gnode (gnode e))), n4, ed]
      rw [this, gmgridE, halfg_face]; exact Or.inl h
    · right
      rw [gmgridE, halfg_edge_node]; exact Or.inr h
  have key : ∀ F : GmDart bb, (F.1 = gnode (gnode (gnode e)) ∨
      (F.1 = gnode (gnode e) ∧ gnode (gnode (gnode e)) ∉ gmgrid bb) ∨
      (F.1 = gnode e ∧ gnode (gnode (gnode e)) ∉ gmgrid bb ∧ gnode (gnode e) ∉ gmgrid bb)) →
      (gmNode F).1 = d := by
    intro F hF
    rw [val_gmNode]
    rcases hF with hF | ⟨hF, h3⟩ | ⟨hF, h3, h2⟩ <;> rw [hF]
    · rw [n4, ed]; simp [Gd]
    · have h3' : gedge (gnode (gnode (gnode e))) ∉ gmgrid bb := by rwa [gmgrid_edge]
      rw [n4, ed, ite_eq_right h3', ite_eq_left Gd]
    · have h2' : gedge (gnode (gnode e)) ∉ gmgrid bb := by rwa [gmgrid_edge]
      have h3' : gedge (gnode (gnode (gnode e))) ∉ gmgrid bb := by rwa [gmgrid_edge]
      rw [n4, ed, ite_eq_right h2', ite_eq_right h3', ite_eq_left Gd]
  apply key
  rw [val_gmFace, val_gmEdge]
  by_cases h3 : gnode (gnode (gnode e)) ∈ gmgrid bb
  · left; rw [ite_eq_left h3]
  · right
    rw [ite_eq_right h3]
    by_cases h2 : gnode (gnode e) ∈ gmgrid bb
    · left; rw [ite_eq_left h2]; exact ⟨rfl, h3⟩
    · right; rw [ite_eq_right h2, ite_eq_left (hn.resolve_left h3)]; exact ⟨rfl, h3, h2⟩

variable (bb)

/-- Coq `gmdart_map`: the box hypermap. -/
def gmdartMap : Hypermap (GmDart bb) := ⟨gmEdge, gmNode, gmFace, gmedgeK⟩

@[simp] theorem gmdartMap_edge (u : GmDart bb) : (gmdartMap bb).edge u = gmEdge u := rfl
@[simp] theorem gmdartMap_node (u : GmDart bb) : (gmdartMap bb).node u = gmNode u := rfl
@[simp] theorem gmdartMap_face (u : GmDart bb) : (gmdartMap bb).face u = gmFace u := rfl

/-- Coq `gmdart_plain`. -/
theorem gmdart_plain : (gmdartMap bb).Plain := by
  rw [Plain, plainP]
  intro u _
  refine ⟨gmedge2 u, fun h => neq_halfg_edge u.1 ?_⟩
  have := congrArg Subtype.val h
  simp only [gmdartMap_edge, val_gmEdge] at this
  rw [this]

/-- Coq `gm_inner`: the darts whose pixel lies in the bounding box. -/
def gmInner : Set (GmDart bb) := {u | halfg u.1 ∈ bb}

variable {bb}

/-- Coq `val_gmnode`. -/
theorem val_gmnode {u : GmDart bb} (hu : u ∈ gmInner bb) :
    ((gmdartMap bb).node u).1 = gedge (gnode u.1) := by
  have h : gedge (gnode u.1) ∈ gmgrid bb := by
    rw [gmgridE, halfg_edge_node]
    exact Or.inl hu
  rw [gmdartMap_node, val_gmNode, ite_eq_left h]

/-- `node` preserves the pixel of inner darts (not in Coq). -/
theorem halfg_gmnode {u : GmDart bb} (hu : u ∈ gmInner bb) :
    halfg ((gmdartMap bb).node u).1 = halfg u.1 := by
  rw [val_gmnode hu, halfg_edge_node]

/-- Coq `gm_inner_node`. -/
theorem gm_inner_node {u : GmDart bb} (hu : u ∈ gmInner bb) :
    (gmdartMap bb).node u ∈ gmInner bb := by
  show halfg _ ∈ bb
  rw [halfg_gmnode hu]; exact hu

variable (bb)

/-- Coq `gm_inner_closed`. -/
theorem gm_inner_closed : Closed (frel (gmdartMap bb).node) (gmInner bb) :=
  Closed.of_forward (gmdartMap bb).cnode_sym fun _ _ hxy hx => hxy ▸ gm_inner_node hx

end BoxMap

/-! ### Counting the darts of the box hypermap -/

section CardGmdart

/-- The darts `gedge (2 • p + c)` for `p` in `r`: the outer border darts along one side of the
bounding box (the sides of the Coq proof of `card_gmdart`). -/
private def side (r : GRect) (c : GPoint) : List GPoint :=
  (enumGrect r).map fun p => gedge (2 • p + c)

private theorem mem_side' (r : GRect) {c : GPoint} (hc : IsOddg c) (x : GPoint) :
    x ∈ side r c ↔ halfg (gedge x) ∈ r ∧ oddg (gedge x) = c := by
  simp only [side, List.mem_map, mem_enum_grect]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [gedge2, halfg_eq _ hc, oddg_eq _ hc]
    exact ⟨hp, rfl⟩
  · rintro ⟨h1, h2⟩
    exact ⟨_, h1, by rw [← h2, halfgK, gedge2]⟩

private theorem side_nodup (r : GRect) {c : GPoint} (hc : IsOddg c) : (side r c).Nodup := by
  refine (enum_grect_uniq r).map fun p q h => ?_
  have h' : 2 • p + c = 2 • q + c := by
    have := congrArg gedge h
    simpa only [gedge2] using this
  rw [← halfg_eq p hc, h', halfg_eq q hc]

private theorem length_side (r : GRect) (c : GPoint) : (side r c).length = garea r := by
  rw [side, List.length_map, size_enum_grect]

/-- Coq `card_gmdart`. -/
theorem card_gmdart (bb : GRect) (hbb : GrProper bb) :
    Fintype.card (GmDart bb) = 2 * (gwidth bb * gheight bb * 2 + gwidth bb + gheight bb) := by
  classical
  rw [grProper_iff] at hbb
  obtain ⟨x0, x1, y0, y1⟩ := bb
  simp only at hbb
  have o00 : IsOddg (0 : GPoint) := IsOddg.gpoint00
  have o10 : IsOddg (⟨1, 0⟩ : GPoint) := IsOddg.gpoint10
  have o11 : IsOddg (⟨1, 1⟩ : GPoint) := IsOddg.gpoint11
  have o01 : IsOddg (⟨0, 1⟩ : GPoint) := IsOddg.gpoint01
  set L : List GPoint := enumGrect (refineRect ⟨x0, x1, y0, y1⟩) ++
    (side ⟨x0, x1, y0, y0 + 1⟩ 0 ++ (side ⟨x1 - 1, x1, y0, y1⟩ ⟨1, 0⟩ ++
      (side ⟨x0, x1, y1 - 1, y1⟩ ⟨1, 1⟩ ++ side ⟨x0, x0 + 1, y0, y1⟩ ⟨0, 1⟩))) with hL
  have hin : ∀ x : GPoint, x ∈ enumGrect (refineRect ⟨x0, x1, y0, y1⟩) ↔
      (x0 ≤ x.x / 2 ∧ x.x / 2 < x1) ∧ (y0 ≤ x.y / 2 ∧ x.y / 2 < y1) := fun x => by
    rw [mem_enum_grect, in_refine_rect, mem_grect]; rfl
  have hs : ∀ (r : GRect) {c : GPoint}, IsOddg c → ∀ x : GPoint, x ∈ side r c ↔
      ((r.xmin ≤ (x.x + 1 - 2 * (x.y % 2)) / 2 ∧ (x.x + 1 - 2 * (x.y % 2)) / 2 < r.xmax) ∧
       (r.ymin ≤ (x.y + 2 * (x.x % 2) - 1) / 2 ∧ (x.y + 2 * (x.x % 2) - 1) / 2 < r.ymax)) ∧
      ((x.x + 1 - 2 * (x.y % 2)) % 2 = c.x ∧ (x.y + 2 * (x.x % 2) - 1) % 2 = c.y) := by
    intro r c hc x
    rw [mem_side' r hc, mem_grect, GPoint.ext_iff]
    simp only [halfg_x, halfg_y, oddg_x, oddg_y, gedge_x, gedge_y]
  have hmem : ∀ x, x ∈ L ↔ x ∈ gmgrid ⟨x0, x1, y0, y1⟩ := by
    intro x
    simp only [hL, List.mem_append, hin, hs _ o00, hs _ o10, hs _ o11, hs _ o01, gmgridE,
      mem_grect, halfg_x, halfg_y, gedge_x, gedge_y, zero_x, zero_y]
    rcases Int.emod_two_eq_zero_or_one x.x with h1 | h1 <;>
      rcases Int.emod_two_eq_zero_or_one x.y with h2 | h2 <;> simp only [h1, h2] <;> omega
  have hnd : L.Nodup := by
    simp only [hL, List.nodup_append, side_nodup _ o00, side_nodup _ o10, side_nodup _ o11,
      side_nodup _ o01, enum_grect_uniq, true_and, List.mem_append, hin, hs _ o00, hs _ o10,
      hs _ o11, hs _ o01, zero_x, zero_y]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> intro a ha b hb hab <;> subst hab <;>
      rcases Int.emod_two_eq_zero_or_one a.x with h1 | h1 <;>
      rcases Int.emod_two_eq_zero_or_one a.y with h2 | h2 <;> omega
  rw [Fintype.card_of_subtype L.toFinset (fun x => by rw [List.mem_toFinset, hmem]),
    List.toFinset_card_of_nodup hnd]
  simp only [hL, List.length_append, length_side, size_enum_grect, garea_refine_rect]
  simp only [garea, gwidth, gheight, zwidth]
  have e1 : (y0 + 1 - y0).toNat = 1 := by omega
  have e2 : (x1 - (x1 - 1)).toNat = 1 := by omega
  have e3 : (y1 - (y1 - 1)).toNat = 1 := by omega
  have e4 : (x0 + 1 - x0).toNat = 1 := by omega
  rw [e1, e2, e3, e4]
  ring

end CardGmdart

/-! ### Faces, nodes, connectivity and planarity of the box hypermap -/

section BoxMapProps

variable {bb : GRect}

private theorem gmFace_n3 {u v : GmDart bb} (h : v.1 = gnode (gnode (gnode u.1))) :
    gmFace u = v := by
  apply Subtype.ext
  rw [val_gmFace, ← h, ite_eq_left v.2]

private theorem gmFace_n2 {u v : GmDart bb} (h : v.1 = gnode (gnode u.1)) :
    (gmdartMap bb).cface u v := by
  by_cases h3 : gnode (gnode (gnode u.1)) ∈ gmgrid bb
  · have e1 : gmFace u = ⟨_, h3⟩ := gmFace_n3 rfl
    have e2 : gmFace (⟨_, h3⟩ : GmDart bb) = v := gmFace_n3 (by
      show v.1 = gnode (gnode (gnode (gnode (gnode (gnode u.1)))))
      rw [gnode4, h])
    exact connect_trans (connect_of_rel e1) (connect_of_rel e2)
  · refine connect_of_rel (Subtype.ext ?_)
    show (gmFace u).1 = v.1
    rw [val_gmFace, ite_eq_right h3, ← h, ite_eq_left v.2]

private theorem gmFace_n1 {u v : GmDart bb} (h : v.1 = gnode u.1) :
    (gmdartMap bb).cface u v := by
  by_cases h3 : gnode (gnode (gnode u.1)) ∈ gmgrid bb
  · have e1 : gmFace u = ⟨_, h3⟩ := gmFace_n3 rfl
    refine connect_trans (connect_of_rel e1) (gmFace_n2 ?_)
    show v.1 = gnode (gnode (gnode (gnode (gnode u.1))))
    rw [gnode4, h]
  · by_cases h2 : gnode (gnode u.1) ∈ gmgrid bb
    · have e1 : (gmdartMap bb).face u = ⟨_, h2⟩ := by
        apply Subtype.ext
        show (gmFace u).1 = _
        rw [val_gmFace, ite_eq_right h3, ite_eq_left h2]
      refine connect_trans (connect_of_rel e1) (connect_of_rel (gmFace_n3 ?_))
      show v.1 = gnode (gnode (gnode (gnode (gnode u.1))))
      rw [gnode4, h]
    · refine connect_of_rel (Subtype.ext ?_)
      show (gmFace u).1 = v.1
      rw [val_gmFace, ite_eq_right h3, ite_eq_right h2, ← h, ite_eq_left v.2]

/-- Coq `cface_end0g`: the faces of the box hypermap are the grid points. -/
theorem cface_end0g (u v : GmDart bb) :
    (gmdartMap bb).cface u v ↔ end0g u.1 = end0g v.1 := by
  constructor
  · intro h
    induction h with
    | refl => rfl
    | tail _ hbc ih =>
      rw [ih, ← hbc]
      show end0g _ = end0g (gmFace _).1
      rw [val_gmFace]
      split_ifs <;> simp only [end0g_node]
  · intro h
    have := same_end0g h
    simp only [List.iterate, List.mem_cons, List.not_mem_nil, or_false] at this
    rcases this with h0 | h1 | h2 | h3
    · rw [Subtype.ext h0.symm]
    · exact gmFace_n1 h1
    · exact gmFace_n2 h2
    · exact connect_of_rel (gmFace_n3 h3)

/-- Coq `fcard_gmface`. -/
theorem fcard_gmface (hbb : GrProper bb) :
    fcard (gmdartMap bb).face Set.univ = (gwidth bb + 1) * (gheight bb + 1) := by
  rw [grProper_iff] at hbb
  have himg : (fun u : GmDart bb => end0g u.1) '' Set.univ =
      {q | q ∈ enumGrect ⟨bb.xmin, bb.xmax + 1, bb.ymin, bb.ymax + 1⟩} := by
    ext q
    simp only [Set.image_univ, Set.mem_range, Set.mem_ofPred_eq, mem_enum_grect, mem_grect]
    constructor
    · rintro ⟨u, rfl⟩
      have hu := (gmgridE bb u.1).1 u.2
      simp only [mem_grect, halfg_x, halfg_y, gedge_x, gedge_y] at hu
      rw [end0g_x, end0g_y]
      rcases Int.emod_two_eq_zero_or_one u.1.x with h1 | h1 <;>
        rcases Int.emod_two_eq_zero_or_one u.1.y with h2 | h2 <;> omega
    · intro hq
      let d : GPoint := ⟨if q.x = bb.xmax then 2 * q.x - 1 else 2 * q.x,
        if q.y = bb.ymax then 2 * q.y - 1 else 2 * q.y⟩
      have Gd : d ∈ gmgrid bb := by
        rw [gmgridE]; left
        simp only [d, mem_grect, halfg_x, halfg_y]
        split_ifs <;> omega
      refine ⟨⟨d, Gd⟩, ?_⟩
      ext <;> simp only [end0g_x, end0g_y, d] <;> split_ifs <;> omega
  rw [fcard, nComp, ncard_image_eq_of_ker (comp (frel (gmdartMap bb).face))
      (fun u : GmDart bb => end0g u.1) (fun x _ y _ => by
        rw [comp_eq_iff (gmdartMap bb).cface_sym]; exact cface_end0g x y),
    himg, ncard_mem_of_nodup (enum_grect_uniq _), size_enum_grect]
  simp only [garea, gwidth, gheight, zwidth]
  have e1 : (bb.xmax + 1 - bb.xmin).toNat = (bb.xmax - bb.xmin).toNat + 1 := by omega
  have e2 : (bb.ymax + 1 - bb.ymin).toNat = (bb.ymax - bb.ymin).toNat + 1 := by omega
  rw [e1, e2]

/-- `node` acts as the inverse of `gface` on the inner darts (not in Coq). -/
private theorem val_gmnode' {u : GmDart bb} (hu : u ∈ gmInner bb) :
    ((gmdartMap bb).node u).1 = gface (gface (gface u.1)) := by
  rw [val_gmnode hu, gedge_gnode]

private theorem gface_ne (x : GPoint) :
    gface x ≠ x ∧ gface (gface x) ≠ x ∧ gface (gface (gface x)) ≠ x := by
  have o1 := oddg_face x
  have o2 : oddg (gface (gface x)) = ccw (ccw (oddg x)) := by rw [oddg_face, oddg_face]
  have o3 : oddg (gface (gface (gface x))) = ccw (ccw (ccw (oddg x))) := by
    rw [oddg_face, oddg_face, oddg_face]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h] at o1; exact neq_ccw _ o1.symm
  · rw [h, ccw2] at o2
    have := congrArg GPoint.x o2
    simp only [sub_x] at this
    omega
  · rw [h] at o3
    have := congrArg ccw o3
    rw [ccw4] at this
    exact neq_ccw _ this

/-- The inner darts have node order `4` (not in Coq). -/
private theorem order_gmnode {u : GmDart bb} (hu : u ∈ gmInner bb) :
    order (gmdartMap bb).node u = 4 := by
  set n := (gmdartMap bb).node
  have hu1 := gm_inner_node hu
  have hu2 := gm_inner_node hu1
  have hu3 := gm_inner_node hu2
  have v1 := val_gmnode' hu
  have v2 := val_gmnode' hu1
  have v3 := val_gmnode' hu2
  have v4 := val_gmnode' hu3
  rw [v3, v2, v1] at v4
  rw [v2, v1] at v3
  rw [v1] at v2
  set d := u.1
  have f4 := gface4 d
  have e2 : (n (n u)).1 = gface (gface d) := by rw [v2, f4]
  have e3 : (n (n (n u))).1 = gface d := by rw [v3, f4, f4]
  have e4 : n (n (n (n u))) = u := Subtype.ext (by rw [v4, f4, f4, f4])
  have cyc : fcycle n [u, n u, n (n u), n (n (n u))] := by
    exact ⟨rfl, rfl, rfl, e4, trivial⟩
  have nd : [u, n u, n (n u), n (n (n u))].Nodup := by
    apply List.Nodup.of_map Subtype.val
    have e1 : (n u).1 = gface (gface (gface d)) := v1
    simp only [List.map_cons, List.map_nil, e1, e2, e3]
    obtain ⟨g1, g2, g3⟩ := gface_ne d
    obtain ⟨g1', g2', -⟩ := gface_ne (gface d)
    obtain ⟨g1'', -, -⟩ := gface_ne (gface (gface d))
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    exact ⟨⟨Ne.symm g3, Ne.symm g2, Ne.symm g1⟩, ⟨g1'', g2'⟩, g1', not_false⟩
  rw [order_cycle cyc nd List.mem_cons_self]
  rfl

/-- Coq `fcard_gmnode`. -/
theorem fcard_gmnode : gwidth bb * gheight bb ≤ fcard (gmdartMap bb).node Set.univ := by
  have hsub : gmInner bb ⊆ orderSet (gmdartMap bb).node 4 := fun u hu => order_gmnode hu
  have key := fcard_order_set (gmdartMap bb).nodeI hsub (gm_inner_closed bb)
  have hcard : (gmInner bb).ncard = 2 * (2 * garea bb) := by
    rw [← Set.ncard_image_of_injective _ Subtype.val_injective, ← garea_refine_rect,
      ← size_enum_grect, ← ncard_mem_of_nodup (enum_grect_uniq _)]
    congr 1
    ext d
    simp only [Set.mem_image, Set.mem_ofPred_eq, mem_enum_grect, in_refine_rect, gmInner]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact hu
    · intro hd
      exact ⟨⟨d, (gmgridE bb d).2 (Or.inl hd)⟩, hd, rfl⟩
  have hle : fcard (gmdartMap bb).node (gmInner bb) ≤ fcard (gmdartMap bb).node Set.univ :=
    Set.ncard_le_ncard (Set.image_mono (Set.subset_univ _)) (Set.toFinite _)
  rw [hcard, garea] at key
  omega

/-- The darts of a pixel are connected by `node` steps (not in Coq). -/
private theorem gcomp_face {v w : GmDart bb} (hv : v ∈ gmInner bb) (h : w.1 = gface v.1) :
    (gmdartMap bb).gcomp v w := by
  have hv1 := gm_inner_node hv
  have hv2 := gm_inner_node hv1
  have e : (gmdartMap bb).node ((gmdartMap bb).node ((gmdartMap bb).node v)) = w := by
    apply Subtype.ext
    rw [val_gmnode' hv2, val_gmnode' hv1, val_gmnode' hv, gface4, gface4, h]
  rw [← e]
  exact connect_trans (connect_trans (connect_of_rel ((gmdartMap bb).glinkN _))
    (connect_of_rel ((gmdartMap bb).glinkN _))) (connect_of_rel ((gmdartMap bb).glinkN _))

private theorem gcomp_pixel {v w : GmDart bb} (hv : v ∈ gmInner bb)
    (h : halfg w.1 = halfg v.1) : (gmdartMap bb).gcomp v w := by
  have hm := same_halfg h.symm
  simp only [List.iterate, List.mem_cons, List.not_mem_nil, or_false] at hm
  have G1 : gface v.1 ∈ gmgrid bb := (gmgridE bb _).2 (Or.inl (by rw [halfg_face]; exact hv))
  have G2 : gface (gface v.1) ∈ gmgrid bb :=
    (gmgridE bb _).2 (Or.inl (by rw [halfg_face, halfg_face]; exact hv))
  have I1 : (⟨_, G1⟩ : GmDart bb) ∈ gmInner bb := by
    show halfg (gface v.1) ∈ bb; rw [halfg_face]; exact hv
  have I2 : (⟨_, G2⟩ : GmDart bb) ∈ gmInner bb := by
    show halfg (gface (gface v.1)) ∈ bb; rw [halfg_face, halfg_face]; exact hv
  rcases hm with h0 | h1 | h2 | h3
  · rw [Subtype.ext h0]
  · exact gcomp_face hv h1
  · exact connect_trans (gcomp_face hv rfl) (gcomp_face I1 h2)
  · exact connect_trans (connect_trans (gcomp_face hv rfl) (gcomp_face I1 rfl))
      (gcomp_face I2 h3)

/-- Coq `gmdart_connected`. -/
theorem gmdart_connected (hbb : GrProper bb) : (gmdartMap bb).Connected := by
  rw [grProper_iff] at hbb
  set H := gmdartMap bb
  set p0 : GPoint := ⟨bb.xmin, bb.ymin⟩
  have Gu : 2 • p0 ∈ gmgrid bb := by
    rw [gmgridE, halfg_double]; left; simp only [p0, mem_grect]; omega
  set u : GmDart bb := ⟨_, Gu⟩
  have Iu : u ∈ gmInner bb := by
    show halfg (2 • p0) ∈ bb; rw [halfg_double]; simp only [p0, mem_grect]; omega
  -- the edge of `w` is linked back to `w`
  have back : ∀ w : GmDart bb, H.gcomp u (H.edge w) → H.gcomp u w := fun w hw => by
    refine connect_trans hw (connect_of_rel ?_)
    have := H.glinkE (H.edge w)
    rwa [show H.edge (H.edge w) = w from gmedge2 w] at this
  have inner : ∀ n : ℕ, ∀ v : GmDart bb, v ∈ gmInner bb →
      ((halfg v.1).x - bb.xmin + ((halfg v.1).y - bb.ymin)).toNat = n → H.gcomp u v := by
    intro n
    induction n with
    | zero =>
      intro v hv hn
      have hv' : halfg v.1 ∈ bb := hv
      rw [mem_grect] at hv'
      refine gcomp_pixel Iu ?_
      rw [halfg_double]
      ext <;> simp only [p0] <;> omega
    | succ n IHn =>
      intro v hv hn
      have hv' : halfg v.1 ∈ bb := hv
      rw [mem_grect] at hv'
      set p := halfg v.1
      by_cases hx : bb.xmin < p.x
      · have o : IsOddg (⟨0, 1⟩ : GPoint) := IsOddg.gpoint01
        have Gw : 2 • p + ⟨0, 1⟩ ∈ gmgrid bb := by
          rw [gmgridE, halfg_eq _ o]; exact Or.inl hv
        have Iw : (⟨_, Gw⟩ : GmDart bb) ∈ gmInner bb := by
          show halfg (2 • p + ⟨0, 1⟩) ∈ bb; rw [halfg_eq _ o]; exact hv
        have hew : halfg (gedge (2 • p + ⟨0, 1⟩)) = ⟨p.x - 1, p.y⟩ := by
          ext <;> simp only [halfg_x, halfg_y, gedge_x, gedge_y, add_x, add_y, nsmul_x,
            nsmul_y] <;> push_cast <;> omega
        have Iew : H.edge ⟨_, Gw⟩ ∈ gmInner bb := by
          show halfg (gedge (2 • p + ⟨0, 1⟩)) ∈ bb
          rw [hew, mem_grect]; simp only; omega
        have h1 := IHn _ Iew (by
          show ((halfg (gedge (2 • p + ⟨0, 1⟩))).x - bb.xmin +
            ((halfg (gedge (2 • p + ⟨0, 1⟩))).y - bb.ymin)).toNat = n
          rw [hew]; simp only; omega)
        exact connect_trans (back _ h1) (gcomp_pixel Iw (halfg_eq _ o).symm)
      · have o : IsOddg (0 : GPoint) := IsOddg.gpoint00
        have Gw : 2 • p + 0 ∈ gmgrid bb := by
          rw [gmgridE, halfg_eq _ o]; exact Or.inl hv
        have Iw : (⟨_, Gw⟩ : GmDart bb) ∈ gmInner bb := by
          show halfg (2 • p + 0) ∈ bb; rw [halfg_eq _ o]; exact hv
        have hew : halfg (gedge (2 • p + 0)) = ⟨p.x, p.y - 1⟩ := by
          ext <;> simp only [halfg_x, halfg_y, gedge_x, gedge_y, add_x, add_y, nsmul_x,
            nsmul_y, zero_x, zero_y] <;> push_cast <;> omega
        have Iew : H.edge ⟨_, Gw⟩ ∈ gmInner bb := by
          show halfg (gedge (2 • p + 0)) ∈ bb
          rw [hew, mem_grect]; simp only; omega
        have h1 := IHn _ Iew (by
          show ((halfg (gedge (2 • p + 0))).x - bb.xmin +
            ((halfg (gedge (2 • p + 0))).y - bb.ymin)).toNat = n
          rw [hew]; simp only; omega)
        exact connect_trans (back _ h1) (gcomp_pixel Iw (halfg_eq _ o).symm)
  have hall : ∀ v : GmDart bb, H.gcomp u v := by
    intro v
    rcases (gmgridE bb v.1).1 v.2 with hv | hv
    · exact inner _ v hv rfl
    · exact back v (inner _ (H.edge v) hv rfl)
  have huniv : (Set.univ : Set (GmDart bb)) = comp H.glink u :=
    Set.ext fun v => ⟨fun _ => hall v, fun _ => Set.mem_univ v⟩
  rw [Connected, huniv, nComp_comp H.glinkC]

/-- Coq `gmdart_planar`. -/
theorem gmdart_planar (hbb : GrProper bb) : (gmdartMap bb).Planar := by
  have hE := fcard_order_set (gmdartMap bb).edgeI (gmdart_plain bb) closed_univ
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, card_gmdart bb hbb] at hE
  have hF := fcard_gmface hbb
  have hN := fcard_gmnode (bb := bb)
  have hC := gmdart_connected hbb
  rw [Connected] at hC
  rw [Planar, genus, eulerLhs, eulerRhs, hC, card_gmdart bb hbb, hF]
  apply Nat.div_eq_of_lt
  have : (gwidth bb + 1) * (gheight bb + 1) = gwidth bb * gheight bb + gwidth bb +
    gheight bb + 1 := by ring
  rw [this]
  generalize gwidth bb * gheight bb = W at *
  omega

end BoxMapProps

/-! ### The matte rings in the box hypermap -/

/-- `cycle` of a mapped sequence (math-comp `map_cycle`-style; not in `gridmap.v`). -/
private theorem cycle_map {α β : Type*} {e : α → α → Prop} {f : β → α} {p : List β} :
    cycle e (p.map f) ↔ cycle (fun a b => e (f a) (f b)) p := by
  cases p with
  | nil => simp
  | cons x p =>
    rw [List.map_cons, cycle_cons, cycle_cons, ← path_map (f := f), List.map_append]
    rfl

/-- math-comp `eq_cycle`. -/
private theorem cycle_congr {α : Type*} {e e' : α → α → Prop} (h : ∀ a b, e a b ↔ e' a b)
    {p : List α} : cycle e p ↔ cycle e' p := by
  cases p with
  | nil => simp
  | cons x p => exact path_congr h

/-- A `cycle` version of `sub_path` restricted to the items of the cycle. -/
private theorem cycle_mono_mem {α : Type*} {e e' : α → α → Prop} {l : List α}
    (h : ∀ a b, a ∈ l → b ∈ l → e a b → e' a b) (hl : cycle e l) : cycle e' l := by
  cases l with
  | nil => trivial
  | cons x p =>
    have hm : ∀ y, y ∈ x :: (p ++ [x]) → y ∈ x :: p := by
      intro y hy
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy ⊢
      tauto
    exact path.mono_mem (fun a b ha hb hab => h a b (hm a ha) (hm b (List.mem_cons_of_mem _ hb))
      hab) hl

section MatteRings

variable {Nr : ℕ} (cm : CMatte Nr)

/-- Coq `gmring i` (`pmap insub (mring (cm i))`): the ring of the matte `cm i`, as a list of
darts of the box hypermap. -/
def gmring (i : Fin Nr) : List (GmDart (cmBbox cm)) :=
  (cm i).mring.filterMap fun d => if h : d ∈ gmgrid (cmBbox cm) then some ⟨d, h⟩ else none

variable {cm}

/-- The ring darts of the mattes are in the grid (not in Coq). -/
theorem mem_gmgrid_of_mring {i : Fin Nr} {d : GPoint} (hd : d ∈ (cm i).mring) :
    d ∈ gmgrid (cmBbox cm) :=
  (gmgridE _ d).2 (Or.inl (sub_cm_bbox cm i _ (mem_gborder.1 (((cm i).in_mring d).1 hd)).1))

private theorem filterMap_val {bb : GRect} (l : List GPoint) (hl : ∀ d ∈ l, d ∈ gmgrid bb) :
    (l.filterMap fun d => if h : d ∈ gmgrid bb then some (⟨d, h⟩ : GmDart bb) else none).map
      Subtype.val = l := by
  induction l with
  | nil => rfl
  | cons d l ih =>
    have hd := hl d List.mem_cons_self
    simp only [List.filterMap_cons, hd, dite_true, List.map_cons]
    rw [ih fun x hx => hl x (List.mem_cons_of_mem _ hx)]

variable (cm)

/-- Coq `val_gmring`. -/
theorem val_gmring (i : Fin Nr) : (gmring cm i).map Subtype.val = (cm i).mring :=
  filterMap_val _ fun _ hd => mem_gmgrid_of_mring hd

variable {cm}

/-- Membership in `gmring` (not in Coq). -/
theorem mem_gmring {i : Fin Nr} {u : GmDart (cmBbox cm)} :
    u ∈ gmring cm i ↔ u.1 ∈ (cm i).mring := by
  rw [← val_gmring cm i, List.mem_map_of_injective Subtype.val_injective]

variable (cm)

/-- Coq `gm_disk_def`: the disk of the ring of `cm i` lies in `cm i`. -/
theorem gm_disk_def (i : Fin Nr) :
    ∀ u, u ∈ (gmdartMap (cmBbox cm)).diskN (gmring cm i) → halfg u.1 ∈ cm i := by
  set H := gmdartMap (cmBbox cm)
  have key : ∀ v, halfg (H.node v).1 ∈ cm i → halfg v.1 ∈ cm i := fun v h => by
    have hn : H.node v ∈ gmInner (cmBbox cm) := sub_cm_bbox cm i _ h
    have hv : v ∈ gmInner (cmBbox cm) := ((gm_inner_closed _) v (H.node v) rfl).2 hn
    rwa [← halfg_gmnode hv]
  rintro u ⟨y, hy, hconn⟩
  induction hconn with
  | refl =>
    apply key
    rw [H.edgeK]
    exact (mem_gborder.1 (((cm i).in_mring _).1 (mem_gmring.1 hy))).1
  | @tail a b _ hbc ih =>
    obtain ⟨a'r, hab⟩ := hbc
    have hea : halfg (gedge a.1) ∈ cm i := by
      by_contra hc
      exact a'r (mem_gmring.2 (((cm i).in_mring _).2 (mem_gborder.2 ⟨ih, hc⟩)))
    rcases hab with e | e
    · apply key
      rw [← e]; exact ih
    · apply key
      have ha : a = H.edge (H.node b) := by rw [← e, H.faceK]
      rw [ha] at hea
      have e2 : (H.edge (H.node b)).1 = gedge (H.node b).1 := rfl
      rwa [e2, gedge2] at hea

/-- Coq `disjoint_gmdisk`. -/
theorem disjoint_gmdisk (cmP : CmProper cm) {i j : Fin Nr} (hij : i ≠ j) :
    Disjoint ((gmdartMap (cmBbox cm)).diskN (gmring cm i))
      ((gmdartMap (cmBbox cm)).diskN (gmring cm j)) :=
  Set.disjoint_left.2 fun u hi hj =>
    hij (cmP i j ⟨_, gm_disk_def cm j u hj, gm_disk_def cm i u hi⟩)

/-- Coq `gmring_cycle`: the matte rings are simple `rlink` cycles of the box hypermap. -/
theorem gmring_cycle (i : Fin Nr) :
    (gmdartMap (cmBbox cm)).SCycle (gmdartMap (cmBbox cm)).rlink (gmring cm i) := by
  set H := gmdartMap (cmBbox cm)
  have hnd : ((gmring cm i).map fun u => end0g u.1).Nodup := by
    have := (cm i).mring_simple
    rw [← val_gmring cm i, List.map_map] at this
    exact this
  refine ⟨?_, ?_⟩
  · have hc := (cm i).mring_cycle
    rw [← val_gmring cm i, cycle_map] at hc
    refine (cycle_congr fun a b => ?_).2 hc
    show H.cface (H.edge a) b ↔ mrlink a.1 b.1
    rw [cface_end0g, mrlink, gmdartMap_edge, val_gmEdge, end0g_edge]
  · refine List.Nodup.map_on (fun x hx y hy hxy => ?_) hnd.of_map
    rw [H.froot_face_eq_iff, cface_end0g] at hxy
    exact List.inj_on_of_nodup_map hnd hx hy hxy

end MatteRings

/-! ### Cutting out the mattes -/

section Cutout

variable {Nr : ℕ}

/-- Coq `gm_cutout E`: a planar hypermap `G` that is the remainder left by removing from
`gmdartMap (cmBbox cm)` the interior of all the mattes `cm i` for `i ∈ E`, alongside its
embedding `h` in `GmDart (cmBbox cm)` and the border rings `r i` of the removed mattes. -/
structure GmCutout (cm : CMatte Nr) (E : Finset (Fin Nr)) : Type 1 where
  /-- The dart type of the remainder map. -/
  D : Type
  /-- The dart type is finite. -/
  [fintype : Fintype D]
  /-- The dart type has decidable equality. -/
  [decEq : DecidableEq D]
  /-- The remainder map (Coq `G`). -/
  G : Hypermap D
  /-- The embedding in the box hypermap (Coq `h`). -/
  h : D → GmDart (cmBbox cm)
  /-- The border rings (Coq `r`). -/
  r : Fin Nr → List D
  /-- Coq `planar G`. -/
  planar : G.Planar
  /-- Coq `injective h`. -/
  inj : Injective h
  /-- Coq `{morph h : x / edge x}`. -/
  edge_morph : ∀ x, h (G.edge x) = (gmdartMap (cmBbox cm)).edge (h x)
  /-- Coq `{mono h : x y / cface x y}`. -/
  cface_mono : ∀ x y, (gmdartMap (cmBbox cm)).cface (h x) (h y) ↔ G.cface x y
  /-- Coq `{in [pred x | [forall i in E, x \notin r i]], {morph h : x / node x}}`. -/
  node_morph : ∀ x, (∀ i ∈ E, x ∉ r i) → h (G.node x) = (gmdartMap (cmBbox cm)).node (h x)
  /-- Coq `forall i, rev (map h (r i)) = gmring i`. -/
  map_ring : ∀ i, ((r i).map h).reverse = gmring cm i
  /-- Coq `{in E, forall i, ufcycle node (r i)}`. -/
  ucycle_node : ∀ i ∈ E, UCycle (frel G.node) (r i)

attribute [instance] GmCutout.fintype GmCutout.decEq

variable (cm : CMatte Nr)

/-- Coq `has_cutout`: all the mattes can be cut out of the box hypermap. -/
theorem has_cutout (cmP : CmProper cm) : Nonempty (GmCutout cm Finset.univ) := by
  classical
  suffices ∀ E : Finset (Fin Nr), Nonempty (GmCutout cm E) from this _
  have bbP := cmBbox_proper cm
  set H := gmdartMap (cmBbox cm)
  intro E
  induction E using Finset.induction_on with
  | empty =>
    exact ⟨{
      D := GmDart (cmBbox cm)
      G := H
      h := id
      r := fun i => (gmring cm i).reverse
      planar := gmdart_planar bbP
      inj := injective_id
      edge_morph := fun _ => rfl
      cface_mono := fun _ _ => Iff.rfl
      node_morph := fun _ _ => rfl
      map_ring := fun i => by simp
      ucycle_node := fun i hi => absurd hi (Finset.notMem_empty i) }⟩
  | insert j E jE IH =>
    obtain ⟨c⟩ := IH
    obtain ⟨D, G, h, r, planG, Ih, hE, hF, hN, Dr, cycNr⟩ := c
    have h_r : ∀ i x, h x ∈ gmring cm i ↔ x ∈ r i := fun i x => by
      rw [← Dr i, List.mem_reverse, List.mem_map_of_injective Ih]
    have cycRrj : G.SCycle G.rlink (r j).reverse := by
      have g := gmring_cycle cm j
      rw [← Dr j, ← List.map_reverse] at g
      refine ⟨?_, (simple_map hF _).1 g.2⟩
      have g1 := g.1
      rw [cycle_map] at g1
      refine (cycle_congr fun a b => ?_).1 g1
      show H.cface (H.edge (h a)) (h b) ↔ G.cface (G.edge a) b
      rw [← hE, hF]
    let mj : Set D := {x | h x ∈ H.diskN (gmring cm j)}
    have r'mj : ∀ i x, i ≠ j → x ∈ mj → x ∉ r i := fun i x hij hx hr =>
      Set.disjoint_left.1 (disjoint_gmdisk cm cmP hij)
        (H.mem_diskN_of_mem _ ((h_r i x).2 hr)) hx
    have mj_hN : ∀ x, x ∈ mj → h (G.node x) = H.node (h x) := fun x hx =>
      hN x fun i hi hr => r'mj i x (fun e => jE (e ▸ hi)) hx hr
    have mjN : Closed (frel G.node) mj := Closed.of_forward G.cnode_sym fun x y hxy hx => by
      rw [← hxy]
      show h (G.node x) ∈ H.diskN (gmring cm j)
      rw [mj_hN x hx]
      exact (H.diskN_node _ (h x) (H.node (h x)) rfl).1 hx
    have h_mj : ∀ x, x ∈ G.diskN (r j).reverse → x ∈ mj := by
      rintro x ⟨z, hz, hconn⟩
      induction hconn with
      | refl =>
        refine (mjN _ _ (G.edgeK z)).2 ?_
        exact H.mem_diskN_of_mem _ ((h_r j z).2 (List.mem_reverse.1 hz))
      | @tail a b _ hbc ih =>
        obtain ⟨a'r, hab⟩ := hbc
        rcases hab with e | e
        · exact (mjN b a e.symm).2 ih
        · have ha : a = G.edge (G.node b) := by rw [← e, G.faceK]
          have hdE : h a ∈ H.diskE (gmring cm j) :=
            ⟨ih, fun hr => a'r (List.mem_reverse.2 ((h_r j a).1 hr))⟩
          rw [ha, hE] at hdE
          have := ((H.diskE_edge (gmdart_planar bbP) (gmring_cycle cm j)) (h (G.node b)) _
            rfl).2 hdE
          exact (mjN b (G.node b) rfl).2 this.1
    have patch_j := G.snip_patch planG cycRrj
    set Gj := G.snipRem planG cycRrj
    set hj := G.snipr (r j).reverse
    let rj : Fin Nr → List (G.SniprDart (r j).reverse) := fun i =>
      preimSeq hj (r i).reverse.reverse
    have Drj : ∀ i, (rj i).map hj = r i := fun i => by
      show (preimSeq hj (r i).reverse.reverse).map hj = r i
      rw [map_preim, List.reverse_reverse]
      intro y hy
      rw [List.reverse_reverse] at hy
      rw [G.codom_snipr]
      rintro ⟨hdN, hnr⟩
      by_cases hij : i = j
      · subst hij; exact hnr (List.mem_reverse.2 hy)
      · exact r'mj i y hij (h_mj y hdN) hy
    have h_rj : ∀ i x, hj x ∈ r i ↔ x ∈ rj i := fun i x => by
      rw [← Drj i, List.mem_map_of_injective patch_j.injr]
    have hjF : ∀ x y, G.cface (hj x) (hj y) ↔ Gj.cface x y := fun x y =>
      (patch_j.patch_face_r x y).symm
    refine ⟨{
      D := G.SniprDart (r j).reverse
      G := Gj
      h := h ∘ hj
      r := rj
      planar := G.planar_snipr planG cycRrj
      inj := Ih.comp patch_j.injr
      edge_morph := ?_
      cface_mono := ?_
      node_morph := ?_
      map_ring := ?_
      ucycle_node := ?_ }⟩
    · intro x
      show h (hj (Gj.edge x)) = _
      rw [patch_j.edge_r, hE]
      rfl
    · intro x y
      exact (hF _ _).trans (hjF x y)
    · intro x hx
      have hx' : x ∉ G.sniprRing (r j).reverse := hx j (Finset.mem_insert_self j E)
      show h (hj (Gj.node x)) = _
      rw [patch_j.node_r x hx', hN]
      · rfl
      · intro i hi hr
        exact hx i (Finset.mem_insert_of_mem hi) ((h_rj i x).1 hr)
    · intro i
      show ((rj i).map (h ∘ hj)).reverse = _
      rw [← List.map_map, Drj, Dr]
    · intro i hi
      by_cases hij : i = j
      · subst hij
        exact patch_j.cycle_r
      · have hiE : i ∈ E := (Finset.mem_insert.1 hi).resolve_left hij
        obtain ⟨cyc, nd⟩ := cycNr i hiE
        refine ⟨?_, List.Nodup.of_map hj (by rw [Drj]; exact nd)⟩
        rw [← Drj i, cycle_map] at cyc
        refine cycle_mono_mem (fun a b ha _ hab => ?_) cyc
        have ha' : a ∉ rj j := fun haj => r'mj i (hj a) hij
          (h_mj _ (G.mem_diskN_of_mem _ (List.mem_reverse.2 ((h_rj j a).2 haj))))
          ((h_rj i a).2 ha)
        apply patch_j.injr
        rw [patch_j.node_r a ha']
        exact hab

/-- The cutout chosen by `has_cutout`. -/
noncomputable def gmCutout (cmP : CmProper cm) : GmCutout cm Finset.univ :=
  Classical.choice (has_cutout cm cmP)

variable {cm}

/-- The remainder map of a cutout of all the mattes is loopless (the main step of Coq's
`planar_bridgeless_grid_map`). -/
theorem GmCutout.loopless (c : GmCutout cm Finset.univ) : c.G.Loopless := by
  set H := gmdartMap (cmBbox cm)
  have h_r : ∀ i x, c.h x ∈ gmring cm i ↔ x ∈ c.r i := fun i x => by
    rw [← c.map_ring i, List.mem_reverse, List.mem_map_of_injective c.inj]
  have main : ∀ x, c.h x ∈ gmInner (cmBbox cm) → ¬ c.G.cnode x (c.G.edge x) := by
    intro x hx xNex
    by_cases hr : ∃ i, x ∈ c.r i
    · obtain ⟨i, hi⟩ := hr
      obtain ⟨cyc, -⟩ := c.ucycle_node i (Finset.mem_univ i)
      have hei : c.G.edge x ∈ c.r i := (fconnect_cycle cyc hi).1 xNex
      have m1 : (c.h x).1 ∈ (cm i).mring := mem_gmring.1 ((h_r i x).2 hi)
      have m2 : gedge (c.h x).1 ∈ (cm i).mring := by
        have := mem_gmring.1 ((h_r i _).2 hei)
        rwa [c.edge_morph] at this
      exact mring_edge (cm i) m1 m2
    · push Not at hr
      obtain ⟨n, hn⟩ := fconnect_iff_iterate.1 xNex
      have key : ∀ k y, c.h y ∈ gmInner (cmBbox cm) → (∀ i, y ∉ c.r i) →
          c.h (c.G.node^[k] y) ∈ gmInner (cmBbox cm) ∧
            halfg (c.h (c.G.node^[k] y)).1 = halfg (c.h y).1 := by
        intro k
        induction k with
        | zero => intro y hy _; exact ⟨hy, rfl⟩
        | succ k ih =>
          intro y hy hry
          obtain ⟨h1, h2⟩ := ih y hy hry
          have hz : ∀ i, c.G.node^[k] y ∉ c.r i := fun i hz =>
            hry i ((fconnect_cycle (c.ucycle_node i (Finset.mem_univ _)).1 hz).1
              (c.G.cnodeC.1 (fconnect_iterate _ y k)))
          rw [iterate_succ_apply', c.node_morph _ fun i _ => hz i]
          exact ⟨gm_inner_node h1, by rw [halfg_gmnode h1, h2]⟩
      have := (key n x hx hr).2
      rw [hn, c.edge_morph] at this
      exact neq_halfg_edge _ this.symm
  rintro ⟨x, xNex⟩
  by_cases hx : c.h x ∈ gmInner (cmBbox cm)
  · exact main x hx xNex
  · have hex : c.h (c.G.edge x) ∈ gmInner (cmBbox cm) := by
      rw [c.edge_morph]
      exact ((gmgridE _ _).1 (c.h x).2).resolve_left hx
    apply main _ hex
    have e2 : c.G.edge (c.G.edge x) = x :=
      c.inj (by rw [c.edge_morph, c.edge_morph]; exact gmedge2 _)
    rw [e2]
    exact c.G.cnodeC.1 xNex

/-- A function invariant under `f` is constant on the `f`-orbits (math-comp
`fconnect_invariant`). -/
private theorem fconnect_invariant' {α β : Type*} {f : α → α} {k : α → β}
    (hk : ∀ x, k (f x) = k x) {x y : α} (h : fconnect f x y) : k y = k x := by
  induction h with
  | refl => rfl
  | tail _ hbc ih => rw [← hbc, hk, ih]

/-- The index in `Fin 4` of a color (Coq `index (k x) [:: Color0; Color1; Color2]`). -/
def colorIndex : Color → Fin 4
  | Color0 => 0
  | Color1 => 1
  | Color2 => 2
  | Color3 => 3

/-- `colorIndex` is injective. -/
theorem colorIndex_injective : Injective colorIndex := by
  intro a b h
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- A four coloring of the dual of a cutout of all the mattes gives a four coloring of the
mattes that separates adjacent mattes (the main step of Coq's `grid_map_coloring`). -/
theorem GmCutout.colorable (c : GmCutout cm Finset.univ) (hcol : c.G.dual.FourColorable) :
    ∃ k : Fin Nr → Fin 4, ∀ i j, Madj (cm i) (cm j) → k i ≠ k j := by
  classical
  obtain ⟨k, kE, kN⟩ := (c.G.four_colorable_dual).1 hcol
  have k_r : ∀ i x y, x ∈ c.r i → y ∈ c.r i → k y = k x := fun i x y hx hy =>
    fconnect_invariant' kN ((fconnect_cycle (c.ucycle_node i (Finset.mem_univ _)).1 hx).2 hy)
  let k' : Fin Nr → Fin 4 := fun i =>
    if h : ∃ x, x ∈ c.r i then colorIndex (k h.choose) else 0
  have k'_eq : ∀ i x, x ∈ c.r i → k' i = colorIndex (k x) := fun i x hx => by
    have h : ∃ x, x ∈ c.r i := ⟨x, hx⟩
    simp only [k', h, dite_true]
    rw [k_r i x _ hx h.choose_spec]
  refine ⟨k', fun i j hadj => ?_⟩
  obtain ⟨d, hd, hed⟩ := hadj
  have hu : (⟨d, mem_gmgrid_of_mring hd⟩ : GmDart (cmBbox cm)) ∈ gmring cm j := mem_gmring.2 hd
  rw [← c.map_ring j, List.mem_reverse, List.mem_map] at hu
  obtain ⟨x, hx, hxu⟩ := hu
  have hex : c.h (c.G.edge x) ∈ gmring cm i := by
    rw [c.edge_morph, hxu]
    exact mem_gmring.2 hed
  rw [← c.map_ring i, List.mem_reverse, List.mem_map_of_injective c.inj] at hex
  rw [k'_eq i _ hex, k'_eq j x hx]
  exact fun h => kE x (colorIndex_injective h)

end Cutout

/-! ### The grid map -/

section GridMapDef

variable {Nr : ℕ} {ab0 : AdjBox Nr} {cm0 : CMatte Nr}

/-- The dart type of `gridMapOf` (the dart type of the remainder map of Coq's `has_cutout`). -/
abbrev gridMapOfDart (ab0P : AbProper ab0) (cm0P : CmProper cm0)
    (abcm0P : ∀ e i, AbCmProper ab0 cm0 e i) : Type :=
  (gmCutout (cmExtend ab0P cm0P abcm0P) (cmExtend_proper ab0P cm0P abcm0P)).D

/-- Coq `grid_map ab0P cm0P abcm0P` (named `gridMapOf`, since `gridMap` is the infinite grid
hypermap of `FourColor.Grid`): the dual of the remainder map of the box hypermap of the
extended mattes, once all the mattes have been cut out. -/
noncomputable def gridMapOf (ab0P : AbProper ab0) (cm0P : CmProper cm0)
    (abcm0P : ∀ e i, AbCmProper ab0 cm0 e i) : Hypermap (gridMapOfDart ab0P cm0P abcm0P) :=
  (gmCutout (cmExtend ab0P cm0P abcm0P) (cmExtend_proper ab0P cm0P abcm0P)).G.dual

/-- Coq `planar_bridgeless_grid_map`. -/
theorem planar_bridgeless_grid_map (ab0P : AbProper ab0) (cm0P : CmProper cm0)
    (abcm0P : ∀ e i, AbCmProper ab0 cm0 e i) : (gridMapOf ab0P cm0P abcm0P).PlanarBridgeless := by
  set c := gmCutout (cmExtend ab0P cm0P abcm0P) (cmExtend_proper ab0P cm0P abcm0P)
  exact ⟨(c.G.planar_dual).2 c.planar, (c.G.bridgeless_dual).2 c.loopless⟩

/-- Coq `grid_map_coloring`: a four coloring of `gridMapOf` yields a four coloring of the matte
indices that separates the adjacencies witnessed by `ab0`. -/
theorem grid_map_coloring (ab0P : AbProper ab0) (cm0P : CmProper cm0)
    (abcm0P : ∀ e i, AbCmProper ab0 cm0 e i) (h4 : (gridMapOf ab0P cm0P abcm0P).FourColorable) :
    ∃ k : Fin Nr → Fin 4, ∀ e, GrProper (ab0 e) → k e.fst ≠ k e.snd := by
  obtain ⟨k, hk⟩ := GmCutout.colorable _ h4
  exact ⟨k, fun e he => hk _ _ (cmExtend_adj ab0P cm0P abcm0P e he)⟩

/-- `gridMapOf` packaged as an existential over a dart type with its instances (not in Coq; the
form used by `discretize_to_hypermap`). -/
theorem exists_grid_map (ab0P : AbProper ab0) (cm0P : CmProper cm0)
    (abcm0P : ∀ e i, AbCmProper ab0 cm0 e i) :
    ∃ (D : Type) (_ : Fintype D) (_ : DecidableEq D) (G : Hypermap D), G.PlanarBridgeless ∧
      (G.FourColorable → ∃ k : Fin Nr → Fin 4, ∀ e, GrProper (ab0 e) → k e.fst ≠ k e.snd) :=
  ⟨_, inferInstance, inferInstance, gridMapOf ab0P cm0P abcm0P,
    planar_bridgeless_grid_map ab0P cm0P abcm0P, grid_map_coloring ab0P cm0P abcm0P⟩

end GridMapDef

end FourColor
