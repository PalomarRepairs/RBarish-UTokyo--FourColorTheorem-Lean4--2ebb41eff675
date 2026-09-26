/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Grid
import Mathlib.Data.List.Rotate

/-!
# Mattes  (port of `matte.v`)

Mattes are finite sets of grid squares that are delimited by a simple grid ring; we explicitly
include the enumeration of the region and the ring.  Mattes will be used to define conservative
approximations of arbitrary connected open sets of points (regions).  We therefore need to
provide operations for extending a matte in order to improve the approximation.  This involves
three different operations:

* adding pixels within a specified rectangle that the matte meets, so that a specific pixel is
  covered;
* adding the pixels surrounding a grid point of the matte boundary;
* refining the grid to ensure that the two previous operations are safe.

Note that we can't add a large rectangle blindly to a matte if we want to preserve its
geometrical properties (we might end up with a disconnected contour).  We reduce the first two
operations above to two primitives that add a pixel that has exactly one or two consecutive
sides in common with the matte, respectively (more precisely, 2 or 3 consecutive vertices in
common with the matte contour vertices).  We don't actually provide the second operation here,
because it requires multiple grid refinements.  Instead we provide a basic step that needs to
be iterated to accomplish the operation, along with the metric (`mcorner`) that decreases
with that step.

The main definitions in this file are:

* `mrlink d1 d2`   : the end of grid dart `d1` (interpreted as a directed grid edge, see
  `Grid.lean`) coincides with the start of grid dart `d2`.  This is the successor relation for
  the contour cycle of mattes.
* `d ∈ gborder m`  : `d` is a border edge of the collection `m` of pixels (a list of
  `GPoint`s): the pixel on the left of `d` interpreted as a directed edge (a.k.a. the pixel of
  `d`) lies in `m`, while the one on the right does not.
* `Matte`          : the representation of a simple grid polyomino.  An `m : Matte` comprises
  two somewhat redundant data:
  * `m.mdisk`      : a (nonempty) list comprising the pixels covered by `m`; `p ∈ m` means
    `p ∈ m.mdisk` (and `m` coerces to the region `inMatte m`);
  * `m.mring`      : the node-simple `mrlink`-cycle of darts tracing the counterclockwise
    border of `m`.
* `pointMatte p`   : the matte comprising the single pixel `p`, with `mdisk` `pmdisk p := [p]`
  and `mring` `pmring p`.
* `Madj m1 m2`     : `m1` and `m2` are adjacent: their respective borders contain converse
  directed edges, separating two pixels on the periphery of `m1` and `m2`.
* `CoarseIn r m`   : within the region `r`, the matte `m` is the binary refinement of a coarser
  region: for all `p ∈ r`, `p ∈ m` depends only on `halfg p`.
* `refineMatte m`  : the matte that covers exactly the subpixels of `m` in the binary
  refinement of the grid pixels, with `mdisk` `refineMdisk` and `mring` `refineMring`.
* `ehex d`         : the 3x2 rectangle covering the pixel of the dart `d` and the five pixels
  adjacent to it that are in the half-plane to the left of `d` interpreted as a directed edge.
* `equad d`        : the 2x2 square covering the pixel of the dart `d` and the three pixels
  adjacent to it that are in the quadrant that is both left of `d` and of `gface d` (the next
  edge after `d` in the counter-clockwise border of the pixel of `d`).
* `Ext1Hex m d`    : `m` contains the pixel to the right of `d` and none of the pixels in
  `ehex d`.
* `ext1Matte m d h`: the matte extending a matte `m` with the pixel `p` of a dart `d`, given a
  proof `h` of `Ext1Hex m d`, which implies `p` is outside `m` and touches the border of `m` on
  exactly one side, at `d`.  Its `mdisk` is `extMdisk m d := p :: m.mdisk` and its `mring` is
  `ext1Mring m d`.
* `Ext2Quad m d`   : `m` contains the pixels to the right of both `d` and `gface d`, but none
  of the pixels in `equad d`.
* `ext2Matte m d h`: the matte extending a matte `m` with the pixel `p` of a dart `d`, given a
  proof `h` of `Ext2Quad m d`, which implies `p` is outside `m` and touches the border of `m` on
  exactly two consecutive sides, at `d` and `gface d`.  Its `mdisk` is `extMdisk m d` and its
  `mring` is `ext2Mring m d`.
* `MatteExtension m xm` : inductive (indexed) predicate asserting that there is a sequence of
  mattes from `m` to `xm` in which each matte differs from the next by the addition of exactly
  ONE adjacent pixel.  We use induction on this predicate to obtain an extension that is
  adjacent to a given matte.
* `ExtendsIn m r p`: there is some `MatteExtension xm` of `m` that contains `p` and only
  extends `m` inside the rectangle `r`; we show this holds whenever `m` is coarse in `r`, `m`
  meets `r`, and `p` is strictly inside `r` (i.e., in `inset r`).
* `mcorner m q`    : the number of pixels incident to grid node `q` that are NOT in the matte
  `m`, other than (upper right) pixel `q`, with the upper left and lower right pixels counted
  twice and the lower left pixel counted only once.  The asymmetry of this definition reflects
  the asymmetry of the extent of a pixel in the real plane, which includes only the lower left
  corner and edges.  Thus, when `p ∈ m` and `mcorner m p = 0` all of the pixel `p`, including
  the grid point `p` and edges incident to `p`, lie in the interior of the extent of the matte
  `m`.  If `mcorner m p > 0`, for any dart `q` of `p`, viewed as a subpixel of `p`, we can
  construct an extension `xm` of `refineMatte m` such that `mcorner xm q < mcorner m p`.

## Translation notes

* Boolean predicates become `Prop`s (`mrlink`, `Madj`, `CoarseIn`, `Ext1Hex`, `Ext2Quad`);
  `has a s` becomes `∃ p ∈ s, p ∈ a`, `=i` a pointwise `↔`, `{subset a <= b}` an implication.
* Coq's `matte_extension` and `extends_in` are `Type`-valued (so that `extend_madj` and
  `refine_mcorner` can return `sig` types); here `MatteExtension` and `ExtendsIn` are `Prop`s,
  and `extend_madj`, `refine_mcorner` state existence (`∃ xm, ...`).
* Coq defines `ext1_mring` and `ext2_mring` inside sections assuming `ext1_hex m d`
  (resp. `ext2_quad m d`), by destructing the opaque rotation lemmas `rot_to` and `ext2_P`.
  Here `ext1Mring m d` and `ext2Mring m d` are total, computable functions that use the same
  rotation (`List.rotate` by the index of `gedge d`, resp. `gedge (gface d)`, which agrees with
  math-comp's `rot` since the index is in range); `ext2_P` states the corresponding rotation
  property.  The section-local `Let`s of the Coq file become private lemmas.
-/

namespace FourColor

open Function GPoint

/-! ### Contours and mattes -/

/-- Coq `mrlink d1 d2`: the end of the directed edge `d1` is the start of `d2`. -/
def mrlink (d1 d2 : GPoint) : Prop := end1g d1 = end0g d2

/-- Coq `gborder m`: the darts whose pixel is in `m` while the pixel across their edge is not. -/
def gborder (m : List GPoint) : GRegion := {d | halfg d ∈ m ∧ halfg (gedge d) ∉ m}

/-- Membership in `gborder m`, explicitly. -/
theorem mem_gborder {m : List GPoint} {d : GPoint} :
    d ∈ gborder m ↔ halfg d ∈ m ∧ halfg (gedge d) ∉ m := Iff.rfl

/-- Coq `matte`: a simple grid polyomino, given by its pixels and its border ring. -/
structure Matte where
  /-- Coq `mdisk`: the pixels covered by the matte. -/
  mdisk : List GPoint
  /-- Coq `mring`: the counterclockwise contour of the matte. -/
  mring : List GPoint
  /-- Coq `matte_ne`. -/
  matte_ne : mdisk ≠ []
  /-- Coq `mring_cycle`. -/
  mring_cycle : cycle mrlink mring
  /-- Coq `mring_simple`. -/
  mring_simple : (mring.map end0g).Nodup
  /-- Coq `in_mring`. -/
  in_mring : ∀ d, d ∈ mring ↔ d ∈ gborder mdisk

/-- `p ∈ m` for a matte `m` means `p ∈ m.mdisk` (Coq coercions `mdisk :> seq gpoint` and
`in_matte`). -/
instance : Membership GPoint Matte := ⟨fun m p => p ∈ m.mdisk⟩

/-- Membership in a matte is membership in its `mdisk`. -/
theorem mem_matte {m : Matte} {p : GPoint} : p ∈ m ↔ p ∈ m.mdisk := Iff.rfl

instance (m : Matte) (p : GPoint) : Decidable (p ∈ m) :=
  inferInstanceAs (Decidable (p ∈ m.mdisk))

/-- Coq coercion `in_matte : matte >-> pred gpoint`. -/
def inMatte (m : Matte) : GRegion := {p | p ∈ m}

instance : Coe Matte GRegion := ⟨inMatte⟩

/-- Membership in the region of a matte. -/
@[simp] theorem mem_inMatte {m : Matte} {p : GPoint} : p ∈ (m : GRegion) ↔ p ∈ m := Iff.rfl

/-- Coq `mring_edge`. -/
theorem mring_edge (m : Matte) {p : GPoint} (h : p ∈ m.mring) : gedge p ∉ m.mring := by
  rw [m.in_mring, mem_gborder] at h ⊢
  exact fun h' => h.2 h'.1

/-- Coq `mring_uniq`. -/
theorem mring_uniq (m : Matte) : m.mring.Nodup := List.Nodup.of_map end0g m.mring_simple

/-! ### Matte adjacency -/

/-- Coq `madj m1 m2`: some border edge of `m2` is the converse of a border edge of `m1`. -/
def Madj (m1 m2 : Matte) : Prop := ∃ d ∈ m2.mring, gedge d ∈ m1.mring

/-- Coq `madj_sym`. -/
theorem madj_sym {m1 m2 : Matte} : Madj m1 m2 ↔ Madj m2 m1 := by
  constructor <;> rintro ⟨d, hd, hed⟩ <;> exact ⟨gedge d, hed, by rwa [gedge2]⟩

/-- Coq `madj_irrefl`. -/
theorem madj_irrefl (m : Matte) : ¬ Madj m m := by
  rintro ⟨d, hd, hed⟩
  exact mring_edge m hd hed

/-! ### Initial single-square matte -/

section PointMatte

variable (p : GPoint)

/-- Coq `pmdisk p`. -/
def pmdisk : List GPoint := [p]

/-- Coq `pmring p`: the four darts of the pixel `p`. -/
def pmring : List GPoint := List.iterate gface (2 • p) 4

/-- Coq `pmatte_ne`. -/
theorem pmatte_ne : pmdisk p ≠ [] := List.cons_ne_nil _ _

/-- Coq `pmring_cycle`. -/
theorem pmring_cycle : cycle mrlink (pmring p) := by
  simp only [pmring, List.iterate, cycle_cons, List.cons_append, List.nil_append, path_cons,
    path_nil, mrlink, and_true]
  refine ⟨(end0g_face _).symm, (end0g_face _).symm, (end0g_face _).symm, ?_⟩
  rw [← end0g_face, gface4]

/-- Coq `pmring_simple`. -/
theorem pmring_simple : ((pmring p).map end0g).Nodup := by
  simp only [pmring, List.iterate, List.map_cons, List.map_nil, end0g_face]
  simp only [end0g, end1g, halfg_face, oddg_face, halfg_double, oddg_double]
  simp [List.nodup_cons, ccw, GPoint.ext_iff]

/-- Coq `in_pmring`. -/
theorem in_pmring (d : GPoint) : d ∈ pmring p ↔ halfg d = p := by
  constructor
  · intro h
    rw [pmring, List.mem_iterate] at h
    obtain ⟨k, _, rfl⟩ := h
    rw [halfg_iter_face, halfg_double]
  · intro h
    apply same_halfg
    rw [halfg_double, h]

/-- Coq `pmring_def`. -/
theorem pmring_def (d : GPoint) : d ∈ pmring p ↔ d ∈ gborder (pmdisk p) := by
  rw [in_pmring, mem_gborder, pmdisk, List.mem_singleton, List.mem_singleton]
  constructor
  · intro h
    exact ⟨h, fun h' => neq_halfg_edge d (h.trans h'.symm)⟩
  · exact fun h => h.1

/-- Coq `point_matte p`: the matte made of the single pixel `p`. -/
def pointMatte : Matte :=
  ⟨pmdisk p, pmring p, pmatte_ne p, pmring_cycle p, pmring_simple p, pmring_def p⟩

end PointMatte

/-! ### Grid refinement for mattes -/

section RefineMatte

/-- Coq `coarse_in r m`: within the region `r`, membership in `m` only depends on `halfg`. -/
def CoarseIn (r : GRegion) (m : Matte) : Prop :=
  ∀ p q, p ∈ r → halfg q = halfg p → (q ∈ m ↔ p ∈ m)

/-- Coq `refine_mring mr`: each dart `d` of `mr` is replaced by the two subdarts
`[d *+ 2 + oddg d, gface d *+ 2 + oddg d]` that cover its edge in the refined grid. -/
def refineMring (mr : List GPoint) : List GPoint :=
  mr.flatMap fun d => [d, gface d].map fun p => 2 • p + oddg d

/-- Coq `refine_mdisk md`: the subpixels of the pixels in `md`. -/
def refineMdisk (md : List GPoint) : List GPoint := md.flatMap pmring

/-- Coq `in_refine_mdisk`. -/
theorem in_refine_mdisk (md : List GPoint) (p : GPoint) :
    p ∈ refineMdisk md ↔ halfg p ∈ md := by
  rw [refineMdisk, List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, hp⟩
    rw [in_pmring] at hp
    rw [hp]
    exact hx
  · intro h
    exact ⟨halfg p, h, (in_pmring _ _).2 rfl⟩

variable (m : Matte)

/-- Coq `refine_matte_ne`. -/
theorem refine_matte_ne : refineMdisk m.mdisk ≠ [] := by
  obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ m.matte_ne
  intro h
  have : 2 • x ∈ refineMdisk m.mdisk := (in_refine_mdisk _ _).2 (by rwa [halfg_double])
  rw [h] at this
  exact List.not_mem_nil this

private theorem add_oddg_eq (x : GPoint) : x + oddg x = 2 • end0g x := by
  have := end0g_eq x
  rw [sub_eq_iff_eq_add] at this
  exact this.symm

private theorem refine_link1 {d1 d2 : GPoint} (h : mrlink d1 d2) :
    mrlink (2 • gface d1 + oddg d1) (2 • d2 + oddg d2) := by
  unfold mrlink at h ⊢
  rw [end1g, end0g, halfg_eq _ (oddgP _), oddg_eq _ (oddgP _), halfg_eq _ (oddgP _),
    oddg_eq _ (oddgP _), ← oddg_face, add_oddg_eq, add_oddg_eq, end0g_face, h]

private theorem refine_link2 (d : GPoint) :
    mrlink (2 • d + oddg d) (2 • gface d + oddg d) := by
  unfold mrlink
  rw [end1g, end0g, halfg_eq _ (oddgP _), oddg_eq _ (oddgP _), halfg_eq _ (oddgP _),
    oddg_eq _ (oddgP _), unlock_gface, arcg, add_assoc, sub_add_cancel]

private theorem refine_path {d1 : GPoint} {mr : List GPoint} (h : path mrlink d1 mr) :
    path mrlink (2 • gface d1 + oddg d1) (refineMring mr) := by
  induction mr generalizing d1 with
  | nil => trivial
  | cons d2 mr ih =>
    obtain ⟨h12, h2⟩ := h
    exact ⟨refine_link1 h12, refine_link2 d2, ih h2⟩

private theorem refine_last (d0 : GPoint) (mr0 : List GPoint) (x : GPoint) :
    last x (refineMring (d0 :: mr0)) =
      2 • gface (last d0 mr0) + oddg (last d0 mr0) := by
  induction mr0 generalizing d0 x with
  | nil => rfl
  | cons d1 mr1 ih =>
    rw [last_cons, ← ih d1 (2 • gface d0 + oddg d0)]
    rfl

/-- Coq `refine_mring_cycle`. -/
theorem refine_mring_cycle : cycle mrlink (refineMring m.mring) := by
  have hc := m.mring_cycle
  rcases h : m.mring with _ | ⟨d0, mr0⟩
  · exact trivial
  · rw [h, cycle_iff_path d0, last_cons] at hc
    rw [cycle_iff_path d0, refine_last]
    exact refine_path hc

/-- Coq `in_refine_mring`. -/
theorem in_refine_mring (mr : List GPoint) (d : GPoint) :
    d ∈ refineMring mr ↔
      ∃ d0, (d0 ∈ mr ∧ oddg d = oddg d0) ∧ (halfg d = d0 ∨ halfg d = gface d0) := by
  simp only [refineMring, List.mem_flatMap, List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨d0, hd0, rfl | rfl⟩
    · exact ⟨d0, ⟨hd0, oddg_eq _ (oddgP d0)⟩, Or.inl (halfg_eq _ (oddgP d0))⟩
    · exact ⟨d0, ⟨hd0, oddg_eq _ (oddgP d0)⟩, Or.inr (halfg_eq _ (oddgP d0))⟩
  · rintro ⟨d0, ⟨hd0, ho⟩, hh | hh⟩
    · exact ⟨d0, hd0, Or.inl (by rw [← ho, ← hh, halfgK])⟩
    · exact ⟨d0, hd0, Or.inr (by rw [← ho, ← hh, halfgK])⟩

private theorem refine_simple_aux1 {d d0 : GPoint} (h : d + oddg d = gface d0 + oddg d0) :
    False := by
  have hx := congrArg GPoint.x h
  have hy := congrArg GPoint.y h
  simp only [add_x, add_y, oddg_x, oddg_y, gface_x, gface_y] at hx hy
  omega

private theorem refine_simple_aux2 {d d0 : GPoint} (hne1 : gedge d0 ≠ d)
    (hne2 : end0g d ≠ end0g d0) (h : gface d + oddg d = gface d0 + oddg d0) : False := by
  have hx := congrArg GPoint.x h
  have hy := congrArg GPoint.y h
  rw [Ne, GPoint.ext_iff] at hne1 hne2
  simp only [add_x, add_y, oddg_x, oddg_y, gface_x, gface_y] at hx hy
  simp only [gedge_x, gedge_y, end0g_x, end0g_y] at hne1 hne2
  omega

private theorem refine_mring_simple_aux (r : List GPoint) (hr : (r.map end0g).Nodup)
    (hE : ∀ p ∈ r, gedge p ∉ r) : ((refineMring r).map end0g).Nodup := by
  induction r with
  | nil => exact List.nodup_nil
  | cons d r ih =>
    rw [List.map_cons, List.nodup_cons] at hr
    have hE' : ∀ p ∈ r, gedge p ∉ r := fun p hp hp' =>
      hE p (List.mem_cons_of_mem _ hp) (List.mem_cons_of_mem _ hp')
    have hEd : ∀ p ∈ r, gedge p ≠ d := fun p hp hp' =>
      hE p (List.mem_cons_of_mem _ hp) (hp' ▸ List.mem_cons_self)
    have ih' := ih hr.2 hE'
    have e1 : end0g (2 • d + oddg d) = d + oddg d := by
      rw [end0g, halfg_eq _ (oddgP _), oddg_eq _ (oddgP _)]
    have e2 : end0g (2 • gface d + oddg d) = gface d + oddg d := by
      rw [end0g, halfg_eq _ (oddgP _), oddg_eq _ (oddgP _)]
    have hmem : ∀ z, z ∈ (refineMring r).map end0g →
        ∃ d0 ∈ r, z = d0 + oddg d0 ∨ z = gface d0 + oddg d0 := by
      intro z hz
      rw [List.mem_map] at hz
      obtain ⟨d1, hd1, rfl⟩ := hz
      obtain ⟨d0, ⟨hd0, ho⟩, hh | hh⟩ := (in_refine_mring r d1).1 hd1
      · exact ⟨d0, hd0, Or.inl (by rw [end0g, hh, ho])⟩
      · exact ⟨d0, hd0, Or.inr (by rw [end0g, hh, ho])⟩
    show ((2 • d + oddg d) :: (2 • gface d + oddg d) :: refineMring r).map end0g |>.Nodup
    rw [List.map_cons, List.map_cons, e1, e2, List.nodup_cons, List.nodup_cons,
      List.mem_cons]
    refine ⟨?_, ?_, ih'⟩
    · rintro (h | h)
      · have := congrArg oddg (add_right_cancel h)
        rw [oddg_face] at this
        exact neq_ccw _ this.symm
      · obtain ⟨d0, hd0, h0 | h0⟩ := hmem _ h
        · apply hr.1
          rw [List.mem_map]
          refine ⟨d0, hd0, ?_⟩
          rw [← halfg_add_odd, ← halfg_add_odd, h0]
        · exact refine_simple_aux1 h0
    · intro h
      obtain ⟨d0, hd0, h0 | h0⟩ := hmem _ h
      · exact refine_simple_aux1 h0.symm
      · refine refine_simple_aux2 (hEd d0 hd0) (fun he => hr.1 ?_) h0
        rw [List.mem_map]
        exact ⟨d0, hd0, he.symm⟩

/-- Coq `refine_mring_simple`. -/
theorem refine_mring_simple : ((refineMring m.mring).map end0g).Nodup :=
  refine_mring_simple_aux _ m.mring_simple fun _ hp => mring_edge m hp

private theorem halfg_halfg_edge {d d1 : GPoint} (ho : oddg d = oddg d1)
    (hh : halfg d = d1 ∨ halfg d = gface d1) : halfg (halfg (gedge d)) = halfg (gedge d1) := by
  rw [GPoint.ext_iff] at ho
  simp only [oddg_x, oddg_y] at ho
  rcases Int.emod_two_eq d1.x with h1 | h1 <;> rcases Int.emod_two_eq d1.y with h2 | h2 <;>
  rcases hh with hh | hh <;> rw [GPoint.ext_iff] at hh <;>
    simp only [halfg_x, halfg_y, gface_x, gface_y] at hh <;>
    ext <;> simp only [halfg_x, halfg_y, gedge_x, gedge_y] <;> omega

private theorem oddg_halfg_of_edge {d : GPoint}
    (h : halfg (halfg (gedge d)) ≠ halfg (halfg d)) :
    oddg (halfg d) = oddg d ∨ oddg (halfg d) = ccw (oddg d) := by
  rw [Ne, GPoint.ext_iff] at h
  simp only [halfg_x, halfg_y, gedge_x, gedge_y] at h
  simp only [GPoint.ext_iff, oddg_x, oddg_y, halfg_x, halfg_y, ccw_x, ccw_y]
  omega

/-- Coq `refine_mring_def`. -/
theorem refine_mring_def (d : GPoint) :
    d ∈ refineMring m.mring ↔ d ∈ gborder (refineMdisk m.mdisk) := by
  rw [mem_gborder, in_refine_mdisk, in_refine_mdisk, in_refine_mring]
  constructor
  · rintro ⟨d1, ⟨hd1, ho⟩, hh⟩
    rw [m.in_mring, mem_gborder] at hd1
    have e1 : halfg (halfg d) = halfg d1 := by
      rcases hh with hh | hh <;> rw [hh]
      rw [halfg_face]
    rw [e1, halfg_halfg_edge ho hh]
    exact hd1
  · rintro ⟨h1, h2⟩
    have hne : halfg (halfg (gedge d)) ≠ halfg (halfg d) := fun h => h2 (h ▸ h1)
    have ho : oddg d = oddg (2 • halfg (halfg d) + oddg d) := (oddg_eq _ (oddgP d)).symm
    have hh : halfg d = 2 • halfg (halfg d) + oddg d ∨
        halfg d = gface (2 • halfg (halfg d) + oddg d) := by
      rw [gface_def, halfg_eq _ (oddgP d), oddg_eq _ (oddgP d)]
      rcases oddg_halfg_of_edge hne with h | h
      · left; conv_lhs => rw [← halfgK (halfg d)]
        rw [h]
      · right; conv_lhs => rw [← halfgK (halfg d)]
        rw [h]
    refine ⟨_, ⟨?_, ho⟩, hh⟩
    rw [m.in_mring, mem_gborder, halfg_eq _ (oddgP d), ← halfg_halfg_edge ho hh]
    exact ⟨h1, h2⟩

/-- Coq `refine_matte m`: the refinement of the matte `m`. -/
def refineMatte : Matte :=
  ⟨refineMdisk m.mdisk, refineMring m.mring, refine_matte_ne m, refine_mring_cycle m,
    refine_mring_simple m, refine_mring_def m⟩

/-- Coq `in_refine_matte`. -/
theorem in_refine_matte (p : GPoint) : p ∈ refineMatte m ↔ halfg p ∈ m :=
  in_refine_mdisk _ _

/-- Coq `refine_matte_coarse`. -/
theorem refine_matte_coarse (r : GRegion) : CoarseIn r (refineMatte m) := by
  intro p q _ hq
  rw [in_refine_matte, in_refine_matte, hq]

end RefineMatte

/-! ### Extending mattes -/

section ExtendMatte

/-- Case analysis on `oddg q`, with the corresponding parities of the coordinates of `q`. -/
private theorem oddg_cases_coord (q : GPoint) :
    (oddg q = ⟨0, 0⟩ ∧ q.x % 2 = 0 ∧ q.y % 2 = 0) ∨ (oddg q = ⟨0, 1⟩ ∧ q.x % 2 = 0 ∧ q.y % 2 = 1) ∨
    (oddg q = ⟨1, 1⟩ ∧ q.x % 2 = 1 ∧ q.y % 2 = 1) ∨ (oddg q = ⟨1, 0⟩ ∧ q.x % 2 = 1 ∧ q.y % 2 = 0) := by
  rcases Int.emod_two_eq q.x with hx | hx <;> rcases Int.emod_two_eq q.y with hy | hy <;>
    simp [GPoint.ext_iff, hx, hy]

/-- The start and end of the edge of a dart are distinct. -/
private theorem end0g_ne_end1g (e : GPoint) : end0g e ≠ end1g e := by
  intro h
  exact neq_ccw (oddg e) (add_left_cancel h).symm

/-- math-comp `rot_to` (in the form used here): rotating `s` by the index of `x ∈ s` brings
`x` to the head. -/
private theorem rot_to {s : List GPoint} {x : GPoint} (h : x ∈ s) :
    s.rotate (s.idxOf x) = x :: (s.rotate (s.idxOf x)).tail := by
  have hi : s.idxOf x < s.length := List.idxOf_lt_length_of_mem h
  rw [List.rotate_eq_drop_append_take hi.le, List.drop_eq_getElem_cons hi, List.getElem_idxOf hi]
  rfl

/-- math-comp `rot_cycle` (private copy; `FourColor.Geometry` is not imported here). -/
private theorem cycle_rotate_one' {e : GPoint → GPoint → Prop} (x : GPoint) (p : List GPoint) :
    cycle e (p ++ [x]) ↔ cycle e (x :: p) := by
  cases p with
  | nil => exact Iff.rfl
  | cons y p =>
    rw [List.cons_append, cycle_cons, cycle_cons, path_concat, path_concat, last_concat,
      List.cons_append, path_cons, path_concat]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h3, h1, h2⟩
    · rintro ⟨h3, h1, h2⟩
      exact ⟨⟨h1, h2⟩, h3⟩

private theorem cycle_rotate' {e : GPoint → GPoint → Prop} (n : ℕ) (p : List GPoint) :
    cycle e (p.rotate n) ↔ cycle e p := by
  rw [List.rotate_eq_rotate']
  induction n generalizing p with
  | zero => rw [List.rotate'_zero]
  | succ n ih =>
    cases p with
    | nil => rw [List.rotate'_nil]
    | cons a l => rw [List.rotate'_cons_succ, ih, cycle_rotate_one']

/-- `mrlink` only depends on the end of its first argument and the start of its second. -/
private theorem path_mrlink_congr {a a' b b' : GPoint} (ha : end1g a = end1g a')
    (hb : end0g b = end0g b') (R : List GPoint) :
    path mrlink a (R ++ [b]) ↔ path mrlink a' (R ++ [b']) := by
  rw [path_concat, path_concat]
  cases R with
  | nil => simp only [path_nil, last_nil, mrlink, ha, hb, true_and]
  | cons d1 R =>
    simp only [path_cons, last_cons, mrlink, ha, hb]

variable (m : Matte)

/-- Coq `ext_mdisk m d`: the pixels of `m` and the pixel of `d`. -/
def extMdisk (d : GPoint) : List GPoint := halfg d :: m.mdisk

/-- Membership in `extMdisk m d`, explicitly. -/
theorem mem_extMdisk {d p : GPoint} : p ∈ extMdisk m d ↔ p = halfg d ∨ p ∈ m :=
  List.mem_cons

/-- Coq `ext_mdisk_ne`. -/
theorem ext_mdisk_ne (d : GPoint) : extMdisk m d ≠ [] := List.cons_ne_nil _ _

/-- Coq `ehex d`: the 3x2 rectangle of the pixels touching the pixel of `d` on its left side. -/
def ehex (d : GPoint) : GRect := gchopRect (gtouch (halfg d)) d

/-- Coq `equad d`: the 2x2 square of the pixels touching the pixel of `d` on the left of both
`d` and `gface d`. -/
def equad (d : GPoint) : GRect := gchopRect (ehex d) (gface d)

/-- Membership in `ehex d`, explicitly. -/
theorem mem_ehex {d p : GPoint} : p ∈ ehex d ↔ p ∈ gtouch (halfg d) ∧ p ∈ gchop d :=
  in_gchop_rect _ _ _

/-- Membership in `equad d`, explicitly. -/
theorem mem_equad {d p : GPoint} :
    p ∈ equad d ↔ (p ∈ gtouch (halfg d) ∧ p ∈ gchop d) ∧ p ∈ gchop (gface d) := by
  rw [equad, in_gchop_rect, mem_ehex]

/-- Coq `ehexF`. -/
theorem ehexF (d : GPoint) : equad d ⊆ ehex (gface d) := by
  intro p hp
  rw [mem_equad] at hp
  rw [mem_ehex, halfg_face]
  exact ⟨hp.1.1, hp.2⟩

private theorem end0g_mem_equad (d : GPoint) : end0g d ∈ equad (gface d) := by
  rw [mem_equad, mem_gchop, mem_gchop]
  simp only [halfg_face, oddg_face, end0g]
  rw [mem_grect]
  rcases oddg_eq_or d with h | h | h | h <;> simp [h, ccw, gtouch] <;> omega

private theorem halfg_mem_equad {d d1 : GPoint} (he : end0g d1 = end0g d) :
    halfg d1 ∈ equad (gface d) := by
  rw [GPoint.ext_iff, end0g_x, end0g_y, end0g_x, end0g_y] at he
  rw [mem_equad, mem_gchop, mem_gchop]
  simp only [halfg_face, oddg_face]
  rw [mem_grect]
  rcases oddg_cases_coord d with ⟨h, hx, hy⟩ | ⟨h, hx, hy⟩ | ⟨h, hx, hy⟩ | ⟨h, hx, hy⟩ <;>
    simp [h, ccw, gtouch] <;> omega

/-- Coq `end0g_equad`. -/
theorem end0g_equad (d : GPoint) (h : ¬ ∃ p ∈ m, p ∈ equad (gface d)) : end0g d ∉ m :=
  fun hm => h ⟨end0g d, hm, end0g_mem_equad d⟩

/-- Coq `mring_equad`. -/
theorem mring_equad (d : GPoint) (h : ¬ ∃ p ∈ m, p ∈ equad (gface d)) :
    end0g d ∉ m.mring.map end0g := by
  rw [List.mem_map]
  rintro ⟨d1, hd1, he⟩
  rw [m.in_mring, mem_gborder] at hd1
  exact h ⟨halfg d1, hd1.1, halfg_mem_equad he⟩

/-! #### Adding a pixel with one side on the border -/

section Extend1

/-- Coq `ext1_hex m d`: `m` contains the pixel across the edge `d` but no pixel of `ehex d`. -/
def Ext1Hex (d : GPoint) : Prop := halfg (gedge d) ∈ m ∧ ¬ ∃ p ∈ m, p ∈ ehex d

variable {m} {d : GPoint}

/-- Coq section-local `m'd`. -/
private theorem ext1_m'd (h : Ext1Hex m d) : halfg d ∉ m :=
  fun hm => h.2 ⟨halfg d, hm, mem_ehex.2 ⟨gtouch_refl _, gchop_halfg d⟩⟩

/-- Coq section-local `rm_ed`. -/
private theorem ext1_rm_ed (h : Ext1Hex m d) : gedge d ∈ m.mring := by
  rw [m.in_mring, mem_gborder, gedge2]
  exact ⟨h.1, ext1_m'd h⟩

/-- Coq section-local `m'f3d`. -/
private theorem ext1_m'f3d (h : Ext1Hex m d) :
    ¬ ∃ p ∈ m, p ∈ equad (gface (gface (gface d))) := by
  rintro ⟨p, hp, hq⟩
  have := ehexF _ p hq
  rw [gface4] at this
  exact h.2 ⟨p, hp, this⟩

/-- Coq section-local `m'f4d`. -/
private theorem ext1_m'f4d (h : Ext1Hex m d) :
    ¬ ∃ p ∈ m, p ∈ equad (gface (gface (gface (gface d)))) := by
  rw [gface4]
  rintro ⟨p, hp, hq⟩
  rw [mem_equad] at hq
  exact h.2 ⟨p, hp, mem_ehex.2 hq.1⟩

variable (d)

/-- Coq section-local `ext1_loop`: the three other darts of the pixel of `d`. -/
def ext1Loop : List GPoint := List.iterate gface (gface d) 3

variable (m)

/-- Coq `ext1_mring m d`: the contour of `m` with the edge `gedge d` replaced by the three other
edges of the pixel of `d`. -/
def ext1Mring : List GPoint :=
  ext1Loop d ++ (m.mring.rotate (m.mring.idxOf (gedge d))).tail

variable {m d}

/-- Coq `ext1_mring_cycle`. -/
theorem ext1_mring_cycle (h : Ext1Hex m d) : cycle mrlink (ext1Mring m d) := by
  have hc := (cycle_rotate' (m.mring.idxOf (gedge d)) m.mring).2 m.mring_cycle
  rw [rot_to (ext1_rm_ed h)] at hc
  simp only [ext1Mring, ext1Loop, List.iterate, List.cons_append, List.nil_append]
  rw [cycle_cons] at hc ⊢
  simp only [List.cons_append, path_cons]
  refine ⟨(end0g_face _).symm, (end0g_face _).symm, ?_⟩
  refine (path_mrlink_congr ?_ ?_ _).1 hc
  · rw [end1g_edge, ← end0g_face, gface4]
  · rw [end0g_edge, end0g_face]

/-- Coq `ext1_mring_simple`. -/
theorem ext1_mring_simple (h : Ext1Hex m d) : ((ext1Mring m d).map end0g).Nodup := by
  have hrot := rot_to (ext1_rm_ed h)
  set R := (m.mring.rotate (m.mring.idxOf (gedge d))).tail with hR
  have hs : ((gedge d :: R).map end0g).Nodup := by
    rw [← hrot, List.map_rotate, List.nodup_rotate]
    exact m.mring_simple
  have hsub : ∀ x, x ∈ gedge d :: R → x ∈ m.mring := fun x hx => by
    rw [← hrot, List.mem_rotate] at hx
    exact hx
  have h2 := mring_equad m _ (ext1_m'f3d h)
  have h3 := mring_equad m _ (ext1_m'f4d h)
  have n2 : ∀ x, x ∈ gedge d :: R → end0g x ≠ end0g (gface (gface d)) := fun x hx he =>
    h2 (List.mem_map.2 ⟨x, hsub x hx, he⟩)
  have n3 : ∀ x, x ∈ gedge d :: R → end0g x ≠ end0g (gface (gface (gface d))) := fun x hx he =>
    h3 (List.mem_map.2 ⟨x, hsub x hx, he⟩)
  rw [List.map_cons, List.nodup_cons] at hs
  have e1 : end0g (gface d) = end0g (gedge d) := by rw [end0g_face, end0g_edge]
  simp only [ext1Mring, ext1Loop, List.iterate, List.cons_append, List.nil_append,
    List.map_cons, List.nodup_cons, List.mem_cons, List.mem_map, not_or, not_exists, not_and]
  refine ⟨⟨?_, ?_, fun x hx he => hs.1 (List.mem_map.2 ⟨x, hx, he.trans e1⟩)⟩,
    ⟨?_, fun x hx he => n2 x (List.mem_cons_of_mem _ hx) he⟩,
    fun x hx he => n3 x (List.mem_cons_of_mem _ hx) he, hs.2⟩
  · rw [e1]; exact n2 _ List.mem_cons_self
  · rw [e1]; exact n3 _ List.mem_cons_self
  · rw [end0g_face (gface (gface d))]
    exact end0g_ne_end1g _

private theorem halfg_edge_iter_mem_ehex (d : GPoint) :
    halfg (gedge (gface d)) ∈ ehex d ∧ halfg (gedge (gface (gface d))) ∈ ehex d ∧
      halfg (gedge (gface (gface (gface d)))) ∈ ehex d := by
  simp only [mem_ehex, mem_gchop]
  simp only [halfg_edge, halfg_face, oddg_face]
  simp only [mem_grect, gtouch]
  rcases oddg_eq_or d with h | h | h | h <;> simp [h, ccw] <;> omega

/-- Coq section-local `m'Eloop`. -/
private theorem ext1_m'Eloop (h : Ext1Hex m d) :
    halfg (gedge (gface d)) ∉ m ∧ halfg (gedge (gface (gface d))) ∉ m ∧
      halfg (gedge (gface (gface (gface d)))) ∉ m := by
  obtain ⟨h1, h2, h3⟩ := halfg_edge_iter_mem_ehex d
  exact ⟨fun hm => h.2 ⟨_, hm, h1⟩, fun hm => h.2 ⟨_, hm, h2⟩, fun hm => h.2 ⟨_, hm, h3⟩⟩

/-- Darts of the pixel of `d`. -/
private theorem mem_iterate_face4 {d x : GPoint} :
    x ∈ List.iterate gface d 4 ↔
      x = d ∨ x = gface d ∨ x = gface (gface d) ∨ x = gface (gface (gface d)) := by
  simp only [List.iterate, List.mem_cons, List.not_mem_nil, or_false]

/-- The pixel condition satisfied by the darts of the pixel of `d` that are added to a
contour. -/
private theorem loop_border {m : Matte} {d e : GPoint} (he : halfg e = halfg d)
    (hE : halfg (gedge e) ∉ m) :
    (halfg e = halfg d ∨ halfg e ∈ m) ∧ ¬(halfg (gedge e) = halfg d ∨ halfg (gedge e) ∈ m) := by
  refine ⟨Or.inl he, ?_⟩
  rintro (h' | h')
  · exact neq_halfg_edge e (he.trans h'.symm)
  · exact hE h'

/-- Coq `ext1_mring_def`. -/
theorem ext1_mring_def (h : Ext1Hex m d) (p : GPoint) :
    p ∈ ext1Mring m d ↔ p ∈ gborder (extMdisk m d) := by
  obtain ⟨E1, E2, E3⟩ := ext1_m'Eloop h
  have hrot := rot_to (ext1_rm_ed h)
  unfold ext1Mring
  generalize (m.mring.rotate (m.mring.idxOf (gedge d))).tail = R at hrot ⊢
  have hmem : ∀ x, x ∈ gedge d :: R ↔ x ∈ m.mring := fun x => by
    rw [← hrot, List.mem_rotate]
  have hnd : (gedge d :: R).Nodup := by
    rw [← hrot, List.nodup_rotate]
    exact mring_uniq m
  rw [ext1Loop, mem_gborder, mem_extMdisk, mem_extMdisk]
  simp only [List.iterate, List.cons_append, List.nil_append, List.mem_cons]
  by_cases p1 : p = gface d
  · subst p1
    exact iff_of_true (Or.inl rfl) (loop_border (halfg_face d) E1)
  by_cases p2 : p = gface (gface d)
  · subst p2
    exact iff_of_true (Or.inr (Or.inl rfl)) (loop_border (by rw [halfg_face, halfg_face]) E2)
  by_cases p3 : p = gface (gface (gface d))
  · subst p3
    exact iff_of_true (Or.inr (Or.inr (Or.inl rfl)))
      (loop_border (by rw [halfg_face, halfg_face, halfg_face]) E3)
  rw [or_iff_right p1, or_iff_right p2, or_iff_right p3]
  rw [List.nodup_cons] at hnd
  by_cases mr_p : p ∈ m.mring
  · rw [← hmem, List.mem_cons] at mr_p
    rcases mr_p with rfl | r_p
    · -- `p = gedge d`: neither side holds
      refine iff_of_false hnd.1 ?_
      rw [gedge2]
      rintro ⟨_, h'⟩
      exact h' (Or.inl rfl)
    · have hp := (m.in_mring p).1 ((hmem p).1 (List.mem_cons_of_mem _ r_p))
      rw [mem_gborder] at hp
      refine iff_of_true r_p ⟨Or.inr hp.1, ?_⟩
      rintro (h' | h')
      · -- `gedge p` would be a dart of the pixel of `d`
        have := same_halfg h'.symm
        rw [mem_iterate_face4] at this
        rcases this with h'' | h'' | h'' | h''
        · exact hnd.1 (by rw [← h'', gedge2]; exact r_p)
        · exact E1 (by rw [← h'', gedge2]; exact hp.1)
        · exact E2 (by rw [← h'', gedge2]; exact hp.1)
        · exact E3 (by rw [← h'', gedge2]; exact hp.1)
      · exact hp.2 h'
  · have r'p : p ∉ R := fun hp => mr_p ((hmem p).1 (List.mem_cons_of_mem _ hp))
    refine iff_of_false r'p ?_
    rintro ⟨h' | h', h''⟩
    · have := same_halfg h'.symm
      rw [mem_iterate_face4] at this
      rcases this with h3 | h3 | h3 | h3
      · subst h3
        exact h'' (Or.inr h.1)
      · exact p1 h3
      · exact p2 h3
      · exact p3 h3
    · rw [not_or] at h''
      exact mr_p ((m.in_mring p).2 ⟨h', h''.2⟩)

/-- Coq `ext1_matte`: the matte `m` extended with the pixel of `d`. -/
def ext1Matte (m : Matte) (d : GPoint) (h : Ext1Hex m d) : Matte :=
  ⟨extMdisk m d, ext1Mring m d, ext_mdisk_ne m d, ext1_mring_cycle h, ext1_mring_simple h,
    ext1_mring_def h⟩

/-- Membership in `ext1Matte m d h`. -/
theorem mem_ext1Matte {m : Matte} {d : GPoint} {h : Ext1Hex m d} {p : GPoint} :
    p ∈ ext1Matte m d h ↔ p = halfg d ∨ p ∈ m :=
  List.mem_cons

end Extend1

/-! #### Adding a pixel with two consecutive sides on the border -/

section Extend2

/-- Coq `ext2_quad m d`: `m` contains the pixels across the edges `d` and `gface d`, but no
pixel of `equad d`. -/
def Ext2Quad (d : GPoint) : Prop :=
  halfg (gedge d) ∈ m ∧ halfg (gedge (gface d)) ∈ m ∧ ¬ ∃ p ∈ m, p ∈ equad d

variable {m} {d : GPoint}

/-- Coq section-local `m'd`. -/
private theorem ext2_m'd (h : Ext2Quad m d) : halfg d ∉ m := fun hm =>
  h.2.2 ⟨halfg d, hm, mem_equad.2 ⟨⟨gtouch_refl _, gchop_halfg d⟩,
    by rw [← halfg_face]; exact gchop_halfg _⟩⟩

/-- Coq section-local `m'f4d`. -/
private theorem ext2_m'f4d (h : Ext2Quad m d) :
    ¬ ∃ p ∈ m, p ∈ equad (gface (gface (gface (gface d)))) := by
  rw [gface4]
  exact h.2.2

/-- Coq section-local `mr_efd`. -/
private theorem ext2_mr_efd (h : Ext2Quad m d) : gedge (gface d) ∈ m.mring := by
  rw [m.in_mring, mem_gborder, gedge2, halfg_face]
  exact ⟨h.2.1, ext2_m'd h⟩

/-- Coq section-local `mr_ed`. -/
private theorem ext2_mr_ed (h : Ext2Quad m d) : gedge d ∈ m.mring := by
  rw [m.in_mring, mem_gborder, gedge2]
  exact ⟨h.1, ext2_m'd h⟩

private theorem gface_ne (d : GPoint) : gface d ≠ d := by
  intro h
  have := congrArg oddg h
  rw [oddg_face] at this
  exact neq_ccw _ this

/-- Coq `ext2_P`: rotating the contour of `m` to `gedge (gface d)` brings `gedge d` next (the
Coq statement is the existence of such a rotation). -/
theorem ext2_P (h : Ext2Quad m d) :
    m.mring.rotate (m.mring.idxOf (gedge (gface d))) =
      gedge (gface d) :: gedge d ::
        (m.mring.rotate (m.mring.idxOf (gedge (gface d)))).drop 2 := by
  obtain ⟨T, hT⟩ : ∃ T, m.mring.rotate (m.mring.idxOf (gedge (gface d))) = gedge (gface d) :: T :=
    ⟨_, rot_to (ext2_mr_efd h)⟩
  have hc : cycle mrlink (gedge (gface d) :: T) := by
    rw [← hT, cycle_rotate']
    exact m.mring_cycle
  have hs : ((gedge (gface d) :: T).map end0g).Nodup := by
    rw [← hT, List.map_rotate, List.nodup_rotate]
    exact m.mring_simple
  have hed : gedge d ∈ gedge (gface d) :: T := by
    rw [← hT, List.mem_rotate]
    exact ext2_mr_ed h
  rw [hT]
  rcases T with _ | ⟨d1, T⟩
  · exfalso
    rw [cycle_cons] at hc
    simp only [List.nil_append, path_cons, path_nil, and_true, mrlink] at hc
    exact end0g_ne_end1g _ hc.symm
  · rw [cycle_cons] at hc
    have h1 : end0g d1 = end0g (gedge d) := by
      have := hc.1
      rw [mrlink, end1g_edge, end0g_face, ← end0g_edge] at this
      exact this.symm
    rw [List.map_cons, List.map_cons, List.nodup_cons, List.nodup_cons] at hs
    simp only [List.drop_succ_cons, List.drop_zero, List.cons.injEq, and_true, true_and]
    rcases List.mem_cons.1 hed with h' | h'
    · exact absurd (by simpa [gedge2] using congrArg gedge h') (gface_ne d).symm
    rcases List.mem_cons.1 h' with h' | h'
    · exact h'.symm
    · exact absurd (List.mem_map.2 ⟨_, h', h1.symm⟩) hs.2.1

variable (d)

/-- Coq section-local `ext2_loop`: the two darts of the pixel of `d` after `gface d`. -/
def ext2Loop : List GPoint := List.iterate gface (gface (gface d)) 2

variable (m)

/-- Coq `ext2_mring m d`: the contour of `m` with the edges `gedge (gface d)` and `gedge d`
replaced by the two other edges of the pixel of `d`. -/
def ext2Mring : List GPoint :=
  ext2Loop d ++ (m.mring.rotate (m.mring.idxOf (gedge (gface d)))).drop 2

variable {m d}

/-- Coq `ext2_mring_cycle`. -/
theorem ext2_mring_cycle (h : Ext2Quad m d) : cycle mrlink (ext2Mring m d) := by
  have hc := (cycle_rotate' (m.mring.idxOf (gedge (gface d))) m.mring).2 m.mring_cycle
  rw [ext2_P h] at hc
  unfold ext2Mring ext2Loop
  generalize (m.mring.rotate (m.mring.idxOf (gedge (gface d)))).drop 2 = R at hc ⊢
  simp only [List.iterate, List.cons_append, List.nil_append]
  rw [cycle_cons] at hc ⊢
  simp only [List.cons_append, path_cons] at hc ⊢
  refine ⟨(end0g_face _).symm, (path_mrlink_congr ?_ ?_ _).1 hc.2⟩
  · rw [end1g_edge, ← end0g_face, gface4]
  · rw [end0g_edge, end0g_face]

/-- Coq `ext2_mring_simple`. -/
theorem ext2_mring_simple (h : Ext2Quad m d) : ((ext2Mring m d).map end0g).Nodup := by
  have hs := m.mring_simple
  rw [← List.nodup_rotate (n := m.mring.idxOf (gedge (gface d))), ← List.map_rotate,
    ext2_P h] at hs
  have hmem : ∀ x, x ∈ m.mring.rotate (m.mring.idxOf (gedge (gface d))) → x ∈ m.mring :=
    fun x hx => List.mem_rotate.1 hx
  rw [ext2_P h] at hmem
  have h3 := mring_equad m _ (ext2_m'f4d h)
  unfold ext2Mring ext2Loop
  generalize (m.mring.rotate (m.mring.idxOf (gedge (gface d)))).drop 2 = R at hs hmem ⊢
  have n3 : ∀ x, x ∈ gedge (gface d) :: gedge d :: R →
      end0g x ≠ end0g (gface (gface (gface d))) := fun x hx he =>
    h3 (List.mem_map.2 ⟨x, hmem x hx, he⟩)
  have e1 : end0g (gedge (gface d)) = end0g (gface (gface d)) := by
    rw [end0g_edge, end0g_face]
  simp only [List.map_cons, List.nodup_cons, List.mem_cons, not_or] at hs
  simp only [List.iterate, List.cons_append, List.nil_append, List.map_cons, List.nodup_cons,
    List.mem_cons, not_or]
  refine ⟨⟨?_, ?_⟩, fun hx => ?_, hs.2.2⟩
  · rw [← e1]; exact n3 _ List.mem_cons_self
  · rw [← e1]; exact hs.1.2
  · rw [List.mem_map] at hx
    obtain ⟨x, hx, he⟩ := hx
    exact n3 x (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)) he

private theorem halfg_edge_iter_mem_equad (d : GPoint) :
    halfg (gedge (gface (gface d))) ∈ equad d ∧
      halfg (gedge (gface (gface (gface d)))) ∈ equad d := by
  simp only [mem_equad, mem_gchop]
  simp only [halfg_edge, halfg_face, oddg_face]
  simp only [mem_grect, gtouch]
  rcases oddg_eq_or d with h | h | h | h <;> simp [h, ccw] <;> omega

/-- Coq section-local `m'Eloop`. -/
private theorem ext2_m'Eloop (h : Ext2Quad m d) :
    halfg (gedge (gface (gface d))) ∉ m ∧ halfg (gedge (gface (gface (gface d)))) ∉ m := by
  obtain ⟨h2, h3⟩ := halfg_edge_iter_mem_equad d
  exact ⟨fun hm => h.2.2 ⟨_, hm, h2⟩, fun hm => h.2.2 ⟨_, hm, h3⟩⟩

/-- Coq `ext2_mring_def`. -/
theorem ext2_mring_def (h : Ext2Quad m d) (p : GPoint) :
    p ∈ ext2Mring m d ↔ p ∈ gborder (extMdisk m d) := by
  obtain ⟨E2, E3⟩ := ext2_m'Eloop h
  have hmem0 : ∀ x, x ∈ m.mring.rotate (m.mring.idxOf (gedge (gface d))) ↔ x ∈ m.mring :=
    fun x => List.mem_rotate
  have hnd0 : (m.mring.rotate (m.mring.idxOf (gedge (gface d)))).Nodup :=
    List.nodup_rotate.2 (mring_uniq m)
  rw [ext2_P h] at hmem0 hnd0
  unfold ext2Mring ext2Loop
  generalize (m.mring.rotate (m.mring.idxOf (gedge (gface d)))).drop 2 = R at hmem0 hnd0 ⊢
  rw [mem_gborder, mem_extMdisk, mem_extMdisk]
  simp only [List.iterate, List.cons_append, List.nil_append, List.mem_cons]
  by_cases p2 : p = gface (gface d)
  · subst p2
    exact iff_of_true (Or.inl rfl) (loop_border (by rw [halfg_face, halfg_face]) E2)
  by_cases p3 : p = gface (gface (gface d))
  · subst p3
    exact iff_of_true (Or.inr (Or.inl rfl))
      (loop_border (by rw [halfg_face, halfg_face, halfg_face]) E3)
  rw [or_iff_right p2, or_iff_right p3]
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd0
  by_cases mr_p : p ∈ m.mring
  · rw [← hmem0, List.mem_cons, List.mem_cons] at mr_p
    rcases mr_p with rfl | rfl | r_p
    · -- `p = gedge (gface d)`
      refine iff_of_false hnd0.1.2 ?_
      rw [gedge2, halfg_face]
      rintro ⟨_, h'⟩
      exact h' (Or.inl rfl)
    · -- `p = gedge d`
      refine iff_of_false hnd0.2.1 ?_
      rw [gedge2]
      rintro ⟨_, h'⟩
      exact h' (Or.inl rfl)
    · have hp := (m.in_mring p).1
        ((hmem0 p).1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ r_p)))
      rw [mem_gborder] at hp
      refine iff_of_true r_p ⟨Or.inr hp.1, ?_⟩
      rintro (h' | h')
      · have := same_halfg h'.symm
        rw [mem_iterate_face4] at this
        rcases this with h'' | h'' | h'' | h''
        · exact hnd0.2.1 (by rw [← h'', gedge2]; exact r_p)
        · exact hnd0.1.2 (by rw [← h'', gedge2]; exact r_p)
        · exact E2 (by rw [← h'', gedge2]; exact hp.1)
        · exact E3 (by rw [← h'', gedge2]; exact hp.1)
      · exact hp.2 h'
  · have r'p : p ∉ R := fun hp =>
      mr_p ((hmem0 p).1 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp)))
    refine iff_of_false r'p ?_
    rintro ⟨h' | h', h''⟩
    · have := same_halfg h'.symm
      rw [mem_iterate_face4] at this
      rcases this with h3 | h3 | h3 | h3
      · subst h3
        exact h'' (Or.inr h.1)
      · subst h3
        exact h'' (Or.inr h.2.1)
      · exact p2 h3
      · exact p3 h3
    · rw [not_or] at h''
      exact mr_p ((m.in_mring p).2 ⟨h', h''.2⟩)

/-- Coq `ext2_matte`: the matte `m` extended with the pixel of `d`. -/
def ext2Matte (m : Matte) (d : GPoint) (h : Ext2Quad m d) : Matte :=
  ⟨extMdisk m d, ext2Mring m d, ext_mdisk_ne m d, ext2_mring_cycle h, ext2_mring_simple h,
    ext2_mring_def h⟩

/-- Membership in `ext2Matte m d h`. -/
theorem mem_ext2Matte {m : Matte} {d : GPoint} {h : Ext2Quad m d} {p : GPoint} :
    p ∈ ext2Matte m d h ↔ p = halfg d ∨ p ∈ m :=
  List.mem_cons

end Extend2

end ExtendMatte

/-! ### Matte extensions -/

section MatteExtension

/-- Coq `matte_extension m xm`: `xm` is obtained from `m` by adding pixels one at a time, each
new pixel sharing a border edge with the previous matte. -/
inductive MatteExtension (m : Matte) : Matte → Prop
  /-- Coq `Mext_nil`. -/
  | mextNil : MatteExtension m m
  /-- Coq `Mext_add`. -/
  | mextAdd (d : GPoint) (xm0 xm : Matte) : MatteExtension m xm0 → gedge d ∈ xm0.mring →
      (∀ p, p ∈ xm ↔ p ∈ extMdisk xm0 d) → MatteExtension m xm

variable (m : Matte)

/-- Coq `in_extension`. -/
theorem in_extension {xm : Matte} (h : MatteExtension m xm) : ∀ p, p ∈ m → p ∈ xm := by
  induction h with
  | mextNil => exact fun p hp => hp
  | mextAdd d xm0 xm _ _ hxm ih =>
    exact fun p hp => (hxm p).2 (List.mem_cons_of_mem _ (ih p hp))

/-- Coq `extends_in m r p`: some extension of `m` inside `r` contains `p`. -/
inductive ExtendsIn (r : GRect) (p : GPoint) : Prop
  /-- Coq `ExtendsIn`. -/
  | intro (xm : Matte) : MatteExtension m xm → (∀ q, q ∈ xm → q ∈ r ∨ q ∈ m) → p ∈ xm →
      ExtendsIn r p

/-- Coq `extends_in_sub`. -/
theorem extends_in_sub {r1 r2 : GRect} (h : r1 ⊆ r2) (p : GPoint) (h1 : ExtendsIn m r1 p) :
    ExtendsIn m r2 p := by
  obtain ⟨xm, xmP, sxmr, xm_p⟩ := h1
  exact ⟨xm, xmP, fun q hq => (sxmr q hq).imp_left (h q), xm_p⟩

/-! #### Geometric lemmas used by `coarse_extends_in` -/

private theorem isOddg_ccw {c : GPoint} (h : IsOddg c) : IsOddg (ccw c) := by
  rw [← oddg_id h, ccw_odd]
  exact oddgP _

/-- The dart of the pixel `q` whose edge separates `q` from `gnode q` (Coq local `nd`). -/
private def nd (q : GPoint) : GPoint := 2 • q + ccw (ccw (ccw (oddg q)))

private theorem isOddg_nd (q : GPoint) : IsOddg (ccw (ccw (ccw (oddg q)))) :=
  isOddg_ccw (isOddg_ccw (isOddg_ccw (oddgP q)))

/-- Coq local `h_nd`. -/
private theorem h_nd (q : GPoint) : halfg (nd q) = q := halfg_eq _ (isOddg_nd q)

/-- Coq local `o_nd`. -/
private theorem o_nd (q : GPoint) : oddg (nd q) = ccw (ccw (ccw (oddg q))) :=
  oddg_eq _ (isOddg_nd q)

/-- Coq local `hEnd`. -/
private theorem hEnd (q : GPoint) : halfg (gedge (nd q)) = gnode q := by
  rw [halfg_edge, h_nd, o_nd, ccw4, unlock_gnode]

private theorem gface_nd_gnode (q : GPoint) : gface (nd (gnode q)) = gedge (nd q) := by
  have e1 : gface (nd (gnode q)) = 2 • gnode q + ccw (ccw (ccw (ccw (ccw (oddg q))))) := by
    rw [gface_def, h_nd, o_nd, oddg_node]
  have e2 : gedge (nd q) = 2 • gnode q + ccw (ccw (ccw (ccw (ccw (oddg q))))) := by
    conv_lhs => rw [← halfgK (gedge (nd q))]
    rw [hEnd, oddg_edge, o_nd]
  rw [e1, e2]

/-- Coq local `ndN`. -/
private theorem ndN (q : GPoint) : nd (gnode q) = gedge (gnode (gedge (nd q))) := by
  rw [← gface_nd_gnode, gfaceK]

/-- Coq local `ndFE`. -/
private theorem ndFE (q : GPoint) : nd (gface (gedge q)) = gedge (gface (nd q)) := by
  conv_rhs => rw [← gedgeK q]
  rw [ndN, gnodeK, gedge2]

private theorem efq_gnode (q : GPoint) : gedge (gface (nd (gnode q))) = nd q := by
  rw [← ndFE, gnodeK]

/-- The pixels of `equad (nd q)` are the four subpixels of the coarse pixel of `q`. -/
private theorem halfg_of_mem_equad_nd {q q1 : GPoint} (h : q1 ∈ equad (nd q)) :
    halfg q1 = halfg q := by
  rw [mem_equad, mem_gchop, mem_gchop] at h
  simp only [halfg_face, oddg_face, h_nd, o_nd, ccw4] at h
  rw [mem_grect] at h
  rcases oddg_cases_coord q with ⟨hc, hx, hy⟩ | ⟨hc, hx, hy⟩ | ⟨hc, hx, hy⟩ | ⟨hc, hx, hy⟩ <;>
    simp [hc, ccw, gtouch] at h <;> ext <;> simp only [halfg_x, halfg_y] <;> omega

/-- Coq local `ehex_shift_quad`. -/
private theorem ehex_shift_quad (q q' : GPoint)
    (h : q' ∈ ehex q ∨ q' ∈ ehex (gface (gedge (gface q)))) :
    q' ∈ equad q ∨ q' ∈ equad (gedge (gface q)) := by
  simp only [mem_ehex, mem_equad, mem_gchop] at h ⊢
  simp only [halfg_face, oddg_face, halfg_edge, oddg_edge] at h ⊢
  simp only [mem_grect, gtouch] at h ⊢
  rcases oddg_eq_or q with hc | hc | hc | hc <;> simp [hc, ccw] at h ⊢ <;> omega

/-- The pixel two steps away from `halfg d` across `d` is in `r0`: then so is the inset of the
neighbor of `halfg d` across `d`. -/
private theorem inset_halfg_edge {r0 : GRect} {d : GPoint} (h1 : halfg d ∈ inset r0)
    (h2 : halfg (gedge (gface (gface (gedge d)))) ∈ r0) : halfg (gedge d) ∈ inset r0 := by
  simp only [halfg_edge, halfg_face, oddg_face, oddg_edge] at h2 ⊢
  simp only [mem_grect, inset] at h1 h2 ⊢
  rcases oddg_eq_or d with hc | hc | hc | hc <;> simp [hc, ccw] at h1 h2 ⊢ <;> omega

private theorem gnode_mem_of_inset {r0 : GRect} {p : GPoint} (h : p ∈ inset r0) :
    gnode p ∈ r0 := by
  simp only [mem_grect, inset] at h ⊢
  simp only [gnode_x, gnode_y]
  omega

private theorem gface_gedge_mem_of_inset {r0 : GRect} {p : GPoint} (h : p ∈ inset r0) :
    gface (gedge p) ∈ r0 := by
  simp only [mem_grect, inset] at h ⊢
  simp only [gface_x, gface_y, gedge_x, gedge_y]
  rcases Int.emod_two_eq p.x with hx | hx <;> rcases Int.emod_two_eq p.y with hy | hy <;>
    omega

private theorem gnode_gnode_mem_of_inset {r0 : GRect} {p : GPoint} (h : p ∈ inset r0) :
    gnode (gnode p) ∈ r0 := by
  simp only [mem_grect, inset] at h ⊢
  simp only [gnode_x, gnode_y]
  rcases Int.emod_two_eq p.x with hx | hx <;> rcases Int.emod_two_eq p.y with hy | hy <;>
    omega

private theorem gnode_mem_of_mem {r : GRect} {p : GPoint} (h1 : p ∈ r)
    (h2 : gnode (gnode p) ∈ r) : gnode p ∈ r := by
  simp only [mem_grect] at h1 h2 ⊢
  simp only [gnode_x, gnode_y] at h2 ⊢
  rcases Int.emod_two_eq p.x with hx | hx <;> rcases Int.emod_two_eq p.y with hy | hy <;>
    omega

/-- A pixel of `gtouch p` beyond the edge `nd p` touches `gnode p`. -/
private theorem gtouch_gnode_of {p q : GPoint} (h1 : q ∈ gtouch p) (h2 : q ∉ gchop (nd p)) :
    q ∈ gtouch (gnode p) := by
  rw [mem_gchop, h_nd, o_nd] at h2
  rw [unlock_gnode]
  simp only [mem_grect, gtouch] at h1 ⊢
  rcases oddg_eq_or p with hc | hc | hc | hc <;> simp [hc, ccw] at h2 ⊢ <;> omega

/-- Coq local `ext_hex` of `coarse_extends_in`: extending `m` inside a half rectangle to cover
the pixel across the edge `d`, then adding the pixel of `d`. -/
private theorem ext_hex_step {m : Matte} {r : GRect} {p d : GPoint} (r_p : p ∈ r) (m'p : p ∉ m)
    (Dp : halfg d = p) (d'm : ¬ ∃ q ∈ m, q ∈ ehex d)
    (hx : ExtendsIn m (gchopRect r (gedge d)) (halfg (gedge d))) : ExtendsIn m r p := by
  obtain ⟨xm, xmP, rm_xm, xm_ed⟩ := hx
  have ext1d : Ext1Hex xm d := by
    refine ⟨xm_ed, ?_⟩
    rintro ⟨q, hq, hqe⟩
    rcases rm_xm q hq with hq' | hq'
    · rw [in_gchop_rect, gchop_edge] at hq'
      exact hq'.2 (mem_ehex.1 hqe).2
    · exact d'm ⟨q, hq', hqe⟩
  refine ⟨ext1Matte xm d ext1d, .mextAdd d xm _ xmP ?_ (fun _ => Iff.rfl), ?_, ?_⟩
  · rw [xm.in_mring, mem_gborder, gedge2, Dp]
    refine ⟨xm_ed, fun hpx => ?_⟩
    rcases rm_xm p hpx with h' | h'
    · rw [in_gchop_rect, gchop_edge, ← Dp] at h'
      exact h'.2 (gchop_halfg d)
    · exact m'p h'
  · intro q hq
    rcases mem_ext1Matte.1 hq with rfl | hq
    · left
      rw [Dp]
      exact r_p
    · rcases rm_xm q hq with h' | h'
      · exact Or.inl (gchop_rect_sub r _ q h')
      · exact Or.inr h'
  · exact mem_ext1Matte.2 (Or.inl Dp.symm)

/-- Coq `coarse_extends_in`: if `m` is coarse in `r` and meets `r`, then any pixel strictly
inside `r` can be covered by an extension of `m` inside `r`. -/
theorem coarse_extends_in (r : GRect) (hc : CoarseIn r m) (hrm : ∃ q ∈ m, q ∈ r) :
    ∀ p, p ∈ inset r → ExtendsIn m r p := by
  intro p r0p
  suffices H : ∀ n (r r0 : GRect) (p : GPoint), garea r < n → (∃ q ∈ m, q ∈ r) → p ∈ r →
      (∀ q, q ∈ r0 → q ∈ m → q ∈ r) → r ⊆ r0 → p ∈ inset r0 → CoarseIn r0 m →
      ExtendsIn m r p from
    H _ r r p (Nat.lt_succ_self _) hrm (insetW r p r0p) (fun q hq _ => hq) (fun q hq => hq) r0p hc
  intro n
  induction n with
  | zero => intro r r0 p h; exact absurd h (Nat.not_lt_zero _)
  | succ n IHn =>
  intro r r0 p le_r_n m_r r_p r_m0 r0_r r0p r0Emh
  by_cases m_p : p ∈ m
  · exact ⟨m, .mextNil, fun q hq => Or.inr hq, m_p⟩
  have ext_hex : ∀ d, halfg d = p → (¬ ∃ q ∈ m, q ∈ ehex d) →
      ExtendsIn m (gchopRect r (gedge d)) (halfg (gedge d)) → ExtendsIn m r p :=
    fun d Dp d'm hx => ext_hex_step r_p m_p Dp d'm hx
  have IHp : ∀ d, halfg d = p → (∃ q ∈ m, q ∉ gchop1 d ∧ q ∈ r0) → ExtendsIn m r p := by
    intro d Dp m_r0d
    have r01p : p ∈ inset (gchop1Rect r0 d) := by
      rw [insetP]
      intro q p1q
      rw [in_gchop1_rect]
      refine ⟨insetP.1 r0p q p1q, ?_⟩
      rw [← Dp, gtouch_chop1] at p1q
      exact p1q d (by simp)
    by_cases m_r01 : ∃ q ∈ m, q ∈ gchop1Rect r0 d
    · have r_r1 : gchop1Rect r d ⊆ r := gchop_rect_sub r _
      refine extends_in_sub m r_r1 p
        (IHn (gchop1Rect r d) (gchop1Rect r0 d) p ?_ ?_ ?_ ?_ ?_ r01p ?_)
      · obtain ⟨q, m_q, d'q, r0q⟩ := m_r0d
        have := ltn_garea_subrect q r_r1
          ⟨fun hq1 => d'q ((in_gchop1_rect r d q).1 hq1).2, r_m0 q r0q m_q⟩
        omega
      · obtain ⟨q, m_q, hq⟩ := m_r01
        rw [in_gchop1_rect] at hq
        exact ⟨q, m_q, (in_gchop1_rect r d q).2 ⟨r_m0 q hq.1 m_q, hq.2⟩⟩
      · exact (in_gchop1_rect r d p).2 ⟨r_p, gchop_chop1 d (Dp ▸ gchop_halfg d)⟩
      · intro q hq m_q
        rw [in_gchop1_rect] at hq ⊢
        exact ⟨r_m0 q hq.1 m_q, hq.2⟩
      · intro q hq
        rw [in_gchop1_rect] at hq ⊢
        exact ⟨r0_r q hq.1, hq.2⟩
      · intro q1 q2 hq1 h12
        exact r0Emh q1 q2 (gchop_rect_sub r0 _ q1 hq1) h12
    · refine ext_hex d Dp ?_ ?_
      · rintro ⟨q, m_q, hq⟩
        apply m_r01
        refine ⟨q, m_q, ?_⟩
        rw [mem_ehex, Dp] at hq
        exact insetP.1 r01p q hq.1
      · have r_r1 : gchopRect r (gedge d) ⊆ r := gchop_rect_sub r _
        have m_r1 : ∃ q ∈ m, q ∈ gchopRect r (gedge d) := by
          obtain ⟨q, m_q, d'q, r0q⟩ := m_r0d
          refine ⟨q, m_q, (in_gchop_rect r _ q).2 ⟨r_m0 q r0q m_q, ?_⟩⟩
          rw [gchop_edge]
          exact fun hq => d'q (gchop_chop1 d hq)
        refine IHn (gchopRect r (gedge d)) r0 (halfg (gedge d)) ?_ m_r1 ?_ ?_
          (fun q hq => r0_r q (r_r1 q hq)) ?_ r0Emh
        · have hp1 : p ∉ gchopRect r (gedge d) := by
            rw [in_gchop_rect, gchop_edge, ← Dp]
            exact fun h' => h'.2 (gchop_halfg d)
          have := ltn_garea_subrect p r_r1 ⟨hp1, r_p⟩
          omega
        · obtain ⟨q, _, hq⟩ := m_r1
          exact gchop_rect_edge r (gedge d) (by rw [gedge2, Dp]; exact r_p) q hq
        · intro q r0q m_q
          refine (in_gchop_rect r _ q).2 ⟨r_m0 q r0q m_q, ?_⟩
          rw [gchop_edge]
          intro d_q
          exact m_r01 ⟨q, m_q, (in_gchop1_rect r0 d q).2 ⟨r0q, gchop_chop1 d d_q⟩⟩
        · have hd2 : halfg (gedge (gface (gface (gedge d)))) ∈ r0 := by
            obtain ⟨q, _, d'q, r0q⟩ := m_r0d
            have := gchop_rect_edge r0 (gedge (gface (gface (gedge d)))) ?_ q ?_
            · exact ((in_gchop_rect r0 _ _).1 this).1
            · rw [gedge2, halfg_face, halfg_face]
              exact insetP.1 r0p _ (Dp ▸ gtouch_edge d)
            · rw [in_gchop_rect, gchop_edge]
              exact ⟨r0q, d'q⟩
          exact inset_halfg_edge (Dp ▸ r0p) hd2
  have r0_np : gnode p ∈ r0 := gnode_mem_of_inset r0p
  have r0_fep : gface (gedge p) ∈ r0 := gface_gedge_mem_of_inset r0p
  have m_nd4 : ∀ q, q ∈ r0 → (∃ q1 ∈ m, q1 ∈ equad (nd q)) → q ∈ m := by
    rintro q r0q ⟨q1, m_q1, hq1⟩
    exact (r0Emh q q1 r0q (halfg_of_mem_equad_nd hq1)).1 m_q1
  have p4'm : ¬ ∃ q ∈ m, q ∈ equad (nd p) := fun h => m_p (m_nd4 p (r0_r p r_p) h)
  by_cases m_p6 : ∃ q ∈ m, q ∈ ehex (nd p)
  · have m_efp : halfg (gedge (gface (nd p))) ∈ m := by
      obtain ⟨q, m_q, p6_q⟩ := m_p6
      rw [← ndFE, h_nd]
      refine m_nd4 _ r0_fep ⟨q, m_q, ?_⟩
      rcases ehex_shift_quad (nd p) q (Or.inl p6_q) with h | h
      · exact absurd ⟨q, m_q, h⟩ p4'm
      · rwa [← ndFE] at h
    by_cases m_fp6 : ∃ q ∈ m, q ∈ ehex (gface (nd p))
    · have m_ep : halfg (gedge (nd p)) ∈ m := by
        obtain ⟨q, m_q, p6_q⟩ := m_fp6
        rw [hEnd]
        refine m_nd4 _ r0_np ⟨q, m_q, ?_⟩
        have := ehex_shift_quad (nd (gnode p)) q (Or.inr (by rw [efq_gnode]; exact p6_q))
        rw [efq_gnode] at this
        rcases this with h | h
        · exact h
        · exact absurd ⟨q, m_q, h⟩ p4'm
      have ext2p : Ext2Quad m (nd p) := ⟨m_ep, m_efp, p4'm⟩
      refine ⟨ext2Matte m (nd p) ext2p, .mextAdd (nd p) m _ .mextNil ?_ (fun _ => Iff.rfl),
        ?_, ?_⟩
      · rw [m.in_mring, mem_gborder, gedge2, h_nd]
        exact ⟨m_ep, m_p⟩
      · intro q hq
        rcases mem_ext2Matte.1 hq with rfl | hq
        · left
          rw [h_nd]
          exact r_p
        · exact Or.inr hq
      · exact mem_ext2Matte.2 (Or.inl (h_nd p).symm)
    · exact ext_hex (gface (nd p)) (by rw [halfg_face, h_nd]) m_fp6
        ⟨m, .mextNil, fun q hq => Or.inr hq, m_efp⟩
  by_cases m_p9 : ∃ q ∈ m, q ∈ gtouch p
  · refine ext_hex (nd p) (h_nd p) m_p6 ?_
    rw [hEnd]
    by_cases m_nd : gnode p ∈ m
    · exact ⟨m, .mextNil, fun q hq => Or.inr hq, m_nd⟩
    have nd4'm : ¬ ∃ q ∈ m, q ∈ equad (nd (gnode p)) := fun h => m_nd (m_nd4 _ r0_np h)
    have r0_n2p : gnode (gnode p) ∈ r0 := gnode_gnode_mem_of_inset r0p
    have m_n2p : gnode (gnode p) ∈ m := by
      obtain ⟨q, m_q, p9q⟩ := m_p9
      refine m_nd4 _ r0_n2p ⟨q, m_q, ?_⟩
      have ep_q : q ∉ gchop (nd p) := fun p_q =>
        m_p6 ⟨q, m_q, mem_ehex.2 ⟨by rw [h_nd]; exact p9q, p_q⟩⟩
      have := ehex_shift_quad (nd (gnode (gnode p))) q (Or.inr ?_)
      · rw [efq_gnode] at this
        rcases this with h | h
        · exact h
        · exact absurd ⟨q, m_q, h⟩ nd4'm
      · rw [efq_gnode, gface_nd_gnode, mem_ehex, hEnd, gchop_edge]
        exact ⟨gtouch_gnode_of p9q ep_q, ep_q⟩
    have r_np : gnode p ∈ r := gnode_mem_of_mem r_p (r_m0 _ r0_n2p m_n2p)
    have ext1nd : Ext1Hex m (nd (gnode p)) := by
      refine ⟨by rw [hEnd]; exact m_n2p, ?_⟩
      rintro ⟨q, m_q, nd4q⟩
      rcases ehex_shift_quad (nd (gnode p)) q (Or.inl nd4q) with h | h
      · exact nd4'm ⟨q, m_q, h⟩
      · rw [efq_gnode] at h
        exact p4'm ⟨q, m_q, h⟩
    refine ⟨ext1Matte m (nd (gnode p)) ext1nd,
      .mextAdd (nd (gnode p)) m _ .mextNil ?_ (fun _ => Iff.rfl), ?_, ?_⟩
    · rw [m.in_mring, mem_gborder, hEnd, gedge2, h_nd]
      exact ⟨m_n2p, m_nd⟩
    · intro q hq
      rcases mem_ext1Matte.1 hq with rfl | hq
      · left
        rw [h_nd, in_gchop_rect]
        exact ⟨r_np, by rw [← hEnd]; exact gchop_halfg _⟩
      · exact Or.inr hq
    · exact mem_ext1Matte.2 (Or.inl (h_nd _).symm)
  · obtain ⟨q, m_q, r_q⟩ := m_r
    have : ∃ k < 4, q ∉ gchop1 (gface^[k] (nd p)) := by
      by_contra hcon
      push Not at hcon
      apply m_p9
      refine ⟨q, m_q, ?_⟩
      rw [← h_nd p, gtouch_chop1]
      intro e he
      rw [List.mem_iterate] at he
      obtain ⟨k, hk, rfl⟩ := he
      exact hcon k hk
    obtain ⟨k, _, hk⟩ := this
    exact IHp (gface^[k] (nd p)) (by rw [halfg_iter_face, h_nd]) ⟨q, m_q, hk, r0_r q r_q⟩

/-- Coq `extend_madj`: under the assumptions of `coarse_extends_in`, if `m1` meets `inset r`
but not `m`, then some extension `xm` of `m`, inside `r` and outside `m1`, is adjacent to
`m1`. -/
theorem extend_madj (m1 : Matte) (r : GRect) (hc : CoarseIn r m) (hrm : ∃ q ∈ m, q ∈ r)
    (h1 : ∃ q ∈ m1, q ∈ inset r) (h2 : ¬ ∃ q ∈ m1, q ∈ m) :
    ∃ xm : Matte, ((∀ q, q ∈ m → q ∈ xm) ∧ (∀ q, q ∈ xm → q ∉ m1 ∧ (q ∈ r ∨ q ∈ m))) ∧
      Madj m1 xm := by
  obtain ⟨p, m1_p, r_p⟩ := h1
  obtain ⟨xm, xmP, sxmr, xm_p⟩ := coarse_extends_in m r hc hrm p r_p
  have m1_xm : ∃ q ∈ xm, q ∈ m1 := ⟨p, xm_p, m1_p⟩
  clear xm_p m1_p r_p
  revert sxmr m1_xm
  induction xmP with
  | mextNil =>
    intro _ m1_xm
    obtain ⟨q, hq, hq1⟩ := m1_xm
    exact absurd ⟨q, hq1, hq⟩ h2
  | mextAdd d xm0 xm _ xm0ep Dxm IHxm =>
    intro sxmr m1_xm
    have sxm0r : ∀ q, q ∈ xm0 → q ∈ r ∨ q ∈ m := fun q hq =>
      sxmr q ((Dxm q).2 (List.mem_cons_of_mem _ hq))
    by_cases m1_xm0 : ∃ q ∈ xm0, q ∈ m1
    · exact IHxm sxm0r m1_xm0
    · rename_i xm0P
      refine ⟨xm0, ⟨in_extension m xm0P, fun q hq => ⟨fun hq1 => m1_xm0 ⟨q, hq, hq1⟩,
        sxm0r q hq⟩⟩, gedge d, xm0ep, ?_⟩
      have hxm0 := (xm0.in_mring _).1 xm0ep
      rw [mem_gborder, gedge2] at hxm0
      rw [gedge2, m1.in_mring, mem_gborder]
      refine ⟨?_, fun h => m1_xm0 ⟨_, hxm0.1, h⟩⟩
      obtain ⟨q, hq, hq1⟩ := m1_xm
      rcases List.mem_cons.1 ((Dxm q).1 hq) with rfl | hq'
      · exact hq1
      · exact absurd ⟨q, hq', hq1⟩ m1_xm0

end MatteExtension

/-! ### The matte order -/

section MatteOrder

/-- Coq `mcorner m q`: a weighted count of the pixels incident to the grid point `q` (other
than the pixel `q`) that are not in `m`: the lower left pixel `q - ⟨1, 1⟩` counts once, the
upper left `q - ⟨1, 0⟩` and lower right `q - ⟨0, 1⟩` pixels count twice. -/
def mcorner (m : Matte) (q : GPoint) : ℕ :=
  let m'q : ℕ → ℕ := fun i => if q - ccw^[i] 0 ∈ m then 0 else 1
  m'q 2 + 2 * (m'q 1 + m'q 3)

/-- An explicit form of `mcorner` (not in Coq). -/
theorem mcorner_eq (m : Matte) (q : GPoint) :
    mcorner m q = (if q - ⟨1, 1⟩ ∈ m then 0 else 1) +
      2 * ((if q - ⟨1, 0⟩ ∈ m then 0 else 1) + (if q - ⟨0, 1⟩ ∈ m then 0 else 1)) := by
  have e1 : ccw^[1] (0 : GPoint) = ⟨1, 0⟩ := by decide
  have e2 : ccw^[2] (0 : GPoint) = ⟨1, 1⟩ := by decide
  have e3 : ccw^[3] (0 : GPoint) = ⟨0, 1⟩ := by decide
  simp only [mcorner, e1, e2, e3]

/-- Coq `mcorner0`. -/
theorem mcorner0 (m : Matte) (q : GPoint) (hq : q ∈ m) (h0 : mcorner m q = 0) :
    ∀ p, p ∈ ltouch q → p ∈ m := by
  rw [mcorner_eq] at h0
  split_ifs at h0 with h1 h2 h3 <;> try omega
  intro p hp
  simp only [mem_grect, ltouch] at hp
  have : p = q ∨ p = q - ⟨1, 0⟩ ∨ p = q - ⟨1, 1⟩ ∨ p = q - ⟨0, 1⟩ := by
    simp only [GPoint.ext_iff, sub_x, sub_y]
    omega
  rcases this with rfl | rfl | rfl | rfl <;> assumption

/-- Coq `refine_mcorner`: if the pixel `halfg q` of `m` has a positive `mcorner`, some
extension `xm` of the refinement of `m`, inside the refinement of `r`, has a smaller `mcorner`
at the subpixel `q`. -/
theorem refine_mcorner (m : Matte) (r : GRect) (q : GPoint) (m_p : halfg q ∈ m)
    (r_p : halfg q ∈ inset r) (mp_gt0 : 0 < mcorner m (halfg q)) :
    ∃ xm : Matte, ((∀ x, halfg x ∈ m → x ∈ xm) ∧ (∀ x, x ∈ xm → halfg x ∈ r ∨ halfg x ∈ m)) ∧
      mcorner xm q < mcorner m (halfg q) := by
  have ext_along : ∀ c0, IsOddg c0 → ∃ xm : Matte, ((∀ x, halfg x ∈ m → x ∈ xm) ∧
      (∀ x, x ∈ xm → halfg x ∈ r ∨ halfg x ∈ m)) ∧ q - c0 ∈ xm := by
    intro c0 hc0
    have xr_xm : ∃ x ∈ refineMatte m, x ∈ refineRect r :=
      ⟨q, (in_refine_matte m q).2 m_p, (in_refine_rect r q).2 (insetW r _ r_p)⟩
    have xr_qd : q - c0 ∈ inset (refineRect r) := by
      have hq : q ∈ inset (inset (refineRect r)) := by
        rw [← refine_inset, in_refine_rect]
        exact r_p
      apply insetP.1 hq
      simp only [mem_grect, gtouch, sub_x, sub_y]
      rcases hc0.eq_or with rfl | rfl | rfl | rfl <;> simp <;> omega
    obtain ⟨xm1, xm1P, xrm_xm1, xm1c1⟩ := coarse_extends_in (refineMatte m) (refineRect r)
      (refine_matte_coarse m _) xr_xm (q - c0) xr_qd
    refine ⟨xm1, ⟨fun x hx => in_extension _ xm1P x ((in_refine_matte m x).2 hx),
      fun x hx => ?_⟩, xm1c1⟩
    rcases xrm_xm1 x hx with h | h
    · exact Or.inl ((in_refine_rect r x).1 h)
    · exact Or.inr ((in_refine_matte m x).1 h)
  rw [mcorner_eq] at mp_gt0
  rcases oddg_cases_coord q with ⟨hc, hx, hy⟩ | ⟨hc, hx, hy⟩ | ⟨hc, hx, hy⟩ | ⟨hc, hx, hy⟩
  · -- `q` is the lower left subpixel of `halfg q`: extend towards a missing neighbor
    have e10 : halfg (q - ⟨1, 0⟩) = halfg q - ⟨1, 0⟩ := by
      simp only [GPoint.ext_iff, halfg_x, halfg_y, sub_x, sub_y]; omega
    have e11 : halfg (q - ⟨1, 1⟩) = halfg q - ⟨1, 1⟩ := by
      simp only [GPoint.ext_iff, halfg_x, halfg_y, sub_x, sub_y]; omega
    have e01 : halfg (q - ⟨0, 1⟩) = halfg q - ⟨0, 1⟩ := by
      simp only [GPoint.ext_iff, halfg_x, halfg_y, sub_x, sub_y]; omega
    have hc0 : ∃ c0, IsOddg c0 ∧ c0 ≠ 0 ∧ halfg q - c0 ∉ m := by
      by_contra hcon
      push Not at hcon
      have h10 := hcon ⟨1, 0⟩ .gpoint10 (by decide)
      have h11 := hcon ⟨1, 1⟩ .gpoint11 (by decide)
      have h01 := hcon ⟨0, 1⟩ .gpoint01 (by decide)
      simp [h10, h11, h01] at mp_gt0
    obtain ⟨c0, hc0odd, hc0ne, hc0m⟩ := hc0
    obtain ⟨xm, ⟨hxm1, hxm2⟩, hxc0⟩ := ext_along c0 hc0odd
    refine ⟨xm, ⟨hxm1, hxm2⟩, ?_⟩
    have F10 : halfg q - ⟨1, 0⟩ ∈ m → q - ⟨1, 0⟩ ∈ xm := fun h => hxm1 _ (by rwa [e10])
    have F11 : halfg q - ⟨1, 1⟩ ∈ m → q - ⟨1, 1⟩ ∈ xm := fun h => hxm1 _ (by rwa [e11])
    have F01 : halfg q - ⟨0, 1⟩ ∈ m → q - ⟨0, 1⟩ ∈ xm := fun h => hxm1 _ (by rwa [e01])
    rw [mcorner_eq, mcorner_eq]
    rcases hc0odd.eq_or with rfl | rfl | rfl | rfl
    · exact absurd rfl hc0ne
    all_goals
      split_ifs at mp_gt0 ⊢ <;>
        first
        | omega
        | exact absurd (F10 ‹_›) ‹_›
        | exact absurd (F11 ‹_›) ‹_›
        | exact absurd (F01 ‹_›) ‹_›
  · -- `q` is the upper left subpixel of `halfg q`: extend towards `q - ⟨1, 0⟩`
    have e10 : halfg (q - ⟨1, 0⟩) = halfg q - ⟨1, 0⟩ := by
      simp only [GPoint.ext_iff, halfg_x, halfg_y, sub_x, sub_y]; omega
    have e11 : halfg (q - ⟨1, 1⟩) = halfg q - ⟨1, 0⟩ := by
      simp only [GPoint.ext_iff, halfg_x, halfg_y, sub_x, sub_y]; omega
    have e01 : halfg (q - ⟨0, 1⟩) = halfg q := by
      simp only [GPoint.ext_iff, halfg_x, halfg_y, sub_x, sub_y]; omega
    obtain ⟨xm, ⟨hxm1, hxm2⟩, hxc0⟩ := ext_along ⟨1, 0⟩ .gpoint10
    refine ⟨xm, ⟨hxm1, hxm2⟩, ?_⟩
    have F11 : halfg q - ⟨1, 0⟩ ∈ m → q - ⟨1, 1⟩ ∈ xm := fun h => hxm1 _ (by rwa [e11])
    have F01 : q - ⟨0, 1⟩ ∈ xm := hxm1 _ (by rwa [e01])
    rw [mcorner_eq, mcorner_eq]
    split_ifs at mp_gt0 ⊢ <;>
      first
      | omega
      | exact absurd (F11 ‹_›) ‹_›
  · -- `q` is the upper right subpixel of `halfg q`: all its neighbors are in `halfg q`
    have e10 : halfg (q - ⟨1, 0⟩) = halfg q := by
      simp only [GPoint.ext_iff, halfg_x, halfg_y, sub_x, sub_y]; omega
    have e11 : halfg (q - ⟨1, 1⟩) = halfg q := by
      simp only [GPoint.ext_iff, halfg_x, halfg_y, sub_x, sub_y]; omega
    have e01 : halfg (q - ⟨0, 1⟩) = halfg q := by
      simp only [GPoint.ext_iff, halfg_x, halfg_y, sub_x, sub_y]; omega
    obtain ⟨xm, ⟨hxm1, hxm2⟩, -⟩ := ext_along 0 .gpoint00
    refine ⟨xm, ⟨hxm1, hxm2⟩, ?_⟩
    have F10 : q - ⟨1, 0⟩ ∈ xm := hxm1 _ (by rwa [e10])
    have F11 : q - ⟨1, 1⟩ ∈ xm := hxm1 _ (by rwa [e11])
    have F01 : q - ⟨0, 1⟩ ∈ xm := hxm1 _ (by rwa [e01])
    rw [mcorner_eq, mcorner_eq]
    simp only [F10, F11, F01, ite_true]
    omega
  · -- `q` is the lower right subpixel of `halfg q`: extend towards `q - ⟨0, 1⟩`
    have e10 : halfg (q - ⟨1, 0⟩) = halfg q := by
      simp only [GPoint.ext_iff, halfg_x, halfg_y, sub_x, sub_y]; omega
    have e11 : halfg (q - ⟨1, 1⟩) = halfg q - ⟨0, 1⟩ := by
      simp only [GPoint.ext_iff, halfg_x, halfg_y, sub_x, sub_y]; omega
    have e01 : halfg (q - ⟨0, 1⟩) = halfg q - ⟨0, 1⟩ := by
      simp only [GPoint.ext_iff, halfg_x, halfg_y, sub_x, sub_y]; omega
    obtain ⟨xm, ⟨hxm1, hxm2⟩, hxc0⟩ := ext_along ⟨0, 1⟩ .gpoint01
    refine ⟨xm, ⟨hxm1, hxm2⟩, ?_⟩
    have F10 : q - ⟨1, 0⟩ ∈ xm := hxm1 _ (by rwa [e10])
    have F11 : halfg q - ⟨0, 1⟩ ∈ m → q - ⟨1, 1⟩ ∈ xm := fun h => hxm1 _ (by rwa [e11])
    rw [mcorner_eq, mcorner_eq]
    split_ifs at mp_gt0 ⊢ <;>
      first
      | omega
      | exact absurd (F11 ‹_›) ‹_›

end MatteOrder

end FourColor
