/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import Mathlib.Basic.Real.Basic

/-!
# The real plane  (port of `realplane.v`)

An elementary formalization of the real plane topology required to state the Four Color
Theorem. Gonthier's Coq definitions are parametrized by an abstract real structure
`R : Real.structure` (`reals/real.v`); here they are specialised to Mathlib's real numbers `ℝ`.
This is a deliberate design decision: all models of the reals are isomorphic,
and the definitions below only use the order of the reals.

* `Point`       : points of the real plane `ℝ × ℝ` (Coq `point`). In Coq, `Real.val R` is a type
  of *denotations* of real numbers (a setoid), so `point R` is really a type of point
  denotations, and no equality on points is defined; Mathlib's `ℝ` is a quotient, so here two
  points are equal iff they have equal coordinates.
* `Region`      : sets of points, i.e. regions in the common rather than the topological sense
  (Coq `region`). Coq does not enforce extensionality (a Coq region may contain some but not
  all denotations of a point); over `ℝ` every region is extensional.
* `Map`         : point relations (Coq `map`). This allows for arbitrary connectivity in a map
  (see plain and simple maps below).
* `Interval`    : open intervals of `ℝ` (Coq `interval`, with endpoints `lo` and `hi`).
* `Rectangle`   : open rectangles of `ℝ × ℝ` (Coq `rectangle`).
* `inInterval s`, `inRectangle rr` : the set of reals in `s`, the region covered by `rr`
  (in Coq these are also coercions to sets).
* `union r1 r2`, `intersect r1 r2` : the union and the intersection of two regions.
* `NonemptyRegion r` : the region `r` is not empty (Coq `nonempty`, renamed to avoid any
  confusion with Lean's `Nonempty`).
* `Subregion r1 r2` : the region `r1` is included in the region `r2`.
* `Meet r1 r2`  : the regions `r1` and `r2` meet.
* `PlainMap m`  : `m` is a "plain" map, i.e. a partial equivalence relation (PER) whose classes
  are the regions of `m`.
* `cover m`     : the region covered by a plain map `m`; the region of a point `z` in `cover m`
  is `m z`, as `cover m z := m z z`.
* `Submap m1 m2` : `m1` is included in `m2`: each region of `m1` is included in a (possibly
  larger) region of `m2`.
* `AtMostRegions n m` : the plain map `m` has at most `n : ℕ` regions.
* `Open r`      : `r` is a topologically open region (Coq `open`, a keyword in Lean).
* `closure r`   : the topological closure of the region `r`.
* `Connected r` : `r` is a topologically connected region.
* `SimpleMap m` : `m` is a simple map: a plain map with open and connected regions (i.e. the
  regions of `m` are regions in the topological sense).
* `FiniteSimpleMap m` : `m` is a simple map with finitely many regions.
* `border m z1 z2` : the common border between the regions of `z1` and `z2` in `m`, assuming
  `z1` and `z2` are in different regions of `m`.
* `cornerMap m z` : the restriction of `m` to the regions whose closure contains `z`.
* `notCorner m` : the set of non-corner points of `m`, i.e. the points that belong to the
  closure of at most two regions of `m`.
* `Adjacent m z1 z2` : the regions of `z1` and `z2` in `m` are adjacent: they are different and
  have a common border point that is not a corner.
* `Coloring m k` : the map `m` admits `k` as a coloring; `k` is also represented as a map,
  whose regions are the sets of points with the same color. Thus `k` must be a plain map
  covering the same points as `m`, that assigns the same color to each region of `m` (i.e. the
  regions of `m` refine the color partition `k`), and assigns different colors to points of
  adjacent regions.
* `ColorableWith n m` : the map `m` admits a coloring with at most `n` colors.

Rendering choices:
* Coq's `Real.lt x y` is notation for `¬ Real.le y x`; as `ℝ` is linearly ordered it is written
  `x < y` here (the two are equivalent by `not_le`).
* Coq's `exists2 x, P x & Q x` is written `∃ x, P x ∧ Q x`, and `Peano.lt i n` is `i < n` on `ℕ`.
* The coercions of Coq's `RealPlaneCoercions` module from `simple_map` to `plain_map`, from
  `finite_simple_map` to `simple_map` and from `coloring` to `plain_map` become `extends`
  clauses (projections `toPlainMap`, `toSimpleMap`, so that e.g. `h.map_sym` works for
  `h : SimpleMap m`); the coercions from intervals and rectangles to sets are the explicit
  functions `inInterval` and `inRectangle`.
* The implicit arguments of Coq's `map_sym`, `map_trans` and `coloring_adjacent` are implicit
  here too.

The declarations between the `BEGIN SYNCED DEFINITIONS` and `END SYNCED DEFINITIONS` markers are
duplicated verbatim in the statement file `Challenge.lean` (whose imports must also be the same
as the imports of this file): the Palomar comparator requires the declarations used by the
statement of `four_color` to be identical in `Challenge.lean` and in the proof. Run
`python3 scripts/check_challenge_sync.py` after any change; never edit one copy without the other.
-/

-- BEGIN SYNCED DEFINITIONS
namespace FourColor.RealPlane

/-! ### Elementary geometry -/

/-- Coq `point`: a point of the real plane `ℝ × ℝ`. -/
structure Point where
  /-- The first (horizontal) coordinate. -/
  x : ℝ
  /-- The second (vertical) coordinate. -/
  y : ℝ

/-- Coq `region`: a set of points (a region in the common, not the topological, sense). -/
abbrev Region : Type := Point → Prop

/-- Coq `map`: a relation on points. For a plain map `m` (see `PlainMap`), `m z` is the region
of `m` that contains the point `z`. -/
abbrev Map : Type := Point → Region

/-- Coq `interval`: the open interval of `ℝ` with endpoints `lo` and `hi`
(Coq `Interval x y`). -/
structure Interval where
  /-- The (excluded) lower endpoint. -/
  lo : ℝ
  /-- The (excluded) upper endpoint. -/
  hi : ℝ

/-- Coq `rectangle`: the open rectangle `hspan × vspan` of `ℝ × ℝ`. -/
structure Rectangle where
  /-- The horizontal span. -/
  hspan : Interval
  /-- The vertical span. -/
  vspan : Interval

/-- Coq `in_interval`: the set of reals in the open interval `s`, i.e. `lo < t < hi`. -/
def inInterval (s : Interval) : ℝ → Prop :=
  fun t => s.lo < t ∧ t < s.hi

/-- Coq `in_rectangle`: the region covered by the open rectangle `rr`. -/
def inRectangle (rr : Rectangle) : Region :=
  fun z => inInterval rr.hspan z.x ∧ inInterval rr.vspan z.y

/-! ### Elementary set theory for the plane -/

/-- Coq `union`: the union of two regions. -/
def union (r1 r2 : Region) : Region :=
  fun z => r1 z ∨ r2 z

/-- Coq `intersect`: the intersection of two regions. -/
def intersect (r1 r2 : Region) : Region :=
  fun z => r1 z ∧ r2 z

/-- Coq `nonempty`: the region `r` contains some point. -/
def NonemptyRegion (r : Region) : Prop :=
  ∃ z : Point, r z

/-- Coq `subregion`: the region `r1` is included in the region `r2`. -/
def Subregion (r1 r2 : Region) : Prop :=
  ∀ z : Point, r1 z → r2 z

/-- Coq `meet`: the regions `r1` and `r2` have a common point. -/
def Meet (r1 r2 : Region) : Prop :=
  NonemptyRegion (intersect r1 r2)

/-! ### Maps: partial equivalence relations whose classes are the regions -/

/-- Coq `plain_map`: `m` is a partial equivalence relation (symmetric and transitive, not
necessarily reflexive); its equivalence classes are the regions of the map `m`. -/
structure PlainMap (m : Map) : Prop where
  /-- Coq `map_sym`. -/
  map_sym : ∀ {z1 z2 : Point}, m z1 z2 → m z2 z1
  /-- Coq `map_trans`. -/
  map_trans : ∀ {z1 z2 : Point}, m z1 z2 → Subregion (m z2) (m z1)

/-- Coq `cover`: the region covered by the map `m`, i.e. the points `z` with `m z z`. -/
def cover (m : Map) : Region :=
  fun z => m z z

/-- Coq `submap`: each region of `m1` is included in a region of `m2`. -/
def Submap (m1 m2 : Map) : Prop :=
  ∀ z : Point, Subregion (m1 z) (m2 z)

/-- Coq `at_most_regions`: the map `m` has at most `n` regions, i.e. every point covered by `m`
lies in the region of one of the points `f 0`, ..., `f (n - 1)`, for some `f`. -/
def AtMostRegions (n : ℕ) (m : Map) : Prop :=
  ∃ f : ℕ → Point, ∀ z : Point, cover m z → ∃ i : ℕ, i < n ∧ m (f i) z

/-! ### Elementary topology -/

/-- Coq `open`: the region `r` is open, i.e. each point of `r` lies in an open rectangle that is
included in `r`. -/
def Open (r : Region) : Prop :=
  ∀ z : Point, r z → ∃ u : Rectangle, inRectangle u z ∧ Subregion (inRectangle u) r

/-- Coq `closure`: the topological closure of the region `r`, i.e. the points all of whose open
neighborhoods meet `r`. -/
def closure (r : Region) : Region :=
  fun z => ∀ u : Region, Open u → u z → Meet r u

/-- Coq `connected`: the region `r` is connected, i.e. any two open sets that cover `r` and both
meet `r` must meet. -/
def Connected (r : Region) : Prop :=
  ∀ u v : Region, Open u → Open v → Subregion r (union u v) →
    Meet u r → Meet v r → Meet u v

/-- Coq `simple_map`: a plain map whose regions are open and connected. -/
structure SimpleMap (m : Map) : Prop extends PlainMap m where
  /-- Coq `simple_map_open`. -/
  simple_map_open : ∀ z : Point, Open (m z)
  /-- Coq `simple_map_connected`. -/
  simple_map_connected : ∀ z : Point, Connected (m z)

/-- Coq `finite_simple_map`: a simple map with finitely many regions. -/
structure FiniteSimpleMap (m : Map) : Prop extends SimpleMap m where
  /-- Coq `finite_simple_map_finite`. -/
  finite_simple_map_finite : ∃ n : ℕ, AtMostRegions n m

/-! ### Borders, corners, adjacency and coloring -/

/-- Coq `border`: the common border of the regions of `z1` and `z2` in `m`, i.e. the
intersection of their closures. -/
def border (m : Map) (z1 z2 : Point) : Region :=
  intersect (closure (m z1)) (closure (m z2))

/-- Coq `corner_map`: the restriction of `m` to the regions whose closure contains `z`. -/
def cornerMap (m : Map) (z : Point) : Map :=
  fun z1 z2 => m z1 z2 ∧ closure (m z1) z

/-- Coq `not_corner`: the points that belong to the closure of at most two regions of `m`. -/
def notCorner (m : Map) : Region :=
  fun z => AtMostRegions 2 (cornerMap m z)

/-- Coq `adjacent`: `z1` and `z2` lie in different regions of `m` whose common border contains a
point that is not a corner. -/
def Adjacent (m : Map) (z1 z2 : Point) : Prop :=
  ¬ m z1 z2 ∧ Meet (notCorner m) (border m z1 z2)

/-- Coq `coloring`: `k` is a coloring of `m`. The color classes are the regions of the plain map
`k`; `k` covers the same points as `m`, each region of `m` lies in a single color class, and
points of adjacent regions of `m` get different colors. -/
structure Coloring (m k : Map) : Prop extends PlainMap k where
  /-- Coq `coloring_cover`. -/
  coloring_cover : Subregion (cover k) (cover m)
  /-- Coq `coloring_consistent`. -/
  coloring_consistent : Submap m k
  /-- Coq `coloring_adjacent`. -/
  coloring_adjacent : ∀ {z1 z2 : Point}, Adjacent m z1 z2 → ¬ k z1 z2

/-- Coq `colorable_with`: the map `m` has a coloring with at most `n` colors. -/
def ColorableWith (n : ℕ) (m : Map) : Prop :=
  ∃ k : Map, Coloring m k ∧ AtMostRegions n k

end FourColor.RealPlane
-- END SYNCED DEFINITIONS
