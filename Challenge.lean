import Mathlib.Basic.Real.Basic

/-!
# The Four Color Theorem for maps in the real plane

This file states the Four Color Theorem as proved by Georges Gonthier in the Coq/Rocq
development `math-comp/fourcolor` (theorem `four_color` in `theories/proof/fourcolor.v`):

  **every simple map of the real plane can be colored with at most four colors, so that any
  two adjacent regions get different colors.**

The theorem covers *all* simple maps, including maps with infinitely many regions and
unbounded or irregular regions. Only the regions of the map must be open and connected.

## Provenance of the definitions

The definitions below transcribe, one for one and in the same order, the elementary
definitions of Gonthier's `theories/proof/realplane.v`. The Coq file is parametrized by an
abstract structure of real numbers (`Real.structure` in `reals/real.v`), and the theorem of
`fourcolor.v` assumes a model of the reals (`Real.model`); here they are specialised to Mathlib's
real numbers `ℝ`. All models of the reals are isomorphic (Coq file `realcategorical.v`), and
these definitions only use the order of the reals. Coq's `Real.lt x y` is notation for
`¬ Real.le y x`, written `x < y` here. Only basic logic, `ℕ` and `<` on `ℝ` are used. In
particular Mathlib's topology library is not used: open sets, closure and connectedness are
defined directly from open rectangles, exactly as in Coq. The same definitions are in the module
`FourColor.RealPlane` of the proof, which imports the same Mathlib file.

## Reading guide

* A `Region` is a set of points (`Point → Prop`). A `Map` is a relation on points
  (`Point → Region`).
* `PlainMap m`: `m` is a *partial equivalence relation* (symmetric and transitive, but not
  necessarily reflexive). Its equivalence classes are the regions ("countries") of the map:
  `m z` is the region containing `z`, and `cover m` (the points `z` with `m z z`) is the part
  of the plane covered by the map. Points outside `cover m`, such as the borders between
  countries, belong to no region.
* `Open r`: every point of `r` lies in an open axis-parallel rectangle included in `r`. This
  is the usual topology of `ℝ²`. `closure r` is the set of points all of whose open
  neighborhoods meet `r`.
* `Connected r`: two open sets that together cover `r` and both meet `r` must meet each
  other. For open `r`, this is the usual notion of connectedness.
* `SimpleMap m`: a plain map whose regions are open and connected.
* `border m z1 z2` is the intersection of the closures of the regions of `z1` and `z2`.
  `cornerMap m z` keeps the regions whose closure contains the point `z`. `notCorner m` is the
  set of points that lie in the closure of at most two regions of `m`.
* `Adjacent m z1 z2`: `z1` and `z2` lie in different regions of `m`, and the common border of
  these regions contains a point that is not a corner (a corner lies in the closure of three or
  more regions). For example, diagonally opposite squares of a checkerboard are not adjacent:
  their closures only share a point that is in the closure of four squares.
* `Coloring m k`: the coloring `k` is itself a plain map, whose regions are the color classes.
  It covers exactly the points covered by `m` (`coloring_cover` together with
  `coloring_consistent`). Each region of `m` lies inside a single color class
  (`coloring_consistent : Submap m k`). Points of adjacent regions get different colors
  (`coloring_adjacent`).
* `AtMostRegions n m`: all regions of `m` are among the regions of `f 0`, ..., `f (n - 1)`
  for some `f : ℕ → Point`. `ColorableWith n m`: `m` has a coloring with at most `n` colors.
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

namespace FourColor.RealPlane

/-- **The Four Color Theorem** (Coq `four_color` in `fourcolor.v`): every simple map of the real
plane has a coloring with at most four colors in which adjacent regions have different colors. -/
theorem four_color (m : Map) (h : SimpleMap m) : ColorableWith 4 m := sorry

end FourColor.RealPlane
