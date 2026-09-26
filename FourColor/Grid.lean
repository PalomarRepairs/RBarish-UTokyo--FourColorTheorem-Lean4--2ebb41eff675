/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Hypermap
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Data.List.Iterate
import Mathlib.Logic.Encodable.Basic
import Mathlib.Tactic.Ring

/-!
# Geometry over an integer grid  (port of `grid.v`)

Geometry over an integer grid, that is, raster graphics.

We define integer point arithmetic, which we then use to define coordinates for three kinds of
basic geometric objects: grid points, grid pixels (unit squares), and grid darts (pixel corners,
selecting one of the four vertices of a given pixel).  A pixel is denoted by its lower left
vertex, while a dart `d` of a pixel `p` is denoted by the subpixel of `p` in a refined
(bisected) grid, that contains the vertex `q` of `d`.

We also use a dart `d` to denote the directed pixel edge starting at the vertex of `d` and
wrapping counterclockwise around the pixel of `d`.

We define an infinite hypermap on grid darts, whose faces are pixels and nodes are grid points
(we don't represent undirected edges, however).

Interpreting darts as subpixels works rather nicely for binary grid subdivision, which is used
heavily in the construction of discrete approximations of topological regions of the real plane.

* `GPoint`         : type for grid points/pixels/darts; `GPoint` is an additive commutative group
  (Coq `gpoint`, a `zmodType`).
* `⟨x, y⟩ : GPoint`: the grid point/pixel/dart with coordinates `x y` (Coq `Gpoint x y`).
* `halfg d`        : the pixel of which the grid dart `d` is a corner of; the coordinates of
  `halfg d` are half those of its subpixel `d`.
* `oddg d`         : the vertex of the unit square congruent to the vertex of `d` in its pixel;
  the coordinates of `oddg d` are `0` or `1`, according to the parity of the coordinates of `d`
  (i.e., `oddg d` has the coordinates of `d` mod 2).
* `IsOddg q`       : `q : GPoint` is one of the unit square vertices (Coq `is_oddg`).
* `oddgP d`        : proof of `IsOddg (oddg d)`; case analysis on `oddgP` (or on `oddg_eq_or`)
  determines which vertex `oddg d` is.
* `oddgCases c b00 b01 b10 b11` : `bxy`, when `c` is `⟨x, y⟩`, `x, y ∈ {0, 1}`.
* `ccw`            : the 90 degree counterclockwise rotation of the grid point plane that
  permutes the unit square corners.
* `arcg q`         : the chord from `q` to `ccw q` (`:= ccw q - q`).
* `end0g d`        : the start vertex of dart `d`, which `d` shares with its pixel.
* `end1g d`        : the end vertex of the directed edge denoted by dart `d`.
* `gface d`        : the next dart (counterclockwise) with the same pixel as `d`.
* `gnode d`        : the next dart sitting at the same point as `d`.
* `gedge d`        : the dart denoting the edge opposite to that denoted by `d`.
* `GRegion`        : discrete pixel set (Coq `gregion := pred gpoint`), here `Set GPoint`.
* `GRect`          : type for rectangular pixel sets (coerces to `GRegion`, and has a
  membership `p ∈ r` and an inclusion `r ⊆ s`).
* `⟨x0, x1, y0, y1⟩ : GRect` : the set of pixels with coordinates `x, y` such that
  `x0 ≤ x < x1` and `y0 ≤ y < y1` (Coq `Grect x0 x1 y0 y1`).
* `extendGrect r p`: the smallest `GRect` that contains both `r` and `p`.
* `zwidth z0 z1`   : number of integers `z` in the interval `[z0, z1)`.
* `gwidth r`, `gheight r`, `garea r` : pixel width, height and area of `r : GRect`.
* `GrProper r`     : `r` is a proper (non-empty) grid rectangle (Coq `gr_proper`).
* `enumGrect r`    : list enumerating all the pixels in `r : GRect`.
* `inset r`        : the `GRect` obtained by removing a one-pixel border from `r`.
* `gtouch p`       : the 3x3 `GRect` of pixels that touch pixel `p`.
* `ltouch q`       : the 2x2 `GRect` of pixels that touch grid point `q`.
* `gchop d`        : the half-plane region delimited by the line through the edge denoted by
  dart `d`, which contains the pixel of `d`.
* `gchop1 d`       : the half-plane region delimited by the line parallel to the edge denoted by
  dart `d`, one pixel off, and that contains all pixels adjacent to the pixel of `d`.
* `gchopRect r d`  : the `GRect` corresponding to the intersection of `r` with `gchop d`.
* `gchop1Rect r d` : the `GRect` corresponding to the intersection of `r` with `gchop1 d`.
* `refineRect r`   : the `GRect` that contains exactly the subpixels of `r`, in the binary
  subdivision of the grid.

## Translation notes

* math-comp's integer division and modulus `(x %/ d)%Z`, `(x %% d)%Z` (`divz`, `modz`) are
  Lean's `x / d`, `x % d` on `ℤ` (`Int.ediv`, `Int.emod`): both are Euclidean divisions, and
  they coincide for *all* arguments (checked below by `divzMC_eq`, `modzMC_eq`).
* `p *+ 2` is `2 • p`; `iter n f x` is `f^[n] x`; `traject f x n` is `List.iterate f x n`.
* Boolean grid predicates become `Prop`s: `p ∈ r` for `r : GRect`, `p ∈ gchop d`,
  `GrProper r`; `subpred r s` becomes `r ⊆ s`; `r =1 s` becomes a pointwise `↔`.
* Coq's `is_oddg` is a `Type`-valued indexed family, used by `gchop_rect` (a `match` on the
  proof `oddgP d`).  Here `IsOddg` is a `Prop`, and `gchopRect` is defined equivalently with
  `oddgCases (oddg d)`, which selects the same branch.
* The Coq locking devices (`gedge_key`, `gedge_unlocked`, ...) are unnecessary: `gedge`,
  `gnode`, `gface` are plain definitions, and `unlock_gedge` etc. state their bodies.
* The Coq file only states `gedgeK : cancel3 gedge gnode gface`; we also package the three
  functions as the (infinite) hypermap `gridMap : Hypermap GPoint`.
-/

namespace FourColor

open Function

/-! ### Complement to `intdiv` -/

/-- math-comp `divz`, written literally (only used to check that it is Lean's `Int.ediv`). -/
private def divzMC (m d : ℤ) : ℤ :=
  match m with
  | Int.ofNat n => Int.sign d * Int.ofNat (n / d.natAbs)
  | Int.negSucc n => Int.sign d * Int.negSucc (n / d.natAbs)

/-- math-comp `modz`, written literally. -/
private def modzMC (m d : ℤ) : ℤ := m - divzMC m d * d

/-- math-comp's `divz` is Lean's `/` on `ℤ` (`Int.ediv`). -/
private theorem divzMC_eq (m d : ℤ) : divzMC m d = m / d := by
  rcases m with n | n <;> rcases d with k | k
  · rcases k with _ | k
    · simp [divzMC]
    · show Int.sign (Int.ofNat (k + 1)) * Int.ofNat (n / (k + 1)) =
        Int.ofNat n / Int.ofNat (k + 1)
      rw [show Int.sign (Int.ofNat (k + 1)) = 1 from rfl, one_mul]; rfl
  · show Int.sign (Int.negSucc k) * Int.ofNat (n / (k + 1)) = Int.ofNat n / Int.negSucc k
    rw [show Int.sign (Int.negSucc k) = -1 from rfl, neg_one_mul]; rfl
  · rcases k with _ | k
    · simp [divzMC]
    · show Int.sign (Int.ofNat (k + 1)) * Int.negSucc (n / (k + 1)) =
        Int.negSucc n / Int.ofNat (k + 1)
      rw [show Int.sign (Int.ofNat (k + 1)) = 1 from rfl, one_mul]; rfl
  · show Int.sign (Int.negSucc k) * Int.negSucc (n / (k + 1)) = Int.negSucc n / Int.negSucc k
    rw [show Int.sign (Int.negSucc k) = -1 from rfl, neg_one_mul]; rfl

/-- math-comp's `modz` is Lean's `%` on `ℤ` (`Int.emod`). -/
private theorem modzMC_eq (m d : ℤ) : modzMC m d = m % d := by
  rw [modzMC, divzMC_eq, Int.emod_def]; ring

/-- Coq `modz2` (grid.v's complement to intdiv): `x %% 2 = odd |x|`. -/
theorem modz2 (x : ℤ) : x % 2 = ((x.natAbs % 2 : ℕ) : ℤ) := by omega

/-! ### Grid points -/

/-- Grid points, pixels and darts (Coq `gpoint`; the Coq constructor `Gpoint x y` is
`⟨x, y⟩ = GPoint.mk x y`). -/
@[ext]
structure GPoint where
  /-- The first (horizontal) coordinate. -/
  x : ℤ
  /-- The second (vertical) coordinate. -/
  y : ℤ
  deriving DecidableEq

/-- Discrete pixel sets (Coq `gregion := pred gpoint`). -/
abbrev GRegion : Type := Set GPoint

namespace GPoint

/-- Coq `GridPoint.code`. -/
def code (p : GPoint) : ℤ × ℤ := (p.x, p.y)

/-- Coq `GridPoint.decode`. -/
def decode (xy : ℤ × ℤ) : GPoint := ⟨xy.1, xy.2⟩

/-- Coq `GridPoint.codeK`. -/
theorem codeK (p : GPoint) : decode (code p) = p := rfl

/-- `code` is injective (it has the left inverse `decode`). -/
theorem code_injective : Injective code := (LeftInverse.injective codeK)

/-- The countable-type instance of Coq's `gpoint` (`Countable.copy gpoint (can_type codeK)`). -/
instance : Encodable GPoint := Encodable.ofLeftInverse code decode codeK

/-- Coq `GridPoint.zero`. -/
def zero : GPoint := ⟨0, 0⟩

/-- Coq `GridPoint.opp`. -/
def opp (p : GPoint) : GPoint := ⟨-p.x, -p.y⟩

/-- Coq `GridPoint.add`. -/
def add (p₁ p₂ : GPoint) : GPoint := ⟨p₁.x + p₂.x, p₁.y + p₂.y⟩

instance : Zero GPoint := ⟨zero⟩
instance : Neg GPoint := ⟨opp⟩
instance : Add GPoint := ⟨add⟩
instance : Sub GPoint := ⟨fun p q => ⟨p.x - q.x, p.y - q.y⟩⟩
instance : SMul ℕ GPoint := ⟨fun n p => ⟨n * p.x, n * p.y⟩⟩
instance : SMul ℤ GPoint := ⟨fun n p => ⟨n * p.x, n * p.y⟩⟩

/-! Coordinates of the group operations (not in Coq). -/

@[simp] theorem zero_x : (0 : GPoint).x = 0 := rfl
@[simp] theorem zero_y : (0 : GPoint).y = 0 := rfl
@[simp] theorem add_x (p q : GPoint) : (p + q).x = p.x + q.x := rfl
@[simp] theorem add_y (p q : GPoint) : (p + q).y = p.y + q.y := rfl
@[simp] theorem neg_x (p : GPoint) : (-p).x = -p.x := rfl
@[simp] theorem neg_y (p : GPoint) : (-p).y = -p.y := rfl
@[simp] theorem sub_x (p q : GPoint) : (p - q).x = p.x - q.x := rfl
@[simp] theorem sub_y (p q : GPoint) : (p - q).y = p.y - q.y := rfl
@[simp] theorem nsmul_x (n : ℕ) (p : GPoint) : (n • p).x = n * p.x := rfl
@[simp] theorem nsmul_y (n : ℕ) (p : GPoint) : (n • p).y = n * p.y := rfl
@[simp] theorem zsmul_x (n : ℤ) (p : GPoint) : (n • p).x = n * p.x := rfl
@[simp] theorem zsmul_y (n : ℤ) (p : GPoint) : (n • p).y = n * p.y := rfl

/-- Coq `GridPoint.addA`. -/
theorem addA (p₁ p₂ p₃ : GPoint) : p₁ + (p₂ + p₃) = p₁ + p₂ + p₃ := by
  ext <;> simp only [add_x, add_y] <;> omega

/-- Coq `GridPoint.addC`. -/
theorem addC (p₁ p₂ : GPoint) : p₁ + p₂ = p₂ + p₁ := by
  ext <;> simp only [add_x, add_y] <;> omega

/-- Coq `GridPoint.add0`. -/
theorem add0 (p : GPoint) : 0 + p = p := by
  ext <;> simp only [add_x, add_y, zero_x, zero_y] <;> omega

/-- Coq `GridPoint.addN`. -/
theorem addN (p : GPoint) : -p + p = 0 := by
  ext <;> simp only [add_x, add_y, neg_x, neg_y, zero_x, zero_y] <;> omega

/-- The additive group structure of grid points (the Coq `zmodType` instance of `gpoint`). -/
instance : AddCommGroup GPoint :=
  Function.Injective.addCommGroup code code_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun p n => by simp [code])
    (fun p n => by simp [code])

end GPoint

open GPoint

/-! ### Pixels, corners and darts -/

/-- Coq `halfg d`: the pixel of which the grid dart `d` is a corner; its coordinates are half
those of `d`. -/
def halfg (d : GPoint) : GPoint := ⟨d.x / 2, d.y / 2⟩

/-- Coq `oddg d`: the unit square vertex congruent to the vertex of `d` in its pixel (the
coordinates of `d` mod 2). -/
def oddg (d : GPoint) : GPoint := ⟨d.x % 2, d.y % 2⟩

/-! Coordinates of `halfg` and `oddg` (not in Coq). -/

@[simp] theorem halfg_x (d : GPoint) : (halfg d).x = d.x / 2 := rfl
@[simp] theorem halfg_y (d : GPoint) : (halfg d).y = d.y / 2 := rfl
@[simp] theorem oddg_x (d : GPoint) : (oddg d).x = d.x % 2 := rfl
@[simp] theorem oddg_y (d : GPoint) : (oddg d).y = d.y % 2 := rfl

/-- Coq `is_oddg c`: `c` is one of the four unit square vertices. -/
inductive IsOddg : GPoint → Prop
  /-- Coq `Gpoint00`. -/
  | gpoint00 : IsOddg 0
  /-- Coq `Gpoint01`. -/
  | gpoint01 : IsOddg ⟨0, 1⟩
  /-- Coq `Gpoint11`. -/
  | gpoint11 : IsOddg ⟨1, 1⟩
  /-- Coq `Gpoint10`. -/
  | gpoint10 : IsOddg ⟨1, 0⟩

/-- Coq `oddg_cases c b00 b01 b10 b11`: `bxy` when `c = ⟨x, y⟩` with `x, y ∈ {0, 1}`. -/
def oddgCases {T : Sort*} (c : GPoint) (b00 b01 b10 b11 : T) : T :=
  if c.x = 0 then (if c.y = 0 then b00 else b01) else (if c.y = 0 then b10 else b11)

/-- `oddgCases` at the corner `0` (not in Coq). -/
@[simp] theorem oddgCases_zero {T : Sort*} (b00 b01 b10 b11 : T) :
    oddgCases 0 b00 b01 b10 b11 = b00 := by simp [oddgCases]

/-- `oddgCases` at an explicit point (not in Coq). -/
@[simp] theorem oddgCases_mk {T : Sort*} (x y : ℤ) (b00 b01 b10 b11 : T) :
    oddgCases ⟨x, y⟩ b00 b01 b10 b11 =
      if x = 0 then (if y = 0 then b00 else b01) else (if y = 0 then b10 else b11) := rfl

/-- Coq `halfg_add2`. -/
theorem halfg_add2 (p d : GPoint) : halfg (2 • p + d) = p + halfg d := by
  ext <;> simp <;> omega

/-- Coq `oddg_add2`. -/
theorem oddg_add2 (p d : GPoint) : oddg (2 • p + d) = oddg d := by
  ext <;> simp

/-- Coq `halfg_double`. -/
theorem halfg_double (p : GPoint) : halfg (2 • p) = p := by
  ext <;> simp

/-- Coq `oddg_double`. -/
theorem oddg_double (p : GPoint) : oddg (2 • p) = 0 := by
  ext <;> simp

/-- Coq `halfgK`. -/
theorem halfgK (d : GPoint) : 2 • halfg d + oddg d = d := by
  ext <;> simp <;> omega

/-- Coq `oddg_add`. -/
theorem oddg_add (d1 d2 : GPoint) : oddg (d1 + d2) = oddg (d2 + oddg d1) := by
  ext <;> simp <;> omega

/-- Coq `halfg_add`. -/
theorem halfg_add (d1 d2 : GPoint) : halfg (d1 + d2) = halfg d1 + halfg (d2 + oddg d1) := by
  ext <;> simp <;> omega

/-- Coq `oddgP`. -/
theorem oddgP (d : GPoint) : IsOddg (oddg d) := by
  have hx : d.x % 2 = 0 ∨ d.x % 2 = 1 := by omega
  have hy : d.y % 2 = 0 ∨ d.y % 2 = 1 := by omega
  have e : oddg d = ⟨d.x % 2, d.y % 2⟩ := rfl
  rw [e]
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
  · exact IsOddg.gpoint00
  · exact IsOddg.gpoint01
  · exact IsOddg.gpoint10
  · exact IsOddg.gpoint11

/-- The four unit square vertices (case analysis on `IsOddg`; not in Coq). -/
theorem IsOddg.eq_or {c : GPoint} (h : IsOddg c) :
    c = 0 ∨ c = ⟨0, 1⟩ ∨ c = ⟨1, 1⟩ ∨ c = ⟨1, 0⟩ := by
  cases h <;> simp

/-- Case analysis on `oddgP d` (the four possible values of `oddg d`; not in Coq). -/
theorem oddg_eq_or (d : GPoint) :
    oddg d = 0 ∨ oddg d = ⟨0, 1⟩ ∨ oddg d = ⟨1, 1⟩ ∨ oddg d = ⟨1, 0⟩ :=
  (oddgP d).eq_or

/-- Coq `oddg_id`. -/
theorem oddg_id {c : GPoint} (h : IsOddg c) : oddg c = c := by
  cases h <;> rfl

/-- Coq `halfg_odd`. -/
theorem halfg_odd {c : GPoint} (h : IsOddg c) : halfg c = 0 := by
  cases h <;> rfl

/-- Coq `oddg_eq`. -/
theorem oddg_eq (p : GPoint) {c : GPoint} (h : IsOddg c) : oddg (2 • p + c) = c := by
  rw [oddg_add2, oddg_id h]

/-- Coq `halfg_eq`. -/
theorem halfg_eq (p : GPoint) {c : GPoint} (h : IsOddg c) : halfg (2 • p + c) = p := by
  rw [halfg_add2, halfg_odd h, add_zero]

/-! ### Turning 90 degrees counterclockwise around the center of the unit square -/

/-- Coq `ccw`: the quarter turn counterclockwise around the center of the unit square. -/
def ccw (p : GPoint) : GPoint := ⟨1 - p.y, p.x⟩

/-- The first coordinate of `ccw p` (not in Coq). -/
@[simp] theorem ccw_x (p : GPoint) : (ccw p).x = 1 - p.y := rfl
/-- The second coordinate of `ccw p` (not in Coq). -/
@[simp] theorem ccw_y (p : GPoint) : (ccw p).y = p.x := rfl

/-- Coq `ccw_odd`. -/
theorem ccw_odd (d : GPoint) : ccw (oddg d) = oddg (ccw d) := by
  ext
  · simp only [ccw_x, oddg_x, oddg_y]; omega
  · rfl

/-- Coq `neq_ccw` (`(ccw d == d) = false`). -/
theorem neq_ccw (d : GPoint) : ccw d ≠ d := by
  intro h
  have hx := congrArg GPoint.x h
  have hy := congrArg GPoint.y h
  simp only [ccw_x, ccw_y] at hx hy
  omega

/-- Coq `ccw4`. -/
theorem ccw4 (p : GPoint) : ccw (ccw (ccw (ccw p))) = p := by
  ext <;> simp

/-- Coq `ccw2`. -/
theorem ccw2 (p : GPoint) : ccw (ccw p) = ⟨1, 1⟩ - p := by
  ext <;> simp

/-- Coq `arcg c`: the chord from `c` to `ccw c`. -/
def arcg (c : GPoint) : GPoint := ccw c - c

/-- The first coordinate of `arcg c` (not in Coq). -/
@[simp] theorem arcg_x (c : GPoint) : (arcg c).x = 1 - c.y - c.x := rfl
/-- The second coordinate of `arcg c` (not in Coq). -/
@[simp] theorem arcg_y (c : GPoint) : (arcg c).y = c.x - c.y := rfl

/-- Coq `arcg_ccw2`. -/
theorem arcg_ccw2 (c : GPoint) : arcg (ccw (ccw c)) = -arcg c := by
  ext <;> simp only [arcg_x, arcg_y, ccw_x, ccw_y, neg_x, neg_y] <;> omega

/-! ### Darts: origin and target of the directed edge denoted by a dart -/

/-- Coq `end0g d`: the start vertex of the dart `d`, shared with its pixel. -/
def end0g (d : GPoint) : GPoint := halfg d + oddg d

/-- Coq `end1g d`: the end vertex of the directed edge denoted by the dart `d`. -/
def end1g (d : GPoint) : GPoint := halfg d + ccw (oddg d)

/-- Coq `end0g_eq`. -/
theorem end0g_eq (d : GPoint) : 2 • end0g d - oddg d = d := by
  ext <;> simp [end0g] <;> omega

/-- Coq `halfg_add_odd`. -/
theorem halfg_add_odd (d : GPoint) : halfg (d + oddg d) = end0g d := by
  ext <;> simp [end0g] <;> omega

/-- Coq `end0g_sub1`. -/
theorem end0g_sub1 (d : GPoint) : end0g d - ⟨1, 1⟩ = halfg (d - ⟨1, 1⟩) := by
  ext <;> simp [end0g] <;> omega

/-! ### The infinite hypermap of a grid -/

/-- Coq `gedge d`: the dart denoting the edge opposite to that denoted by `d`. -/
def gedge (d : GPoint) : GPoint := d + (arcg (oddg d) - arcg (ccw (oddg d)))

/-- Coq `unlock_gedge`. -/
theorem unlock_gedge (d : GPoint) : gedge d = d + (arcg (oddg d) - arcg (ccw (oddg d))) := rfl

/-- Coq `gnode d`: the next dart sitting at the same point as `d`. -/
def gnode (d : GPoint) : GPoint := d - arcg (oddg d)

/-- Coq `unlock_gnode`. -/
theorem unlock_gnode (d : GPoint) : gnode d = d - arcg (oddg d) := rfl

/-- Coq `gface d`: the next dart (counterclockwise) with the same pixel as `d`. -/
def gface (d : GPoint) : GPoint := d + arcg (oddg d)

/-- Coq `unlock_gface`. -/
theorem unlock_gface (d : GPoint) : gface d = d + arcg (oddg d) := rfl

/-- Coq `oddg_face`. -/
theorem oddg_face (d : GPoint) : oddg (gface d) = ccw (oddg d) := by
  ext <;> simp [gface] <;> omega

/-- Coq `halfg_face`. -/
theorem halfg_face (d : GPoint) : halfg (gface d) = halfg d := by
  ext <;> simp [gface] <;> omega

/-- Coq `halfg_iter_face`. -/
theorem halfg_iter_face (i : ℕ) (d : GPoint) : halfg (gface^[i] d) = halfg d := by
  induction i with
  | zero => rfl
  | succ i ih => rw [iterate_succ_apply', halfg_face, ih]

/-- Coq `oddg_iter_face`. -/
theorem oddg_iter_face (i : ℕ) (d : GPoint) : oddg (gface^[i] d) = ccw^[i] (oddg d) := by
  induction i with
  | zero => rfl
  | succ i ih => rw [iterate_succ_apply', iterate_succ_apply', oddg_face, ih]

/-- Coq `gface_def`. -/
theorem gface_def (d : GPoint) : gface d = 2 • halfg d + ccw (oddg d) := by
  rw [← halfg_face, ← oddg_face, halfgK]

/-- Coq `gface4`. -/
theorem gface4 (d : GPoint) : gface (gface (gface (gface d))) = d := by
  rw [gface_def, halfg_face, halfg_face, halfg_face, oddg_face, oddg_face, oddg_face, ccw4,
    halfgK]

/-- Coq `end0g_face`. -/
theorem end0g_face (d : GPoint) : end0g (gface d) = end1g d := by
  rw [end0g, oddg_face, halfg_face, end1g]

/-- The iterates of `gface`: `gface^[k] d = 2 • halfg d + ccw^[k] (oddg d)` (not in Coq). -/
theorem iter_face_eq (k : ℕ) (d : GPoint) : gface^[k] d = 2 • halfg d + ccw^[k] (oddg d) := by
  rw [← halfg_iter_face k d, ← oddg_iter_face k d, halfgK]

/-- `ccw` cycles through the four unit square vertices (not in Coq). -/
theorem exists_iter_ccw {c1 c2 : GPoint} (h1 : IsOddg c1) (h2 : IsOddg c2) :
    ∃ k < 4, ccw^[k] c1 = c2 := by
  rcases h1.eq_or with rfl | rfl | rfl | rfl <;> rcases h2.eq_or with rfl | rfl | rfl | rfl <;>
    first
    | exact ⟨0, by decide, by decide⟩
    | exact ⟨1, by decide, by decide⟩
    | exact ⟨2, by decide, by decide⟩
    | exact ⟨3, by decide, by decide⟩

/-- Coq `same_halfg`. -/
theorem same_halfg {d1 d2 : GPoint} (h : halfg d1 = halfg d2) :
    d2 ∈ List.iterate gface d1 4 := by
  rw [List.mem_iterate]
  obtain ⟨k, hk, hk'⟩ := exists_iter_ccw (oddgP d1) (oddgP d2)
  exact ⟨k, hk, by rw [iter_face_eq, hk', h, halfgK]⟩

/-- Coq `gnode_sub1`. -/
theorem gnode_sub1 (d : GPoint) : gnode d - ⟨1, 1⟩ = gface (d - ⟨1, 1⟩) := by
  ext <;> simp [gnode, gface] <;> omega

/-- Coq `oddg_node`. -/
theorem oddg_node (d : GPoint) : oddg (gnode d) = ccw (oddg d) := by
  ext <;> simp [gnode] <;> omega

/-- Coq `halfg_node`. -/
theorem halfg_node (d : GPoint) : halfg (gnode d) = halfg d - arcg (oddg d) := by
  ext <;> simp [gnode] <;> omega

/-- Coq `neq_halfg_node` (`(halfg p == halfg (gnode p)) = false`). -/
theorem neq_halfg_node (p : GPoint) : halfg p ≠ halfg (gnode p) := by
  intro h
  have hx := congrArg GPoint.x h
  have hy := congrArg GPoint.y h
  simp [gnode] at hx hy
  omega

/-- Coq `end0g_node`. -/
theorem end0g_node (d : GPoint) : end0g (gnode d) = end0g d := by
  ext <;> simp [end0g, gnode] <;> omega

/-- Coq `gnode4`. -/
theorem gnode4 (d : GPoint) : gnode (gnode (gnode (gnode d))) = d := by
  have h : gnode (gnode (gnode (gnode d))) - ⟨1, 1⟩ = d - ⟨1, 1⟩ := by
    rw [gnode_sub1, gnode_sub1, gnode_sub1, gnode_sub1, gface4]
  exact sub_left_injective h

/-- The iterates of `gnode`, shifted by `⟨1, 1⟩`, are the iterates of `gface` (not in Coq). -/
theorem iter_node_sub1 (k : ℕ) (d : GPoint) :
    gnode^[k] d - ⟨1, 1⟩ = gface^[k] (d - ⟨1, 1⟩) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply', iterate_succ_apply', gnode_sub1, ih]

/-- Coq `same_end0g`. -/
theorem same_end0g {d1 d2 : GPoint} (h : end0g d1 = end0g d2) :
    d2 ∈ List.iterate gnode d1 4 := by
  have h' : halfg (d1 - ⟨1, 1⟩) = halfg (d2 - ⟨1, 1⟩) := by
    rw [← end0g_sub1, ← end0g_sub1, h]
  have := same_halfg h'
  rw [List.mem_iterate] at this ⊢
  obtain ⟨k, hk, hk'⟩ := this
  refine ⟨k, hk, sub_left_injective (b := (⟨1, 1⟩ : GPoint)) ?_⟩
  simp only
  rw [iter_node_sub1, hk']

/-- Coq `gnode_face`. -/
theorem gnode_face (d : GPoint) : gnode (gface d) = gedge d := by
  rw [unlock_gnode, oddg_face, unlock_gface, unlock_gedge, add_sub_assoc]

/-- Coq `oddg_edge`. -/
theorem oddg_edge (p : GPoint) : oddg (gedge p) = ccw (ccw (oddg p)) := by
  rw [← gnode_face, oddg_node, oddg_face]

/-- Coq `halfg_edge`. -/
theorem halfg_edge (p : GPoint) : halfg (gedge p) = halfg p - arcg (ccw (oddg p)) := by
  rw [← gnode_face, halfg_node, halfg_face, oddg_face]

/-- Coq `neq_halfg_edge` (`(halfg p == halfg (gedge p)) = false`). -/
theorem neq_halfg_edge (p : GPoint) : halfg p ≠ halfg (gedge p) := by
  rw [halfg_edge]
  intro h
  have hx := congrArg GPoint.x h
  have hy := congrArg GPoint.y h
  simp at hx hy
  omega

/-- Coq `end0g_edge`. -/
theorem end0g_edge (p : GPoint) : end0g (gedge p) = end1g p := by
  rw [← gnode_face, end0g_node, end0g_face]

/-- Coq `gedge2`. -/
theorem gedge2 (p : GPoint) : gedge (gedge p) = p := by
  rw [unlock_gedge (gedge p), oddg_edge, arcg_ccw2, arcg_ccw2, unlock_gedge]
  ext <;> simp only [add_x, add_y, sub_x, sub_y, neg_x, neg_y] <;> omega

/-- Coq `end1g_edge`. -/
theorem end1g_edge (p : GPoint) : end1g (gedge p) = end0g p := by
  rw [← end0g_edge, gedge2]

/-- Coq `gedgeK` (`cancel3 gedge gnode gface`). -/
theorem gedgeK (d : GPoint) : gnode (gface (gedge d)) = d := by
  rw [gnode_face, gedge2]

/-- Coq `gfaceK` (`cancel3 gface gedge gnode`). -/
theorem gfaceK (d : GPoint) : gedge (gnode (gface d)) = d := by
  rw [gnode_face, gedge2]

/-- Coq `gnodeK` (`cancel3 gnode gface gedge`). -/
theorem gnodeK (d : GPoint) : gface (gedge (gnode d)) = d := by
  have h := gfaceK (gface (gface (gface d)))
  rw [gface4] at h
  rw [h, gface4]

/-- The infinite grid hypermap on darts, with faces the pixels and nodes the grid points
(not a named definition in Coq, which only proves `gedgeK`). -/
def gridMap : Hypermap GPoint := ⟨gedge, gnode, gface, gedgeK⟩

/-! Explicit coordinates of the grid hypermap functions (not in Coq; used for arithmetic). -/

/-- The first coordinate of `gface d`. -/
theorem gface_x (d : GPoint) : (gface d).x = d.x + 1 - d.y % 2 - d.x % 2 := by
  simp only [gface, add_x, arcg_x, oddg_x, oddg_y]; ring

/-- The second coordinate of `gface d`. -/
theorem gface_y (d : GPoint) : (gface d).y = d.y + d.x % 2 - d.y % 2 := by
  simp only [gface, add_y, arcg_y, oddg_x, oddg_y]; ring

/-- The first coordinate of `gnode d`. -/
theorem gnode_x (d : GPoint) : (gnode d).x = d.x - 1 + d.y % 2 + d.x % 2 := by
  simp only [gnode, sub_x, arcg_x, oddg_x, oddg_y]; ring

/-- The second coordinate of `gnode d`. -/
theorem gnode_y (d : GPoint) : (gnode d).y = d.y - d.x % 2 + d.y % 2 := by
  simp only [gnode, sub_y, arcg_y, oddg_x, oddg_y]; ring

/-- The first coordinate of `gedge d`. -/
theorem gedge_x (d : GPoint) : (gedge d).x = d.x + 1 - 2 * (d.y % 2) := by
  simp only [gedge, add_x, sub_x, arcg_x, ccw_x, ccw_y, oddg_x, oddg_y]; ring

/-- The second coordinate of `gedge d`. -/
theorem gedge_y (d : GPoint) : (gedge d).y = d.y + 2 * (d.x % 2) - 1 := by
  simp only [gedge, add_y, sub_y, arcg_y, ccw_x, ccw_y, oddg_x, oddg_y]; ring

/-- The first coordinate of `end0g d`. -/
theorem end0g_x (d : GPoint) : (end0g d).x = d.x / 2 + d.x % 2 := rfl

/-- The second coordinate of `end0g d`. -/
theorem end0g_y (d : GPoint) : (end0g d).y = d.y / 2 + d.y % 2 := rfl

/-- The first coordinate of `end1g d`. -/
theorem end1g_x (d : GPoint) : (end1g d).x = d.x / 2 + (1 - d.y % 2) := rfl

/-- The second coordinate of `end1g d`. -/
theorem end1g_y (d : GPoint) : (end1g d).y = d.y / 2 + d.x % 2 := rfl

/-- The origins of the four darts of a pixel (not in Coq). -/
theorem end0g_iter_face (k : ℕ) (d : GPoint) :
    end0g (gface^[k] d) = halfg d + ccw^[k] (oddg d) := by
  rw [end0g, halfg_iter_face, oddg_iter_face]

/-! ### Rectangles on the grid -/

/-- Coq `grect`: the rectangular pixel set `Grect xmin xmax ymin ymax` of the pixels
`⟨x, y⟩` with `xmin ≤ x < xmax` and `ymin ≤ y < ymax`. -/
structure GRect where
  /-- Lower bound (inclusive) of the first coordinate. -/
  xmin : ℤ
  /-- Upper bound (exclusive) of the first coordinate. -/
  xmax : ℤ
  /-- Lower bound (inclusive) of the second coordinate. -/
  ymin : ℤ
  /-- Upper bound (exclusive) of the second coordinate. -/
  ymax : ℤ
  deriving DecidableEq

/-- Coq coercion `in_grect : grect >-> gregion`. -/
def inGrect (r : GRect) : GRegion :=
  {p | (r.xmin ≤ p.x ∧ p.x < r.xmax) ∧ (r.ymin ≤ p.y ∧ p.y < r.ymax)}

instance : Coe GRect GRegion := ⟨inGrect⟩

/-- `p ∈ r` for a rectangle `r` (Coq `r p`, through the coercion `in_grect`). -/
instance : Membership GPoint GRect := ⟨fun r p => p ∈ inGrect r⟩

/-- `r ⊆ s` for rectangles `r s` (Coq `subpred r s`). -/
instance : HasSubset GRect := ⟨fun r s => ∀ p, p ∈ r → p ∈ s⟩

/-- Membership in a rectangle, explicitly. -/
theorem mem_grect {r : GRect} {p : GPoint} :
    p ∈ r ↔ (r.xmin ≤ p.x ∧ p.x < r.xmax) ∧ (r.ymin ≤ p.y ∧ p.y < r.ymax) := Iff.rfl

/-- Membership in the region of a rectangle. -/
@[simp] theorem mem_inGrect {r : GRect} {p : GPoint} : p ∈ (r : GRegion) ↔ p ∈ r := Iff.rfl

/-- Inclusion of rectangles, explicitly. -/
theorem GRect.subset_def {r s : GRect} : r ⊆ s ↔ ∀ p, p ∈ r → p ∈ s := Iff.rfl

/-- Inclusion of rectangles is inclusion of their regions. -/
theorem GRect.coe_subset {r s : GRect} : (r : GRegion) ⊆ s ↔ r ⊆ s := Iff.rfl

instance (r : GRect) (p : GPoint) : Decidable (p ∈ r) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∧ (_ ∧ _)))

/-! ### Extending a rectangle to cover a specific pixel -/

/-- Coq `extend_grect p r`: the smallest rectangle containing `r` and the pixel `p`. -/
def extendGrect (p : GPoint) (r : GRect) : GRect :=
  ⟨min r.xmin p.x, max r.xmax (p.x + 1), min r.ymin p.y, max r.ymax (p.y + 1)⟩

/-- Coq `in_extend_grect`. -/
theorem in_extend_grect (p : GPoint) (r : GRect) :
    ∀ q, q = p ∨ q ∈ r → q ∈ extendGrect p r := by
  rintro q (rfl | h)
  · simp only [mem_grect, extendGrect]; omega
  · simp only [mem_grect, extendGrect] at h ⊢; omega

/-! ### Rectangle dimensions and enumeration -/

/-- Coq `zwidth xmin xmax`: the number of integers in `[xmin, xmax)`. -/
def zwidth (xmin xmax : ℤ) : ℕ := (xmax - xmin).toNat

/-- Coq `gwidth r`. -/
def gwidth (r : GRect) : ℕ := zwidth r.xmin r.xmax

/-- Coq `gheight r`. -/
def gheight (r : GRect) : ℕ := zwidth r.ymin r.ymax

/-- Coq `garea r`. -/
def garea (r : GRect) : ℕ := gwidth r * gheight r

/-- Coq `gr_proper r`: `r` is a non-empty rectangle. -/
def GrProper (r : GRect) : Prop := 0 < garea r

instance (r : GRect) : Decidable (GrProper r) := inferInstanceAs (Decidable (0 < garea r))

/-- Coq `zspan xmin xmax`: the list `[xmin, xmin + 1, ..., xmax - 1]`. -/
def zspan (xmin xmax : ℤ) : List ℤ := List.iterate (· + 1) xmin (zwidth xmin xmax)

/-- Coq `enum_grect r`: the pixels of `r`, as the list
`[⟨x, y⟩ | x <- zspan xmin xmax, y <- zspan ymin ymax]`. -/
def enumGrect (r : GRect) : List GPoint :=
  (zspan r.xmin r.xmax).flatMap fun x => (zspan r.ymin r.ymax).map fun y => ⟨x, y⟩

/-- Coq `size_zspan`. -/
theorem size_zspan (xmin xmax : ℤ) : (zspan xmin xmax).length = zwidth xmin xmax :=
  List.length_iterate _ _ _

private theorem length_flatMap_map {α β γ : Type*} (f : α → β → γ) (s : List α) (t : List β) :
    (s.flatMap fun x => t.map (f x)).length = s.length * t.length := by
  induction s with
  | nil => simp
  | cons a s ih => simp [List.flatMap_cons, ih, Nat.succ_mul, Nat.add_comm]

/-- Coq `size_enum_grect`. -/
theorem size_enum_grect (r : GRect) : (enumGrect r).length = garea r := by
  rw [enumGrect, length_flatMap_map (fun x y => (⟨x, y⟩ : GPoint)), size_zspan, size_zspan]
  rfl

private theorem iterate_add_one (m : ℕ) (a : ℤ) : (· + (1 : ℤ))^[m] a = a + m := by
  induction m generalizing a with
  | zero => simp
  | succ m ih => rw [iterate_succ_apply, ih]; push_cast; ring

/-- Coq `mem_zspan`. -/
theorem mem_zspan (xmin xmax x : ℤ) : x ∈ zspan xmin xmax ↔ xmin ≤ x ∧ x < xmax := by
  rw [zspan, List.mem_iterate]
  constructor
  · rintro ⟨m, hm, rfl⟩
    rw [iterate_add_one]
    unfold zwidth at hm
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨(x - xmin).toNat, ?_, ?_⟩
    · unfold zwidth; omega
    · rw [iterate_add_one]; omega

/-- Coq `mem_enum_grect`. -/
theorem mem_enum_grect (r : GRect) (p : GPoint) : p ∈ enumGrect r ↔ p ∈ r := by
  rw [enumGrect, List.mem_flatMap, mem_grect]
  constructor
  · rintro ⟨x, hx, hp⟩
    rw [List.mem_map] at hp
    obtain ⟨y, hy, rfl⟩ := hp
    exact ⟨(mem_zspan _ _ _).1 hx, (mem_zspan _ _ _).1 hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨p.x, (mem_zspan _ _ _).2 hx, List.mem_map.2 ⟨p.y, (mem_zspan _ _ _).2 hy, rfl⟩⟩

/-- Coq `gr_properP`. -/
theorem gr_properP (r : GRect) : GrProper r ↔ ∃ p, p ∈ r := by
  rw [GrProper, ← size_enum_grect, List.length_pos_iff_exists_mem]
  simp only [mem_enum_grect]

/-- Coq `zspan_uniq`. -/
theorem zspan_uniq (xmin xmax : ℤ) : (zspan xmin xmax).Nodup := by
  rw [zspan]
  generalize zwidth xmin xmax = n
  induction n generalizing xmin with
  | zero => exact List.nodup_nil
  | succ n ih =>
    rw [show List.iterate (· + (1 : ℤ)) xmin (n + 1) =
      xmin :: List.iterate (· + 1) (xmin + 1) n from rfl, List.nodup_cons]
    refine ⟨?_, ih _⟩
    rw [List.mem_iterate]
    rintro ⟨m, _, hm⟩
    rw [iterate_add_one] at hm
    omega

/-- Coq `enum_grect_uniq`. -/
theorem enum_grect_uniq (r : GRect) : (enumGrect r).Nodup := by
  rw [enumGrect, List.nodup_flatMap]
  refine ⟨fun x _ => (zspan_uniq _ _).map fun y1 y2 h => by cases h; rfl, ?_⟩
  refine (zspan_uniq _ _).pairwise_of_forall_ne fun x1 _ x2 _ hne => ?_
  simp only [Function.onFun, List.disjoint_left, List.mem_map]
  rintro _ ⟨y1, _, rfl⟩ ⟨y2, _, h⟩
  exact hne (congrArg GPoint.x h).symm

/-- Coq `garea_subrect`. -/
theorem garea_subrect {r s : GRect} (h : r ⊆ s) : garea r ≤ garea s := by
  rw [← size_enum_grect, ← size_enum_grect]
  refine ((enum_grect_uniq r).subperm fun p hp => ?_).length_le
  rw [mem_enum_grect] at hp ⊢
  exact h p hp

/-- Coq `ltn_garea_subrect` (`predD s r p` is `p ∉ r ∧ p ∈ s`). -/
theorem ltn_garea_subrect (p : GPoint) {r s : GRect} (h : r ⊆ s) (hp : p ∉ r ∧ p ∈ s) :
    garea r < garea s := by
  rw [← size_enum_grect, ← size_enum_grect]
  have hnd : (p :: enumGrect r).Nodup := by
    rw [List.nodup_cons, mem_enum_grect]
    exact ⟨hp.1, enum_grect_uniq r⟩
  have := (hnd.subperm (l₂ := enumGrect s) fun q hq => ?_).length_le
  · simpa using this
  · rw [mem_enum_grect]
    rcases List.mem_cons.1 hq with rfl | hq
    · exact hp.2
    · exact h q ((mem_enum_grect r q).1 hq)

/-- Coq `gtouch p`: the 3x3 rectangle of the pixels that surround (touch) the pixel `p`. -/
def gtouch (p : GPoint) : GRect := ⟨p.x - 1, p.x + 2, p.y - 1, p.y + 2⟩

/-- Coq `ltouch q`: the 2x2 rectangle of the pixels that surround the grid point `q`. -/
def ltouch (q : GPoint) : GRect := ⟨q.x - 1, q.x + 1, q.y - 1, q.y + 1⟩

/-- Coq `subgrectE`. -/
theorem subgrectE {x0 x1 x2 x3 y0 y1 y2 y3 : ℤ}
    (h : x0 ≤ x1 ∧ x2 ≤ x3 ∧ y0 ≤ y1 ∧ y2 ≤ y3) :
    (⟨x1, x2, y1, y2⟩ : GRect) ⊆ ⟨x0, x3, y0, y3⟩ := by
  intro p hp
  simp only [mem_grect] at hp ⊢
  omega

/-- Coq `gtouch_l`. -/
theorem gtouch_l (p : GPoint) : ltouch p ⊆ gtouch p := by
  intro q hq
  simp only [mem_grect, ltouch, gtouch] at hq ⊢
  omega

/-- Coq `ltouch_refl`. -/
theorem ltouch_refl (q : GPoint) : q ∈ ltouch q := by
  simp only [mem_grect, ltouch]; omega

/-- Coq `gtouch_refl`. -/
theorem gtouch_refl (p : GPoint) : p ∈ gtouch p := by
  simp only [mem_grect, gtouch]; omega

/-- Coq `gtouch_edge`. -/
theorem gtouch_edge (d : GPoint) : halfg (gedge d) ∈ gtouch (halfg d) := by
  rw [halfg_edge]
  simp only [mem_grect, gtouch, sub_x, sub_y, arcg_x, arcg_y, ccw_x, ccw_y, oddg_x, oddg_y]
  omega

/-- Coq `zspan_dec_inc` (explicit computation of `gtouch` and `ltouch` enumerations). -/
theorem zspan_dec_inc (x : ℤ) (n : ℕ) :
    zspan (x - 1) (x + n) = (x - 1) :: List.iterate (· + 1) x n := by
  have h : zwidth (x - 1) (x + n) = n + 1 := by unfold zwidth; omega
  rw [zspan, h, show List.iterate (· + (1 : ℤ)) (x - 1) (n + 1) =
      (x - 1) :: List.iterate (· + 1) (x - 1 + 1) n from rfl, sub_add_cancel]

/-! ### Shaving one row or column of pixels on each side of a rectangle -/

/-- Coq `inset r`: the rectangle `r` with a one-pixel border removed. -/
def inset (r : GRect) : GRect := ⟨r.xmin + 1, r.xmax - 1, r.ymin + 1, r.ymax - 1⟩

/-- Coq `insetP`. -/
theorem insetP {r : GRect} {p : GPoint} : p ∈ inset r ↔ gtouch p ⊆ r := by
  constructor
  · intro h q hq
    simp only [mem_grect, inset, gtouch] at h hq ⊢
    omega
  · intro h
    have h1 := h ⟨p.x + 1, p.y + 1⟩ (by simp only [mem_grect, gtouch]; omega)
    have h2 := h ⟨p.x + -1, p.y + -1⟩ (by simp only [mem_grect, gtouch]; omega)
    simp only [mem_grect, inset] at h1 h2 ⊢
    omega

/-- Coq `insetW`. -/
theorem insetW (r : GRect) : inset r ⊆ r := fun p hp => insetP.1 hp p (gtouch_refl p)

/-! ### The half-grid that lies counterclockwise from a dart -/

/-- Coq `gchop d`: the half-plane region delimited by the line through the edge denoted by
the dart `d`, and containing the pixel of `d`. -/
def gchop (d : GPoint) : GRegion :=
  {p | oddgCases (oddg d) ((halfg d).y ≤ p.y) ((halfg d).x ≤ p.x) (p.x ≤ (halfg d).x)
    (p.y ≤ (halfg d).y)}

/-- Membership in `gchop d`, explicitly. -/
theorem mem_gchop {d p : GPoint} :
    p ∈ gchop d ↔ oddgCases (oddg d) ((halfg d).y ≤ p.y) ((halfg d).x ≤ p.x)
      (p.x ≤ (halfg d).x) (p.y ≤ (halfg d).y) := Iff.rfl

instance (d p : GPoint) : Decidable (p ∈ gchop d) := by
  rw [mem_gchop, oddgCases]; infer_instance

/-- Coq `gchop_halfg`. -/
theorem gchop_halfg (d : GPoint) : halfg d ∈ gchop d := by
  rw [mem_gchop]
  rcases oddg_eq_or d with h | h | h | h <;> simp [h]

/-- Coq `eq_gchop_halfg`. -/
theorem eq_gchop_halfg (d p : GPoint) (h : halfg d = p) : p ∈ gchop d := h ▸ gchop_halfg d

/-- Coq `gchop_edge`. -/
theorem gchop_edge (d p : GPoint) : p ∈ gchop (gedge d) ↔ p ∉ gchop d := by
  rw [mem_gchop, mem_gchop, halfg_edge, oddg_edge]
  rcases oddg_eq_or d with h | h | h | h <;> simp [h, ccw] <;> omega

/-- Coq `gchop_face_node`. -/
theorem gchop_face_node (d : GPoint) : gchop (gface (gnode d)) = gchop (gface (gface d)) := by
  ext p
  rw [mem_gchop, mem_gchop, halfg_face, halfg_face, halfg_face, oddg_face, oddg_face, oddg_face,
    halfg_node, oddg_node]
  rcases oddg_eq_or d with h | h | h | h <;> simp [h, ccw]

/-- Coq `gchop_shift`. -/
theorem gchop_shift (d : GPoint) : gchop (gface (gedge (gface d))) = gchop d := by
  rw [← gnode_face, gchop_face_node, gface4]

/-! ### The same half-grids, extended by a unit band -/

/-- Coq `gchop1 d`: the half-plane `gchop d` extended by a unit band. -/
def gchop1 (d : GPoint) : GRegion := gchop (gface (gface (gedge d)))

/-- An explicit description of `gchop1` (not in Coq). -/
theorem mem_gchop1 {d p : GPoint} :
    p ∈ gchop1 d ↔ oddgCases (oddg d) ((halfg d).y - 1 ≤ p.y) ((halfg d).x - 1 ≤ p.x)
      (p.x ≤ (halfg d).x + 1) (p.y ≤ (halfg d).y + 1) := by
  rw [gchop1, mem_gchop, halfg_face, halfg_face, oddg_face, oddg_face, halfg_edge, oddg_edge,
    ccw4]
  rcases oddg_eq_or d with h | h | h | h <;> simp [h, ccw]

instance (d p : GPoint) : Decidable (p ∈ gchop1 d) :=
  inferInstanceAs (Decidable (p ∈ gchop _))

/-- Coq `gchop_chop1`. -/
theorem gchop_chop1 (d : GPoint) : gchop d ⊆ gchop1 d := by
  intro p hp
  rw [mem_gchop] at hp
  rw [mem_gchop1]
  rcases oddg_eq_or d with h | h | h | h <;> rw [h] at hp ⊢ <;> simp at hp ⊢ <;> omega

/-- Coq `gtouch_chop1`. -/
theorem gtouch_chop1 (d p : GPoint) :
    p ∈ gtouch (halfg d) ↔ ∀ e ∈ List.iterate gface d 4, p ∈ gchop1 e := by
  simp only [List.iterate, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, mem_gchop1, halfg_face, oddg_face, mem_grect, gtouch]
  rcases oddg_eq_or d with h | h | h | h <;> simp [h, ccw] <;> omega

/-- Coq `gchop1_shift`. -/
theorem gchop1_shift (d : GPoint) : gchop1 (gface (gedge (gface d))) = gchop1 d := by
  ext p
  rw [mem_gchop1, mem_gchop1, halfg_face, oddg_face, halfg_edge, oddg_edge, halfg_face,
    oddg_face, ccw4]
  rcases oddg_eq_or d with h | h | h | h <;> simp [h, ccw]

/-! ### Chopping off half of a rectangle -/

section ChopRect

variable (r : GRect)

/-- Coq `gchop_rect r d`: the rectangle `r` intersected with the half-plane `gchop d` (the
dividing line is given as the side of an internal square). -/
def gchopRect (d : GPoint) : GRect :=
  oddgCases (oddg d)
    ⟨r.xmin, r.xmax, max r.ymin (halfg d).y, r.ymax⟩
    ⟨max r.xmin (halfg d).x, r.xmax, r.ymin, r.ymax⟩
    ⟨r.xmin, min r.xmax ((halfg d).x + 1), r.ymin, r.ymax⟩
    ⟨r.xmin, r.xmax, r.ymin, min r.ymax ((halfg d).y + 1)⟩

/-- Coq `in_gchop_rect`. -/
theorem in_gchop_rect (d p : GPoint) : p ∈ gchopRect r d ↔ p ∈ r ∧ p ∈ gchop d := by
  rw [gchopRect, mem_gchop, mem_grect]
  rcases oddg_eq_or d with h | h | h | h <;> simp [h, mem_grect] <;> omega

/-- Coq `gchop_rect_sub`. -/
theorem gchop_rect_sub (d : GPoint) : gchopRect r d ⊆ r :=
  fun p hp => ((in_gchop_rect r d p).1 hp).1

/-- Coq `gchop_rect_edge`. -/
theorem gchop_rect_edge (d : GPoint) (hr : halfg (gedge d) ∈ r) :
    ∀ p, p ∈ gchopRect r d → halfg d ∈ gchopRect r d := by
  intro p hp
  rw [in_gchop_rect] at hp ⊢
  refine ⟨?_, gchop_halfg d⟩
  obtain ⟨hpr, hpd⟩ := hp
  rw [halfg_edge] at hr
  rw [mem_gchop] at hpd
  rw [mem_grect] at hr hpr ⊢
  rcases oddg_eq_or d with h | h | h | h <;> simp [h, ccw] at hr hpd ⊢ <;> omega

/-- Coq `gchop1_rect r d`. -/
def gchop1Rect (d : GPoint) : GRect := gchopRect r (gface (gface (gedge d)))

/-- Coq `in_gchop1_rect`. -/
theorem in_gchop1_rect (d p : GPoint) : p ∈ gchop1Rect r d ↔ p ∈ r ∧ p ∈ gchop1 d :=
  in_gchop_rect r _ p

end ChopRect

/-! ### Grid refinement, which doubles coordinates and rectangle bounds -/

/-- Coq `refine_rect r`: the rectangle of the subpixels of `r` in the refined grid. -/
def refineRect (r : GRect) : GRect := ⟨2 * r.xmin, 2 * r.xmax, 2 * r.ymin, 2 * r.ymax⟩

/-- Coq `in_refine_rect`. -/
theorem in_refine_rect (r : GRect) (p : GPoint) : p ∈ refineRect r ↔ halfg p ∈ r := by
  simp only [mem_grect, refineRect, halfg_x, halfg_y]
  omega

private theorem zwidth_double (x y : ℤ) : zwidth (2 * x) (2 * y) = 2 * zwidth x y := by
  unfold zwidth; omega

/-- Coq `garea_refine_rect`. -/
theorem garea_refine_rect (r : GRect) : garea (refineRect r) = 2 * (2 * garea r) := by
  simp only [garea, gwidth, gheight, refineRect, zwidth_double]
  ring

/-- Coq `refine_inset`. -/
theorem refine_inset (r : GRect) : refineRect (inset r) = inset (inset (refineRect r)) := by
  simp only [refineRect, inset, GRect.mk.injEq]
  omega

/-- Coq `gr_proper_refine`. -/
theorem gr_proper_refine (s : ℕ) (r : GRect) : GrProper (refineRect^[s] r) ↔ GrProper r := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [iterate_succ_apply', GrProper, garea_refine_rect, ← ih, GrProper]
    omega

end FourColor
