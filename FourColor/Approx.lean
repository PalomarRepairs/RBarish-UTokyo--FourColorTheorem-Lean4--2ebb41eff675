/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.RealPlane
import FourColor.Matte
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.Linarith

/-!
# Approximations  (port of `approx.v`)

Approximations of real scalars, points, regions and rectangles, used to cast the continuous four
color problem into a combinatorial form. Because the grid decomposition is based on dichotomy,
the real coordinates are approximated with binary decimals (i.e., floating point numbers),
rather than arbitrary rationals.

* `range1 x`         : the unit interval `[x, x + 1)` (from Coq's `realprop.v`).
* `exp2R s`          : `2 ^ s` as a real number, for `s : ℕ`.
* `scale s m`        : the integer `m` scaled back by `s`, as a real (i.e., `m / 2 ^ s`).
* `scalePoint s p`   : the grid point `p` scaled back by `s`, as a `Point`.
* `Approx s x m`     : `m` is the integer approximation of the real `x` at scale `s`,
  i.e., `m ≤ 2 ^ s * x < m + 1`.
* `ApproxPoint s z p` : the grid point `p` is the approximation of the point `z` at scale `s`.
* `memApprox s gr z` : the approximation of `z` at scale `s` is in the grid region `gr`.
* `ScaledRect`       : pairs of a natural scale and a grid rectangle; `srectRegion b` is the
  (rectangular) region of `b`, via `memApprox`.
* `refineSrect s b`  : the scaled rectangle obtained by increasing the scale of `b` by `s` while
  simultaneously scaling the coordinates of `b` by `s`, so that `b` and `refineSrect s b` have
  the same region.
* `insetSrect b`     : the scaled rectangle inset one grid pixel from `b`; this insets the
  corresponding real region by `1 / 2 ^ s` on all sides.
* `capInterval xz1 xz2` : the intersection of two intervals (a possibly empty interval).
* `capRect r1 r2`    : the rectangle intersection of two rectangles.
* `sepInterval x1 x2` : a separating interval containing `x2` and NOT containing `x1`, provided
  `x1 ≠ x2`.
* `sepRect z1 z2`    : a separating rectangle containing `z2` but not `z1`, unless `z1 = z2`.
* `ScaledMatte`      : pairs of a natural scale and a grid matte; `smatteRegion m` is the
  (polygonal) region of `m`, via `memApprox`.
* `refineSmatte s m` : the scaled matte obtained by increasing the scale of `m` by `s` while
  simultaneously scaling the coordinates of `m` by `s`, so that `m` and `refineSmatte s m` have
  the same region.

## Translation notes

* Coq's abstract `Real.model R` is Mathlib's `ℝ`; the section variable `R` disappears, and so
  does the phantom parameter `R` of `scaled_rect R` and `scaled_matte R`.
* Coq's setoid equality `==` of reals is `=` (`exp2RS`, `exp2R_add`, `meet_sep_interval`), and
  the setoid morphism instance `approx_Proper` has no counterpart.
* Coq's real-valued `floor x` is Mathlib's `Int.floor x` (`⌊x⌋ : ℤ`), so realprop.v's
  `range1z_floor` states `⌊x⌋ = m` instead of `floor x == m`; the coercion `intR : int -> R` is
  `Int.cast`; realprop.v's `min`, `max` and `IF _ then _ else _` are Lean's `min`, `max` and
  `if _ then _ else _` (Coq's `x2 >= w` is `w ≤ x2`); `iter s f x` is `f^[s] x`;
  `(m %/ 2)%Z` is `m / 2` on `ℤ` (`Int.ediv`, equal to math-comp's `divz`, see `Grid.lean`).
* The Coq coercions `srect_region : scaled_rect >-> region`, `smatte_region : scaled_matte >->
  region`, `in_interval`, `in_rectangle`, `in_grect` and `in_matte` are the explicit functions
  `srectRegion`, `smatteRegion`, `inInterval`, `inRectangle`, `inGrect` and `inMatte`.
* `exists2 x, P x & Q x` is `∃ x, P x ∧ Q x`; `subpred gr1 gr2` is `gr1 ⊆ gr2`; `gr1 =1 gr2` is
  `∀ p, p ∈ gr1 ↔ p ∈ gr2`; `preim halfg gr` is `halfg ⁻¹' gr`; the `reflect` lemma
  `mem_approx_scale` is an `↔`.
* The section `Let`s `ltR01`, `ltR02`, `ltR12` are Mathlib's `zero_lt_one`, `two_pos`,
  `one_lt_two`; the default argument `b_p := (s, ltouch p)` of Coq's `rect_approx` is inlined.
-/

namespace FourColor.RealPlane

open Function

/-! ### Complement to `realprop.v`: the unit interval `range1` -/

/-- realprop.v `range1 x`: the unit interval `[x, x + 1)`. -/
def range1 (x : ℝ) : ℝ → Prop := fun y => x ≤ y ∧ y < x + 1

/-- realprop.v `range1_floor` (Coq's real-valued `floor x` is `Int.floor x` here). -/
theorem range1_floor (x : ℝ) : range1 ⌊x⌋ x := ⟨Int.floor_le x, Int.lt_floor_add_one x⟩

/-- realprop.v `range1z_inj`. -/
theorem range1z_inj {x : ℝ} {m1 m2 : ℤ} (h1 : range1 m1 x) (h2 : range1 m2 x) : m1 = m2 :=
  (Int.floor_eq_iff.2 h1).symm.trans (Int.floor_eq_iff.2 h2)

/-- realprop.v `range1zz`. -/
theorem range1zz (m : ℤ) : range1 m m := ⟨le_rfl, lt_add_one _⟩

/-- realprop.v `range1z_floor` (Coq: `range1 m x <-> floor x == m`, with a real-valued
`floor`). -/
theorem range1z_floor (m : ℤ) (x : ℝ) : range1 m x ↔ ⌊x⌋ = m := Int.floor_eq_iff.symm

/-- realprop.v `find_range1z`. -/
theorem find_range1z (x : ℝ) : ∃ m : ℤ, range1 m x := ⟨⌊x⌋, range1_floor x⟩

/-! ### Scaled rectangles and mattes -/

/-- Coq `scaled_rect R`: pairs of a natural scale and a grid rectangle (Coq's phantom parameter
`R` is dropped). Such a pair `b` denotes the region `srectRegion b`. -/
abbrev ScaledRect : Type := ℕ × GRect

/-- Coq `scaled_matte R`: pairs of a natural scale and a grid matte (Coq's phantom parameter
`R` is dropped). Such a pair `m` denotes the region `smatteRegion m`. -/
abbrev ScaledMatte : Type := ℕ × Matte

/-! ### Real powers of 2, for scaling approximations -/

/-- Coq `exp2R s`: `2 ^ s` as a real number (Coq `intR R (2 ^ s)%N`, see `exp2R_eq_cast`). -/
noncomputable def exp2R (s : ℕ) : ℝ := (2 : ℝ) ^ s

/-- `exp2R s` is the embedding of the natural number `2 ^ s`, as in Coq's definition
(not in Coq). -/
theorem exp2R_eq_cast (s : ℕ) : exp2R s = ((2 ^ s : ℕ) : ℝ) := by
  rw [exp2R, Nat.cast_pow, Nat.cast_ofNat]

/-- Coq `exp2RS` (Coq: `exp2R s.+1 == 2 * exp2R s`). -/
theorem exp2RS (s : ℕ) : exp2R (s + 1) = 2 * exp2R s := pow_succ' (2 : ℝ) s

/-- Coq `leR1exp2`. -/
theorem leR1exp2 (s : ℕ) : 1 ≤ exp2R s := one_le_pow₀ one_le_two

/-- Coq `ltR0exp2`. -/
theorem ltR0exp2 (s : ℕ) : 0 < exp2R s := lt_of_lt_of_le zero_lt_one (leR1exp2 s)

/-- Coq `exp2R_add` (Coq: `exp2R (s1 + s2) == exp2R s1 * exp2R s2`). -/
theorem exp2R_add (s1 s2 : ℕ) : exp2R (s1 + s2) = exp2R s1 * exp2R s2 := pow_add (2 : ℝ) s1 s2

/-- Coq `leRexp2`. -/
theorem leRexp2 {s1 s2 : ℕ} (h : s1 ≤ s2) : exp2R s1 ≤ exp2R s2 :=
  pow_le_pow_right₀ one_le_two h

/-- Coq `ltR1exp2S`. -/
theorem ltR1exp2S (s : ℕ) : 1 < exp2R (s + 1) := one_lt_pow₀ one_lt_two s.succ_ne_zero

/-! ### Scalar binary approximation -/

/-- Coq `approx s x m`: the integer `m` is the approximation of the real `x` at scale `s`,
i.e., `m ≤ 2 ^ s * x < m + 1`. -/
def Approx (s : ℕ) (x : ℝ) (m : ℤ) : Prop := range1 m (exp2R s * x)

/-- The approximation of `x` at scale `s` is the floor of `2 ^ s * x` (not in Coq). -/
theorem approx_iff_floor {s : ℕ} {x : ℝ} {m : ℤ} : Approx s x m ↔ ⌊exp2R s * x⌋ = m :=
  range1z_floor m _

/-- Coq `approx_inj`. -/
theorem approx_inj {s : ℕ} {x : ℝ} {m1 m2 : ℤ} (h1 : Approx s x m1) (h2 : Approx s x m2) :
    m1 = m2 :=
  range1z_inj h1 h2

/-- Coq `approx_exists`. -/
theorem approx_exists (s : ℕ) (x : ℝ) : ∃ m, Approx s x m := find_range1z _

/-- Coq `scale s m`: the integer `m` scaled back by `s`, i.e., `m / 2 ^ s`. -/
noncomputable def scale (s : ℕ) (m : ℤ) : ℝ := m / exp2R s

/-- Coq `approx_scale`. -/
theorem approx_scale (s : ℕ) (m : ℤ) : Approx s (scale s m) m := by
  rw [Approx, scale, mul_div_cancel₀ _ (ltR0exp2 s).ne']
  exact range1zz m

/-- Coq `approx_halfz` (Coq's `(m %/ 2)%Z` is `m / 2`). -/
theorem approx_halfz {s : ℕ} {x : ℝ} {m : ℤ} (h : Approx (s + 1) x m) : Approx s x (m / 2) := by
  obtain ⟨hxm, hmx⟩ := h
  rw [exp2RS] at hxm hmx
  -- `m = m %% 2 + 2 * (m %/ 2)` with `0 ≤ m %% 2 ≤ 1` (Coq: `intR_addbit`, `modz2`)
  have e1 : ((2 * (m / 2) : ℤ) : ℝ) ≤ m := Int.cast_le.2 (by omega)
  have e2 : ((m + 1 : ℤ) : ℝ) ≤ ((2 * (m / 2) + 2 : ℤ) : ℝ) := Int.cast_le.2 (by omega)
  push_cast at e1 e2
  exact ⟨by linarith, by linarith⟩

/-- Coq `scale_exists`. -/
theorem scale_exists {x : ℝ} (hx : 0 < x) : ∃ s, 1 < exp2R s * x := by
  obtain ⟨s, hs⟩ := pow_unbounded_of_one_lt (1 / x) (one_lt_two : (1 : ℝ) < 2)
  exact ⟨s, (div_lt_iff₀ hx).1 hs⟩

/-- Coq `approx_between`. -/
theorem approx_between {s : ℕ} {x1 x2 : ℝ} {m1 m2 : ℤ} (h1 : Approx (s + 1) x1 m1)
    (h2 : Approx (s + 1) x2 m2) (hx : 1 < exp2R s * (x2 - x1)) :
    ∃ m : ℤ, m1 + 1 ≤ m ∧ m + 1 ≤ m2 := by
  obtain ⟨m, hmy, hym⟩ := approx_exists s (x1 + x2)
  obtain ⟨hm1, -⟩ := h1
  obtain ⟨-, hm2⟩ := h2
  rw [exp2RS] at hm1 hm2
  refine ⟨m, ?_, ?_⟩
  · have h : (m1 : ℝ) < m := by linarith
    exact Int.add_one_le_iff.2 (by exact_mod_cast h)
  · have h : (m : ℝ) < m2 := by linarith
    exact Int.add_one_le_iff.2 (by exact_mod_cast h)

/-! ### Geometrical binary approximation -/

/-- Coq `approx_point s z p`: the grid point `p` is the approximation of the point `z` at
scale `s`. -/
def ApproxPoint (s : ℕ) (z : Point) (p : GPoint) : Prop := Approx s z.x p.x ∧ Approx s z.y p.y

/-- Coq `approx_point_inj`. -/
theorem approx_point_inj {s : ℕ} {z : Point} {p1 p2 : GPoint} (h1 : ApproxPoint s z p1)
    (h2 : ApproxPoint s z p2) : p1 = p2 :=
  GPoint.ext (approx_inj h1.1 h2.1) (approx_inj h1.2 h2.2)

/-- Coq `approx_point_exists`. -/
theorem approx_point_exists (s : ℕ) (z : Point) : ∃ p, ApproxPoint s z p := by
  obtain ⟨mx, hmx⟩ := approx_exists s z.x
  obtain ⟨my, hmy⟩ := approx_exists s z.y
  exact ⟨⟨mx, my⟩, hmx, hmy⟩

/-- Coq `scale_point s p`: the grid point `p` scaled back by `s`. -/
noncomputable def scalePoint (s : ℕ) (p : GPoint) : Point := ⟨scale s p.x, scale s p.y⟩

/-- Coq `approx_scale_point`. -/
theorem approx_scale_point (s : ℕ) (p : GPoint) : ApproxPoint s (scalePoint s p) p :=
  ⟨approx_scale s p.x, approx_scale s p.y⟩

/-- Coq `approx_halfg`. -/
theorem approx_halfg {s : ℕ} {z : Point} {p : GPoint} (h : ApproxPoint (s + 1) z p) :
    ApproxPoint s z (halfg p) :=
  ⟨approx_halfz h.1, approx_halfz h.2⟩

/-- Coq `mem_approx s gr`: the region of the points whose approximation at scale `s` lies in
the grid region `gr`. -/
def memApprox (s : ℕ) (gr : GRegion) : Region := fun z => ∃ p, ApproxPoint s z p ∧ p ∈ gr

/-- Coq `sub_mem_approx`. -/
theorem sub_mem_approx (s : ℕ) {gr1 gr2 : GRegion} (h : gr1 ⊆ gr2) :
    Subregion (memApprox s gr1) (memApprox s gr2) :=
  fun _ ⟨p, hp, hgr⟩ => ⟨p, hp, h hgr⟩

/-- Coq `mem_approx_scale` (a `reflect` lemma in Coq). -/
theorem mem_approx_scale (s : ℕ) (gr : GRegion) (p : GPoint) :
    memApprox s gr (scalePoint s p) ↔ p ∈ gr := by
  constructor
  · rintro ⟨p', hp', hgr⟩
    rwa [approx_point_inj (approx_scale_point s p) hp']
  · exact fun h => ⟨p, approx_scale_point s p, h⟩

/-- Coq `eq_mem_approx`. -/
theorem eq_mem_approx (s : ℕ) {gr1 gr2 : GRegion} (z : Point) (h : ∀ p, p ∈ gr1 ↔ p ∈ gr2) :
    memApprox s gr1 z ↔ memApprox s gr2 z :=
  ⟨sub_mem_approx s (fun p => (h p).1) z, sub_mem_approx s (fun p => (h p).2) z⟩

/-- Coq `mem_approx_refine`. -/
theorem mem_approx_refine (s : ℕ) (gr : GRegion) (z : Point) :
    memApprox (s + 1) (halfg ⁻¹' gr) z ↔ memApprox s gr z := by
  constructor
  · rintro ⟨p, hp, hgr⟩
    exact ⟨halfg p, approx_halfg hp, hgr⟩
  · rintro ⟨p, hp, hgr⟩
    obtain ⟨q, hq⟩ := approx_point_exists (s + 1) z
    refine ⟨q, hq, ?_⟩
    show halfg q ∈ gr
    rwa [approx_point_inj (approx_halfg hq) hp]

/-- Coq `mem_approx_refine_inset`. -/
theorem mem_approx_refine_inset (s : ℕ) (b : GRect) :
    Subregion (memApprox s (inGrect (inset b)))
      (memApprox (s + 1) (inGrect (inset (refineRect b)))) := by
  intro z hz
  obtain ⟨p, hp, hpb⟩ := (mem_approx_refine s _ z).2 hz
  refine ⟨p, hp, ?_⟩
  have h : p ∈ refineRect (inset b) := (in_refine_rect _ p).2 hpb
  rw [refine_inset] at h
  exact insetW _ p h

/-! ### Scaled rectangles -/

/-- Coq `srect_region b` (a coercion in Coq): the region of the points whose approximation at
scale `b.1` lies in the grid rectangle `b.2`. -/
def srectRegion (b : ScaledRect) : Region := memApprox b.1 (inGrect b.2)

/-- Coq `refine_srect s b`. -/
def refineSrect (s : ℕ) (b : ScaledRect) : ScaledRect := (s + b.1, refineRect^[s] b.2)

/-- Coq `inset_srect b`. -/
def insetSrect (b : ScaledRect) : ScaledRect := (b.1, inset b.2)

/-- Coq `in_refine_srect`. -/
theorem in_refine_srect (s : ℕ) (b : ScaledRect) (z : Point) :
    srectRegion (refineSrect s b) z ↔ srectRegion b z := by
  induction s with
  | zero =>
    show memApprox (0 + b.1) (inGrect b.2) z ↔ memApprox b.1 (inGrect b.2) z
    rw [Nat.zero_add]
  | succ s ih =>
    refine Iff.trans ?_ ((mem_approx_refine (s + b.1) (inGrect (refineRect^[s] b.2)) z).trans ih)
    show memApprox (s + 1 + b.1) (inGrect (refineRect^[s + 1] b.2)) z ↔ _
    rw [Nat.add_right_comm s 1 b.1]
    refine eq_mem_approx _ z fun t => ?_
    rw [iterate_succ_apply']
    exact in_refine_rect _ t

/-- Coq `in_refine_inset`. -/
theorem in_refine_inset (s : ℕ) {b : ScaledRect} {z : Point} (h : srectRegion (insetSrect b) z) :
    srectRegion (insetSrect (refineSrect s b)) z := by
  induction s with
  | zero =>
    show memApprox (0 + b.1) (inGrect (inset b.2)) z
    rwa [Nat.zero_add]
  | succ s ih =>
    have h' := mem_approx_refine_inset (s + b.1) (refineRect^[s] b.2) z ih
    show memApprox (s + 1 + b.1) (inGrect (inset (refineRect^[s + 1] b.2))) z
    rwa [Nat.add_right_comm s 1 b.1, iterate_succ_apply']

/-- A common scale for four positive reals (the `fin_all_exists` and `\max` step of Coq's
`approx_rect`). -/
private theorem scale_exists4 {d0 d1 d2 d3 : ℝ} (h0 : 0 < d0) (h1 : 0 < d1) (h2 : 0 < d2)
    (h3 : 0 < d3) :
    ∃ s, 1 < exp2R s * d0 ∧ 1 < exp2R s * d1 ∧ 1 < exp2R s * d2 ∧ 1 < exp2R s * d3 := by
  obtain ⟨s0, hs0⟩ := scale_exists h0
  obtain ⟨s1, hs1⟩ := scale_exists h1
  obtain ⟨s2, hs2⟩ := scale_exists h2
  obtain ⟨s3, hs3⟩ := scale_exists h3
  have key : ∀ {si : ℕ} {d : ℝ}, 0 < d → si ≤ max (max s0 s1) (max s2 s3) →
      1 < exp2R si * d → 1 < exp2R (max (max s0 s1) (max s2 s3)) * d :=
    fun hd hle h => lt_of_lt_of_le h (mul_le_mul_of_nonneg_right (leRexp2 hle) hd.le)
  exact ⟨_, key h0 (by omega) hs0, key h1 (by omega) hs1, key h2 (by omega) hs2,
    key h3 (by omega) hs3⟩

/-- Coq `approx_rect`. -/
theorem approx_rect {z : Point} {r : Rectangle} (h : inRectangle r z) :
    ∃ b : ScaledRect, srectRegion (insetSrect b) z ∧ Subregion (srectRegion b) (inRectangle r) := by
  obtain ⟨x, y⟩ := z
  obtain ⟨⟨x0, x1⟩, ⟨y0, y1⟩⟩ := r
  obtain ⟨⟨lbx, ubx⟩, ⟨lby, uby⟩⟩ := h
  change x0 < x at lbx
  change x < x1 at ubx
  change y0 < y at lby
  change y < y1 at uby
  obtain ⟨s, hs0, hs1, hs2, hs3⟩ :=
    scale_exists4 (sub_pos.2 lbx) (sub_pos.2 ubx) (sub_pos.2 lby) (sub_pos.2 uby)
  obtain ⟨mx, Dmx⟩ := approx_exists (s + 1) x
  obtain ⟨my, Dmy⟩ := approx_exists (s + 1) y
  obtain ⟨mx0, Dmx0⟩ := approx_exists (s + 1) x0
  obtain ⟨mx1, Dmx1⟩ := approx_exists (s + 1) x1
  obtain ⟨my0, Dmy0⟩ := approx_exists (s + 1) y0
  obtain ⟨my1, Dmy1⟩ := approx_exists (s + 1) y1
  obtain ⟨nx0, lbx0, ubx0⟩ := approx_between Dmx0 Dmx hs0
  obtain ⟨nx1, lbx1, ubx1⟩ := approx_between Dmx Dmx1 hs1
  obtain ⟨ny0, lby0, uby0⟩ := approx_between Dmy0 Dmy hs2
  obtain ⟨ny1, lby1, uby1⟩ := approx_between Dmy Dmy1 hs3
  refine ⟨(s + 1, ⟨nx0, nx1 + 1, ny0, ny1 + 1⟩), ⟨⟨mx, my⟩, ⟨Dmx, Dmy⟩, ?_⟩, ?_⟩
  · show (⟨mx, my⟩ : GPoint) ∈ inset ⟨nx0, nx1 + 1, ny0, ny1 + 1⟩
    simp only [mem_grect, inset]
    omega
  · have lt_approx : ∀ {u v : ℝ} {mu mv : ℤ}, Approx (s + 1) u mu → Approx (s + 1) v mv →
        mu + 1 ≤ mv → u < v := by
      rintro u v mu mv ⟨-, ubu⟩ ⟨lbv, -⟩ ltuv
      have e : ((mu + 1 : ℤ) : ℝ) ≤ mv := Int.cast_le.2 ltuv
      push_cast at e
      exact lt_of_mul_lt_mul_left (by linarith) (ltR0exp2 (s + 1)).le
    rintro ⟨x2, y2⟩ ⟨⟨mx2, my2⟩, ⟨Dmx2, Dmy2⟩, hp⟩
    change Approx (s + 1) x2 mx2 at Dmx2
    change Approx (s + 1) y2 my2 at Dmy2
    change (nx0 ≤ mx2 ∧ mx2 < nx1 + 1) ∧ (ny0 ≤ my2 ∧ my2 < ny1 + 1) at hp
    obtain ⟨⟨hx0, hx1⟩, hy0, hy1⟩ := hp
    exact ⟨⟨lt_approx Dmx0 Dmx2 (by omega), lt_approx Dmx2 Dmx1 (by omega)⟩,
      ⟨lt_approx Dmy0 Dmy2 (by omega), lt_approx Dmy2 Dmy1 (by omega)⟩⟩

/-- Coq `rect_approx` (Coq's default argument `b_p := (s, ltouch p)` is inlined). -/
theorem rect_approx {s : ℕ} {z : Point} {p : GPoint} (h : ApproxPoint s z p) :
    ∃ r : Rectangle, inRectangle r z ∧ Subregion (inRectangle r) (srectRegion (s, ltouch p)) := by
  obtain ⟨x, y⟩ := z
  obtain ⟨mx, my⟩ := p
  obtain ⟨⟨lbx, ubx⟩, ⟨lby, uby⟩⟩ := h
  change (mx : ℝ) ≤ exp2R s * x at lbx
  change exp2R s * x < mx + 1 at ubx
  change (my : ℝ) ≤ exp2R s * y at lby
  change exp2R s * y < my + 1 at uby
  have sXgt0 := ltR0exp2 s
  let step : ℤ → Interval := fun m => ⟨((m - 1 : ℤ) : ℝ) / exp2R s, ((m + 1 : ℤ) : ℝ) / exp2R s⟩
  refine ⟨⟨step mx, step my⟩, ?_, ?_⟩
  · show (_ < x ∧ x < _) ∧ (_ < y ∧ y < _)
    simp only [step, div_lt_iff₀ sXgt0, lt_div_iff₀ sXgt0]
    push_cast
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rintro ⟨x1, y1⟩ ⟨⟨lbx1, ubx1⟩, ⟨lby1, uby1⟩⟩
    change ((mx - 1 : ℤ) : ℝ) / exp2R s < x1 at lbx1
    change x1 < ((mx + 1 : ℤ) : ℝ) / exp2R s at ubx1
    change ((my - 1 : ℤ) : ℝ) / exp2R s < y1 at lby1
    change y1 < ((my + 1 : ℤ) : ℝ) / exp2R s at uby1
    rw [div_lt_iff₀ sXgt0] at lbx1 lby1
    rw [lt_div_iff₀ sXgt0] at ubx1 uby1
    push_cast at lbx1 ubx1 lby1 uby1
    obtain ⟨p1, hp1⟩ := approx_point_exists s ⟨x1, y1⟩
    refine ⟨p1, hp1, ?_⟩
    have hx : (p1.x : ℝ) ≤ exp2R s * x1 ∧ exp2R s * x1 < p1.x + 1 := hp1.1
    have hy : (p1.y : ℝ) ≤ exp2R s * y1 ∧ exp2R s * y1 < p1.y + 1 := hp1.2
    have e1 : (mx : ℝ) < p1.x + 2 := by linarith
    have e2 : (p1.x : ℝ) < mx + 1 := by linarith
    have e3 : (my : ℝ) < p1.y + 2 := by linarith
    have e4 : (p1.y : ℝ) < my + 1 := by linarith
    have e1' : mx < p1.x + 2 := by exact_mod_cast e1
    have e2' : p1.x < mx + 1 := by exact_mod_cast e2
    have e3' : my < p1.y + 2 := by exact_mod_cast e3
    have e4' : p1.y < my + 1 := by exact_mod_cast e4
    show p1 ∈ ltouch ⟨mx, my⟩
    simp only [mem_grect, ltouch]
    omega

/-! ### Some rectangle operations -/

/-- Coq `cap_interval xz1 xz2`: the intersection of the intervals `xz1` and `xz2` (a possibly
empty interval). -/
noncomputable def capInterval (xz1 xz2 : Interval) : Interval :=
  ⟨max xz1.lo xz2.lo, min xz1.hi xz2.hi⟩

/-- Coq `mem_cap_interval`. -/
theorem mem_cap_interval (xz1 xz2 : Interval) (y : ℝ) :
    inInterval (capInterval xz1 xz2) y ↔ inInterval xz1 y ∧ inInterval xz2 y := by
  simp only [capInterval, inInterval, max_lt_iff, lt_min_iff]
  tauto

/-- Coq `cap_rect r1 r2`: the intersection of the rectangles `r1` and `r2`. -/
noncomputable def capRect (r1 r2 : Rectangle) : Rectangle :=
  ⟨capInterval r1.hspan r2.hspan, capInterval r1.vspan r2.vspan⟩

/-- Coq `mem_cap_rect`. -/
theorem mem_cap_rect (r1 r2 : Rectangle) (p : Point) :
    inRectangle (capRect r1 r2) p ↔ inRectangle r1 p ∧ inRectangle r2 p := by
  simp only [capRect, inRectangle, mem_cap_interval]
  tauto

/-- Coq `sep_interval x1 x2`: an interval containing `x2` but not `x1`, provided `x1 ≠ x2`
(Coq's condition `x2 >= w` is `w ≤ x2`). -/
noncomputable def sepInterval (x1 x2 : ℝ) : Interval :=
  let w := (x1 + x2) / 2
  ⟨if x2 ≤ w then x2 - 1 else w, if w ≤ x2 then x2 + 1 else w⟩

/-- Coq `mem_sep_interval`. -/
theorem mem_sep_interval (x1 x2 : ℝ) : inInterval (sepInterval x1 x2) x2 := by
  simp only [sepInterval, inInterval]
  constructor
  · split_ifs <;> linarith
  · split_ifs <;> linarith

/-- Coq `meet_sep_interval` (Coq: `... -> x == y`). -/
theorem meet_sep_interval {x y t : ℝ} (h1 : inInterval (sepInterval x y) t)
    (h2 : inInterval (sepInterval y x) t) : x = y := by
  by_contra hne
  simp only [sepInterval, inInterval] at h1 h2
  obtain ⟨h1l, h1r⟩ := h1
  obtain ⟨h2l, h2r⟩ := h2
  rcases lt_or_gt_of_ne hne with hlt | hlt <;> split_ifs at h1l h1r h2l h2r <;> linarith

/-- Coq `sep_rect z1 z2`: a rectangle containing `z2` but not `z1`, unless `z1 = z2`. -/
noncomputable def sepRect (z1 z2 : Point) : Rectangle :=
  ⟨sepInterval z1.x z2.x, sepInterval z1.y z2.y⟩

/-- Coq `mem_sep_rect`. -/
theorem mem_sep_rect (z1 z2 : Point) : inRectangle (sepRect z1 z2) z2 :=
  ⟨mem_sep_interval z1.x z2.x, mem_sep_interval z1.y z2.y⟩

/-- Coq `meet_sep_rect`. -/
theorem meet_sep_rect {z1 z2 : Point}
    (h : Meet (inRectangle (sepRect z1 z2)) (inRectangle (sepRect z2 z1))) :
    ∀ rr : Rectangle, inRectangle rr z1 → inRectangle rr z2 := by
  obtain ⟨t, ⟨h12x, h12y⟩, ⟨h21x, h21y⟩⟩ := h
  have ex : z1.x = z2.x := meet_sep_interval h12x h21x
  have ey : z1.y = z2.y := meet_sep_interval h12y h21y
  rintro rr ⟨hx, hy⟩
  refine ⟨?_, ?_⟩
  · rw [← ex]; exact hx
  · rw [← ey]; exact hy

/-- The conclusion of `meet_sep_rect`, strengthened to the equality of the two points (not in
Coq, where points have no equality: over `ℝ`, two points are equal iff their coordinates
are). -/
theorem eq_of_meet_sep_rect {z1 z2 : Point}
    (h : Meet (inRectangle (sepRect z1 z2)) (inRectangle (sepRect z2 z1))) : z1 = z2 := by
  obtain ⟨t, ⟨h12x, h12y⟩, ⟨h21x, h21y⟩⟩ := h
  have ex : z1.x = z2.x := meet_sep_interval h12x h21x
  have ey : z1.y = z2.y := meet_sep_interval h12y h21y
  show (⟨z1.x, z1.y⟩ : Point) = ⟨z2.x, z2.y⟩
  rw [ex, ey]

/-! ### Scaled mattes -/

/-- Coq `smatte_region m` (a coercion in Coq): the region of the points whose approximation at
scale `m.1` lies in the matte `m.2`. -/
def smatteRegion (m : ScaledMatte) : Region := memApprox m.1 (inMatte m.2)

/-- Coq `refine_smatte s m`. -/
def refineSmatte (s : ℕ) (m : ScaledMatte) : ScaledMatte := (s + m.1, refineMatte^[s] m.2)

/-- Coq `in_refine_smatte`. -/
theorem in_refine_smatte (s : ℕ) (m : ScaledMatte) (z : Point) :
    smatteRegion (refineSmatte s m) z ↔ smatteRegion m z := by
  induction s with
  | zero =>
    show memApprox (0 + m.1) (inMatte m.2) z ↔ memApprox m.1 (inMatte m.2) z
    rw [Nat.zero_add]
  | succ s ih =>
    refine Iff.trans ?_ ((mem_approx_refine (s + m.1) (inMatte (refineMatte^[s] m.2)) z).trans ih)
    show memApprox (s + 1 + m.1) (inMatte (refineMatte^[s + 1] m.2)) z ↔ _
    rw [Nat.add_right_comm s 1 m.1]
    refine eq_mem_approx _ z fun t => ?_
    rw [iterate_succ_apply']
    exact in_refine_matte _ t

end FourColor.RealPlane
