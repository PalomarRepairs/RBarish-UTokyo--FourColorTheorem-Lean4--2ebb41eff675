/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Reducibility engine, layer 0: big-`Nat` bitset primitives

This file is part of the bit-parallel reducibility engine that replaces Gonthier's
`ctree`/`gtree` engine (`ctree.v` … `kempetree.v`); see `FourColor/Engine.lean` for an
overview of the design.  Nothing here is a port of a Coq definition.

All definitions are kernel-friendly: structural recursion only, and the only operations on
large numbers are the GMP-accelerated kernel primitives `&&&`, `|||`, `^^^`, `<<<`, `>>>`, `+`,
`-`, `*`, `Nat.beq`, `Nat.ble`.  `Nat.pow`, `/` and `%` only take small operands: with big
operands they are very slow in Palomar's checker con-ron (and division in nanoda),
so masks are built with shifts.

* `chooseAux n k`   : the binomial coefficient, computed with `k` multiplications/divisions
  (the Pascal recursion of `Nat.choose` is exponential in the kernel); `chooseAux_eq`.
* `ones n`          : `2 ^ n - 1` (the `n` low bits), built as `(1 <<< n) - 1` (`ones_eq`,
  `testBit_ones`).
* `pmask L P w`     : the periodic mask of the bits `i < L` with `i % P < w` (for `P ∣ L`),
  built by doubling its first run (`pfill`, `⌈log₂ (L / P)⌉` doublings); it equals the closed
  form `(2^w - 1) * ((2^L - 1) / (2^P - 1))` (`pmask_eq`).
* `xlate lo w y`    : exchange of the runs of `y` selected by `lo` with the runs `w` bits
  above them; with `lo = pmask L (2*w) w` it is the bit permutation `i ↦ i xor w` (when
  `w` is a power of two times the run structure, see `testBit_xlate`).
* `deltaSwap x (m, d)` : the delta swap exchanging bits `i` and `i + d` for every `i ∈ m`;
  `applyNet net x`  : a network of delta swaps (e.g. a Beneš network).
* `layerOK (m, d)`  : the pairs of a layer are disjoint (`m &&& (m <<< d) = 0`); under this
  condition a layer, hence a network, is a bit permutation (`testBit_applyNet`).
-/

namespace FourColor.Engine

/-! ### Binomial coefficients -/

/-- The binomial coefficient `n.choose k`, computed as `∏_{i<k} (n - i) / (i + 1)` (each
partial product is exactly divisible); kernel cost `O(k)` operations on small numbers. -/
def chooseAux (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => chooseAux n k * (n - k) / (k + 1)

/-- `chooseAux` is the binomial coefficient. -/
theorem chooseAux_eq (n k : Nat) : chooseAux n k = n.choose k := by
  induction k with
  | zero => simp [chooseAux]
  | succ k ih =>
    simp only [chooseAux, ih]
    rw [← Nat.choose_succ_right_eq]
    exact Nat.mul_div_cancel _ (Nat.succ_pos k)

/-! ### Masks built by shifts -/

/-- `ones n = 2 ^ n - 1`: the `n` low bits, built with a shift (`Nat.pow` with a big result is
slow in con-ron). -/
def ones (n : Nat) : Nat := (1 <<< n) - 1

/-- `ones n` is `2 ^ n - 1`. -/
theorem ones_eq (n : Nat) : ones n = 2 ^ n - 1 := by
  rw [ones, Nat.shiftLeft_eq, Nat.one_mul]

/-- The bits of `ones n`. -/
@[simp] theorem testBit_ones (n i : Nat) : (ones n).testBit i = decide (i < n) := by
  rw [ones_eq, Nat.testBit_two_pow_sub_one]

/-! ### Periodic masks and translations -/

/-- `pfill L fuel s x`: while `s < L` (at most `fuel` times), `x ← x ||| (x <<< s)` and
`s ← 2 * s`.  If `x` is a pattern of period `P ∣ s` on its `s` low bits (and has no higher
bit), the result is the same pattern on at least `L` bits provided `L ≤ s * 2 ^ fuel` (e.g.
`fuel = L`, `0 < s`); only the doublings that are needed are evaluated (`testBit_pfill`).
(The test is a `match` on `Nat.ble`, cheaper in the kernel than an `if` on `s < L`.) -/
def pfill (L : Nat) : Nat → Nat → Nat → Nat
  | 0, _, x => x
  | fuel + 1, s, x =>
    match Nat.ble L s with
    | true => x
    | false => pfill L fuel (2 * s) (x ||| (x <<< s))

/-- `pmask L P w`: the bits `i < L` such that `i % P < w`.  The first run `ones w` is repeated
with period `P` by doubling (`pfill`: `⌈log₂ (L / P)⌉` doublings of two big-number operations)
and truncated to the whole periods below `L` (`L - L % P` bits; `/` and `%` only take small
operands here).  Meaningful for `0 < P`, `P ∣ L` and `w ≤ P` (see `testBit_pmask`); it then
equals the closed form `(2^w - 1) * ((2^L - 1) / (2^P - 1))` (`pmask_eq`), as it does (both
are `0`) when `L < P` or `P = 0` (`pmask_of_lt`). -/
def pmask (L P w : Nat) : Nat := pfill L L P (ones w) &&& ones (L - L % P)

/-- The geometric series `∑_{j<n} 2^(j*P)` (specification of the closed form of `pmask`). -/
def geoP (P : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 ^ (n * P) + geoP P n

/-- The geometric series times `2^P - 1`. -/
theorem geoP_mul (P n : Nat) : (2 ^ P - 1) * geoP P n = 2 ^ (n * P) - 1 := by
  induction n with
  | zero => simp [geoP]
  | succ n ih =>
    simp only [geoP, Nat.mul_add, ih]
    have h1 : 1 ≤ 2 ^ (n * P) := Nat.one_le_two_pow
    have h2 : 1 ≤ 2 ^ P := Nat.one_le_two_pow
    have h3 : 1 ≤ 2 ^ (n * P) * 2 ^ P := Nat.mul_le_mul h1 h2
    rw [Nat.succ_mul, Nat.pow_add]
    zify [h1, h2, h3]
    ring

/-- The division in the closed form of `pmask` is exact. -/
theorem div_eq_geoP {P n : Nat} (hP : 0 < P) : (2 ^ (n * P) - 1) / (2 ^ P - 1) = geoP P n := by
  apply Nat.div_eq_of_eq_mul_left
  · have : 2 ≤ 2 ^ P := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ P := Nat.pow_le_pow_right (by norm_num) hP
    omega
  · rw [Nat.mul_comm (geoP P n), geoP_mul]

/-- The bits of `(2^w - 1) * geoP P n`. -/
theorem testBit_pmask_aux {P w : Nat} (hw : w ≤ P) (n i : Nat) :
    ((2 ^ w - 1) * geoP P n).testBit i = (decide (i < n * P) && decide (i % P < w)) := by
  induction n with
  | zero => simp [geoP]
  | succ n ih =>
    have hlt : (2 ^ w - 1) * geoP P n < 2 ^ (n * P) := by
      calc (2 ^ w - 1) * geoP P n ≤ (2 ^ P - 1) * geoP P n :=
            Nat.mul_le_mul_right _ (Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) hw) 1)
        _ = 2 ^ (n * P) - 1 := geoP_mul P n
        _ < 2 ^ (n * P) := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)
    have e : (2 ^ w - 1) * geoP P (n + 1) = 2 ^ (n * P) * (2 ^ w - 1) + (2 ^ w - 1) * geoP P n := by
      simp only [geoP]; ring
    rw [e, Nat.testBit_two_pow_mul_add _ hlt, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < n * P
    · rw [ite_eq_left hi, ih]
      have : i < (n + 1) * P := by rw [Nat.succ_mul]; omega
      simp [hi, this]
    · rw [ite_eq_right hi]
      have hge : n * P ≤ i := Nat.le_of_not_lt hi
      by_cases h2 : i < (n + 1) * P
      · have hm : i % P = i - n * P := by
          have h3 : i - n * P < P := by rw [Nat.succ_mul] at h2; omega
          have e2 : i = (i - n * P) + P * n := by rw [Nat.mul_comm P n]; omega
          conv_lhs => rw [e2]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h3]
        simp [h2, hm]
      · have : ¬ (i - n * P < w) := by rw [Nat.succ_mul] at h2; omega
        simp [h2, this]

/-- The bits of `pfill`: a pattern of period `P ∣ s` on the `s` low bits of `x` is extended to
(at least) the `L` low bits. -/
theorem testBit_pfill {L P w : Nat} :
    ∀ (fuel s x : Nat), P ∣ s → L ≤ s * 2 ^ fuel →
      (∀ j, x.testBit j = (decide (j < s) && decide (j % P < w))) →
      ∀ i, i < L → (pfill L fuel s x).testBit i = decide (i % P < w) := by
  intro fuel
  induction fuel with
  | zero =>
    intro s x _ hL hx i hi
    rw [Nat.pow_zero, Nat.mul_one] at hL
    rw [pfill, hx, decide_eq_true (show i < s by omega), Bool.true_and]
  | succ fuel ih =>
    intro s x hs hL hx i hi
    cases h : Nat.ble L s with
    | true =>
      have hsL : L ≤ s := Nat.le_of_ble_eq_true h
      simp only [pfill, h]
      rw [hx, decide_eq_true (show i < s by omega), Bool.true_and]
    | false =>
      have hsL : s < L := Nat.gt_of_not_le (Nat.not_le_of_not_ble_eq_true (by simp [h]))
      simp only [pfill, h]
      have hL' : L ≤ 2 * s * 2 ^ fuel := by
        have e : s * 2 ^ (fuel + 1) = 2 * s * 2 ^ fuel := by rw [Nat.pow_succ]; ring
        omega
      refine ih (2 * s) _ (Nat.dvd_trans hs (Nat.dvd_mul_left s 2)) hL' ?_ i hi
      intro j
      rw [Nat.testBit_or, Nat.testBit_shiftLeft, hx, hx]
      by_cases hj : j < s
      · have h2 : j < 2 * s := by omega
        have h3 : ¬ j ≥ s := by omega
        simp only [hj, h2, h3, decide_true, decide_false, Bool.true_and, Bool.false_and,
          Bool.or_false]
      · obtain ⟨c, rfl⟩ := hs
        have hge : P * c ≤ j := by omega
        have hmod : (j - P * c) % P = j % P := by
          conv_rhs => rw [show j = (j - P * c) + P * c by omega]
          rw [Nat.add_mul_mod_self_left]
        have h4 : (j - P * c < P * c) = (j < 2 * (P * c)) := by
          apply propext; omega
        simp only [hj, hge, hmod, h4, decide_false, decide_true, Bool.false_and, Bool.false_or,
          Bool.true_and]

/-- Characterisation of `pmask`. -/
theorem testBit_pmask {L P w : Nat} (hP : 0 < P) (hPL : P ∣ L) (hw : w ≤ P) (i : Nat) :
    (pmask L P w).testBit i = (decide (i < L) && decide (i % P < w)) := by
  have hmod : L % P = 0 := Nat.mod_eq_zero_of_dvd hPL
  rw [pmask, Nat.testBit_and, testBit_ones, hmod, Nat.sub_zero]
  by_cases hi : i < L
  · have hL : L ≤ P * 2 ^ L :=
      Nat.le_trans (Nat.le_of_lt Nat.lt_two_pow_self) (Nat.le_mul_of_pos_left _ hP)
    have hx : ∀ j, (ones w).testBit j = (decide (j < P) && decide (j % P < w)) := by
      intro j
      rw [testBit_ones]
      by_cases hj : j < P
      · rw [Nat.mod_eq_of_lt hj, decide_eq_true hj, Bool.true_and]
      · have : ¬ j < w := by omega
        rw [decide_eq_false hj, decide_eq_false this, Bool.false_and]
    rw [testBit_pfill L P (ones w) (Nat.dvd_refl P) hL hx i hi, decide_eq_true hi,
      Bool.true_and, Bool.and_true]
  · rw [decide_eq_false hi, Bool.and_false, Bool.false_and]

/-- `pmask` is the closed form `(2^w - 1) * ((2^L - 1) / (2^P - 1))` (the first run times a
geometric series) by which it was computed before the masks were built by shifts. -/
theorem pmask_eq {L P w : Nat} (hP : 0 < P) (hPL : P ∣ L) (hw : w ≤ P) :
    pmask L P w = (2 ^ w - 1) * ((2 ^ L - 1) / (2 ^ P - 1)) := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_pmask hP hPL hw]
  obtain ⟨n, rfl⟩ := hPL
  rw [Nat.mul_comm P n, div_eq_geoP hP, testBit_pmask_aux hw]

/-- `pmask` vanishes, as its closed form does, when `L < P` or `P = 0`. -/
theorem pmask_of_lt {L P w : Nat} (h : L < P ∨ P = 0) : pmask L P w = 0 := by
  have h0 : L - L % P = 0 := by
    rcases h with h | rfl
    · rw [Nat.mod_eq_of_lt h, Nat.sub_self]
    · rw [Nat.mod_zero, Nat.sub_self]
  rw [pmask, h0, show ones 0 = 0 from rfl, Nat.and_zero]

/-- `xlate lo w y`: move the bits of `y` selected by `lo` up by `w`, and the bits `w` above
`lo` down by `w`.  With `lo = pmask L (2*w) w` this exchanges the bits `i` and `i + w` for
every `i < L` with `i % (2*w) < w` (and drops the bits of `y` above `L`). -/
def xlate (lo w y : Nat) : Nat := ((y &&& lo) <<< w) ||| ((y >>> w) &&& lo)

/-- The partner of bit `i` in the translation by `w` inside aligned blocks of `2*w` bits. -/
def xpartner (w i : Nat) : Nat := if i % (2 * w) < w then i + w else i - w

/-- Euclidean division by `2 * w`. -/
theorem mod_two_mul_cases {w i : Nat} (hw : 0 < w) :
    ∃ q ρ, i = 2 * w * q + ρ ∧ ρ < 2 * w ∧ i % (2 * w) = ρ :=
  ⟨i / (2 * w), i % (2 * w), (Nat.div_add_mod i (2 * w)).symm, Nat.mod_lt _ (by omega), rfl⟩

/-- Characterisation of `xlate` with its periodic mask: bit `i` of the result is bit
`xpartner w i` of `y`, for `i < L` (and `0` above `L`); no hypothesis on `y` is needed. -/
theorem testBit_xlate {L w : Nat} (hw : 0 < w) (hL : 2 * w ∣ L) (y i : Nat) :
    (xlate (pmask L (2 * w) w) w y).testBit i = (decide (i < L) && y.testBit (xpartner w i)) := by
  have h2w : 0 < 2 * w := by omega
  have hlo := fun j => testBit_pmask (L := L) (P := 2 * w) (w := w) h2w hL (by omega) j
  obtain ⟨q', rfl⟩ := hL
  obtain ⟨q, ρ, hi, hρ, hm⟩ := mod_two_mul_cases (i := i) hw
  simp only [xlate, xpartner, Nat.testBit_lor, Nat.testBit_land, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, hlo, hm]
  -- i < L ↔ q < q'
  have hiL : i < 2 * w * q' ↔ q < q' := by
    constructor
    · intro h; by_contra hc; push Not at hc
      have := Nat.mul_le_mul_left (2 * w) hc; omega
    · intro h
      have : 2 * w * (q + 1) ≤ 2 * w * q' := Nat.mul_le_mul_left _ h
      rw [Nat.mul_add] at this; omega
  by_cases hρw : ρ < w
  · -- first half: partner is i + w; the shifted-down term is excluded
    have hA : ¬ (w ≤ i ∧ (i - w) % (2 * w) < w) := by
      rintro ⟨hwi, h⟩
      have hq : 1 ≤ q := by
        by_contra hc; push Not at hc
        have : q = 0 := by omega
        subst this; simp at hi; omega
      have e : i - w = 2 * w * (q - 1) + (ρ + w) := by
        have : 2 * w * q = 2 * w * (q - 1) + 2 * w := by
          rw [← Nat.mul_add_one]; congr 1; omega
        omega
      rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)] at h
      omega
    simp only [hρw, decide_true, Bool.and_true, ite_true]
    by_cases hwi : w ≤ i
    · have : ¬ ((i - w) % (2 * w) < w) := fun h => hA ⟨hwi, h⟩
      simp [hwi, this, Nat.add_comm w i, Bool.and_comm]
    · simp [hwi, Nat.add_comm w i, Bool.and_comm]
  · -- second half: partner is i - w
    have hwi : w ≤ i := by omega
    have e : i - w = 2 * w * q + (ρ - w) := by omega
    have hmod : (i - w) % (2 * w) = ρ - w := by
      rw [e, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    have hL' : i - w < 2 * w * q' ↔ i < 2 * w * q' := by
      constructor
      · intro h
        by_contra hc; push Not at hc
        -- i ≥ L and i - w < L force ρ < w
        have h1 : q' ≤ q := by
          by_contra hc2; push Not at hc2
          have : 2 * w * (q + 1) ≤ 2 * w * q' := Nat.mul_le_mul_left _ hc2
          rw [Nat.mul_add] at this; omega
        have : 2 * w * q' ≤ 2 * w * q := Nat.mul_le_mul_left _ h1
        omega
      · intro h; omega
    simp only [hρw, decide_false, Bool.and_false, Bool.or_false, ite_false, hwi,
      decide_true, Bool.true_and, hmod, hL']
    have : ρ - w < w := by omega
    simp [this, Bool.and_comm]

/-- `xlate` with its periodic mask stays below `2 ^ L`. -/
theorem xlate_lt {L w : Nat} (hw : 0 < w) (hL : 2 * w ∣ L) (y : Nat) :
    xlate (pmask L (2 * w) w) w y < 2 ^ L := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_xlate hw hL]
  simp [Nat.not_lt.mpr hi]

/-! ### Delta-swap networks -/

/-- A layer of a delta-swap network: `(mask, distance)`. -/
abbrev Layer := Nat × Nat

/-- A delta-swap network (applied left to right). -/
abbrev Net := List Layer

/-- Delta swap: exchange bits `i` and `i + d` of `x` for every `i` in the mask `m`. -/
def deltaSwap (x : Nat) (md : Layer) : Nat :=
  let t := ((x >>> md.2) ^^^ x) &&& md.1
  x ^^^ t ^^^ (t <<< md.2)

/-- Apply a network of delta swaps, first layer first. -/
def applyNet (net : Net) (x : Nat) : Nat := net.foldl deltaSwap x

/-- The swapped pairs of a layer are disjoint: no bit `i` of the mask has bit `i + d` of the
mask set.  (Checked by the kernel for the networks used by the engine.) -/
def layerOK (md : Layer) : Bool := Nat.beq (md.1 &&& (md.1 <<< md.2)) 0

/-- The source position of bit `i` after a delta swap. -/
def layerSrc (md : Layer) (i : Nat) : Nat :=
  if md.1.testBit i then i + md.2
  else if md.2 ≤ i ∧ md.1.testBit (i - md.2) then i - md.2 else i

/-- The source position of bit `i` after a network (the composite of the `layerSrc`). -/
def netSrc : Net → Nat → Nat
  | [], i => i
  | md :: net, i => layerSrc md (netSrc net i)

/-- A valid delta swap is the bit permutation `layerSrc`. -/
theorem testBit_deltaSwap {md : Layer} (h : layerOK md = true) (x i : Nat) :
    (deltaSwap x md).testBit i = x.testBit (layerSrc md i) := by
  obtain ⟨m, d⟩ := md
  simp only [layerOK, Nat.beq_eq] at h
  have hdis : ∀ j, m.testBit j = true → d ≤ j → m.testBit (j - d) = false := by
    intro j hj hdj
    have := congrArg (fun n => n.testBit j) h
    simp only [Nat.testBit_land, Nat.testBit_shiftLeft, Nat.zero_testBit, hj, Bool.true_and,
      Bool.and_eq_false_iff, decide_eq_false_iff_not, not_le] at this
    rcases this with h1 | h1
    · omega
    · exact h1
  simp only [deltaSwap, layerSrc, Nat.testBit_xor, Nat.testBit_land, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  by_cases hm : m.testBit i = true
  · have h2 : ¬ (d ≤ i ∧ m.testBit (i - d) = true) := fun ⟨hd, hm'⟩ => by
      simp [hdis i hm hd] at hm'
    rw [ite_eq_left hm]
    by_cases hd : d ≤ i
    · have h3 : m.testBit (i - d) = false := hdis i hm hd
      simp only [hm, hd, h3, Nat.add_comm, Bool.and_true, Bool.and_false, decide_true,
        Bool.xor_false]
      cases x.testBit i <;> cases x.testBit (i + d) <;> rfl
    · simp only [hm, hd, Nat.add_comm, Bool.and_true, decide_false, Bool.false_and,
        Bool.xor_false]
      cases x.testBit i <;> cases x.testBit (i + d) <;> rfl
  · have hm' : m.testBit i = false := by simpa using hm
    rw [ite_eq_right hm]
    by_cases hc : d ≤ i ∧ m.testBit (i - d) = true
    · rw [ite_eq_left hc]
      have : d + (i - d) = i := by omega
      simp [hm', hc.1, hc.2, this]
    · rw [ite_eq_right hc]
      by_cases hd : d ≤ i
      · have : m.testBit (i - d) = false := by simpa [hd] using hc
        simp [hm', hd, this]
      · simp [hm', hd]

/-- A network of valid delta swaps is the bit permutation `netSrc`. -/
theorem testBit_applyNet {net : Net} (h : net.all layerOK = true) (x i : Nat) :
    (applyNet net x).testBit i = x.testBit (netSrc net i) := by
  induction net generalizing x with
  | nil => rfl
  | cons md net ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [applyNet, List.foldl_cons] at ih ⊢
    rw [ih h.2, testBit_deltaSwap h.1]
    rfl

end FourColor.Engine
