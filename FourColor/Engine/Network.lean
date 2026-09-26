/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Layout

/-!
# Reducibility engine: fixed permutations of the layout, checked by the kernel

Two fixed bit permutations per ring size `r` are realised by delta-swap networks whose masks
are computed outside the kernel (Beneš routing, at elaboration time, see `Gen.lean`) and
*verified* by the kernel:

* `τ12` (`TauSpec r net`): the color transposition `Color1 ↔ Color2` on the concatenated
  packed layout (`Color2 ↔ Color3` is cheap, see `tau23`); together they generate the six
  color permutations used by the permutation closure;
* the conversion (`CnvSpec r net`) from the base-3 layout of the *prefixes* `t.take (r - 1)`
  (the last entry of a valid trace is determined by the others) to the packed layout, used
  to convert the output of the coloring DP.

More generally `NetSpec r net f` states that `net` realises the trace map `f`; the maps used
are the *transforms* `xform r σ g` (`t ↦ (p ↦ g t_{σ p})`), e.g. for the ring reversal of
`birkhoff.v`.

## Verification

By `testBit_applyNet` a network of valid layers is a bit permutation `netSrc net`.  A bit
permutation is determined, on the positions of valid traces, by the images of the
*coordinate indicator sets* `ind r p c = {t | t_p = c}` (they separate the traces), so
`xformCheck`/`cnvCheck` compare `applyNet net (ind r p c)` with the expected indicator set
for all `3r` pairs `(p, c)`: `netSpec_of_xformCheck`, `cnvSpec_of_check`.

The indicator sets are computed efficiently from the recursive structure of the layout:
for a grade `k ≥ 1` (`m = 2k`, `B` blocks, `R = 2^(m-1)` rows),
`{t | t_p = c} = ∑_τ W_τ * rows_{τ,c}` where `W_τ` (a `B`-bit vector, `wtable`) marks the
blocks in which `p` has type `τ` (`0`: `p` not in the block, `l + 1`: `p` has rank `l`), and
`rows_{τ,c}` marks, with one bit per row (at multiples of `B`), the rows `xp` for which the
entry `p` has color `c` (`repAll`, `repBit`: bit `l - 1` of `xp` for rank `l ≥ 1`,
`repPar`: parity of `xp` for rank `0`).  The products do not overlap.
-/

namespace FourColor.Engine

open FourColor

/-- The nonzero colors. -/
def colorsNZ : List Color := [Color1, Color2, Color3]

/-! ### Specifications -/

/-- The trace `p ↦ g (t_{σ p})`, `p < r`. -/
def xform (r : Nat) (σ : Nat → Nat) (g : EdgePerm) (t : Colseq) : Colseq :=
  (List.range r).map fun p => permc g (t.getD (σ p) Color0)

/-- `net` realises the trace map `f` on the concatenated layout of ring size `r`: bit
`cpos r t` of `applyNet net x` is bit `cpos r (f t)` of `x`, for every valid trace `t`. -/
def NetSpec (r : Nat) (net : Net) (f : Colseq → Colseq) : Prop :=
  ∀ t, ValidTrace r t → ∀ x, (applyNet net x).testBit (cpos r t) = x.testBit (cpos r (f t))

/-- `net` realises the color transposition `Color1 ↔ Color2`. -/
def TauSpec (r : Nat) (net : Net) : Prop := NetSpec r net (permt Eperm213)

/-- `net` converts the base-3 layout of the prefixes of length `r - 1` into the packed
layout. -/
def CnvSpec (r : Nat) (net : Net) : Prop :=
  ∀ t, ValidTrace r t → ∀ x,
    (applyNet net x).testBit (cpos r t) = x.testBit (b3idx (t.take (r - 1)))

/-! ### Indicator sets of the packed layout -/

/-- Block types for sequences of length `n ≥ 1` whose head is the tracked position, for `m`
non-`Color1` entries: type `0` (head not in the block) for the first `choose (n-1) m`
blocks, type `1` (head of rank `0`) for the other ones. -/
def wbase (n m τ : Nat) : Nat :=
  if τ == 0 then ones (chooseAux (n - 1) m)
  else if τ == 1 then
    (if m == 0 then 0 else ones (chooseAux (n - 1) (m - 1)) <<< chooseAux (n - 1) m)
  else 0

/-- The table of block types, `[m][τ]` for `m ≤ n`, `τ ≤ m`, for sequences of length `n`
whose head is the tracked position. -/
def wlevelBase (n : Nat) : List (List Nat) :=
  (List.range (n + 1)).map fun m => (List.range (m + 1)).map fun τ => wbase n m τ

/-- The table for sequences of length `n + 1` from the table for their tail (of length `n`):
the blocks without the new head come first, then those containing it, in which the ranks of
the tracked position increase by one. -/
def wnext (n : Nat) (lv : List (List Nat)) : List (List Nat) :=
  (List.range (n + 2)).map fun m => (List.range (m + 1)).map fun τ =>
    let a := (lv.getD m []).getD τ 0
    let b :=
      if m == 0 then 0
      else if τ == 0 then (lv.getD (m - 1) []).getD 0 0
      else if τ == 1 then 0
      else (lv.getD (m - 1) []).getD (τ - 1) 0
    a ||| (b <<< chooseAux n m)

/-- Iterate `wnext` `s` times from length `n`. -/
def wtableAux : Nat → Nat → List (List Nat) → List (List Nat)
  | 0, _, lv => lv
  | s + 1, n, lv => wtableAux s (n + 1) (wnext n lv)

/-- The table of block types of position `p` for ring size `r`: `(wtable r p)[m][τ]` has
bit `b` set iff position `p` has type `τ` in the `b`-th block of size `m`. -/
def wtable (r p : Nat) : List (List Nat) := wtableAux p (r - p) (wlevelBase (r - p))

/-- One bit per row, at multiples of `B`, for the `R` rows: the geometric series
`(2 ^ (R * B) - 1) / (2 ^ B - 1)` (`repAll_eq`), built by doubling (`pmask`). -/
def repAll (B R : Nat) : Nat := pmask (R * B) B 1

/-- `repAll` is the geometric series `(2 ^ (R * B) - 1) / (2 ^ B - 1)`. -/
theorem repAll_eq (B R : Nat) : repAll B R = (2 ^ (R * B) - 1) / (2 ^ B - 1) := by
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · rw [repAll, pmask_of_lt (Or.inr rfl)]; simp
  · rw [repAll, pmask_eq hB (Nat.dvd_mul_left B R) (by omega)]; simp

/-- The row bits of the rows `xp < R` whose bit `j` is `v`. -/
def repBit (B R j : Nat) (v : Bool) : Nat :=
  let lo := pmask (R * B) (2 * (2 ^ j * B)) (2 ^ j * B) &&& repAll B R
  if v then repAll B R ^^^ lo else lo

/-- The row bits of the rows `xp < 2^j` of even popcount (Thue–Morse). -/
def repPar (B : Nat) : Nat → Nat
  | 0 => 1
  | j + 1 =>
    let T := repPar B j
    T ||| ((repAll B (2 ^ j) ^^^ T) <<< (2 ^ j * B))

/-- The indicator of `{t | t_p = c}` in grade `k` of ring size `r`, given the block-type
table `W = wtable r p` of the position `p`. -/
def indGradeW (r k : Nat) (W : List (List Nat)) (c : Color) : Nat :=
  if k == 0 then (match c with | Color1 => gsize r 0 | _ => 0) else
  let m := 2 * k
  let B := chooseAux r m
  let R := 2 ^ (m - 1)
  let Wm := W.getD m []
  let all := repAll B R
  match c with
  | Color0 => 0
  | Color1 => Wm.getD 0 0 * all
  | _ =>
    let even := repPar B (m - 1)
    -- the rank-0 entry is `Color3` iff `r + popcount xp` is odd
    let par0 := if (r % 2 == 0) == (c == Color2) then even else all ^^^ even
    (List.range (m - 1)).foldl
      (fun acc l => acc ||| Wm.getD (l + 2) 0 * repBit B R l (c == Color3))
      (Wm.getD 1 0 * par0)

/-- The indicator of `{t | t_p = c}` in grade `k` of ring size `r`. -/
def indGrade (r k p : Nat) (c : Color) : Nat := indGradeW r k (wtable r p) c

/-- The indicator of `{t | t_p = c}` in the concatenated layout, given `W = wtable r p`. -/
def indW (r : Nat) (W : List (List Nat)) (c : Color) : Nat :=
  catG r ((List.range (ngrades r)).map fun k => indGradeW r k W c)

/-- The indicator of `{t | t_p = c}` in the concatenated packed layout of ring size `r`. -/
def ind (r p : Nat) (c : Color) : Nat := indW r (wtable r p) c

/-- The indicator of `{prefix | prefix_p = c}` in the base-3 layout of `n` digits. -/
def b3ind (n p : Nat) (c : Color) : Nat := digitMask n p (cdig c)

/-! ### Kernel checks -/

/-- The check that `net` realises `xform r σ g`: valid layers, and the right image of every
coordinate indicator set. -/
def xformCheck (r : Nat) (net : Net) (σ : Nat → Nat) (g : EdgePerm) : Bool :=
  net.all layerOK && (List.range r).all fun p =>
    let W := wtable r p
    let W' := wtable r (σ p)
    colorsNZ.all fun c =>
      Nat.beq (applyNet net (indW r W c) &&& fullMask r) (indW r W' (permc (invEperm g) c))

/-- The check that `net` realises `Color1 ↔ Color2` (the specialisation of
`xformCheck r net id Eperm213` computing each indicator set once). -/
def tauCheck (r : Nat) (net : Net) : Bool :=
  net.all layerOK && (List.range r).all fun p =>
    let W := wtable r p
    let i1 := indW r W Color1
    let i2 := indW r W Color2
    let i3 := indW r W Color3
    Nat.beq (applyNet net i1 &&& fullMask r) i2 && Nat.beq (applyNet net i2 &&& fullMask r) i1 &&
      Nat.beq (applyNet net i3 &&& fullMask r) i3

/-- The check that `net` converts the base-3 prefixes into the packed layout. -/
def cnvCheck (r : Nat) (net : Net) : Bool :=
  net.all layerOK && (List.range (r - 1)).all fun p =>
    let W := wtable r p
    colorsNZ.all fun c =>
      Nat.beq (applyNet net (b3ind (r - 1) p c) &&& fullMask r) (indW r W c)

/-! ### Proof helpers: row sets and products -/

/-- Division with remainder by `B` and comparison of rows. -/
private theorem row_lt_iff {B x y ρ : Nat} (hρ : ρ < B) : x * B + ρ < y * B ↔ x < y := by
  constructor
  · intro h
    by_contra hc
    have := Nat.mul_le_mul_right B (Nat.le_of_not_lt hc)
    omega
  · intro h
    have := Nat.mul_le_mul_right B (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at this
    omega

private theorem row_le_iff {B x y ρ : Nat} (hρ : ρ < B) : y * B ≤ x * B + ρ ↔ y ≤ x := by
  have := row_lt_iff (x := x) (y := y) hρ
  constructor
  · intro h; by_contra hc; push Not at hc
    have := Nat.mul_le_mul_right B (Nat.succ_le_of_lt hc)
    rw [Nat.succ_mul] at this; omega
  · intro h; have := Nat.mul_le_mul_right B h; omega

/-- A number whose bits are only at multiples of `B`, the bit of row `x` being `P x`. -/
private def RowSet (B y : Nat) (P : Nat → Bool) : Prop :=
  ∀ x ρ, ρ < B → y.testBit (x * B + ρ) = (decide (ρ = 0) && P x)

/-- The bits of a product `W * y` of a column vector `W < 2^B` and a row set `y`. -/
private theorem testBit_mul_rowSet {B W y : Nat} {P : Nat → Bool} (hW : W < 2 ^ B)
    (hy : RowSet B y P) (x b : Nat) (hb : b < B) :
    (W * y).testBit (x * B + b) = (P x && W.testBit b) := by
  induction x generalizing y P with
  | zero =>
    have hB : 0 < B := by omega
    have e : y = 2 ^ B * (y / 2 ^ B) + y % 2 ^ B := (Nat.div_add_mod y _).symm
    have hmod : y % 2 ^ B < 2 ^ 1 := by
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      rw [Nat.testBit_mod_two_pow]
      by_cases hiB : i < B
      · have := hy 0 i hiB
        simp only [Nat.zero_mul, Nat.zero_add] at this
        rw [this]; simp; omega
      · simp [hiB]
    have hy0 := hy 0 0 hB
    simp only [Nat.zero_mul, Nat.zero_add, decide_true, Bool.true_and] at hy0 ⊢
    have hm : y % 2 ^ B = if P 0 then 1 else 0 := by
      have h0 : (y % 2 ^ B).testBit 0 = P 0 := by rw [Nat.testBit_mod_two_pow, hy0]; simp [hB]
      rw [Nat.testBit_zero] at h0
      have hmod' : y % 2 ^ B < 2 := by simpa using hmod
      cases hp : P 0
      · rw [hp] at h0
        have := of_decide_eq_false h0
        simp only [Bool.false_eq_true, ite_false]; omega
      · rw [hp] at h0
        have := of_decide_eq_true h0
        simp only [ite_true]; omega
    have hlt : W * (y % 2 ^ B) < 2 ^ B := by
      rw [hm]; split_ifs <;> simp [hW]
    rw [e, Nat.mul_add, Nat.mul_left_comm, Nat.testBit_two_pow_mul_add _ hlt, ite_eq_left hb, hm]
    split_ifs with hp <;> simp [hp]
  | succ x ih =>
    have hB : 0 < B := by omega
    have e : y = 2 ^ B * (y / 2 ^ B) + y % 2 ^ B := (Nat.div_add_mod y _).symm
    have hmod : y % 2 ^ B < 2 ^ 1 := by
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      rw [Nat.testBit_mod_two_pow]
      by_cases hiB : i < B
      · have := hy 0 i hiB
        simp only [Nat.zero_mul, Nat.zero_add] at this
        rw [this]; simp; omega
      · simp [hiB]
    have hlt : W * (y % 2 ^ B) < 2 ^ B := by
      have : y % 2 ^ B ≤ 1 := by omega
      calc W * (y % 2 ^ B) ≤ W * 1 := Nat.mul_le_mul_left _ this
        _ < 2 ^ B := by simpa using hW
    have hy' : RowSet B (y / 2 ^ B) (fun x => P (x + 1)) := by
      intro x ρ hρ
      rw [Nat.testBit_div_two_pow]
      have : x * B + ρ + B = (x + 1) * B + ρ := by rw [Nat.succ_mul]; omega
      rw [this, hy _ _ hρ]
    rw [e, Nat.mul_add, Nat.mul_left_comm, Nat.testBit_two_pow_mul_add _ hlt]
    have h1 : ¬ ((x + 1) * B + b < B) := by rw [Nat.succ_mul]; omega
    have h2 : (x + 1) * B + b - B = x * B + b := by rw [Nat.succ_mul]; omega
    rw [ite_eq_right h1, h2, ih hy']

/-- `repAll`: all the rows `x < R`. -/
private theorem rowSet_repAll {B : Nat} (hB : 0 < B) (R : Nat) :
    RowSet B (repAll B R) (fun x => decide (x < R)) := by
  intro x ρ hρ
  rw [repAll, testBit_pmask hB (Nat.dvd_mul_left B R) (by omega)]
  have h1 : (x * B + ρ) % B = ρ := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hρ]
  rw [h1]
  have h2 : x * B + ρ < R * B ↔ x < R := row_lt_iff hρ
  simp only [h2]
  by_cases hr : ρ = 0
  · simp [hr]
  · have : ¬ ρ < 1 := by omega
    simp [hr, this]

/-- `x % 2^(j+1) < 2^j` iff bit `j` of `x` is clear. -/
private theorem mod_two_pow_succ_lt (x j : Nat) :
    x % 2 ^ (j + 1) < 2 ^ j ↔ x.testBit j = false := by
  rw [Nat.mod_pow_succ]
  have h1 := Nat.testBit_div_two_pow (n := j) x 0
  rw [Nat.zero_add, Nat.testBit_zero] at h1
  have h2 : x / 2 ^ j % 2 < 2 := Nat.mod_lt _ (by omega)
  have h3 : x % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
  rw [← h1]
  constructor
  · intro h
    have : x / 2 ^ j % 2 = 0 := by
      by_contra hc
      have : x / 2 ^ j % 2 = 1 := by omega
      rw [this] at h; omega
    simp [this]
  · intro h
    have : x / 2 ^ j % 2 = 0 := by simp at h; omega
    rw [this]; omega

/-- `repBit`: the rows `x < R` whose bit `j` is `v`. -/
private theorem rowSet_repBit {B R j : Nat} (hB : 0 < B) (hR : 2 ^ (j + 1) ∣ R) (v : Bool) :
    RowSet B (repBit B R j v) (fun x => decide (x < R) && (x.testBit j == v)) := by
  have hall := rowSet_repAll hB R
  have hP : 0 < 2 * (2 ^ j * B) := by
    have := Nat.mul_pos (Nat.two_pow_pos j) hB; omega
  have hdvd : 2 * (2 ^ j * B) ∣ R * B := by
    obtain ⟨q, rfl⟩ := hR
    exact ⟨q, by rw [Nat.pow_succ]; ring⟩
  have hlo : RowSet B (pmask (R * B) (2 * (2 ^ j * B)) (2 ^ j * B) &&& repAll B R)
      (fun x => decide (x < R) && !x.testBit j) := by
    intro x ρ hρ
    rw [Nat.testBit_and, hall x ρ hρ, testBit_pmask hP hdvd (by omega)]
    by_cases hr : ρ = 0
    · subst hr
      simp only [Nat.add_zero]
      have e : x * B % (2 * (2 ^ j * B)) = x % 2 ^ (j + 1) * B := by
        rw [show 2 * (2 ^ j * B) = 2 ^ (j + 1) * B by rw [Nat.pow_succ]; ring,
          Nat.mul_mod_mul_right]
      have e2 : (x * B % (2 * (2 ^ j * B)) < 2 ^ j * B) ↔ x.testBit j = false := by
        rw [e, Nat.mul_lt_mul_right hB, mod_two_pow_succ_lt]
      have e3 : x * B < R * B ↔ x < R := Nat.mul_lt_mul_right hB
      simp only [e2, e3]
      cases x.testBit j <;> simp
    · simp [hr]
  intro x ρ hρ
  unfold repBit
  cases v
  · simp only [Bool.false_eq_true, ite_false]
    rw [hlo x ρ hρ]
    beta_reduce
    cases x.testBit j <;> simp
  · simp only [ite_true]
    rw [Nat.testBit_xor, hall x ρ hρ, hlo x ρ hρ]
    beta_reduce
    cases x.testBit j <;> cases decide (x < R) <;> cases decide (ρ = 0) <;> rfl

/-- The parity of the popcount of the low `j` bits. -/
private def par : Nat → Nat → Bool
  | 0, _ => false
  | j + 1, x => par j x ^^ x.testBit j

private theorem par_congr {j x y : Nat} (h : ∀ i < j, x.testBit i = y.testBit i) :
    par j x = par j y := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [par]
    rw [ih (fun i hi => h i (by omega)), h j (by omega)]

private theorem par_succ_low (j x : Nat) : par (j + 1) x = (x.testBit 0 ^^ par j (x / 2)) := by
  induction j with
  | zero => simp [par]
  | succ j ih =>
    rw [par, ih, par, Nat.testBit_div_two]
    cases x.testBit 0 <;> cases par j (x / 2) <;> cases x.testBit (j + 1) <;> rfl

private theorem nw_testBit_one (i : Nat) : (1 : Nat).testBit i = decide (i = 0) := by
  cases i with
  | zero => rfl
  | succ i => rw [Nat.testBit_succ]; simp

/-- `repPar`: the rows `x < 2^j` of even popcount. -/
private theorem rowSet_repPar {B : Nat} (hB : 0 < B) (j : Nat) :
    RowSet B (repPar B j) (fun x => decide (x < 2 ^ j) && !par j x) := by
  induction j with
  | zero =>
    intro x ρ hρ
    simp only [repPar, par, Nat.pow_zero, Bool.not_false, Bool.and_true]
    rw [nw_testBit_one]
    have : x * B + ρ = 0 ↔ ρ = 0 ∧ x < 1 := by
      constructor
      · intro h
        have h1 : x * B = 0 := by omega
        rcases Nat.mul_eq_zero.1 h1 with h2 | h2 <;> omega
      · rintro ⟨h1, h2⟩
        have : x = 0 := by omega
        subst_vars; simp
    by_cases h : ρ = 0 ∧ x < 1
    · have hx : x = 0 := by omega
      simp [hx, h.1]
    · have h' := mt this.1 h
      simp only [h', decide_false]
      by_cases hr : ρ = 0
      · have : ¬ x < 1 := fun hx => h ⟨hr, hx⟩
        simp [hr, this]
      · simp [hr]
  | succ j ih =>
    intro x ρ hρ
    have hall := rowSet_repAll hB (2 ^ j)
    simp only [repPar]
    rw [Nat.testBit_or, Nat.testBit_shiftLeft, ih x ρ hρ]
    simp only [par]
    by_cases hx : 2 ^ j ≤ x
    · have hge : x * B + ρ ≥ 2 ^ j * B := (row_le_iff hρ).2 hx
      have e : x * B + ρ - 2 ^ j * B = (x - 2 ^ j) * B + ρ := by
        rw [Nat.sub_mul]; have := Nat.mul_le_mul_right B hx; omega
      rw [e, Nat.testBit_xor, hall _ _ hρ, ih _ _ hρ]
      beta_reduce
      have hpar : par j (x - 2 ^ j) = par j x := by
        apply par_congr
        intro i hi
        have h1 := Nat.testBit_mod_two_pow (x - 2 ^ j) j i
        have h2 := Nat.testBit_mod_two_pow x j i
        rw [← Nat.mod_eq_sub_mod hx] at h1
        simp only [hi, decide_true, Bool.true_and] at h1 h2
        rw [← h1, h2]
      have hxl : ¬ x < 2 ^ j := by omega
      rw [hpar]
      by_cases hx2 : x < 2 ^ (j + 1)
      · have hbit : x.testBit j = true := by
          have := (mod_two_pow_succ_lt x j).not
          rw [Nat.mod_eq_of_lt hx2] at this
          simpa [hxl] using this
        have : x - 2 ^ j < 2 ^ j := by rw [Nat.pow_succ] at hx2; omega
        simp [hxl, hge, this, hx2, hbit]
        cases par j x <;> cases decide (ρ = 0) <;> rfl
      · have : ¬ x - 2 ^ j < 2 ^ j := by rw [Nat.pow_succ] at hx2; omega
        simp [hxl, hge, this, hx2]
    · have hlt : ¬ x * B + ρ ≥ 2 ^ j * B := by rw [ge_iff_le, row_le_iff hρ]; exact hx
      have hx' : x < 2 ^ j := by omega
      have hx2 : x < 2 ^ (j + 1) := by rw [Nat.pow_succ]; omega
      have hbit : x.testBit j = false := Nat.testBit_lt_two_pow hx'
      simp [hlt, hx', hx2, hbit]

/-- The bits of an iterated `|||`. -/
private theorem testBit_foldl_or (f : Nat → Nat) (init : Nat) (n i : Nat) :
    (List.foldl (fun acc l => acc ||| f l) init (List.range n)).testBit i = true ↔
      (init.testBit i = true ∨ ∃ l < n, (f l).testBit i = true) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.testBit_or,
      Bool.or_eq_true, ih]
    constructor
    · rintro ((h | ⟨l, hl, h⟩) | h)
      · exact Or.inl h
      · exact Or.inr ⟨l, by omega, h⟩
      · exact Or.inr ⟨n, by omega, h⟩
    · rintro (h | ⟨l, hl, h⟩)
      · exact Or.inl (Or.inl h)
      · by_cases hln : l < n
        · exact Or.inl (Or.inr ⟨l, hln, h⟩)
        · have : l = n := by omega
          subst this; exact Or.inr h

/-! ### Proof helpers: traces -/

private theorem nw_nonOne_cons1 (t : Colseq) : nonOne (Color1 :: t) = nonOne t := by
  simp [nonOne]

private theorem nw_nonOne_cons_ne {c : Color} (hc : c ≠ Color1) (t : Colseq) :
    nonOne (c :: t) = nonOne t + 1 := by
  simp only [nonOne, List.countP_cons]
  cases c <;> simp_all

private theorem nw_nonOne_le (t : Colseq) : nonOne t ≤ t.length := List.countP_le_length

private theorem nw_blockRank_cons_ne {c : Color} (hc : c ≠ Color1) (t : Colseq) (m : Nat) :
    blockRank (c :: t) m = t.length.choose m + blockRank t (m - 1) := by
  cases c
  · simp [blockRank, chooseAux_eq]
  · exact absurd rfl hc
  · simp [blockRank, chooseAux_eq]
  · simp [blockRank, chooseAux_eq]

private theorem nw_blockRank_lt (t : Colseq) :
    blockRank t (nonOne t) < t.length.choose (nonOne t) := by
  induction t with
  | nil => simp [blockRank, nonOne]
  | cons c t ih =>
    by_cases hc : c = Color1
    · subst hc
      rw [nw_nonOne_cons1]
      simp only [blockRank, List.length_cons]
      exact Nat.lt_of_lt_of_le ih (Nat.choose_le_succ _ _)
    · rw [nw_nonOne_cons_ne hc, nw_blockRank_cons_ne hc, List.length_cons, Nat.choose_succ_succ',
        Nat.add_sub_cancel]
      omega

private theorem nw_xcode_cons (c : Color) (t : Colseq) :
    xcode (c :: t) =
      if c = Color1 then xcode t else 2 * xcode t + (if c = Color3 then 1 else 0) := by
  cases c <;> rfl

private theorem nw_xcode_lt (t : Colseq) : xcode t < 2 ^ nonOne t := by
  induction t with
  | nil => simp [xcode, nonOne]
  | cons c t ih =>
    rw [nw_xcode_cons]
    by_cases hc : c = Color1
    · subst hc; rw [nw_nonOne_cons1]; simpa using ih
    · rw [nw_nonOne_cons_ne hc, Nat.pow_succ, ite_eq_right hc]
      split_ifs <;> omega

/-- The type of position `q` in the block of `s`: `0` if `s_q = Color1`, `l + 1` if `s_q`
has rank `l` among the non-`Color1` entries. -/
private def typeOf : Colseq → Nat → Nat
  | [], _ => 0
  | c :: _, 0 => if c = Color1 then 0 else 1
  | c :: s, q + 1 =>
    if typeOf s q = 0 then 0 else if c = Color1 then typeOf s q else typeOf s q + 1

private theorem typeOf_le (s : Colseq) (q : Nat) : typeOf s q ≤ nonOne s := by
  induction s generalizing q with
  | nil => simp [typeOf]
  | cons c s ih =>
    cases q with
    | zero =>
      simp only [typeOf]
      split_ifs with hc
      · omega
      · rw [nw_nonOne_cons_ne hc]; omega
    | succ q =>
      simp only [typeOf]
      have := ih q
      split_ifs with h1 hc
      · omega
      · subst hc; rw [nw_nonOne_cons1]; exact this
      · rw [nw_nonOne_cons_ne hc]; omega

private theorem typeOf_eq_zero {s : Colseq} (h0 : Color0 ∉ s) {q : Nat} (hq : q < s.length) :
    typeOf s q = 0 ↔ s.getD q Color0 = Color1 := by
  induction s generalizing q with
  | nil => simp at hq
  | cons c s ih =>
    simp only [List.mem_cons, not_or] at h0
    cases q with
    | zero =>
      simp only [typeOf, List.getD_cons_zero]
      split_ifs with hc <;> simp [hc]
    | succ q =>
      simp only [typeOf, List.getD_cons_succ]
      rw [← ih h0.2 (by simpa using hq)]
      by_cases h : typeOf s q = 0 <;> by_cases hc : c = Color1 <;> simp [h, hc]

private theorem typeOf_rank {s : Colseq} (h0 : Color0 ∉ s) {q l : Nat} (hq : q < s.length)
    (h : typeOf s q = l + 1) : s.getD q Color0 = Color3 ↔ (xcode s).testBit l = true := by
  induction s generalizing q l with
  | nil => simp at hq
  | cons c s ih =>
    simp only [List.mem_cons, not_or] at h0
    rw [nw_xcode_cons]
    cases q with
    | zero =>
      simp only [typeOf] at h
      simp only [List.getD_cons_zero]
      split_ifs at h with hc
      have hl : l = 0 := by omega
      subst hl
      rw [ite_eq_right hc, Nat.testBit_zero]
      split_ifs with h3 <;> simp [h3]
    | succ q =>
      simp only [typeOf] at h
      simp only [List.getD_cons_succ]
      have hq' : q < s.length := by simpa using hq
      split_ifs at h with h1 hc
      · rw [ite_eq_left hc]; exact ih h0.2 hq' h
      · rw [ite_eq_right hc]
        obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
        rw [← Nat.testBit_div_two]
        have : (2 * xcode s + (if c = Color3 then 1 else 0)) / 2 = xcode s := by split_ifs <;> omega
        rw [this]
        exact ih h0.2 hq' (by omega)

private theorem cbit0_sumt {s : Colseq} (h0 : Color0 ∉ s) :
    cbit0 (sumt s) = (decide ((s.length + nonOne s) % 2 = 1) ^^ par (nonOne s) (xcode s)) := by
  induction s with
  | nil => rfl
  | cons c s ih =>
    simp only [List.mem_cons, not_or] at h0
    rw [sumt_cons, cbit0_addc, ih h0.2, nw_xcode_cons, List.length_cons]
    cases c with
    | Color0 => exact absurd rfl h0.1
    | Color1 =>
      rw [nw_nonOne_cons1]
      simp only [cbit0_Color1, ite_true]
      rcases Nat.mod_two_eq_zero_or_one (s.length + nonOne s) with h | h
      · have : (s.length + 1 + nonOne s) % 2 = 1 := by omega
        simp [h, this]
      · have : (s.length + 1 + nonOne s) % 2 = 0 := by omega
        simp [h, this]
    | Color2 =>
      rw [nw_nonOne_cons_ne (by decide), par_succ_low]
      have e1 : (2 * xcode s + 0) / 2 = xcode s := by omega
      simp only [cbit0_Color2, ite_eq_right (show Color2 ≠ Color1 by decide),
        ite_eq_right (show Color2 ≠ Color3 by decide), e1, Nat.testBit_zero]
      have e2 : (s.length + 1 + (nonOne s + 1)) % 2 = (s.length + nonOne s) % 2 := by omega
      simp [e2]
    | Color3 =>
      rw [nw_nonOne_cons_ne (by decide), par_succ_low]
      have e1 : (2 * xcode s + 1) / 2 = xcode s := by omega
      simp only [cbit0_Color3, ite_eq_right (show Color3 ≠ Color1 by decide), ↓reduceIte, e1,
        Nat.testBit_zero]
      have e2 : (s.length + 1 + (nonOne s + 1)) % 2 = (s.length + nonOne s) % 2 := by omega
      have e3 : (2 * xcode s + 1) % 2 = 1 := by omega
      simp only [e2, e3, decide_true]
      cases decide ((s.length + nonOne s) % 2 = 1) <;> cases par (nonOne s) (xcode s) <;> rfl

/-! ### Proof helpers: the block-type tables -/

private def getW (W : List (List Nat)) (m τ : Nat) : Nat := (W.getD m []).getD τ 0

private theorem getW_tab (f : Nat → Nat → Nat) (n m τ : Nat) :
    getW ((List.range (n + 1)).map fun m => (List.range (m + 1)).map fun τ => f m τ) m τ =
      if m ≤ n ∧ τ ≤ m then f m τ else 0 := by
  unfold getW
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hm : m ≤ n
  · rw [List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, List.getElem?_map]
    by_cases hτ : τ ≤ m
    · rw [List.getElem?_range (by omega)]; simp [hm, hτ]
    · rw [List.getElem?_eq_none (l := List.range (m + 1)) (by simp; omega)]; simp [hτ]
  · rw [List.getElem?_eq_none (l := List.range (n + 1)) (by simp; omega)]; simp [hm]

/-- The invariant of the block-type tables for sequences of length `n`, tracked position `q`. -/
private def WInv (n q : Nat) (W : List (List Nat)) : Prop :=
  (∀ m τ, getW W m τ < 2 ^ n.choose m) ∧
  ∀ s : Colseq, s.length = n → Color0 ∉ s → ∀ τ,
    (getW W (nonOne s) τ).testBit (blockRank s (nonOne s)) = decide (typeOf s q = τ)

private theorem shift_lt {a C D : Nat} (ha : a < 2 ^ D) : a <<< C < 2 ^ (D + C) := by
  rw [Nat.shiftLeft_eq, Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos C)

private theorem wInv_base {n : Nat} (hn : 1 ≤ n) : WInv n 0 (wlevelBase n) := by
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have e : wlevelBase (n' + 1) = (List.range (n' + 1 + 1)).map fun m =>
      (List.range (m + 1)).map fun τ => wbase (n' + 1) m τ := rfl
  rw [e]
  constructor
  · intro m τ
    rw [getW_tab]
    split_ifs
    · unfold wbase
      simp only [Nat.add_sub_cancel, chooseAux_eq, ones_eq]
      split_ifs with h1 h2 h3
      · have h4 : n'.choose m ≤ (n' + 1).choose m := Nat.choose_le_succ n' m
        calc 2 ^ n'.choose m - 1 < 2 ^ n'.choose m := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)
          _ ≤ 2 ^ (n' + 1).choose m := Nat.pow_le_pow_right (by norm_num) h4
      · exact Nat.two_pow_pos _
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at h3; omega⟩
        rw [Nat.choose_succ_succ', Nat.add_sub_cancel]
        exact shift_lt (Nat.sub_lt (Nat.two_pow_pos _) (by norm_num))
      · exact Nat.two_pow_pos _
    · exact Nat.two_pow_pos _
  · intro s hs h0 τ
    obtain ⟨c, s', rfl⟩ : ∃ c s', s = c :: s' := by
      cases s with
      | nil => simp at hs
      | cons c s' => exact ⟨c, s', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hs
    have hle := typeOf_le (c :: s') 0
    rw [getW_tab]
    by_cases hτ : τ ≤ nonOne (c :: s')
    · have hm : nonOne (c :: s') ≤ n' + 1 := by
        have := nw_nonOne_le (c :: s'); simpa [hs] using this
      rw [ite_eq_left ⟨hm, hτ⟩]
      unfold wbase
      simp only [Nat.add_sub_cancel, chooseAux_eq, ones_eq]
      by_cases hc : c = Color1
      · subst hc
        have ht : typeOf (Color1 :: s') 0 = 0 := rfl
        rw [ht]
        rw [nw_nonOne_cons1] at hτ ⊢
        have hb := nw_blockRank_lt s'
        rw [hs] at hb
        simp only [blockRank]
        rcases Nat.lt_trichotomy τ 1 with h | h | h
        · have : τ = 0 := by omega
          subst this; simp [hb]
        · subst h
          simp only [beq_self_eq_true, ite_true, show ((1 : Nat) == 0) = false from rfl,
            Bool.false_eq_true, ite_false]
          split_ifs
          · simp
          · rw [Nat.testBit_shiftLeft]; simp; omega
        · have h1 : (τ == 0) = false := by simp; omega
          have h2 : (τ == 1) = false := by simp; omega
          simp [h1, h2]; omega
      · have ht : typeOf (c :: s') 0 = 1 := by simp [typeOf, hc]
        rw [ht]
        rw [nw_nonOne_cons_ne hc] at hτ ⊢
        rw [nw_blockRank_cons_ne hc, hs, Nat.add_sub_cancel]
        have hb := nw_blockRank_lt s'
        rw [hs] at hb
        rcases Nat.lt_trichotomy τ 1 with h | h | h
        · have : τ = 0 := by omega
          subst this
          simp only [beq_self_eq_true, ite_true, Nat.testBit_two_pow_sub_one]
          simp
        · subst h
          simp only [show ((1 : Nat) == 0) = false from rfl, beq_self_eq_true, Bool.false_eq_true,
            ite_false, ite_true]
          simpa using hb
        · have h1 : (τ == 0) = false := by simp; omega
          have h2 : (τ == 1) = false := by simp; omega
          simp [h1, h2]; omega
    · rw [ite_eq_right (fun h => hτ h.2)]
      simp only [Nat.zero_testBit]
      symm; simp; omega

private theorem wInv_next {n q : Nat} {lv : List (List Nat)} (h : WInv n q lv) :
    WInv (n + 1) (q + 1) (wnext n lv) := by
  obtain ⟨hb, hs⟩ := h
  let f : Nat → Nat → Nat := fun m τ =>
    getW lv m τ |||
      ((if m == 0 then 0
        else if τ == 0 then getW lv (m - 1) 0
        else if τ == 1 then 0
        else getW lv (m - 1) (τ - 1)) <<< chooseAux n m)
  have e : wnext n lv = (List.range (n + 1 + 1)).map fun m =>
      (List.range (m + 1)).map fun τ => f m τ := rfl
  rw [e]
  constructor
  · intro m τ
    rw [getW_tab]
    split_ifs
    · simp only [f]
      rw [chooseAux_eq]
      cases m with
      | zero =>
        simp only [beq_self_eq_true, ite_true, Nat.zero_shiftLeft, Nat.or_zero]
        simpa using hb 0 τ
      | succ m =>
        rw [Nat.choose_succ_succ']
        apply Nat.or_lt_two_pow
        · exact Nat.lt_of_lt_of_le (hb _ _) (Nat.pow_le_pow_right (by norm_num) (by omega))
        · simp only [show (m + 1 == 0) = false by simp, Bool.false_eq_true, ite_false,
            Nat.add_sub_cancel]
          apply shift_lt
          split_ifs
          · exact hb _ _
          · exact Nat.two_pow_pos _
          · exact hb _ _
    · exact Nat.two_pow_pos _
  · intro s hlen h0 τ
    obtain ⟨c, s', rfl⟩ : ∃ c s', s = c :: s' := by
      cases s with
      | nil => simp at hlen
      | cons c s' => exact ⟨c, s', rfl⟩
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.mem_cons, not_or] at h0
    have hle := typeOf_le (c :: s') (q + 1)
    rw [getW_tab]
    by_cases hτ : τ ≤ nonOne (c :: s')
    · have hm : nonOne (c :: s') ≤ n + 1 := by
        have := nw_nonOne_le (c :: s'); simpa [hlen] using this
      rw [ite_eq_left ⟨hm, hτ⟩]
      simp only [f]
      have hbr := nw_blockRank_lt s'
      rw [hlen] at hbr
      have ih := hs s' hlen h0.2
      by_cases hc : c = Color1
      · subst hc
        have ht : typeOf (Color1 :: s') (q + 1) = typeOf s' q := by
          simp only [typeOf]; by_cases h : typeOf s' q = 0 <;> simp [h]
        rw [ht, nw_nonOne_cons1]
        simp only [blockRank, Nat.testBit_or, Nat.testBit_shiftLeft, chooseAux_eq]
        have : ¬ (blockRank s' (nonOne s') ≥ n.choose (nonOne s')) := by omega
        simp only [this, decide_false, Bool.false_and, Bool.or_false, ih]
      · have ht : typeOf (c :: s') (q + 1) =
            if typeOf s' q = 0 then 0 else typeOf s' q + 1 := by
          simp [typeOf, hc]
        rw [ht, nw_nonOne_cons_ne hc, nw_blockRank_cons_ne hc, hlen]
        simp only [Nat.testBit_or, Nat.testBit_shiftLeft, chooseAux_eq, Nat.add_sub_cancel,
          show (nonOne s' + 1 == 0) = false by simp, Bool.false_eq_true, ite_false]
        have hlow : (getW lv (nonOne s' + 1) τ).testBit
            (n.choose (nonOne s' + 1) + blockRank s' (nonOne s')) = false := by
          apply Nat.testBit_lt_two_pow
          exact Nat.lt_of_lt_of_le (hb _ _) (Nat.pow_le_pow_right (by norm_num) (by omega))
        rw [hlow, Bool.false_or, Nat.add_sub_cancel_left]
        simp only [ge_iff_le, Nat.le_add_right, decide_true, Bool.true_and]
        rcases Nat.lt_trichotomy τ 1 with h | h | h
        · have : τ = 0 := by omega
          subst this
          simp only [beq_self_eq_true, ite_true, ih]
          by_cases h : typeOf s' q = 0 <;> simp [h]
        · subst h
          simp only [show ((1 : Nat) == 0) = false from rfl, beq_self_eq_true, Bool.false_eq_true,
            ite_false, ite_true, Nat.zero_testBit]
          by_cases h : typeOf s' q = 0 <;> simp [h]
        · have h1 : (τ == 0) = false := by simp; omega
          have h2 : (τ == 1) = false := by simp; omega
          simp only [h1, h2, Bool.false_eq_true, ite_false, ih]
          by_cases h : typeOf s' q = 0
          · simp [h]; omega
          · simp only [h, ite_false]
            rw [Bool.eq_iff_iff]; simp; omega
    · rw [ite_eq_right (fun h => hτ h.2)]
      simp only [Nat.zero_testBit]
      symm; simp; omega

private theorem wInv_aux : ∀ (s n q : Nat) (lv : List (List Nat)), WInv n q lv →
    WInv (n + s) (q + s) (wtableAux s n lv)
  | 0, _, _, _, h => h
  | s + 1, n, q, lv, h => by
    have := wInv_aux s (n + 1) (q + 1) (wnext n lv) (wInv_next h)
    simp only [wtableAux]
    rw [show n + (s + 1) = n + 1 + s by omega, show q + (s + 1) = q + 1 + s by omega]
    exact this

private theorem wInv_wtable {r p : Nat} (hp : p < r) : WInv r p (wtable r p) := by
  have := wInv_aux p (r - p) 0 (wlevelBase (r - p)) (wInv_base (by omega))
  rw [show r - p + p = r by omega, Nat.zero_add] at this
  exact this

/-! ### Proof helpers: the indicator sets of a grade -/

/-- The nonzero-color case of `indGradeW`: the rank-`0` part (parity) and the rank-`l ≥ 1`
parts (`repBit`). -/
private theorem testBit_indGrade_nz {r p : Nat} {W : List (List Nat)} (hW : WInv r p W)
    (hp : p < r) {t : Colseq} (ht : ValidTrace r t) (hk : gradeOf t ≠ 0) {c : Color}
    (hc : c = Color2 ∨ c = Color3) :
    (List.foldl (fun acc l => acc |||
        getW W (2 * gradeOf t) (l + 2) *
          repBit (chooseAux r (2 * gradeOf t)) (2 ^ (2 * gradeOf t - 1)) l (c == Color3))
      (getW W (2 * gradeOf t) 1 *
        (if (r % 2 == 0) == (c == Color2) then
          repPar (chooseAux r (2 * gradeOf t)) (2 * gradeOf t - 1)
        else repAll (chooseAux r (2 * gradeOf t)) (2 ^ (2 * gradeOf t - 1)) ^^^
          repPar (chooseAux r (2 * gradeOf t)) (2 * gradeOf t - 1)))
      (List.range (2 * gradeOf t - 1))).testBit (gpos r t) = decide (t.getD p Color0 = c) := by
  have hm := nonOne_eq_two_mul ht
  set k := gradeOf t with hkdef
  set m := 2 * k with hmdef
  have hlen := ht.1
  have h0 := ht.2.1
  have hpl : p < t.length := by omega
  have hmr : m ≤ r := by rw [← hm, ← hlen]; exact nw_nonOne_le t
  set B := chooseAux r m with hBdef
  have hBc : B = r.choose m := chooseAux_eq r m
  have hB : 0 < B := by rw [hBc]; exact Nat.choose_pos hmr
  have hbr : blockRank t m < B := by
    have := nw_blockRank_lt t; rw [hm, hlen] at this; rw [hBc]; exact this
  have hx := nw_xcode_lt t
  rw [hm] at hx
  set xp := xcode t / 2 with hxp
  have hR : xp < 2 ^ (m - 1) := by
    have : 2 ^ m = 2 ^ (m - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
    omega
  have hg : gpos r t = xp * B + blockRank t m := by
    unfold gpos; rw [hm]
  have hWb : ∀ τ, getW W m τ < 2 ^ B := by intro τ; rw [hBc]; exact hW.1 m τ
  have hWt : ∀ τ, (getW W m τ).testBit (blockRank t m) = decide (typeOf t p = τ) := by
    intro τ; have := hW.2 t hlen h0 τ; rw [hm] at this; exact this
  have hτle : typeOf t p ≤ m := by have := typeOf_le t p; omega
  have htp0 : t.getD p Color0 ≠ Color0 := by
    rw [List.getD_eq_getElem _ _ hpl]; intro h; exact h0 (h ▸ List.getElem_mem hpl)
  rw [hg, Bool.eq_iff_iff, testBit_foldl_or, decide_eq_true_iff]
  have hprod : ∀ τ (Y : Nat) (P : Nat → Bool), RowSet B Y P →
      (getW W m τ * Y).testBit (xp * B + blockRank t m) = (P xp && decide (typeOf t p = τ)) := by
    intro τ Y P hY
    rw [testBit_mul_rowSet (hWb τ) hY xp _ hbr, hWt]
  have hbit : ∀ l, l < m - 1 → (getW W m (l + 2) * repBit B (2 ^ (m - 1)) l (c == Color3)).testBit
      (xp * B + blockRank t m) =
        ((decide (xp < 2 ^ (m - 1)) && (xp.testBit l == (c == Color3))) &&
          decide (typeOf t p = l + 2)) := by
    intro l hl
    exact hprod _ _ (fun x => decide (x < 2 ^ (m - 1)) && (x.testBit l == (c == Color3)))
      (rowSet_repBit hB (Nat.pow_dvd_pow 2 (by omega)) _)
  have hpar := rowSet_repPar hB (m - 1)
  have hall := rowSet_repAll hB (2 ^ (m - 1))
  have hpar0 : RowSet B (if (r % 2 == 0) == (c == Color2) then repPar B (m - 1)
      else repAll B (2 ^ (m - 1)) ^^^ repPar B (m - 1))
      (fun x => if (r % 2 == 0) == (c == Color2) then
        (decide (x < 2 ^ (m - 1)) && !par (m - 1) x)
        else (decide (x < 2 ^ (m - 1)) ^^ (decide (x < 2 ^ (m - 1)) && !par (m - 1) x))) := by
    intro x ρ hρ
    split_ifs
    · exact hpar x ρ hρ
    · rw [Nat.testBit_xor, hall x ρ hρ, hpar x ρ hρ]
      cases decide (ρ = 0) <;> simp
  rw [hprod 1 _ _ hpar0]
  -- the type of position `p`
  rcases Nat.lt_trichotomy (typeOf t p) 1 with h | h | h
  · -- `t_p = Color1`
    have h1 : typeOf t p = 0 := by omega
    have htp : t.getD p Color0 = Color1 := (typeOf_eq_zero h0 hpl).1 h1
    rw [htp]
    have hc1 : Color1 ≠ c := by rcases hc with rfl | rfl <;> decide
    simp only [h1, hc1, iff_false, not_or, not_exists, not_and]
    refine ⟨by simp, fun l hl => ?_⟩
    rw [hbit l hl, h1]; simp
  · -- rank `0`: parity
    have hne : ∀ l, l < m - 1 → (getW W m (l + 2) * repBit B (2 ^ (m - 1)) l (c == Color3)).testBit
        (xp * B + blockRank t m) = false := by
      intro l hl; rw [hbit l hl, h]; simp
    have hex : ¬ ∃ l < m - 1, (getW W m (l + 2) * repBit B (2 ^ (m - 1)) l
        (c == Color3)).testBit (xp * B + blockRank t m) = true := by
      rintro ⟨l, hl, h'⟩; rw [hne l hl] at h'; exact absurd h' (by decide)
    simp only [hex, or_false, h, decide_true, Bool.and_true, hR, decide_true]
    have h3 := typeOf_rank h0 hpl (l := 0) h
    have hs := cbit0_sumt h0
    rw [ht.2.2, hm, hlen] at hs
    have hmsucc : m = (m - 1) + 1 := by omega
    rw [hmsucc, par_succ_low, ← hmsucc] at hs
    have hr2 : (r + m) % 2 = r % 2 := by omega
    rw [hr2] at hs
    have hne1 : t.getD p Color0 ≠ Color1 := fun e => by
      have := (typeOf_eq_zero h0 hpl).2 e; omega
    have htp : t.getD p Color0 = Color2 ∨ t.getD p Color0 = Color3 := by
      revert htp0 hne1; cases t.getD p Color0 <;> simp
    simp only [cbit0_Color0] at hs
    rw [← hxp] at hs
    generalize par (m - 1) xp = P at hs ⊢
    generalize (xcode t).testBit 0 = b0 at hs h3
    generalize t.getD p Color0 = d at h3 htp ⊢
    rcases Nat.mod_two_eq_zero_or_one r with hr | hr <;> simp only [hr] at hs ⊢ <;>
      rcases hc with rfl | rfl <;> rcases htp with rfl | rfl <;> cases P <;> cases b0 <;>
      simp at hs h3 ⊢
  · -- rank `l ≥ 1`
    obtain ⟨l0, hl0⟩ : ∃ l0, typeOf t p = l0 + 2 := ⟨typeOf t p - 2, by omega⟩
    have hl0m : l0 < m - 1 := by omega
    have hinit : (decide (typeOf t p = 1)) = false := by simp; omega
    simp only [hinit, Bool.and_false, Bool.false_eq_true, false_or]
    have h3 := typeOf_rank h0 hpl (l := l0 + 1) hl0
    rw [← Nat.testBit_div_two, ← hxp] at h3
    have hne1 : t.getD p Color0 ≠ Color1 := fun e => by
      have := (typeOf_eq_zero h0 hpl).2 e; omega
    have htp : t.getD p Color0 = Color2 ∨ t.getD p Color0 = Color3 := by
      revert htp0 hne1; cases t.getD p Color0 <;> simp
    constructor
    · rintro ⟨l, hl, h'⟩
      rw [hbit l hl, hl0] at h'
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
      obtain ⟨⟨_, hv⟩, hll⟩ := h'
      have : l = l0 := by omega
      subst this
      rcases hc with rfl | rfl <;> rcases htp with e | e <;> rw [e] at h3 ⊢ <;> simp_all
    · intro e
      refine ⟨l0, hl0m, ?_⟩
      rw [hbit l0 hl0m, hl0]
      simp only [hR, decide_true, Bool.true_and, Bool.and_true, beq_iff_eq]
      rcases hc with rfl | rfl <;> rw [e] at h3 <;> simp_all

/-- The indicator of `{t | t_p = c}` in the grade of a valid trace `t`. -/
private theorem testBit_indGrade {r p : Nat} (hp : p < r) {t : Colseq} (ht : ValidTrace r t)
    (c : Color) :
    (indGradeW r (gradeOf t) (wtable r p) c).testBit (gpos r t) =
      decide (t.getD p Color0 = c) := by
  have hW := wInv_wtable hp
  have hpl : p < t.length := by rw [ht.1]; exact hp
  have h0 := ht.2.1
  have htp0 : t.getD p Color0 ≠ Color0 := by
    rw [List.getD_eq_getElem _ _ hpl]; intro h; exact h0 (h ▸ List.getElem_mem hpl)
  by_cases hk : gradeOf t = 0
  · have hm := nonOne_eq_two_mul ht
    rw [hk] at hm
    have h1 : typeOf t p = 0 := by have := typeOf_le t p; omega
    have htp : t.getD p Color0 = Color1 := (typeOf_eq_zero h0 hpl).1 h1
    have hlt := gpos_lt ht
    rw [hk] at hlt ⊢
    have hs : gsize r 0 = 1 - r % 2 := rfl
    rw [hs] at hlt
    have hg : gpos r t = 0 := by omega
    have hr : 1 - r % 2 = 1 := by omega
    rw [hg, htp]
    cases c <;> simp [indGradeW, gsize, hr]
  · have hk' : (gradeOf t == 0) = false := by simpa using hk
    cases c with
    | Color0 =>
      simp only [indGradeW, hk', Bool.false_eq_true, ite_false, Nat.zero_testBit]
      rw [decide_eq_false htp0]
    | Color1 =>
      simp only [indGradeW, hk', Bool.false_eq_true, ite_false]
      have hm := nonOne_eq_two_mul ht
      set m := 2 * gradeOf t
      have hmr : m ≤ r := by rw [← hm, ← ht.1]; exact nw_nonOne_le t
      have hB : 0 < chooseAux r m := by rw [chooseAux_eq]; exact Nat.choose_pos hmr
      have hbr : blockRank t m < chooseAux r m := by
        have := nw_blockRank_lt t; rw [hm, ht.1] at this; rw [chooseAux_eq]; exact this
      have hx := nw_xcode_lt t
      rw [hm] at hx
      have hR : xcode t / 2 < 2 ^ (m - 1) := by
        have : 2 ^ m = 2 ^ (m - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
        omega
      have hg : gpos r t = xcode t / 2 * chooseAux r m + blockRank t m := by
        unfold gpos; rw [hm]
      have hWb : getW (wtable r p) m 0 < 2 ^ chooseAux r m := by
        rw [chooseAux_eq]; exact hW.1 m 0
      rw [hg]
      show (getW (wtable r p) m 0 * _).testBit _ = _
      rw [testBit_mul_rowSet hWb (rowSet_repAll hB _) _ _ hbr]
      have := hW.2 t ht.1 h0 0
      rw [hm] at this
      rw [this]
      simp only [hR, decide_true, Bool.true_and]
      rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff]
      exact typeOf_eq_zero h0 hpl
    | Color2 =>
      simp only [indGradeW, hk', Bool.false_eq_true, ite_false]
      exact testBit_indGrade_nz hW hp ht hk (Or.inl rfl)
    | Color3 =>
      simp only [indGradeW, hk', Bool.false_eq_true, ite_false]
      exact testBit_indGrade_nz hW hp ht hk (Or.inr rfl)

/-! ### Proof helpers: concatenation -/

private theorem nw_goff_mono (r a b : Nat) : goff r a ≤ goff r (a + b) := by
  induction b with
  | zero => exact Nat.le_refl _
  | succ b ih => show goff r a ≤ goff r (a + b) + gsize r (a + b); omega

private theorem testBit_catGAux_high (r : Nat) : ∀ (X : List Nat) (k i : Nat),
    goff r (k + X.length) ≤ i → (catGAux r k (goff r k) X).testBit i = false := by
  intro X
  induction X with
  | nil => intro k i _; simp [catGAux]
  | cons q qs ih =>
    intro k i hi
    simp only [catGAux, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, testBit_ones]
    have e : goff r k + gsize r k = goff r (k + 1) := rfl
    rw [e, ih (k + 1) i (by simpa [Nat.add_assoc, Nat.add_comm 1] using hi)]
    have := nw_goff_mono r (k + 1) qs.length
    have e2 : k + (q :: qs).length = k + 1 + qs.length := by simp; omega
    rw [e2] at hi
    have : ¬ (i - goff r k < gsize r k) := by omega
    simp [this]

private theorem getD_indList {r p k : Nat} (hk : k < ngrades r) (c : Color) :
    ((List.range (ngrades r)).map fun k => indGradeW r k (wtable r p) c).getD k 0 =
      indGradeW r k (wtable r p) c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]
  rfl

/-! ### Proof helpers: transforms and checks -/

private theorem sumt_perm {s u : Colseq} (h : s.Perm u) : sumt s = sumt u := by
  induction h with
  | nil => rfl
  | cons x _ ih => rw [sumt_cons, sumt_cons, ih]
  | swap x y l => rw [sumt_cons, sumt_cons, sumt_cons, sumt_cons, addcA, addcA, addcC x y]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

private theorem map_getD_range (t : Colseq) :
    (List.range t.length).map (fun p => t.getD p Color0) = t := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact List.getD_eq_getElem _ _ h2

private theorem mem_colorsNZ {c : Color} (h : c ≠ Color0) : c ∈ colorsNZ := by
  cases c <;> simp_all [colorsNZ]


/-! ### Specification -/

/-- The indicator sets. -/
theorem testBit_ind {r p : Nat} (hp : p < r) (c : Color) (i : Nat) :
    (ind r p c).testBit i = true ↔ ∃ t, ValidTrace r t ∧ cpos r t = i ∧ t.getD p Color0 = c := by
  have e : ind r p c = catGAux r 0 (goff r 0)
      ((List.range (ngrades r)).map fun k => indGradeW r k (wtable r p) c) := rfl
  constructor
  · intro hbit
    have hi : i < gtotal r := by
      by_contra hc
      rw [e, testBit_catGAux_high r _ 0 i (by simpa [gtotal] using hc)] at hbit
      exact absurd hbit (by decide)
    obtain ⟨t, ht, rfl⟩ := exists_cpos hi
    refine ⟨t, ht, rfl, ?_⟩
    have e2 : ind r p c = catG r
        ((List.range (ngrades r)).map fun k => indGradeW r k (wtable r p) c) := rfl
    rw [e2, testBit_catG ht, getD_indList (gradeOf_lt ht), testBit_indGrade hp ht] at hbit
    simpa using hbit
  · rintro ⟨t, ht, rfl, htp⟩
    have e2 : ind r p c = catG r
        ((List.range (ngrades r)).map fun k => indGradeW r k (wtable r p) c) := rfl
    rw [e2, testBit_catG ht, getD_indList (gradeOf_lt ht), testBit_indGrade hp ht]
    simpa using htp

/-- The separation argument: a network of valid layers that maps, at the position of `t`,
every coordinate indicator set to the right one sends the position of `t` to that of `u`. -/
private theorem netSrc_eq {r : Nat} (hr : 1 ≤ r) {net : Net} (hnet : net.all layerOK = true)
    {t u : Colseq} (hu : ValidTrace r u)
    (h : ∀ p < r, (applyNet net (ind r p (u.getD p Color0))).testBit (cpos r t) = true) :
    netSrc net (cpos r t) = cpos r u := by
  have hs : ∀ p < r, ∃ s, ValidTrace r s ∧ cpos r s = netSrc net (cpos r t) ∧
      s.getD p Color0 = u.getD p Color0 := by
    intro p hp
    have := h p hp
    rw [testBit_applyNet hnet] at this
    exact (testBit_ind hp _ _).1 this
  obtain ⟨s, hsv, hsp, _⟩ := hs 0 hr
  have hsu : s = u := by
    apply List.ext_getElem (by rw [hsv.1, hu.1])
    intro p h1 h2
    have hp : p < r := by rw [← hsv.1]; exact h1
    obtain ⟨s', hs'v, hs'p, hs'c⟩ := hs p hp
    have : s' = s := cpos_inj hs'v hsv (hs'p.trans hsp.symm)
    subst this
    rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at hs'c
    exact hs'c
  rw [← hsp, hsu]

/-- A transform of a valid trace by a permutation of the positions is valid. -/
theorem validTrace_xform {r : Nat} {σ : Nat → Nat} (hσ : ∀ p < r, σ p < r)
    (hσi : ∀ p < r, ∀ q < r, σ p = σ q → p = q) (g : EdgePerm) {t : Colseq}
    (ht : ValidTrace r t) : ValidTrace r (xform r σ g t) := by
  obtain ⟨hlen, h0, hsum⟩ := ht
  have e : xform r σ g t = permt g (((List.range r).map σ).map fun q => t.getD q Color0) := by
    simp [xform, permt, List.map_map]
  have hperm : ((List.range r).map σ).Perm (List.range r) := by
    apply List.Subperm.perm_of_length_le
    · apply List.Nodup.subperm
      · exact List.Nodup.map_on (fun x hx y hy hxy =>
          hσi x (List.mem_range.1 hx) y (List.mem_range.1 hy) hxy) List.nodup_range
      · intro q hq
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
        exact List.mem_range.2 (hσ p (List.mem_range.1 hp))
    · simp
  have hperm2 : (((List.range r).map σ).map fun q => t.getD q Color0).Perm t := by
    have h1 := hperm.map (fun q => t.getD q Color0)
    have h2 : (List.range r).map (fun q => t.getD q Color0) = t := by
      rw [← hlen]; exact map_getD_range t
    rwa [h2] at h1
  rw [e]
  refine ⟨by simp [permt], ?_, ?_⟩
  · rw [memc0_permt]
    intro hm
    exact h0 (hperm2.mem_iff.1 hm)
  · rw [sumt_permt, sumt_perm hperm2, hsum, permc0]

/-- The `r ≥ 1` case of `netSpec_of_xformCheck`. -/
private theorem netSpec_of_xformCheck_pos {r : Nat} (hr : 1 ≤ r) {net : Net} {σ : Nat → Nat}
    {g : EdgePerm} (hσ : ∀ p < r, σ p < r) (hσi : ∀ p < r, ∀ q < r, σ p = σ q → p = q)
    (h : xformCheck r net σ g = true) : NetSpec r net (xform r σ g) := by
  simp only [xformCheck, Bool.and_eq_true] at h
  obtain ⟨hnet, hchk⟩ := h
  simp only [List.all_eq_true, List.mem_range, Nat.beq_eq] at hchk
  intro t ht x
  have hu := validTrace_xform hσ hσi g ht
  rw [testBit_applyNet hnet]
  congr 1
  apply netSrc_eq hr hnet hu
  intro p hp
  have hlen : (xform r σ g t).length = r := hu.1
  have hup : (xform r σ g t).getD p Color0 = permc g (t.getD (σ p) Color0) := by
    simp [xform, List.getD_eq_getElem?_getD, List.getElem?_range hp]
  have hc0 : (xform r σ g t).getD p Color0 ≠ Color0 := by
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hp)]
    intro e; exact hu.2.1 (e ▸ List.getElem_mem _)
  have := congrArg (fun n => n.testBit (cpos r t))
    (hchk p hp _ (mem_colorsNZ hc0))
  simp only [Nat.testBit_and, fullMask, testBit_ones, cpos_lt ht, decide_true,
    Bool.and_true] at this
  show (applyNet net (indW r (wtable r p) _)).testBit _ = true
  rw [this]
  apply (testBit_ind (hσ p hp) _ _).2
  refine ⟨t, ht, rfl, ?_⟩
  rw [hup, inv_permc]

/-- Soundness of `xformCheck`. -/
theorem netSpec_of_xformCheck {r : Nat} {net : Net} {σ : Nat → Nat} {g : EdgePerm}
    (hr : 1 ≤ r) (hσ : ∀ p < r, σ p < r) (hσi : ∀ p < r, ∀ q < r, σ p = σ q → p = q)
    (h : xformCheck r net σ g = true) : NetSpec r net (xform r σ g) :=
  -- `1 ≤ r` is needed: `xformCheck 0 [(1, 1)] id Eperm123 = true`, but
  -- `NetSpec 0 [(1, 1)] (xform 0 id Eperm123)` fails at `t = []`, `x = 2` (no position
  -- `p < 0` pins the image of `cpos 0 [] = 0`).
  netSpec_of_xformCheck_pos hr hσ hσi h

/-- `tauCheck` is `xformCheck` for the identity and `Eperm213`. -/
private theorem xformCheck_of_tauCheck {r : Nat} {net : Net} (h : tauCheck r net = true) :
    xformCheck r net id Eperm213 = true := by
  simp only [tauCheck, Bool.and_eq_true] at h
  obtain ⟨hnet, hchk⟩ := h
  simp only [List.all_eq_true, List.mem_range] at hchk
  simp only [xformCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, hnet, true_and]
  intro p hp c hc
  have := hchk p hp
  simp only [Bool.and_eq_true] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  simp only [colorsNZ, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact h1
  · exact h2
  · exact h3

/-- The `r ≥ 1` case of `tauSpec_of_check`. -/
private theorem tauSpec_of_check_pos {r : Nat} (hr : 1 ≤ r) {net : Net}
    (h : tauCheck r net = true) : TauSpec r net := by
  have hx := netSpec_of_xformCheck_pos hr (fun p hp => hp) (fun p _ q _ e => e)
    (xformCheck_of_tauCheck h)
  intro t ht x
  have e : xform r (fun p => p) Eperm213 t = permt Eperm213 t := by
    have h2 := map_getD_range t
    rw [ht.1] at h2
    conv_rhs => rw [← h2]
    simp only [xform, permt, List.map_map]; rfl
  rw [hx t ht x, e]

/-- Soundness of `tauCheck`. -/
theorem tauSpec_of_check {r : Nat} {net : Net} (hr : 1 ≤ r) (h : tauCheck r net = true) :
    TauSpec r net :=
  -- `1 ≤ r` is needed: `tauCheck 0 [(1, 1)] = true`, but `TauSpec 0 [(1, 1)]` fails at
  -- `t = []`, `x = 2`.
  tauSpec_of_check_pos hr h

/-- The base-3 index is determined by its digits. -/
private theorem eq_b3idx : ∀ (s : Colseq) (j : Nat), j < 3 ^ s.length →
    (∀ p < s.length, j / 3 ^ p % 3 = cdig (s.getD p Color0)) → j = b3idx s
  | [], j, hj, _ => by simp at hj; simp [hj, b3idx]
  | c :: s, j, hj, hd => by
    have h0 := hd 0 (by simp)
    simp only [Nat.pow_zero, Nat.div_one, List.getD_cons_zero] at h0
    have ih := eq_b3idx s (j / 3) (by
        simp only [List.length_cons, Nat.pow_succ] at hj
        omega) (by
        intro p hp
        have := hd (p + 1) (by simp; omega)
        rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul, List.getD_cons_succ] at this
        exact this)
    simp only [b3idx]
    omega

/-- Soundness of `cnvCheck`. -/
theorem cnvSpec_of_check {r : Nat} {net : Net} (hr : 2 ≤ r) (h : cnvCheck r net = true) :
    CnvSpec r net := by
  simp only [cnvCheck, Bool.and_eq_true] at h
  obtain ⟨hnet, hchk⟩ := h
  simp only [List.all_eq_true, List.mem_range, Nat.beq_eq] at hchk
  intro t ht x
  rw [testBit_applyNet hnet]
  congr 1
  set j := netSrc net (cpos r t)
  have hd : ∀ p < r - 1, j < 3 ^ (r - 1) ∧ j / 3 ^ p % 3 = cdig (t.getD p Color0) := by
    intro p hp
    have hpl : p < t.length := by rw [ht.1]; omega
    have hc0 : t.getD p Color0 ≠ Color0 := by
      rw [List.getD_eq_getElem _ _ hpl]
      intro e; exact ht.2.1 (e ▸ List.getElem_mem _)
    have := congrArg (fun n => n.testBit (cpos r t)) (hchk p hp _ (mem_colorsNZ hc0))
    simp only [Nat.testBit_and, fullMask, testBit_ones, cpos_lt ht, decide_true,
      Bool.and_true] at this
    have h2 : (indW r (wtable r p) (t.getD p Color0)).testBit (cpos r t) = true :=
      (testBit_ind (by omega) _ _).2 ⟨t, ht, rfl, rfl⟩
    rw [← this, testBit_applyNet hnet] at h2
    have hv : cdig (t.getD p Color0) ≤ 2 := by cases t.getD p Color0 <;> decide
    unfold b3ind at h2
    rw [testBit_digitMask hp hv] at h2
    simpa using h2
  have htake : (t.take (r - 1)).length = r - 1 := by simp [ht.1]
  apply eq_b3idx
  · rw [htake]; exact (hd 0 (by omega)).1
  · intro p hp
    rw [htake] at hp
    have e1 : (t.take (r - 1)).getD p Color0 = t.getD p Color0 := by
      simp [List.getD_eq_getElem?_getD, hp]
    rw [e1]; exact (hd p hp).2

end FourColor.Engine
