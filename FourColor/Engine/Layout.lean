/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Bits
import FourColor.Color

/-!
# Reducibility engine, layer 1: the packed graded layout of trace sets

A *valid trace* of ring size `r` is a sequence `t : Colseq` of length `r` over
`Color1, Color2, Color3` with `sumt t = Color0` (`ValidTrace r t`); every ring trace of a
coloring is valid.  Sets of valid traces are stored as big numbers in the **packed graded
layout** (called `P1`):

* the *grade* of `t` is `k = m / 2`, where `m = nonOne t` is the number of non-`Color1`
  entries (always even for a valid trace); grade `k` is stored in its own `Nat`, and a trace
  set is a `List Nat` indexed by grades `0 … r / 2` (`ngrades r`);
* inside grade `k ≥ 1` (`m = 2k`), a trace is determined by its *block* `N` (the set of its
  non-`Color1` positions, one of `B = choose r m` blocks) and by the colors of the entries of
  `N` of *rank* `1 … m-1` (rank `l` = the `l`-th element of `N`, from the head of the list);
  the color of the rank-`0` entry is then determined by `sumt t = Color0` ("parity packing").
  The packed code is `xp = xcode t / 2` (bit `l-1` of `xp` set iff rank `l` is `Color3`),
  and the position of `t` is `gpos r t = xp * B + blockRank t m` ("row-major": rows indexed
  by `xp`, of `B` bits each);
* blocks are ranked in lexicographic order of their membership vector read from the head,
  blocks without the head position first (`blockRank`);
* grade `0` holds only the all-`Color1` trace, valid iff `r` is even: `gsize r 0 = 1 - r % 2`;
  grade `k ≥ 1` has `gsize r k = choose r (2k) * 2^(2k-1)` bits.  Every position below
  `gsize r k` is the position of exactly one valid trace of grade `k`.

The concatenation of the grades (grade `0` lowest, `goff r k` = offset of grade `k`) is used
for the fixed bit permutations (delta-swap networks): `catG`, `splitG`, `cpos r t`.

The semantics of a trace-set representation `X : List Nat` is `den r X`; that of a
concatenated one `x : Nat` is `denCat r x`.

The layout was chosen so that
1. a Kempe chord flip of the ranks `a < b` is the same masked shift for every block of a
   grade (`xp ↦ xp xor 2^(a-1) xor 2^(b-1)`, or `xp xor 2^(b-1)` when `a = 0`);
2. the color transposition `Color2 ↔ Color3` complements `xp` (cheap);
3. the `Color2 ↔ Color3` symmetric halves of a grade are its low and high halves (rows
   `xp < 2^(m-2)` and above), which halves the checkpoints;
4. the indicator sets `{t | t_p = c}` have a simple recursive structure (`Network.lean`).
-/

namespace FourColor.Engine

open FourColor

/-! ### Sizes and offsets -/

/-- The number of grades for ring size `r`: grades `0 … r / 2`. -/
def ngrades (r : Nat) : Nat := r / 2 + 1

/-- The number of bits of grade `k` for ring size `r`: `1 - r % 2` for `k = 0` (the
all-`Color1` trace, valid iff `r` is even), `choose r (2k) * 2^(2k-1)` otherwise. -/
def gsize (r k : Nat) : Nat :=
  if k == 0 then 1 - r % 2 else chooseAux r (2 * k) * 2 ^ (2 * k - 1)

/-- The offset of grade `k` in the concatenated layout. -/
def goff (r : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => goff r k + gsize r k

/-- The total size of the concatenated layout: the number of valid traces of size `r`,
`(3^r + 3 (-1)^r) / 4`. -/
def gtotal (r : Nat) : Nat := goff r (ngrades r)

/-- All the positions of the concatenated layout (`2 ^ gtotal r - 1`, built by a shift). -/
def fullMask (r : Nat) : Nat := ones (gtotal r)

/-! ### Concatenation and splitting of grades -/

/-- Concatenate grades `k, k+1, …` at offset `off` (each grade is truncated to its size). -/
def catGAux (r : Nat) : Nat → Nat → List Nat → Nat
  | _, _, [] => 0
  | k, off, q :: qs =>
    ((q &&& ones (gsize r k)) <<< off) ||| catGAux r (k + 1) (off + gsize r k) qs

/-- The concatenated layout of a list of grades. -/
def catG (r : Nat) (X : List Nat) : Nat := catGAux r 0 0 X

/-- Split `n` grades, starting at grade `k`, off a concatenated layout. -/
def splitGAux (r : Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | n + 1, k, x => (x &&& ones (gsize r k)) :: splitGAux r n (k + 1) (x >>> gsize r k)

/-- The grades of a concatenated layout. -/
def splitG (r x : Nat) : List Nat := splitGAux r (ngrades r) 0 x

/-- Map a function of the grade index over a list of grades, starting at index `k`. -/
def mapGradesAux (f : Nat → Nat → Nat) : Nat → List Nat → List Nat
  | _, [] => []
  | k, q :: qs => f k q :: mapGradesAux f (k + 1) qs

/-- Map a function of the grade index over a list of grades. -/
def mapGrades (f : Nat → Nat → Nat) (X : List Nat) : List Nat := mapGradesAux f 0 X

/-! ### Traces and their positions -/

/-- A valid trace of ring size `r`: `r` colors among `Color1`, `Color2`, `Color3`, with sum
`Color0`.  Ring traces of colorings are valid. -/
def ValidTrace (r : Nat) (t : Colseq) : Prop :=
  t.length = r ∧ Color0 ∉ t ∧ sumt t = Color0

/-- The number of non-`Color1` entries of `t`. -/
def nonOne (t : Colseq) : Nat := t.countP (fun c => c != Color1)

/-- The grade of `t`: half its number of non-`Color1` entries. -/
def gradeOf (t : Colseq) : Nat := nonOne t / 2

/-- The rank of the block of `t` (its set of non-`Color1` positions, of size `m`) among the
`m`-subsets of positions, in lexicographic order of membership vectors read from the head,
blocks not containing the head first. -/
def blockRank : Colseq → Nat → Nat
  | [], _ => 0
  | c :: t, m =>
    match c with
    | Color1 => blockRank t m
    | _ => chooseAux t.length m + blockRank t (m - 1)

/-- The unpacked code of `t` inside its block: bit `l` is set iff the rank-`l`
non-`Color1` entry of `t` is `Color3`. -/
def xcode : Colseq → Nat
  | [] => 0
  | Color1 :: t => xcode t
  | Color3 :: t => 2 * xcode t + 1
  | _ :: t => 2 * xcode t

/-- The position of `t` inside its grade: row `xcode t / 2` (the rank-`0` color is dropped:
it is determined by `sumt t = Color0`), column `blockRank t m`, rows of `choose r m` bits. -/
def gpos (r : Nat) (t : Colseq) : Nat :=
  xcode t / 2 * chooseAux r (nonOne t) + blockRank t (nonOne t)

/-- The position of `t` in the concatenated layout. -/
def cpos (r : Nat) (t : Colseq) : Nat := goff r (gradeOf t) + gpos r t

/-- The set of valid traces represented by a list of grades. -/
def den (r : Nat) (X : List Nat) (t : Colseq) : Prop :=
  ValidTrace r t ∧ (X.getD (gradeOf t) 0).testBit (gpos r t) = true

/-- The set of valid traces represented by a concatenated layout. -/
def denCat (r : Nat) (x : Nat) (t : Colseq) : Prop :=
  ValidTrace r t ∧ x.testBit (cpos r t) = true

/-! ### The base-3 layout (used by the coloring DP)

A sequence `t` over `Color1, Color2, Color3` is also stored at the base-3 index
`b3idx t = ∑_p cdig t_p * 3^p` (head = least significant digit, `cdig Colori = i - 1`). -/

/-- The base-3 digit of a nonzero color: `Color1 ↦ 0`, `Color2 ↦ 1`, `Color3 ↦ 2`. -/
def cdig (c : Color) : Nat :=
  match c with
  | Color2 => 1
  | Color3 => 2
  | _ => 0

/-- The base-3 index of a sequence of nonzero colors (head = least significant digit). -/
def b3idx : Colseq → Nat
  | [] => 0
  | c :: t => cdig c + 3 * b3idx t

/-- The bits `i < 3^n` whose base-3 digit `p` is `v` (for `p < n`, `v ≤ 2`). -/
def digitMask (n p v : Nat) : Nat := pmask (3 ^ n) (3 ^ (p + 1)) (3 ^ p) <<< (v * 3 ^ p)

/-- The arithmetic behind `testBit_digitMask` (with `P = 3^p` and `3^n = 3P * Q`): the index
`i` is `v * P` plus an index whose residue modulo `3P` is below `P` iff the digit of `i` of
weight `P` is `v`. -/
private theorem digit_arith {P Q v i : Nat} (hP : 0 < P) (hv : v ≤ 2) :
    (decide (i ≥ v * P) && (decide (i - v * P < P * 3 * Q) &&
      decide ((i - v * P) % (P * 3) < P))) =
    (decide (i < P * 3 * Q) && decide (i / P % 3 = v)) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hi, hlt, hmod⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
    have e1 : v * P + j - v * P = j := by omega
    rw [e1] at hlt hmod
    have hj := Nat.div_add_mod j (P * 3)
    have hq : j / (P * 3) < Q := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; rwa [Nat.mul_comm]
    have h2 : P * 3 * (j / (P * 3) + 1) ≤ P * 3 * Q := Nat.mul_le_mul_left _ hq
    have h3 : v * P ≤ 2 * P := Nat.mul_le_mul_right _ hv
    rw [Nat.mul_add, Nat.mul_one] at h2
    refine ⟨by omega, ?_⟩
    have e2 : v * P + j = P * (3 * (j / (P * 3)) + v) + j % (P * 3) := by
      rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm P v]; omega
    rw [e2, Nat.mul_add_div hP, Nat.div_eq_of_lt hmod]
    omega
  · rintro ⟨hlt, hd⟩
    have h1 := Nat.div_add_mod i P
    have h2 := Nat.div_add_mod (i / P) 3
    rw [hd] at h2
    have hm : i % P < P := Nat.mod_lt _ hP
    have e : i = P * 3 * (i / P / 3) + v * P + i % P := by
      have : P * (3 * (i / P / 3) + v) = P * 3 * (i / P / 3) + v * P := by
        rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm P v]
      rw [← h2] at h1; omega
    refine ⟨by omega, by omega, ?_⟩
    have e' : i - v * P = P * 3 * (i / P / 3) + i % P := by omega
    rw [e', Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    exact hm

/-- Characterisation of `digitMask`. -/
theorem testBit_digitMask {n p v : Nat} (hp : p < n) (hv : v ≤ 2) (i : Nat) :
    (digitMask n p v).testBit i = (decide (i < 3 ^ n) && decide (i / 3 ^ p % 3 = v)) := by
  have hP : 0 < 3 ^ p := Nat.pow_pos (by norm_num)
  have hP3 : 3 ^ (p + 1) = 3 ^ p * 3 := by rw [Nat.pow_succ]
  have hdvd : 3 ^ (p + 1) ∣ 3 ^ n := Nat.pow_dvd_pow 3 hp
  have hw : 3 ^ p ≤ 3 ^ (p + 1) := Nat.pow_le_pow_right (by norm_num) (Nat.le_succ p)
  unfold digitMask
  rw [Nat.testBit_shiftLeft, testBit_pmask (by omega) hdvd hw]
  obtain ⟨Q, hQ⟩ := hdvd
  rw [hQ, hP3]
  exact digit_arith hP hv

/-! ### Specification of the layout -/

/-- The parity of the number of non-`Color1` entries is the high bit of the sum. -/
theorem cbit1_sumt_nonOne {t : Colseq} (h0 : Color0 ∉ t) :
    cbit1 (sumt t) = decide (nonOne t % 2 = 1) := by
  induction t with
  | nil => rfl
  | cons c t ih =>
    simp only [List.mem_cons, not_or] at h0
    have ih := ih h0.2
    have e : nonOne (c :: t) = nonOne t + (if c = Color1 then 0 else 1) := by
      simp only [nonOne, List.countP_cons]
      cases c <;> simp
    rw [sumt_cons, cbit1_addc, ih, e]
    cases c with
    | Color0 => exact absurd rfl h0.1
    | Color1 => simp
    | Color2 => rcases Nat.mod_two_eq_zero_or_one (nonOne t) with h | h <;> simp [h, Nat.add_mod]
    | Color3 => rcases Nat.mod_two_eq_zero_or_one (nonOne t) with h | h <;> simp [h, Nat.add_mod]

/-- A valid trace has an even number of non-`Color1` entries. -/
theorem nonOne_eq_two_mul {r : Nat} {t : Colseq} (h : ValidTrace r t) :
    nonOne t = 2 * gradeOf t := by
  have := cbit1_sumt_nonOne h.2.1
  rw [h.2.2] at this
  simp at this
  unfold gradeOf; omega

/-- The grade of a valid trace is a grade of the layout. -/
theorem gradeOf_lt {r : Nat} {t : Colseq} (h : ValidTrace r t) : gradeOf t < ngrades r := by
  have h1 : nonOne t ≤ t.length := List.countP_le_length
  unfold gradeOf ngrades; rw [h.1] at h1; omega

/-! ### Helpers: block ranks, codes and the decoding of positions -/

private theorem nonOne_nil : nonOne [] = 0 := rfl

private theorem nonOne_cons (c : Color) (t : Colseq) :
    nonOne (c :: t) = nonOne t + (if c = Color1 then 0 else 1) := by
  simp only [nonOne, List.countP_cons]
  cases c <;> simp

private theorem nonOne_cons1 (t : Colseq) : nonOne (Color1 :: t) = nonOne t := by
  rw [nonOne_cons]; simp

private theorem nonOne_cons_ne {c : Color} (hc : c ≠ Color1) (t : Colseq) :
    nonOne (c :: t) = nonOne t + 1 := by
  rw [nonOne_cons, ite_eq_right hc]

private theorem blockRank_cons_ne {c : Color} (hc : c ≠ Color1) (t : Colseq) (m : Nat) :
    blockRank (c :: t) m = t.length.choose m + blockRank t (m - 1) := by
  cases c
  · simp [blockRank, chooseAux_eq]
  · exact absurd rfl hc
  · simp [blockRank, chooseAux_eq]
  · simp [blockRank, chooseAux_eq]

private theorem blockRank_lt (t : Colseq) :
    blockRank t (nonOne t) < t.length.choose (nonOne t) := by
  induction t with
  | nil => simp [blockRank, nonOne_nil]
  | cons c t ih =>
    by_cases hc : c = Color1
    · subst hc
      rw [nonOne_cons1]
      simp only [blockRank, List.length_cons]
      exact Nat.lt_of_lt_of_le ih (Nat.choose_le_succ _ _)
    · rw [nonOne_cons_ne hc, blockRank_cons_ne hc, List.length_cons, Nat.choose_succ_succ',
        Nat.add_sub_cancel]
      omega

private theorem xcode_lt (t : Colseq) : xcode t < 2 ^ nonOne t := by
  induction t with
  | nil => simp [xcode, nonOne_nil]
  | cons c t ih =>
    cases c
    · rw [nonOne_cons_ne (by decide), Nat.pow_succ]; simp only [xcode]; omega
    · rw [nonOne_cons1]; exact ih
    · rw [nonOne_cons_ne (by decide), Nat.pow_succ]; simp only [xcode]; omega
    · rw [nonOne_cons_ne (by decide), Nat.pow_succ]; simp only [xcode]; omega

/-- Decoding a block rank and an unpacked code into a trace. -/
private def dec : Nat → Nat → Nat → Nat → Colseq
  | 0, _, _, _ => []
  | n + 1, m, b, x =>
    if b < n.choose m then Color1 :: dec n m b x
    else (if x % 2 = 1 then Color3 else Color2) :: dec n (m - 1) (b - n.choose m) (x / 2)

private theorem dec_eq {t : Colseq} (h0 : Color0 ∉ t) :
    dec t.length (nonOne t) (blockRank t (nonOne t)) (xcode t) = t := by
  induction t with
  | nil => rfl
  | cons c t ih =>
    simp only [List.mem_cons, not_or] at h0
    have ih := ih h0.2
    by_cases hc : c = Color1
    · subst hc
      rw [nonOne_cons1]
      simp only [List.length_cons, dec, blockRank, xcode, ite_eq_left (blockRank_lt t), ih]
    · rw [nonOne_cons_ne hc, blockRank_cons_ne hc, List.length_cons]
      simp only [dec, Nat.add_sub_cancel]
      rw [ite_eq_right (by omega), Nat.add_sub_cancel_left]
      cases c
      · exact absurd rfl h0.1
      · exact absurd rfl hc
      · simp only [xcode]
        have e1 : 2 * xcode t % 2 = 0 := by omega
        have e2 : 2 * xcode t / 2 = xcode t := by omega
        rw [e2, ih]; simp [e1]
      · simp only [xcode]
        have e1 : (2 * xcode t + 1) % 2 = 1 := by omega
        have e2 : (2 * xcode t + 1) / 2 = xcode t := by omega
        rw [e2, ih]; simp [e1]

private theorem dec_spec (n : Nat) : ∀ {m b x : Nat}, b < n.choose m → x < 2 ^ m →
    (dec n m b x).length = n ∧ Color0 ∉ dec n m b x ∧ nonOne (dec n m b x) = m ∧
      blockRank (dec n m b x) m = b ∧ xcode (dec n m b x) = x := by
  induction n with
  | zero =>
    intro m b x hb hx
    cases m with
    | zero =>
      have : b = 0 := by simpa using hb
      have : x = 0 := by simpa using hx
      subst_vars
      simp [dec, nonOne_nil, blockRank, xcode]
    | succ m => simp at hb
  | succ n ih =>
    intro m b x hb hx
    simp only [dec]
    split_ifs with h1 h2
    · obtain ⟨e1, e2, e3, e4, e5⟩ := ih h1 hx
      refine ⟨by simp [e1], by simp [e2], by rw [nonOne_cons1, e3], by simp [blockRank, e4],
        by simp [xcode, e5]⟩
    · cases m with
      | zero => exfalso; rw [Nat.choose_zero_right] at hb h1; omega
      | succ m =>
        rw [Nat.choose_succ_succ'] at hb
        rw [Nat.pow_succ] at hx
        have hb' : b - n.choose (m + 1) < n.choose m := by omega
        have hx' : x / 2 < 2 ^ m := by omega
        obtain ⟨e1, e2, e3, e4, e5⟩ := ih hb' hx'
        simp only [Nat.add_sub_cancel] at e1 e2 e3 e4 e5 ⊢
        refine ⟨by simp [e1], by simp [e2], ?_, ?_, ?_⟩
        · rw [nonOne_cons_ne (by decide), e3]
        · rw [blockRank_cons_ne (by decide), e1, Nat.add_sub_cancel, e4]; omega
        · simp only [xcode, e5]; omega
    · cases m with
      | zero => exfalso; rw [Nat.choose_zero_right] at hb h1; omega
      | succ m =>
        rw [Nat.choose_succ_succ'] at hb
        rw [Nat.pow_succ] at hx
        have hb' : b - n.choose (m + 1) < n.choose m := by omega
        have hx' : x / 2 < 2 ^ m := by omega
        obtain ⟨e1, e2, e3, e4, e5⟩ := ih hb' hx'
        simp only [Nat.add_sub_cancel] at e1 e2 e3 e4 e5 ⊢
        refine ⟨by simp [e1], by simp [e2], ?_, ?_, ?_⟩
        · rw [nonOne_cons_ne (by decide), e3]
        · rw [blockRank_cons_ne (by decide), e1, Nat.add_sub_cancel, e4]; omega
        · simp only [xcode, e5]; omega

private theorem dec_flip (n : Nat) : ∀ {m b : Nat} (q : Nat), b < n.choose m → 1 ≤ m →
    sumt (dec n m b (2 * q + 1)) = addc Color1 (sumt (dec n m b (2 * q))) := by
  induction n with
  | zero => intro m b q hb hm; cases m with
    | zero => omega
    | succ m => simp at hb
  | succ n ih =>
    intro m b q hb hm
    simp only [dec]
    by_cases h1 : b < n.choose m
    · rw [ite_eq_left h1, ite_eq_left h1, sumt_cons, sumt_cons, ih q h1 hm, addcA, addcC Color1 Color1,
        ← addcA]
    · rw [ite_eq_right h1, ite_eq_right h1]
      have e1 : (2 * q + 1) % 2 = 1 := by omega
      have e2 : (2 * q + 1) / 2 = q := by omega
      have e3 : 2 * q % 2 = 0 := by omega
      have e4 : 2 * q / 2 = q := by omega
      rw [e1, e2, e3, e4]
      simp only [sumt_cons, addcA]
      rfl

private theorem sumt_ones {t : Colseq} (h0 : Color0 ∉ t) (h : nonOne t = 0) :
    sumt t = if t.length % 2 = 0 then Color0 else Color1 := by
  induction t with
  | nil => rfl
  | cons c t ih =>
    simp only [List.mem_cons, not_or] at h0
    by_cases hc : c = Color1
    · subst hc
      rw [nonOne_cons1] at h
      rw [sumt_cons, ih h0.2 h, List.length_cons]
      rcases Nat.mod_two_eq_zero_or_one t.length with e | e
      · have : (t.length + 1) % 2 = 1 := by omega
        simp [e, this]
      · have : (t.length + 1) % 2 = 0 := by omega
        simp [e, this]
    · rw [nonOne_cons_ne hc] at h; omega

private theorem cbit1_false {c : Color} (h : cbit1 c = false) : c = Color0 ∨ c = Color1 := by
  cases c <;> simp_all

private theorem goff_mono (r a b : Nat) : goff r a ≤ goff r (a + b) := by
  induction b with
  | zero => exact Nat.le_refl _
  | succ b ih => show goff r a ≤ goff r (a + b) + gsize r (a + b); omega

private theorem goff_le {r a b : Nat} (h : a ≤ b) : goff r a ≤ goff r b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h; exact goff_mono r a c

/-- The block and row decomposition of `gpos`. -/
private theorem gpos_parts {r : Nat} {t : Colseq} (h : ValidTrace r t) :
    blockRank t (nonOne t) < chooseAux r (nonOne t) ∧ xcode t < 2 ^ nonOne t := by
  refine ⟨?_, xcode_lt t⟩
  rw [chooseAux_eq, ← h.1]; exact blockRank_lt t

/-- The position of a valid trace is inside its grade. -/
theorem gpos_lt {r : Nat} {t : Colseq} (h : ValidTrace r t) : gpos r t < gsize r (gradeOf t) := by
  have hm := nonOne_eq_two_mul h
  obtain ⟨hb, hx⟩ := gpos_parts h
  unfold gpos gsize
  by_cases hk : gradeOf t = 0
  · rw [hk] at hm ⊢
    rw [hm] at hb hx ⊢
    have hx0 : xcode t = 0 := by simpa using hx
    have hb0 : blockRank t 0 = 0 := by simpa [chooseAux] using hb
    have hs := sumt_ones h.2.1 (by omega)
    rw [h.2.2, h.1] at hs
    have hr : r % 2 = 0 := by
      by_contra hr; rw [ite_eq_right hr] at hs; exact absurd hs (by decide)
    simp [hx0, hb0, hr]
  · have hk' : (gradeOf t == 0) = false := by simpa using hk
    rw [hk', ite_eq_right (by decide)]
    rw [hm] at hb hx ⊢
    have hq : xcode t / 2 < 2 ^ (2 * gradeOf t - 1) := by
      have : 2 ^ (2 * gradeOf t) = 2 ^ (2 * gradeOf t - 1) * 2 := by
        rw [← Nat.pow_succ]; congr 1; omega
      omega
    have := Nat.mul_le_mul_right (chooseAux r (2 * gradeOf t)) (Nat.succ_le_of_lt hq)
    rw [Nat.succ_mul, Nat.mul_comm (2 ^ _)] at this
    omega

/-- The position of a valid trace in the concatenated layout. -/
theorem cpos_lt {r : Nat} {t : Colseq} (h : ValidTrace r t) : cpos r t < gtotal r := by
  have h1 := gpos_lt h
  have h2 : goff r (gradeOf t + 1) ≤ goff r (ngrades r) := goff_le (gradeOf_lt h)
  unfold cpos gtotal
  show _ < goff r (ngrades r)
  have : goff r (gradeOf t + 1) = goff r (gradeOf t) + gsize r (gradeOf t) := rfl
  omega

private theorem gradeOf_eq_of_cpos {r : Nat} {s t : Colseq} (hs : ValidTrace r s)
    (ht : ValidTrace r t) (h : cpos r s = cpos r t) : gradeOf s = gradeOf t := by
  have h1 := gpos_lt hs
  have h2 := gpos_lt ht
  unfold cpos at h
  rcases Nat.lt_trichotomy (gradeOf s) (gradeOf t) with c | c | c
  · have := goff_le (r := r) (show _ + 1 ≤ _ from c)
    have e : goff r (gradeOf s + 1) = goff r (gradeOf s) + gsize r (gradeOf s) := rfl
    omega
  · exact c
  · have := goff_le (r := r) (show _ + 1 ≤ _ from c)
    have e : goff r (gradeOf t + 1) = goff r (gradeOf t) + gsize r (gradeOf t) := rfl
    omega

private theorem mul_add_inj {B q1 q2 b1 b2 : Nat} (h1 : b1 < B) (h2 : b2 < B)
    (h : q1 * B + b1 = q2 * B + b2) : q1 = q2 ∧ b1 = b2 := by
  have hB : 0 < B := by omega
  have e1 : (q1 * B + b1) / B = q1 := by
    rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt h1, Nat.add_zero]
  have e2 : (q2 * B + b2) / B = q2 := by
    rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt h2, Nat.add_zero]
  have hq : q1 = q2 := by rw [← e1, ← e2, h]
  subst hq
  exact ⟨rfl, by omega⟩

/-- Different valid traces have different positions. -/
theorem cpos_inj {r : Nat} {s t : Colseq} (hs : ValidTrace r s) (ht : ValidTrace r t)
    (h : cpos r s = cpos r t) : s = t := by
  have hg := gradeOf_eq_of_cpos hs ht h
  have hm : nonOne s = nonOne t := by rw [nonOne_eq_two_mul hs, nonOne_eq_two_mul ht, hg]
  have hp : gpos r s = gpos r t := by unfold cpos at h; rw [hg] at h; omega
  obtain ⟨hbs, hxs⟩ := gpos_parts hs
  obtain ⟨hbt, hxt⟩ := gpos_parts ht
  unfold gpos at hp
  rw [hm] at hp hbs hxs
  obtain ⟨hq, hb⟩ := mul_add_inj hbs hbt hp
  have hl : s.length = t.length := by rw [hs.1, ht.1]
  have ds := dec_eq hs.2.1
  have dt := dec_eq ht.2.1
  rw [hl, hm, hb] at ds
  -- the codes agree up to their low bit, which is fixed by `sumt = Color0`
  have hbnd : blockRank t (nonOne t) < t.length.choose (nonOne t) := blockRank_lt t
  rcases Nat.mod_two_eq_zero_or_one (xcode s) with a | a <;>
    rcases Nat.mod_two_eq_zero_or_one (xcode t) with a' | a'
  · have : xcode s = xcode t := by omega
    rw [this] at ds; exact ds.symm.trans dt
  · exfalso
    have m1 : 1 ≤ nonOne t := by
      by_contra z
      have z' : nonOne t = 0 := by omega
      rw [z', Nat.pow_zero] at hxs hxt
      omega
    have ex : xcode s = 2 * (xcode t / 2) := by omega
    have ey : xcode t = 2 * (xcode t / 2) + 1 := by omega
    have hf := dec_flip t.length (xcode t / 2) hbnd m1
    rw [← ey, dt, ← ex, ds, hs.2.2, ht.2.2] at hf
    exact absurd hf (by decide)
  · exfalso
    have m1 : 1 ≤ nonOne t := by
      by_contra z
      have z' : nonOne t = 0 := by omega
      rw [z', Nat.pow_zero] at hxs hxt
      omega
    have ex : xcode s = 2 * (xcode t / 2) + 1 := by omega
    have ey : xcode t = 2 * (xcode t / 2) := by omega
    have hf := dec_flip t.length (xcode t / 2) hbnd m1
    rw [← ex, ds, ← ey, dt, hs.2.2, ht.2.2] at hf
    exact absurd hf (by decide)
  · have : xcode s = xcode t := by omega
    rw [this] at ds; exact ds.symm.trans dt

private theorem exists_grade {r i : Nat} : ∀ n, i < goff r n →
    ∃ k, k < n ∧ goff r k ≤ i ∧ i < goff r k + gsize r k := by
  intro n
  induction n with
  | zero => intro hi; exact absurd hi (Nat.not_lt_zero _)
  | succ n ih =>
    intro hi
    by_cases h : i < goff r n
    · obtain ⟨k, hk, h1, h2⟩ := ih h
      exact ⟨k, by omega, h1, h2⟩
    · exact ⟨n, by omega, by omega, hi⟩

/-- Every position of the concatenated layout is the position of a valid trace (used by the
Birkhoff check to name the picked trace). -/
theorem exists_cpos {r i : Nat} (hi : i < gtotal r) : ∃ t, ValidTrace r t ∧ cpos r t = i := by
  obtain ⟨k, hk, h1, h2⟩ := exists_grade (ngrades r) hi
  by_cases hk0 : k = 0
  · subst hk0
    have hs : gsize r 0 = 1 - r % 2 := rfl
    have hg0 : goff r 0 = 0 := rfl
    have hr : r % 2 = 0 := by omega
    have hi0 : i = 0 := by omega
    obtain ⟨e1, e2, e3, e4, e5⟩ := dec_spec r (m := 0) (b := 0) (x := 0) (by simp) (by simp)
    refine ⟨dec r 0 0 0, ⟨e1, e2, ?_⟩, ?_⟩
    · rw [sumt_ones e2 e3, e1, ite_eq_left hr]
    · have hg : gradeOf (dec r 0 0 0) = 0 := by unfold gradeOf; rw [e3]
      unfold cpos gpos; rw [hg, e3, e4, e5, hi0]; rfl
  · have hs : gsize r k = chooseAux r (2 * k) * 2 ^ (2 * k - 1) := by
      unfold gsize; rw [ite_eq_right (by simpa using hk0)]
    set B := chooseAux r (2 * k) with hBdef
    set j := i - goff r k with hj
    have hjl : j < B * 2 ^ (2 * k - 1) := by omega
    have hB : 0 < B := by
      rcases Nat.eq_zero_or_pos B with z | z
      · rw [z, Nat.zero_mul] at hjl; omega
      · exact z
    have hb : j % B < r.choose (2 * k) := by rw [← chooseAux_eq]; exact Nat.mod_lt _ hB
    have hq : j / B < 2 ^ (2 * k - 1) := by
      rw [Nat.div_lt_iff_lt_mul hB]; rwa [Nat.mul_comm]
    have hpow : 2 ^ (2 * k) = 2 ^ (2 * k - 1) * 2 := by
      rw [← Nat.pow_succ]; congr 1; omega
    have hx0 : 2 * (j / B) < 2 ^ (2 * k) := by omega
    have hx1 : 2 * (j / B) + 1 < 2 ^ (2 * k) := by omega
    -- the trace with code `2 * (j / B) + a`, for the right low bit `a`
    have key : ∀ a, a < 2 → sumt (dec r (2 * k) (j % B) (2 * (j / B) + a)) = Color0 →
        ∃ t, ValidTrace r t ∧ cpos r t = i := by
      intro a ha hsum
      obtain ⟨e1, e2, e3, e4, e5⟩ := dec_spec r hb (x := 2 * (j / B) + a) (by omega)
      refine ⟨_, ⟨e1, e2, hsum⟩, ?_⟩
      have hg : gradeOf (dec r (2 * k) (j % B) (2 * (j / B) + a)) = k := by
        unfold gradeOf; rw [e3]; omega
      unfold cpos gpos
      rw [hg, e3, e4, e5, ← hBdef]
      have : (2 * (j / B) + a) / 2 = j / B := by omega
      rw [this, Nat.mul_comm, Nat.div_add_mod]
      omega
    obtain ⟨_, f2, f3, _, _⟩ := dec_spec r hb hx0
    have hc := cbit1_sumt_nonOne f2
    rw [f3] at hc
    have hc' : cbit1 (sumt (dec r (2 * k) (j % B) (2 * (j / B)))) = false := by
      rw [hc]; simp
    rcases cbit1_false hc' with c | c
    · exact key 0 (by omega) c
    · apply key 1 (by omega)
      have hf := dec_flip r (j / B) hb (by omega)
      rw [hf, c]; rfl

private theorem testBit_catGAux_low (r : Nat) : ∀ (X : List Nat) (k i : Nat), i < goff r k →
    (catGAux r k (goff r k) X).testBit i = false := by
  intro X
  induction X with
  | nil => intro k i _; simp [catGAux]
  | cons q qs ih =>
    intro k i hi
    simp only [catGAux, Nat.testBit_or, Nat.testBit_shiftLeft]
    have e : goff r k + gsize r k = goff r (k + 1) := rfl
    rw [e, ih (k + 1) i (by have := goff_le (r := r) (Nat.le_succ k); omega)]
    simp; omega

private theorem testBit_catGAux (r : Nat) : ∀ (X : List Nat) (k j p : Nat), p < gsize r (k + j) →
    (catGAux r k (goff r k) X).testBit (goff r (k + j) + p) = (X.getD j 0).testBit p := by
  intro X
  induction X with
  | nil => intro k j p _; simp [catGAux]
  | cons q qs ih =>
    intro k j p hp
    simp only [catGAux, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_and, testBit_ones]
    have e : goff r k + gsize r k = goff r (k + 1) := rfl
    rw [e]
    cases j with
    | zero =>
      rw [testBit_catGAux_low r qs (k + 1) _ (by rw [← e]; simpa using hp)]
      simp only [Nat.add_zero, List.getD_cons_zero] at hp ⊢
      simp [hp]
    | succ j =>
      have e2 : k + (j + 1) = k + 1 + j := by omega
      rw [e2] at hp ⊢
      rw [ih (k + 1) j p hp, List.getD_cons_succ]
      have := goff_le (r := r) (Nat.le_add_right (k + 1) j)
      have h3 : ¬ (goff r (k + 1 + j) + p - goff r k < gsize r k) := by omega
      simp [h3]

/-- Grades and concatenation: reading a trace in `catG`. -/
theorem testBit_catG {r : Nat} {t : Colseq} (h : ValidTrace r t) (X : List Nat) :
    (catG r X).testBit (cpos r t) = (X.getD (gradeOf t) 0).testBit (gpos r t) := by
  have := testBit_catGAux r X 0 (gradeOf t) (gpos r t) (by simpa using gpos_lt h)
  have e : catG r X = catGAux r 0 (goff r 0) X := rfl
  rw [e]
  simpa [cpos] using this

private theorem testBit_splitGAux (r : Nat) : ∀ (n k x j p : Nat), j < n → p < gsize r (k + j) →
    ((splitGAux r n k x).getD j 0).testBit p = x.testBit (goff r (k + j) + p - goff r k) := by
  intro n
  induction n with
  | zero => intro k x j p hj; omega
  | succ n ih =>
    intro k x j p hj hp
    cases j with
    | zero =>
      simp only [Nat.add_zero] at hp
      simp [splitGAux, hp]
    | succ j =>
      have e2 : k + (j + 1) = k + 1 + j := by omega
      rw [e2] at hp ⊢
      simp only [splitGAux, List.getD_cons_succ]
      rw [ih (k + 1) _ j p (by omega) hp, Nat.testBit_shiftRight]
      have e : goff r (k + 1) = goff r k + gsize r k := rfl
      have := goff_le (r := r) (Nat.le_add_right (k + 1) j)
      congr 1
      omega

/-- Grades and splitting: reading a trace in `splitG`. -/
theorem testBit_splitG {r : Nat} {t : Colseq} (h : ValidTrace r t) (x : Nat) :
    ((splitG r x).getD (gradeOf t) 0).testBit (gpos r t) = x.testBit (cpos r t) := by
  have := testBit_splitGAux r (ngrades r) 0 x (gradeOf t) (gpos r t) (gradeOf_lt h)
    (by simpa using gpos_lt h)
  have e : goff r 0 = 0 := rfl
  simpa [cpos, splitG, e] using this

/-- `den` of a split layout. -/
theorem den_splitG {r x : Nat} {t : Colseq} : den r (splitG r x) t ↔ denCat r x t := by
  unfold den denCat
  constructor
  · rintro ⟨h, hb⟩
    exact ⟨h, by rwa [testBit_splitG h] at hb⟩
  · rintro ⟨h, hb⟩
    exact ⟨h, by rwa [testBit_splitG h]⟩

/-- `denCat` of a concatenated layout. -/
theorem denCat_catG {r : Nat} {X : List Nat} {t : Colseq} : denCat r (catG r X) t ↔ den r X t := by
  unfold den denCat
  constructor
  · rintro ⟨h, hb⟩
    exact ⟨h, by rwa [testBit_catG h] at hb⟩
  · rintro ⟨h, hb⟩
    exact ⟨h, by rwa [testBit_catG h]⟩

/-- `mapGrades` reads grade `k` through `f k`. -/
theorem getD_mapGrades (f : Nat → Nat → Nat) (hf : ∀ k, f k 0 = 0) (X : List Nat) (k : Nat) :
    (mapGrades f X).getD k 0 = f k (X.getD k 0) := by
  unfold mapGrades
  suffices h : ∀ j (X : List Nat) k, (mapGradesAux f j X).getD k 0 = f (j + k) (X.getD k 0) by
    simpa using h 0 X k
  intro j X
  induction X generalizing j with
  | nil => intro k; simp [mapGradesAux, hf]
  | cons q qs ih =>
    intro k
    cases k with
    | zero => simp [mapGradesAux]
    | succ k =>
      simp only [mapGradesAux, List.getD_cons_succ, ih]
      congr 1
      omega

end FourColor.Engine
