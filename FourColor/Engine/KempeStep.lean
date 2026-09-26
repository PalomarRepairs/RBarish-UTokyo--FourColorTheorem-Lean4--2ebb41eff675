/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Matching
import FourColor.Engine.SetLevel

/-!
# Reducibility engine: the bit-parallel Kempe step and the `Color2 ↔ Color3` transposition

In grade `k ≥ 1` (`m = 2k` non-`Color1` entries, `B = choose r m` blocks, rows of `B` bits,
`L = 2^(m-1) * B` bits), flipping the rank `l ≥ 1` of every trace is the bit permutation
`xp ↦ xp xor 2^(l-1)` on rows, i.e. the translation `xlate` by `w = 2^(l-1) * B` with the
periodic mask `pmask L (2w) w` (precomputed once per grade in `rankMasks`); the rank `0`
is implicit (parity packing), so flipping the chord `(0, b)` is the single translation of
rank `b`.  Then

* `chordSat … a b y = y ||| flip_{a,b} y` closes `y` under the flip of one chord;
* `Sat_M y` (chord saturations along `M`) is the set of traces having some chord-flip of `M`
  in `y`;
* the Kempe step of grade `k` is `⋂_{M ∈ ncm m 0 m} Sat_M(q)`, computed by `ncmFold`, a
  continuation-passing enumeration of the matchings that shares chord prefixes (the matchings
  are never materialised; 1301–1429 chord saturations for `m = 14`).

`tau23Grade` flips every rank `1 … m-1`: it is the color transposition `Color2 ↔ Color3`.

All functions are kernel-friendly; the list of matchings `ncm` only appears in the
specification (`ncmFold_eq`).
-/

namespace FourColor.Engine

open FourColor

/-- The masks of the rank flips of a grade of `L` bits with rows of `B` bits: the mask of
rank `j + 1` (translation width `2^j * B`) is at index `j`, for `j < nr`. -/
def rankMasks (L B nr : Nat) : List Nat :=
  (List.range nr).map fun j => pmask L (2 * (2 ^ j * B)) (2 ^ j * B)

/-- Flip rank `l ≥ 1` of every trace of a grade (rows of `B` bits, precomputed masks). -/
def flipRank (B : Nat) (masks : List Nat) (l y : Nat) : Nat :=
  xlate (masks.getD (l - 1) 0) (2 ^ (l - 1) * B) y

/-- Close `y` under the flip of the chord `(a, b)`, `a < b`; rank `0` is implicit. -/
def chordSat (B : Nat) (masks : List Nat) (a b y : Nat) : Nat :=
  y ||| (if a == 0 then flipRank B masks b y else flipRank B masks a (flipRank B masks b y))

/-- Continuation-passing enumeration of the non-crossing perfect matchings `M` of the ranks
`lo … lo+n-1` (for `fuel ≥ n`), in the order of `ncm`: for each `M`,
`acc ← k (Sat_M y) acc`, where `Sat_M` applies `sat a b` for the chords `(a, b)` of `M` in
order.  Chord prefixes are shared between matchings. -/
def ncmFold (sat : Nat → Nat → Nat → Nat) :
    Nat → Nat → Nat → Nat → Nat → (Nat → Nat → Nat) → Nat
  | 0, _, _, y, acc, k => k y acc
  | fuel + 1, lo, n, y, acc, k =>
    if n == 0 then k y acc else
    (List.range (n / 2)).foldl (fun acc j =>
      ncmFold sat fuel (lo + 1) (2 * j) (sat lo (lo + 2 * j + 1) y) acc
        (fun y' acc' => ncmFold sat fuel (lo + 2 * j + 2) (n - 2 * j - 2) y' acc' k)) acc

/-- The Kempe step (skip color `Color1`) on grade `k` of ring size `r`:
`⋂_{M} Sat_M(q)` over the non-crossing perfect matchings of the `2k` ranks.  Grade `0` (the
all-`Color1` trace) is unchanged. -/
def kempeGrade (r k q : Nat) : Nat :=
  if k == 0 then q else
  let m := 2 * k
  let B := chooseAux r m
  let L := 2 ^ (m - 1) * B
  let masks := rankMasks L B (m - 1)
  ncmFold (chordSat B masks) m 0 m q (ones L) (fun y acc => acc &&& y)

/-- The Kempe step on all grades. -/
def kempeStep (r : Nat) (X : List Nat) : List Nat := mapGrades (kempeGrade r) X

/-- The color transposition `Color2 ↔ Color3` on grade `k`: flip all ranks `1 … 2k-1`. -/
def tau23Grade (r k q : Nat) : Nat :=
  if k == 0 then q else
  let m := 2 * k
  let B := chooseAux r m
  let L := 2 ^ (m - 1) * B
  let masks := rankMasks L B (m - 1)
  (List.range (m - 1)).foldl (fun y j => flipRank B masks (j + 1) y) q

/-- The color transposition `Color2 ↔ Color3` on all grades. -/
def tau23 (r : Nat) (X : List Nat) : List Nat := mapGrades (tau23Grade r) X

/-! ### Specification -/

/-- Chord saturations along a list of chords (the specification of `ncmFold`). -/
def satList (sat : Nat → Nat → Nat → Nat) (M : List Chord) (y : Nat) : Nat :=
  M.foldl (fun y ab => sat ab.1 ab.2 y) y

/-- `ncmFold` is the fold of its continuation over the enumerated matchings. -/
theorem ncmFold_eq (sat : Nat → Nat → Nat → Nat) (fuel lo n y acc : Nat)
    (k : Nat → Nat → Nat) :
    ncmFold sat fuel lo n y acc k =
      (ncm fuel lo n).foldl (fun acc M => k (satList sat M y) acc) acc := by
  induction fuel generalizing lo n y acc k with
  | zero => simp [ncmFold, ncm, satList]
  | succ fuel ih =>
    by_cases hn : n = 0
    · subst hn; simp [ncmFold, ncm, satList]
    · have hn' : (n == 0) = false := by simpa using hn
      simp only [ncmFold, ncm, hn', Bool.false_eq_true, ite_false, List.foldl_flatMap,
        List.foldl_map]
      congr 1
      funext acc j
      rw [ih]
      congr 1
      funext acc' mi
      rw [ih]
      congr 1
      funext acc'' mo
      simp [satList, List.foldl_append]

/-! ### Proof helpers -/

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
  | nil => simp [blockRank, nonOne]
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
  | nil => simp [xcode, nonOne]
  | cons c t ih =>
    cases c
    · rw [nonOne_cons_ne (by decide), Nat.pow_succ]; simp only [xcode]; omega
    · rw [nonOne_cons1]; exact ih
    · rw [nonOne_cons_ne (by decide), Nat.pow_succ]; simp only [xcode]; omega
    · rw [nonOne_cons_ne (by decide), Nat.pow_succ]; simp only [xcode]; omega

/-- The block rank and the row of a valid trace. -/
private theorem gpos_parts {r : Nat} {t : Colseq} (h : ValidTrace r t) :
    blockRank t (nonOne t) < chooseAux r (nonOne t) ∧ xcode t / 2 < 2 ^ (nonOne t - 1) := by
  refine ⟨?_, ?_⟩
  · rw [chooseAux_eq, ← h.1]; exact blockRank_lt t
  · have := xcode_lt t
    rcases Nat.eq_zero_or_pos (nonOne t) with h0 | h0
    · rw [h0] at this ⊢; simp at this ⊢; omega
    · have e : 2 ^ nonOne t = 2 * 2 ^ (nonOne t - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      omega

/-- Flipping bit `e` of a number decomposed around it. -/
private theorem xor_two_pow_split {e q b s : Nat} (hs : s < 2 ^ e) (hb : b < 2) :
    (2 ^ (e + 1) * q + (2 ^ e * b + s)) ^^^ 2 ^ e = 2 ^ (e + 1) * q + (2 ^ e * (1 - b) + s) := by
  have h1 : 2 ^ e * b + s < 2 ^ (e + 1) := by rw [Nat.pow_succ]; rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> omega
  have h2 : 2 ^ e * (1 - b) + s < 2 ^ (e + 1) := by rw [Nat.pow_succ]; rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> omega
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2,
    Nat.testBit_two_pow]
  by_cases hi : i < e + 1
  · rw [ite_eq_left hi, ite_eq_left hi, Nat.testBit_two_pow_mul_add _ hs,
      Nat.testBit_two_pow_mul_add _ hs]
    by_cases hie : i < e
    · rw [ite_eq_left hie, ite_eq_left hie]
      have : ¬ e = i := by omega
      simp [this]
    · rw [ite_eq_right hie, ite_eq_right hie]
      have : i = e := by omega
      subst this; rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> simp
  · rw [ite_eq_right hi, ite_eq_right hi]
    have : ¬ e = i := by omega
    simp [this]

/-- Bit-level meaning of a rank flip. -/
private theorem testBit_flipRank {m B l xp br : Nat} (hl1 : 1 ≤ l) (hl : l ≤ m - 1)
    (hbr : br < B) (hxp : xp < 2 ^ (m - 1)) (y : Nat) :
    (flipRank B (rankMasks (2 ^ (m - 1) * B) B (m - 1)) l y).testBit (xp * B + br) =
      y.testBit ((xp ^^^ 2 ^ (l - 1)) * B + br) := by
  obtain ⟨e, rfl⟩ : ∃ e, l = e + 1 := ⟨l - 1, by omega⟩
  have hmask : (rankMasks (2 ^ (m - 1) * B) B (m - 1)).getD e 0 =
      pmask (2 ^ (m - 1) * B) (2 * (2 ^ e * B)) (2 ^ e * B) := by
    simp [rankMasks, List.getD_eq_getElem?_getD, List.getElem?_range (show e < m - 1 by omega)]
  unfold flipRank
  simp only [Nat.add_sub_cancel]
  rw [hmask]
  have hB : 0 < B := by omega
  have hw : 0 < 2 ^ e * B := Nat.mul_pos (Nat.two_pow_pos e) hB
  have hdvd : 2 * (2 ^ e * B) ∣ 2 ^ (m - 1) * B := by
    rw [← Nat.mul_assoc, ← Nat.pow_succ']
    exact Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 (by omega)) B
  rw [testBit_xlate hw hdvd]
  have hlt : xp * B + br < 2 ^ (m - 1) * B := by
    have : (xp + 1) * B ≤ 2 ^ (m - 1) * B := Nat.mul_le_mul_right _ hxp
    rw [Nat.succ_mul] at this; omega
  simp only [hlt, decide_true, Bool.true_and]
  congr 1
  obtain ⟨q, b, s, rfl, hb, hs⟩ : ∃ q b s, xp = 2 ^ (e + 1) * q + (2 ^ e * b + s) ∧ b < 2 ∧
      s < 2 ^ e := by
    refine ⟨xp / 2 ^ (e + 1), xp % 2 ^ (e + 1) / 2 ^ e, xp % 2 ^ (e + 1) % 2 ^ e, ?_, ?_,
      Nat.mod_lt _ (Nat.two_pow_pos e)⟩
    · rw [Nat.div_add_mod, Nat.div_add_mod]
    · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos e), ← Nat.pow_succ']
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
  rw [xor_two_pow_split hs hb]
  unfold xpartner
  rw [Nat.pow_succ'] at *
  generalize 2 ^ e = W at *
  have hsB : s * B + br < W * B := by
    have : (s + 1) * B ≤ W * B := Nat.mul_le_mul_right _ hs
    rw [Nat.succ_mul] at this; omega
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
  · have ei : (2 * W * q + (W * 0 + s)) * B + br = 2 * (W * B) * q + (s * B + br) := by ring
    rw [ei, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega), ite_eq_left hsB]
    ring
  · have ei : (2 * W * q + (W * 1 + s)) * B + br = 2 * (W * B) * q + (W * B + (s * B + br)) := by
      ring
    have hWB : W * B + (s * B + br) < 2 * (W * B) := by omega
    rw [ei, Nat.mul_add_mod, Nat.mod_eq_of_lt hWB, ite_eq_right (by omega)]
    have : (2 * W * q + (W * (1 - 1) + s)) * B + br = 2 * (W * B) * q + (s * B + br) := by ring
    rw [this]; omega

private theorem color0_flipNth (l : Nat) {t : Colseq} (h : Color0 ∉ t) : Color0 ∉ flipNth l t := by
  induction t generalizing l with
  | nil => simp [flipNth]
  | cons c t ih =>
    simp only [List.mem_cons, not_or] at h
    cases c
    · exact absurd rfl h.1
    · simp [flipNth, ih _ h.2]
    · cases l <;> simp [flipNth, permc, palette, ih _ h.2, h.2]
    · cases l <;> simp [flipNth, permc, palette, ih _ h.2, h.2]

/-- Rank flips commute. -/
private theorem flipNth_comm (a b : Nat) (t : Colseq) :
    flipNth a (flipNth b t) = flipNth b (flipNth a t) := by
  induction t generalizing a b with
  | nil => rfl
  | cons c t ih =>
    cases c <;> cases a <;> cases b <;> simp [flipNth, permc, palette, ih]

private theorem flipChord_comm (c d : Chord) (t : Colseq) :
    flipChord c (flipChord d t) = flipChord d (flipChord c t) := by
  unfold flipChord
  rw [flipNth_comm c.2 d.1, flipNth_comm c.2 d.2, flipNth_comm c.1 d.1, flipNth_comm c.1 d.2]

private theorem flipChord_flipChords (c : Chord) (S : List Chord) (t : Colseq) :
    flipChord c (flipChords S t) = flipChords S (flipChord c t) := by
  induction S generalizing t with
  | nil => rfl
  | cons d S ih =>
    simp only [flipChords, List.foldl_cons] at ih ⊢
    rw [ih, flipChord_comm]

private theorem nonOne_flipChord (c : Chord) (t : Colseq) : nonOne (flipChord c t) = nonOne t := by
  simp [flipChord, nonOne_flipNth]

private theorem validTrace_flipChords {r : Nat} (S : List Chord) {t : Colseq}
    (hS : ∀ ab ∈ S, ab.1 < ab.2 ∧ ab.2 < nonOne t) (h : ValidTrace r t) :
    ValidTrace r (flipChords S t) ∧ nonOne (flipChords S t) = nonOne t := by
  induction S generalizing t with
  | nil => exact ⟨h, rfl⟩
  | cons c S ih =>
    simp only [flipChords, List.foldl_cons] at ih ⊢
    have hc := hS c (by simp)
    have h' := validTrace_flipChord (a := c.1) (b := c.2) h hc.1 hc.2
    have e := nonOne_flipChord c t
    obtain ⟨h1, h2⟩ := ih (t := flipChord c t) (by
      intro ab hab; rw [e]; exact hS ab (by simp [hab])) h'
    exact ⟨h1, h2.trans e⟩

/-- The position of a chord flip. -/
private theorem gpos_flipChord {r a b : Nat} {t : Colseq} (h0 : Color0 ∉ t) (hab : a < b)
    (hb : b < nonOne t) :
    gpos r (flipChord (a, b) t) =
      (xcode t ^^^ 2 ^ b ^^^ 2 ^ a) / 2 * chooseAux r (nonOne t) + blockRank t (nonOne t) := by
  unfold gpos flipChord
  simp only
  rw [nonOne_flipNth, nonOne_flipNth, blockRank_flipNth, blockRank_flipNth,
    xcode_flipNth (by rw [nonOne_flipNth]; omega) (color0_flipNth _ h0), xcode_flipNth hb h0]

private theorem two_pow_div_two {b : Nat} (hb : 1 ≤ b) : 2 ^ b / 2 = 2 ^ (b - 1) := by
  have := Nat.pow_div (x := 2) hb (by norm_num)
  simpa using this

/-- Bit-level meaning of a chord flip (the statement of `testBit_chordFlip`). -/
private theorem testBit_chordFlip' {r k a b : Nat} {t : Colseq} (ht : ValidTrace r t)
    (hk : gradeOf t = k) (hk0 : 0 < k) (hab : a < b) (hb : b < 2 * k) (y : Nat) :
    (chordSat (chooseAux r (2 * k))
        (rankMasks (2 ^ (2 * k - 1) * chooseAux r (2 * k)) (chooseAux r (2 * k)) (2 * k - 1))
        a b y).testBit (gpos r t) =
      (y.testBit (gpos r t) || y.testBit (gpos r (flipChord (a, b) t))) := by
  have hm : nonOne t = 2 * k := by rw [nonOne_eq_two_mul ht, hk]
  obtain ⟨hbr, hxp⟩ := gpos_parts ht
  rw [hm] at hbr hxp
  rw [gpos_flipChord ht.2.1 hab (by omega)]
  have hg : gpos r t = xcode t / 2 * chooseAux r (2 * k) + blockRank t (2 * k) := by
    unfold gpos; rw [hm]
  rw [hg, hm]
  generalize xcode t = x at *
  generalize chooseAux r (2 * k) = B at *
  generalize blockRank t (2 * k) = br at *
  unfold chordSat
  rw [Nat.testBit_or]
  congr 1
  rw [Nat.xor_div_two, Nat.xor_div_two, two_pow_div_two (by omega)]
  by_cases ha : a = 0
  · subst ha
    simp only [BEq.rfl, ite_true, Nat.pow_zero]
    rw [testBit_flipRank (m := 2 * k) (by omega) (by omega) hbr hxp]
    simp
  · have ha' : (a == 0) = false := by simpa using ha
    rw [ha']
    simp only [Bool.false_eq_true, ite_false]
    rw [two_pow_div_two (by omega)]
    rw [testBit_flipRank (m := 2 * k) (by omega) (by omega) hbr hxp]
    have hxa : x / 2 ^^^ 2 ^ (a - 1) < 2 ^ (2 * k - 1) :=
      Nat.xor_lt_two_pow hxp (Nat.pow_lt_pow_right (by norm_num) (by omega))
    rw [testBit_flipRank (m := 2 * k) (by omega) (by omega) hbr hxa]
    rw [Nat.xor_assoc, Nat.xor_assoc, Nat.xor_comm (2 ^ (a - 1))]

/-- Private copy of `kempeGrade_zero` (declared later in the file). -/
private theorem kempeGrade_zero' (r k : Nat) : kempeGrade r k 0 = 0 := by
  unfold kempeGrade
  split
  · rfl
  · simp only
    rw [ncmFold_eq]
    have hne := ncm_ne_nil (2 * k) 0 (2 * k) (by omega)
    generalize ncm (2 * k) 0 (2 * k) = l at hne
    generalize ones _ = a
    have hs : ∀ (B : Nat) (masks : List Nat) (M : List Chord),
        satList (chordSat B masks) M 0 = 0 := by
      intro B masks M
      unfold satList
      induction M with
      | nil => rfl
      | cons c M ih =>
        simp only [List.foldl_cons]
        have : chordSat B masks c.1 c.2 0 = 0 := by
          unfold chordSat flipRank xlate; split <;> simp
        rw [this]; exact ih
    simp only [hs, Nat.and_zero]
    cases l with
    | nil => exact absurd rfl hne
    | cons M l =>
      simp only [List.foldl_cons]
      clear hne
      induction l with
      | nil => rfl
      | cons M' l ih => simpa using ih

/-- The bits of a fold of intersections. -/
private theorem testBit_foldl_and {α : Type} (f : α → Nat) (i : Nat) :
    ∀ (l : List α) (a : Nat), (l.foldl (fun acc M => acc &&& f M) a).testBit i = true →
      a.testBit i = true ∧ ∀ M ∈ l, (f M).testBit i = true := by
  intro l
  induction l with
  | nil => intro a h; exact ⟨h, by simp⟩
  | cons M l ih =>
    intro a h
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := ih _ h
    rw [Nat.testBit_land, Bool.and_eq_true] at h1
    refine ⟨h1.1, ?_⟩
    intro M' hM'
    rcases List.mem_cons.mp hM' with rfl | hM'
    · exact h1.2
    · exact h2 M' hM'

/-- Bits of a saturation along a list of chords. -/
private theorem satList_bit {r k : Nat} (hk0 : 0 < k) {t : Colseq} (ht : ValidTrace r t)
    (hk : gradeOf t = k) : ∀ (M : List Chord) (y : Nat),
    (∀ ab ∈ M, ab.1 < ab.2 ∧ ab.2 < 2 * k) →
    (satList (chordSat (chooseAux r (2 * k))
        (rankMasks (2 ^ (2 * k - 1) * chooseAux r (2 * k)) (chooseAux r (2 * k)) (2 * k - 1)))
        M y).testBit (gpos r t) = true →
    ∃ S, S.Sublist M ∧ y.testBit (gpos r (flipChords S t)) = true := by
  have hm : nonOne t = 2 * k := by rw [nonOne_eq_two_mul ht, hk]
  intro M
  induction M with
  | nil => intro y _ h; exact ⟨[], List.Sublist.slnil, h⟩
  | cons c M ih =>
    intro y hM h
    simp only [satList, List.foldl_cons] at h
    obtain ⟨S, hS, hbit⟩ := ih _ (fun ab hab => hM ab (by simp [hab])) h
    have hSb : ∀ ab ∈ S, ab.1 < ab.2 ∧ ab.2 < nonOne t := by
      intro ab hab; rw [hm]; exact hM ab (by simp [hS.subset hab])
    obtain ⟨hv, hn⟩ := validTrace_flipChords S hSb ht
    have hk' : gradeOf (flipChords S t) = k := by unfold gradeOf; rw [hn, hm]; omega
    have hc := hM c (by simp)
    rw [testBit_chordFlip' hv hk' hk0 hc.1 hc.2, Bool.or_eq_true] at hbit
    rcases hbit with hbit | hbit
    · exact ⟨S, hS.cons c, hbit⟩
    · refine ⟨c :: S, hS.cons_cons c, ?_⟩
      rw [flipChord_flipChords] at hbit
      simpa [flipChords] using hbit

private theorem nonOne_permt132 (t : Colseq) : nonOne (permt Eperm132 t) = nonOne t := by
  induction t with
  | nil => rfl
  | cons c t ih =>
    rw [permt_cons, nonOne_cons, nonOne_cons, ih]
    cases c <;> simp [permc, palette]

private theorem gradeOf_permt132 (t : Colseq) : gradeOf (permt Eperm132 t) = gradeOf t := by
  unfold gradeOf; rw [nonOne_permt132]

private theorem blockRank_permt132 (t : Colseq) (m : Nat) :
    blockRank (permt Eperm132 t) m = blockRank t m := by
  induction t generalizing m with
  | nil => rfl
  | cons c t ih =>
    have hl : (permt Eperm132 t).length = t.length := List.length_map _
    cases c <;> simp only [permt_cons, permc, palette, blockRank, ih, hl]

private theorem xor_mask_succ (x n b : Nat) (hb : b < 2) :
    (2 * x + b) ^^^ (2 ^ (n + 1) - 1) = 2 * (x ^^^ (2 ^ n - 1)) + (1 - b) := by
  have e1 : 2 * x + b = 2 ^ 1 * x + b := by simp
  have e2 : 2 * (x ^^^ (2 ^ n - 1)) + (1 - b) = 2 ^ 1 * (x ^^^ (2 ^ n - 1)) + (1 - b) := by simp
  rw [e1, e2]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ (by simpa using hb),
    Nat.testBit_two_pow_mul_add _ (by simp; omega), Nat.testBit_two_pow_sub_one]
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> cases i <;> simp

private theorem xcode_permt132 {t : Colseq} (h0 : Color0 ∉ t) :
    xcode (permt Eperm132 t) = xcode t ^^^ (2 ^ nonOne t - 1) := by
  induction t with
  | nil => rfl
  | cons c t ih =>
    simp only [List.mem_cons, not_or] at h0
    have ih := ih h0.2
    cases c
    · exact absurd rfl h0.1
    · rw [nonOne_cons1]; simpa [xcode, permc] using ih
    · rw [nonOne_cons_ne (by decide)]
      simp only [permt_cons, xcode, permc, palette]
      rw [ih]
      have := xor_mask_succ (xcode t) (nonOne t) 0 (by omega)
      simpa using this.symm
    · rw [nonOne_cons_ne (by decide)]
      simp only [permt_cons, xcode, permc, palette]
      rw [ih]
      have := xor_mask_succ (xcode t) (nonOne t) 1 (by omega)
      simpa using this.symm

private theorem validTrace_permt {r : Nat} (g : EdgePerm) {t : Colseq} (h : ValidTrace r t) :
    ValidTrace r (permt g t) :=
  ⟨by simp [permt, h.1], by rw [memc0_permt]; exact h.2.1, by rw [sumt_permt, h.2.2, permc0]⟩

private theorem gpos_permt132 {r : Nat} {t : Colseq} (h : ValidTrace r t) :
    gpos r (permt Eperm132 t) =
      (xcode t / 2 ^^^ (2 ^ (nonOne t - 1) - 1)) * chooseAux r (nonOne t) +
        blockRank t (nonOne t) := by
  unfold gpos
  rw [nonOne_permt132, blockRank_permt132, xcode_permt132 h.2.1, Nat.xor_div_two]
  congr 3
  cases nonOne t with
  | zero => rfl
  | succ n => rw [Nat.pow_succ]; simp only [Nat.add_sub_cancel]; omega

private theorem two_pow_xor_mask (n : Nat) : 2 ^ n ^^^ (2 ^ n - 1) = 2 ^ (n + 1) - 1 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_two_pow_sub_one]
  by_cases h : n = i
  · subst h; simp
  · have : (i < n + 1) = (i < n) := by apply propext; omega
    simp [h, this]

private theorem testBit_tau23fold {m B br : Nat} (hbr : br < B) (q : Nat) :
    ∀ n, n ≤ m - 1 → ∀ xp, xp < 2 ^ (m - 1) →
    ((List.range n).foldl
        (fun y j => flipRank B (rankMasks (2 ^ (m - 1) * B) B (m - 1)) (j + 1) y) q).testBit
        (xp * B + br) = q.testBit ((xp ^^^ (2 ^ n - 1)) * B + br) := by
  intro n
  induction n with
  | zero => intro _ xp _; simp
  | succ n ih =>
    intro hn xp hxp
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      testBit_flipRank (by omega) hn hbr hxp]
    simp only [Nat.add_sub_cancel]
    rw [ih (by omega) _ (Nat.xor_lt_two_pow hxp (Nat.pow_lt_pow_right (by norm_num) (by omega))),
      Nat.xor_assoc, two_pow_xor_mask]

private theorem tau23Grade_zero' (r k : Nat) : tau23Grade r k 0 = 0 := by
  unfold tau23Grade
  split
  · rfl
  · simp only
    generalize List.range _ = l
    induction l with
    | nil => rfl
    | cons j l ih => simpa [flipRank, xlate] using ih

private theorem tau23_bit {r : Nat} (X : List Nat) {t : Colseq} (ht : ValidTrace r t) :
    ((tau23 r X).getD (gradeOf t) 0).testBit (gpos r t) =
      (X.getD (gradeOf (permt Eperm132 t)) 0).testBit (gpos r (permt Eperm132 t)) := by
  unfold tau23
  rw [getD_mapGrades _ (tau23Grade_zero' r) X, gradeOf_permt132, gpos_permt132 ht]
  have hm := nonOne_eq_two_mul ht
  obtain ⟨hbr, hxp⟩ := gpos_parts ht
  have hg : gpos r t = xcode t / 2 * chooseAux r (nonOne t) + blockRank t (nonOne t) := rfl
  rw [hg]
  rw [hm] at hbr hxp ⊢
  generalize gradeOf t = k at *
  generalize xcode t / 2 = xp at *
  generalize blockRank t (2 * k) = br at *
  unfold tau23Grade
  by_cases hk : k = 0
  · subst hk
    simp at hxp
    subst hxp
    simp
  · have hk' : (k == 0) = false := by simpa using hk
    rw [hk']
    simp only [Bool.false_eq_true, ite_false]
    rw [testBit_tau23fold hbr _ (2 * k - 1) le_rfl xp hxp]

/-- Bit-level meaning of a chord flip: for a valid trace `t` of grade `k ≥ 1` and a chord
`a < b < 2k`, the chord flip of the grade moves the bit of `flipChord (a, b) t` to the
position of `t`. -/
theorem testBit_chordFlip {r k a b : Nat} {t : Colseq} (ht : ValidTrace r t)
    (hk : gradeOf t = k) (hk0 : 0 < k) (hab : a < b) (hb : b < 2 * k) (y : Nat) :
    let B := chooseAux r (2 * k)
    let masks := rankMasks (2 ^ (2 * k - 1) * B) B (2 * k - 1)
    (chordSat B masks a b y).testBit (gpos r t) =
      (y.testBit (gpos r t) || y.testBit (gpos r (flipChord (a, b) t))) :=
  testBit_chordFlip' ht hk hk0 hab hb y

/-- **Soundness of the bit-parallel Kempe step**: every trace of `kempeStep r X` is in
`Kempe1 (den r X)`. -/
theorem kempeStep_sound {r : Nat} {X : List Nat} {t : Colseq} (h : den r (kempeStep r X) t) :
    Kempe1 (den r X) t := by
  obtain ⟨ht, hb⟩ := h
  intro w hw
  obtain ⟨M, hM, hflip⟩ := exists_ncm_of_matchg hw
  unfold kempeStep at hb
  rw [getD_mapGrades _ (kempeGrade_zero' r) X] at hb
  have hm := nonOne_eq_two_mul ht
  by_cases hk0 : gradeOf t = 0
  · refine ⟨t, ⟨ht, ?_⟩, hw⟩
    have : kempeGrade r (gradeOf t) (X.getD (gradeOf t) 0) = X.getD (gradeOf t) 0 := by
      unfold kempeGrade; simp [hk0]
    rwa [this] at hb
  · have hk' : (gradeOf t == 0) = false := by simpa using hk0
    unfold kempeGrade at hb
    rw [hk'] at hb
    simp only [Bool.false_eq_true, ite_false] at hb
    rw [ncmFold_eq] at hb
    rw [hm] at hM
    have hMbit := (testBit_foldl_and _ _ _ _ hb).2 M hM
    have hMc : ∀ ab ∈ M, ab.1 < ab.2 ∧ ab.2 < 2 * gradeOf t := by
      intro ab hab
      have := mem_ncm_chord hM hab
      omega
    obtain ⟨S, hS, hbit⟩ := satList_bit (Nat.pos_of_ne_zero hk0) ht rfl M _ hMc hMbit
    have hSb : ∀ ab ∈ S, ab.1 < ab.2 ∧ ab.2 < nonOne t := by
      intro ab hab; rw [hm]; exact hMc ab (hS.subset hab)
    obtain ⟨hv, hn⟩ := validTrace_flipChords S hSb ht
    have hg : gradeOf (flipChords S t) = gradeOf t := by unfold gradeOf; rw [hn]
    refine ⟨flipChords S t, ⟨hv, ?_⟩, hflip S hS⟩
    rw [hg]; exact hbit

/-- The transposition `tau23` is the color permutation `Eperm132` on traces. -/
theorem den_tau23 {r : Nat} {X : List Nat} {t : Colseq} :
    den r (tau23 r X) t ↔ den r X (permt Eperm132 t) := by
  constructor
  · rintro ⟨ht, hb⟩
    exact ⟨validTrace_permt _ ht, by rwa [tau23_bit X ht] at hb⟩
  · rintro ⟨ht, hb⟩
    have ht' : ValidTrace r t := by
      have := validTrace_permt Eperm132 ht; rwa [etrace_id] at this
    exact ⟨ht', by rwa [tau23_bit X ht']⟩

/-- Translating the empty set. -/
theorem xlate_zero (lo w : Nat) : xlate lo w 0 = 0 := by simp [xlate]

/-- Flipping a rank of the empty set. -/
theorem flipRank_zero (B : Nat) (masks : List Nat) (l : Nat) : flipRank B masks l 0 = 0 := by
  simp [flipRank, xlate_zero]

/-- Saturating the empty set. -/
theorem chordSat_zero (B : Nat) (masks : List Nat) (a b : Nat) : chordSat B masks a b 0 = 0 := by
  unfold chordSat; split <;> simp [flipRank_zero]

/-- `tau23Grade` of the empty grade is empty (used for the checkpoint expansion). -/
theorem tau23Grade_zero (r k : Nat) : tau23Grade r k 0 = 0 := by
  unfold tau23Grade
  split
  · rfl
  · simp only
    generalize List.range _ = l
    induction l with
    | nil => rfl
    | cons j l ih => simpa [flipRank_zero] using ih

/-- Saturating the empty set along a matching. -/
theorem satList_zero (B : Nat) (masks : List Nat) (M : List Chord) :
    satList (chordSat B masks) M 0 = 0 := by
  unfold satList
  induction M with
  | nil => rfl
  | cons c M ih => simpa [chordSat_zero] using ih

/-- `kempeGrade` of the empty grade is empty. -/
theorem kempeGrade_zero (r k : Nat) : kempeGrade r k 0 = 0 := by
  unfold kempeGrade
  split
  · rfl
  · simp only
    rw [ncmFold_eq]
    have hne := ncm_ne_nil (2 * k) 0 (2 * k) (by omega)
    generalize ncm (2 * k) 0 (2 * k) = l at hne
    generalize ones _ = a
    simp only [satList_zero, Nat.and_zero]
    cases l with
    | nil => exact absurd rfl hne
    | cons M l =>
      simp only [List.foldl_cons]
      clear hne
      induction l with
      | nil => rfl
      | cons M' l ih => simpa using ih

end FourColor.Engine
