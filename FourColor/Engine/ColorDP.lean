/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Succ
import FourColor.Engine.Network

/-!
# Reducibility engine: the bit-parallel coloring DP

The set `CpReach cp` of ring traces of a construction program (see `Succ.lean`) is computed
as a big number in a base-3 *slot* layout: the state `⟨ℓ, ord, x⟩` stores traces of length
`ℓ`, the ring position `i` living in the base-3 digit (*slot*) `ord[i]`, i.e. `t` is stored at
`slotIdx ord t = ∑_i cdig t_i * 3^ord[i]` (`DPState.den`).  Every construction step is a
handful of masked shifts (digit selections `sel` and digit rewrites `mv`):

* `R n`, `R'`: rotate `ord` only (no bit operation);
* `Y`, `U`: new edges go to fresh top slots;
* `H`: digit rewrites of the first two slots;
* `K`, `A`: digit rewrites, then the dead slots are killed (`killSlot`: digit set to `0`,
  moved to the top slot by a digit transposition, and truncated).

This is the set-lift of `cpsucc` (`dpStep_den`), starting from all the traces of the base
map (no symmetry reduction).  At the end the digits are sorted into ring order
(`sortDigits`, at most `ℓ` digit transpositions), giving the base-3 layout `b3idx`; the last
digit, determined by the others for valid traces, is folded away (`fold3`), and the result is
converted into the packed layout by the conversion network (`dpP1`).

The same DP computes the coloring traces of a configuration (`cfprog cf`) and the contract
traces (the program `cpc` computed by `cfctr`, whose ring colorings are the contract colorings
of the configuration), as well as the basis colorings of the Birkhoff check.
-/

namespace FourColor.Engine

open FourColor

/-- The DP state: `len` slots, the slots of the ring positions in ring order (`ord`, a
permutation of `0 … len-1`), and the trace set `x` over the indices `< 3^len`. -/
structure DPState where
  /-- The number of slots (the ring size). -/
  len : Nat
  /-- The slot of each ring position, in ring order. -/
  ord : List Nat
  /-- The trace set (bit `slotIdx ord t` for the trace `t`). -/
  x : Nat

/-- The entries of `x` (below `3^ℓ`) whose digit `s` is `v`. -/
def sel (ℓ x s v : Nat) : Nat := x &&& digitMask ℓ s v

/-- Rewrite digit `s` from `v` to `v'` in all entries of `y` (which all have digit `s = v`). -/
def mv (y s v v' : Nat) : Nat :=
  if v ≤ v' then y <<< ((v' - v) * 3 ^ s) else y >>> ((v - v') * 3 ^ s)

/-- `Eperm231` on digits (`Color1 ↦ Color2 ↦ Color3 ↦ Color1`). -/
def p231 (v : Nat) : Nat :=
  match v with
  | 0 => 1
  | 1 => 2
  | _ => 0

/-- `Eperm312` on digits (`Color1 ↦ Color3 ↦ Color2 ↦ Color1`). -/
def p312 (v : Nat) : Nat :=
  match v with
  | 0 => 2
  | 1 => 0
  | _ => 1

/-- `addc` on the digits of two distinct nonzero colors. -/
def addd (a b : Nat) : Nat := ((a + 1) ^^^ (b + 1)) - 1

/-- The three digits. -/
def digits3 : List Nat := [0, 1, 2]

/-- Union of a list of sets. -/
def ors (l : List Nat) : Nat := l.foldl (· ||| ·) 0

/-- Transpose the digits `a` and `b` of every entry. -/
def transp (ℓ x a b : Nat) : Nat :=
  if a == b then x else
  ors (digits3.flatMap fun u => digits3.map fun v =>
    let y := sel ℓ (sel ℓ x a u) b v
    mv (mv y a u v) b v u)

/-- Kill slot `s` (not in `st.ord`): set its digit to `0`, move it to the top slot, rename the
top slot into `s`, and truncate. -/
def killSlot (st : DPState) (s : Nat) : DPState :=
  let ℓ := st.len
  let x0 := ors (digits3.map fun v => mv (sel ℓ st.x s v) s v 0)
  let top := ℓ - 1
  let x1 := transp ℓ x0 s top
  let ord' := st.ord.map fun t => if t == top then s else t
  ⟨ℓ - 1, ord', x1 &&& ones (3 ^ (ℓ - 1))⟩

/-- One construction step on the DP state: the set-lift of `cpsucc s`. -/
def dpStep (st : DPState) (s : Cpstep) : DPState :=
  let ℓ := st.len
  match s, st.ord with
  | .R n, _ => { st with ord := rot n st.ord }
  | .R', _ => if st.ord.length ≤ 1 then { st with x := 0 } else { st with ord := rotr 1 st.ord }
  | .Y, s0 :: rest =>
    let x' := ors (digits3.map fun v =>
      let y := sel ℓ st.x s0 v
      (mv y s0 v (p231 v) <<< (p312 v * 3 ^ ℓ)) ||| (mv y s0 v (p312 v) <<< (p231 v * 3 ^ ℓ)))
    ⟨ℓ + 1, s0 :: ℓ :: rest, x'⟩
  | .H, s0 :: s1 :: _ =>
    let x' := ors (digits3.flatMap fun v1 => digits3.map fun v2 =>
      let y := sel ℓ (sel ℓ st.x s0 v1) s1 v2
      if v1 == v2 then
        mv (mv y s0 v1 (p231 v1)) s1 v2 (p231 v1) ||| mv (mv y s0 v1 (p312 v1)) s1 v2 (p312 v1)
      else mv (mv y s0 v1 v2) s1 v2 v1)
    { st with x := x' }
  | .U, _ =>
    let x' := ors (digits3.map fun v => st.x <<< (v * 3 ^ ℓ + v * 3 ^ (ℓ + 1)))
    ⟨ℓ + 2, ℓ :: (ℓ + 1) :: st.ord, x'⟩
  | .K, s0 :: s1 :: rest =>
    let x' := ors (digits3.flatMap fun v1 => digits3.map fun v2 =>
      if v1 == v2 then 0 else mv (sel ℓ (sel ℓ st.x s0 v1) s1 v2) s0 v1 (addd v1 v2))
    killSlot ⟨ℓ, s0 :: rest, x'⟩ s1
  | .A, s0 :: s1 :: rest =>
    let x' := ors (digits3.map fun v => sel ℓ (sel ℓ st.x s0 v) s1 v)
    match rest with
    | [] => { st with x := x' }
    | _ :: _ =>
      let st1 := killSlot ⟨ℓ, rest ++ [s0], x'⟩ s1
      match st1.ord.getLast? with
      | some s0' => killSlot ⟨st1.len, st1.ord.dropLast, st1.x⟩ s0'
      | none => st1
  | _, _ => { st with x := 0 }

/-- The DP state of the base map `cpmap []`: the traces `[c, c]`, at indices `0, 4, 8`. -/
def dpBase : DPState := ⟨2, [0, 1], 2 ^ 0 ||| 2 ^ 4 ||| 2 ^ 8⟩

/-- The DP state of a program (read right to left, like `cpmap`). -/
def dpRun : Cprog → DPState
  | [] => dpBase
  | s :: cp => dpStep (dpRun cp) s

/-- Sort the digits into ring order: position `i + j` gets digit `i + j` (`fuel ≥` length of
`ord`). -/
def sortDigits (ℓ : Nat) : Nat → Nat → List Nat → Nat → Nat
  | 0, _, _, x => x
  | fuel + 1, i, ord, x =>
    match ord with
    | [] => x
    | s :: rest =>
      sortDigits ℓ fuel (i + 1) (rest.map fun t => if t == i then s else t) (transp ℓ x s i)

/-- The ring traces of a program in the base-3 layout (`b3idx`, ring order). -/
def dpB3 (cp : Cprog) : Nat :=
  let st := dpRun cp
  sortDigits st.len st.len 0 st.ord st.x

/-- Fold the last digit of a base-3 layout of `r` digits: the result is indexed by the
prefixes of length `r - 1`. -/
def fold3 (r x : Nat) : Nat :=
  let n := 3 ^ (r - 1)
  let M := ones n
  (x &&& M) ||| ((x >>> n) &&& M) ||| ((x >>> (2 * n)) &&& M)

/-- The ring traces of a program of ring size `r` in the packed layout. -/
def dpP1 (r : Nat) (cnv : Net) (cp : Cprog) : List Nat :=
  splitG r (applyNet cnv (fold3 r (dpB3 cp)))

/-! ### Specification -/

/-- The slot index of a trace. -/
def slotIdx : List Nat → Colseq → Nat
  | s :: ord, c :: t => cdig c * 3 ^ s + slotIdx ord t
  | _, _ => 0

/-- The traces represented by a DP state. -/
def DPState.den (st : DPState) (t : Colseq) : Prop :=
  t.length = st.len ∧ Color0 ∉ t ∧ st.x.testBit (slotIdx st.ord t) = true

/-- Well-formed DP states: `ord` is a permutation of the slots, and `x` has no index beyond
`3^len`. -/
def DPState.WF (st : DPState) : Prop :=
  st.ord.Perm (List.range st.len) ∧ st.x < 2 ^ (3 ^ st.len) ∧ 1 ≤ st.len

/-! ### Proofs: base-3 digit arithmetic -/

/-- The base-3 digit `s` of `j`. -/
private def dig (j s : Nat) : Nat := j / 3 ^ s % 3

/-- The number with base-3 digits `f 0, …, f (n-1)`. -/
private def bv (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bv f n + f n * 3 ^ n

private theorem bv_congr {f g : Nat → Nat} : ∀ {n : Nat}, (∀ s < n, f s = g s) → bv f n = bv g n
  | 0, _ => rfl
  | n + 1, h => by
    simp only [bv]
    rw [bv_congr (fun s hs => h s (by omega)), h n (by omega)]

private theorem bv_lt {f : Nat → Nat} : ∀ {n : Nat}, (∀ s < n, f s ≤ 2) → bv f n < 3 ^ n
  | 0, _ => by simp [bv]
  | n + 1, h => by
    simp only [bv]
    have h1 := bv_lt (n := n) (fun s hs => h s (by omega))
    have h2 : f n * 3 ^ n ≤ 2 * 3 ^ n := Nat.mul_le_mul_right _ (h n (by omega))
    rw [Nat.pow_succ]; omega

private theorem dig_bv {f : Nat → Nat} : ∀ {n : Nat}, (∀ s < n, f s ≤ 2) → ∀ s < n,
    dig (bv f n) s = f s
  | 0, _, s, hs => absurd hs (Nat.not_lt_zero _)
  | n + 1, h, s, hs => by
    have hlt := bv_lt (n := n) (fun s hs => h s (by omega))
    simp only [bv, dig]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
    · have e : 3 ^ n = 3 ^ s * 3 ^ (n - s) := by rw [← Nat.pow_add]; congr 1; omega
      rw [e, ← Nat.mul_assoc, Nat.mul_comm (f n), Nat.mul_assoc, Nat.add_mul_div_left _ _
        (Nat.pow_pos (by norm_num))]
      obtain ⟨k, hk⟩ : ∃ k, n - s = k + 1 := ⟨n - s - 1, by omega⟩
      rw [hk, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (f n * 3 ^ k) 3, Nat.add_mul_mod_self_left]
      exact dig_bv (fun s hs => h s (by omega)) s hs
    · rw [Nat.add_mul_div_right _ _ (Nat.pow_pos (by norm_num)), Nat.div_eq_of_lt hlt,
        Nat.zero_add, Nat.mod_eq_of_lt (by have := h s (by omega); omega)]

private theorem bv_dig_mod (j : Nat) : ∀ n, bv (dig j) n = j % 3 ^ n
  | 0 => by simp [bv, Nat.mod_one]
  | n + 1 => by
    simp only [bv]
    rw [bv_dig_mod j n, Nat.mod_pow_succ, dig, Nat.mul_comm]

private theorem bv_dig {j n : Nat} (h : j < 3 ^ n) : bv (dig j) n = j := by
  rw [bv_dig_mod, Nat.mod_eq_of_lt h]

private theorem dig_le (j s : Nat) : dig j s ≤ 2 := by
  unfold dig; have := Nat.mod_lt (j / 3 ^ s) (show 3 > 0 by norm_num); omega

private theorem bv_update {f : Nat → Nat} {s a : Nat} : ∀ {n : Nat}, s < n →
    bv (Function.update f s a) n + f s * 3 ^ s = bv f n + a * 3 ^ s
  | 0, hs => absurd hs (Nat.not_lt_zero _)
  | n + 1, hs => by
    simp only [bv]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hs with hs | rfl
    · have := bv_update (f := f) (a := a) hs
      rw [Function.update_of_ne (by omega)]; omega
    · rw [bv_congr (g := f) (fun s' hs' => Function.update_of_ne (by omega) _ _),
        Function.update_self]; omega


private theorem bv_le_two (j : Nat) {s a : Nat} (ha : a ≤ 2) (s' : Nat) :
    Function.update (dig j) s a s' ≤ 2 := by
  by_cases h : s' = s
  · subst h; simp [ha]
  · rw [Function.update_of_ne h]; exact dig_le _ _

private theorem testBit_mv_core (y s v v' j : Nat) :
    (mv y s v v').testBit j = true ↔ ∃ K, K + v' * 3 ^ s = j + v * 3 ^ s ∧ y.testBit K = true := by
  unfold mv
  split
  · rename_i hvv
    rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, Nat.sub_mul]
    have : v * 3 ^ s ≤ v' * 3 ^ s := Nat.mul_le_mul_right _ hvv
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨_, by omega, h2⟩
    · rintro ⟨K, hK, h2⟩
      refine ⟨by omega, ?_⟩
      have e : j - (v' * 3 ^ s - v * 3 ^ s) = K := by omega
      rw [e]; exact h2
  · rename_i hvv
    rw [Nat.testBit_shiftRight, Nat.sub_mul]
    have : v' * 3 ^ s ≤ v * 3 ^ s := Nat.mul_le_mul_right _ (by omega)
    constructor
    · intro h; exact ⟨_, by omega, h⟩
    · rintro ⟨K, hK, h2⟩
      have e : v * 3 ^ s - v' * 3 ^ s + j = K := by omega
      rw [e]; exact h2

/-- Rewriting a digit. -/
private theorem testBit_mv {n y s v v' : Nat} (hs : s < n) (_hv : v ≤ 2) (hv' : v' ≤ 2)
    (hy : ∀ K, y.testBit K = true → K < 3 ^ n ∧ dig K s = v) (j : Nat) :
    (mv y s v v').testBit j = true ↔
      j < 3 ^ n ∧ dig j s = v' ∧ y.testBit (bv (Function.update (dig j) s v) n) = true := by
  rw [testBit_mv_core]
  constructor
  · rintro ⟨K, hK, hyK⟩
    obtain ⟨hKn, hKs⟩ := hy K hyK
    have hg : bv (dig K) n = K := bv_dig hKn
    have hu := bv_update (f := dig K) (a := v') hs
    have hle : ∀ s' < n, Function.update (dig K) s v' s' ≤ 2 := fun s' _ => bv_le_two K hv' s'
    have hj : j = bv (Function.update (dig K) s v') n := by rw [hKs, hg] at hu; omega
    have hdj : ∀ s' < n, dig j s' = Function.update (dig K) s v' s' := by
      intro s' hs'; rw [hj]; exact dig_bv hle s' hs'
    refine ⟨hj ▸ bv_lt hle, by rw [hdj s hs]; simp, ?_⟩
    rw [bv_congr (g := dig K), hg]
    · exact hyK
    intro s' hs'
    by_cases h : s' = s
    · subst h; simp [hKs]
    · rw [Function.update_of_ne h, hdj s' hs', Function.update_of_ne h]
  · rintro ⟨hj, hjs, hyK⟩
    refine ⟨_, ?_, hyK⟩
    have hu := bv_update (f := dig j) (a := v) hs
    rw [bv_dig hj, hjs] at hu; omega

/-- The digits kept by a digit rewrite. -/
private theorem mv_keep {n y s v v' s1 v1 : Nat} (hs : s < n) (hv : v ≤ 2) (hv' : v' ≤ 2)
    (hy : ∀ K, y.testBit K = true → K < 3 ^ n ∧ dig K s = v)
    (hs1 : s1 < n) (hne : s1 ≠ s) (hy1 : ∀ K, y.testBit K = true → dig K s1 = v1) (j : Nat)
    (hj : (mv y s v v').testBit j = true) : dig j s1 = v1 := by
  obtain ⟨hj, -, hK⟩ := (testBit_mv hs hv hv' hy j).1 hj
  have := hy1 _ hK
  rwa [dig_bv (fun s' _ => bv_le_two j hv s') s1 hs1, Function.update_of_ne hne] at this

/-- Selecting a digit. -/
private theorem testBit_sel {n x s v : Nat} (hs : s < n) (hv : v ≤ 2) (j : Nat) :
    (sel n x s v).testBit j = true ↔ x.testBit j = true ∧ j < 3 ^ n ∧ dig j s = v := by
  unfold sel
  rw [Nat.testBit_land, testBit_digitMask hs hv]
  simp [dig]

private theorem testBit_foldl_or (l : List Nat) (a j : Nat) :
    (l.foldl (· ||| ·) a).testBit j = true ↔ a.testBit j = true ∨ ∃ y ∈ l, y.testBit j = true := by
  induction l generalizing a with
  | nil => simp
  | cons y l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_or]
    simp only [Bool.or_eq_true, List.mem_cons, exists_eq_or_imp]
    tauto

private theorem testBit_ors (l : List Nat) (j : Nat) :
    (ors l).testBit j = true ↔ ∃ y ∈ l, y.testBit j = true := by
  rw [ors, testBit_foldl_or]; simp


private theorem mem_digits3 {u : Nat} : u ∈ digits3 ↔ u ≤ 2 := by
  simp only [digits3, List.mem_cons, List.not_mem_nil, or_false]; omega

/-- The transposition of `a` and `b`. -/
private def swp (a b s : Nat) : Nat := if s = a then b else if s = b then a else s

/-- Transposing two digits. -/
private theorem testBit_transp {n x a b : Nat} (ha : a < n) (hb : b < n) {j : Nat}
    (hj : j < 3 ^ n) :
    (transp n x a b).testBit j = x.testBit (bv (fun s => dig j (swp a b s)) n) := by
  unfold transp
  split
  · rename_i hab
    have hab : a = b := by simpa using hab
    subst hab
    rw [bv_congr (g := dig j), bv_dig hj]
    intro s _; unfold swp; split <;> simp_all
  rename_i hab
  have hab : a ≠ b := by simpa using hab
  rw [Bool.eq_iff_iff, testBit_ors]
  simp only [List.mem_flatMap, List.mem_map, mem_digits3]
  constructor
  · rintro ⟨_, ⟨u, hu, v, hv, rfl⟩, h⟩
    have hy : ∀ K, (sel n (sel n x a u) b v).testBit K = true →
        K < 3 ^ n ∧ dig K a = u ∧ dig K b = v ∧ x.testBit K = true := by
      intro K hK
      rw [testBit_sel hb hv, testBit_sel ha hu] at hK
      exact ⟨hK.2.1, hK.1.2.2, hK.2.2, hK.1.1⟩
    have hZ : ∀ K, (mv (sel n (sel n x a u) b v) a u v).testBit K = true →
        K < 3 ^ n ∧ dig K b = v := by
      intro K hK
      refine ⟨((testBit_mv ha hu hv (fun K h => ⟨(hy K h).1, (hy K h).2.1⟩) K).1 hK).1, ?_⟩
      exact mv_keep ha hu hv (fun K h => ⟨(hy K h).1, (hy K h).2.1⟩) hb (Ne.symm hab)
        (fun K h => (hy K h).2.2.1) K hK
    obtain ⟨-, hjb, h⟩ := (testBit_mv hb hv hu hZ j).1 h
    obtain ⟨hJ1, hJ1a, h⟩ := (testBit_mv ha hu hv
      (fun K h => ⟨(hy K h).1, (hy K h).2.1⟩) _).1 h
    have hle1 : ∀ s' < n, Function.update (dig j) b v s' ≤ 2 := fun s' _ => bv_le_two j hv s'
    rw [dig_bv hle1 a ha, Function.update_of_ne hab] at hJ1a
    have h := (hy _ h).2.2.2
    convert h using 2
    apply bv_congr
    intro s hs
    unfold swp
    by_cases h1 : s = a
    · subst h1; simp [hjb]
    · rw [Function.update_of_ne h1, dig_bv hle1 _ hs]
      by_cases h2 : s = b
      · subst h2; simp [h1, hJ1a]
      · simp [h1, h2]
  · intro h
    refine ⟨_, ⟨dig j b, dig_le _ _, dig j a, dig_le _ _, rfl⟩, ?_⟩
    have hy : ∀ K, (sel n (sel n x a (dig j b)) b (dig j a)).testBit K = true →
        K < 3 ^ n ∧ dig K a = dig j b ∧ dig K b = dig j a ∧ x.testBit K = true := by
      intro K hK
      rw [testBit_sel hb (dig_le _ _), testBit_sel ha (dig_le _ _)] at hK
      exact ⟨hK.2.1, hK.1.2.2, hK.2.2, hK.1.1⟩
    have hZ : ∀ K, (mv (sel n (sel n x a (dig j b)) b (dig j a)) a (dig j b) (dig j a)).testBit K
        = true → K < 3 ^ n ∧ dig K b = dig j a := by
      intro K hK
      refine ⟨((testBit_mv ha (dig_le _ _) (dig_le _ _)
        (fun K h => ⟨(hy K h).1, (hy K h).2.1⟩) K).1 hK).1, ?_⟩
      exact mv_keep ha (dig_le _ _) (dig_le _ _) (fun K h => ⟨(hy K h).1, (hy K h).2.1⟩) hb
        (Ne.symm hab) (fun K h => (hy K h).2.2.1) K hK
    refine (testBit_mv hb (dig_le _ _) (dig_le _ _) hZ j).2 ⟨hj, rfl, ?_⟩
    have hle1 : ∀ s' < n, Function.update (dig j) b (dig j a) s' ≤ 2 :=
      fun s' _ => bv_le_two j (dig_le _ _) s'
    refine (testBit_mv ha (dig_le _ _) (dig_le _ _)
      (fun K h => ⟨(hy K h).1, (hy K h).2.1⟩) _).2 ⟨bv_lt hle1, ?_, ?_⟩
    · rw [dig_bv hle1 a ha, Function.update_of_ne hab]
    have hle2 : ∀ s' < n, Function.update (dig (bv (Function.update (dig j) b (dig j a)) n)) a
        (dig j b) s' ≤ 2 := fun s' _ => bv_le_two _ (dig_le _ _) s'
    have e : bv (Function.update (dig (bv (Function.update (dig j) b (dig j a)) n)) a (dig j b)) n
        = bv (fun s => dig j (swp a b s)) n := by
      apply bv_congr
      intro s hs
      unfold swp
      by_cases h1 : s = a
      · subst h1; simp
      · rw [Function.update_of_ne h1, dig_bv hle1 _ hs]
        by_cases h2 : s = b
        · subst h2; simp [h1]
        · simp [h1, h2]
    rw [e]
    rw [testBit_sel hb (dig_le _ _), testBit_sel ha (dig_le _ _)]
    refine ⟨⟨h, bv_lt (fun s _ => dig_le _ _), ?_⟩, bv_lt (fun s _ => dig_le _ _), ?_⟩
    · rw [← e, dig_bv hle2 a ha]; simp
    · rw [← e, dig_bv hle2 b hb, Function.update_of_ne (Ne.symm hab), dig_bv hle1 b hb]; simp


private theorem testBit_mv_bv {n y s v v' : Nat} (hs : s < n) (hv : v ≤ 2) (hv' : v' ≤ 2)
    (hy : ∀ K, y.testBit K = true → K < 3 ^ n ∧ dig K s = v) {f : Nat → Nat}
    (hf : ∀ s' < n, f s' ≤ 2) :
    (mv y s v v').testBit (bv f n) = true ↔
      f s = v' ∧ y.testBit (bv (Function.update f s v) n) = true := by
  have e : bv (Function.update (dig (bv f n)) s v) n = bv (Function.update f s v) n := by
    apply bv_congr
    intro s' hs'
    by_cases h : s' = s
    · subst h; simp
    · rw [Function.update_of_ne h, Function.update_of_ne h, dig_bv hf s' hs']
  rw [testBit_mv hs hv hv' hy, dig_bv hf s hs, e]
  simp only [bv_lt hf, true_and]

private theorem testBit_sel_bv {n x s v : Nat} (hs : s < n) (hv : v ≤ 2) {f : Nat → Nat}
    (hf : ∀ s' < n, f s' ≤ 2) :
    (sel n x s v).testBit (bv f n) = true ↔ x.testBit (bv f n) = true ∧ f s = v := by
  rw [testBit_sel hs hv, dig_bv hf s hs]; simp [bv_lt hf]

private theorem update_le {f : Nat → Nat} {n s a : Nat} (hf : ∀ s' < n, f s' ≤ 2) (ha : a ≤ 2) :
    ∀ s' < n, Function.update f s a s' ≤ 2 := by
  intro s' hs'
  by_cases h : s' = s
  · subst h; simp [ha]
  · rw [Function.update_of_ne h]; exact hf s' hs'

/-! ### Slots and traces -/

/-- The digits of a trace in the slot layout `ord`. -/
private def dfun : List Nat → Colseq → Nat → Nat
  | s0 :: ord, c :: t, s => if s = s0 then cdig c else dfun ord t s
  | _, _, _ => 0

private theorem cdig_le (c : Color) : cdig c ≤ 2 := by cases c <;> decide

private theorem dfun_le (ord : List Nat) (t : Colseq) (s : Nat) : dfun ord t s ≤ 2 := by
  induction ord generalizing t with
  | nil => simp [dfun]
  | cons s0 ord ih =>
    cases t with
    | nil => simp [dfun]
    | cons c t => simp only [dfun]; split; exact cdig_le c; exact ih t

private theorem dfun_not_mem {ord : List Nat} {s : Nat} (h : s ∉ ord) (t : Colseq) :
    dfun ord t s = 0 := by
  induction ord generalizing t with
  | nil => simp [dfun]
  | cons s0 ord ih =>
    cases t with
    | nil => simp [dfun]
    | cons c t =>
      simp only [List.mem_cons, not_or] at h
      simp only [dfun, ite_eq_right h.1]; exact ih h.2 t

private theorem dfun_cons (s0 : Nat) (ord : List Nat) (c : Color) (t : Colseq) :
    dfun (s0 :: ord) (c :: t) = Function.update (dfun ord t) s0 (cdig c) := by
  funext s; simp only [dfun, Function.update_apply]

/-- Slot lists: distinct slots below `n`. -/
private def Slots (n : Nat) (ord : List Nat) : Prop := ord.Nodup ∧ ∀ s ∈ ord, s < n

private theorem bv_zero : ∀ n, bv (fun _ => 0) n = 0
  | 0 => rfl
  | n + 1 => by simp [bv, bv_zero n]

private theorem slotIdx_eq {n : Nat} {ord : List Nat} (h : Slots n ord) (t : Colseq) :
    slotIdx ord t = bv (dfun ord t) n := by
  induction ord generalizing t with
  | nil =>
    rw [bv_congr (g := fun _ => 0), bv_zero]
    · cases t <;> rfl
    · intro s _; cases t <;> rfl
  | cons s0 ord ih =>
    obtain ⟨hnd, hlt⟩ := h
    rw [List.nodup_cons] at hnd
    have h' : Slots n ord := ⟨hnd.2, fun s hs => hlt s (List.mem_cons_of_mem _ hs)⟩
    cases t with
    | nil =>
      rw [bv_congr (g := fun _ => 0), bv_zero]
      · rfl
      · intro s _; rfl
    | cons c t =>
      simp only [slotIdx]
      rw [dfun_cons, ih h' t]
      have := bv_update (f := dfun ord t) (a := cdig c) (hlt s0 (by simp))
      rw [dfun_not_mem hnd.1] at this
      omega

private theorem slotIdx_lt {n : Nat} {ord : List Nat} (h : Slots n ord) (t : Colseq) :
    slotIdx ord t < 3 ^ n := by
  rw [slotIdx_eq h]; exact bv_lt (fun s _ => dfun_le _ _ _)

private theorem perm_range_iff {n : Nat} {ord : List Nat} :
    ord.Perm (List.range n) ↔ Slots n ord ∧ ord.length = n := by
  constructor
  · intro h
    refine ⟨⟨h.nodup_iff.2 List.nodup_range, fun s hs => by simpa using h.subset hs⟩, ?_⟩
    rw [h.length_eq, List.length_range]
  · rintro ⟨⟨hnd, hlt⟩, hlen⟩
    exact (List.subperm_of_subset hnd (fun s hs => by simpa using hlt s hs)).perm_of_length_le
      (by simp [hlen])

private theorem exists_dig {P : Nat → Prop} :
    (∃ v, v ≤ 2 ∧ P v) ↔ ∃ c, c ≠ Color0 ∧ P (cdig c) := by
  constructor
  · rintro ⟨v, hv, h⟩
    rcases (show v = 0 ∨ v = 1 ∨ v = 2 by omega) with rfl | rfl | rfl
    · exact ⟨Color1, by decide, h⟩
    · exact ⟨Color2, by decide, h⟩
    · exact ⟨Color3, by decide, h⟩
  · rintro ⟨c, -, h⟩; exact ⟨_, cdig_le c, h⟩


private theorem sel_supp {n x s v : Nat} (hs : s < n) (hv : v ≤ 2) :
    ∀ K, (sel n x s v).testBit K = true → K < 3 ^ n ∧ dig K s = v := by
  intro K hK; rw [testBit_sel hs hv] at hK; exact hK.2

private theorem dfun_map_swp {s top : Nat} {ord : List Nat} (hs : s ∉ ord) (t : Colseq)
    (s' : Nat) :
    dfun (ord.map fun o => if o == top then s else o) t (swp s top s') = dfun ord t s' := by
  induction ord generalizing t with
  | nil => cases t <;> rfl
  | cons o ord ih =>
    simp only [List.mem_cons, not_or] at hs
    cases t with
    | nil => rfl
    | cons c t =>
      simp only [List.map_cons, dfun]
      have e : (swp s top s' = if o == top then s else o) ↔ s' = o := by
        unfold swp
        have := hs.1
        by_cases h1 : o = top <;> simp only [h1, beq_self_eq_true, ite_true, beq_iff_eq,
          ite_false] <;> split_ifs <;> omega
      by_cases h : s' = o
      · rw [ite_eq_left (e.2 h), ite_eq_left h]
      · rw [ite_eq_right (fun h' => h (e.1 h')), ite_eq_right h, ih hs.2]

private theorem slots_mono {n m : Nat} {ord : List Nat} (h : Slots n ord) (hnm : n ≤ m) :
    Slots m ord := ⟨h.1, fun s hs => by have := h.2 s hs; omega⟩

private theorem slots_kill {n s : Nat} {ord : List Nat} (h : Slots n (s :: ord)) :
    Slots (n - 1) (ord.map fun o => if o == n - 1 then s else o) := by
  obtain ⟨hnd, hlt⟩ := h
  rw [List.nodup_cons] at hnd
  have hsn := hlt s (by simp)
  refine ⟨hnd.2.map_on ?_, ?_⟩
  · intro a ha b hb hab
    have h1 : a ≠ s := fun e => hnd.1 (e ▸ ha)
    have h2 : b ≠ s := fun e => hnd.1 (e ▸ hb)
    by_cases h3 : a = n - 1 <;> by_cases h4 : b = n - 1 <;>
      simp only [h3, h4, beq_self_eq_true, ite_true, beq_iff_eq, ite_false] at hab <;> omega
  · intro o ho
    rw [List.mem_map] at ho
    obtain ⟨a, ha, rfl⟩ := ho
    have h1 : a ≠ s := fun e => hnd.1 (e ▸ ha)
    have h2 := hlt a (by simp [ha])
    by_cases h3 : a = n - 1
    · simp only [h3, beq_self_eq_true, ite_true]; omega
    · simp only [beq_iff_eq, h3, ite_false]; omega

/-- Killing a slot: the traces of the result are the traces of the input without the killed
position. -/
private theorem killSlot_den {st : DPState} {s : Nat} (h : Slots st.len (s :: st.ord))
    (t : Colseq) :
    (killSlot st s).den t ↔ ∃ c, (⟨st.len, s :: st.ord, st.x⟩ : DPState).den (c :: t) := by
  obtain ⟨ℓ, ord, x⟩ := st
  simp only at h
  have hsl := h.2 s (by simp)
  have hs : s ∉ ord := (List.nodup_cons.1 h.1).1
  have hk := slots_kill h
  have hk' := slots_mono hk (Nat.sub_le ℓ 1)
  have hsl' : Slots ℓ ord := ⟨(List.nodup_cons.1 h.1).2, fun o ho => h.2 o (by simp [ho])⟩
  unfold killSlot DPState.den
  simp only
  rw [Nat.testBit_land, testBit_ones, decide_eq_true (slotIdx_lt hk t),
    Bool.and_true, testBit_transp hsl (by omega) (slotIdx_lt hk' t)]
  have e1 : bv (fun s' => dig (slotIdx (ord.map fun o => if o == ℓ - 1 then s else o) t)
      (swp s (ℓ - 1) s')) ℓ = bv (dfun ord t) ℓ := by
    apply bv_congr
    intro s' hs'
    have : swp s (ℓ - 1) s' < ℓ := by unfold swp; split_ifs <;> omega
    rw [slotIdx_eq hk', dig_bv (fun _ _ => dfun_le _ _ _) _ this, dfun_map_swp hs]
  rw [e1, testBit_ors]
  simp only [List.mem_map, mem_digits3]
  have hF : ∀ s' < ℓ, dfun ord t s' ≤ 2 := fun _ _ => dfun_le _ _ _
  constructor
  · rintro ⟨hlen, h0, _, ⟨v, hv, rfl⟩, hb⟩
    rw [testBit_mv_bv hsl hv (by omega) (sel_supp hsl hv) hF,
      testBit_sel_bv hsl hv (update_le hF hv)] at hb
    obtain ⟨c, hc, hb⟩ := (exists_dig (P := fun v =>
      x.testBit (bv (Function.update (dfun ord t) s v) ℓ) = true)).1 ⟨v, hv, hb.2.1⟩
    refine ⟨c, by simp; omega, by simp [Ne.symm hc, h0], ?_⟩
    rw [slotIdx_eq h, dfun_cons]
    exact hb
  · rintro ⟨c, hlen, h0, hb⟩
    simp only [List.mem_cons, not_or] at h0
    refine ⟨by simp at hlen; omega, h0.2, _, ⟨cdig c, cdig_le c, rfl⟩, ?_⟩
    rw [testBit_mv_bv hsl (cdig_le c) (by omega) (sel_supp hsl (cdig_le c)) hF,
      testBit_sel_bv hsl (cdig_le c) (update_le hF (cdig_le c))]
    rw [slotIdx_eq h, dfun_cons] at hb
    exact ⟨dfun_not_mem hs t, hb, by simp⟩


/-! ### Traces, colors and slot indices -/

private theorem slotIdx_append {A B : List Nat} {C' D : Colseq}
    (h : A.length = C'.length) : slotIdx (A ++ B) (C' ++ D) = slotIdx A C' + slotIdx B D := by
  induction A generalizing C' with
  | nil =>
    cases C' with
    | nil => simp [slotIdx]
    | cons _ _ => simp at h
  | cons s A ih =>
    cases C' with
    | nil => simp at h
    | cons c C' =>
      simp only [List.cons_append, slotIdx, List.length_cons] at h ⊢
      rw [ih (by omega)]; omega

private theorem slotIdx_rot (n : Nat) {ord : List Nat} {t : Colseq} (h : ord.length = t.length) :
    slotIdx (rot n ord) (rot n t) = slotIdx ord t := by
  unfold rot
  conv_rhs => rw [← List.take_append_drop n ord, ← List.take_append_drop n t]
  rw [slotIdx_append (by simp [h]), slotIdx_append (by simp [h])]
  omega

private theorem slotIdx_snoc {A : List Nat} {u : Colseq} (h : A.length = u.length) (s : Nat)
    (c : Color) : slotIdx (A ++ [s]) (u ++ [c]) = slotIdx (s :: A) (c :: u) := by
  rw [slotIdx_append h]; simp only [slotIdx]; omega

private theorem slotIdx_swap (s0 s1 : Nat) (ord : List Nat) (a b : Color) (t : Colseq) :
    slotIdx (s1 :: s0 :: ord) (b :: a :: t) = slotIdx (s0 :: s1 :: ord) (a :: b :: t) := by
  simp only [slotIdx]; omega

private def Supp (n x : Nat) : Prop := ∀ j, x.testBit j = true → j < n

private theorem supp_iff {n x : Nat} : Supp n x ↔ x < 2 ^ n := by
  constructor
  · intro h
    apply Nat.lt_pow_two_of_testBit
    intro i hi
    by_contra h'
    have := h i (by simpa using h')
    omega
  · intro h j hj
    by_contra h'
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num)
      (by omega)))] at hj
    exact absurd hj (by simp)

private theorem supp_ors {n : Nat} {l : List Nat} (h : ∀ y ∈ l, Supp n y) : Supp n (ors l) := by
  intro j hj
  obtain ⟨y, hy, hj⟩ := (testBit_ors l j).1 hj
  exact h y hy j hj

/-- Shifting by whole top digits. -/
private theorem testBit_shift_top {P z w b J : Nat} (hz : Supp P z) (hJ : J < P) :
    (z <<< (w * P)).testBit (J + b * P) = true ↔ w = b ∧ z.testBit J = true := by
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩
    have hwb : w ≤ b := by
      by_contra h
      have : (b + 1) * P ≤ w * P := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    rcases Nat.lt_or_eq_of_le hwb with hwb | rfl
    · have := hz _ h2
      have : (w + 1) * P ≤ b * P := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.add_mul, Nat.one_mul] at this; omega
    · refine ⟨rfl, ?_⟩
      have e : J + w * P - w * P = J := by omega
      rwa [e] at h2
  · rintro ⟨rfl, h⟩
    refine ⟨by omega, ?_⟩
    have e : J + w * P - w * P = J := by omega
    rwa [e]

private theorem supp_shift {P z w : Nat} (hz : Supp P z) : Supp ((w + 1) * P) (z <<< (w * P)) := by
  intro j hj
  rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at hj
  have := hz _ hj.2
  rw [Nat.add_mul, Nat.one_mul]; omega

private theorem supp_mv {n y s v v' : Nat} (hs : s < n) (hv : v ≤ 2) (hv' : v' ≤ 2)
    (hy : ∀ K, y.testBit K = true → K < 3 ^ n ∧ dig K s = v) : Supp (3 ^ n) (mv y s v v') :=
  fun j hj => ((testBit_mv hs hv hv' hy j).1 hj).1

private theorem cdig_inj {a b : Color} (ha : a ≠ Color0) (hb : b ≠ Color0) :
    cdig a = cdig b ↔ a = b := by
  cases a <;> cases b <;> simp_all [cdig]

private theorem cdig_p231 {c : Color} (hc : c ≠ Color0) : cdig (permc Eperm231 c) = p231 (cdig c) := by
  cases c <;> simp_all [cdig, permc, palette, p231]

private theorem cdig_p312 {c : Color} (hc : c ≠ Color0) : cdig (permc Eperm312 c) = p312 (cdig c) := by
  cases c <;> simp_all [cdig, permc, palette, p312]

private theorem permc_ne0 {g : EdgePerm} {c : Color} (hc : c ≠ Color0) : permc g c ≠ Color0 := by
  cases g <;> cases c <;> simp_all [permc, palette]

private theorem cdig_addc {a b : Color} (ha : a ≠ Color0) (hb : b ≠ Color0) (hab : a ≠ b) :
    cdig (addc a b) = addd (cdig a) (cdig b) ∧ addc a b ≠ Color0 := by
  cases a <;> cases b <;> simp_all [cdig, addc, palette, addd]

private theorem den_zero {ℓ : Nat} {ord : List Nat} (t : Colseq) :
    ¬ (⟨ℓ, ord, 0⟩ : DPState).den t := by
  simp [DPState.den]

/-! ### The steps -/

private theorem den_rot {ℓ : Nat} {ord : List Nat} {x : Nat} (hlen : ord.length = ℓ) (n : Nat)
    (t : Colseq) : (⟨ℓ, rot n ord, x⟩ : DPState).den t ↔
      ∃ t0, (⟨ℓ, ord, x⟩ : DPState).den t0 ∧ t = rot n t0 := by
  simp only [DPState.den]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨rotr n t, ⟨by simp [h1], by simpa using h2, ?_⟩, (rotrK n t).symm⟩
    rw [← slotIdx_rot n (by simp [hlen, h1]), rotrK]; exact h3
  · rintro ⟨t0, ⟨h1, h2, h3⟩, rfl⟩
    refine ⟨by simp [h1], by simpa using h2, ?_⟩
    rw [slotIdx_rot n (by simp [hlen, h1])]; exact h3


private theorem p231_le (v : Nat) : p231 v ≤ 2 := by unfold p231; split <;> omega
private theorem p312_le (v : Nat) : p312 v ≤ 2 := by unfold p312; split <;> omega

private theorem stepR {ℓ : Nat} {ord : List Nat} {x : Nat} (hlen : ord.length = ℓ) (n : Nat)
    (t : Colseq) : (dpStep ⟨ℓ, ord, x⟩ (.R n)).den t ↔
      ∃ t0, (⟨ℓ, ord, x⟩ : DPState).den t0 ∧ t ∈ cpsucc (.R n) t0 := by
  show (⟨ℓ, rot n ord, x⟩ : DPState).den t ↔ _
  rw [den_rot hlen]
  simp only [cpsucc, List.mem_singleton]

private theorem stepR' {ℓ : Nat} {ord : List Nat} {x : Nat} (hlen : ord.length = ℓ)
    (t : Colseq) : (dpStep ⟨ℓ, ord, x⟩ .R').den t ↔
      ∃ t0, (⟨ℓ, ord, x⟩ : DPState).den t0 ∧ t ∈ cpsucc .R' t0 := by
  simp only [dpStep, cpsucc]
  split
  · rename_i h1
    simp only [den_zero, false_iff, not_exists, not_and]
    intro t0 h0
    have hl0 : t0.length = ℓ := h0.1
    have : t0.length ≤ 1 := by omega
    simp [this]
  · rename_i h1
    have e : rotr 1 ord = rot (ℓ - 1) ord := by rw [rotr, hlen]
    rw [e, den_rot hlen]
    constructor
    · rintro ⟨t0, h0, rfl⟩
      refine ⟨t0, h0, ?_⟩
      have hl0 : t0.length = ℓ := h0.1
      have : 1 < ℓ := by omega
      simp [this, rotr, hl0]
    · rintro ⟨t0, h0, ht⟩
      have hl0 : t0.length = ℓ := h0.1
      have : ¬ t0.length ≤ 1 := by omega
      simp only [this, ite_false, List.mem_singleton] at ht
      exact ⟨t0, h0, by rw [ht, rotr, hl0]⟩

private theorem stepU {ℓ : Nat} {ord : List Nat} {x : Nat} (hsl : Slots ℓ ord)
    (hx : x < 2 ^ 3 ^ ℓ) (t : Colseq) : (dpStep ⟨ℓ, ord, x⟩ .U).den t ↔
      ∃ t0, (⟨ℓ, ord, x⟩ : DPState).den t0 ∧ t ∈ cpsucc .U t0 := by
  simp only [dpStep, DPState.den, cpsucc]
  have hz : Supp (3 ^ ℓ) x := supp_iff.2 hx
  constructor
  · rintro ⟨hlen, h0, hb⟩
    match t, hlen, h0, hb with
    | a :: b :: e, hlen, h0, hb =>
      simp only [List.mem_cons, not_or] at h0
      have ei : slotIdx (ℓ :: (ℓ + 1) :: ord) (a :: b :: e) =
          slotIdx ord e + (cdig a + 3 * cdig b) * 3 ^ ℓ := by
        simp only [slotIdx, Nat.pow_succ]; ring
      rw [ei, testBit_ors] at hb
      simp only [List.mem_map, mem_digits3] at hb
      obtain ⟨_, ⟨v, hv, rfl⟩, hb⟩ := hb
      have es : v * 3 ^ ℓ + v * 3 ^ (ℓ + 1) = (4 * v) * 3 ^ ℓ := by rw [Nat.pow_succ]; ring
      rw [es, testBit_shift_top hz (slotIdx_lt hsl e)] at hb
      have ha := cdig_le a
      have hb' := cdig_le b
      have hab : cdig a = cdig b := by omega
      rw [cdig_inj (Ne.symm h0.1) (Ne.symm h0.2.1)] at hab
      subst hab
      refine ⟨e, ⟨by simp at hlen; omega, h0.2.2, hb.2⟩, ?_⟩
      cases a <;> simp_all
  · rintro ⟨t0, ⟨hlen, h0, hb⟩, ht⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    have key : ∀ c, c ≠ Color0 → t = c :: c :: t0 →
        List.length t = ℓ + 2 ∧ Color0 ∉ t ∧
        (ors (List.map (fun v => x <<< (v * 3 ^ ℓ + v * 3 ^ (ℓ + 1))) digits3)).testBit
          (slotIdx (ℓ :: (ℓ + 1) :: ord) t) = true := by
      rintro c hc rfl
      refine ⟨by simp [hlen], by simp [Ne.symm hc, h0], ?_⟩
      have ei : slotIdx (ℓ :: (ℓ + 1) :: ord) (c :: c :: t0) =
          slotIdx ord t0 + (4 * cdig c) * 3 ^ ℓ := by
        simp only [slotIdx, Nat.pow_succ]; ring
      rw [ei, testBit_ors]
      refine ⟨_, List.mem_map.2 ⟨cdig c, mem_digits3.2 (cdig_le c), rfl⟩, ?_⟩
      have es : cdig c * 3 ^ ℓ + cdig c * 3 ^ (ℓ + 1) = (4 * cdig c) * 3 ^ ℓ := by
        rw [Nat.pow_succ]; ring
      rw [es, testBit_shift_top hz (slotIdx_lt hsl t0)]
      exact ⟨rfl, hb⟩
    rcases ht with ht | ht | ht
    · exact key Color1 (by decide) ht
    · exact key Color2 (by decide) ht
    · exact key Color3 (by decide) ht


private theorem dig_col {v : Nat} (hv : v ≤ 2) : ∃ c, c ≠ Color0 ∧ cdig c = v := by
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 by omega) with rfl | rfl | rfl
  · exact ⟨Color1, by decide, rfl⟩
  · exact ⟨Color2, by decide, rfl⟩
  · exact ⟨Color3, by decide, rfl⟩

private theorem mv_sel_head {ℓ x s0 w : Nat} {rest : List Nat} (hsl : Slots ℓ (s0 :: rest))
    (c : Color) (hw : w ≤ 2) (a : Color) (e : Colseq) :
    (mv (sel ℓ x s0 (cdig c)) s0 (cdig c) w).testBit (slotIdx (s0 :: rest) (a :: e)) = true ↔
      cdig a = w ∧ x.testBit (slotIdx (s0 :: rest) (c :: e)) = true := by
  have hs0 := hsl.2 s0 (by simp)
  rw [slotIdx_eq hsl, slotIdx_eq hsl, testBit_mv_bv hs0 (cdig_le c) hw (sel_supp hs0 (cdig_le c))
    (fun _ _ => dfun_le _ _ _), testBit_sel_bv hs0 (cdig_le c)
    (update_le (fun _ _ => dfun_le _ _ _) (cdig_le c))]
  simp only [dfun_cons, Function.update_self, Function.update_idem, and_true]

private theorem stepY {ℓ s0 : Nat} {rest : List Nat} {x : Nat} (hsl : Slots ℓ (s0 :: rest))
    (hlen : (s0 :: rest).length = ℓ) (t : Colseq) : (dpStep ⟨ℓ, s0 :: rest, x⟩ .Y).den t ↔
      ∃ t0, (⟨ℓ, s0 :: rest, x⟩ : DPState).den t0 ∧ t ∈ cpsucc .Y t0 := by
  have hs0 := hsl.2 s0 (by simp)
  have hsup : ∀ v w, v ≤ 2 → w ≤ 2 → Supp (3 ^ ℓ) (mv (sel ℓ x s0 v) s0 v w) :=
    fun v w hv hw => supp_mv hs0 hv hw (sel_supp hs0 hv)
  have ei : ∀ a b e, slotIdx (s0 :: ℓ :: rest) (a :: b :: e) =
      slotIdx (s0 :: rest) (a :: e) + cdig b * 3 ^ ℓ := by
    intro a b e; simp only [slotIdx]; ring
  simp only [dpStep, DPState.den]
  constructor
  · rintro ⟨hl, h0, hb⟩
    match t, hl, h0, hb with
    | [_], hl, _, _ => simp at hl hlen; omega
    | a :: b :: e, hl, h0, hb =>
      simp only [List.mem_cons, not_or] at h0
      rw [ei, testBit_ors] at hb
      simp only [List.mem_map, mem_digits3] at hb
      obtain ⟨_, ⟨v, hv, rfl⟩, hb⟩ := hb
      obtain ⟨c, hc, rfl⟩ := dig_col hv
      have hJ := slotIdx_lt hsl (a :: e)
      rw [Nat.testBit_or, Bool.or_eq_true, testBit_shift_top (hsup _ _ hv (p231_le _)) hJ,
        testBit_shift_top (hsup _ _ hv (p312_le _)) hJ, mv_sel_head hsl c (p231_le _),
        mv_sel_head hsl c (p312_le _), ← cdig_p231 hc, ← cdig_p312 hc,
        cdig_inj (Ne.symm h0.1) (permc_ne0 hc), cdig_inj (permc_ne0 hc) (Ne.symm h0.2.1),
        cdig_inj (Ne.symm h0.1) (permc_ne0 hc), cdig_inj (permc_ne0 hc) (Ne.symm h0.2.1)] at hb
      refine ⟨c :: e, ⟨by simp at hl ⊢; omega, by simp [Ne.symm hc, h0.2.2], ?_⟩, ?_⟩
      · rcases hb with hb | hb
        · exact hb.2.2
        · exact hb.2.2
      · simp only [cpsucc, List.mem_cons, List.not_mem_nil, or_false]
        rcases hb with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
  · rintro ⟨t0, ⟨hl, h0, hb⟩, ht⟩
    match t0, hl, h0, hb, ht with
    | [], hl, _, _, _ => simp at hl hlen; omega
    | c :: e, hl, h0, hb, ht =>
      simp only [List.mem_cons, not_or] at h0
      have hc : c ≠ Color0 := Ne.symm h0.1
      simp only [cpsucc, List.mem_cons, List.not_mem_nil, or_false] at ht
      have key : ∀ a b, (a = permc Eperm231 c ∧ b = permc Eperm312 c) ∨
          (a = permc Eperm312 c ∧ b = permc Eperm231 c) →
          List.length (a :: b :: e) = ℓ + 1 ∧ Color0 ∉ a :: b :: e ∧
          (ors (List.map (fun v => mv (sel ℓ x s0 v) s0 v (p231 v) <<< (p312 v * 3 ^ ℓ) |||
            mv (sel ℓ x s0 v) s0 v (p312 v) <<< (p231 v * 3 ^ ℓ)) digits3)).testBit
            (slotIdx (s0 :: ℓ :: rest) (a :: b :: e)) = true := by
        intro a b hab
        have ha : a ≠ Color0 := by rcases hab with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact permc_ne0 hc
        have hb' : b ≠ Color0 := by rcases hab with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> exact permc_ne0 hc
        refine ⟨by simp at hl ⊢; omega, by simp [Ne.symm ha, Ne.symm hb', h0.2], ?_⟩
        rw [ei, testBit_ors]
        refine ⟨_, List.mem_map.2 ⟨cdig c, mem_digits3.2 (cdig_le c), rfl⟩, ?_⟩
        have hJ := slotIdx_lt hsl (a :: e)
        rw [Nat.testBit_or, Bool.or_eq_true, testBit_shift_top (hsup _ _ (cdig_le c) (p231_le _)) hJ,
          testBit_shift_top (hsup _ _ (cdig_le c) (p312_le _)) hJ, mv_sel_head hsl c (p231_le _),
          mv_sel_head hsl c (p312_le _), ← cdig_p231 hc, ← cdig_p312 hc]
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl, hb⟩
        · exact Or.inr ⟨rfl, rfl, hb⟩
      rcases ht with rfl | rfl
      · exact key _ _ (Or.inl ⟨rfl, rfl⟩)
      · exact key _ _ (Or.inr ⟨rfl, rfl⟩)


private theorem dfun_cons2 {s0 s1 : Nat} (_hne : s0 ≠ s1) (rest : List Nat) (a b : Color)
    (e : Colseq) (v1 v2 : Nat) :
    Function.update (Function.update (dfun (s0 :: s1 :: rest) (a :: b :: e)) s1 v2) s0 v1 =
      Function.update (Function.update (dfun rest e) s1 v2) s0 v1 := by
  rw [dfun_cons, dfun_cons]
  funext s
  simp only [Function.update_apply]
  split_ifs <;> rfl

private theorem mv2_head {ℓ x s0 s1 w1 w2 : Nat} {rest : List Nat}
    (hsl : Slots ℓ (s0 :: s1 :: rest)) (c1 c2 : Color) (hw1 : w1 ≤ 2) (hw2 : w2 ≤ 2)
    (a b : Color) (e : Colseq) :
    (mv (mv (sel ℓ (sel ℓ x s0 (cdig c1)) s1 (cdig c2)) s0 (cdig c1) w1) s1 (cdig c2) w2).testBit
      (slotIdx (s0 :: s1 :: rest) (a :: b :: e)) = true ↔
      cdig a = w1 ∧ cdig b = w2 ∧ x.testBit (slotIdx (s0 :: s1 :: rest) (c1 :: c2 :: e)) = true := by
  have hs0 := hsl.2 s0 (by simp)
  have hs1 := hsl.2 s1 (by simp)
  have hne : s0 ≠ s1 := by
    have := hsl.1; simp only [List.nodup_cons, List.mem_cons, not_or] at this; exact this.1.1
  have hv1 := cdig_le c1
  have hv2 := cdig_le c2
  have hy : ∀ K, (sel ℓ (sel ℓ x s0 (cdig c1)) s1 (cdig c2)).testBit K = true →
      K < 3 ^ ℓ ∧ dig K s0 = cdig c1 ∧ dig K s1 = cdig c2 := by
    intro K hK
    rw [testBit_sel hs1 hv2, testBit_sel hs0 hv1] at hK
    exact ⟨hK.2.1, hK.1.2.2, hK.2.2⟩
  have hZ : ∀ K, (mv (sel ℓ (sel ℓ x s0 (cdig c1)) s1 (cdig c2)) s0 (cdig c1) w1).testBit K
      = true → K < 3 ^ ℓ ∧ dig K s1 = cdig c2 := by
    intro K hK
    refine ⟨((testBit_mv hs0 hv1 hw1 (fun K h => ⟨(hy K h).1, (hy K h).2.1⟩) K).1 hK).1, ?_⟩
    exact mv_keep hs0 hv1 hw1 (fun K h => ⟨(hy K h).1, (hy K h).2.1⟩) hs1 (Ne.symm hne)
      (fun K h => (hy K h).2.2) K hK
  have hF : ∀ s' < ℓ, dfun (s0 :: s1 :: rest) (a :: b :: e) s' ≤ 2 := fun _ _ => dfun_le _ _ _
  rw [slotIdx_eq hsl, slotIdx_eq hsl, testBit_mv_bv hs1 hv2 hw2 hZ hF,
    testBit_mv_bv hs0 hv1 hw1 (fun K h => ⟨(hy K h).1, (hy K h).2.1⟩) (update_le hF hv2),
    testBit_sel_bv hs1 hv2 (update_le (update_le hF hv2) hv1),
    testBit_sel_bv hs0 hv1 (update_le (update_le hF hv2) hv1), dfun_cons2 hne]
  have e2 : dfun (s0 :: s1 :: rest) (c1 :: c2 :: e) =
      Function.update (Function.update (dfun rest e) s1 (cdig c2)) s0 (cdig c1) := by
    rw [dfun_cons, dfun_cons]
  rw [e2]
  simp only [dfun_cons, Function.update_self, Function.update_of_ne hne,
    Function.update_of_ne (Ne.symm hne)]
  tauto


private theorem stepH {ℓ s0 s1 : Nat} {rest : List Nat} {x : Nat}
    (hsl : Slots ℓ (s0 :: s1 :: rest)) (hlen : (s0 :: s1 :: rest).length = ℓ) (t : Colseq) :
    (dpStep ⟨ℓ, s0 :: s1 :: rest, x⟩ .H).den t ↔
      ∃ t0, (⟨ℓ, s0 :: s1 :: rest, x⟩ : DPState).den t0 ∧ t ∈ cpsucc .H t0 := by
  have hchar : ∀ a b e, (ors (digits3.flatMap fun v1 => digits3.map fun v2 =>
      let y := sel ℓ (sel ℓ x s0 v1) s1 v2
      if v1 == v2 then
        mv (mv y s0 v1 (p231 v1)) s1 v2 (p231 v1) ||| mv (mv y s0 v1 (p312 v1)) s1 v2 (p312 v1)
      else mv (mv y s0 v1 v2) s1 v2 v1)).testBit (slotIdx (s0 :: s1 :: rest) (a :: b :: e)) = true
      ↔ ∃ c1 c2, c1 ≠ Color0 ∧ c2 ≠ Color0 ∧
        x.testBit (slotIdx (s0 :: s1 :: rest) (c1 :: c2 :: e)) = true ∧
        (if c1 = c2 then (cdig a = p231 (cdig c1) ∧ cdig b = p231 (cdig c1)) ∨
          (cdig a = p312 (cdig c1) ∧ cdig b = p312 (cdig c1))
        else cdig a = cdig c2 ∧ cdig b = cdig c1) := by
    intro a b e
    rw [testBit_ors]
    simp only [List.mem_flatMap, List.mem_map, mem_digits3]
    constructor
    · rintro ⟨_, ⟨v1, hv1, v2, hv2, rfl⟩, h⟩
      obtain ⟨c1, hc1, rfl⟩ := dig_col hv1
      obtain ⟨c2, hc2, rfl⟩ := dig_col hv2
      refine ⟨c1, c2, hc1, hc2, ?_⟩
      by_cases h12 : c1 = c2
      · subst h12
        simp only [beq_self_eq_true, ite_true, Nat.testBit_or, Bool.or_eq_true,
          mv2_head hsl c1 c1 (p231_le _) (p231_le _), mv2_head hsl c1 c1 (p312_le _) (p312_le _)] at h
        rw [ite_eq_left rfl]
        rcases h with h | h
        · exact ⟨h.2.2, Or.inl ⟨h.1, h.2.1⟩⟩
        · exact ⟨h.2.2, Or.inr ⟨h.1, h.2.1⟩⟩
      · have : (cdig c1 == cdig c2) = false := by
          rw [beq_eq_false_iff_ne, Ne, cdig_inj hc1 hc2]; exact h12
        simp only [this, Bool.false_eq_true, ite_false,
          mv2_head hsl c1 c2 (cdig_le _) (cdig_le _)] at h
        simp only [h12, ite_false]
        exact ⟨h.2.2, h.1, h.2.1⟩
    · rintro ⟨c1, c2, hc1, hc2, hx, h⟩
      refine ⟨_, ⟨cdig c1, cdig_le _, cdig c2, cdig_le _, rfl⟩, ?_⟩
      by_cases h12 : c1 = c2
      · subst h12
        simp only [ite_true] at h
        simp only [beq_self_eq_true, ite_true, Nat.testBit_or, Bool.or_eq_true,
          mv2_head hsl c1 c1 (p231_le _) (p231_le _), mv2_head hsl c1 c1 (p312_le _) (p312_le _)]
        rcases h with h | h
        · exact Or.inl ⟨h.1, h.2, hx⟩
        · exact Or.inr ⟨h.1, h.2, hx⟩
      · have : (cdig c1 == cdig c2) = false := by
          rw [beq_eq_false_iff_ne, Ne, cdig_inj hc1 hc2]; exact h12
        simp only [h12, ite_false] at h
        simp only [this, Bool.false_eq_true, ite_false,
          mv2_head hsl c1 c2 (cdig_le _) (cdig_le _)]
        exact ⟨h.1, h.2, hx⟩
  simp only [dpStep, DPState.den]
  constructor
  · rintro ⟨hl, h0, hb⟩
    match t, hl, h0, hb with
    | [], hl, _, _ => simp at hl hlen; omega
    | [_], hl, _, _ => simp at hl hlen; omega
    | a :: b :: e, hl, h0, hb =>
      simp only [List.mem_cons, not_or] at h0
      have ha : a ≠ Color0 := Ne.symm h0.1
      have hb0 : b ≠ Color0 := Ne.symm h0.2.1
      obtain ⟨c1, c2, hc1, hc2, hx, h⟩ := (hchar a b e).1 hb
      refine ⟨c1 :: c2 :: e, ⟨by simp at hl ⊢; omega, by simp [Ne.symm hc1, Ne.symm hc2, h0.2.2],
        hx⟩, ?_⟩
      simp only [cpsucc]
      by_cases h12 : c1 = c2
      · subst h12
        simp only [ite_true, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
        rw [← cdig_p231 hc1, ← cdig_p312 hc1, cdig_inj ha (permc_ne0 hc1),
          cdig_inj hb0 (permc_ne0 hc1), cdig_inj ha (permc_ne0 hc1),
          cdig_inj hb0 (permc_ne0 hc1)] at h
        rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr rfl
      · simp only [h12, ite_false, List.mem_singleton] at h ⊢
        rw [cdig_inj ha hc2, cdig_inj hb0 hc1] at h
        rw [h.1, h.2]
  · rintro ⟨t0, ⟨hl, h0, hb⟩, ht⟩
    match t0, hl, h0, hb, ht with
    | [], hl, _, _, _ => simp at hl hlen; omega
    | [_], hl, _, _, _ => simp at hl hlen; omega
    | c1 :: c2 :: e, hl, h0, hb, ht =>
      simp only [List.mem_cons, not_or] at h0
      have hc1 : c1 ≠ Color0 := Ne.symm h0.1
      have hc2 : c2 ≠ Color0 := Ne.symm h0.2.1
      simp only [cpsucc] at ht
      by_cases h12 : c1 = c2
      · subst h12
        simp only [ite_true, List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl
        · refine ⟨by simp at hl ⊢; omega, by simp [Ne.symm (permc_ne0 (g := Eperm231) hc1), h0.2.2],
            (hchar _ _ _).2 ⟨c1, c1, hc1, hc1, hb, ?_⟩⟩
          simp [cdig_p231 hc1]
        · refine ⟨by simp at hl ⊢; omega, by simp [Ne.symm (permc_ne0 (g := Eperm312) hc1), h0.2.2],
            (hchar _ _ _).2 ⟨c1, c1, hc1, hc1, hb, ?_⟩⟩
          simp [cdig_p312 hc1]
      · simp only [h12, ite_false, List.mem_singleton] at ht
        subst ht
        refine ⟨by simp at hl ⊢; omega, by simp [h0.1, h0.2.1, h0.2.2],
          (hchar _ _ _).2 ⟨c1, c2, hc1, hc2, hb, ?_⟩⟩
        simp [h12]


private theorem slots_perm {n : Nat} {l l' : List Nat} (hp : l.Perm l') (h : Slots n l) :
    Slots n l' := ⟨hp.nodup_iff.1 h.1, fun s hs => h.2 s (hp.symm.subset hs)⟩

private theorem addd_le {v1 v2 : Nat} (h1 : v1 ≤ 2) (h2 : v2 ≤ 2) : addd v1 v2 ≤ 2 := by
  rcases (show v1 = 0 ∨ v1 = 1 ∨ v1 = 2 by omega) with rfl | rfl | rfl <;>
  rcases (show v2 = 0 ∨ v2 = 1 ∨ v2 = 2 by omega) with rfl | rfl | rfl <;> decide

private theorem sel2_head {ℓ x s0 s1 : Nat} {rest : List Nat}
    (hsl : Slots ℓ (s0 :: s1 :: rest)) (v1 v2 : Nat) (hv1 : v1 ≤ 2) (hv2 : v2 ≤ 2)
    (a b : Color) (e : Colseq) :
    (sel ℓ (sel ℓ x s0 v1) s1 v2).testBit (slotIdx (s0 :: s1 :: rest) (a :: b :: e)) = true ↔
      x.testBit (slotIdx (s0 :: s1 :: rest) (a :: b :: e)) = true ∧ cdig a = v1 ∧
        cdig b = v2 := by
  have hs0 := hsl.2 s0 (by simp)
  have hs1 := hsl.2 s1 (by simp)
  have hne : s0 ≠ s1 := by
    have := hsl.1; simp only [List.nodup_cons, List.mem_cons, not_or] at this; exact this.1.1
  have hF : ∀ s' < ℓ, dfun (s0 :: s1 :: rest) (a :: b :: e) s' ≤ 2 := fun _ _ => dfun_le _ _ _
  rw [slotIdx_eq hsl, testBit_sel_bv hs1 hv2 hF, testBit_sel_bv hs0 hv1 hF]
  simp only [dfun_cons, Function.update_self, Function.update_of_ne (Ne.symm hne)]
  tauto

private theorem mv_sel2_head {ℓ x s0 s1 w : Nat} {rest : List Nat}
    (hsl : Slots ℓ (s0 :: s1 :: rest)) (c1 c2 : Color) (hw : w ≤ 2) (a b : Color) (e : Colseq) :
    (mv (sel ℓ (sel ℓ x s0 (cdig c1)) s1 (cdig c2)) s0 (cdig c1) w).testBit
      (slotIdx (s0 :: s1 :: rest) (a :: b :: e)) = true ↔
      cdig a = w ∧ cdig b = cdig c2 ∧
        x.testBit (slotIdx (s0 :: s1 :: rest) (c1 :: b :: e)) = true := by
  have hs0 := hsl.2 s0 (by simp)
  have hs1 := hsl.2 s1 (by simp)
  have hne : s0 ≠ s1 := by
    have := hsl.1; simp only [List.nodup_cons, List.mem_cons, not_or] at this; exact this.1.1
  have hv1 := cdig_le c1
  have hv2 := cdig_le c2
  have hy : ∀ K, (sel ℓ (sel ℓ x s0 (cdig c1)) s1 (cdig c2)).testBit K = true →
      K < 3 ^ ℓ ∧ dig K s0 = cdig c1 := by
    intro K hK
    rw [testBit_sel hs1 hv2, testBit_sel hs0 hv1] at hK
    exact ⟨hK.2.1, hK.1.2.2⟩
  have hF : ∀ s' < ℓ, dfun (s0 :: s1 :: rest) (a :: b :: e) s' ≤ 2 := fun _ _ => dfun_le _ _ _
  rw [slotIdx_eq hsl, slotIdx_eq hsl, testBit_mv_bv hs0 hv1 hw hy hF,
    testBit_sel_bv hs1 hv2 (update_le hF hv1), testBit_sel_bv hs0 hv1 (update_le hF hv1)]
  simp only [dfun_cons, Function.update_self, Function.update_idem,
    Function.update_of_ne (Ne.symm hne)]
  tauto

private theorem stepK {ℓ s0 s1 : Nat} {rest : List Nat} {x : Nat}
    (hsl : Slots ℓ (s0 :: s1 :: rest)) (hlen : (s0 :: s1 :: rest).length = ℓ) (t : Colseq) :
    (dpStep ⟨ℓ, s0 :: s1 :: rest, x⟩ .K).den t ↔
      ∃ t0, (⟨ℓ, s0 :: s1 :: rest, x⟩ : DPState).den t0 ∧ t ∈ cpsucc .K t0 := by
  have hchar : ∀ a b e, b ≠ Color0 → ((ors (digits3.flatMap fun v1 => digits3.map fun v2 =>
      if v1 == v2 then 0 else mv (sel ℓ (sel ℓ x s0 v1) s1 v2) s0 v1 (addd v1 v2))).testBit
      (slotIdx (s0 :: s1 :: rest) (a :: b :: e)) = true
      ↔ ∃ c1, c1 ≠ Color0 ∧ c1 ≠ b ∧ cdig a = addd (cdig c1) (cdig b) ∧
        x.testBit (slotIdx (s0 :: s1 :: rest) (c1 :: b :: e)) = true) := by
    intro a b e hb
    rw [testBit_ors]
    simp only [List.mem_flatMap, List.mem_map, mem_digits3]
    constructor
    · rintro ⟨_, ⟨v1, hv1, v2, hv2, rfl⟩, h⟩
      obtain ⟨c1, hc1, rfl⟩ := dig_col hv1
      obtain ⟨c2, hc2, rfl⟩ := dig_col hv2
      by_cases h12 : c1 = c2
      · subst h12; simp at h
      · have : (cdig c1 == cdig c2) = false := by
          rw [beq_eq_false_iff_ne, Ne, cdig_inj hc1 hc2]; exact h12
        simp only [this, Bool.false_eq_true, ite_false] at h
        rw [mv_sel2_head hsl c1 c2 (addd_le (cdig_le _) (cdig_le _))] at h
        obtain ⟨h1, h2, h3⟩ := h
        rw [cdig_inj hb hc2] at h2
        subst h2
        exact ⟨c1, hc1, h12, h1, h3⟩
    · rintro ⟨c1, hc1, h1b, ha, hx⟩
      refine ⟨_, ⟨cdig c1, cdig_le _, cdig b, cdig_le _, rfl⟩, ?_⟩
      have : (cdig c1 == cdig b) = false := by
        rw [beq_eq_false_iff_ne, Ne, cdig_inj hc1 hb]; exact h1b
      simp only [this, Bool.false_eq_true, ite_false]
      rw [mv_sel2_head hsl c1 b (addd_le (cdig_le _) (cdig_le _))]
      exact ⟨ha, rfl, hx⟩
  have hsl' : Slots ℓ (s1 :: s0 :: rest) := slots_perm (List.Perm.swap s1 s0 rest) hsl
  show (killSlot _ s1).den t ↔ _
  rw [killSlot_den hsl']
  simp only [DPState.den]
  constructor
  · rintro ⟨c, hl, h0, hb⟩
    match t, hl, h0, hb with
    | [], hl, _, _ => simp at hl hlen; omega
    | a :: e, hl, h0, hb =>
      simp only [List.mem_cons, not_or] at h0
      rw [slotIdx_swap, hchar _ _ _ (Ne.symm h0.1)] at hb
      obtain ⟨c1, hc1, h1c, ha, hx⟩ := hb
      refine ⟨c1 :: c :: e, ⟨by simp at hl ⊢; omega, by simp [Ne.symm hc1, h0.1, h0.2.2], hx⟩, ?_⟩
      simp only [cpsucc, h1c, ite_false, List.mem_singleton]
      obtain ⟨h1, h2⟩ := cdig_addc hc1 (Ne.symm h0.1) h1c
      rw [← h1, cdig_inj (Ne.symm h0.2.1) h2] at ha
      rw [ha]
  · rintro ⟨t0, ⟨hl, h0, hb⟩, ht⟩
    match t0, hl, h0, hb, ht with
    | [], hl, _, _, _ => simp at hl hlen; omega
    | [_], hl, _, _, _ => simp at hl hlen; omega
    | c1 :: c2 :: e, hl, h0, hb, ht =>
      simp only [List.mem_cons, not_or] at h0
      have hc1 : c1 ≠ Color0 := Ne.symm h0.1
      have hc2 : c2 ≠ Color0 := Ne.symm h0.2.1
      simp only [cpsucc] at ht
      by_cases h12 : c1 = c2
      · simp [h12] at ht
      · simp only [h12, ite_false, List.mem_singleton] at ht
        subst ht
        obtain ⟨h1, h2⟩ := cdig_addc hc1 hc2 h12
        refine ⟨c2, by simp at hl ⊢; omega, by simp [h0.2.1, h0.2.2, Ne.symm h2], ?_⟩
        rw [slotIdx_swap, hchar _ _ _ hc2]
        exact ⟨c1, hc1, h12, h1, hb⟩


private def xA (ℓ x s0 s1 : Nat) : Nat := ors (digits3.map fun v => sel ℓ (sel ℓ x s0 v) s1 v)

private def phiK (ℓ s1 o : Nat) : Nat := if o == ℓ - 1 then s1 else o

private theorem xA_char {ℓ x s0 s1 : Nat} {rest : List Nat} (hsl : Slots ℓ (s0 :: s1 :: rest))
    {a b : Color} (ha : a ≠ Color0) (hb : b ≠ Color0) (e : Colseq) :
    (xA ℓ x s0 s1).testBit (slotIdx (s0 :: s1 :: rest) (a :: b :: e)) = true ↔
      x.testBit (slotIdx (s0 :: s1 :: rest) (a :: b :: e)) = true ∧ a = b := by
  rw [xA, testBit_ors]
  simp only [List.mem_map, mem_digits3]
  constructor
  · rintro ⟨_, ⟨v, hv, rfl⟩, h⟩
    rw [sel2_head hsl v v hv hv] at h
    exact ⟨h.1, (cdig_inj ha hb).1 (h.2.1.trans h.2.2.symm)⟩
  · rintro ⟨h, rfl⟩
    exact ⟨_, ⟨cdig a, cdig_le a, rfl⟩, (sel2_head hsl _ _ (cdig_le a) (cdig_le a) _ _ _).2
      ⟨h, rfl, rfl⟩⟩

private theorem dpStep_A_cons (ℓ s0 s1 r : Nat) (rs : List Nat) (x : Nat) :
    dpStep ⟨ℓ, s0 :: s1 :: r :: rs, x⟩ .A = killSlot ⟨ℓ - 1, (r :: rs).map (phiK ℓ s1),
      (killSlot ⟨ℓ, (r :: rs) ++ [s0], xA ℓ x s0 s1⟩ s1).x⟩ (phiK ℓ s1 s0) := by
  simp only [dpStep]
  have h : (killSlot ⟨ℓ, (r :: rs) ++ [s0], ors (digits3.map fun v => sel ℓ (sel ℓ x s0 v) s1 v)⟩
      s1).ord = (r :: rs).map (fun o => if o == ℓ - 1 then s1 else o) ++
        [if s0 == ℓ - 1 then s1 else s0] := by
    simp [killSlot]
  rw [h, List.getLast?_concat, List.dropLast_concat]
  rfl

private theorem killSlot_A (ℓ s0 s1 : Nat) (R : List Nat) (x : Nat) :
    killSlot ⟨ℓ, R ++ [s0], x⟩ s1 =
      ⟨ℓ - 1, R.map (phiK ℓ s1) ++ [phiK ℓ s1 s0], (killSlot ⟨ℓ, R ++ [s0], x⟩ s1).x⟩ := by
  simp [killSlot, phiK]

private theorem stepA {ℓ s0 s1 : Nat} {rest : List Nat} {x : Nat}
    (hsl : Slots ℓ (s0 :: s1 :: rest)) (hlen : (s0 :: s1 :: rest).length = ℓ) (t : Colseq) :
    (dpStep ⟨ℓ, s0 :: s1 :: rest, x⟩ .A).den t ↔
      ∃ t0, (⟨ℓ, s0 :: s1 :: rest, x⟩ : DPState).den t0 ∧ t ∈ cpsucc .A t0 := by
  cases rest with
  | nil =>
    show (⟨ℓ, [s0, s1], xA ℓ x s0 s1⟩ : DPState).den t ↔ _
    simp only [DPState.den]
    constructor
    · rintro ⟨hl, h0, hb⟩
      match t, hl, h0, hb with
      | [], hl, _, _ => simp at hl hlen; omega
      | [_], hl, _, _ => simp at hl hlen; omega
      | a :: b :: e, hl, h0, hb =>
        simp only [List.mem_cons, not_or] at h0
        rw [xA_char hsl (Ne.symm h0.1) (Ne.symm h0.2.1)] at hb
        obtain ⟨hb, rfl⟩ := hb
        refine ⟨a :: a :: e, ⟨hl, by simp [h0.1, h0.2.2], hb⟩, ?_⟩
        have he : e = [] := by simp at hl hlen; exact List.eq_nil_of_length_eq_zero (by omega)
        subst he
        simp [cpsucc]
    · rintro ⟨t0, ⟨hl, h0, hb⟩, ht⟩
      match t0, hl, h0, hb, ht with
      | [], hl, _, _, _ => simp at hl hlen; omega
      | [_], hl, _, _, _ => simp at hl hlen; omega
      | c1 :: c2 :: e, hl, h0, hb, ht =>
        simp only [List.mem_cons, not_or] at h0
        have he : e = [] := by simp at hl hlen; exact List.eq_nil_of_length_eq_zero (by omega)
        subst he
        simp only [cpsucc] at ht
        by_cases h12 : c1 = c2
        · subst h12
          simp only [ite_true, List.mem_singleton] at ht
          subst ht
          refine ⟨hl, by simp [h0.1, h0.2.2], ?_⟩
          rw [xA_char hsl (Ne.symm h0.1) (Ne.symm h0.1)]
          exact ⟨hb, rfl⟩
        · simp [h12] at ht
  | cons r rs =>
    have hA1 : Slots ℓ (s1 :: ((r :: rs) ++ [s0])) :=
      slots_perm ((List.Perm.swap s1 s0 (r :: rs)).trans
        (List.Perm.cons s1 (List.perm_append_singleton s0 (r :: rs)).symm)) hsl
    have hk1 := slots_kill hA1
    have hA2 : Slots (ℓ - 1) (phiK ℓ s1 s0 :: (r :: rs).map (phiK ℓ s1)) := by
      refine slots_perm (List.perm_append_singleton _ _) ?_
      have e : ((r :: rs) ++ [s0]).map (fun o => if o == ℓ - 1 then s1 else o) =
          (r :: rs).map (phiK ℓ s1) ++ [phiK ℓ s1 s0] := by simp [phiK]
      rw [← e]; exact hk1
    rw [dpStep_A_cons, killSlot_den hA2]
    have e1 : ∀ c', (⟨ℓ - 1, phiK ℓ s1 s0 :: (r :: rs).map (phiK ℓ s1),
        (killSlot ⟨ℓ, (r :: rs) ++ [s0], xA ℓ x s0 s1⟩ s1).x⟩ : DPState).den (c' :: t) ↔
        ∃ c, (⟨ℓ, s0 :: s1 :: r :: rs, xA ℓ x s0 s1⟩ : DPState).den (c' :: c :: t) := by
      intro c'
      have e1a : (⟨ℓ - 1, phiK ℓ s1 s0 :: (r :: rs).map (phiK ℓ s1),
          (killSlot ⟨ℓ, (r :: rs) ++ [s0], xA ℓ x s0 s1⟩ s1).x⟩ : DPState).den (c' :: t) ↔
          (killSlot ⟨ℓ, (r :: rs) ++ [s0], xA ℓ x s0 s1⟩ s1).den (t ++ [c']) := by
        rw [killSlot_A]
        simp only [DPState.den]
        constructor
        · rintro ⟨hl, h0, hb⟩
          refine ⟨by simp at hl ⊢; omega, by simpa [or_comm] using h0, ?_⟩
          rw [slotIdx_snoc (by simp at hl hlen ⊢; omega)]; exact hb
        · rintro ⟨hl, h0, hb⟩
          refine ⟨by simp at hl ⊢; omega, by simpa [or_comm] using h0, ?_⟩
          rw [slotIdx_snoc (by simp at hl hlen ⊢; omega)] at hb; exact hb
      rw [e1a, killSlot_den hA1]
      simp only [DPState.den]
      constructor
      · rintro ⟨c, hl, h0, hb⟩
        refine ⟨c, by simp at hl ⊢; omega, by simp at h0 ⊢; tauto, ?_⟩
        have : slotIdx (s1 :: ((r :: rs) ++ [s0])) (c :: (t ++ [c'])) =
            slotIdx (s0 :: s1 :: r :: rs) (c' :: c :: t) := by
          simp only [slotIdx]
          rw [slotIdx_snoc (by simp at hl hlen ⊢; omega)]
          simp only [slotIdx]; omega
        rw [← this]; exact hb
      · rintro ⟨c, hl, h0, hb⟩
        refine ⟨c, by simp at hl ⊢; omega, by simp at h0 ⊢; tauto, ?_⟩
        have : slotIdx (s1 :: ((r :: rs) ++ [s0])) (c :: (t ++ [c'])) =
            slotIdx (s0 :: s1 :: r :: rs) (c' :: c :: t) := by
          simp only [slotIdx]
          rw [slotIdx_snoc (by simp at hl hlen ⊢; omega)]
          simp only [slotIdx]; omega
        rw [this]; exact hb
    simp only [e1]
    simp only [DPState.den]
    constructor
    · rintro ⟨c', c, hl, h0, hb⟩
      simp only [List.mem_cons, not_or] at h0
      rw [xA_char hsl (Ne.symm h0.1) (Ne.symm h0.2.1)] at hb
      obtain ⟨hb, rfl⟩ := hb
      refine ⟨c' :: c' :: t, ⟨hl, by simp [h0.1, h0.2.2], hb⟩, ?_⟩
      match t, hl with
      | [], hl => simp at hl hlen; omega
      | _ :: _, _ => simp [cpsucc]
    · rintro ⟨t0, ⟨hl, h0, hb⟩, ht⟩
      match t0, hl, h0, hb, ht with
      | [], hl, _, _, _ => simp at hl hlen; omega
      | [_], hl, _, _, _ => simp at hl hlen; omega
      | c1 :: c2 :: e, hl, h0, hb, ht =>
        simp only [List.mem_cons, not_or] at h0
        simp only [cpsucc] at ht
        by_cases h12 : c1 = c2
        · subst h12
          match e, hl, h0, hb, ht with
          | [], hl, _, _, _ => simp at hl hlen; omega
          | f :: e, hl, h0, hb, ht =>
            simp only [ite_true, List.mem_singleton] at ht
            subst ht
            refine ⟨c1, c1, hl, by simp [h0.1, h0.2.2], ?_⟩
            rw [xA_char hsl (Ne.symm h0.1) (Ne.symm h0.1)]
            exact ⟨hb, rfl⟩
        · simp [h12] at ht



/-! ### Well-formedness and length -/

private theorem supp_or {n a b : Nat} (ha : Supp n a) (hb : Supp n b) : Supp n (a ||| b) := by
  intro j hj
  rw [Nat.testBit_or, Bool.or_eq_true] at hj
  rcases hj with hj | hj
  · exact ha j hj
  · exact hb j hj

private theorem supp_mono {n m a : Nat} (ha : Supp n a) (h : n ≤ m) : Supp m a :=
  fun j hj => Nat.lt_of_lt_of_le (ha j hj) h

private theorem supp_mv2 {ℓ x s0 s1 v1 v2 w1 w2 : Nat} (hs0 : s0 < ℓ) (hs1 : s1 < ℓ)
    (hne : s0 ≠ s1) (hv1 : v1 ≤ 2) (hv2 : v2 ≤ 2) (hw1 : w1 ≤ 2) (hw2 : w2 ≤ 2) :
    Supp (3 ^ ℓ) (mv (mv (sel ℓ (sel ℓ x s0 v1) s1 v2) s0 v1 w1) s1 v2 w2) := by
  have hy : ∀ K, (sel ℓ (sel ℓ x s0 v1) s1 v2).testBit K = true →
      K < 3 ^ ℓ ∧ dig K s0 = v1 ∧ dig K s1 = v2 := by
    intro K hK
    rw [testBit_sel hs1 hv2, testBit_sel hs0 hv1] at hK
    exact ⟨hK.2.1, hK.1.2.2, hK.2.2⟩
  refine supp_mv hs1 hv2 hw2 ?_
  intro K hK
  refine ⟨((testBit_mv hs0 hv1 hw1 (fun K h => ⟨(hy K h).1, (hy K h).2.1⟩) K).1 hK).1, ?_⟩
  exact mv_keep hs0 hv1 hw1 (fun K h => ⟨(hy K h).1, (hy K h).2.1⟩) hs1 (Ne.symm hne)
    (fun K h => (hy K h).2.2) K hK

private theorem killSlot_WF {st : DPState} {s : Nat} (h : Slots st.len (s :: st.ord))
    (hlen : (s :: st.ord).length = st.len) (h2 : 2 ≤ st.len) : (killSlot st s).WF := by
  obtain ⟨ℓ, ord, x⟩ := st
  simp only at h hlen h2
  refine ⟨perm_range_iff.2 ⟨slots_kill h, by simp [killSlot]; simp at hlen; omega⟩, ?_, ?_⟩
  · show _ &&& _ < _
    apply supp_iff.1
    intro j hj
    rw [Nat.testBit_land, testBit_ones, Bool.and_eq_true, decide_eq_true_eq] at hj
    exact hj.2
  · show 1 ≤ ℓ - 1; omega

private theorem slots_cons {n s : Nat} {ord : List Nat} (hs : s < n) (hn : s ∉ ord)
    (h : Slots n ord) : Slots n (s :: ord) :=
  ⟨List.nodup_cons.2 ⟨hn, h.1⟩, fun o ho => by
    rcases List.mem_cons.1 ho with rfl | ho
    · exact hs
    · exact h.2 o ho⟩

private theorem dpStep_WF {st : DPState} (hst : st.WF) (s : Cpstep) : (dpStep st s).WF := by
  obtain ⟨ℓ, ord, x⟩ := st
  obtain ⟨hperm, hx, hl⟩ := hst
  obtain ⟨hsl, hlen⟩ := perm_range_iff.1 hperm
  simp only at hsl hlen hx hl hperm
  have hz : Supp (3 ^ ℓ) x := supp_iff.2 hx
  have h0 : ∀ ord', ord'.Perm (List.range ℓ) → (⟨ℓ, ord', 0⟩ : DPState).WF :=
    fun ord' h => ⟨h, Nat.two_pow_pos _, hl⟩
  cases s with
  | R n => exact ⟨(perm_rot n ord).trans hperm, hx, hl⟩
  | R' =>
    simp only [dpStep]
    split
    · exact h0 ord hperm
    · exact ⟨(perm_rotr 1 ord).trans hperm, hx, hl⟩
  | U =>
    show DPState.WF ⟨ℓ + 2, ℓ :: (ℓ + 1) :: ord,
      ors (digits3.map fun v => x <<< (v * 3 ^ ℓ + v * 3 ^ (ℓ + 1)))⟩
    unfold DPState.WF; dsimp only
    refine ⟨perm_range_iff.2 ⟨?_, by simp [hlen]⟩, ?_, by show 1 ≤ ℓ + 2; omega⟩
    · refine slots_cons (by omega) ?_ (slots_cons (by omega) ?_ (slots_mono hsl (by omega)))
      · simp only [List.mem_cons, not_or]
        exact ⟨by omega, fun h => by have := hsl.2 _ h; omega⟩
      · exact fun h => by have := hsl.2 _ h; omega
    · apply supp_iff.1
      apply supp_ors
      intro y hy
      simp only [List.mem_map, mem_digits3] at hy
      obtain ⟨v, hv, rfl⟩ := hy
      have es : v * 3 ^ ℓ + v * 3 ^ (ℓ + 1) = (4 * v) * 3 ^ ℓ := by rw [Nat.pow_succ]; ring
      rw [es]
      refine supp_mono (supp_shift hz) ?_
      have : (4 * v + 1) * 3 ^ ℓ ≤ 9 * 3 ^ ℓ := Nat.mul_le_mul_right _ (by omega)
      show _ ≤ 3 ^ (ℓ + 1 + 1)
      rw [Nat.pow_succ, Nat.pow_succ]; omega
  | Y =>
    match ord, hsl, hlen, hperm with
    | [], _, hlen, _ => simp at hlen; omega
    | s0 :: rest, hsl, hlen, _ =>
      have hs0 := hsl.2 s0 (by simp)
      show DPState.WF ⟨ℓ + 1, s0 :: ℓ :: rest, ors (digits3.map fun v =>
        (mv (sel ℓ x s0 v) s0 v (p231 v) <<< (p312 v * 3 ^ ℓ)) |||
          (mv (sel ℓ x s0 v) s0 v (p312 v) <<< (p231 v * 3 ^ ℓ)))⟩
      unfold DPState.WF; dsimp only
      refine ⟨perm_range_iff.2 ⟨?_, by simp at hlen ⊢; omega⟩, ?_, by show 1 ≤ ℓ + 1; omega⟩
      · refine slots_cons (by omega) ?_ (slots_cons (by omega) ?_ ?_)
        · simp only [List.mem_cons, not_or]
          exact ⟨by omega, (List.nodup_cons.1 hsl.1).1⟩
        · exact fun h => by have := hsl.2 _ (List.mem_cons_of_mem _ h); omega
        · exact slots_mono ⟨(List.nodup_cons.1 hsl.1).2,
            fun o ho => hsl.2 o (List.mem_cons_of_mem _ ho)⟩ (by omega)
      · apply supp_iff.1
        apply supp_ors
        intro y hy
        simp only [List.mem_map, mem_digits3] at hy
        obtain ⟨v, hv, rfl⟩ := hy
        have key : ∀ w w', w ≤ 2 → w' ≤ 2 →
            Supp (3 ^ (ℓ + 1)) (mv (sel ℓ x s0 v) s0 v w <<< (w' * 3 ^ ℓ)) := by
          intro w w' hw hw'
          refine supp_mono (supp_shift (supp_mv hs0 hv hw (sel_supp hs0 hv))) ?_
          have : (w' + 1) * 3 ^ ℓ ≤ 3 * 3 ^ ℓ := Nat.mul_le_mul_right _ (by omega)
          rw [Nat.pow_succ]; omega
        exact supp_or (key _ _ (p231_le _) (p312_le _)) (key _ _ (p312_le _) (p231_le _))
  | H =>
    match ord, hsl, hlen, hperm with
    | [], _, hlen, _ => simp at hlen; omega
    | [s0], _, _, hperm => exact h0 _ hperm
    | s0 :: s1 :: rest, hsl, hlen, hperm =>
      have hs0 := hsl.2 s0 (by simp)
      have hs1 := hsl.2 s1 (by simp)
      have hne : s0 ≠ s1 := by
        have := hsl.1; simp only [List.nodup_cons, List.mem_cons, not_or] at this; exact this.1.1
      refine ⟨hperm, ?_, hl⟩
      show ors _ < _
      apply supp_iff.1
      apply supp_ors
      intro y hy
      simp only [List.mem_flatMap, List.mem_map, mem_digits3] at hy
      obtain ⟨v1, hv1, v2, hv2, rfl⟩ := hy
      split
      · exact supp_or (supp_mv2 hs0 hs1 hne hv1 hv2 (p231_le _) (p231_le _))
          (supp_mv2 hs0 hs1 hne hv1 hv2 (p312_le _) (p312_le _))
      · exact supp_mv2 hs0 hs1 hne hv1 hv2 hv2 hv1
  | K =>
    match ord, hsl, hlen, hperm with
    | [], _, hlen, _ => simp at hlen; omega
    | [s0], _, _, hperm => exact h0 _ hperm
    | s0 :: s1 :: rest, hsl, hlen, hperm =>
      exact killSlot_WF (slots_perm (List.Perm.swap s1 s0 rest) hsl)
        (by simp at hlen ⊢; omega) (by simp at hlen ⊢; omega)
  | A =>
    match ord, hsl, hlen, hperm with
    | [], _, hlen, _ => simp at hlen; omega
    | [s0], _, _, hperm => exact h0 _ hperm
    | [s0, s1], hsl, hlen, hperm =>
      have hs0 := hsl.2 s0 (by simp)
      have hs1 := hsl.2 s1 (by simp)
      refine ⟨hperm, ?_, hl⟩
      show xA ℓ x s0 s1 < _
      apply supp_iff.1
      apply supp_ors
      intro y hy
      simp only [List.mem_map, mem_digits3] at hy
      obtain ⟨v, hv, rfl⟩ := hy
      exact fun j hj => ((testBit_sel hs1 hv j).1 hj).2.1
    | s0 :: s1 :: r :: rs, hsl, hlen, hperm =>
      rw [dpStep_A_cons]
      have hA1 : Slots ℓ (s1 :: ((r :: rs) ++ [s0])) :=
        slots_perm ((List.Perm.swap s1 s0 (r :: rs)).trans
          (List.Perm.cons s1 (List.perm_append_singleton s0 (r :: rs)).symm)) hsl
      have hk1 := slots_kill hA1
      have hA2 : Slots (ℓ - 1) (phiK ℓ s1 s0 :: (r :: rs).map (phiK ℓ s1)) := by
        refine slots_perm (List.perm_append_singleton _ _) ?_
        have e : ((r :: rs) ++ [s0]).map (fun o => if o == ℓ - 1 then s1 else o) =
            (r :: rs).map (phiK ℓ s1) ++ [phiK ℓ s1 s0] := by simp [phiK]
        rw [← e]; exact hk1
      exact killSlot_WF hA2 (by simp at hlen ⊢; omega) (by simp at hlen ⊢; omega)

private theorem dpStep_len {st : DPState} (hst : st.WF) {cp : Cprog} (hcp : st.len = cprsize cp)
    (s : Cpstep) : (dpStep st s).len = cprsize (s :: cp) := by
  obtain ⟨ℓ, ord, x⟩ := st
  obtain ⟨hperm, hx, hl⟩ := hst
  obtain ⟨hsl, hlen⟩ := perm_range_iff.1 hperm
  simp only at hsl hlen hx hl hperm hcp
  cases s with
  | R n => exact hcp
  | R' => simp only [dpStep]; split <;> exact hcp
  | U => show ℓ + 2 = _; simp [cprsize, hcp]
  | Y =>
    match ord, hlen with
    | [], hlen => simp at hlen; omega
    | s0 :: rest, _ => show ℓ + 1 = _; simp [cprsize, hcp]
  | H =>
    match ord, hlen with
    | [], hlen => simp at hlen; omega
    | [s0], _ => exact hcp
    | s0 :: s1 :: rest, _ => exact hcp
  | K =>
    match ord, hlen with
    | [], hlen => simp at hlen; omega
    | [s0], hlen => show ℓ = _; simp at hlen; simp [cprsize]; omega
    | s0 :: s1 :: rest, hlen => show ℓ - 1 = _; simp at hlen; simp [cprsize]; omega
  | A =>
    match ord, hlen with
    | [], hlen => simp at hlen; omega
    | [s0], hlen => show ℓ = _; simp at hlen; simp [cprsize, ← hcp, ← hlen, sub2ifgt2]
    | [s0, s1], hlen => show ℓ = _; simp at hlen; simp [cprsize, ← hcp, ← hlen, sub2ifgt2]
    | s0 :: s1 :: r :: rs, hlen =>
      rw [dpStep_A_cons]
      show ℓ - 1 - 1 = _
      simp at hlen
      simp only [cprsize, ← hcp, ← hlen]
      simp [sub2ifgt2]


private theorem dpBase_den (t : Colseq) : dpBase.den t ↔ t ∈ baseTraces := by
  simp only [DPState.den, dpBase, baseTraces]
  constructor
  · rintro ⟨hl, h0, hb⟩
    match t, hl, h0, hb with
    | [a, b], _, h0, hb =>
      simp only [List.mem_cons, not_or] at h0
      cases a <;> cases b <;> simp_all <;> revert hb <;> decide
  · intro h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide

/-! ### Sorting the digits -/

private theorem swp_inj {a b x y : Nat} (h : swp a b x = swp a b y) : x = y := by
  unfold swp at h; split_ifs at h <;> omega

private theorem dfun_map_swp' (a b : Nat) (L : List Nat) (t : Colseq) (s' : Nat) :
    dfun (L.map (swp a b)) t (swp a b s') = dfun L t s' := by
  induction L generalizing t with
  | nil => cases t <;> rfl
  | cons o L ih =>
    cases t with
    | nil => rfl
    | cons c t =>
      simp only [List.map_cons, dfun]
      by_cases h : s' = o
      · subst h; simp
      · rw [ite_eq_right (fun h' => h (swp_inj h')), ite_eq_right h, ih]

private theorem slotIdx_range' : ∀ (t : Colseq) (k : Nat),
    slotIdx (List.range' k t.length) t = 3 ^ k * b3idx t
  | [], _ => by simp [slotIdx, b3idx]
  | c :: t, k => by
    simp only [List.length_cons, List.range'_succ, slotIdx, b3idx]
    rw [slotIdx_range' t (k + 1), Nat.pow_succ]; ring

private theorem sortDigits_spec {ℓ : Nat} : ∀ (fuel i : Nat) (ord : List Nat) (x : Nat),
    Slots ℓ (List.range' 0 i ++ ord) → (List.range' 0 i ++ ord).length = ℓ →
    ord.length ≤ fuel → ∀ t : Colseq, t.length = ℓ →
    (sortDigits ℓ fuel i ord x).testBit (b3idx t) =
      x.testBit (slotIdx (List.range' 0 i ++ ord) t) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i ord x _ hlen hf t ht
    have : ord = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp only [List.append_nil, List.length_range'] at hlen ⊢
    simp only [sortDigits]
    rw [hlen, ← ht, slotIdx_range', Nat.pow_zero, Nat.one_mul]
  | succ fuel ih =>
    intro i ord x hsl hlen hf t ht
    match ord, hsl, hlen, hf with
    | [], _, hlen, _ =>
      simp only [List.append_nil, List.length_range'] at hlen ⊢
      simp only [sortDigits]
      rw [hlen, ← ht, slotIdx_range', Nat.pow_zero, Nat.one_mul]
    | s :: rest, hsl, hlen, hf =>
      simp only [sortDigits]
      have hnd := hsl.1
      rw [List.nodup_append] at hnd
      have hsi : i ≤ s := by
        by_contra h
        exact hnd.2.2 s (List.mem_range'.2 ⟨s, by omega, by simp⟩) s (by simp) rfl
      have hsrest : s ∉ rest := (List.nodup_cons.1 hnd.2.1).1
      simp only [List.length_append, List.length_range', List.length_cons] at hlen
      have hsℓ : s < ℓ := hsl.2 s (by simp)
      have hiℓ : i < ℓ := by omega
      have hL' : List.range' 0 (i + 1) ++ rest.map (fun t => if t == i then s else t) =
          (List.range' 0 i ++ s :: rest).map (swp s i) := by
        rw [List.map_append, List.map_cons, List.range'_concat, List.append_assoc]
        congr 1
        · conv_lhs => rw [← List.map_id (List.range' 0 i)]
          apply List.map_congr_left
          intro o ho
          obtain ⟨k, hk, rfl⟩ := List.mem_range'.1 ho
          unfold swp; simp only [id]; split_ifs <;> omega
        · simp only [List.singleton_append, List.cons.injEq]
          refine ⟨by simp [swp], ?_⟩
          apply List.map_congr_left
          intro o ho
          have : o ≠ s := fun h => hsrest (h ▸ ho)
          unfold swp
          split_ifs <;> simp_all
      have hsl' : Slots ℓ (List.range' 0 (i + 1) ++ rest.map (fun t => if t == i then s else t)) := by
        rw [hL']
        refine ⟨hsl.1.map (fun _ _ h => swp_inj h), ?_⟩
        intro o ho
        obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
        have := hsl.2 o' ho'
        unfold swp; split_ifs <;> omega
      rw [ih (i + 1) _ _ hsl' (by simp; omega) (by simp at hf ⊢; omega) t ht,
        testBit_transp hsℓ hiℓ (slotIdx_lt hsl' t)]
      congr 1
      rw [slotIdx_eq hsl]
      apply bv_congr
      intro s' hs'
      have : swp s i s' < ℓ := by unfold swp; split_ifs <;> omega
      rw [slotIdx_eq hsl', dig_bv (fun _ _ => dfun_le _ _ _) _ this, hL', dfun_map_swp']

/-! ### The packed layout -/

private theorem b3idx_snoc (u : Colseq) (c : Color) :
    b3idx (u ++ [c]) = b3idx u + cdig c * 3 ^ u.length := by
  induction u with
  | nil => simp [b3idx]
  | cons a u ih => simp only [List.cons_append, b3idx, ih, List.length_cons, Nat.pow_succ]; ring

private theorem b3idx_lt (u : Colseq) : b3idx u < 3 ^ u.length := by
  induction u with
  | nil => simp [b3idx]
  | cons a u ih =>
    simp only [b3idx, List.length_cons, Nat.pow_succ]
    have := cdig_le a; omega

private theorem testBit_fold3 (r w k : Nat) :
    (fold3 r w).testBit k = true ↔ k < 3 ^ (r - 1) ∧ (w.testBit k = true ∨
      w.testBit (k + 1 * 3 ^ (r - 1)) = true ∨ w.testBit (k + 2 * 3 ^ (r - 1)) = true) := by
  simp only [fold3, Nat.testBit_or, Nat.testBit_land, Nat.testBit_shiftRight,
    testBit_ones, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rw [Nat.one_mul, Nat.add_comm k, Nat.add_comm k]
  tauto

/-- Every DP state computed from the base state is well formed. -/
theorem dpRun_WF (cp : Cprog) : (dpRun cp).WF := by
  induction cp with
  | nil => exact ⟨by decide, by decide, by decide⟩
  | cons s cp ih => exact dpStep_WF ih s

/-- The DP computes the ring size. -/
theorem dpRun_len (cp : Cprog) : (dpRun cp).len = cprsize cp := by
  induction cp with
  | nil => rfl
  | cons s cp ih => exact dpStep_len (dpRun_WF cp) ih s

/-- **The DP step is the set-lift of `cpsucc`.** -/
theorem dpStep_den {st : DPState} (hst : st.WF) (s : Cpstep) (t : Colseq) :
    (dpStep st s).den t ↔ ∃ t0, st.den t0 ∧ t ∈ cpsucc s t0 := by
  obtain ⟨ℓ, ord, x⟩ := st
  obtain ⟨hperm, hx, hl⟩ := hst
  obtain ⟨hsl, hlen⟩ := perm_range_iff.1 hperm
  simp only at hsl hlen hx hl
  have shortH : ∀ s, ord.length ≤ 1 → (∀ t0 : Colseq, t0.length ≤ 1 → cpsucc s t0 = []) →
      ((⟨ℓ, ord, 0⟩ : DPState).den t ↔ ∃ t0, (⟨ℓ, ord, x⟩ : DPState).den t0 ∧ t ∈ cpsucc s t0) := by
    intro s hs hc
    simp only [den_zero, false_iff, not_exists, not_and]
    intro t0 h0
    have : t0.length = ℓ := h0.1
    rw [hc t0 (by omega)]; simp
  cases s with
  | R n => exact stepR hlen n t
  | R' => exact stepR' hlen t
  | U => exact stepU hsl hx t
  | Y =>
    match ord, hsl, hlen with
    | [], _, hlen => simp at hlen; omega
    | s0 :: rest, hsl, hlen => exact stepY hsl hlen t
  | H =>
    match ord, hsl, hlen with
    | [], _, hlen => simp at hlen; omega
    | [s0], _, hlen =>
      exact shortH .H (by simp) (fun t0 h => by
        match t0, h with
        | [], _ => rfl
        | [_], _ => rfl)
    | s0 :: s1 :: rest, hsl, hlen => exact stepH hsl hlen t
  | K =>
    match ord, hsl, hlen with
    | [], _, hlen => simp at hlen; omega
    | [s0], _, hlen =>
      exact shortH .K (by simp) (fun t0 h => by
        match t0, h with
        | [], _ => rfl
        | [_], _ => rfl)
    | s0 :: s1 :: rest, hsl, hlen => exact stepK hsl hlen t
  | A =>
    match ord, hsl, hlen with
    | [], _, hlen => simp at hlen; omega
    | [s0], _, hlen =>
      exact shortH .A (by simp) (fun t0 h => by
        match t0, h with
        | [], _ => rfl
        | [_], _ => rfl)
    | s0 :: s1 :: rest, hsl, hlen => exact stepA hsl hlen t

/-- The DP computes the reachable traces. -/
theorem dpRun_den (cp : Cprog) (t : Colseq) : (dpRun cp).den t ↔ CpReach cp t := by
  induction cp generalizing t with
  | nil => exact dpBase_den t
  | cons s cp ih =>
    show (dpStep (dpRun cp) s).den t ↔ _
    rw [dpStep_den (dpRun_WF cp)]
    simp only [CpReach, ih]

/-- The DP result in ring order. -/
theorem testBit_dpB3 (cp : Cprog) {t : Colseq} (hlen : t.length = cprsize cp)
    (h0 : Color0 ∉ t) : (dpB3 cp).testBit (b3idx t) = true ↔ CpReach cp t := by
  rw [← dpRun_den]
  obtain ⟨hperm, -, -⟩ := dpRun_WF cp
  obtain ⟨hsl, hl⟩ := perm_range_iff.1 hperm
  unfold dpB3
  dsimp only
  rw [sortDigits_spec _ 0 _ _ (by simpa using hsl) (by simpa using hl) (by omega) t
    (by rw [hlen, dpRun_len])]
  simp only [DPState.den, List.range'_zero, List.nil_append, dpRun_len, hlen, h0,
    not_false_eq_true, true_and]

/-- **The DP result in the packed layout.** -/
theorem den_dpP1 {r : Nat} {cnv : Net} (hcnv : CnvSpec r cnv) {cp : Cprog} (hr : cprsize cp = r)
    (h2 : 2 ≤ r) {t : Colseq} : den r (dpP1 r cnv cp) t ↔ ValidTrace r t ∧ CpReach cp t := by
  rw [dpP1, den_splitG, denCat]
  constructor
  · rintro ⟨hv, hb⟩
    refine ⟨hv, ?_⟩
    obtain ⟨hl, h0, hs⟩ := hv
    rw [hcnv t ⟨hl, h0, hs⟩] at hb
    obtain ⟨u, c, rfl⟩ : ∃ u c, t = u ++ [c] := by
      rcases List.eq_nil_or_concat t with h | ⟨u, c, h⟩
      · subst h; simp at hl; omega
      · exact ⟨u, c, by simpa using h⟩
    simp only [List.length_append, List.length_singleton] at hl
    have hu : u.length = r - 1 := by omega
    have htake : (u ++ [c]).take (r - 1) = u := by rw [← hu]; simp
    rw [htake, testBit_fold3] at hb
    obtain ⟨-, hb⟩ := hb
    simp only [List.mem_append, List.mem_singleton, not_or] at h0
    have key : ∃ c', c' ≠ Color0 ∧ CpReach cp (u ++ [c']) := by
      have hr' : ∀ c', c' ≠ Color0 →
          (dpB3 cp).testBit (b3idx u + cdig c' * 3 ^ (r - 1)) = true → CpReach cp (u ++ [c']) := by
        intro c' hc' h
        rw [← hu, ← b3idx_snoc] at h
        exact (testBit_dpB3 cp (by simp [hr]; omega) (by simp [h0.1, Ne.symm hc'])).1 h
      rcases hb with hb | hb | hb
      · exact ⟨Color1, by decide, hr' Color1 (by decide) (by simpa [cdig] using hb)⟩
      · exact ⟨Color2, by decide, hr' Color2 (by decide) (by simpa [cdig] using hb)⟩
      · exact ⟨Color3, by decide, hr' Color3 (by decide) (by simpa [cdig] using hb)⟩
    obtain ⟨c', hc', hreach⟩ := key
    have hs' := (cpReach_valid hreach).2.2
    rw [sumt_append, addc_eq0] at hs hs'
    have e : ∀ c, sumt [c] = c := fun c => by simp [sumt]
    rw [e] at hs hs'
    have : c = c' := by rw [← hs, hs']
    rwa [this]
  · rintro ⟨hv, hreach⟩
    refine ⟨hv, ?_⟩
    obtain ⟨hl, h0, hs⟩ := hv
    rw [hcnv t ⟨hl, h0, hs⟩]
    obtain ⟨u, c, rfl⟩ : ∃ u c, t = u ++ [c] := by
      rcases List.eq_nil_or_concat t with h | ⟨u, c, h⟩
      · subst h; simp at hl; omega
      · exact ⟨u, c, by simpa using h⟩
    simp only [List.length_append, List.length_singleton] at hl
    have hu : u.length = r - 1 := by omega
    have htake : (u ++ [c]).take (r - 1) = u := by rw [← hu]; simp
    rw [htake, testBit_fold3]
    refine ⟨hu ▸ b3idx_lt u, ?_⟩
    have hb := (testBit_dpB3 cp (by simp [hr]; omega) h0).2 hreach
    rw [b3idx_snoc, hu] at hb
    simp only [List.mem_append, List.mem_singleton, not_or] at h0
    cases c with
    | Color0 => exact absurd rfl h0.2
    | Color1 => left; simpa [cdig] using hb
    | Color2 => right; left; simpa [cdig] using hb
    | Color3 => right; right; simpa [cdig] using hb

end FourColor.Engine
