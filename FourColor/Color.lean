/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Seq
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.List.Rotate

/-!
# Colors and edge traces  (port of `color.v`)

The four colors, with color sum (xor) and comparison:

* `Color`                : the finite type of colors, with values `Color0` – `Color3`
  (Coq `color`).
* `palette c0 c1 c2 c3 c` : `cI` when `c = ColorI` (Coq notation `palette`).
* `cbit0 c`              : the lower bit of color `c` (`true` for `Color1` and `Color3`).
* `cbit1 c`              : the higher bit of color `c` (`true` for `Color2` and `Color3`).
* `ccons b1 b0`          : the color `2 b1 + b0`.
* `addc c1 c2`           : the bitwise sum of colors `c1` and `c2` (Coq `c1 +c c2`).
* `EdgePerm`             : a finite type enumerating the permutations of the nonzero colors
  (Coq `edge_perm`). `EpermIJK` maps `Color1` to `ColorI`, `Color2` to `ColorJ`, `Color3`
  to `ColorK`; e.g. `Eperm132` swaps `Color2` and `Color3`, and `Eperm123` is the identity.
* `permc g`              : the function `Color → Color` of `g : EdgePerm`; `EdgePerm`
  coerces to functions through `permc` (Coq coercion `permc`).
* `invEperm g`           : the `EdgePerm` inverse of `g` (Coq `inv_eperm`).
* `edgeRot c`            : the even `EdgePerm` mapping `c` to `Color1`, if `c ≠ Color0`
  (Coq `edge_rot`).
* `Colseq`               : `List Color` (a perimeter / edge perimeter coloring; Coq `colseq`).
* `countCbit1 s`         : the number of times `cbit1` is set in `s` (Coq `count_cbit1`).
* `headColor s`          : the first color in `s`, defaulting to `Color0` (Coq `head_color`).
* `trace s`              : the trace (edge coloring) corresponding to a perimeter coloring `s`;
  the `i`-th color in `trace s` is the sum of colors `i` and `i+1 [mod length s]` in `s`.
* `urtrace s`            : the right-rotated trace of `s` (`= rotr 1 (trace s)`).
* `ptrace s`             : the partial trace of `s`: `trace s` less its last color, which is
  redundant as it is the sum of the other ones.
* `sumt t`               : the sum of all colors in `t`.
* `ctrace t`             : completes a partial trace `t` by computing the last color.
* `untrace c0 t`         : the coloring with head color `c0` and trace `t`.
* `properTrace t`        : `t` does not start with `Color0` (Coq `proper_trace`); a trace
  obtained from a proper coloring cannot contain `Color0` at all, so `[Color0]` is used to
  signal failure of some trace operations.
* `permt g t`            : `g : EdgePerm` mapped over `t`.
* `ttail t`              : the seminormalised tail of a trace `t`, obtained by mapping
  `edgeRot c` over `t.tail`, when `c = headColor t` is not `Color0`; otherwise `ttail`
  fails, returning `[Color0]`.
* `evenTail t`           : `Color2` appears before `Color3` in `t` (Coq `even_tail`).
* `evenTrace t`          : if `t` is proper, there is an even permutation of edge colors of
  `t` where colors appear in the 1, 2, 3 order (Coq `even_trace`).
* `etracePerm t`         : a permutation of `Color2`–`Color3` that maps `t` to an even trace
  (Coq `etrace_perm`).
* `etrace t`             : a `Color2`–`Color3` permutation of `t` that is even.
* `etail t`              : the normalised, even tail of `t`: colors appear in order in
  `Color1 :: etail t`, which is an edge color permutation of `t`.
* `eptrace s`            : the standardized tail of the partial trace of `s`,
  `etail (ptrace s)`.

We also define the math-comp sequence operations used on color sequences and not provided
by `FourColor.Seq`, literally as in math-comp:

* `rot n s`   : `drop n s ++ take n s` (math-comp `rot`; unlike `List.rotate`, `n` is not
  reduced modulo `length s`, so `rot n s = s` when `length s ≤ n`);
* `rotr n s`  : `rot (length s - n) s` (math-comp `rotr`);
* `pairmap f x s` : `[f x s₁, f s₁ s₂, …, f sₙ₋₁ sₙ]` (math-comp `pairmap`);
* `scanl g x s`   : `[g x s₁, g (g x s₁) s₂, …]` (math-comp `scanl`; unlike core
  `List.scanl`, the initial value `x` is not included).

## Porting notes

* All the functions are computable and structurally recursive, so that they can be evaluated
  by the Lean kernel (`decide`).  Computational predicates (`properTrace`, `evenTail`,
  `evenTrace`) stay `Bool`-valued; the equations between them stay `Bool` equations.
* The equality of colors is decided by `eqc`, as in the Coq `eqType` instance.
* Coq's `c1 +c c2` notation is not introduced (the token `+c` would break expressions such
  as `n+c` in client files); write `addc c1 c2`.
* The informative Coq lemmas `color_inj_permc`, `compose_permt` and `etail_perm`, whose
  conclusions are `sig` types, are `def`s returning subtypes.
* math-comp `rcons s x` is `s ++ [x]`, `rev` is `List.reverse`, `behead` is `List.tail`,
  and membership `Color0 \in s` is `Color0 ∈ s`.
-/

namespace FourColor

open Function

universe u

/-! ### math-comp sequence operations: `rot`, `rotr`, `pairmap`, `scanl` -/

section SeqOps

variable {α β : Type*}

/-- math-comp `rot n s`: rotation of `s` by `n` items to the left, `drop n s ++ take n s`.
Unlike `List.rotate`, `n` is not reduced modulo the length: `rot n s = s` when
`length s ≤ n` (`rot_oversize`). -/
def rot (n : ℕ) (s : List α) : List α := s.drop n ++ s.take n

/-- math-comp `rotr n s`: rotation of `s` by `n` items to the right,
`rot (length s - n) s`. -/
def rotr (n : ℕ) (s : List α) : List α := rot (s.length - n) s

/-- math-comp `rot0`. -/
@[simp] theorem rot0 (s : List α) : rot 0 s = s := by simp [rot]

/-- math-comp `size_rot`. -/
@[simp] theorem length_rot (n : ℕ) (s : List α) : (rot n s).length = s.length := by
  simp only [rot, List.length_append, List.length_drop, List.length_take]
  omega

/-- math-comp `rot_oversize`. -/
theorem rot_oversize {n : ℕ} {s : List α} (h : s.length ≤ n) : rot n s = s := by
  simp [rot, List.drop_eq_nil_of_le h, List.take_of_length_le h]

/-- math-comp `rot_size`. -/
@[simp] theorem rot_size (s : List α) : rot s.length s = s := rot_oversize le_rfl

/-- math-comp `rot1_cons`. -/
@[simp] theorem rot1_cons (x : α) (s : List α) : rot 1 (x :: s) = s ++ [x] := by
  simp [rot]

/-- math-comp `rotD`. -/
theorem rotD {m n : ℕ} {s : List α} (h : m + n ≤ s.length) :
    rot (m + n) s = rot m (rot n s) := by
  have hm : m ≤ (s.drop n).length := by rw [List.length_drop]; omega
  simp only [rot]
  rw [List.drop_append_of_le_length hm, List.take_append_of_le_length hm, List.drop_drop,
    Nat.add_comm m n, List.take_add, List.append_assoc]

/-- `rot` agrees with `List.rotate` for rotations by at most the length. -/
theorem rot_eq_rotate {n : ℕ} {s : List α} (h : n ≤ s.length) : rot n s = s.rotate n :=
  (List.rotate_eq_drop_append_take h).symm

/-- math-comp `perm_rot`. -/
theorem perm_rot (n : ℕ) (s : List α) : (rot n s).Perm s := by
  simpa only [rot, List.take_append_drop] using
    (List.perm_append_comm (l₁ := s.drop n) (l₂ := s.take n))

/-- math-comp `mem_rot`. -/
@[simp] theorem mem_rot {n : ℕ} {s : List α} {x : α} : x ∈ rot n s ↔ x ∈ s :=
  (perm_rot n s).mem_iff

/-- math-comp `map_rot`. -/
theorem map_rot (f : α → β) (n : ℕ) (s : List α) : (rot n s).map f = rot n (s.map f) := by
  simp [rot, List.map_drop, List.map_take]

/-- math-comp `rotK`: `rotr n` cancels `rot n`. -/
theorem rotK (n : ℕ) (s : List α) : rotr n (rot n s) = s := by
  rcases le_or_gt n s.length with h | h
  · rw [rotr, length_rot, ← rotD (by omega), Nat.sub_add_cancel h, rot_size]
  · rw [rot_oversize h.le, rotr, Nat.sub_eq_zero_of_le h.le, rot0]

/-- math-comp `rotrK`: `rot n` cancels `rotr n`. -/
theorem rotrK (n : ℕ) (s : List α) : rot n (rotr n s) = s := by
  rcases le_or_gt n s.length with h | h
  · rw [rotr, ← rotD (by omega), Nat.add_sub_cancel' h, rot_size]
  · rw [rotr, Nat.sub_eq_zero_of_le h.le, rot0, rot_oversize h.le]

/-- math-comp `rot_inj`. -/
theorem rot_inj (n : ℕ) : Injective (rot n : List α → List α) := fun s t h => by
  rw [← rotK n s, h, rotK]

/-- math-comp `size_rotr`. -/
@[simp] theorem length_rotr (n : ℕ) (s : List α) : (rotr n s).length = s.length :=
  length_rot _ s

/-- math-comp `rotr_inj`. -/
theorem rotr_inj (n : ℕ) : Injective (rotr n : List α → List α) := fun s t h => by
  rw [← rotrK n s, h, rotrK]

/-- math-comp `perm_rotr`. -/
theorem perm_rotr (n : ℕ) (s : List α) : (rotr n s).Perm s := perm_rot _ s

/-- math-comp `mem_rotr`. -/
@[simp] theorem mem_rotr {n : ℕ} {s : List α} {x : α} : x ∈ rotr n s ↔ x ∈ s :=
  (perm_rotr n s).mem_iff

/-- math-comp `rot_uniq`. -/
@[simp] theorem nodup_rot {n : ℕ} {s : List α} : (rot n s).Nodup ↔ s.Nodup :=
  (perm_rot n s).nodup_iff

/-- math-comp `rotr_uniq`. -/
@[simp] theorem nodup_rotr {n : ℕ} {s : List α} : (rotr n s).Nodup ↔ s.Nodup :=
  (perm_rotr n s).nodup_iff

/-- math-comp `map_rotr`. -/
theorem map_rotr (f : α → β) (n : ℕ) (s : List α) : (rotr n s).map f = rotr n (s.map f) := by
  rw [rotr, rotr, map_rot, List.length_map]

/-- math-comp `rot_size_cat`. -/
theorem rot_size_cat (s1 s2 : List α) : rot s1.length (s1 ++ s2) = s2 ++ s1 := by
  rw [rot, List.drop_left, List.take_left]

/-- math-comp `rotr_size_cat`. -/
theorem rotr_size_cat (s1 s2 : List α) : rotr s2.length (s1 ++ s2) = s2 ++ s1 := by
  rw [rotr, List.length_append, Nat.add_sub_cancel, rot_size_cat]

/-- math-comp `rotr1_rcons`. -/
theorem rotr1_rcons (x : α) (s : List α) : rotr 1 (s ++ [x]) = x :: s :=
  rotr_size_cat s [x]

/-- math-comp `rotS`. -/
theorem rotS {n : ℕ} {s : List α} (h : n < s.length) : rot (n + 1) s = rot 1 (rot n s) := by
  rw [Nat.add_comm, rotD (by omega)]

/-- math-comp `rev_rotr`. -/
theorem rev_rotr (n : ℕ) (s : List α) : (rotr n s).reverse = rot n s.reverse := by
  rcases le_or_gt n s.length with h | h
  · simp only [rotr, rot, List.reverse_append, List.drop_reverse, List.take_reverse]
  · rw [rotr, Nat.sub_eq_zero_of_le h.le, rot0,
      rot_oversize (by rw [List.length_reverse]; omega)]

/-- math-comp `rev_rot`. -/
theorem rev_rot (n : ℕ) (s : List α) : (rot n s).reverse = rotr n s.reverse := by
  rw [← List.reverse_reverse (rotr n s.reverse), rev_rotr, List.reverse_reverse]

/-- math-comp `rot_to`: any item of `s` can be rotated to the head of `s`. -/
theorem rot_to {s : List α} {x : α} (h : x ∈ s) : ∃ i s', rot i s = x :: s' := by
  obtain ⟨s1, s2, rfl⟩ := List.append_of_mem h
  exact ⟨s1.length, s2 ++ s1, by rw [rot_size_cat, List.cons_append]⟩

/-- math-comp `pairmap f x s`: `[f x s₁, f s₁ s₂, …, f sₙ₋₁ sₙ]` for `s = [s₁, …, sₙ]`. -/
def pairmap (f : α → α → β) : α → List α → List β
  | _, [] => []
  | x, y :: s => f x y :: pairmap f y s

/-- Unfolding equation of `pairmap` on `[]`. -/
@[simp] theorem pairmap_nil (f : α → α → β) (x : α) : pairmap f x [] = [] := rfl

/-- Unfolding equation of `pairmap` on a cons. -/
@[simp] theorem pairmap_cons (f : α → α → β) (x y : α) (s : List α) :
    pairmap f x (y :: s) = f x y :: pairmap f y s := rfl

/-- math-comp `size_pairmap`. -/
@[simp] theorem length_pairmap (f : α → α → β) (x : α) (s : List α) :
    (pairmap f x s).length = s.length := by
  induction s generalizing x with
  | nil => rfl
  | cons y s ih => simp [ih]

/-- math-comp `pairmap_cat`. -/
theorem pairmap_append (f : α → α → β) (x : α) (s t : List α) :
    pairmap f x (s ++ t) = pairmap f x s ++ pairmap f (last x s) t := by
  induction s generalizing x with
  | nil => rfl
  | cons y s ih => simp [ih]

/-- Reversal of a `pairmap` (not in math-comp; used for `trace_rev`). -/
theorem reverse_pairmap (f : α → α → β) (x : α) (s : List α) :
    (pairmap f x s).reverse = pairmap (fun a b => f b a) (last x s) (belast x s).reverse := by
  induction s generalizing x with
  | nil => rfl
  | cons y s ih =>
    rw [pairmap_cons, List.reverse_cons, ih, last_cons, belast_cons, List.reverse_cons,
      pairmap_append, last_last_belast_reverse]
    rfl

/-- math-comp `scanl g x s`: the partial folds `[g x s₁, g (g x s₁) s₂, …]` of `s`.  Unlike
core `List.scanl`, the initial value `x` is not included. -/
def scanl (g : β → α → β) : β → List α → List β
  | _, [] => []
  | x, y :: s => let x' := g x y; x' :: scanl g x' s

/-- Unfolding equation of `scanl` on `[]`. -/
@[simp] theorem scanl_nil (g : β → α → β) (x : β) : scanl g x [] = [] := rfl

/-- Unfolding equation of `scanl` on a cons. -/
@[simp] theorem scanl_cons (g : β → α → β) (x : β) (y : α) (s : List α) :
    scanl g x (y :: s) = g x y :: scanl g (g x y) s := rfl

/-- math-comp `size_scanl`. -/
@[simp] theorem length_scanl (g : β → α → β) (x : β) (s : List α) :
    (scanl g x s).length = s.length := by
  induction s generalizing x with
  | nil => rfl
  | cons y s ih => simp [ih]

/-- math-comp `scanlK`: `pairmap f x` cancels `scanl g x` when `f x` cancels `g x`. -/
theorem scanlK {f : α → α → β} {g : α → β → α} (h : ∀ x y, f x (g x y) = y) (x : α)
    (s : List β) : pairmap f x (scanl g x s) = s := by
  induction s generalizing x with
  | nil => rfl
  | cons y s ih => rw [scanl_cons, pairmap_cons, h, ih]

/-- math-comp `pairmapK`: `scanl g x` cancels `pairmap f x` when `g x` cancels `f x`. -/
theorem pairmapK {f : α → α → β} {g : α → β → α} (h : ∀ x y, g x (f x y) = y) (x : α)
    (s : List α) : scanl g x (pairmap f x s) = s := by
  induction s generalizing x with
  | nil => rfl
  | cons y s ih => rw [pairmap_cons, scanl_cons, h, ih]

end SeqOps

/-! ### Colors -/

/-- Coq `color`: the four colors. -/
inductive Color : Type where
  /-- The color with bits `00` (Coq `Color0`). -/
  | Color0
  /-- The color with bits `01` (Coq `Color1`). -/
  | Color1
  /-- The color with bits `10` (Coq `Color2`). -/
  | Color2
  /-- The color with bits `11` (Coq `Color3`). -/
  | Color3
  deriving Repr, Inhabited

export Color (Color0 Color1 Color2 Color3)

/-- Coq notation `palette c0 c1 c2 c3`: the function mapping `ColorI` to `cI`. -/
def palette {α : Sort u} (c0 c1 c2 c3 : α) : Color → α
  | Color0 => c0
  | Color1 => c1
  | Color2 => c2
  | Color3 => c3

/-- `palette` on `Color0`. -/
@[simp] theorem palette_Color0 {α : Sort u} (c0 c1 c2 c3 : α) :
    palette c0 c1 c2 c3 Color0 = c0 := rfl

/-- `palette` on `Color1`. -/
@[simp] theorem palette_Color1 {α : Sort u} (c0 c1 c2 c3 : α) :
    palette c0 c1 c2 c3 Color1 = c1 := rfl

/-- `palette` on `Color2`. -/
@[simp] theorem palette_Color2 {α : Sort u} (c0 c1 c2 c3 : α) :
    palette c0 c1 c2 c3 Color2 = c2 := rfl

/-- `palette` on `Color3`. -/
@[simp] theorem palette_Color3 {α : Sort u} (c0 c1 c2 c3 : α) :
    palette c0 c1 c2 c3 Color3 = c3 := rfl

/-! Color comparison and sum; the sum is used to compute traces, so it is taken as
primitive. -/

/-- Coq `addc` (notation `c1 +c c2`): the bitwise sum (xor) of two colors. -/
def addc : Color → Color → Color :=
  palette id (palette Color1 Color0 Color3 Color2)
    (palette Color2 Color3 Color0 Color1)
    (palette Color3 Color2 Color1 Color0)

/-- Coq `eqc`: color comparison, `c = c'` iff `addc c c' = Color0`. -/
def eqc (c c' : Color) : Bool :=
  match addc c c' with
  | Color0 => true
  | _ => false

/-- Coq `eqcP`: `eqc` reflects equality. -/
theorem eqcP {c1 c2 : Color} : eqc c1 c2 = true ↔ c1 = c2 := by
  cases c1 <;> cases c2 <;> simp [eqc, addc, palette]

/-- The decidable equality of colors, computed with `eqc` (Coq `hasDecEq.Build color eqcP`). -/
instance : DecidableEq Color := fun _ _ => decidable_of_iff _ eqcP

/-- Coq `eqcE`: `eqc` is the boolean equality test of colors. -/
theorem eqcE : eqc = fun c1 c2 => decide (c1 = c2) := by
  funext c1 c2
  cases c1 <;> cases c2 <;> rfl

/-- `Color` is a finite type (Coq `predArgType` / `finType` structure of `color`). -/
instance : Fintype Color where
  elems := ⟨↑[Color0, Color1, Color2, Color3], by decide⟩
  complete c := by cases c <;> decide

/-! Algebraic properties of `addc`. -/

/-- Coq `addcA`. -/
theorem addcA (c1 c2 c3 : Color) : addc c1 (addc c2 c3) = addc (addc c1 c2) c3 := by
  cases c1 <;> cases c2 <;> cases c3 <;> rfl

/-- Coq `addcC`. -/
theorem addcC (c1 c2 : Color) : addc c1 c2 = addc c2 c1 := by
  cases c1 <;> cases c2 <;> rfl

/-- Coq `add0c`. -/
@[simp] theorem add0c (c : Color) : addc Color0 c = c := by cases c <;> rfl

/-- Coq `addc0`. -/
@[simp] theorem addc0 (c : Color) : addc c Color0 = c := by cases c <;> rfl

/-- Coq `addcc`. -/
@[simp] theorem addcc (c : Color) : addc c c = Color0 := by cases c <;> rfl

/-- Coq `addKc`. -/
@[simp] theorem addKc (c1 c2 : Color) : addc c1 (addc c1 c2) = c2 := by
  cases c1 <;> cases c2 <;> rfl

/-- Coq `addcK`. -/
@[simp] theorem addcK (c1 c2 : Color) : addc (addc c1 c2) c2 = c1 := by
  cases c1 <;> cases c2 <;> rfl

/-- Coq `addcI`. -/
theorem addcI (c : Color) : Injective (addc c) := fun c1 c2 h => by
  rw [← addKc c c1, h, addKc]

/-- Coq `addc_eq0`. -/
theorem addc_eq0 (c1 c2 : Color) : addc c1 c2 = Color0 ↔ c1 = c2 := by
  cases c1 <;> cases c2 <;> decide

/-! Colors as bit vectors. -/

/-- Coq `cbit0`: the lower bit of a color (`true` for `Color1` and `Color3`). -/
def cbit0 : Color → Bool := palette false true false true

/-- Coq `cbit1`: the higher bit of a color (`true` for `Color2` and `Color3`). -/
def cbit1 : Color → Bool := palette false false true true

/-- Coq `ccons b1 b0`: the color `2 b1 + b0`. -/
def ccons : Bool → Bool → Color
  | false, false => Color0
  | false, true => Color1
  | true, false => Color2
  | true, true => Color3

/-- The lower bit of `Color0`. -/
@[simp] theorem cbit0_Color0 : cbit0 Color0 = false := rfl
/-- The lower bit of `Color1`. -/
@[simp] theorem cbit0_Color1 : cbit0 Color1 = true := rfl
/-- The lower bit of `Color2`. -/
@[simp] theorem cbit0_Color2 : cbit0 Color2 = false := rfl
/-- The lower bit of `Color3`. -/
@[simp] theorem cbit0_Color3 : cbit0 Color3 = true := rfl
/-- The higher bit of `Color0`. -/
@[simp] theorem cbit1_Color0 : cbit1 Color0 = false := rfl
/-- The higher bit of `Color1`. -/
@[simp] theorem cbit1_Color1 : cbit1 Color1 = false := rfl
/-- The higher bit of `Color2`. -/
@[simp] theorem cbit1_Color2 : cbit1 Color2 = true := rfl
/-- The higher bit of `Color3`. -/
@[simp] theorem cbit1_Color3 : cbit1 Color3 = true := rfl

/-- Coq `ccons_cbits`. -/
theorem ccons_cbits (c : Color) : ccons (cbit1 c) (cbit0 c) = c := by cases c <;> rfl

/-- Coq `cbit1_ccons`. -/
theorem cbit1_ccons (b1 b0 : Bool) : cbit1 (ccons b1 b0) = b1 := by
  cases b1 <;> cases b0 <;> rfl

/-- Coq `cbit0_ccons`. -/
theorem cbit0_ccons (b1 b0 : Bool) : cbit0 (ccons b1 b0) = b0 := by
  cases b1 <;> cases b0 <;> rfl

/-- Coq `cbit1_addc`. -/
theorem cbit1_addc (c1 c2 : Color) : cbit1 (addc c1 c2) = (cbit1 c1 ^^ cbit1 c2) := by
  cases c1 <;> cases c2 <;> rfl

/-- Coq `cbit0_addc`. -/
theorem cbit0_addc (c1 c2 : Color) : cbit0 (addc c1 c2) = (cbit0 c1 ^^ cbit0 c2) := by
  cases c1 <;> cases c2 <;> rfl

/-! ### Edge permutations: the six permutations that leave `Color0` unchanged -/

/-- Coq `edge_perm`: the six permutations of the colors that fix `Color0`; `EpermIJK` maps
`Color1`, `Color2`, `Color3` to `ColorI`, `ColorJ`, `ColorK`, respectively. -/
inductive EdgePerm : Type where
  /-- The identity (Coq `Eperm123`). -/
  | Eperm123
  /-- Swap `Color2` and `Color3` (Coq `Eperm132`). -/
  | Eperm132
  /-- Swap `Color1` and `Color2` (Coq `Eperm213`). -/
  | Eperm213
  /-- `Color1 ↦ Color2 ↦ Color3 ↦ Color1` (Coq `Eperm231`). -/
  | Eperm231
  /-- `Color1 ↦ Color3 ↦ Color2 ↦ Color1` (Coq `Eperm312`). -/
  | Eperm312
  /-- Swap `Color1` and `Color3` (Coq `Eperm321`). -/
  | Eperm321
  deriving DecidableEq, Repr, Inhabited

export EdgePerm (Eperm123 Eperm132 Eperm213 Eperm231 Eperm312 Eperm321)

/-- `EdgePerm` is a finite type. -/
instance : Fintype EdgePerm where
  elems := ⟨↑[Eperm123, Eperm132, Eperm213, Eperm231, Eperm312, Eperm321], by decide⟩
  complete g := by cases g <;> decide

/-- Coq `permc g`: the color permutation denoted by `g : EdgePerm`. -/
def permc : EdgePerm → Color → Color
  | Eperm123 => fun c => c
  | Eperm132 => palette Color0 Color1 Color3 Color2
  | Eperm213 => palette Color0 Color2 Color1 Color3
  | Eperm231 => palette Color0 Color2 Color3 Color1
  | Eperm312 => palette Color0 Color3 Color1 Color2
  | Eperm321 => palette Color0 Color3 Color2 Color1

/-- Coq `Coercion permc : edge_perm >-> Funclass`. -/
instance : CoeFun EdgePerm (fun _ => Color → Color) := ⟨permc⟩

/-- Coq `inv_eperm g`: the inverse of `g`. -/
def invEperm (g : EdgePerm) : EdgePerm :=
  match g with
  | Eperm312 => Eperm231
  | Eperm231 => Eperm312
  | _ => g

/-- Coq `inv_epermK`. -/
theorem inv_epermK : Involutive invEperm := by
  intro g; cases g <;> rfl

/-- Coq `inv_permc`: `invEperm g` cancels `g`. -/
theorem inv_permc (g : EdgePerm) (c : Color) : invEperm g (g c) = c := by
  cases g <;> cases c <;> rfl

/-- Coq `permc_inv`: `g` cancels `invEperm g`. -/
theorem permc_inv (g : EdgePerm) (c : Color) : g (invEperm g c) = c := by
  cases g <;> cases c <;> rfl

/-- Coq `permc_inj`. -/
theorem permc_inj (g : EdgePerm) : Injective (permc g) := fun c1 c2 h => by
  rw [← inv_permc g c1, ← inv_permc g c2]
  exact congrArg (permc (invEperm g)) h

/-- Coq `permc_addc`. -/
theorem permc_addc (g : EdgePerm) (c1 c2 : Color) : g (addc c1 c2) = addc (g c1) (g c2) := by
  cases g <;> cases c1 <;> cases c2 <;> rfl

/-- Coq `permc0`. -/
@[simp] theorem permc0 (g : EdgePerm) : g Color0 = Color0 := by cases g <;> rfl

/-- The value of `color_inj_permc` on `Color3` is forced by injectivity. -/
private theorem eq_permc_of_inj {f : Color → Color} (hf : Injective f) (g : EdgePerm)
    (h0 : f Color0 = Color0) (h1 : f Color1 = g Color1) (h2 : f Color2 = g Color2) :
    ∀ c, f c = g c := by
  intro c
  cases c
  · rw [h0, permc0]
  · exact h1
  · exact h2
  · have h03 : f Color3 ≠ f Color0 := fun h => nomatch hf h
    have h13 : f Color3 ≠ f Color1 := fun h => nomatch hf h
    have h23 : f Color3 ≠ f Color2 := fun h => nomatch hf h
    rw [h0] at h03
    rw [h1] at h13
    rw [h2] at h23
    revert h03 h13 h23
    generalize f Color3 = x
    cases g <;> cases x <;> decide

/-- Coq `color_inj_permc`: an injective color map fixing `Color0` is an edge permutation.
(The Coq lemma has a `sig` conclusion; this is a `def` returning a subtype.) -/
def color_inj_permc (f : Color → Color) (hf : Injective f) (h0 : f Color0 = Color0) :
    {g : EdgePerm // ∀ c, f c = g c} :=
  match h1 : f Color1, h2 : f Color2 with
  | Color1, Color2 => ⟨Eperm123, eq_permc_of_inj hf _ h0 h1 h2⟩
  | Color1, Color3 => ⟨Eperm132, eq_permc_of_inj hf _ h0 h1 h2⟩
  | Color2, Color1 => ⟨Eperm213, eq_permc_of_inj hf _ h0 h1 h2⟩
  | Color2, Color3 => ⟨Eperm231, eq_permc_of_inj hf _ h0 h1 h2⟩
  | Color3, Color1 => ⟨Eperm312, eq_permc_of_inj hf _ h0 h1 h2⟩
  | Color3, Color2 => ⟨Eperm321, eq_permc_of_inj hf _ h0 h1 h2⟩
  | Color0, _ => absurd (hf (h1.trans h0.symm)) (by decide)
  | _, Color0 => absurd (hf (h2.trans h0.symm)) (by decide)
  | Color1, Color1 => absurd (hf (h1.trans h2.symm)) (by decide)
  | Color2, Color2 => absurd (hf (h1.trans h2.symm)) (by decide)
  | Color3, Color3 => absurd (hf (h1.trans h2.symm)) (by decide)

/-- Coq `other_colors`: if `c ≠ Color0`, then `Color0`, `c`, `Eperm312 c` and `Eperm231 c`
are all the colors (Coq: `pred4 Color0 c (Eperm312 c) (Eperm231 c) =i color`). -/
theorem other_colors {c : Color} (hc : c ≠ Color0) (x : Color) :
    x = Color0 ∨ x = c ∨ x = Eperm312 c ∨ x = Eperm231 c := by
  cases c
  · exact absurd rfl hc
  all_goals cases x <;> decide

/-! ### Traces

Basic operations on edge traces = pairwise sums of the list of colors on a configuration
perimeter.  Many of these operations use permutations of the non-zero colors, so we
introduce an explicit enumeration of these six permutations.  A "proper" trace, one that
begins with a non-zero color, has a "normal" tail, obtained by applying the rotation that
sends the first color to `Color1` to the rest of the trace.  A trace is even if `Color3`
does not occur before `Color2` in its tail.  To cut our work in half, we only consider even
traces in our algorithm, as the match relation is invariant under swapping `Color2` and
`Color3`.  The coloring function outputs directly the even trace tail of colorings, so we
prove here that this is invariant under permutations of the coloring.

Allowing `Color0` in traces allows us to carry fewer side conditions in our lemmas, and gives
us a convenient "bad" value as well.

Finally, we define a completion operation that adds the last "cyclic" sum to a trace, and
prove its basic properties.  These will be used with the "canonical" match relation. -/

/-- Coq `colseq`: sequences of colors (perimeter colorings and edge traces). -/
abbrev Colseq := List Color

/-- Coq `head_color`: the first color of a sequence, defaulting to `Color0`. -/
def headColor (et : Colseq) : Color := et.headD Color0

/-- Coq `proper_trace`: the boolean correctness predicate of traces, `et` does not start
with `Color0`. -/
def properTrace (et : Colseq) : Bool := headColor et != Color0

/-! Conversion from color lists to traces is done in two steps: compute the pairwise sum to
get a partial (linear) trace, then append the last color, which can be computed as the sum
of the partial trace, to get a full (cyclic) trace.  The trace computation inverse just
computes partial sums. -/

/-- Coq `ptrace`: the partial trace of a perimeter coloring. -/
def ptrace (lc : Colseq) : Colseq :=
  match lc with
  | c :: lc' => pairmap addc c lc'
  | [] => []

/-- Coq `permt g`: `g` mapped over a trace. -/
def permt (g : EdgePerm) : Colseq → Colseq := List.map (permc g)

/-- Coq `sumt`: the sum of all the colors of a trace. -/
def sumt : Colseq → Color := List.foldr addc Color0

/-- Coq `ctrace`: completion of a partial trace with its last color. -/
def ctrace (et : Colseq) : Colseq := et ++ [sumt et]

/-- Coq `trace`: the (cyclic) trace of a perimeter coloring. -/
def trace (lc : Colseq) : Colseq :=
  match lc with
  | _ :: _ => ctrace (ptrace lc)
  | [] => []

/-- Coq `urtrace`: the right-rotated trace of a perimeter coloring. -/
def urtrace (lc : Colseq) : Colseq := pairmap addc (last Color0 lc) lc

/-- Coq `untrace c0 et`: the perimeter coloring with head color `c0` and trace `et`. -/
def untrace (c0 : Color) (et : Colseq) : Colseq := scanl addc c0 (belast Color0 et)

/-! Trace normalization. -/

/-- Coq `edge_rot c`: the even edge permutation mapping `c` to `Color1`, if
`c ≠ Color0`. -/
def edgeRot : Color → EdgePerm := palette Eperm123 Eperm123 Eperm312 Eperm231

/-- Coq `ttail`: the seminormalised tail of a trace (`[Color0]` if the trace is not
proper). -/
def ttail (et : Colseq) : Colseq :=
  if properTrace et then
    match et with
    | c :: et' => permt (edgeRot c) et'
    | [] => []
  else [Color0]

/-- Coq `even_tail`: `Color2` appears before `Color3` in the sequence. -/
def evenTail : Colseq → Bool := List.foldr (fun c b => palette b b true false c) true

/-- Coq `even_trace`. -/
def evenTrace (et : Colseq) : Bool := evenTail (ttail et)

/-- Coq `etrace_perm`: a permutation of `Color2`–`Color3` that maps `et` to an even
trace. -/
def etracePerm (et : Colseq) : EdgePerm := if evenTrace et then Eperm123 else Eperm132

/-- Coq `etrace`: the even `Color2`–`Color3` permutation of `et`. -/
def etrace (et : Colseq) : Colseq := permt (etracePerm et) et

/-- Coq `etail`: the normalised, even tail of `et`. -/
def etail (et : Colseq) : Colseq := permt (etracePerm et) (ttail et)

/-- Coq `eptrace`: the standardized tail of the partial trace of a perimeter coloring. -/
def eptrace (lc : Colseq) : Colseq := etail (ptrace lc)

/-- Coq `count_cbit1`: the number of colors of `s` with `cbit1` set (used to validate the
initial tree construction). -/
def countCbit1 : Colseq → ℕ := List.foldr (fun c n => (cbit1 c).toNat + n) 0

/-! Unfolding equations and small helper lemmas (not in the Coq file). -/

/-- Unfolding equation of `headColor` on `[]`. -/
@[simp] theorem headColor_nil : headColor [] = Color0 := rfl

/-- Unfolding equation of `headColor` on a cons. -/
@[simp] theorem headColor_cons (c : Color) (et : Colseq) : headColor (c :: et) = c := rfl

/-- `properTrace` as a proposition. -/
theorem properTrace_eq_true {et : Colseq} : properTrace et = true ↔ headColor et ≠ Color0 :=
  bne_iff_ne

/-- Unfolding equation of `ptrace` on `[]`. -/
@[simp] theorem ptrace_nil : ptrace [] = [] := rfl

/-- Unfolding equation of `ptrace` on a cons. -/
@[simp] theorem ptrace_cons (c : Color) (lc : Colseq) : ptrace (c :: lc) = pairmap addc c lc :=
  rfl

/-- Unfolding equation of `permt` on `[]`. -/
@[simp] theorem permt_nil (g : EdgePerm) : permt g [] = [] := rfl

/-- Unfolding equation of `permt` on a cons. -/
@[simp] theorem permt_cons (g : EdgePerm) (c : Color) (et : Colseq) :
    permt g (c :: et) = g c :: permt g et := rfl

/-- `permt` distributes over concatenation. -/
theorem permt_append (g : EdgePerm) (et et' : Colseq) :
    permt g (et ++ et') = permt g et ++ permt g et' := List.map_append

/-- Unfolding equation of `sumt` on `[]`. -/
@[simp] theorem sumt_nil : sumt [] = Color0 := rfl

/-- Unfolding equation of `sumt` on a cons. -/
@[simp] theorem sumt_cons (c : Color) (et : Colseq) : sumt (c :: et) = addc c (sumt et) := rfl

/-- `sumt` of a concatenation (math-comp `foldr_cat` for `sumt`). -/
theorem sumt_append (et et' : Colseq) : sumt (et ++ et') = addc (sumt et) (sumt et') := by
  induction et with
  | nil => simp
  | cons c et ih => rw [List.cons_append, sumt_cons, sumt_cons, ih, addcA]

/-- Unfolding equation of `trace` on `[]`. -/
@[simp] theorem trace_nil : trace [] = [] := rfl

/-- Unfolding equation of `trace` on a cons (see also `trace_cons`). -/
theorem trace_cons_eq (c : Color) (lc : Colseq) : trace (c :: lc) = ctrace (pairmap addc c lc) :=
  rfl

/-- Unfolding equation of `evenTail` on `[]`. -/
@[simp] theorem evenTail_nil : evenTail [] = true := rfl

/-- Unfolding equation of `evenTail` on a cons. -/
@[simp] theorem evenTail_cons (c : Color) (et : Colseq) :
    evenTail (c :: et) = palette (evenTail et) (evenTail et) true false c := rfl

/-- Unfolding equation of `countCbit1` on `[]`. -/
@[simp] theorem countCbit1_nil : countCbit1 [] = 0 := rfl

/-- Unfolding equation of `countCbit1` on a cons. -/
@[simp] theorem countCbit1_cons (c : Color) (et : Colseq) :
    countCbit1 (c :: et) = (cbit1 c).toNat + countCbit1 et := rfl

/-- `ttail` of a proper trace. -/
theorem ttail_cons_of_ne {c : Color} (hc : c ≠ Color0) (et : Colseq) :
    ttail (c :: et) = permt (edgeRot c) et := by
  cases c
  · exact absurd rfl hc
  all_goals rfl

/-- `edgeRot c` maps `c` to `Color1`, if `c ≠ Color0`. -/
theorem edgeRot_self {c : Color} (hc : c ≠ Color0) : edgeRot c c = Color1 := by
  cases c
  · exact absurd rfl hc
  all_goals rfl

/-- `permt (invEperm g)` cancels `permt g` (math-comp `mapK (inv_permc g)`). -/
theorem permt_inv (g : EdgePerm) (et : Colseq) : permt (invEperm g) (permt g et) = et := by
  induction et with
  | nil => rfl
  | cons c et ih => rw [permt_cons, permt_cons, ih, inv_permc]

/-! Lemmas for edge permutations: the standard iso lemmas, and commutation with `addc`
(proved by brute force). -/

/-! Trace permutation. -/

/-- Coq `permt_id`. -/
theorem permt_id (et : Colseq) : permt Eperm123 et = et := List.map_id' et

/-- Coq `etrace_id`. -/
theorem etrace_id (et : Colseq) : permt Eperm132 (permt Eperm132 et) = et :=
  permt_inv Eperm132 et

/-- Coq `permc_eq0`. -/
theorem permc_eq0 (g : EdgePerm) (c : Color) : g c = Color0 ↔ c = Color0 := by
  cases g <;> cases c <;> decide

/-- Coq `memc0_permt`. -/
theorem memc0_permt (g : EdgePerm) (et : Colseq) : Color0 ∈ permt g et ↔ Color0 ∈ et := by
  simp only [permt, List.mem_map]
  constructor
  · rintro ⟨c, hc, h⟩
    rwa [(permc_eq0 g c).1 h] at hc
  · intro h
    exact ⟨Color0, h, permc0 g⟩

/-- Coq `proper_permt`. -/
theorem proper_permt (g : EdgePerm) (et : Colseq) : properTrace (permt g et) = properTrace et := by
  cases et with
  | nil => rfl
  | cons c et => cases g <;> cases c <;> rfl

/-- Coq `memc0_ttail`. -/
theorem memc0_ttail (et : Colseq) :
    Color0 ∈ ttail et ↔ properTrace et = false ∨ Color0 ∈ et := by
  cases et with
  | nil => simp [ttail, properTrace]
  | cons c et =>
    cases c
    · simp [ttail, properTrace]
    all_goals simp [ttail_cons_of_ne, memc0_permt, properTrace]

/-! Even and tail permutations. -/

private theorem evenTail_permt132 {t : Colseq} (h : evenTail t = false) :
    evenTail (permt Eperm132 t) = true := by
  induction t with
  | nil => exact absurd h (by decide)
  | cons c t ih => cases c <;> simp_all [permc]

/-- Coq `even_etail`. -/
theorem even_etail (et : Colseq) : evenTail (etail et) = true := by
  unfold etail etracePerm
  cases h : evenTrace et
  · exact evenTail_permt132 h
  · rw [ite_eq_left rfl, permt_id]
    exact h

private theorem ttail_permt132 (et : Colseq) :
    ttail (permt Eperm132 et) = permt Eperm132 (ttail et) := by
  cases et with
  | nil => rfl
  | cons c et =>
    cases c
    · rfl
    all_goals
      rw [permt_cons, ttail_cons_of_ne (by decide), ttail_cons_of_ne (by decide)]
      simp only [permt, List.map_map]
      exact List.map_congr_left fun c _ => by cases c <;> rfl

/-- Coq `ttail_etrace`. -/
theorem ttail_etrace (et : Colseq) : ttail (etrace et) = etail et := by
  unfold etail etrace etracePerm
  cases evenTrace et
  · exact ttail_permt132 et
  · rw [ite_eq_left rfl, permt_id, permt_id]

/-- Coq `even_etrace`. -/
theorem even_etrace (et : Colseq) : evenTrace (etrace et) = true := by
  rw [evenTrace, ttail_etrace, even_etail]

/-- Coq `compose_permt`: the composite of two edge permutations, on a trace.  (The Coq lemma
has a `sig` conclusion; this is a `def` returning a subtype.) -/
def compose_permt (g g' : EdgePerm) (et : Colseq) :
    {h : EdgePerm // permt h et = permt g (permt g' et)} :=
  let h := color_inj_permc (fun c => g (g' c)) ((permc_inj g).comp (permc_inj g'))
    (by simp only [permc0])
  ⟨h.1, by
    simp only [permt, List.map_map]
    exact List.map_congr_left fun c _ => (h.2 c).symm⟩

/-- Coq `etail_perm`: a proper trace is an edge permutation of `Color1 :: etail et`.  (The
Coq lemma has a `sig` conclusion; this is a `def` returning a subtype.) -/
def etail_perm : (et : Colseq) → properTrace et = true →
    {g : EdgePerm // permt g et = Color1 :: etail et}
  | [], hp => absurd hp (by decide)
  | c :: et', hp =>
    let g := compose_permt (edgeRot (etracePerm (c :: et') c)) (etracePerm (c :: et')) (c :: et')
    ⟨g.1, by
      have hc : etracePerm (c :: et') c ≠ Color0 := by
        rw [Ne, permc_eq0]
        rintro rfl
        simp [properTrace] at hp
      rw [g.2, ← ttail_etrace, etrace, permt_cons, permt_cons, ttail_cons_of_ne hc,
        edgeRot_self hc]⟩

/-- `permt Eperm132 t = t` for a sequence `t` such that `t` and `permt Eperm132 t` are both
even. -/
private theorem permt132_eq_of_even {t : Colseq} (h1 : evenTail t = true)
    (h2 : evenTail (permt Eperm132 t) = true) : permt Eperm132 t = t := by
  induction t with
  | nil => rfl
  | cons c t ih => cases c <;> simp_all [permc]

/-- Coq `etail_permt`. -/
theorem etail_permt (g : EdgePerm) (et : Colseq) : etail (permt g et) = etail et := by
  cases hp : properTrace et
  · have hp' : properTrace (permt g et) = false := by rw [proper_permt, hp]
    simp only [etail, ttail, hp, hp', Bool.false_eq_true, ite_false]
    cases etracePerm (permt g et) <;> cases etracePerm et <;> rfl
  · obtain ⟨h, Dhet⟩ := etail_perm et hp
    obtain ⟨h', Dh'et⟩ := etail_perm (permt g et) (by rw [proper_permt, hp])
    obtain ⟨g', Dg'et⟩ := compose_permt h' g et
    obtain ⟨g'', Eg''⟩ := compose_permt g' (invEperm h) (permt h et)
    rw [permt_inv, Dg'et, Dh'et, Dhet, permt_cons, List.cons.injEq] at Eg''
    obtain ⟨g''1, Eg⟩ := Eg''
    have e1 := even_etail et
    have e2 := even_etail (permt g et)
    rw [← Eg] at e2 ⊢
    cases g'' <;> first
      | exact absurd g''1 (by decide)
      | exact permt_id _
      | exact permt132_eq_of_even e1 e2

/-! Perimeter-trace equations. -/

/-- Coq `ptrace_addc`. -/
theorem ptrace_addc (c : Color) (lc : Colseq) : ptrace (lc.map (addc c)) = ptrace lc := by
  cases lc with
  | nil => rfl
  | cons c' lc =>
    rw [List.map_cons, ptrace_cons, ptrace_cons]
    induction lc generalizing c' with
    | nil => rfl
    | cons c'' lc ih =>
      rw [List.map_cons, pairmap_cons, pairmap_cons, ih, addcC c c', ← addcA, addKc]

/-- Coq `ptrace_permt`. -/
theorem ptrace_permt (g : EdgePerm) (lc : Colseq) : ptrace (permt g lc) = permt g (ptrace lc) := by
  cases lc with
  | nil => rfl
  | cons c lc =>
    rw [permt_cons, ptrace_cons, ptrace_cons]
    induction lc generalizing c with
    | nil => rfl
    | cons c' lc ih => rw [permt_cons, pairmap_cons, pairmap_cons, ih, permt_cons, permc_addc]

/-- Coq `eptrace_inj`. -/
theorem eptrace_inj (lc : Colseq) {f : Color → Color} (hf : Injective f) :
    eptrace (lc.map f) = eptrace lc := by
  unfold eptrace
  rw [← ptrace_addc (f Color0), List.map_map]
  obtain ⟨g, hg⟩ := color_inj_permc (addc (f Color0) ∘ f) ((addcI _).comp hf)
    (by simp only [comp_apply, addcc])
  have : lc.map (addc (f Color0) ∘ f) = permt g lc := List.map_congr_left fun c _ => hg c
  rw [this, ptrace_permt, etail_permt]

/-! Properties of the trace completion. -/

/-- Coq `sumt_ctrace`. -/
theorem sumt_ctrace (et : Colseq) : sumt (ctrace et) = Color0 := by
  rw [ctrace, sumt_append, sumt_cons, sumt_nil, addc0, addcc]

/-- Coq `memc0_ctrace`. -/
theorem memc0_ctrace (et : Colseq) : Color0 ∈ ctrace et ↔ sumt et = Color0 ∨ Color0 ∈ et := by
  rw [ctrace, List.mem_append, List.mem_singleton, eq_comm, or_comm]

/-- Coq `proper_ctrace`. -/
theorem proper_ctrace (et : Colseq) : properTrace (ctrace et) = properTrace et := by
  cases et <;> rfl

/-- Coq `sumt_permt`. -/
theorem sumt_permt (g : EdgePerm) (et : Colseq) : sumt (permt g et) = g (sumt et) := by
  induction et with
  | nil => exact (permc0 g).symm
  | cons c et ih => rw [permt_cons, sumt_cons, sumt_cons, ih, permc_addc]

/-- Coq `ctrace_permt`. -/
theorem ctrace_permt (g : EdgePerm) (et : Colseq) : ctrace (permt g et) = permt g (ctrace et) := by
  rw [ctrace, ctrace, permt_append, sumt_permt]
  rfl

private theorem even_ctrace_aux (g : EdgePerm) (et : Colseq) :
    ∀ e : Color, cbit1 (g e) = false →
      evenTail (permt g (et ++ [addc e (sumt et)])) = evenTail (permt g et) := by
  induction et with
  | nil =>
    intro e he
    rw [List.nil_append, sumt_nil, addc0, permt_cons, permt_nil, evenTail_cons, evenTail_nil]
    revert he
    cases g e <;> decide
  | cons e' et ih =>
    intro e he
    rw [List.cons_append, permt_cons, permt_cons, evenTail_cons, evenTail_cons, sumt_cons,
      addcA]
    have key := ih (addc e e')
    rw [permc_addc, cbit1_addc, he] at key
    revert key
    cases g e' <;> simp [cbit1]

/-- Coq `even_ctrace`. -/
theorem even_ctrace (et : Colseq) : evenTrace (ctrace et) = evenTrace et := by
  cases et with
  | nil => rfl
  | cons e et =>
    cases e
    · rfl
    all_goals
      rw [evenTrace, evenTrace, ctrace, List.cons_append, ttail_cons_of_ne (by decide),
        ttail_cons_of_ne (by decide), sumt_cons]
      exact even_ctrace_aux _ et _ rfl

/-- Coq `ctrace_inj`. -/
theorem ctrace_inj : Injective ctrace := fun _ _ h =>
  (List.append_inj' h rfl).1

/-! Properties of the full (cyclic) trace. -/

/-- Coq `trace_permt`. -/
theorem trace_permt (g : EdgePerm) (lc : Colseq) : trace (permt g lc) = permt g (trace lc) := by
  cases lc with
  | nil => rfl
  | cons c lc =>
    show ctrace (ptrace (permt g (c :: lc))) = permt g (ctrace (ptrace (c :: lc)))
    rw [ptrace_permt, ctrace_permt]

/-- Coq `size_trace`. -/
theorem size_trace (lc : Colseq) : (trace lc).length = lc.length := by
  cases lc with
  | nil => rfl
  | cons c lc => simp [trace_cons_eq, ctrace]

private theorem sumt_belast (x : Color) (s : Colseq) :
    addc (sumt (belast x s)) (last x s) = sumt (x :: s) := by
  induction s generalizing x with
  | nil => simp
  | cons y s ih => rw [belast_cons, last_cons, sumt_cons, ← addcA, ih]; rfl

/-- Coq `trace_untrace`. -/
theorem trace_untrace (c0 : Color) {et : Colseq} (h : sumt et = Color0) :
    trace (untrace c0 et) = et := by
  cases et with
  | nil => rfl
  | cons e1 et =>
    show ctrace (ptrace (scanl addc c0 (Color0 :: belast e1 et))) = e1 :: et
    rw [scanl_cons, ptrace_cons, scanlK (fun x y => addKc x y), ctrace, lastI e1 et]
    congr 2
    have := sumt_belast e1 et
    rw [h, addc_eq0] at this
    exact this

/-- Coq `sumt_trace`. -/
theorem sumt_trace (lc : Colseq) : sumt (trace lc) = Color0 := by
  cases lc with
  | nil => rfl
  | cons c lc => exact sumt_ctrace _

/-- Coq `untrace_trace`. -/
theorem untrace_trace (c0 : Color) (lc : Colseq) : untrace c0 (trace (c0 :: lc)) = c0 :: lc := by
  rw [untrace, trace_cons_eq, ctrace, belast_concat, scanl_cons, addc0,
    pairmapK (fun x y => addKc x y)]

/-- Coq `trace_addc`. -/
theorem trace_addc (c : Color) (lc : Colseq) : trace (lc.map (addc c)) = trace lc := by
  cases lc with
  | nil => rfl
  | cons c0 lc =>
    show ctrace (ptrace ((c0 :: lc).map (addc c))) = ctrace (ptrace (c0 :: lc))
    rw [ptrace_addc]

private theorem sumt_pairmap (c : Color) (lc : Colseq) :
    sumt (pairmap addc c lc) = addc c (last c lc) := by
  induction lc generalizing c with
  | nil => simp
  | cons c' lc ih => rw [pairmap_cons, sumt_cons, ih, last_cons, ← addcA, addKc]

/-- Coq `trace_cons`. -/
theorem trace_cons (c : Color) (lc : Colseq) : trace (c :: lc) = pairmap addc c (lc ++ [c]) := by
  rw [trace_cons_eq, ctrace, pairmap_append, sumt_pairmap, pairmap_cons, pairmap_nil,
    addcC]

/-- Coq `trace_rcons`. -/
theorem trace_rcons (c : Color) (lc : Colseq) :
    trace (lc ++ [c]) =
      match trace (c :: lc) with
      | e :: et => et ++ [e]
      | [] => lc := by
  cases lc with
  | nil => rfl
  | cons c1 lc =>
    rw [List.cons_append, trace_cons, trace_cons, List.cons_append, pairmap_cons,
      pairmap_append, last_concat, pairmap_cons, pairmap_nil, addcC]

/-- Coq `urtrace_trace`. -/
theorem urtrace_trace (lc : Colseq) : urtrace (rot 1 lc) = trace lc := by
  cases lc with
  | nil => rfl
  | cons c lc => rw [rot1_cons, trace_cons, urtrace, last_concat]

/-- Coq `urtrace_rot`. -/
theorem urtrace_rot (lc : Colseq) : urtrace (rot 1 lc) = rot 1 (urtrace lc) := by
  cases lc with
  | nil => rfl
  | cons c lc =>
    rw [rot1_cons, urtrace, urtrace, last_concat, last_cons, pairmap_cons, rot1_cons,
      pairmap_append, pairmap_cons, pairmap_nil]

/-- Coq `trace_rot`. -/
theorem trace_rot (n : ℕ) (lc : Colseq) : trace (rot n lc) = rot n (trace lc) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rcases le_or_gt lc.length n with h | h
    · rw [rot_oversize (by omega), rot_oversize (by rw [size_trace]; omega)]
    · rw [Nat.add_comm, rotD (by omega), rotD (by rw [size_trace]; omega), ← ih,
        ← urtrace_trace, ← urtrace_trace (rot n lc), ← urtrace_rot]

/-- Coq `trace_rev`. -/
theorem trace_rev (lc : Colseq) : trace lc.reverse = rot 1 (trace lc).reverse := by
  have hflip : (fun a b => addc b a) = addc := by
    funext a b
    exact addcC b a
  cases lc with
  | nil => rfl
  | cons c l =>
    rw [trace_cons, reverse_pairmap, last_concat, belast_concat, List.reverse_cons, hflip]
    cases h : l.reverse with
    | nil => simp [trace_cons, rot]
    | cons z zs =>
      rw [List.cons_append, trace_cons, pairmap_cons, rot1_cons,
        pairmap_append addc z (zs ++ [c]) [z], last_concat, pairmap_cons, pairmap_nil]

end FourColor
