/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Seq
import Mathlib.Data.List.Rotate

/-!
# Configuration construction programs (port of `cfmap.v`, program-level part)

Configuration maps are entered as little linear construction programs: starting from a basic
triangle, these build a sequence of concentric quasicubic maps, alternatively rotating the
perimeter and adding a single outer node (and a new region) or two adjacent ones (which close
up a region and start a new one).  See `FourColor/CfMap.lean` for the full documentation of
`cfmap.v`; this file contains the part of `cfmap.v` that only computes on programs (and not on
hypermaps).  All the definitions below are first-order and structurally recursive, so that they
can be evaluated by the Lean kernel (`decide`).

* `Cpstep`         : the basic steps of the configuration construction programs (math-comp
  `cpstep`), with constructors `R n`, `R'`, `Y`, `H`, `U`, `K`, `A` (math-comp `CpR n`,
  `CpR'`, `CpY`, `CpH`, `CpU`, `CpK`, `CpA`).
* `Cprog`          : configuration programs (`List Cpstep`, math-comp `cprog`); the actual
  construction is performed RIGHT-TO-LEFT.
* `cubicProg cp`   : `cp` consists only of `R`, `U`, `Y` and `H` steps (math-comp `cubic_prog`).
* `Config`         : configuration descriptors, which add symmetry and contract annotations to
  a configuration program (math-comp `config`, fields `cfsym`, `cfcontract_ref`, `cfprog`;
  the contract field is called `cfcontractRef`, because `cfcontract` is the name of the
  contract dart sequence computed from it in `cfcontract.v`).
* `configProg cp`  : `cp` consists only of `R`, `Y` and `H` steps, and ends with a `Y` step
  (math-comp `config_prog`).
* `ConfigSyntax`   : concrete syntax for programs and configurations (see below).
* `cprsize cp`     : the size of the ring of `cpmap cp` (math-comp `cprsize`).
* `cpksize cp`     : the number of `H` steps of `cp` (math-comp `cpksize`), which is the size
  of `cpker cp` for a well-formed configuration program.
* `Cfmask`         : a pair of bit sequences used to select faces in a configuration (math-comp
  `cfmask`); `ProperCpmask cp cm` states that the sizes match `cp` (math-comp `proper_cpmask`).
* `cfmask1 cp i`   : the mask selecting only the `i`-th kernel face (math-comp `cfmask1`).
* `cpadj cm cp`    : a mask selecting the faces adjacent to the faces selected by `cm`
  (math-comp `cpadj`; its specification `cpmask_adj` is in `FourColor/CfMap/Map.lean`).

We also define the math-comp sequence operations `rot`, `rotr` and `mask` literally (in the
namespace `FourColor.CfMap`, to avoid clashes with other ports); note that math-comp's
`rot n s` is the identity when `n ≥ size s`, unlike `List.rotate`.

## Concrete syntax

After `open FourColor.ConfigSyntax` (math-comp `Import ConfigSyntax`), the following notations
are available, where each item is a numeral `n` (for the step `R n`) or one of the identifiers
`H`, `Y`, `U` (as in the Coq development; `K`, `A` and `R'` are also accepted):

* `Cprog H 3 H 2 Y Y` is the program `[.H, .R 3, .H, .R 2, .Y, .Y]`;
* `Config* 1 2 H 2 H Y` is the symmetric configuration
  `{ cfsym := true, cfcontractRef := [1, 2], cfprog := [.H, .R 2, .H, .Y] }`;
* `Config 1 H Y` is the non-symmetric configuration
  `{ cfsym := false, cfcontractRef := [1], cfprog := [.H, .Y] }`.

As in Coq, the leading numerals of a `Config`/`Config*` form the contract annotation (the
program of a configuration always starts with an `H`).  The keywords `Cprog` and `Config` are
scoped: inside `open FourColor.ConfigSyntax` the types must be written `FourColor.Cprog` and
`FourColor.Config` (or be left to type inference).  Configurations can equivalently be written
as plain structure literals, e.g.
`{ cfsym := true, cfcontractRef := [13], cfprog := [.H, .R 3, .H, .R 5, .H, .R 5, .Y, .R 4, .H,
  .R 4, .Y, .R 2, .Y, .R 1, .Y] }`, which is equal (by `rfl`) to
`Config* 13 H 3 H 5 H 5 Y 4 H 4 Y 2 Y 1 Y`.
-/

namespace FourColor

/-! ### math-comp `rot`, `rotr` and `mask` -/

namespace CfMap

variable {α β : Type*}

/-- math-comp `rot n s`: rotation of `s` by `n` items to the left; this is the identity when
`n ≥ size s` (unlike `List.rotate`, which reduces `n` modulo the length). -/
def rot (n : ℕ) (s : List α) : List α := s.drop n ++ s.take n

/-- math-comp `rotr n s`: rotation of `s` by `n` items to the right. -/
def rotr (n : ℕ) (s : List α) : List α := rot (s.length - n) s

/-- math-comp `mask m s`: the subsequence of `s` selected by the bit sequence `m`. -/
def mask : List Bool → List α → List α
  | true :: m, x :: s => x :: mask m s
  | false :: m, _ :: s => mask m s
  | _, _ => []

/-- math-comp `mask0`. -/
@[simp] theorem mask_nil_left (s : List α) : mask [] s = [] := by cases s <;> rfl

/-- math-comp `mask0s`. -/
@[simp] theorem mask_nil_right (m : List Bool) : mask m ([] : List α) = [] := by
  cases m with
  | nil => rfl
  | cons b m => cases b <;> rfl

/-- math-comp `mask_cons` for a selected item. -/
@[simp] theorem mask_true_cons (m : List Bool) (x : α) (s : List α) :
    mask (true :: m) (x :: s) = x :: mask m s := rfl

/-- math-comp `mask_cons` for an unselected item. -/
@[simp] theorem mask_false_cons (m : List Bool) (x : α) (s : List α) :
    mask (false :: m) (x :: s) = mask m s := rfl

/-- math-comp `mask_cons`. -/
theorem mask_cons (b : Bool) (m : List Bool) (x : α) (s : List α) :
    mask (b :: m) (x :: s) = (if b then [x] else []) ++ mask m s := by
  cases b <;> rfl

/-- math-comp `mask_false`. -/
theorem mask_false (n : ℕ) (s : List α) : mask (List.replicate n false) s = [] := by
  induction n generalizing s with
  | zero => simp
  | succ n ih => cases s with
    | nil => simp
    | cons x s => rw [List.replicate_succ, mask_false_cons, ih]

/-- math-comp `mask_true`. -/
theorem mask_true {n : ℕ} {s : List α} (h : s.length ≤ n) : mask (List.replicate n true) s = s := by
  induction s generalizing n with
  | nil => simp
  | cons x s ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      rw [List.replicate_succ, mask_true_cons, ih (by simp at h; omega)]

/-- math-comp `mask_cat`. -/
theorem mask_cat {m1 m2 : List Bool} {s1 s2 : List α} (h : m1.length = s1.length) :
    mask (m1 ++ m2) (s1 ++ s2) = mask m1 s1 ++ mask m2 s2 := by
  induction s1 generalizing m1 with
  | nil =>
    cases m1 with
    | nil => simp
    | cons b m1 => simp at h
  | cons x s1 ih =>
    cases m1 with
    | nil => simp at h
    | cons b m1 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      cases b <;> simp [ih h]

/-- math-comp `map_mask`. -/
theorem map_mask (f : α → β) (m : List Bool) (s : List α) :
    (mask m s).map f = mask m (s.map f) := by
  induction s generalizing m with
  | nil => simp
  | cons x s ih =>
    cases m with
    | nil => simp
    | cons b m => cases b <;> simp [ih]

/-- math-comp `mem_mask`. -/
theorem mem_of_mem_mask {m : List Bool} {s : List α} {x : α} (h : x ∈ mask m s) : x ∈ s := by
  induction s generalizing m with
  | nil => simp at h
  | cons y s ih =>
    cases m with
    | nil => simp at h
    | cons b m =>
      cases b
      · exact List.mem_cons_of_mem _ (ih h)
      · rcases List.mem_cons.1 h with rfl | h
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih h)

/-- math-comp `size_mask`, in the form used here. -/
theorem length_mask_le (m : List Bool) (s : List α) : (mask m s).length ≤ s.length := by
  induction s generalizing m with
  | nil => simp
  | cons x s ih =>
    cases m with
    | nil => simp
    | cons b m =>
      have := ih m
      cases b
      · rw [mask_false_cons, List.length_cons]; omega
      · rw [mask_true_cons, List.length_cons, List.length_cons]; omega

/-- Membership in a masked sequence of the same size (math-comp `has_mask_cons`, membership
form): `x ∈ mask (b :: m) (y :: s)` iff `b` and `x = y`, or `x ∈ mask m s`. -/
theorem mem_mask_cons {b : Bool} {m : List Bool} {y : α} {s : List α} {x : α} :
    x ∈ mask (b :: m) (y :: s) ↔ (b = true ∧ x = y) ∨ x ∈ mask m s := by
  cases b <;> simp

/-- Existential quantification over a masked sequence (math-comp `has_mask_cons`). -/
theorem exists_mem_mask_cons {P : α → Prop} {b : Bool} {m : List Bool} {x : α} {s : List α} :
    (∃ y ∈ mask (b :: m) (x :: s), P y) ↔ (b = true ∧ P x) ∨ ∃ y ∈ mask m s, P y := by
  cases b <;> simp

/-- Existential quantification over a masked mapped sequence (math-comp `map_mask`, `has_map`). -/
theorem exists_mem_mask_map {P : β → Prop} {f : α → β} {m : List Bool} {s : List α} :
    (∃ y ∈ mask m (s.map f), P y) ↔ ∃ y ∈ mask m s, P (f y) := by
  rw [← map_mask]
  simp

/-- Existential quantification over a concatenation (math-comp `has_cat`). -/
theorem exists_mem_append' {P : α → Prop} {s t : List α} :
    (∃ y ∈ s ++ t, P y) ↔ (∃ y ∈ s, P y) ∨ ∃ y ∈ t, P y := by
  simp only [List.mem_append, or_and_right, exists_or]

/-- A mask selecting no index of the list (helper for math-comp `cpmask1`). -/
theorem mask_range'_beq_of_lt {j s : ℕ} (h : j < s) (l : List α) :
    mask ((List.range' s l.length).map (· == j)) l = [] := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, List.range'_succ, List.map_cons]
    have : (s == j) = false := by simp; omega
    rw [this, mask_false_cons, ih (by omega)]

/-- A mask selecting the index `i` of the list (helper for math-comp `cpmask1`). -/
theorem mask_range'_beq {s i : ℕ} (l : List α) (hi : i < l.length) (d : α) :
    mask ((List.range' s l.length).map (· == s + i)) l = [l.getD i d] := by
  induction l generalizing s i with
  | nil => simp at hi
  | cons a l ih =>
    rw [List.length_cons, List.range'_succ, List.map_cons]
    cases i with
    | zero =>
      rw [Nat.add_zero, beq_self_eq_true, mask_true_cons, mask_range'_beq_of_lt (by omega)]
      rfl
    | succ i =>
      have : (s == s + (i + 1)) = false := by simp
      rw [this, mask_false_cons, show s + (i + 1) = (s + 1) + i by omega,
        ih (by simpa using hi)]
      rfl

/-- math-comp `rot0`. -/
@[simp] theorem rot_zero (s : List α) : rot 0 s = s := by simp [rot]

/-- math-comp `size_rot`. -/
@[simp] theorem length_rot (n : ℕ) (s : List α) : (rot n s).length = s.length := by
  simp only [rot, List.length_append, List.length_drop, List.length_take]
  omega

/-- math-comp `size_rotr`. -/
@[simp] theorem length_rotr (n : ℕ) (s : List α) : (rotr n s).length = s.length := by
  simp [rotr]

/-- math-comp `rot_oversize`. -/
theorem rot_oversize {n : ℕ} {s : List α} (h : s.length ≤ n) : rot n s = s := by
  simp [rot, List.drop_eq_nil_of_le h, List.take_of_length_le h]

/-- math-comp `rot_size`. -/
@[simp] theorem rot_length (s : List α) : rot s.length s = s := rot_oversize le_rfl

/-- `rot` agrees with `List.rotate` for rotations by at most the length. -/
theorem rot_eq_rotate {n : ℕ} {s : List α} (h : n ≤ s.length) : rot n s = s.rotate n := by
  rcases Nat.lt_or_ge n s.length with h' | h'
  · rw [List.rotate_eq_drop_append_take h'.le, rot]
  · have : n = s.length := le_antisymm h h'
    subst this
    rw [rot_length, List.rotate_length]

/-- `rot` is always a `List.rotate`. -/
theorem rot_eq_rotate' (n : ℕ) (s : List α) : ∃ k, rot n s = s.rotate k := by
  rcases Nat.le_total n s.length with h | h
  · exact ⟨n, rot_eq_rotate h⟩
  · exact ⟨0, by rw [rot_oversize h, List.rotate_zero]⟩

/-- math-comp `mem_rot`. -/
@[simp] theorem mem_rot {n : ℕ} {s : List α} {x : α} : x ∈ rot n s ↔ x ∈ s := by
  obtain ⟨k, hk⟩ := rot_eq_rotate' n s
  rw [hk, List.mem_rotate]

/-- math-comp `rot_uniq`. -/
theorem nodup_rot {n : ℕ} {s : List α} : (rot n s).Nodup ↔ s.Nodup := by
  obtain ⟨k, hk⟩ := rot_eq_rotate' n s
  rw [hk, List.nodup_rotate]

/-- math-comp `map_rot`. -/
theorem map_rot (f : α → β) (n : ℕ) (s : List α) : (rot n s).map f = rot n (s.map f) := by
  simp [rot, List.map_drop, List.map_take]

/-- math-comp `rotK`. -/
theorem rotr_rot (n : ℕ) (s : List α) : rotr n (rot n s) = s := by
  rcases Nat.le_total n s.length with h | h
  · rw [rotr, length_rot, rot_eq_rotate h, rot_eq_rotate (by simp),
      List.rotate_rotate, Nat.add_sub_cancel' h, List.rotate_length]
  · rw [rot_oversize h, rotr, show s.length - n = 0 by omega, rot_zero]

/-- math-comp `rotrK`. -/
theorem rot_rotr (n : ℕ) (s : List α) : rot n (rotr n s) = s := by
  rcases Nat.le_total n s.length with h | h
  · have h1 := rotr_rot (s.length - n) s
    rw [rotr, length_rot, show s.length - (s.length - n) = n by omega] at h1
    rw [rotr]
    exact h1
  · rw [rotr, show s.length - n = 0 by omega, rot_zero, rot_oversize h]

/-- The head of a rotation within the list. -/
theorem head?_rot {n : ℕ} {s : List α} (h : n < s.length) : (rot n s).head? = s[n]? := by
  rw [rot, List.head?_append, List.head?_drop]
  rw [List.getElem?_eq_getElem h]
  rfl

/-- math-comp `rot1_cons`. -/
theorem rot_one_cons (x : α) (s : List α) : rot 1 (x :: s) = s ++ [x] := by
  simp [rot]

/-- math-comp `rot_add_mod`, in the case of rotations within the list. -/
theorem rot_rot {m n : ℕ} {s : List α} (h : m + n ≤ s.length) : rot m (rot n s) = rot (m + n) s := by
  rw [rot_eq_rotate (by simpa using (by omega : m ≤ s.length)), rot_eq_rotate (by omega),
    rot_eq_rotate (by omega), List.rotate_rotate, Nat.add_comm]

/-- math-comp `rev_rot`. -/
theorem reverse_rot (n : ℕ) (s : List α) : (rot n s).reverse = rotr n s.reverse := by
  rcases Nat.le_total n s.length with h | h
  · rw [rotr, List.length_reverse, rot, rot, List.reverse_append, List.drop_reverse,
      List.take_reverse, Nat.sub_sub_self h]
  · rw [rot_oversize h, rotr, List.length_reverse, show s.length - n = 0 by omega, rot_zero]

/-- math-comp `rev_rotr`. -/
theorem reverse_rotr (n : ℕ) (s : List α) : (rotr n s).reverse = rot n s.reverse := by
  have := reverse_rot n s.reverse
  rw [List.reverse_reverse] at this
  rw [← this, List.reverse_reverse]

/-- math-comp `rot_cycle` for `List.rotate` (this is `cycle_rotate` of `Geometry.lean`, which
we do not import here). -/
private theorem cycle_rotate_aux {e : α → α → Prop} (k : ℕ) (s : List α) :
    cycle e (s.rotate k) ↔ cycle e s := by
  rw [List.rotate_eq_rotate']
  induction k generalizing s with
  | zero => rw [List.rotate'_zero]
  | succ k ih =>
    cases s with
    | nil => rw [List.rotate'_nil]
    | cons a l =>
      rw [List.rotate'_cons_succ, ih]
      cases l with
      | nil => exact Iff.rfl
      | cons y p =>
        rw [List.cons_append, cycle_cons, cycle_cons, path_concat, path_concat, last_concat,
          List.cons_append, path_cons, path_concat]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h3, h1, h2⟩
        · rintro ⟨h3, h1, h2⟩
          exact ⟨⟨h1, h2⟩, h3⟩

/-- math-comp `rot_cycle`. -/
theorem cycle_rot {e : α → α → Prop} (n : ℕ) (s : List α) : cycle e (rot n s) ↔ cycle e s := by
  obtain ⟨k, hk⟩ := rot_eq_rotate' n s
  rw [hk, cycle_rotate_aux]

/-- math-comp `rotr_cycle`. -/
theorem cycle_rotr {e : α → α → Prop} (n : ℕ) (s : List α) : cycle e (rotr n s) ↔ cycle e s :=
  cycle_rot _ s

/-- math-comp `mask_rot`, in its membership form `mem_mask_rot`. -/
theorem mem_mask_rot {m : List Bool} {s : List α} (h : m.length = s.length) (n : ℕ) {x : α} :
    x ∈ mask (rot n m) (rot n s) ↔ x ∈ mask m s := by
  rcases Nat.le_total n s.length with hn | hn
  · have h1 : (m.drop n).length = (s.drop n).length := by simp [h]
    rw [rot, rot, mask_cat h1, List.mem_append, or_comm, ← List.mem_append,
      ← mask_cat (by simp [h]), List.take_append_drop, List.take_append_drop]
  · rw [rot_oversize hn, rot_oversize (h ▸ hn)]

end CfMap

open CfMap

/-! ### Configuration construction programs -/

/-- math-comp `cpstep`: the basic steps of the configuration construction programs. -/
inductive Cpstep : Type
  /-- math-comp `CpR n`: rotation around the outer ring (noop on overflow). -/
  | R (n : ℕ)
  /-- math-comp `CpR'`: single-step reverse rotation (for encodings). -/
  | R'
  /-- math-comp `CpY`: new Y junction and face. -/
  | Y
  /-- math-comp `CpH`: new H junction and face (closing an inner face). -/
  | H
  /-- math-comp `CpU`: new face, no junctions (U-shaped loop). -/
  | U
  /-- math-comp `CpK`: new K (inverted Y) junction (closing off a face). -/
  | K
  /-- math-comp `CpA`: inverted-V junction, merging neighbors of a face. -/
  | A
  deriving DecidableEq, Repr

/-- math-comp `cprog`: a configuration map construction program is just a sequence of steps.
It is interpreted RIGHT TO LEFT, starting from a simple U-shaped map. -/
abbrev Cprog : Type := List Cpstep

/-- math-comp `cubic_prog cp`: `cp` consists only of `R`, `U`, `Y` and `H` steps. -/
def cubicProg : Cprog → Bool
  | [] => true
  | .R _ :: cp => cubicProg cp
  | .U :: cp => cubicProg cp
  | .Y :: cp => cubicProg cp
  | .H :: cp => cubicProg cp
  | _ => false

/-- math-comp `config`: the configuration data comprises the construction program for the
configuration map, the reducibility contract, represented as a sequence of integers (indexing
the contract edges in the construction process), and a boolean flagging symmetrical maps, whose
reflection does not need to be checked when scanning a part for reducible patterns (see
`quiztree.v`).

The reducibility program always starts with an `H`, and ends with a `Y`; this needs to be
checked explicitly (both in `cfquiz.v` and `cfcontract.v`). The initial `H` signals the end of
the contract in the concrete syntax. The pattern-matching tree store further assumes that if a
face has arity 9, 10, or 11, it is the one containing the first dart created. -/
structure Config : Type where
  /-- math-comp `cfsym`: the (boolean) symmetry annotation. -/
  cfsym : Bool
  /-- math-comp `cfcontract_ref`: the contract annotation, a list of indices of kernel edges
  (see `cfcontract.v`, where `cfcontract` denotes the contract darts computed from it). -/
  cfcontractRef : List ℕ
  /-- math-comp `cfprog`: the configuration construction program. -/
  cfprog : Cprog
  deriving DecidableEq, Repr

/-- math-comp `config_prog cp`: `cp` consists only of `R`, `Y` and `H` steps, and ends with a
`Y` step (so the construction starts with a `Y` step). -/
def configProg : Cprog → Bool
  | .R _ :: cp => configProg cp
  | [.Y] => true
  | .Y :: cp => configProg cp
  | .H :: cp => configProg cp
  | _ => false

/-- math-comp `config_prog_cubic`. -/
theorem config_prog_cubic {cp : Cprog} (h : configProg cp) : cubicProg cp := by
  induction cp with
  | nil => simp [configProg] at h
  | cons s cp ih =>
    cases s with
    | R n => exact ih h
    | Y =>
      cases cp with
      | nil => rfl
      | cons s' cp' => exact ih h
    | H => exact ih h
    | _ => simp [configProg] at h

/-! ### Concrete syntax (math-comp `ConfigSyntax`) -/

namespace ConfigSyntax

/-- math-comp `parse_config`: split the leading `R` steps of a program as the contract
annotation. -/
def parseConfig (sym : Bool) (cc : List ℕ) : Cprog → Config
  | .R i :: cp => parseConfig sym (i :: cc) cp
  | cp => ⟨sym, cc.reverse, cp⟩

/-- The items of the configuration concrete syntax: numerals `n` (for `R n`) and the step
identifiers `H`, `Y`, `U` (and `K`, `A`, `R'`). -/
declare_syntax_cat cpitem

/-- A numeral item `n`, standing for the step `R n` (math-comp coercion `CpR : nat >-> cpstep`). -/
syntax num : cpitem

/-- An identifier item: `H`, `Y`, `U`, `K`, `A` or `R'`. -/
syntax ident : cpitem

open Lean in
/-- Expansion of a configuration syntax item into a `Cpstep` term. -/
def expandCpitem : TSyntax `cpitem → MacroM (TSyntax `term)
  | `(cpitem| $n:num) => `(FourColor.Cpstep.R $n)
  | `(cpitem| $i:ident) =>
    match i.getId with
    | `H => `(FourColor.Cpstep.H)
    | `Y => `(FourColor.Cpstep.Y)
    | `U => `(FourColor.Cpstep.U)
    | `K => `(FourColor.Cpstep.K)
    | `A => `(FourColor.Cpstep.A)
    | `R' => `(FourColor.Cpstep.R')
    | _ => Macro.throwErrorAt i "unknown configuration step, expected H, Y, U, K, A, R' or a numeral"
  | _ => Macro.throwUnsupported

/-- math-comp notation `Cprog s1 .. sn`: the program `[s1, ..., sn]`, e.g.
`Cprog H 3 H 2 Y Y = [.H, .R 3, .H, .R 2, .Y, .Y]`. -/
scoped macro (name := cprogNotation) "Cprog" items:(ppSpace cpitem)+ : term => do
  let ts ← items.mapM expandCpitem
  `(([$ts,*] : FourColor.Cprog))

/-- math-comp notation `Config* s1 .. sn`: a symmetric configuration, e.g.
`Config* 1 2 H 2 H Y = { cfsym := true, cfcontractRef := [1, 2], cfprog := Cprog H 2 H Y }`. -/
scoped macro (name := configSymNotation) "Config*" items:(ppSpace cpitem)+ : term => do
  let ts ← items.mapM expandCpitem
  `(FourColor.ConfigSyntax.parseConfig true [] [$ts,*])

/-- math-comp notation `Config s1 .. sn`: a non-symmetric configuration, e.g.
`Config 1 H Y = { cfsym := false, cfcontractRef := [1], cfprog := Cprog H Y }`. -/
scoped macro (name := configNotation) "Config" items:(ppSpace cpitem)+ : term => do
  let ts ← items.mapM expandCpitem
  `(FourColor.ConfigSyntax.parseConfig false [] [$ts,*])

end ConfigSyntax

/-! Samples (math-comp `ConfigSamples`): the pentaton map construction, and the first
reducible configuration. -/

section Samples

open ConfigSyntax

example : (Cprog H 4 Y Y) = [.H, .R 4, .Y, .Y] := rfl

example : (Config* 15 H 3 H 5 H 5 Y 4 H 4 Y 2 Y 1 Y) =
    { cfsym := true, cfcontractRef := [15],
      cfprog := [.H, .R 3, .H, .R 5, .H, .R 5, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .R 1, .Y] } :=
  rfl

example : (Config 1 2 H 3 Y) = { cfsym := false, cfcontractRef := [1, 2], cfprog := [.H, .R 3, .Y] } :=
  rfl

example : configProg (Config* 15 H 3 H 5 H 5 Y 4 H 4 Y 2 Y 1 Y).cfprog = true := by decide

end Samples

/-! ### Ring sizes, kernel sizes and face masks -/

/-- math-comp `sub2ifgt2 n`: `n - 2` if `n > 2`, else `n`. -/
def sub2ifgt2 : ℕ → ℕ
  | n + 3 => n + 1
  | n => n

/-- math-comp `cprsize cp`: the size of the ring `cpring (cpmap cp)` (see `size_ring_cpmap`). -/
def cprsize : Cprog → ℕ
  | [] => 2
  | .Y :: cp => cprsize cp + 1
  | .U :: cp => cprsize cp + 2
  | .K :: cp => cprsize cp - 2 + 1
  | .A :: cp => sub2ifgt2 (cprsize cp)
  | _ :: cp => cprsize cp

/-- The steps counted by `cpksize` (the `H` steps). -/
def isCpH : Cpstep → Bool
  | .H => true
  | _ => false

/-- math-comp `cpksize cp`: the number of `H` steps of `cp`, which is the size of `cpker cp`
when `cp` is a configuration program (see `size_cpker`). -/
def cpksize (cp : Cprog) : ℕ := cp.countP isCpH

set_option linter.dupNamespace false in
/-- math-comp `cfmask`: a pair of bit sequences, used to select faces in a configuration:
`mr` selects darts on the ring `cpring (cpmap cp)` and `mk` selects darts in `cpker cp`. -/
structure Cfmask : Type where
  /-- math-comp constructor `Cfmask mr mk`. -/
  Cfmask ::
  /-- The ring mask. -/
  mr : List Bool
  /-- The kernel mask. -/
  mk : List Bool
  deriving DecidableEq, Repr

/-- math-comp `proper_cpmask cp cm`: the masks of `cm` have the sizes of the ring and the
kernel sequence of `cpmap cp`. -/
def ProperCpmask (cp : Cprog) (cm : Cfmask) : Prop :=
  cm.mr.length = cprsize cp ∧ cm.mk.length = cpksize cp

/-- `ProperCpmask` is decidable (math-comp's `proper_cpmask` is boolean). -/
instance (cp : Cprog) (cm : Cfmask) : Decidable (ProperCpmask cp cm) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- math-comp `cfmask1 cp i`: the mask selecting only the `i`-th dart of `cpker cp`
(math-comp `mkseq (pred1 i) n` is `(List.range' 0 n).map (· == i)`). -/
def cfmask1 (cp : Cprog) (i : ℕ) : Cfmask :=
  ⟨List.replicate (cprsize cp) false, (List.range' 0 (cpksize cp)).map (· == i)⟩

/-- math-comp `proper_cpmask1`. -/
theorem proper_cpmask1 (cp : Cprog) (i : ℕ) : ProperCpmask cp (cfmask1 cp i) := by
  simp [ProperCpmask, cfmask1]

/-- math-comp `cpadj cm cp`: a mask selecting the set of faces adjacent to the set of faces of
`cpmap cp` selected by `cm`; this assumes `cp` has only `H`, `Y` and `R` steps. -/
def cpadj : Cfmask → Cprog → Cfmask
  | ⟨mr, mk⟩, .R n :: cp =>
    match cpadj ⟨rotr n mr, mk⟩ cp with
    | ⟨mr', mk'⟩ => ⟨rot n mr', mk'⟩
  | cm@⟨b0 :: b1 :: b2 :: mr, mk⟩, .Y :: cp =>
    match cpadj ⟨b0 :: b2 :: mr, mk⟩ cp with
    | ⟨a0 :: a2 :: mr', mk'⟩ => ⟨(a0 || b1) :: (b0 || b2) :: (a2 || b1) :: mr', mk'⟩
    | _ => cm
  | cm@⟨b0 :: b1 :: mr, b1' :: mk⟩, .H :: cp =>
    match cpadj ⟨b0 :: b1' :: mr, mk⟩ cp with
    | ⟨a0 :: a1 :: mr', mk'⟩ =>
      ⟨(a0 || b1) :: (b0 || (b1' || mr.headD b0)) ::
          (match mr' with
            | a2 :: mr'' => (a2 || b1) :: mr''
            | [] => mr'),
        (a1 || b1) :: mk'⟩
    | _ => cm
  | ⟨[b0, b1], []⟩, [] => ⟨[b1, b0], []⟩
  | cm, _ => cm

/-- math-comp `cpadj_proper`. -/
theorem cpadj_proper (cp : Cprog) (cm : Cfmask) (h : ProperCpmask cp cm) :
    ProperCpmask cp (cpadj cm cp) := by
  induction cp generalizing cm with
  | nil =>
    obtain ⟨mr, mk⟩ := cm
    obtain ⟨hr, hk⟩ := h
    simp only [cprsize, cpksize, List.countP_nil] at hr hk
    match mr, mk, hr, hk with
    | [b0, b1], [], _, _ => exact ⟨rfl, rfl⟩
  | cons s cp ih =>
    obtain ⟨mr, mk⟩ := cm
    obtain ⟨hr, hk⟩ := h
    cases s with
    | R n =>
      have h' : ProperCpmask cp ⟨rotr n mr, mk⟩ := ⟨by simpa [cprsize] using hr, by
        simpa [cpksize, isCpH] using hk⟩
      have := ih _ h'
      simp only [cpadj]
      revert this
      generalize cpadj ⟨rotr n mr, mk⟩ cp = cm'
      rintro ⟨h1, h2⟩
      obtain ⟨mr', mk'⟩ := cm'
      exact ⟨by simpa [cprsize] using h1, by simpa [cpksize, isCpH] using h2⟩
    | Y =>
      match mr, hr with
      | [], hr => exact ⟨hr, hk⟩
      | [b0], hr => exact ⟨hr, hk⟩
      | [b0, b1], hr => exact ⟨hr, hk⟩
      | b0 :: b1 :: b2 :: mr, hr =>
        have h' : ProperCpmask cp ⟨b0 :: b2 :: mr, mk⟩ := ⟨by simp [cprsize] at hr ⊢; omega, by
          simpa [cpksize, isCpH] using hk⟩
        have := ih _ h'
        simp only [cpadj]
        revert this
        generalize cpadj ⟨b0 :: b2 :: mr, mk⟩ cp = cm'
        rintro ⟨h1, h2⟩
        obtain ⟨mr', mk'⟩ := cm'
        match mr', h1 with
        | [], h1 => exact ⟨hr, hk⟩
        | [a0], h1 => exact ⟨hr, hk⟩
        | a0 :: a2 :: mr', h1 =>
          refine ⟨?_, by simpa [cpksize, isCpH] using h2⟩
          simp [cprsize] at h1 ⊢; omega
    | H =>
      match mr, mk, hr, hk with
      | [], mk, hr, hk => exact ⟨hr, hk⟩
      | [b0], mk, hr, hk => exact ⟨hr, hk⟩
      | b0 :: b1 :: mr, [], hr, hk => exact ⟨hr, hk⟩
      | b0 :: b1 :: mr, b1' :: mk, hr, hk =>
        have h' : ProperCpmask cp ⟨b0 :: b1' :: mr, mk⟩ := ⟨by simpa [cprsize] using hr, by
          simp [cpksize, isCpH, List.countP_cons] at hk ⊢; omega⟩
        have := ih _ h'
        simp only [cpadj]
        revert this
        generalize cpadj ⟨b0 :: b1' :: mr, mk⟩ cp = cm'
        rintro ⟨h1, h2⟩
        obtain ⟨mr', mk'⟩ := cm'
        match mr', h1 with
        | [], h1 => exact ⟨hr, hk⟩
        | [a0], h1 => exact ⟨hr, hk⟩
        | a0 :: a1 :: mr', h1 =>
          refine ⟨?_, ?_⟩
          · cases mr' <;> simp [cprsize] at h1 ⊢ <;> omega
          · simp [cpksize, isCpH, List.countP_cons] at h2 ⊢; omega
    | R' => exact ⟨hr, hk⟩
    | U => exact ⟨hr, hk⟩
    | K => exact ⟨hr, hk⟩
    | A => exact ⟨hr, hk⟩

end FourColor
