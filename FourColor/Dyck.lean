/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/

/-!
# Dyck numbers  (port of `dyck.v`)

We define two combinatorial functions:

* `dyck n`        : the number of balanced bracket words of length `n`;
* `genDyck m n`   : the number of balanced bracket word fragments of length `n` with `m - 1`
  extra closing brackets: `dyck n = genDyck 1 n` (Coq `gen_dyck`).

These "Dyck numbers" are closely related to the well-known Catalan numbers
`C_n = (2n choose n) / (n + 1)`.  More precisely, `dyck n = C_(n/2)` if `n` is even, and `0`
if `n` is odd; the `genDyck m n` are similarly related to the Catalan-Fuss (or Raney) numbers
`A_{(n+1-m)/2}(2, m)`; however they are defined using a non-standard recurrence that simplifies
the correctness proof of the initial data of the reducibility check.  Indeed, Dyck numbers are
the only link between the initial color and (chromo)gram trees.

`genDyck` is structurally recursive on `n`, with the same case structure as the Coq
fixpoint, so that it can be evaluated by the Lean kernel.
-/

namespace FourColor

/-- Coq `gen_dyck m n`: the number of balanced bracket word fragments of length `n` with
`m - 1` extra closing brackets. -/
def genDyck (m n : Nat) : Nat :=
  match n, m with
  | 0, 1 => 1
  | n' + 1, m' + 1 => genDyck (m + 1) n' + genDyck m' n'
  | _, _ => 0

/-- Coq `dyck n`: the number of balanced bracket words of length `n`. -/
def dyck : Nat → Nat := genDyck 1

/-- Coq `gen_dyck_max`. -/
theorem gen_dyck_max {m n : Nat} (h : n + 1 < m) : genDyck m n = 0 := by
  induction n generalizing m with
  | zero =>
    match m, h with
    | m + 2, _ => rfl
  | succ n ih =>
    match m, h with
    | m + 1, h =>
      show genDyck (m + 2) n + genDyck m n = 0
      rw [ih (by omega), ih (by omega)]

/-- Coq `gen_dyck_all_close`. -/
theorem gen_dyck_all_close (m : Nat) : genDyck (m + 1) m = 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    show genDyck (m + 3) m + genDyck (m + 1) m = 1
    rw [gen_dyck_max (by omega), ih]

/-- Coq `even_dyck_pos`. -/
theorem even_dyck_pos (n : Nat) : 0 < dyck (2 * n) := by
  have key : ∀ m, 0 < genDyck (m + 1) (2 * n + m) := by
    induction n with
    | zero =>
      intro m
      rw [Nat.mul_zero, Nat.zero_add, gen_dyck_all_close]
      exact Nat.one_pos
    | succ n ih =>
      intro m
      have e : 2 * (n + 1) + m = (2 * n + (m + 1)) + 1 := by omega
      rw [e]
      show 0 < genDyck (m + 2) (2 * n + (m + 1)) + genDyck m (2 * n + (m + 1))
      exact Nat.lt_of_lt_of_le (ih (m + 1)) (Nat.le_add_right _ _)
  exact key 0

end FourColor
