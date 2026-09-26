/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Round
import FourColor.Engine.ColorDP

/-!
# Reducibility engine: the per-configuration kernel checks

The C-reducibility of a configuration with program `cp` (ring size `r = cprsize cp`) and
contract program `cpc` is established by a chain of kernel-checked boolean facts, each in its
own declaration (fresh kernel cache), between checkpoints `H₀, …, Hₙ` (big-number literals
generated at elaboration time):

* `checkInit r cnv cp H₀`       : the ring traces of `cp` are `expand r H₀`;
* `checkStep r τ k Hᵢ Hᵢ₊₁`     : `k` rounds map `expand r Hᵢ` to `expand r Hᵢ₊₁`;
* `checkFinal r cnv cpc Hₙ`     : the contract traces are covered by `expand r Hₙ`.

`Reducible.lean` turns such a chain into `CReducible`.
-/

namespace FourColor.Engine

open FourColor

/-- The ring traces of `cp` are the expansion of the first checkpoint. -/
def checkInit (r : Nat) (cnv : Net) (cp : Cprog) (H0 : List Nat) : Bool :=
  dpP1 r cnv cp == expand r H0

/-- `n` rounds lead from a checkpoint to the next one. -/
def checkStep (r : Nat) (tau : Net) (n : Nat) (H H' : List Nat) : Bool :=
  roundsN r tau n (expand r H) == expand r H'

/-- The contract traces are covered by the last checkpoint. -/
def checkFinal (r : Nat) (cnv : Net) (cpc : Cprog) (H : List Nat) : Bool :=
  covered (dpP1 r cnv cpc) (expand r H)

/-- A checkpoint equation gives a chain of rounds. -/
theorem reachN_of_checkStep {r : Nat} {tau : Net} {n : Nat} {H H' : List Nat}
    (h : checkStep r tau n H H' = true) : ReachN r tau (expand r H) (expand r H') :=
  reachN_of_eq (beq_iff_eq.mp h)

/-- The initial checkpoint equation. -/
theorem eq_of_checkInit {r : Nat} {cnv : Net} {cp : Cprog} {H0 : List Nat}
    (h : checkInit r cnv cp H0 = true) : dpP1 r cnv cp = expand r H0 :=
  beq_iff_eq.mp h

end FourColor.Engine
