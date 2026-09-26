/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Network

/-!
# Reducibility engine: the network checks split by position

`tauCheck r net` and `cnvCheck r net` (`Network.lean`) check a delta-swap network on the `3r`
coordinate indicator sets.  Evaluated in one declaration, the check of the ring-14 networks
keeps `42` network applications on `2^21`-bit numbers in the kernel's cache: about 3.5 GB in
Lean's kernel and 4.7 GB in Palomar's checker con-ron, which checks up to 16 declarations at
once on a 32 GB machine.  This file splits
the checks into one part per position `p` (`tauCheckAt`, `cnvCheckAt`) and the layer test, so
that the generator can prove each part in its own declaration and assemble the check from them
(`tauCheck_of_parts`, `cnvCheck_of_parts`), without evaluating anything twice:

* `allFrom f p n` is `f p && f (p + 1) && … && f (p + n - 1)`, with `allFrom_cons`
  (`f p = true → allFrom f (p + 1) n = true → allFrom f p (n + 1) = true`) and `allFrom_nil`;
* `tauCheck_of_parts : net.all layerOK = true → allFrom (tauCheckAt r net) 0 r = true →
  tauCheck r net = true`, and `cnvCheck_of_parts` (with `r - 1` positions).
-/

namespace FourColor.Engine

open FourColor

/-- `f p && f (p + 1) && … && f (p + n - 1)`. -/
def allFrom (f : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | p, n + 1 => f p && allFrom f (p + 1) n

/-- The empty conjunction. -/
theorem allFrom_nil (f : Nat → Bool) (p : Nat) : allFrom f p 0 = true := rfl

/-- One more conjunct. -/
theorem allFrom_cons {f : Nat → Bool} {p n : Nat} (h : f p = true)
    (t : allFrom f (p + 1) n = true) : allFrom f p (n + 1) = true := by
  simp [allFrom, h, t]

/-- `allFrom f 0 n` is `(List.range n).all f`. -/
theorem all_range_eq_allFrom (f : Nat → Bool) (n : Nat) :
    (List.range n).all f = allFrom f 0 n := by
  suffices h : ∀ p n, (List.range' p n).all f = allFrom f p n by
    rw [List.range_eq_range', h]
  intro p n
  induction n generalizing p with
  | zero => rfl
  | succ n ih => simp [List.range'_succ, allFrom, ih]

/-- The part of `tauCheck` for the position `p`: the network maps the indicator sets of the
colors `Color1`, `Color2`, `Color3` at `p` to those of `Color2`, `Color1`, `Color3`. -/
def tauCheckAt (r : Nat) (net : Net) (p : Nat) : Bool :=
  let W := wtable r p
  let i1 := indW r W Color1
  let i2 := indW r W Color2
  let i3 := indW r W Color3
  Nat.beq (applyNet net i1 &&& fullMask r) i2 && Nat.beq (applyNet net i2 &&& fullMask r) i1 &&
    Nat.beq (applyNet net i3 &&& fullMask r) i3

/-- `tauCheck` is the layer test and the parts for the positions `0 … r - 1`. -/
theorem tauCheck_eq_parts (r : Nat) (net : Net) :
    tauCheck r net = (net.all layerOK && allFrom (tauCheckAt r net) 0 r) := by
  rw [← all_range_eq_allFrom]
  rfl

/-- `tauCheck` from its parts. -/
theorem tauCheck_of_parts {r : Nat} {net : Net} (hl : net.all layerOK = true)
    (hp : allFrom (tauCheckAt r net) 0 r = true) : tauCheck r net = true := by
  rw [tauCheck_eq_parts, hl, hp]; rfl

/-- The part of `cnvCheck` for the position `p`: the network maps the base-3 indicator sets of
the colors at `p` to the indicator sets of the packed layout. -/
def cnvCheckAt (r : Nat) (net : Net) (p : Nat) : Bool :=
  let W := wtable r p
  colorsNZ.all fun c =>
    Nat.beq (applyNet net (b3ind (r - 1) p c) &&& fullMask r) (indW r W c)

/-- `cnvCheck` is the layer test and the parts for the positions `0 … r - 2`. -/
theorem cnvCheck_eq_parts (r : Nat) (net : Net) :
    cnvCheck r net = (net.all layerOK && allFrom (cnvCheckAt r net) 0 (r - 1)) := by
  rw [← all_range_eq_allFrom]
  rfl

/-- `cnvCheck` from its parts. -/
theorem cnvCheck_of_parts {r : Nat} {net : Net} (hl : net.all layerOK = true)
    (hp : allFrom (cnvCheckAt r net) 0 (r - 1) = true) : cnvCheck r net = true := by
  rw [cnvCheck_eq_parts, hl, hp]; rfl

end FourColor.Engine
