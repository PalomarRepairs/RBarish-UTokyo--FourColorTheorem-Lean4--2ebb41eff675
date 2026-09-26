/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfMap.Prog

/-!
# Configuration contracts (port of `cfcontract.v`, program-level part)

This file contains the part of `cfcontract.v` that only computes on programs and bit sequences
(and not on hypermaps).  All the definitions are first-order and structurally recursive, so
that they can be evaluated by the Lean kernel (`decide +kernel`): the reducibility engine
evaluates `contractProg` for each of the 633 configurations.

* `ctrmsize cp`        : the number of "kernel" (non-ring) edges of `cpmap cp` (math-comp
  `ctrmsize`).
* `ctrmaskRec cci i n`, `ctrmask cp cci` : the kernel-edge mask of the contract index list `cci`
  (math-comp `ctrmask_rec`, `ctrmask`).
* `cfcontractMask cf`  : the contract mask of the configuration `cf` (math-comp
  `cfcontract_mask`).
* `nsp b1 b2 b3`       : `(if b1 then orb else andb) b2 b3` (the section-local `nsp` of
  `cfcontract.v`).
* `cfctr mr mc cp`     : `some` construction program of the map obtained by contracting the
  edges selected by the masks `mc` (for kernel edges) and `mr` (for ring edges, in recursive
  calls), provided `cp` is a `configProg` and the contract is sparse (math-comp `cfctr`).
* `ctrband cm cp`      : the face mask selecting the faces of `cpmap cp` incident to one of the
  edges selected by the contract mask `cm` (math-comp `ctrband`).
* `cptriad ccm cp i`   : the kernel of `cpmap cp` has a triad with index `< i`, for a contract
  with band `ccm` (math-comp `cptriad`).
* `validCtrm cm cp`    : the contract represented by the mask `cm` is valid for `cpmap cp`
  (size in `[1, 4]`, with a triad for size `4`) (math-comp `valid_ctrm`).
* `contractProg cf`    : the construction program of the contract map of the configuration
  `cf`, if the contract is valid; this replaces math-comp's `contract_ctree` (which returned the
  `ctree` of the ring colorings of that program).

The map-level part (`ctrenum`, `cfcontract`) and the correctness theorems are in the other files
of `FourColor/CfContract/`.
-/

namespace FourColor

open CfMap

/-- math-comp `ctrmsize cp`: the number of "kernel" (non-ring) edges of `cpmap cp`. Each `Y`
step adds one kernel edge, except the initial `Y` step (the last step of the program), and each
`H` step adds three kernel edges. -/
def ctrmsize : Cprog → ℕ
  | .R _ :: cp => ctrmsize cp
  | [.Y] => 0
  | .Y :: cp => ctrmsize cp + 1
  | .H :: cp => ctrmsize cp + 3
  | _ => 0

/-- math-comp `ctrmask_rec cci i n`: the bits `i ∈ cci`, `i + 1 ∈ cci`, ...,
`i + n - 1 ∈ cci`. -/
def ctrmaskRec (cci : List ℕ) : ℕ → ℕ → List Bool
  | _, 0 => []
  | i, n + 1 => decide (i ∈ cci) :: ctrmaskRec cci (i + 1) n

/-- math-comp `ctrmask cp cci`: the kernel-edge mask of `cpmap cp` for the contract index list
`cci`; out-of-bounds indices are ignored. -/
def ctrmask (cp : Cprog) (cci : List ℕ) : List Bool := ctrmaskRec cci 0 (ctrmsize cp)

/-- math-comp `size_ctrmask`. -/
theorem size_ctrmask (cp : Cprog) (cci : List ℕ) : (ctrmask cp cci).length = ctrmsize cp := by
  unfold ctrmask
  generalize ctrmsize cp = n
  suffices ∀ i, (ctrmaskRec cci i n).length = n from this 0
  induction n with
  | zero => intro i; rfl
  | succ n ih => intro i; simp [ctrmaskRec, ih]

/-- math-comp `cfcontract_mask cf`: the contract mask of the configuration `cf`. -/
def cfcontractMask (cf : Config) : List Bool := ctrmask cf.cfprog cf.cfcontractRef

/-- The section-local `nsp b` of `cfcontract.v`: `if b then orb else andb`. The contract is not
sparse at a node when `nsp` holds for the bits of its three edges (one of them, if the node
itself is contracted, or two of them otherwise). -/
def nsp (b1 b2 b3 : Bool) : Bool := if b1 then b2 || b3 else b2 && b3

/-- math-comp `cfctr mr mc cp`: `some` construction program for the map obtained from
`cpmap cp` by contracting the kernel edges selected by `mc` and the ring edges selected by `mr`
(in recursive calls), provided `cp` is a configuration program and the contract is sparse;
`none` otherwise. -/
def cfctr : List Bool → List Bool → Cprog → Option Cprog
  | mr, mc, .R i :: cp =>
    let mr' := rotr i mr
    match cfctr mr' mc cp with
    | some cpc => some (.R ((mr'.take i).countP (fun b => !b)) :: cpc)
    | none => none
  | b1 :: b2 :: b3 :: _, _, [.Y] =>
    if nsp b1 b2 b3 then none else
    some (if b1 || (b2 || b3) then [] else [.Y])
  | b1 :: b2 :: mr, b3 :: mc, .Y :: cp =>
    if nsp b1 b2 b3 then none else
    match cfctr (b3 :: mr) mc cp with
    | some cpc => some (if b1 || b2 then cpc else (if b3 then .U else .Y) :: cpc)
    | none => none
  | b1 :: b2 :: mr, b3 :: b4 :: b5 :: mc, .H :: cp =>
    if nsp b3 b1 b4 || nsp b3 b2 b5 then none else
    if b1 && (b2 && mr.all id) then none else
    match cfctr (b4 :: b5 :: mr) mc cp with
    | some cpc => some (
        if b3 then cpc else
        if b1 then
          (if b2 then .A :: cpc else if b5 then cpc else .K :: cpc)
        else
          if b2 then (if b4 then cpc else .K :: cpc) else
          if b4 then (if b5 then .U :: cpc else .Y :: cpc) else
          if b5 then .Y :: cpc else .H :: cpc)
    | none => none
  | _, _, _ => none

/-- The equation of `cfctr` for an `R n` step. -/
theorem cfctr_R (n : ℕ) (mr mc : List Bool) (cp : Cprog) :
    cfctr mr mc (.R n :: cp) = (cfctr (rotr n mr) mc cp).map
      (fun cpc => .R (((rotr n mr).take n).countP (fun b => !b)) :: cpc) := by
  rw [cfctr]; cases cfctr _ _ _ <;> rfl

/-- The equation of `cfctr` for the initial `Y` step. -/
theorem cfctr_Y_nil (b1 b2 b3 : Bool) (mr mc : List Bool) :
    cfctr (b1 :: b2 :: b3 :: mr) mc [.Y] =
      if nsp b1 b2 b3 then none else some (if b1 || (b2 || b3) then [] else [.Y]) := by
  rw [cfctr]

/-- The equation of `cfctr` for a non-initial `Y` step. -/
theorem cfctr_Y_cons (b1 b2 b3 : Bool) (mr mc : List Bool) (s : Cpstep) (cp : Cprog) :
    cfctr (b1 :: b2 :: mr) (b3 :: mc) (.Y :: s :: cp) =
      if nsp b1 b2 b3 then none else (cfctr (b3 :: mr) mc (s :: cp)).map
        (fun cpc => if b1 || b2 then cpc else (if b3 then .U else .Y) :: cpc) := by
  rw [cfctr]
  · cases cfctr _ _ _ <;> rfl
  · intro _ _ _ h; cases h

/-- The equation of `cfctr` for an `H` step. -/
theorem cfctr_H (b1 b2 b3 b4 b5 : Bool) (mr mc : List Bool) (cp : Cprog) :
    cfctr (b1 :: b2 :: mr) (b3 :: b4 :: b5 :: mc) (.H :: cp) =
      if nsp b3 b1 b4 || nsp b3 b2 b5 then none else
      if b1 && (b2 && mr.all id) then none else
      (cfctr (b4 :: b5 :: mr) mc cp).map (fun cpc =>
        if b3 then cpc else
        if b1 then
          (if b2 then .A :: cpc else if b5 then cpc else .K :: cpc)
        else
          if b2 then (if b4 then cpc else .K :: cpc) else
          if b4 then (if b5 then .U :: cpc else .Y :: cpc) else
          if b5 then .Y :: cpc else .H :: cpc) := by
  rw [cfctr]; cases cfctr _ _ _ <;> rfl

/-- math-comp `cfctr_config_prog`: `cfctr` only succeeds on configuration programs. -/
theorem cfctr_config_prog {mr mc : List Bool} {cp : Cprog} {cpc : Cprog}
    (h : cfctr mr mc cp = some cpc) : configProg cp = true := by
  induction cp generalizing mr mc cpc with
  | nil =>
    rcases mr with _ | ⟨b1, _ | ⟨b2, mr⟩⟩ <;> rcases mc with _ | ⟨b3, mc⟩ <;>
      simp [cfctr] at h
  | cons s cp ih =>
    cases s with
    | R n =>
      simp only [cfctr] at h
      generalize hc : cfctr (rotr n mr) mc cp = c at h
      cases c with
      | none => simp at h
      | some c => exact ih hc
    | Y =>
      cases cp with
      | nil => rfl
      | cons s' cp' =>
        rcases mr with _ | ⟨b1, _ | ⟨b2, mr⟩⟩ <;> rcases mc with _ | ⟨b3, mc⟩ <;>
          simp only [cfctr, reduceCtorEq] at h
        generalize hc : cfctr (b3 :: mr) mc (s' :: cp') = c at h
        cases c with
        | none => simp at h
        | some c => exact ih hc
    | H =>
      rcases mr with _ | ⟨b1, _ | ⟨b2, mr⟩⟩ <;>
        rcases mc with _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, mc⟩⟩⟩ <;>
        simp only [cfctr, reduceCtorEq] at h
      generalize hc : cfctr (b4 :: b5 :: mr) mc cp = c at h
      cases c with
      | none => simp at h
      | some c => exact ih hc
    | _ =>
      rcases mr with _ | ⟨b1, _ | ⟨b2, mr⟩⟩ <;> rcases mc with _ | ⟨b3, mc⟩ <;>
        simp [cfctr] at h

/-- math-comp `ctrband cm cp`: the face mask (`Cfmask`) selecting the faces of `cpmap cp`
incident to one of the edges selected by the contract mask `cm`; this may include both kernel
and ring faces. -/
def ctrband : List Bool → Cprog → Cfmask
  | cm, .R n :: cp =>
    match ctrband cm cp with
    | ⟨mr, mk⟩ => ⟨rot n mr, mk⟩
  | _, [.Y] => ⟨List.replicate 3 false, []⟩
  | b1 :: cm, .Y :: cp =>
    match ctrband cm cp with
    | ⟨a0 :: a1 :: mr, mk⟩ => ⟨(b1 || a0) :: false :: (b1 || a1) :: mr, mk⟩
    | _ => ⟨[], []⟩
  | b1 :: b0 :: b2 :: cm, .H :: cp =>
    match ctrband cm cp with
    | ⟨a0 :: a1 :: a2 :: mr, mk⟩ =>
      ⟨(b0 || a0) :: b1 :: (b2 || a2) :: mr, (b0 || (b1 || (b2 || a1))) :: mk⟩
    | _ => ⟨[], []⟩
  | _, _ => ⟨[], []⟩

/-- math-comp `cptriad ccm cp i`: the kernel of `cpmap cp` has a triad with index `< i`, for a
contract with band `ccm`: there is a kernel face with index `< i` that is adjacent to at least
three of the faces selected by `ccm`, as well as to a face NOT selected by `ccm`. -/
def cptriad (ccm : Cfmask) (cp : Cprog) : ℕ → Bool
  | 0 => false
  | i + 1 =>
    match cpadj (cfmask1 cp i) cp, ccm with
    | ⟨mrt, mkt⟩, ⟨mrc, mkc⟩ =>
      let mct := mask mrc mrt ++ mask mkc mkt
      if mct.any (fun b => !b) && decide (2 < mct.countP id) then true else cptriad ccm cp i

/-- math-comp `valid_ctrm cm cp`: the contract represented by the mask `cm` is valid for
`cpmap cp`: it has size in `[1, 4]`, with a triad for size `4`. -/
def validCtrm (cm : List Bool) (cp : Cprog) : Bool :=
  let n := cm.countP id
  if n == 4 then cptriad (ctrband cm cp) cp (cpksize cp) else decide (0 < n) && decide (n ≤ 3)

/-- The construction program of the contract map of the configuration `cf`, provided its
contract is valid.  This replaces math-comp's `contract_ctree cf` (which returned `Some` of the
`ctree` of the ring colorings of this program): the ring colorings of `cpc` are computed by the
bit-parallel engine instead.  Its specification is `contractProg_spec`. -/
def contractProg (cf : Config) : Option Cprog :=
  let cp := cf.cfprog; let cm := cfcontractMask cf
  match cfctr (List.replicate (cprsize cp) false) cm cp with
  | some cpc => if validCtrm cm cp then some cpc else none
  | none => none

end FourColor
