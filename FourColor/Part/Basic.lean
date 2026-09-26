/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Geometry

/-!
# Parts: arity patterns around a hub  (port of `part.v`, combinatorial half)

These "parts" are patterns for performing local matching on maps. Specifically, a part
specifies ranges of arities for darts in the second neighbourhood of some match anchor `x`,
using the `Prange` type below to specify ranges.

A part is broken into a sequence of subparts, each specifying arities in a basic sector of the
second neighbourhood of `x`. Subparts are listed counterclockwise around a "hub" (the face
orbit of `x`); we also use part sublists (represented with the same type) to specify arities in
larger sectors around the hub. Each subpart comprises a "spoke" (a face adjacent to the hub;
the spoke of the first subpart is the face orbit of `edge x`), a "hat" (the face adjacent to
the spokes of this subpart and the previous one, different from the hub; the hat of the first
subpart is the face of `edge (face (edge x))`), and "fans" (the faces adjacent only to the
spoke of the subpart, numbered in a counterclockwise arc that starts from the hat). The hub
and subparts are a partition of the second neighborhood of `x`; a subpart does not contain the
hat of the next (counterclockwise) one, even though this hat is adjacent to the subpart's
spoke.

Because parts are created and traversed in the inner loop of the unavoidability checks their
representation is somewhat optimised: the list structure is merged into the record structure;
there are four different kinds of subparts, according to the number of (known) fans. The spoke
arity is always fixed when there are known fans (e.g., if there are two known fans, the spoke
is a heptagon). The converse isn't true: the explicit fan forms are never used when there are
no nontrivial fan constraints, as this simplifies the converse part computation.

All the operations of this file are computable, structurally recursive, first-order functions
on the inductive types below, so that they can be evaluated by the Lean kernel (`decide`) in
the discharge, hubcap, redpart and presentation checks.

## Main definitions (Coq name → Lean name)

`Prange`, `PartRel` and `SubpartLoc` have `DecidableEq` and (hand-written) `Fintype`
instances; `Part` has `DecidableEq`. The Coq coercions of `prange` and `part_rel` to functions
are `CoeFun` instances (to `memRange` and `applyPartRel`); the coercion of `subpart_loc` is
`SubpartLoc.move` (in `FourColor.Part.Fit`).

* `prange` → `Prange`: the arity ranges for non-hub faces; constructor `PrMN` (here `prMN`)
  means the range `[M, N]`, with `N = 9` meaning an unbounded range (so `pr59` is the free
  range of pentagonal maps). `mem_range` (a coercion to `pred nat` in Coq) → `memRange`.
* `part_rel` → `PartRel` (`Pdisjoint`/`Pstraddle`/`Psubset` → `disjoint`/`straddle`/`subset`),
  the outcomes of set comparisons; `apply_part_rel` (a coercion to `bool -> bool` in Coq) →
  `applyPartRel`, mapping the result of a membership test in the second set to its expected
  outcome.
* `subpart_loc` → `SubpartLoc` (`Pspoke`, `Phat`, `Pfan1`..`Pfan3` → `spoke`, `hat`,
  `fan1`..`fan3`): the faces of a subpart.
* `part` → `Part` (`Pnil`, `Pcons`, `Pcons6`, `Pcons7`, `Pcons8` → `nil`, `cons`, `cons6`,
  `cons7`, `cons8`); `PconsN` adds a subpart with spoke arity `N` and `N - 5` fans.
* `pcons_s s p` → `pconsS s p`: add a subpart with spoke range `s` and free hat range.
* `pcons_ n` → `pcons_ n`: `n` free subparts; fits any dart of arity `n`.
* `notPsubset`, `meet_prel` → `notPsubset`, `meetPrel`: set comparison logic.
* `cmp_range`, `meet_range`, `prange_lo`, `prange_hi`, `good_rsplit`, `split_range` →
  `cmpRange`, `meetRange`, `prangeLo`, `prangeHi`, `goodRsplit`, `splitRange`.
* `size_part`, `drop_part`, `take_part`, `cat_part`, `rot_part`, `catrev_part`, `rev_part` →
  `sizePart`, `dropPart`, `takePart`, `catPart`, `rotPart`, `catrevPart`, `revPart`.
* `get_spoke`, `next_hat`, `get_hat`, `get_fan[123][lr]` → `getSpoke`, `nextHat`, `getHat`,
  `getFan[123][lr]`.
* `mirror_part_rec`, `mirror_part` → `mirrorPartRec`, `mirrorPart` (reflection across the
  first spoke).
* `conv_part12`, `conv_part3`, `conv_part4`, `conv_part5`, `converse_part` → `convPart12`,
  `convPart3`, `convPart4`, `convPart5`, `conversePart` (reflection along the third spoke).
* `good_split`, `split_part` → `goodSplit`, `splitPart` (part refinement).
* `cmp_part`, `meet_part` → `cmpPart`, `meetPart` (part comparison and intersection).

The semantics of parts (`fitp`, `exact_fitp`, ...) is in `FourColor.Part.Fit`.

## Concrete syntax (Coq modules `PartSyntax` and `SublocSyntax`)

`open FourColor.PartSyntax` (Coq `Import PartSyntax`) activates the part literals
`Part <part>` (the keyword `Part` alone still denotes the type `FourColor.Part`):
```
  <part>    ::= $                                  -- nil
              | $ <range> <part>                   -- $ s p     = cons s * p
              | $[<range>] <range> <part>          -- $[h] s p  = cons s h p
              | $[<range> <range>] 6 <part>        -- $[h f1] 6 p = cons6 h f1 p
              | $[<range> <range> <range>] 7 <part>          -- cons7 h f1 f2 p
              | $[<range> <range> <range> <range>] 8 <part>  -- cons8 h f1 f2 f3 p
  <range>   ::= * | M | M+ | N- | M?N
```
In `$[h f1 f2] s`, `s` is the spoke range, `h` the hat range and `f1`, `f2` the fan ranges; a
bracket with fan ranges requires the literal spoke arity `6`, `7` or `8` (one, two or three
fans). The ranges `*`, `M`, `M+`, `N-`, `M?N` mean `pr59`, `prMM`, `prM9`, `pr5N`, `prMN`;
Coq defines `5`..`8`, `6+`..`9+`, `6-`..`8-`, `6?7`, `6?8`, `7?8`, and we also accept the other
forms with the same meaning (`5+` = `*`, `5-` = `5`, `5?6` = `6-`, ...), with `5 ≤ M ≤ 8`,
`5 ≤ N ≤ 8`, `M < N`, except `M+` which allows `M = 9` (`9` encodes infinity). E.g.
`Part $[6+] 7?8 $ 7- $[* 5] 6 $` is
`cons .pr78 .pr69 (cons .pr57 .pr59 (cons6 .pr59 .pr55 nil))`, and the discharge rule
`drule7` is `Part $ 6 $[6 6-] 6 $[5] 7+ $ * $ * $ * $`. While `PartSyntax` is open, closed
part values are also displayed in this syntax.

`open FourColor.SublocSyntax` (Coq `Import SublocSyntax`) provides the sublocation
shorthands `s`, `h`, `f1`, `f2`, `f3` (for `spoke`, `hat`, `fan1`..`fan3`) and the term forms
`split_part% <cond> p` and `good_split% <cond> p` for the arity assumptions of the
presentation scripts (Coq `present.v`), in syntax category `fcsubcond`:
```
  <cond> ::= <loc>[<nat>] <= <nat> | <loc>[<nat>] > <nat>      -- <loc> ∈ s, h, f1, f2, f3
```
e.g. `s[2] <= 6` (the second spoke has arity at most 6) or `f1[5] > 5`. Subpart indices start
at 1 in the concrete syntax: `split_part% i[j] <= k p` is `splitPart i (j - 1) k true p` and
`split_part% i[j] > k p` is `splitPart i (j - 1) k false p`. Tactic front ends (e.g. `Pcase`)
can reuse the category through `FourColor.SublocSyntax.expandSublocCond`.
-/

namespace FourColor

/-! ### Types -/

/-- Coq `prange`: arity ranges for non-hub faces. `prMN` stands for the range `M..N`; `N = 9`
actually means infinity, e.g., `pr59` means any arity greater than or equal to 5, that is any
arity in a pentagonal map. -/
inductive Prange
  | pr55 | pr66 | pr77 | pr88 | pr99
  | pr56 | pr67 | pr78 | pr89
  | pr57 | pr68 | pr79
  | pr58 | pr69
  | pr59
  deriving DecidableEq, Repr, Inhabited

/-- Coq `part`: parts and part sectors, represented as sequences of subparts. -/
inductive Part
  /-- Coq `Pnil`: the empty sector. -/
  | nil
  /-- Coq `Pcons spk hat p`: add a subpart with spoke range `spk`, hat range `hat` and no
  fan constraints. -/
  | cons (spk hat : Prange) (p : Part)
  /-- Coq `Pcons6 hat fan1 p`: add a subpart with a hexagonal spoke and one fan. -/
  | cons6 (hat fan1 : Prange) (p : Part)
  /-- Coq `Pcons7 hat fan1 fan2 p`: add a subpart with a heptagonal spoke and two fans. -/
  | cons7 (hat fan1 fan2 : Prange) (p : Part)
  /-- Coq `Pcons8 hat fan1 fan2 fan3 p`: add a subpart with an octagonal spoke and three
  fans. -/
  | cons8 (hat fan1 fan2 fan3 : Prange) (p : Part)
  deriving DecidableEq, Repr, Inhabited

/-- Coq `subpart_loc`: the faces of a subpart (Coq `Pspoke`, `Phat`, `Pfan1`, `Pfan2`,
`Pfan3`). -/
inductive SubpartLoc
  | spoke | hat | fan1 | fan2 | fan3
  deriving DecidableEq, Repr, Inhabited

/-- All the arity ranges. -/
def Prange.all : List Prange :=
  [.pr55, .pr66, .pr77, .pr88, .pr99, .pr56, .pr67, .pr78, .pr89, .pr57, .pr68, .pr79, .pr58,
    .pr69, .pr59]

instance : Fintype Prange where
  elems := ⟨↑Prange.all, by decide⟩
  complete r := by cases r <;> decide

instance : Fintype SubpartLoc where
  elems := ⟨↑[SubpartLoc.spoke, .hat, .fan1, .fan2, .fan3], by decide⟩
  complete i := by cases i <;> decide

/-! ### Concrete syntax (Coq module `PartSyntax`) -/

/-- Arity range literals (Coq `prange_scope`): `*`, `5`, `6`, `7`, `8`, `6+`, `7+`, `8+`,
`9+`, `6-`, `7-`, `8-`, `6?7`, `6?8`, `7?8`. -/
declare_syntax_cat fcprange
/-- `*`: the free range `pr59`. -/
syntax (name := fcprangeStar) "*" : fcprange
/-- `M`: the range `prMM`, for `M ∈ 5..8`. -/
syntax (name := fcprangeNum) num : fcprange
/-- `M+`: the range `prM9`, for `M ∈ 6..9`. -/
syntax (name := fcprangePlus) num noWs "+" : fcprange
/-- `N-`: the range `pr5N`, for `N ∈ 6..8`. -/
syntax (name := fcprangeMinus) num noWs "-" : fcprange
/-- `M?N`: the range `prMN`, for `6 ≤ M < N ≤ 8`. -/
syntax (name := fcprangeQuery) num noWs "?" noWs num : fcprange

/-- Part literals (Coq `part_scope`), see the module docstring. -/
declare_syntax_cat fcpart
/-- `$`: the empty part (Coq `Pnil`). -/
syntax (name := fcpartNil) "$" : fcpart
/-- `$ s p`: Coq `Pcons s * p`. -/
syntax (name := fcpartCons) "$" ppSpace fcprange ppSpace fcpart : fcpart
/-- `$[h] s p`, `$[h f1] 6 p`, `$[h f1 f2] 7 p`, `$[h f1 f2 f3] 8 p`: Coq `Pcons s h p`,
`Pcons6 h f1 p`, `Pcons7 h f1 f2 p`, `Pcons8 h f1 f2 f3 p`. -/
syntax (name := fcpartConsN)
  "$" noWs "[" fcprange (ppSpace fcprange)* "]" ppSpace fcprange ppSpace fcpart : fcpart

namespace PartSyntax

open Lean

/-- The `Prange` denoted by a range literal, if any. -/
def prangeOfBounds : ℕ → ℕ → Option Prange
  | 5, 5 => some .pr55 | 6, 6 => some .pr66 | 7, 7 => some .pr77 | 8, 8 => some .pr88
  | 9, 9 => some .pr99 | 5, 6 => some .pr56 | 6, 7 => some .pr67 | 7, 8 => some .pr78
  | 8, 9 => some .pr89 | 5, 7 => some .pr57 | 6, 8 => some .pr68 | 7, 9 => some .pr79
  | 5, 8 => some .pr58 | 6, 9 => some .pr69 | 5, 9 => some .pr59
  | _, _ => none

/-- The name of the constructor of a `Prange`. -/
def prangeCtorName : Prange → Name
  | .pr55 => ``Prange.pr55 | .pr66 => ``Prange.pr66 | .pr77 => ``Prange.pr77
  | .pr88 => ``Prange.pr88 | .pr99 => ``Prange.pr99 | .pr56 => ``Prange.pr56
  | .pr67 => ``Prange.pr67 | .pr78 => ``Prange.pr78 | .pr89 => ``Prange.pr89
  | .pr57 => ``Prange.pr57 | .pr68 => ``Prange.pr68 | .pr79 => ``Prange.pr79
  | .pr58 => ``Prange.pr58 | .pr69 => ``Prange.pr69 | .pr59 => ``Prange.pr59

/-- Expand a range literal to a `Prange` constructor term. -/
def expandPrange (r : TSyntax `fcprange) : MacroM Term := do
  let stx := r.raw
  let k := stx.getKind
  let nat (i : ℕ) : MacroM ℕ := match stx[i].isNatLit? with
    | some n => pure n
    | none => Macro.throwErrorAt stx "ill-formed arity range"
  -- `9` encodes infinity, so it may only appear as `9+`
  let bounds : ℕ × ℕ ←
    if k == ``fcprangeStar then pure (5, 9)
    else if k == ``fcprangeNum then do
      let m ← nat 0
      unless 5 ≤ m && m ≤ 8 do
        Macro.throwErrorAt stx "expected an arity range M with 5 ≤ M ≤ 8"
      pure (m, m)
    else if k == ``fcprangePlus then do
      let m ← nat 0
      unless 5 ≤ m && m ≤ 9 do
        Macro.throwErrorAt stx "expected an arity range M+ with 5 ≤ M ≤ 9"
      pure (m, 9)
    else if k == ``fcprangeMinus then do
      let n ← nat 0
      unless 5 ≤ n && n ≤ 8 do
        Macro.throwErrorAt stx "expected an arity range N- with 5 ≤ N ≤ 8"
      pure (5, n)
    else if k == ``fcprangeQuery then do
      let m ← nat 0
      let n ← nat 2
      unless 5 ≤ m && m < n && n ≤ 8 do
        Macro.throwErrorAt stx "expected an arity range M?N with 5 ≤ M < N ≤ 8"
      pure (m, n)
    else Macro.throwUnsupported
  match prangeOfBounds bounds.1 bounds.2 with
  | some r => pure (mkCIdent (prangeCtorName r))
  | none => Macro.throwErrorAt stx "ill-formed arity range"

/-- Expand a part literal (with a structural fuel bound on its length). -/
def expandPartAux : ℕ → Syntax → MacroM Term
  | 0, stx => Macro.throwErrorAt stx "part literal too long"
  | fuel + 1, stx => do
    let k := stx.getKind
    if k == ``fcpartNil then
      `(FourColor.Part.nil)
    else if k == ``fcpartCons then
      let s ← expandPrange ⟨stx[1]⟩
      let rest ← expandPartAux fuel stx[2]
      `(FourColor.Part.cons $s FourColor.Prange.pr59 $rest)
    else if k == ``fcpartConsN then
      let h ← expandPrange ⟨stx[2]⟩
      let fans ← stx[3].getArgs.mapM fun f => expandPrange ⟨f⟩
      let spk := stx[5]
      let rest ← expandPartAux fuel stx[6]
      let spkNum : Option ℕ :=
        if spk.getKind == ``fcprangeNum then spk[0].isNatLit? else none
      match fans.size, spkNum with
      | 0, _ => `(FourColor.Part.cons $(← expandPrange ⟨spk⟩) $h $rest)
      | 1, some 6 => `(FourColor.Part.cons6 $h $(fans[0]!) $rest)
      | 2, some 7 => `(FourColor.Part.cons7 $h $(fans[0]!) $(fans[1]!) $rest)
      | 3, some 8 => `(FourColor.Part.cons8 $h $(fans[0]!) $(fans[1]!) $(fans[2]!) $rest)
      | n, _ =>
        Macro.throwErrorAt spk
          s!"a subpart with {n} fan range(s) must have spoke arity exactly {n + 5}"
    else Macro.throwUnsupported

/-- Expand a part literal to nested `Part` constructors. -/
def expandPart (p : TSyntax `fcpart) : MacroM Term := expandPartAux 10000 p.raw

/-- Coq `Part p` (with `p` in `part_scope`): a part literal, e.g. `Part $ * $ 5 $ 7+ $`. -/
scoped syntax (name := partLit) "Part " fcpart : term

/-- While `PartSyntax` is open, the keyword `Part` alone denotes the type `FourColor.Part`. -/
scoped syntax (name := partType) "Part" : term

macro_rules
  | `(partLit| Part $p:fcpart) => expandPart p

macro_rules
  | `(partType| Part) => `(FourColor.Part)

/-! Display of closed part values in the literal syntax (only while `PartSyntax` is open). -/

/-- The range literal denoting a `Prange`. -/
def prangeToSyntax : Prange → TSyntax `fcprange
  | .pr59 => ⟨Syntax.node .none ``fcprangeStar #[mkAtom "*"]⟩
  | .pr55 => num 5 | .pr66 => num 6 | .pr77 => num 7 | .pr88 => num 8
  | .pr69 => plus 6 | .pr79 => plus 7 | .pr89 => plus 8 | .pr99 => plus 9
  | .pr56 => minus 6 | .pr57 => minus 7 | .pr58 => minus 8
  | .pr67 => query 6 7 | .pr68 => query 6 8 | .pr78 => query 7 8
where
  /-- `M`. -/
  num (m : ℕ) : TSyntax `fcprange :=
    ⟨Syntax.node .none ``fcprangeNum #[Syntax.mkNumLit (toString m)]⟩
  /-- `M+`. -/
  plus (m : ℕ) : TSyntax `fcprange :=
    ⟨Syntax.node .none ``fcprangePlus #[Syntax.mkNumLit (toString m), mkAtom "+"]⟩
  /-- `N-`. -/
  minus (n : ℕ) : TSyntax `fcprange :=
    ⟨Syntax.node .none ``fcprangeMinus #[Syntax.mkNumLit (toString n), mkAtom "-"]⟩
  /-- `M?N`. -/
  query (m n : ℕ) : TSyntax `fcprange :=
    ⟨Syntax.node .none ``fcprangeQuery
      #[Syntax.mkNumLit (toString m), mkAtom "?", Syntax.mkNumLit (toString n)]⟩

/-- The `Prange` constructor denoted by a constant, if any. -/
def prangeOfExpr? (e : Expr) : Option Prange :=
  match e.constName? with
  | some n =>
    Prange.all.find? (fun r => prangeCtorName r == n)
  | none => none

/-- `$[r₀ r₁ ...] s p`. -/
private def mkConsN (rs : List Prange) (s : TSyntax `fcprange) (p : TSyntax `fcpart) :
    TSyntax `fcpart :=
  match rs with
  | [] => p
  | r :: rs =>
    ⟨Syntax.node .none ``fcpartConsN #[mkAtom "$", mkAtom "[", prangeToSyntax r,
      mkNullNode (rs.map fun r => (prangeToSyntax r).raw).toArray, mkAtom "]", s, p]⟩

/-- The literal syntax of a closed `Part` value (with a structural fuel bound). -/
def partToSyntax? : ℕ → Expr → Option (TSyntax `fcpart)
  | 0, _ => none
  | fuel + 1, e =>
    if e.isConstOf ``Part.nil then
      some ⟨Syntax.node .none ``fcpartNil #[mkAtom "$"]⟩
    else
      let args := e.getAppArgs
      let rs := args.toList.dropLast.map prangeOfExpr?
      if rs.any Option.isNone then none else
      let rs := rs.filterMap id
      match e.getAppFn.constName?, args.back?.bind (partToSyntax? fuel) with
      | some ``Part.cons, some p =>
        match rs with
        | [s, .pr59] =>
          some ⟨Syntax.node .none ``fcpartCons #[mkAtom "$", prangeToSyntax s, p]⟩
        | [s, h] => some (mkConsN [h] (prangeToSyntax s) p)
        | _ => none
      | some ``Part.cons6, some p =>
        if rs.length = 2 then some (mkConsN rs (prangeToSyntax .pr66) p) else none
      | some ``Part.cons7, some p =>
        if rs.length = 3 then some (mkConsN rs (prangeToSyntax .pr77) p) else none
      | some ``Part.cons8, some p =>
        if rs.length = 4 then some (mkConsN rs (prangeToSyntax .pr88) p) else none
      | _, _ => none

open PrettyPrinter.Delaborator SubExpr in
/-- Display closed parts as part literals while `PartSyntax` is open. -/
@[scoped delab app.FourColor.Part.nil, scoped delab app.FourColor.Part.cons,
  scoped delab app.FourColor.Part.cons6, scoped delab app.FourColor.Part.cons7,
  scoped delab app.FourColor.Part.cons8]
def delabPartLit : Delab := do
  let some p := partToSyntax? 10000 (← getExpr) | failure
  return ⟨Syntax.node .none ``partLit #[mkAtom "Part", p]⟩

open PrettyPrinter.Delaborator SubExpr in
/-- Display the type `FourColor.Part` as the keyword `Part` while `PartSyntax` is open. -/
@[scoped delab app.FourColor.Part]
def delabPartType : Delab := do
  unless (← getExpr).isConstOf ``FourColor.Part do failure
  return ⟨Syntax.node .none ``partType #[mkAtom "Part"]⟩

end PartSyntax

/-! ### Sublocations (Coq module `SublocSyntax`) -/

/-- Arity assumptions of the presentation scripts (Coq `present.v`): `<loc>[j] <= k` or
`<loc>[j] > k`, where `<loc>` is one of the sublocations `s`, `h`, `f1`, `f2`, `f3`. -/
declare_syntax_cat fcsubcond
/-- `i[j] <= k`: the arity at sublocation `i` of subpart `j` (counting from 1) is at most
`k`. -/
syntax (name := fcsubcondLe) ident noWs "[" num "]" " <= " num : fcsubcond
/-- `i[j] > k`: the arity at sublocation `i` of subpart `j` (counting from 1) exceeds `k`. -/
syntax (name := fcsubcondGt) ident noWs "[" num "]" " > " num : fcsubcond

namespace SublocSyntax

/-- Coq `SublocSyntax.s`: the spoke sublocation. -/
abbrev s : SubpartLoc := .spoke
/-- Coq `SublocSyntax.h`: the hat sublocation. -/
abbrev h : SubpartLoc := .hat
/-- Coq `SublocSyntax.f1`: the first fan sublocation. -/
abbrev f1 : SubpartLoc := .fan1
/-- Coq `SublocSyntax.f2`: the second fan sublocation. -/
abbrev f2 : SubpartLoc := .fan2
/-- Coq `SublocSyntax.f3`: the third fan sublocation. -/
abbrev f3 : SubpartLoc := .fan3

open Lean

/-- Expand an arity assumption `i[j] <= k` (resp. `i[j] > k`) into the Coq quadruple
`(i, j.-1, k, lo)` of arguments of `splitPart`/`goodSplit`, with `lo = true` (resp.
`false`); as in the Coq tactic notation, `j` counts from 1 in the concrete syntax. -/
def expandSublocCond (c : TSyntax `fcsubcond) : MacroM (Term × Term × Term × Term) := do
  let stx := c.raw
  let lo : Term ← if stx.getKind == ``fcsubcondLe then `(true)
    else if stx.getKind == ``fcsubcondGt then `(false)
    else Macro.throwUnsupported
  let loc := stx[0].getId
  let i : Term ← match loc with
    | `s => `(FourColor.SubpartLoc.spoke)
    | `h => `(FourColor.SubpartLoc.hat)
    | `f1 => `(FourColor.SubpartLoc.fan1)
    | `f2 => `(FourColor.SubpartLoc.fan2)
    | `f3 => `(FourColor.SubpartLoc.fan3)
    | _ => Macro.throwErrorAt stx[0] "expected a sublocation: s, h, f1, f2 or f3"
  let some j := stx[2].isNatLit? | Macro.throwErrorAt stx[2] "expected a subpart index"
  if j == 0 then Macro.throwErrorAt stx[2] "subpart indices start at 1"
  let some k := stx[5].isNatLit? | Macro.throwErrorAt stx[5] "expected an arity"
  return (i, quote (j - 1), quote k, lo)

/-- `split_part% i[j] <= k p` is `splitPart i (j-1) k true p`, and
`split_part% i[j] > k p` is `splitPart i (j-1) k false p`. -/
scoped syntax (name := splitPartCond) "split_part% " fcsubcond ppSpace term:max : term

/-- `good_split% i[j] <= k p` (or `> k`) is `goodSplit i (j-1) k p`. -/
scoped syntax (name := goodSplitCond) "good_split% " fcsubcond ppSpace term:max : term

macro_rules
  | `(splitPartCond| split_part% $c:fcsubcond $p) => do
    let (i, j, k, lo) ← expandSublocCond c
    let f := mkCIdent `FourColor.splitPart
    `($f $i $j $k $lo $p)

macro_rules
  | `(goodSplitCond| good_split% $c:fcsubcond $p) => do
    let (i, j, k, _) ← expandSublocCond c
    let f := mkCIdent `FourColor.goodSplit
    `($f $i $j $k $p)

end SublocSyntax

/-! ### Shorthand for making (mostly) empty parts -/

/-- Coq `pcons_s s`: add a subpart with spoke range `s` and free hat range. -/
def pconsS (s : Prange) : Part → Part := Part.cons s .pr59

/-- Coq `pcons_ n`: the part consisting of `n` free subparts (free spoke and hat ranges),
which will fit any dart with arity `n`. -/
def pcons_ (n : ℕ) : Part := (Part.cons .pr59 .pr59)^[n] .nil

/-! ### Range semantics -/

/-- Coq `mem_range` (a coercion `prange >-> pred nat`): the arities in a range. -/
def memRange : Prange → ℕ → Bool
  | .pr55, n => n == 5
  | .pr66, n => n == 6
  | .pr77, n => n == 7
  | .pr88, n => n == 8
  | .pr56, n => n == 5 || n == 6
  | .pr67, n => n == 6 || n == 7
  | .pr78, n => n == 7 || n == 8
  | .pr57, n => n == 5 || (n == 6 || n == 7)
  | .pr68, n => n == 6 || (n == 7 || n == 8)
  | .pr58, n => n == 5 || (n == 6 || (n == 7 || n == 8))
  | .pr59, n => decide (5 ≤ n)
  | .pr69, n => decide (6 ≤ n)
  | .pr79, n => decide (7 ≤ n)
  | .pr89, n => decide (8 ≤ n)
  | .pr99, n => decide (9 ≤ n)

/-- Coq `Coercion mem_range : prange >-> pred`. -/
instance : CoeFun Prange (fun _ => ℕ → Bool) := ⟨memRange⟩

/-- Coq `part_rel`: part/range comparison results; `straddle` covers all the remaining
cases, including when the left hand side strictly contains the right hand side. We use the
result of a comparison by applying it to a "fit" predicate. -/
inductive PartRel
  /-- Coq `Pdisjoint`. -/
  | disjoint
  /-- Coq `Pstraddle`. -/
  | straddle
  /-- Coq `Psubset`. -/
  | subset
  deriving DecidableEq, Repr, Inhabited

instance : Fintype PartRel where
  elems := ⟨↑[PartRel.disjoint, .straddle, .subset], by decide⟩
  complete c := by cases c <;> decide

/-- Coq `apply_part_rel` (a coercion `part_rel >-> Funclass`): maps the result `b` of a
membership test of an element of the first set in the second one to its expected
outcome. -/
def applyPartRel : PartRel → Bool → Bool
  | .disjoint, _ => false
  | .subset, _ => true
  | _, b => b

/-- Coq `Coercion apply_part_rel : part_rel >-> Funclass`. -/
instance : CoeFun PartRel (fun _ => Bool → Bool) := ⟨applyPartRel⟩

/-- Coq `notPsubset c`: `straddle` if `c = subset`, else `c`. -/
def notPsubset : PartRel → PartRel
  | .subset => .straddle
  | c => c

/-- Coq `meet_prel c c'`: the relation for products `A × A'` and `B × B'` of sets where
`A` and `B`, `A'` and `B'` compare as `c`, `c'`, respectively. -/
def meetPrel (c c' : PartRel) : PartRel :=
  match c with
  | .disjoint => c
  | .subset => c'
  | .straddle => notPsubset c'

/-! ### Range comparison and meet -/

/-- Coq `cmp_range r r'`: set comparison of `r` and `r'`. -/
def cmpRange (r r' : Prange) : PartRel :=
  match r', r with
  | .pr59, _ => .subset
  | _, .pr59 => .straddle
  | .pr69, .pr55 => .disjoint
  | .pr69, .pr56 => .straddle
  | .pr69, .pr57 => .straddle
  | .pr69, .pr58 => .straddle
  | .pr69, _ => .subset
  | .pr55, .pr69 => .disjoint
  | _, .pr69 => .straddle
  | .pr58, .pr99 => .disjoint
  | .pr58, .pr89 => .straddle
  | .pr58, .pr79 => .straddle
  | .pr58, _ => .subset
  | .pr99, .pr58 => .disjoint
  | _, .pr58 => .straddle
  | .pr55, .pr55 => .subset
  | .pr55, .pr56 => .straddle
  | .pr55, .pr57 => .straddle
  | .pr55, _ => .disjoint
  | .pr56, .pr55 => .subset
  | .pr57, .pr55 => .subset
  | _, .pr55 => .disjoint
  | .pr99, .pr99 => .subset
  | .pr99, .pr89 => .straddle
  | .pr99, .pr79 => .straddle
  | .pr99, _ => .disjoint
  | .pr89, .pr99 => .subset
  | .pr79, .pr99 => .subset
  | _, .pr99 => .disjoint
  | .pr66, .pr66 => .subset
  | .pr66, .pr56 => .straddle
  | .pr66, .pr57 => .straddle
  | .pr66, .pr67 => .straddle
  | .pr66, .pr68 => .straddle
  | .pr66, _ => .disjoint
  | .pr56, .pr66 => .subset
  | .pr57, .pr66 => .subset
  | .pr67, .pr66 => .subset
  | .pr68, .pr66 => .subset
  | _, .pr66 => .disjoint
  | .pr88, .pr88 => .subset
  | .pr88, .pr89 => .straddle
  | .pr88, .pr79 => .straddle
  | .pr88, .pr78 => .straddle
  | .pr88, .pr68 => .straddle
  | .pr88, _ => .disjoint
  | .pr89, .pr88 => .subset
  | .pr79, .pr88 => .subset
  | .pr78, .pr88 => .subset
  | .pr68, .pr88 => .subset
  | _, .pr88 => .disjoint
  | .pr77, .pr77 => .subset
  | .pr77, .pr56 => .disjoint
  | .pr77, .pr89 => .disjoint
  | .pr77, _ => .straddle
  | .pr56, .pr77 => .disjoint
  | .pr89, .pr77 => .disjoint
  | _, .pr77 => .subset
  | .pr68, .pr68 => .subset
  | .pr68, .pr67 => .subset
  | .pr68, .pr78 => .subset
  | .pr68, _ => .straddle
  | _, .pr68 => .straddle
  | .pr67, .pr67 => .subset
  | .pr67, .pr89 => .disjoint
  | .pr67, _ => .straddle
  | .pr57, .pr67 => .subset
  | .pr89, .pr67 => .disjoint
  | _, .pr67 => .straddle
  | .pr78, .pr78 => .subset
  | .pr78, .pr56 => .disjoint
  | .pr78, _ => .straddle
  | .pr79, .pr78 => .subset
  | .pr56, .pr78 => .disjoint
  | _, .pr78 => .straddle
  | .pr89, .pr56 => .disjoint
  | .pr79, .pr56 => .disjoint
  | _, .pr56 => .subset
  | .pr56, .pr57 => .straddle
  | .pr56, _ => .disjoint
  | .pr57, .pr89 => .disjoint
  | _, .pr89 => .subset
  | .pr89, .pr79 => .straddle
  | .pr89, _ => .disjoint
  | .pr57, .pr57 => .subset
  | .pr79, .pr79 => .subset
  | _, _ => .straddle

/-- Coq `meet_range r r'`: the intersection of non-disjoint ranges `r` and `r'`. -/
def meetRange (r r' : Prange) : Prange :=
  match r', r with
  | .pr56, .pr67 => .pr66
  | .pr56, .pr68 => .pr66
  | .pr56, .pr69 => .pr66
  | .pr67, .pr56 => .pr66
  | .pr68, .pr56 => .pr66
  | .pr69, .pr56 => .pr66
  | .pr57, .pr78 => .pr77
  | .pr57, .pr79 => .pr77
  | .pr67, .pr78 => .pr77
  | .pr67, .pr79 => .pr77
  | .pr78, .pr57 => .pr77
  | .pr79, .pr57 => .pr77
  | .pr78, .pr67 => .pr77
  | .pr79, .pr67 => .pr77
  | .pr89, .pr58 => .pr88
  | .pr89, .pr68 => .pr88
  | .pr89, .pr78 => .pr88
  | .pr58, .pr89 => .pr88
  | .pr68, .pr89 => .pr88
  | .pr78, .pr89 => .pr88
  | .pr57, .pr68 => .pr67
  | .pr57, .pr69 => .pr67
  | .pr68, .pr57 => .pr67
  | .pr69, .pr57 => .pr67
  | .pr79, .pr58 => .pr78
  | .pr79, .pr68 => .pr78
  | .pr58, .pr79 => .pr78
  | .pr68, .pr79 => .pr78
  | .pr58, .pr69 => .pr68
  | .pr69, .pr58 => .pr68
  | .pr59, _ => r
  | _, .pr59 => r'
  | .pr58, _ => r
  | .pr69, _ => r
  | _, .pr58 => r'
  | _, .pr69 => r'
  | .pr57, _ => r
  | .pr68, _ => r
  | .pr79, _ => r
  | _, .pr57 => r'
  | _, .pr68 => r'
  | _, .pr79 => r'
  | .pr56, _ => r
  | .pr67, _ => r
  | .pr78, _ => r
  | .pr89, _ => r
  | _, .pr56 => r'
  | _, .pr67 => r'
  | _, .pr78 => r'
  | _, _ => r'

/-- Range membership only depends on the arity up to 9. -/
private theorem memRange_min (r : Prange) (n : ℕ) : memRange r n = memRange r (min n 9) := by
  rcases Nat.lt_or_ge n 9 with h | h
  · rw [Nat.min_eq_left (by omega)]
  · rw [Nat.min_eq_right h]
    cases r <;> simp [memRange] <;> omega

/-- Coq `mem_cmp_range`. -/
theorem mem_cmp_range (r1 : Prange) (n : ℕ) (h1 : memRange r1 n) (r2 : Prange) :
    memRange r2 n = applyPartRel (cmpRange r1 r2) (memRange r2 n) := by
  have key : ∀ m, m < 10 → ∀ r1 r2 : Prange, memRange r1 m = true →
      memRange r2 m = applyPartRel (cmpRange r1 r2) (memRange r2 m) := by decide
  rw [memRange_min] at h1 ⊢
  exact key _ (by omega) r1 r2 h1

/-- Coq `mem_meet_range`. -/
theorem mem_meet_range (r1 r2 : Prange) (n : ℕ) (h1 : memRange r1 n) (h2 : memRange r2 n) :
    memRange (meetRange r1 r2) n := by
  have key : ∀ m, m < 10 → ∀ r1 r2 : Prange, memRange r1 m = true → memRange r2 m = true →
      memRange (meetRange r1 r2) m = true := by decide
  rw [memRange_min] at h1 h2 ⊢
  exact key _ (by omega) r1 r2 h1 h2

/-! ### List-like operations on parts

Most also have a geometric meaning, except `revPart`, which is just a subroutine for the
implementation of zipped parts in `redpart`. -/

/-- Coq `size_part`: the number of subparts (the hub arity of a part). -/
def sizePart : Part → ℕ
  | .nil => 0
  | .cons _ _ p' => sizePart p' + 1
  | .cons6 _ _ p' => sizePart p' + 1
  | .cons7 _ _ _ p' => sizePart p' + 1
  | .cons8 _ _ _ _ p' => sizePart p' + 1

/-- Coq `drop_part n p`: the sector left by dropping the `n` first subparts of `p`. -/
def dropPart (n : ℕ) (p : Part) : Part :=
  match n, p with
  | n' + 1, .cons _ _ p' => dropPart n' p'
  | n' + 1, .cons6 _ _ p' => dropPart n' p'
  | n' + 1, .cons7 _ _ _ p' => dropPart n' p'
  | n' + 1, .cons8 _ _ _ _ p' => dropPart n' p'
  | _, _ => p
termination_by structural n

/-- Coq `take_part n p`: the sector consisting of the `n` first subparts of `p`. -/
def takePart (n : ℕ) (p : Part) : Part :=
  match n, p with
  | n' + 1, .cons s h p' => .cons s h (takePart n' p')
  | n' + 1, .cons6 h f1 p' => .cons6 h f1 (takePart n' p')
  | n' + 1, .cons7 h f1 f2 p' => .cons7 h f1 f2 (takePart n' p')
  | n' + 1, .cons8 h f1 f2 f3 p' => .cons8 h f1 f2 f3 (takePart n' p')
  | _, _ => .nil
termination_by structural n

/-- Coq `cat_part p q`: part concatenation. -/
def catPart (p q : Part) : Part :=
  match p with
  | .cons s h p' => .cons s h (catPart p' q)
  | .cons6 h f1 p' => .cons6 h f1 (catPart p' q)
  | .cons7 h f1 f2 p' => .cons7 h f1 f2 (catPart p' q)
  | .cons8 h f1 f2 f3 p' => .cons8 h f1 f2 f3 (catPart p' q)
  | .nil => q

/-- Coq `rot_part n p`: `p` rotated `n` times, provided `n < size_part p`. -/
def rotPart (n : ℕ) (p : Part) : Part := catPart (dropPart n p) (takePart n p)

/-- Coq `size_cat_part`. -/
theorem size_cat_part (p1 p2 : Part) : sizePart (catPart p1 p2) = sizePart p1 + sizePart p2 := by
  induction p1 <;> simp only [catPart, sizePart, *] <;> omega

/-- Coq `size_drop_part`. -/
theorem size_drop_part (n : ℕ) (p : Part) : sizePart (dropPart n p) = sizePart p - n := by
  induction n generalizing p with
  | zero => cases p <;> rfl
  | succ n ih => cases p <;> simp only [dropPart, sizePart, ih] <;> omega

/-- Coq `cat_take_drop_part`. -/
theorem cat_take_drop_part (n : ℕ) (p : Part) : catPart (takePart n p) (dropPart n p) = p := by
  induction n generalizing p with
  | zero => cases p <;> rfl
  | succ n ih => cases p <;> simp only [takePart, dropPart, catPart, ih]

/-- Coq `size_rot_part`. -/
theorem size_rot_part (n : ℕ) (p : Part) : sizePart (rotPart n p) = sizePart p := by
  conv_rhs => rw [← cat_take_drop_part n p]
  rw [rotPart, size_cat_part, size_cat_part, Nat.add_comm]

/-- Coq `catrev_part p1 p2`: part concatenation of `p1` reversed, and `p2`. -/
def catrevPart (p1 p2 : Part) : Part :=
  match p1 with
  | .nil => p2
  | .cons s h p1' => catrevPart p1' (.cons s h p2)
  | .cons6 h f1 p1' => catrevPart p1' (.cons6 h f1 p2)
  | .cons7 h f1 f2 p1' => catrevPart p1' (.cons7 h f1 f2 p2)
  | .cons8 h f1 f2 f3 p1' => catrevPart p1' (.cons8 h f1 f2 f3 p2)

/-- Coq `rev_part p`: `p` reversed; NOT a mirror image, as subparts are not modified; used
to implement zippers in `redpart`. -/
def revPart (p : Part) : Part := catrevPart p .nil

/-- Coq `catrev_part_eq`. -/
theorem catrev_part_eq (p1 p2 : Part) : catrevPart p1 p2 = catPart (revPart p1) p2 := by
  have key : ∀ p1 p3 : Part, catrevPart p1 (catPart p3 p2) = catPart (catrevPart p1 p3) p2 := by
    intro p1
    induction p1 with
    | nil => intro p3; rfl
    | cons s h p1 ih => intro p3; exact ih (.cons s h p3)
    | cons6 h f1 p1 ih => intro p3; exact ih (.cons6 h f1 p3)
    | cons7 h f1 f2 p1 ih => intro p3; exact ih (.cons7 h f1 f2 p3)
    | cons8 h f1 f2 f3 p1 ih => intro p3; exact ih (.cons8 h f1 f2 f3 p3)
  exact key p1 .nil

/-- Coq `size_rev_part`. -/
theorem size_rev_part (p : Part) : sizePart (revPart p) = sizePart p := by
  have key : ∀ p q : Part, sizePart (catrevPart p q) = sizePart p + sizePart q := by
    intro p
    induction p with
    | nil => intro q; simp [catrevPart, sizePart]
    | cons _ _ p ih | cons6 _ _ p ih | cons7 _ _ _ p ih | cons8 _ _ _ _ p ih =>
      intro q; simp only [catrevPart, ih, sizePart]; omega
  simpa [revPart, sizePart] using key p .nil

/-- Coq `rev_rev_part`. -/
theorem rev_rev_part (p : Part) : revPart (revPart p) = p := by
  have key : ∀ p q : Part, catrevPart (catrevPart p q) .nil = catrevPart q p := by
    intro p
    induction p with
    | nil => intro q; rfl
    | cons s h p ih => intro q; exact ih (.cons s h q)
    | cons6 h f1 p ih => intro q; exact ih (.cons6 h f1 q)
    | cons7 h f1 f2 p ih => intro q; exact ih (.cons7 h f1 f2 q)
    | cons8 h f1 f2 f3 p ih => intro q; exact ih (.cons8 h f1 f2 f3 q)
  exact key p .nil

/-! ### Accessors

Except for `nextHat`, they assume the part is not nil. The accessors are mostly used for
zipped parts, where we also need to access the fans in clockwise order, so we have both "r"
(counterclockwise) and "l" (clockwise) versions of the fan accessors. -/

/-- Coq `get_spoke p`: the arity range for the first spoke in `p`. -/
def getSpoke : Part → Prange
  | .cons s _ _ => s
  | .cons6 _ _ _ => .pr66
  | .cons7 _ _ _ _ => .pr77
  | .cons8 _ _ _ _ _ => .pr88
  | _ => .pr59

/-- Coq `next_hat h0 p`: the range for the first hat in `p`, defaulting to `h0` for `nil`. -/
def nextHat (h0 : Prange) : Part → Prange
  | .nil => h0
  | .cons _ h _ => h
  | .cons6 h _ _ => h
  | .cons7 h _ _ _ => h
  | .cons8 h _ _ _ _ => h

/-- Coq `get_hat p`: the arity range for the first hat in `p`. -/
def getHat (p : Part) : Prange := nextHat .pr59 p

/-- Coq `get_fan1r p`: the first fan range, counting counterclockwise. -/
def getFan1r : Part → Prange
  | .cons6 _ f1 _ => f1
  | .cons7 _ f1 _ _ => f1
  | .cons8 _ f1 _ _ _ => f1
  | _ => .pr59

/-- Coq `get_fan2r p`: the second fan range, counting counterclockwise. -/
def getFan2r : Part → Prange
  | .cons7 _ _ f2 _ => f2
  | .cons8 _ _ f2 _ _ => f2
  | _ => .pr59

/-- Coq `get_fan3r p`: the third fan range, counting counterclockwise. -/
def getFan3r : Part → Prange
  | .cons8 _ _ _ f3 _ => f3
  | _ => .pr59

/-- Coq `get_fan1l p`: the first fan range, counting clockwise. -/
def getFan1l : Part → Prange
  | .cons6 _ f1 _ => f1
  | .cons7 _ _ f2 _ => f2
  | .cons8 _ _ _ f3 _ => f3
  | _ => .pr59

/-- Coq `get_fan2l p`: the second fan range, counting clockwise. -/
def getFan2l : Part → Prange
  | .cons7 _ f1 _ _ => f1
  | .cons8 _ _ f2 _ _ => f2
  | _ => .pr59

/-- Coq `get_fan3l p`: the third fan range, counting clockwise. -/
def getFan3l : Part → Prange
  | .cons8 _ f1 _ _ _ => f1
  | _ => .pr59

/-! ### Mirror image: reflection ACROSS the first spoke (exchanges second and last spoke
faces) -/

/-- Coq `mirror_part_rec h0 rp p`: `rp` prefixed by the mirror image of `p`, whose last hat
is `h0`. -/
def mirrorPartRec (h0 : Prange) (rp p : Part) : Part :=
  match p with
  | .nil => rp
  | .cons s _ p' => mirrorPartRec h0 (.cons s (nextHat h0 p') rp) p'
  | .cons6 _ f1 p' => mirrorPartRec h0 (.cons6 (nextHat h0 p') f1 rp) p'
  | .cons7 _ f1 f2 p' => mirrorPartRec h0 (.cons7 (nextHat h0 p') f2 f1 rp) p'
  | .cons8 _ f1 f2 f3 p' => mirrorPartRec h0 (.cons8 (nextHat h0 p') f3 f2 f1 rp) p'

/-- Coq `mirror_part p`: the mirror image (reflection across the first spoke) of `p`. -/
def mirrorPart (p : Part) : Part := mirrorPartRec (getHat p) .nil p

/-- Coq `size_mirror_part`. -/
theorem size_mirror_part (p : Part) : sizePart (mirrorPart p) = sizePart p := by
  have key : ∀ (p q : Part) (h0 : Prange),
      sizePart (mirrorPartRec h0 q p) = sizePart p + sizePart q := by
    intro p
    induction p with
    | nil => intro q h0; simp [mirrorPartRec, sizePart]
    | cons _ _ p ih | cons6 _ _ p ih | cons7 _ _ _ p ih | cons8 _ _ _ _ p ih =>
      intro q h0; simp only [mirrorPartRec, ih, sizePart]; omega
  simpa [mirrorPart, sizePart] using key p .nil (getHat p)

/-- Coq `mirror_mirror_part`. -/
theorem mirror_mirror_part (p : Part) : mirrorPart (mirrorPart p) = p := by
  -- the Coq generalization: `mirror_part (mirror_part_rec h0 q p) = mirror_part_rec h0 p q`
  have key : ∀ (h0 : Prange) (p q : Part),
      nextHat (match p with | .nil => .pr59 | _ => h0) q = nextHat h0 p →
      mirrorPart (mirrorPartRec h0 q p) = mirrorPartRec h0 p q := by
    intro h0 p
    induction p with
    | nil =>
      intro q hq
      simp only [mirrorPartRec, mirrorPart, getHat]
      rw [hq]; rfl
    | cons s h p ih =>
      intro q hq
      rw [mirrorPartRec, ih _ rfl]
      cases q <;> simp_all [mirrorPartRec, nextHat]
    | cons6 h f1 p ih =>
      intro q hq
      rw [mirrorPartRec, ih _ rfl]
      cases q <;> simp_all [mirrorPartRec, nextHat]
    | cons7 h f1 f2 p ih =>
      intro q hq
      rw [mirrorPartRec, ih _ rfl]
      cases q <;> simp_all [mirrorPartRec, nextHat]
    | cons8 h f1 f2 f3 p ih =>
      intro q hq
      rw [mirrorPartRec, ih _ rfl]
      cases q <;> simp_all [mirrorPartRec, nextHat]
  have := key (getHat p) p .nil (by cases p <;> rfl)
  show mirrorPart (mirrorPartRec (getHat p) .nil p) = p
  rw [this]
  rfl

/-! ### Converse part: reflection ALONG the THIRD spoke (exchanges hub and third spoke
faces)

The converse part operation is only used to compute converse discharge rules, and is
over-approximate: constraints of `p` that fall outside of the second neighbourhood of its
first spoke must be ignored, and corner cases not needed by the data in `discharge` are cut
out. The approximation only affects the hubcap computations, is provably safe, and
empirically complete as approximations don't actually arise with the discharge data. -/

/-- Coq `conv_part12 p4`. -/
def convPart12 (p4 : Part) : Prange × (Part → Part) :=
  match p4 with
  | .cons s2 s1 (.cons h23 f2 _) =>
    match f2, s2 with
    | .pr59, _ => (h23, fun q => pconsS s1 (pconsS s2 q))
    | _, .pr55 => (h23, fun q => pconsS s1 (.cons .pr55 f2 q))
    | _, .pr66 => (h23, fun q => pconsS s1 (.cons6 .pr59 f2 q))
    | _, .pr77 => (h23, fun q => pconsS s1 (.cons7 .pr59 .pr59 f2 q))
    | _, _ => (.pr59, fun _ => .nil)
  | .cons6 s1 h12 (.cons h23 f21 _) =>
    (h23, fun q => pconsS s1 (.cons6 h12 f21 q))
  | .cons7 s1 h12 f21 (.cons h23 f22 _) =>
    (h23, fun q => pconsS s1 (.cons7 h12 f21 f22 q))
  | _ => (.pr59, fun _ => .nil)

/-- Coq `conv_part3 h23 p6`. -/
def convPart3 (h23 : Prange) (p6 : Part) : Part → Part :=
  match p6 with
  | .nil => Part.cons .pr55 h23
  | .cons _ _ .nil => Part.cons .pr66 h23
  | .cons f31 _ (.cons f32 _ .nil) =>
    match f31, f32 with
    | .pr59, .pr59 => Part.cons .pr77 h23
    | _, _ => Part.cons7 h23 f31 f32
  | .cons f31 _ (.cons f32 _ (.cons f33 _ .nil)) => Part.cons8 h23 f31 f32 f33
  | _ => fun _ => .nil

/-- Coq `conv_part4 p1`. -/
def convPart4 (p1 : Part) : Prange × (Part → Part) :=
  match p1 with
  | .cons h34 _ (.cons s4 f41 _) =>
    match f41, s4 with
    | .pr59, _ => (.pr59, Part.cons s4 h34)
    | _, .pr55 => (f41, Part.cons .pr55 h34)
    | _, .pr66 => (.pr59, Part.cons6 h34 f41)
    | _, .pr77 => (.pr59, Part.cons7 h34 f41 .pr59)
    | _, _ => (.pr59, fun _ => .nil)
  | .cons h34 _ (.cons6 f41 h45 _) => (h45, Part.cons6 h34 f41)
  | .cons h34 _ (.cons7 f41 f42 h45 _) => (h45, Part.cons7 h34 f41 f42)
  | _ => (.pr59, fun _ => .nil)

/-- Coq `conv_part5 h45 p3`. -/
def convPart5 (h45 : Prange) (p3 : Part) : Prange × Part :=
  match p3 with
  | .cons u s5 _ => (u, .cons s5 h45 .nil)
  | .cons7 s5 s6 s7 _ => (.pr77, .cons s5 h45 (pconsS s6 (pconsS s7 .nil)))
  | _ => (.pr59, .nil)

/-- Coq `converse_part p`: the converse of part `p`, i.e., its reflection across the edge
between the hub and the THIRD spoke. This returns a pair of a range constraint for the new
hub and a sector part whose first spoke is the first hat of `p`, since the arity of the
first spoke of `p` might not be fixed. -/
def conversePart (p1 : Part) : Prange × Part :=
  let (h45, q4) := convPart4 p1
  let (u, q5) := convPart5 h45 (dropPart 2 p1)
  let (h23, q12) := convPart12 (dropPart 3 p1)
  let q3 := convPart3 h23 (dropPart 5 p1)
  (u, q12 (q3 (q4 q5)))

/-! ### Part (and range) splitting

Splitting is done with respect to a condition, i.e., a quadruple of a part location `i`,
spoke index `j`, arity value `k`, and a boolean `lo`, true if we want to restrict the range at
`i[j]` to arities lower than or equal to `k`, and false if we want the arities greater than
`k`. A split is "good" if it is nontrivial (`k` is in the range) and definite (if `i` is a fan
location, the spoke below it has a definite arity that is large enough). -/

/-- Coq `prange_lo k`: the range `[5, k]`. -/
def prangeLo : ℕ → Prange
  | 5 => .pr55
  | 6 => .pr56
  | 7 => .pr57
  | 8 => .pr58
  | _ => .pr59

/-- Coq `prange_hi k`: the range `[k + 1, 9]`. -/
def prangeHi : ℕ → Prange
  | 5 => .pr69
  | 6 => .pr79
  | 7 => .pr89
  | 8 => .pr99
  | _ => .pr59

/-- Coq `good_rsplit k r`: the range `r` can be split at `k`, as it straddles `[5, k]`,
i.e., `i ≤ k < j` when `r` is the range `[i, j]`. -/
def goodRsplit (k : ℕ) (r : Prange) : Bool :=
  match cmpRange r (prangeLo k) with
  | .straddle => true
  | _ => false

/-- Coq `split_range k lo r`: the range `[i, k]` if `lo`, and `[k + 1, j]` if `¬ lo`, when
`r` is the range `[i, j]`, with `i ≤ k < j`. -/
def splitRange (k : ℕ) (lo : Bool) (r : Prange) : Prange :=
  meetRange ((if lo then prangeLo else prangeHi) k) r

/-- Outside `5..8`, `prangeLo` is the free range. -/
private theorem prangeLo_of_not_mem {k : ℕ} (hk : ¬ (5 ≤ k ∧ k ≤ 8)) : prangeLo k = .pr59 := by
  unfold prangeLo
  split <;> first | rfl | omega

/-- `goodRsplit` for the free range `[5, 9]` (auxiliary). -/
private def goodRsplit' (r : Prange) : Bool :=
  match cmpRange r .pr59 with
  | .straddle => true
  | _ => false

/-- Coq `fit_split_range`. -/
theorem fit_split_range (k : ℕ) (r : Prange) (hk : goodRsplit k r) (lo : Bool) (a : ℕ) :
    memRange (splitRange k lo r) a = ((lo ^^ decide (k < a)) && memRange r a) := by
  have key : ∀ k' < 4, ∀ r : Prange, goodRsplit (k' + 5) r = true → ∀ lo : Bool, ∀ a < 10,
      memRange (splitRange (k' + 5) lo r) a = ((lo ^^ decide (k' + 5 < a)) && memRange r a) := by
    decide
  have h58 : 5 ≤ k ∧ k ≤ 8 := by
    by_contra hc
    have h59 : ∀ r : Prange, goodRsplit' r = false := by decide
    rw [goodRsplit, prangeLo_of_not_mem hc] at hk
    have h59r := h59 r
    rw [goodRsplit'] at h59r
    rw [h59r] at hk
    exact Bool.false_ne_true hk
  have hka : decide (k < a) = decide (k < min a 9) := by
    simp only [decide_eq_decide]; omega
  rw [memRange_min, hka, memRange_min r a]
  have := key (k - 5) (by omega) r (by rwa [Nat.sub_add_cancel h58.1]) lo (min a 9) (by omega)
  rwa [Nat.sub_add_cancel h58.1] at this

/-- Coq `good_split i j k p`: the arity range `r` at sublocation `i` in subpart `j` of part
`p` can be split at `k`. -/
def goodSplit (i : SubpartLoc) (j k : ℕ) (p : Part) : Bool :=
  match i, dropPart j p with
  | .spoke, .cons s _ _ => goodRsplit k s
  | .hat, .cons _ h _ => goodRsplit k h
  | .hat, .cons6 h _ _ => goodRsplit k h
  | .hat, .cons7 h _ _ _ => goodRsplit k h
  | .hat, .cons8 h _ _ _ _ => goodRsplit k h
  | .fan1, .cons6 _ f1 _ => goodRsplit k f1
  | .fan1, .cons .pr66 _ _ => goodRsplit k .pr59
  | .fan1, .cons7 _ f1 _ _ => goodRsplit k f1
  | .fan1, .cons .pr77 _ _ => goodRsplit k .pr59
  | .fan1, .cons8 _ f1 _ _ _ => goodRsplit k f1
  | .fan1, .cons .pr88 _ _ => goodRsplit k .pr59
  | .fan2, .cons7 _ _ f2 _ => goodRsplit k f2
  | .fan2, .cons .pr77 _ _ => goodRsplit k .pr59
  | .fan2, .cons8 _ _ f2 _ _ => goodRsplit k f2
  | .fan2, .cons .pr88 _ _ => goodRsplit k .pr59
  | .fan3, .cons8 _ _ _ f3 _ => goodRsplit k f3
  | .fan3, .cons .pr88 _ _ => goodRsplit k .pr59
  | _, _ => false

/-- Coq `split_part i j k lo p`: part `p` where the arity range `r` at sublocation `i` in
subpart `j` has been replaced by `split_range k lo r`. -/
def splitPart (i : SubpartLoc) (j k : ℕ) (lo : Bool) (p : Part) : Part :=
  let p1 := takePart j p
  let p2 := dropPart j p
  let mkp (df : Prange → Part → Part) (r : Prange) (p' : Part) : Part :=
    catPart p1 (df (splitRange k lo r) p')
  match i, p2 with
  | .spoke, .cons s h p' => mkp (fun r => Part.cons r h) s p'
  | .hat, .cons s h p' => mkp (fun r => Part.cons s r) h p'
  | .hat, .cons6 h f1 p' => mkp (fun r => Part.cons6 r f1) h p'
  | .hat, .cons7 h f1 f2 p' => mkp (fun r => Part.cons7 r f1 f2) h p'
  | .hat, .cons8 h f1 f2 f3 p' => mkp (fun r => Part.cons8 r f1 f2 f3) h p'
  | .fan1, .cons6 h f1 p' => mkp (fun r => Part.cons6 h r) f1 p'
  | .fan1, .cons .pr66 h p' => mkp (fun r => Part.cons6 h r) .pr59 p'
  | .fan1, .cons7 h f1 f2 p' => mkp (fun r => Part.cons7 h r f2) f1 p'
  | .fan1, .cons .pr77 h p' => mkp (fun r => Part.cons7 h r .pr59) .pr59 p'
  | .fan1, .cons8 h f1 f2 f3 p' => mkp (fun r => Part.cons8 h r f2 f3) f1 p'
  | .fan1, .cons .pr88 h p' => mkp (fun r => Part.cons8 h r .pr59 .pr59) .pr59 p'
  | .fan2, .cons7 h f1 f2 p' => mkp (fun r => Part.cons7 h f1 r) f2 p'
  | .fan2, .cons .pr77 h p' => mkp (fun r => Part.cons7 h .pr59 r) .pr59 p'
  | .fan2, .cons8 h f1 f2 f3 p' => mkp (fun r => Part.cons8 h f1 r f3) f2 p'
  | .fan2, .cons .pr88 h p' => mkp (fun r => Part.cons8 h .pr59 r .pr59) .pr59 p'
  | .fan3, .cons8 h f1 f2 f3 p' => mkp (fun r => Part.cons8 h f1 f2 r) f3 p'
  | .fan3, .cons .pr88 h p' => mkp (fun r => Part.cons8 h .pr59 .pr59 r) .pr59 p'
  | _, _ => p

/-- `take`/`drop` split the size of a part. -/
private theorem size_take_add_drop (n : ℕ) (p : Part) :
    sizePart (takePart n p) + sizePart (dropPart n p) = sizePart p := by
  conv_rhs => rw [← cat_take_drop_part n p]
  rw [size_cat_part]

/-- Coq `size_split_part`. -/
theorem size_split_part (i : SubpartLoc) (j k : ℕ) (lo : Bool) (p : Part) :
    sizePart (splitPart i j k lo p) = sizePart p := by
  have hsz := size_take_add_drop j p
  simp only [splitPart]
  split <;> (rename_i heq; simp only [heq, size_cat_part, sizePart] at hsz ⊢; try omega)

/-! ### Part comparison and intersection

Note that the intersection is slightly asymmetric, in that it will truncate the second
argument. -/

/-- Coq `cmp_part p q`: set comparison of `p` and `q`, viewed as sets of pointed maps. -/
def cmpPart (p q : Part) : PartRel :=
  match q, p with
  | .cons sq hq q', .cons sp hp p' =>
    meetPrel (cmpRange sp sq)
      (meetPrel (cmpRange hp hq)
        (cmpPart p' q'))
  | .cons sq hq q', .cons6 hp _ p' =>
    meetPrel (cmpRange .pr66 sq)
      (meetPrel (cmpRange hp hq)
        (cmpPart p' q'))
  | .cons sq hq q', .cons7 hp _ _ p' =>
    meetPrel (cmpRange .pr77 sq)
      (meetPrel (cmpRange hp hq)
        (cmpPart p' q'))
  | .cons sq hq q', .cons8 hp _ _ _ p' =>
    meetPrel (cmpRange .pr88 sq)
      (meetPrel (cmpRange hp hq)
        (cmpPart p' q'))
  | .cons6 hq _ q', .cons sp hp p' =>
    meetPrel (notPsubset (cmpRange sp .pr66))
      (meetPrel (cmpRange hp hq)
        (cmpPart p' q'))
  | .cons7 hq _ _ q', .cons sp hp p' =>
    meetPrel (notPsubset (cmpRange sp .pr77))
      (meetPrel (cmpRange hp hq)
        (cmpPart p' q'))
  | .cons8 hq _ _ _ q', .cons sp hp p' =>
    meetPrel (notPsubset (cmpRange sp .pr88))
      (meetPrel (cmpRange hp hq)
        (cmpPart p' q'))
  | .cons6 hq f1q q', .cons6 hp f1p p' =>
    meetPrel (cmpRange hp hq)
      (meetPrel (cmpRange f1p f1q)
        (cmpPart p' q'))
  | .cons7 hq f1q f2q q', .cons7 hp f1p f2p p' =>
    meetPrel (cmpRange hp hq)
      (meetPrel (cmpRange f1p f1q)
        (meetPrel (cmpRange f2p f2q)
          (cmpPart p' q')))
  | .cons8 hq f1q f2q f3q q', .cons8 hp f1p f2p f3p p' =>
    meetPrel (cmpRange hp hq)
      (meetPrel (cmpRange f1p f1q)
        (meetPrel (cmpRange f2p f2q)
          (meetPrel (cmpRange f3p f3q)
            (cmpPart p' q'))))
  | .nil, _ => .subset
  | _, .nil => .straddle
  | _, _ => .disjoint
termination_by structural q

/-- Coq `meet_part p q`: part intersection of part `p` with part sector `q` — thus assuming
`size_part p ≥ size_part q`, and `p` and `q` are not disjoint. -/
def meetPart (p q : Part) : Part :=
  match q, p with
  | .cons sq hq q', .cons sp hp p' =>
    .cons (meetRange sp sq) (meetRange hp hq) (meetPart p' q')
  | .cons _ hq q', .cons6 hp f1 p' =>
    .cons6 (meetRange hp hq) f1 (meetPart p' q')
  | .cons _ hq q', .cons7 hp f1 f2 p' =>
    .cons7 (meetRange hp hq) f1 f2 (meetPart p' q')
  | .cons _ hq q', .cons8 hp f1 f2 f3 p' =>
    .cons8 (meetRange hp hq) f1 f2 f3 (meetPart p' q')
  | .cons6 hq f1 q', .cons _ hp p' =>
    .cons6 (meetRange hp hq) f1 (meetPart p' q')
  | .cons7 hq f1 f2 q', .cons _ hp p' =>
    .cons7 (meetRange hp hq) f1 f2 (meetPart p' q')
  | .cons8 hq f1 f2 f3 q', .cons _ hp p' =>
    .cons8 (meetRange hp hq) f1 f2 f3 (meetPart p' q')
  | .cons6 hq f1q q', .cons6 hp f1p p' =>
    .cons6 (meetRange hp hq) (meetRange f1p f1q) (meetPart p' q')
  | .cons7 hq f1q f2q q', .cons7 hp f1p f2p p' =>
    .cons7 (meetRange hp hq) (meetRange f1p f1q) (meetRange f2p f2q)
      (meetPart p' q')
  | .cons8 hq f1q f2q f3q q', .cons8 hp f1p f2p f3p p' =>
    .cons8 (meetRange hp hq) (meetRange f1p f1q) (meetRange f2p f2q)
      (meetRange f3p f3q) (meetPart p' q')
  | _, _ => p
termination_by structural q

/-- Coq `size_meet_part`. -/
theorem size_meet_part (p q : Part) : sizePart (meetPart p q) = sizePart p := by
  induction q generalizing p with
  | nil => cases p <;> rfl
  | cons _ _ q ih | cons6 _ _ q ih | cons7 _ _ _ q ih | cons8 _ _ _ _ q ih =>
    cases p <;> simp only [meetPart, sizePart, ih]

/-! ### Examples of the concrete syntax -/

section Examples

open PartSyntax SublocSyntax

/-- The example of the Coq header. -/
example : (Part $[6+] 7?8 $ 7- $[* 5] 6 $) =
    .cons .pr78 .pr69 (.cons .pr57 .pr59 (.cons6 .pr59 .pr55 .nil)) := rfl

example : (Part $ 6 $[6 6-] 6 $[5] 7+ $) =
    .cons .pr66 .pr59 (.cons6 .pr66 .pr56 (.cons .pr79 .pr55 .nil)) := rfl

/-- `f1[2] <= 5` refines the second subpart to a heptagon with a pentagonal first fan. -/
example : split_part% f1[2] <= 5 (Part $ * $ 7 $ * $) = Part $ * $[* 5 *] 7 $ * $ := by decide

example : good_split% s[1] > 6 (pcons_ 5) = true := by decide

end Examples

end FourColor
