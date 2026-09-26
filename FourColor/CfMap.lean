/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfMap.Prog
import FourColor.CfMap.Ring
import FourColor.CfMap.ExtA
import FourColor.CfMap.ExtUN
import FourColor.CfMap.CompExt
import FourColor.CfMap.Map

/-!
# Configuration maps  (port of `cfmap.v`)

Configuration maps are entered as little linear construction programs: starting from a basic
triangle, these build a sequence of concentric quasicubic maps, alternatively rotating the
perimeter and adding a single outer node (and a new region) or two adjacent ones (which close up
a region and start a new one).

We also need two generalizations of this construction:
* the proof of the Birkhoff theorem requires computing the coloring of a few non two-connected
  quasicubic plain maps; they can be obtained by starting the construction from a single edge,
  and allowing adding a disconnected face during the construction;
* the contract colorings are computed as colorings of reduced maps whose construction is similar
  to the above, but uses two operations that close a region by either merging its two neighbors
  (creating a binary node), or making them adjacent (creating a ternary node).

The port is split into the following files:

* `FourColor/CfMap/Prog.lean`    : the program-level (kernel-computable) part: `Cpstep`, `Cprog`,
  `cubicProg`, `Config`, `configProg`, the concrete syntax `ConfigSyntax`, `sub2ifgt2`,
  `cprsize`, `cpksize`, `Cfmask`, `ProperCpmask`, `cfmask1`, `cpadj`, `cpadj_proper`, and the
  math-comp sequence operations `CfMap.rot`, `CfMap.rotr`, `CfMap.mask`;
* `FourColor/CfMap/Ring.lean`    : `PointedMap` and section `CpRing` (`cpring`, ...);
* `FourColor/CfMap/ExtA.lean`    : section `ExtConfig`, part 1 (`ecpR`, `ecpA`);
* `FourColor/CfMap/ExtUN.lean`   : section `ExtConfig`, part 2 (`EcpDart`, `ecpU`, `ecpN`),
  and `ecpR1_eq`;
* `FourColor/CfMap/CompExt.lean` : section `CompExtConfig` (`ecpR'`, `ecpK`, `ecpY`, `ecpH`);
* `FourColor/CfMap/Map.lean`     : `cpmap0`, `cpmap`, `cfmap`, `cfring`, `cpker`, `injcp`,
  `cpmask` and their properties, up to `cpmask_adj`.

## Definitions (math-comp names in parentheses)

* `Cpstep` (`cpstep`) : the basic steps of the configuration construction programs, with seven
  constructors `R n`, `R'`, `Y`, `H`, `U`, `K`, `A` (`CpR n`, `CpR'`, `CpY`, `CpH`, `CpU`, `CpK`,
  `CpA`). The `R` and `R'` steps merely rotate the start point of the configuration around its
  perimeter; note that there is no constructor for the `N` step, which is just a rotation
  conjugate of the `K` step.
* `Cprog` (`cprog`) : the type of configuration programs (`List Cpstep`). The actual construction
  is performed right-to-left.
* `Config` (`config`) : configuration descriptors, which add symmetry and contract annotations to
  a configuration program; `cf.cfsym`, `cf.cfcontractRef`, `cf.cfprog` (`cfsym`,
  `cfcontract_ref`, `cfprog`).
* `cubicProg cp` (`cubic_prog`) : `cp` consists only of `R`, `U`, `Y` and `H` steps.
* `configProg cp` (`config_prog`) : `cp` consists only of `R`, `Y` and `H` steps, and ends with a
  `Y` step (so the construction starts with a `Y` step).
* `PointedMap` (`pointed_map`) : a hypermap `M.pointee` on the finite dart type `M.D`, bundled
  with a reference dart `M.pointer`.
* `G.cpring x` (`cpring x`) : the ring (reverse N-cycle) of the remainder hypermap of a
  configuration, given a reference point on that ring; unless it is trivial, `G.cpring x` starts
  with `G.node x :: x :: ...`.
* `G.ProperCpring x` (`proper_cpring x`) : `x ≠ G.node x`, so `G.cpring x` has size > 1.
* `G.LongCpring x` (`long_cpring x`) : `G.face (G.edge x) ≠ G.node x`, so `G.cpring x` has
  size > 2.
* Given a reference dart `x` in a hypermap `G`, we provide pointed maps that implement the various
  construction steps, along with injections from `G`:
  - `G.ecpR n x` (`ecpR n x`) : the pointed map with reference dart `node^-n x`, which implements
    an `R n` step at dart `x`;
  - `G.ecpA x` (`ecpA x`) : a pointed map that implements an `A` step at `x`;
  - `G.ecpU x` (`ecpU x`) : a pointed map that implements a `U` step at `x`;
  - `G.ecpN x` (`ecpN x`) : a pointed map that implements an `N` step at `x`;
  - `G.ecpR' x` (`ecpR' x`) : a pointed map that implements an `R'` step at `x`
    (`ecpR ((order node x).-1) x`);
  - `G.ecpK x` (`ecpK x`) : a pointed map that implements a `K` step at `x`
    (`ecpR 1 (ecpN (ecpR' x))`);
  - `G.ecpY x` (`ecpY x`) : a pointed map that implements a `Y` step at `x` (`ecpN (ecpU x)`);
  - `G.ecpH x` (`ecpH x`) : a pointed map that implements an `H` step at `x` (`ecpN (ecpY x)`);
  - `G.icpR n x`, `G.icpR' x`, `G.icpA x`, `G.icpU x`, `G.icpN x`, `G.icpK x`, `G.icpY x`,
    `G.icpH x` : the injections from `G` into the above maps; the first three are identity
    functions as the hypermap is unchanged.
* `cpmap cp` (`cpmap`) : the pointed map obtained by running `cp : Cprog` right-to-left.
* `cfmap cf` (`cfmap`) : the pointed map of `cf : Config` (`cpmap cf.cfprog`).
* `cfring cf` (`cfring`) : the ring of `cf : Config` (`rev (cpring (cfmap cf))`).
* `cpker cp` (`cpker`) : a sequence of darts transversal of the kernel of `cpmap cp`, with one
  dart for each face NOT incident to the ring of `cpmap cp`. Thus `cpring (cpmap cp) ++ cpker cp`
  is a transversal of the faces of `cpmap cp`.
* `injcp cp1 cp2` (`injcp`) : injection from `cpmap cp2` to `cpmap (catrev cp1 cp2)`, where
  math-comp's `catrev cp1 cp2` is `List.reverseAux cp1 cp2` (`= cp1.reverse ++ cp2`).
* `cprsize cp` (`cprsize`) : the size of the ring `cpring (cpmap cp)`.
* `Cfmask` (`cfmask`) : a pair of bit sequences used to select faces in a configuration.
* `cpmask cm cp` (`cpmask`) : the subsequence of `cpring (cpmap cp) ++ cpker cp` selected by
  `cm : Cfmask`.
* `cpadj cm cp` (`cpadj`) : a `Cfmask` selecting the set of faces adjacent to the set of faces of
  `cpmap cp` selected by `cm : Cfmask`; this assumes `cp` has only `H`, `Y` and `R` steps.

## Concrete syntax (math-comp `Import ConfigSyntax`)

After `open FourColor.ConfigSyntax`:

* `Cprog H 3 H 2 Y Y` is `[.H, .R 3, .H, .R 2, .Y, .Y]`;
* `Config* 1 2 H 2 H Y` is `{ cfsym := true, cfcontractRef := [1, 2], cfprog := Cprog H 2 H Y }`;
* `Config 1 H Y` is `{ cfsym := false, cfcontractRef := [1], cfprog := Cprog H Y }`.

The items are numerals `n` (for `R n`) and the identifiers `H`, `Y`, `U` (and also `K`, `A`,
`R'`); the leading numerals of a `Config`/`Config*` form the contract annotation. For example,
the first reducible configuration of `configurations.v` is written

```
open FourColor.ConfigSyntax in
def cf001 := Config* 13
  H 3 H 5 H 5 Y 4 H 4 Y 2 Y 1 Y
```

Since the keywords `Cprog` and `Config` are scoped, inside `open FourColor.ConfigSyntax` the types
must be written `FourColor.Cprog` and `FourColor.Config` (or left to type inference). The same
configuration can be written as a plain structure literal (on one line, or with the fields aligned
on the same column when split across lines):

```
def cf001 : FourColor.Config :=
  { cfsym := true, cfcontractRef := [13],
    cfprog := [.H, .R 3, .H, .R 5, .H, .R 5, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .R 1, .Y] }
```

and both forms are equal by `rfl`.

## Representation choices

* The pointed-map constructions `ecpR`, `ecpA`, `ecpU`, `ecpN`, `ecpR'`, `ecpK`, `ecpY`, `ecpH`
  (and the injections `icp*`) are reducible (`abbrev`s), so that e.g. `(G.ecpY x).D` is reducibly
  `EcpDart (EcpDart D)` and `(G.ecpR n x).pointee` is reducibly `G`. The underlying hypermaps are
  the (non-reducible) definitions `G.ecpAMap x`, `G.ecpUMap x`, `G.ecpNMap x`, with `@[simp]`
  lemmas evaluating their `edge`, `node` and `face`.
* `cpmap` is an ordinary (structurally recursive) definition; `cpmap (s :: cp)` unfolds
  definitionally to the corresponding construction on `cpmap cp` (see the `rfl` lemmas `cpmap_R`,
  `cpmap_Y`, ...). Because the dart type of `cpmap (s :: cp)` depends on `cp`, goals involving
  `cpker` or `injcp` are best converted with `show` rather than rewritten with `cpmap_Y`.
* math-comp statements about `pointed_map`s coerced to hypermaps and darts are stated with the
  projections `M.pointee` and `M.pointer`, e.g. `cpring (ecpY x)` is
  `(G.ecpY x).pointee.cpring (G.ecpY x).pointer`.
* The adjacency map `ecpA` uses classical decidability for its `cface` tests.
-/
