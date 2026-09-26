/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfMap.Prog

/-!
# The 633 reducible configurations  (port of `configurations.v`)

**This file is generated**: it is a mechanical translation of the Coq file
`theories/proof/configurations.v` of math-comp/fourcolor, produced by
`scripts/gen_configurations.py`. Do not edit it by hand; rerun the script instead:

```
python3 scripts/gen_configurations.py --coq-dir <fourcolor>/theories/proof \
  --out FourColor/Configurations.lean
```

The Coq file gives the construction programs of the 633 reducible configurations of the proof,
in the concrete syntax of `cfmap.v` (module `ConfigSyntax`, see `FourColor/CfMap/Prog.lean`).

* `cfNNN` (math-comp `cfXXX`, `NNN` = `001` ... `633`): the data for configuration number `NNN`.
* `theConfigs` (math-comp `the_configs`): the list of all the `cfNNN`, in order; configuration
  number `n` has index `n - 1` in `theConfigs`, as list indices start at 0.
* `cf000` (math-comp `cf000`, defined in `cfreducible.v` as `Config 0 H`): a dummy
  configuration, the default value in `theConfigs.getD i cf000` (math-comp `nth cf000`).

## Representation

The Coq definition `Definition cfNNN := Config* c1 .. ck s1 .. sm.` (resp. `Config`), where the
`ci` are numerals and `s1` is `H`, is the value of math-comp's `parse_config`; it is translated
into the explicit structure literal it denotes:

* `cfsym := true` for `Config*`, `cfsym := false` for `Config`;
* `cfcontractRef := [c1, ..., ck]`: the leading numerals form the contract annotation;
* `cfprog := [s1', ..., sm']`: the remaining items form the construction program, where a numeral
  `n` stands for the rotation step `.R n` (math-comp coercion `CpR : nat >-> cpstep`) and the
  identifiers `H`, `Y` for the steps `.H`, `.Y` (`U`, `K`, `A` do not occur).

The Coq text of each configuration is quoted verbatim in its docstring. The explicit form does
not depend on the notation nor on `ConfigSyntax.parseConfig`, and `cfNNN` unfolds directly to
constructor applications. With `--check-out FILE`, the script also writes a validation file
checking by `rfl` that each `cfNNN` is equal to the `Config*`/`Config` notation of
`FourColor.ConfigSyntax` applied to the Coq items, and (with `--ring-csv`) by `decide +kernel`
that the ring sizes `cprsize cf.cfprog` are the expected ones; both checks pass for this file.

Only the program-level part of `cfmap.v` is needed, so this file imports
`FourColor.CfMap.Prog` rather than the whole `FourColor.CfMap`. The definitions are computable
(so that they can be `#eval`uated), but closed-term extraction is disabled for this file
(`compiler.extract_closed`): it would compile every sub-term of the data into a separate
auxiliary constant and triple the size of the `.olean`. This only affects the compiled code.

The file ends with two sanity checks, not present in the Coq development and proved by kernel
evaluation: `theConfigs` has length 633, and the program of every configuration satisfies
`configProg` (math-comp `config_prog`: only `R`, `Y` and `H` steps, ending with a `Y`).
-/

namespace FourColor

-- Code generation only: do not cache every closed sub-term of the data (see the header).
set_option compiler.extract_closed false

/-! ### The dummy configuration `cf000` (from `cfreducible.v`) -/

/-- math-comp `cf000` (`cfreducible.v`), the default value of `nth` on configuration lists:
```
Config 0 H
```
-/
def cf000 : Config :=
  { cfsym := false, cfcontractRef := [0], cfprog := [.H] }

/-! ### The 633 reducible configurations -/

/-- math-comp `cf001`:
```
Config* 13
  H 3 H 5 H 5 Y 4 H 4 Y 2 Y 1 Y
```
-/
def cf001 : Config :=
  { cfsym := true, cfcontractRef := [13],
    cfprog := [.H, .R 3, .H, .R 5, .H, .R 5, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf002`:
```
Config* 6
  H 2 H 6 Y 4 H 1 Y 4 H 4 Y 2 Y Y
```
-/
def cf002 : Config :=
  { cfsym := true, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 6, .Y, .R 4, .H, .R 1, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf003`:
```
Config* 17
  H 1 H 6 H 1 Y 4 H 6 H 6 H 6 Y Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf003 : Config :=
  { cfsym := true, cfcontractRef := [17],
    cfprog := [.H, .R 1, .H, .R 6, .H, .R 1, .Y, .R 4, .H, .R 6, .H, .R 6, .H, .R 6, .Y, .Y, .R 4,
               .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf004`:
```
Config* 1 2 12 13
  H 2 H 7 Y 5 H 1 Y 4 H 1 Y 4 Y 2 Y 2 Y
```
-/
def cf004 : Config :=
  { cfsym := true, cfcontractRef := [1, 2, 12, 13],
    cfprog := [.H, .R 2, .H, .R 7, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 4, .Y, .R 2, .Y,
               .R 2, .Y] }

/-- math-comp `cf005`:
```
Config* 10
  H 6 H 1 Y 5 H 1 Y 4 H 1 Y 4 H 4 Y 2 Y Y
```
-/
def cf005 : Config :=
  { cfsym := true, cfcontractRef := [10],
    cfprog := [.H, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 4, .H, .R 4, .Y,
               .R 2, .Y, .Y] }

/-- math-comp `cf006`:
```
Config 19
  H 2 H 8 Y 4 H 7 H 2 H 7 Y 6 H 1 Y 1 Y 2 H 4 Y 2 Y Y
```
-/
def cf006 : Config :=
  { cfsym := false, cfcontractRef := [19],
    cfprog := [.H, .R 2, .H, .R 8, .Y, .R 4, .H, .R 7, .H, .R 2, .H, .R 7, .Y, .R 6, .H, .R 1, .Y,
               .R 1, .Y, .R 2, .H, .R 4, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf007`:
```
Config* 17
  H 3 H 8 H 8 Y 6 H 1 Y 5 H 1 Y 5 Y 3 Y 2 Y Y
```
-/
def cf007 : Config :=
  { cfsym := true, cfcontractRef := [17],
    cfprog := [.H, .R 3, .H, .R 8, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 5, .Y,
               .R 3, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf008`:
```
Config* 6
  H 2 H 7 Y 3 H 6 Y 2 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf008 : Config :=
  { cfsym := true, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 7, .Y, .R 3, .H, .R 6, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .H, .R 4,
               .Y, .Y, .R 1, .Y] }

/-- math-comp `cf009`:
```
Config* 26
  H 8 H 1 Y 7 H 7 H 1 Y 5 H 7 Y 3 H 6 H 6 Y Y Y 3 Y Y
```
-/
def cf009 : Config :=
  { cfsym := true, cfcontractRef := [26],
    cfprog := [.H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 7, .H, .R 1, .Y, .R 5, .H, .R 7, .Y, .R 3, .H,
               .R 6, .H, .R 6, .Y, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf010`:
```
Config 20
  H 2 H 9 Y 4 H 2 H 8 Y 3 H 1 Y 6 H 1 Y 1 Y 2 H 4 Y 2 Y Y
```
-/
def cf010 : Config :=
  { cfsym := false, cfcontractRef := [20],
    cfprog := [.H, .R 2, .H, .R 9, .Y, .R 4, .H, .R 2, .H, .R 8, .Y, .R 3, .H, .R 1, .Y, .R 6, .H,
               .R 1, .Y, .R 1, .Y, .R 2, .H, .R 4, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf011`:
```
Config* 1 2 8 9
  H 8 H 1 Y 7 H 1 Y 5 H 1 H 6 H 1 Y 2 H 6 Y Y Y 3 Y 2 Y
```
-/
def cf011 : Config :=
  { cfsym := true, cfcontractRef := [1, 2, 8, 9],
    cfprog := [.H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 6, .H, .R 1, .Y,
               .R 2, .H, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 2, .Y] }

/-- math-comp `cf012`:
```
Config* 6
  H 2 H 8 Y 3 H 7 Y 3 H 6 Y 2 H 1 Y H 4 Y Y 1 Y
```
-/
def cf012 : Config :=
  { cfsym := true, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 3, .H, .R 6, .Y, .R 2, .H, .R 1, .Y,
               .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf013`:
```
Config 23
  H 3 H 9 H 9 Y 7 H 1 Y 5 H 2 H 7 Y 6 Y 4 Y 3 Y 2 Y 1 Y
```
-/
def cf013 : Config :=
  { cfsym := false, cfcontractRef := [23],
    cfprog := [.H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 2, .H, .R 7, .Y,
               .R 6, .Y, .R 4, .Y, .R 3, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf014`:
```
Config* 14
  H 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H 1 Y 5 H 5 Y 2 Y 3 Y 1 Y
```
-/
def cf014 : Config :=
  { cfsym := true, cfcontractRef := [14],
    cfprog := [.H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y,
               .R 5, .H, .R 5, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf015`:
```
Config 8 9 15 16
  H 9 H 1 Y 8 H 8 H 1 Y 7 H 1 Y 6 H 7 Y 2 H 6 Y Y Y 3 Y 2 Y
```
-/
def cf015 : Config :=
  { cfsym := false, cfcontractRef := [8, 9, 15, 16],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H,
               .R 7, .Y, .R 2, .H, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 2, .Y] }

/-- math-comp `cf016`:
```
Config 30
  H 2 H 10 Y 3 H 9 Y 5 H 8 H 2 H 8 Y 6 H 1 H 1 Y 1 Y 1 Y 3 Y 2 Y 1 Y
```
-/
def cf016 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 5, .H, .R 8, .H, .R 2, .H, .R 8, .Y,
               .R 6, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf017`:
```
Config* 26
  H 2 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 4 H 7 H 7 Y 3 Y 4 Y 3 Y Y 1 Y
```
-/
def cf017 : Config :=
  { cfsym := true, cfcontractRef := [26],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 4, .H,
               .R 7, .H, .R 7, .Y, .R 3, .Y, .R 4, .Y, .R 3, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf018`:
```
Config 26
  H 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 6 H 1 Y 6 H 6 Y 3 Y 3 Y Y 1 Y
```
-/
def cf018 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .H,
               .R 1, .Y, .R 6, .H, .R 6, .Y, .R 3, .Y, .R 3, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf019`:
```
Config* 6
  H 2 H 9 Y 3 H 8 Y 3 H 7 Y 2 H 1 H 1 Y H 5 Y Y Y 1 Y
```
-/
def cf019 : Config :=
  { cfsym := true, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 2, .H, .R 1, .H,
               .R 1, .Y, .H, .R 5, .Y, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf020`:
```
Config 1 2 8 9
  H 10 H 1 Y 9 H 1 Y 8 H 7 H 2 H 9 Y 5 Y 3 H 7 H 7 Y Y Y 3 Y 1 Y 2 Y
```
-/
def cf020 : Config :=
  { cfsym := false, cfcontractRef := [1, 2, 8, 9],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 7, .H, .R 2, .H, .R 9, .Y,
               .R 5, .Y, .R 3, .H, .R 7, .H, .R 7, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf021`:
```
Config* 6
  H 2 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 2 H 1 Y H 5 Y Y Y 1 Y
```
-/
def cf021 : Config :=
  { cfsym := true, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y,
               .R 2, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf022`:
```
Config 29
  H 2 H 11 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 2 H 1 H 1 Y 5 Y 3 Y 1 Y Y 1 Y
```
-/
def cf022 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H,
               .R 8, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 5, .Y, .R 3, .Y, .R 1, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf023`:
```
Config 1 2 8 9
  H 2 H 12 Y 3 H 11 Y 3 H 2 H 10 Y 3 H 9 Y 5 Y 6 H 1 H 1 Y 1 Y 1 Y 3 Y 2 Y 1 Y
```
-/
def cf023 : Config :=
  { cfsym := false, cfcontractRef := [1, 2, 8, 9],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 3,
               .H, .R 9, .Y, .R 5, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y,
               .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf024`:
```
Config* 6
  H 2 H 7 Y 5 H 1 Y 5 H 5 H 5 Y 3 Y Y Y
```
-/
def cf024 : Config :=
  { cfsym := true, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 7, .Y, .R 5, .H, .R 1, .Y, .R 5, .H, .R 5, .H, .R 5, .Y, .R 3, .Y,
               .Y, .Y] }

/-- math-comp `cf025`:
```
Config* 25
  H 3 H 7 H 1 Y 4 H 1 H 1 H 1 Y 1 Y 1 Y 2 H 4 Y 2 Y 1 Y
```
-/
def cf025 : Config :=
  { cfsym := true, cfcontractRef := [25],
    cfprog := [.H, .R 3, .H, .R 7, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 1, .Y,
               .R 1, .Y, .R 2, .H, .R 4, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf026`:
```
Config 19
  H 7 H 1 Y 3 H 7 Y 4 H 5 H 1 Y 2 Y 3 Y 1 Y 2 Y
```
-/
def cf026 : Config :=
  { cfsym := false, cfcontractRef := [19],
    cfprog := [.H, .R 7, .H, .R 1, .Y, .R 3, .H, .R 7, .Y, .R 4, .H, .R 5, .H, .R 1, .Y, .R 2, .Y,
               .R 3, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf027`:
```
Config 6
  H 2 H 8 Y 6 H 1 Y 4 H 6 Y 3 H 1 Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf027 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 4, .H, .R 6, .Y, .R 3, .H, .R 1, .Y,
               .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf028`:
```
Config 26
  H 2 H 9 Y 4 H 3 H 7 H 1 Y 5 H 1 H 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf028 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 2, .H, .R 9, .Y, .R 4, .H, .R 3, .H, .R 7, .H, .R 1, .Y, .R 5, .H, .R 1, .H,
               .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf029`:
```
Config* 4 5 21 25
  H 8 H 1 Y 7 H 1 Y 5 H 1 H 6 H 1 Y 6 H 1 Y 1 Y 1 Y 1 Y 2 Y
```
-/
def cf029 : Config :=
  { cfsym := true, cfcontractRef := [4, 5, 21, 25],
    cfprog := [.H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 6, .H, .R 1, .Y,
               .R 6, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf030`:
```
Config 19
  H 2 H 9 Y 4 H 8 H 2 H 8 Y 7 H 1 Y 1 Y 3 H 5 H 5 Y 3 Y Y Y
```
-/
def cf030 : Config :=
  { cfsym := false, cfcontractRef := [19],
    cfprog := [.H, .R 2, .H, .R 9, .Y, .R 4, .H, .R 8, .H, .R 2, .H, .R 8, .Y, .R 7, .H, .R 1, .Y,
               .R 1, .Y, .R 3, .H, .R 5, .H, .R 5, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf031`:
```
Config 18
  H 2 H 9 Y 6 H 8 H 2 H 8 Y 2 H 7 Y Y 5 H 1 Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf031 : Config :=
  { cfsym := false, cfcontractRef := [18],
    cfprog := [.H, .R 2, .H, .R 9, .Y, .R 6, .H, .R 8, .H, .R 2, .H, .R 8, .Y, .R 2, .H, .R 7, .Y,
               .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf032`:
```
Config 23
  H 2 H 9 Y 7 H 1 Y 4 H 3 H 7 H 7 Y 6 Y 4 Y Y 3 Y 1 Y
```
-/
def cf032 : Config :=
  { cfsym := false, cfcontractRef := [23],
    cfprog := [.H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 4, .H, .R 3, .H, .R 7, .H, .R 7, .Y,
               .R 6, .Y, .R 4, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf033`:
```
Config 24
  H 3 H 9 H 9 Y 6 H 2 H 8 Y 6 H 1 Y 6 Y 4 Y Y 2 Y 2 Y
```
-/
def cf033 : Config :=
  { cfsym := false, cfcontractRef := [24],
    cfprog := [.H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .H, .R 1, .Y,
               .R 6, .Y, .R 4, .Y, .Y, .R 2, .Y, .R 2, .Y] }

/-- math-comp `cf034`:
```
Config 15
  H 8 H 1 Y 7 H 1 Y 5 H 2 H 7 Y 5 H 1 Y 4 Y 3 Y Y 2 Y
```
-/
def cf034 : Config :=
  { cfsym := false, cfcontractRef := [15],
    cfprog := [.H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 2, .H, .R 7, .Y, .R 5, .H,
               .R 1, .Y, .R 4, .Y, .R 3, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf035`:
```
Config 6
  H 2 H 9 Y 7 H 1 Y 6 H 1 Y 5 H 6 Y 4 Y 4 H 4 Y 2 Y Y
```
-/
def cf035 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 6, .Y,
               .R 4, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf036`:
```
Config* 23
  H 7 H 1 H 1 Y 3 H 8 Y 4 H 6 H 1 Y 2 Y 3 Y 1 Y 1 Y 2 Y
```
-/
def cf036 : Config :=
  { cfsym := true, cfcontractRef := [23],
    cfprog := [.H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 6, .H, .R 1, .Y,
               .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf037`:
```
Config* 23
  H 2 H 9 Y 7 H 1 Y 5 H 2 H 7 Y 6 H 6 Y 4 Y 2 Y 2 Y 1 Y
```
-/
def cf037 : Config :=
  { cfsym := true, cfcontractRef := [23],
    cfprog := [.H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 2, .H, .R 7, .Y, .R 6, .H,
               .R 6, .Y, .R 4, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf038`:
```
Config 10
  H 2 H 8 Y 3 H 7 Y 3 H 6 Y 2 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf038 : Config :=
  { cfsym := false, cfcontractRef := [10],
    cfprog := [.H, .R 2, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 3, .H, .R 6, .Y, .R 2, .H, .R 1, .H,
               .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf039`:
```
Config* 1 2 8 9
  H 2 H 10 Y 3 H 9 Y 3 H 3 H 7 H 1 Y 6 H 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf039 : Config :=
  { cfsym := true, cfcontractRef := [1, 2, 8, 9],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 3, .H, .R 7, .H, .R 1, .Y,
               .R 6, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf040`:
```
Config 11 12 21 26
  H 2 H 10 Y 4 H 2 H 9 Y 3 H 8 Y 5 H 1 H 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf040 : Config :=
  { cfsym := false, cfcontractRef := [11, 12, 21, 26],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 5, .H,
               .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf041`:
```
Config 20
  H 2 H 10 Y 5 H 2 H 9 Y 3 H 1 Y 7 H 1 Y 1 Y 3 H 5 H 5 Y 3 Y Y Y
```
-/
def cf041 : Config :=
  { cfsym := false, cfcontractRef := [20],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 5, .H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 1, .Y, .R 7, .H,
               .R 1, .Y, .R 1, .Y, .R 3, .H, .R 5, .H, .R 5, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf042`:
```
Config 23
  H 2 H 10 Y 3 H 9 Y 4 H 8 H 2 H 8 Y 7 H 1 Y 1 Y 2 H 5 Y Y 1 Y 2 Y
```
-/
def cf042 : Config :=
  { cfsym := false, cfcontractRef := [23],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 8, .H, .R 2, .H, .R 8, .Y,
               .R 7, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 5, .Y, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf043`:
```
Config 30
  H 8 H 2 H 10 Y 8 H 1 Y 6 H 1 H 7 H 1 Y 2 H 7 Y Y Y 3 Y 1 Y 2 Y
```
-/
def cf043 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 7, .H,
               .R 1, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf044`:
```
Config 25
  H 2 H 10 Y 4 H 8 H 1 Y 4 H 8 H 2 H 8 Y 2 H 7 Y Y Y Y 3 Y 1 Y
```
-/
def cf044 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 4, .H, .R 8, .H, .R 2, .H,
               .R 8, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf045`:
```
Config* 24
  H 6 H 3 H 9 H 9 Y 6 H 1 H 7 H 1 Y 2 H 7 Y Y Y 4 H 4 Y 2 Y Y
```
-/
def cf045 : Config :=
  { cfsym := true, cfcontractRef := [24],
    cfprog := [.H, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 6, .H, .R 1, .H, .R 7, .H, .R 1, .Y,
               .R 2, .H, .R 7, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf046`:
```
Config 18
  H 8 H 1 Y 6 H 1 H 7 H 1 Y 2 H 7 Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf046 : Config :=
  { cfsym := false, cfcontractRef := [18],
    cfprog := [.H, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 7, .H, .R 1, .Y, .R 2, .H, .R 7, .Y,
               .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf047`:
```
Config* 25
  H 3 H 10 H 10 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 Y 4 Y 2 Y 3 Y Y
```
-/
def cf047 : Config :=
  { cfsym := true, cfcontractRef := [25],
    cfprog := [.H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H,
               .R 1, .Y, .R 6, .Y, .R 4, .Y, .R 2, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf048`:
```
Config 27
  H 2 H 9 Y 3 H 8 Y 3 H 7 Y 4 H 5 H 1 Y H 5 Y Y 1 Y 2 Y
```
-/
def cf048 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 4, .H, .R 5, .H,
               .R 1, .Y, .H, .R 5, .Y, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf049`:
```
Config 28
  H 2 H 10 Y 3 H 9 Y 3 H 8 Y 4 H 6 H 1 Y 2 H 1 Y 5 Y 4 Y 3 Y Y
```
-/
def cf049 : Config :=
  { cfsym := false, cfcontractRef := [28],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 6, .H,
               .R 1, .Y, .R 2, .H, .R 1, .Y, .R 5, .Y, .R 4, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf050`:
```
Config 27
  H 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 6 H 1 Y 6 H 6 Y 2 Y 2 Y 2 Y 1 Y
```
-/
def cf050 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 6, .H,
               .R 1, .Y, .R 6, .H, .R 6, .Y, .R 2, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf051`:
```
Config 14
  H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 H 6 H 6 Y 3 Y Y 3 Y 1 Y
```
-/
def cf051 : Config :=
  { cfsym := false, cfcontractRef := [14],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y,
               .R 6, .H, .R 6, .H, .R 6, .Y, .R 3, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf052`:
```
Config 24
  H 3 H 9 H 1 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 2 H 1 Y 1 Y 3 Y 3 Y Y
```
-/
def cf052 : Config :=
  { cfsym := false, cfcontractRef := [24],
    cfprog := [.H, .R 3, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H,
               .R 7, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 3, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf053`:
```
Config 23
  H 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 1 Y 6 H 1 Y 5 Y Y 3 Y 1 Y 1 Y
```
-/
def cf053 : Config :=
  { cfsym := false, cfcontractRef := [23],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 1, .Y,
               .R 6, .H, .R 1, .Y, .R 5, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf054`:
```
Config 28
  H 3 H 10 H 10 Y 7 H 2 H 9 Y 6 H 2 H 8 Y 7 Y 5 Y Y 3 Y 2 Y Y
```
-/
def cf054 : Config :=
  { cfsym := false, cfcontractRef := [28],
    cfprog := [.H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 6, .H, .R 2, .H,
               .R 8, .Y, .R 7, .Y, .R 5, .Y, .Y, .R 3, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf055`:
```
Config 28
  H 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 6 H 1 Y 4 Y 2 H 1 Y 1 Y Y 2 Y
```
-/
def cf055 : Config :=
  { cfsym := false, cfcontractRef := [28],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .H,
               .R 1, .Y, .R 4, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf056`:
```
Config 28
  H 9 H 1 Y 8 H 1 Y 5 H 3 H 8 H 8 Y 6 H 1 Y 5 Y 3 Y 1 Y 2 Y Y
```
-/
def cf056 : Config :=
  { cfsym := false, cfcontractRef := [28],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 3, .H, .R 8, .H, .R 8, .Y,
               .R 6, .H, .R 1, .Y, .R 5, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf057`:
```
Config 7
  H 3 H 10 H 10 Y 8 H 1 Y 7 H 1 Y 6 H 7 Y 5 Y 4 H 5 Y 3 Y Y Y
```
-/
def cf057 : Config :=
  { cfsym := false, cfcontractRef := [7],
    cfprog := [.H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H,
               .R 7, .Y, .R 5, .Y, .R 4, .H, .R 5, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf058`:
```
Config 26
  H 3 H 10 H 10 Y 8 H 1 Y 5 H 3 H 8 H 8 Y 7 Y 5 Y Y Y 3 Y 1 Y
```
-/
def cf058 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 3, .H, .R 8, .H,
               .R 8, .Y, .R 7, .Y, .R 5, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf059`:
```
Config 28
  H 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 6 H 1 Y 6 H 6 Y Y Y 2 Y 2 Y
```
-/
def cf059 : Config :=
  { cfsym := false, cfcontractRef := [28],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 6, .H,
               .R 1, .Y, .R 6, .H, .R 6, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y] }

/-- math-comp `cf060`:
```
Config 21
  H 2 H 10 Y 7 H 2 H 9 Y 5 H 3 H 8 H 8 Y 7 Y 4 Y 1 Y 3 Y 2 Y Y
```
-/
def cf060 : Config :=
  { cfsym := false, cfcontractRef := [21],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 5, .H, .R 3, .H, .R 8, .H,
               .R 8, .Y, .R 7, .Y, .R 4, .Y, .R 1, .Y, .R 3, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf061`:
```
Config 6
  H 2 H 10 Y 8 H 1 Y 7 H 1 Y 5 H 7 Y 2 H 1 H 1 Y 1 Y Y 3 Y 1 Y
```
-/
def cf061 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 7, .Y,
               .R 2, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf062`:
```
Config 8 9 15 16
  H 2 H 11 Y 3 H 2 H 10 Y 3 H 9 Y Y 4 H 7 H 7 H 7 Y Y Y 4 Y Y Y
```
-/
def cf062 : Config :=
  { cfsym := false, cfcontractRef := [8, 9, 15, 16],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .Y, .R 4,
               .H, .R 7, .H, .R 7, .H, .R 7, .Y, .Y, .Y, .R 4, .Y, .Y, .Y] }

/-- math-comp `cf063`:
```
Config 31
  H 10 H 1 Y 9 H 8 H 2 H 10 Y 8 H 1 Y 7 H 8 Y 2 H 7 Y Y Y 3 Y 1 Y 2 Y
```
-/
def cf063 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y,
               .R 7, .H, .R 8, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf064`:
```
Config 4 5 22 27
  H 2 H 11 Y 3 H 10 Y 3 H 2 H 9 Y 3 H 8 Y 6 H 7 Y Y Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf064 : Config :=
  { cfsym := false, cfcontractRef := [4, 5, 22, 27],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 3, .H,
               .R 8, .Y, .R 6, .H, .R 7, .Y, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf065`:
```
Config 31
  H 2 H 11 Y 4 H 2 H 10 Y 4 H 8 H 1 Y 8 Y 6 H 1 H 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf065 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y,
               .R 8, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1,
               .Y] }

/-- math-comp `cf066`:
```
Config 1 2 8 9
  H 2 H 11 Y 3 H 10 Y 4 H 3 H 8 H 1 Y 7 H 1 Y 7 H 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf066 : Config :=
  { cfsym := false, cfcontractRef := [1, 2, 8, 9],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 3, .H, .R 8, .H, .R 1, .Y,
               .R 7, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1,
               .Y] }

/-- math-comp `cf067`:
```
Config 34
  H 10 H 1 Y 8 H 2 H 10 Y 6 H 1 H 8 H 1 Y 3 H 8 H 8 Y Y Y 3 Y 1 Y 3 Y Y
```
-/
def cf067 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 6, .H, .R 1, .H, .R 8, .H,
               .R 1, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf068`:
```
Config 32
  H 9 H 2 H 11 Y 9 H 1 Y 6 H 1 H 8 H 1 Y 8 H 1 Y 1 Y 2 H 6 Y 5 Y 3 Y 1 Y 1 Y
```
-/
def cf068 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 8, .H,
               .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 6, .Y, .R 5, .Y, .R 3, .Y, .R 1,
               .Y, .R 1, .Y] }

/-- math-comp `cf069`:
```
Config* 25
  H 10 H 1 Y 9 H 9 H 1 Y 7 H 1 H 8 H 1 Y 2 H 8 Y Y Y 4 H 1 Y 4 Y 2 Y Y
```
-/
def cf069 : Config :=
  { cfsym := true, cfcontractRef := [25],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H,
               .R 1, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 4, .H, .R 1, .Y, .R 4, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf070`:
```
Config 33
  H 2 H 10 Y 3 H 2 H 9 Y 5 H 8 H 7 H 1 H 1 H 1 Y 1 Y Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf070 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 5, .H, .R 8, .H, .R 7, .H,
               .R 1, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf071`:
```
Config 21
  H 9 H 1 Y 7 H 8 H 1 Y 6 H 1 H 1 H 8 H 8 Y Y 1 Y Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf071 : Config :=
  { cfsym := false, cfcontractRef := [21],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .H,
               .R 8, .H, .R 8, .Y, .Y, .R 1, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf072`:
```
Config 25
  H 9 H 1 Y 8 H 6 H 3 H 9 H 9 Y 7 H 8 Y 2 H 7 Y Y Y 4 H 4 Y 2 Y Y
```
-/
def cf072 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 7, .H,
               .R 8, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf073`:
```
Config 25
  H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 2 H 1 Y 4 Y 3 Y 1 Y Y
```
-/
def cf073 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y,
               .R 3, .H, .R 7, .Y, .R 2, .H, .R 1, .Y, .R 4, .Y, .R 3, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf074`:
```
Config 15
  H 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 6 H 1 Y 5 Y 3 Y 3 Y 3 Y 1 Y
```
-/
def cf074 : Config :=
  { cfsym := false, cfcontractRef := [15],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H,
               .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .Y, .R 3, .Y, .R 3, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf075`:
```
Config 15 29
  H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 7 Y 5 Y 3 Y 3 Y Y Y
```
-/
def cf075 : Config :=
  { cfsym := false, cfcontractRef := [15, 29],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H,
               .R 2, .H, .R 8, .Y, .R 7, .Y, .R 5, .Y, .R 3, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf076`:
```
Config* 27
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 H 6 Y 2 Y 4 Y Y Y
```
-/
def cf076 : Config :=
  { cfsym := true, cfcontractRef := [27],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y,
               .R 6, .H, .R 1, .Y, .R 6, .H, .R 6, .Y, .R 2, .Y, .R 4, .Y, .Y, .Y] }

/-- math-comp `cf077`:
```
Config* 14
  H 2 H 9 Y 3 H 8 Y 3 H 7 Y 3 H 6 Y 2 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf077 : Config :=
  { cfsym := true, cfcontractRef := [14],
    cfprog := [.H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 3, .H, .R 6, .Y,
               .R 2, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf078`:
```
Config 14
  H 2 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 2 H 1 H 1 Y 1 Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf078 : Config :=
  { cfsym := false, cfcontractRef := [14],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 7, .Y,
               .R 2, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf079`:
```
Config 18
  H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 3 H 5 H 1 Y 2 Y 1 Y Y Y
```
-/
def cf079 : Config :=
  { cfsym := false, cfcontractRef := [18],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y,
               .R 3, .H, .R 7, .Y, .R 3, .H, .R 5, .H, .R 1, .Y, .R 2, .Y, .R 1, .Y, .Y, .Y] }

/-- math-comp `cf080`:
```
Config 27
  H 3 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 2 H 1 H 1 Y 1 Y 4 Y 3 Y Y Y
```
-/
def cf080 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 3, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H,
               .R 8, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 4, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf081`:
```
Config 30
  H 10 H 1 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 1 Y 7 H 7 Y 3 Y 1 Y 3 Y Y 1 Y
```
-/
def cf081 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y,
               .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 3, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf082`:
```
Config 14
  H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H 1 H 1 Y H 5 Y Y Y 1 Y
```
-/
def cf082 : Config :=
  { cfsym := false, cfcontractRef := [14],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y,
               .R 5, .H, .R 1, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf083`:
```
Config 4 5 25 30
  H 11 H 1 Y 10 H 1 Y 9 H 9 H 1 Y 8 H 1 Y 8 H 8 H 8 Y Y Y Y 3 Y 1 Y 1 Y
```
-/
def cf083 : Config :=
  { cfsym := false, cfcontractRef := [4, 5, 25, 30],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H,
               .R 1, .Y, .R 8, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf084`:
```
Config 20
  H 10 H 1 Y 9 H 1 Y 7 H 8 H 1 Y 7 H 1 Y 3 H 1 H 1 Y 1 Y Y 3 Y 1 Y 1 Y
```
-/
def cf084 : Config :=
  { cfsym := false, cfcontractRef := [20],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 8, .H, .R 1, .Y, .R 7, .H,
               .R 1, .Y, .R 3, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf085`:
```
Config 30
  H 10 H 1 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 1 Y 7 H 1 Y 1 Y Y 3 Y 1 Y Y
```
-/
def cf085 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y,
               .R 7, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf086`:
```
Config 26
  H 10 H 1 Y 9 H 1 Y 5 H 4 H 9 H 9 H 9 Y 7 H 1 Y 5 Y 4 Y 1 Y 3 Y Y Y
```
-/
def cf086 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 5, .H, .R 4, .H, .R 9, .H, .R 9, .H,
               .R 9, .Y, .R 7, .H, .R 1, .Y, .R 5, .Y, .R 4, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf087`:
```
Config 25
  H 11 H 1 Y 10 H 1 Y 8 H 9 H 1 Y 3 H 1 Y 1 Y 7 H 1 Y 1 Y 3 H 5 H 5 Y 3 Y Y Y
```
-/
def cf087 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 3, .H,
               .R 1, .Y, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 5, .H, .R 5, .Y, .R 3,
               .Y, .Y, .Y] }

/-- math-comp `cf088`:
```
Config 35
  H 11 H 1 Y 10 H 10 H 1 Y 8 H 2 H 10 Y 7 H 9 Y 3 H 8 H 8 Y Y Y 3 Y 1 Y 3 Y Y
```
-/
def cf088 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10,
               .Y, .R 7, .H, .R 9, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y,
               .R 3, .Y, .Y] }

/-- math-comp `cf089`:
```
Config 8 9 15 16
  H 10 H 1 Y 9 H 9 H 1 Y 8 H 1 Y 6 H 1 H 1 H 8 H 8 Y Y 1 Y Y Y 3 Y 1 Y
```
-/
def cf089 : Config :=
  { cfsym := false, cfcontractRef := [8, 9, 15, 16],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H,
               .R 1, .H, .R 1, .H, .R 8, .H, .R 8, .Y, .Y, .R 1, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf090`:
```
Config* 14 15 21 22
  H 8 H 3 H 11 H 11 Y 9 H 9 H 1 Y 8 H 1 Y 6 H 8 Y 3 H 7 Y Y Y Y 3 Y 1 Y
```
-/
def cf090 : Config :=
  { cfsym := true, cfcontractRef := [14, 15, 21, 22],
    cfprog := [.H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H,
               .R 1, .Y, .R 6, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf091`:
```
Config 34
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 7 H 1 H 8 H 1 Y 8 H 1 Y 1 Y 2 H 6 Y Y Y Y Y
```
-/
def cf091 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H,
               .R 1, .H, .R 8, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 6, .Y, .Y,
               .Y, .Y, .Y] }

/-- math-comp `cf092`:
```
Config 28
  H 8 H 3 H 11 H 11 Y 9 H 1 Y 7 H 1 H 8 H 1 Y 2 H 8 Y Y Y 5 H 5 Y 2 Y 3 Y 1 Y
```
-/
def cf092 : Config :=
  { cfsym := false, cfcontractRef := [28],
    cfprog := [.H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H,
               .R 8, .H, .R 1, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 5, .H, .R 5, .Y, .R 2, .Y, .R 3,
               .Y, .R 1, .Y] }

/-- math-comp `cf093`:
```
Config 22
  H 10 H 1 Y 9 H 1 Y 7 H 1 H 8 H 1 Y 2 H 8 Y Y 5 H 1 H 1 Y H 5 Y Y Y 1 Y
```
-/
def cf093 : Config :=
  { cfsym := false, cfcontractRef := [22],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H, .R 1, .Y,
               .R 2, .H, .R 8, .Y, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .Y, .R 1,
               .Y] }

/-- math-comp `cf094`:
```
Config 25
  H 10 H 1 Y 9 H 9 H 1 Y 8 H 1 Y 6 H 1 H 1 H 8 H 8 Y Y 1 Y Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf094 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H,
               .R 1, .H, .R 1, .H, .R 8, .H, .R 8, .Y, .Y, .R 1, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3,
               .Y, .R 1, .Y] }

/-- math-comp `cf095`:
```
Config 28
  H 2 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 2 H 1 H 1 Y 5 Y 3 Y 1 Y Y Y
```
-/
def cf095 : Config :=
  { cfsym := false, cfcontractRef := [28],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9,
               .Y, .R 3, .H, .R 8, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 5, .Y, .R 3, .Y, .R 1, .Y,
               .Y, .Y] }

/-- math-comp `cf096`:
```
Config 27
  H 11 H 1 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y 3 Y 4 Y Y 1 Y Y
```
-/
def cf096 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8,
               .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 3, .Y, .R 4, .Y, .Y, .R 1,
               .Y, .Y] }

/-- math-comp `cf097`:
```
Config 26
  H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 4 H 7 H 7 Y Y 2 H 1 Y 1 Y 1 Y Y
```
-/
def cf097 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y,
               .R 4, .H, .R 7, .H, .R 7, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf098`:
```
Config 26
  H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 7 Y 1 Y 5 H 5 Y Y Y 1 Y
```
-/
def cf098 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H,
               .R 2, .H, .R 8, .Y, .R 7, .Y, .R 1, .Y, .R 5, .H, .R 5, .Y, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf099`:
```
Config 18
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 H 1 Y H 5 Y Y Y 1 Y
```
-/
def cf099 : Config :=
  { cfsym := false, cfcontractRef := [18],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y,
               .R 6, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf100`:
```
Config* 27
  H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 2 H 1 H 1 Y H 6 Y Y Y Y Y
```
-/
def cf100 : Config :=
  { cfsym := true, cfcontractRef := [27],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y,
               .R 2, .H, .R 1, .H, .R 1, .Y, .H, .R 6, .Y, .Y, .Y, .Y, .Y] }

/-- math-comp `cf101`:
```
Config 31
  H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 8 H 1 Y 8 Y 6 Y 5 H 6 Y 3 Y Y 3 Y 1 Y
```
-/
def cf101 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8,
               .H, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .R 5, .H, .R 6, .Y, .R 3, .Y, .Y, .R 3,
               .Y, .R 1, .Y] }

/-- math-comp `cf102`:
```
Config 31
  H 11 H 1 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 6 H 1 H 1 Y 6 Y 3 Y 4 Y Y 3 Y 1 Y
```
-/
def cf102 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8,
               .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .R 3, .Y, .R 4, .Y, .Y, .R 3,
               .Y, .R 1, .Y] }

/-- math-comp `cf103`:
```
Config 33
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 7 H 7 Y 3 Y 4 Y Y Y Y
```
-/
def cf103 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H,
               .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 3, .Y, .R 4, .Y, .Y, .Y, .Y] }

/-- math-comp `cf104`:
```
Config* 31 33
  H 3 H 12 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 7 H 2 H 9 Y 8 Y 5 Y 4 Y 4 Y Y Y Y
```
-/
def cf104 : Config :=
  { cfsym := true, cfcontractRef := [31, 33],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10,
               .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 5, .Y, .R 4, .Y, .R 4, .Y, .Y, .Y,
               .Y] }

/-- math-comp `cf105`:
```
Config 6
  H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H 1 H 6 H 1 H 1 Y 1 Y 1 Y Y Y
```
-/
def cf105 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y,
               .R 5, .H, .R 1, .H, .R 6, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .Y, .Y] }

/-- math-comp `cf106`:
```
Config 33
  H 2 H 12 Y 3 H 11 Y 4 H 2 H 10 Y 3 H 9 Y 6 H 1 H 1 Y 1 Y Y 2 H 1 Y 1 Y 1 Y 1
  Y
```
-/
def cf106 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 3,
               .H, .R 9, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1,
               .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf107`:
```
Config 29
  H 11 H 1 Y 10 H 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 9 Y 2 H 8 Y Y Y 3 H 1 Y 1 Y 1 Y
  Y
```
-/
def cf107 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10,
               .H, .R 10, .Y, .R 8, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 3, .H, .R 1, .Y,
               .R 1, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf108`:
```
Config 23
  H 11 H 1 Y 8 H 10 H 1 Y 9 H 1 Y 8 H 9 Y 2 H 8 Y Y 5 H 1 H 1 Y H 5 Y Y Y 1 Y
```
-/
def cf108 : Config :=
  { cfsym := false, cfcontractRef := [23],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 8, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H,
               .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .Y,
               .R 1, .Y] }

/-- math-comp `cf109`:
```
Config 6
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 5 H 2 H 7 Y H 1 H 1 Y 1 Y 1 Y Y Y
```
-/
def cf109 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y,
               .R 5, .H, .R 2, .H, .R 7, .Y, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .Y, .Y] }

/-- math-comp `cf110`:
```
Config 32
  H 12 H 1 Y 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 8 Y 2 H 1 Y 5 Y Y 3 Y 1 Y
  1 Y
```
-/
def cf110 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9,
               .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 8, .Y, .R 2, .H, .R 1, .Y, .R 5, .Y,
               .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf111`:
```
Config 23
  H 8 H 1 Y 6 H 2 H 8 Y 6 H 1 Y 5 H 1 Y 4 Y Y 3 Y Y
```
-/
def cf111 : Config :=
  { cfsym := false, cfcontractRef := [23],
    cfprog := [.H, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 5, .H,
               .R 1, .Y, .R 4, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf112`:
```
Config* 23
  H 2 H 9 Y 7 H 1 Y 6 H 6 H 1 Y 6 Y 3 H 1 Y 4 Y 1 Y 2 Y
```
-/
def cf112 : Config :=
  { cfsym := true, cfcontractRef := [23],
    cfprog := [.H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 6, .H, .R 1, .Y, .R 6, .Y,
               .R 3, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf113`:
```
Config* 6
  H 8 H 1 Y 3 H 8 Y 5 H 1 Y 4 H 6 Y 3 H 5 H 5 Y 3 Y Y Y
```
-/
def cf113 : Config :=
  { cfsym := true, cfcontractRef := [6],
    cfprog := [.H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 6, .Y,
               .R 3, .H, .R 5, .H, .R 5, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf114`:
```
Config 25
  H 2 H 10 Y 3 H 9 Y 4 H 8 H 2 H 8 Y 3 H 7 H 7 Y Y Y Y 3 Y Y
```
-/
def cf114 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 8, .H, .R 2, .H, .R 8, .Y,
               .R 3, .H, .R 7, .H, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf115`:
```
Config 25
  H 2 H 10 Y 4 H 9 H 2 H 9 Y 3 H 8 H 8 Y Y Y 4 H 5 H 5 Y 3 Y Y Y
```
-/
def cf115 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .H,
               .R 8, .Y, .Y, .Y, .R 4, .H, .R 5, .H, .R 5, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf116`:
```
Config* 1 2 19 24
  H 9 H 1 Y 3 H 9 Y 4 H 7 H 1 Y 3 H 7 Y 2 Y 3 Y 4 Y 3 Y Y
```
-/
def cf116 : Config :=
  { cfsym := true, cfcontractRef := [1, 2, 19, 24],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 7, .H, .R 1, .Y, .R 3, .H,
               .R 7, .Y, .R 2, .Y, .R 3, .Y, .R 4, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf117`:
```
Config 14
  H 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 H 6 H 6 Y 1 H 1 Y 1 Y Y 2 Y
```
-/
def cf117 : Config :=
  { cfsym := false, cfcontractRef := [14],
    cfprog := [.H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 6, .H, .R 6, .H,
               .R 6, .Y, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf118`:
```
Config 23
  H 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 6 H 1 Y 4 Y Y 2 H 1 Y 1 Y Y
```
-/
def cf118 : Config :=
  { cfsym := false, cfcontractRef := [23],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 6, .H,
               .R 1, .Y, .R 4, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf119`:
```
Config 6
  H 9 H 1 Y 3 H 9 Y 4 H 2 H 8 Y 2 Y 4 H 6 Y 2 H 5 Y 3 Y Y Y
```
-/
def cf119 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 2, .H, .R 8, .Y, .R 2, .Y,
               .R 4, .H, .R 6, .Y, .R 2, .H, .R 5, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf120`:
```
Config* 6
  H 9 H 1 Y 3 H 9 Y 6 H 5 H 1 H 1 H 1 Y 2 Y 3 Y 1 Y 3 Y Y Y
```
-/
def cf120 : Config :=
  { cfsym := true, cfcontractRef := [6],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 6, .H, .R 5, .H, .R 1, .H, .R 1, .H,
               .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf121`:
```
Config 28
  H 3 H 9 H 1 Y 3 H 9 Y 3 H 8 Y 4 H 7 H 7 Y 3 Y 1 Y 3 Y 1 Y 2 Y
```
-/
def cf121 : Config :=
  { cfsym := false, cfcontractRef := [28],
    cfprog := [.H, .R 3, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 4, .H,
               .R 7, .H, .R 7, .Y, .R 3, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf122`:
```
Config 27
  H 3 H 10 H 10 Y 6 H 3 H 9 H 9 Y 7 H 1 Y 7 Y 5 Y Y Y 3 Y Y
```
-/
def cf122 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 7, .H,
               .R 1, .Y, .R 7, .Y, .R 5, .Y, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf123`:
```
Config 27
  H 2 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 1 H 1 Y 5 H 1 Y 5 Y 1 Y 2 Y 1 Y
```
-/
def cf123 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 1, .H,
               .R 1, .Y, .R 5, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf124`:
```
Config 12 13 28
  H 2 H 10 Y 3 H 9 Y 3 H 8 Y 4 H 6 H 1 Y 4 Y 5 H 5 Y Y 1 Y 2 Y
```
-/
def cf124 : Config :=
  { cfsym := false, cfcontractRef := [12, 13, 28],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 6, .H,
               .R 1, .Y, .R 4, .Y, .R 5, .H, .R 5, .Y, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf125`:
```
Config 26
  H 3 H 10 H 10 Y 8 H 1 Y 7 H 7 H 1 Y 7 Y 5 Y 5 H 5 Y 2 Y Y 2 Y
```
-/
def cf125 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 7, .H, .R 1, .Y,
               .R 7, .Y, .R 5, .Y, .R 5, .H, .R 5, .Y, .R 2, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf126`:
```
Config 13
  H 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 5 H 1 H 1 Y 5 Y Y Y 3 Y Y
```
-/
def cf126 : Config :=
  { cfsym := false, cfcontractRef := [13],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 5, .H,
               .R 1, .H, .R 1, .Y, .R 5, .Y, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf127`:
```
Config 31
  H 3 H 10 H 1 Y 3 H 3 H 9 H 1 Y 3 H 9 Y 2 H 1 Y 1 Y 1 Y 1 Y 3 Y Y Y
```
-/
def cf127 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 3, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 3, .H, .R 9, .H, .R 1, .Y, .R 3, .H,
               .R 9, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf128`:
```
Config 4 5 18 23
  H 2 H 11 Y 3 H 10 Y 5 H 2 H 9 Y 2 H 1 Y 1 Y 1 Y 3 H 5 H 5 Y 3 Y Y Y
```
-/
def cf128 : Config :=
  { cfsym := false, cfcontractRef := [4, 5, 18, 23],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 2, .H, .R 9, .Y, .R 2, .H,
               .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 5, .H, .R 5, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf129`:
```
Config 26
  H 2 H 11 Y 5 H 2 H 10 Y 3 H 9 Y 5 H 8 Y 3 H 7 H 7 Y Y Y Y 3 Y Y
```
-/
def cf129 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 5, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 5, .H,
               .R 8, .Y, .R 3, .H, .R 7, .H, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf130`:
```
Config 6
  H 9 H 1 Y 3 H 9 Y 3 H 8 Y 4 H 1 Y 6 H 1 Y 4 H 5 Y 1 H 1 Y 1 Y Y
```
-/
def cf130 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 1, .Y,
               .R 6, .H, .R 1, .Y, .R 4, .H, .R 5, .Y, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf131`:
```
Config 29
  H 2 H 11 Y 3 H 10 Y 4 H 9 H 2 H 9 Y 3 H 8 H 8 Y Y Y 3 H 5 Y 3 Y Y Y
```
-/
def cf131 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 2, .H, .R 9, .Y,
               .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 3, .H, .R 5, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf132`:
```
Config 32
  H 4 H 9 H 1 H 1 Y 3 H 10 Y 4 H 9 H 2 H 9 Y 2 H 8 Y Y Y 2 Y 3 Y Y Y
```
-/
def cf132 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 4, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 9, .H,
               .R 2, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 2, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf133`:
```
Config 34
  H 9 H 2 H 11 Y 9 H 1 Y 7 H 1 H 8 H 1 Y 2 H 8 Y Y 6 H 1 Y 5 Y 1 Y 3 Y Y
```
-/
def cf133 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H,
               .R 1, .Y, .R 2, .H, .R 8, .Y, .Y, .R 6, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y,
               .Y] }

/-- math-comp `cf134`:
```
Config 19
  H 2 H 10 Y 4 H 9 H 2 H 9 Y 8 H 1 Y 1 Y 2 H 6 Y 2 H 1 H 1 Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf134 : Config :=
  { cfsym := false, cfcontractRef := [19],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 2, .H, .R 9, .Y, .R 8, .H, .R 1, .Y,
               .R 1, .Y, .R 2, .H, .R 6, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3,
               .Y, .R 1, .Y] }

/-- math-comp `cf135`:
```
Config* 13
  H 8 H 1 H 1 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 2 Y 2 H 1 Y 4 Y 1 Y 2 Y
```
-/
def cf135 : Config :=
  { cfsym := true, cfcontractRef := [13],
    cfprog := [.H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H,
               .R 7, .Y, .R 2, .Y, .R 2, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf136`:
```
Config 14
  H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 H 6 Y 1 H 1 Y 1 Y Y 2 Y
```
-/
def cf136 : Config :=
  { cfsym := false, cfcontractRef := [14],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y,
               .R 6, .H, .R 6, .Y, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf137`:
```
Config 29
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 6 H 6 Y 2 Y 2 Y 2 Y 1 Y
```
-/
def cf137 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y,
               .R 6, .H, .R 1, .Y, .R 6, .H, .R 6, .Y, .R 2, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf138`:
```
Config 18 19 29
  H 10 H 1 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 3 H 8 Y 2 Y 3 Y 1 Y 3 Y Y Y
```
-/
def cf138 : Config :=
  { cfsym := false, cfcontractRef := [18, 19, 29],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y,
               .R 3, .H, .R 8, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf139`:
```
Config 7
  H 3 H 11 H 11 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 7 Y 5 Y Y 3 Y 2 Y 2 Y
```
-/
def cf139 : Config :=
  { cfsym := false, cfcontractRef := [7],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1,
               .Y, .R 7, .H, .R 1, .Y, .R 7, .Y, .R 5, .Y, .Y, .R 3, .Y, .R 2, .Y, .R 2, .Y] }

/-- math-comp `cf140`:
```
Config 12 13 29
  H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 4 Y 5 H 5 Y Y 1 Y 2 Y
```
-/
def cf140 : Config :=
  { cfsym := false, cfcontractRef := [12, 13, 29],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y,
               .R 3, .H, .R 7, .Y, .R 4, .Y, .R 5, .H, .R 5, .Y, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf141`:
```
Config* 29
  H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 2 H 8 Y 2 Y 3 Y 4 Y 4 H 4 Y 2 Y Y
```
-/
def cf141 : Config :=
  { cfsym := true, cfcontractRef := [29],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 2, .H,
               .R 8, .Y, .R 2, .Y, .R 3, .Y, .R 4, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf142`:
```
Config 29
  H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y 5 Y 2 Y 2 Y 2 Y 2 Y
```
-/
def cf142 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H,
               .R 1, .Y, .R 7, .H, .R 7, .Y, .R 5, .Y, .R 2, .Y, .R 2, .Y, .R 2, .Y, .R 2, .Y] }

/-- math-comp `cf143`:
```
Config 17 22 23 28
  H 9 H 1 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 2 Y 3 Y 5 Y 4 Y 3 Y 1 Y
```
-/
def cf143 : Config :=
  { cfsym := false, cfcontractRef := [17, 22, 23, 28],
    cfprog := [.H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y,
               .R 3, .H, .R 8, .Y, .R 2, .Y, .R 3, .Y, .R 5, .Y, .R 4, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf144`:
```
Config 14
  H 2 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 4 H 7 H 7 Y 3 Y 4 Y 1 Y 2 Y 1 Y
```
-/
def cf144 : Config :=
  { cfsym := false, cfcontractRef := [14],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y,
               .R 4, .H, .R 7, .H, .R 7, .Y, .R 3, .Y, .R 4, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf145`:
```
Config 5 19 27 29
  H 3 H 11 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 7 Y 5 Y Y Y 3 Y Y
```
-/
def cf145 : Config :=
  { cfsym := false, cfcontractRef := [5, 19, 27, 29],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y,
               .R 7, .H, .R 1, .Y, .R 7, .Y, .R 5, .Y, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf146`:
```
Config 26
  H 9 H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 7 H 7 Y Y 3 Y 1 Y 2 Y 1 Y
```
-/
def cf146 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y,
               .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf147`:
```
Config 30
  H 8 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 1 H 1 Y 6 Y Y Y 3 Y 1 Y Y
```
-/
def cf147 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y,
               .R 6, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf148`:
```
Config 13
  H 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 6 H 7 Y Y Y 2 H 1 Y 1 Y Y
```
-/
def cf148 : Config :=
  { cfsym := false, cfcontractRef := [13],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H,
               .R 1, .Y, .R 6, .H, .R 7, .Y, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf149`:
```
Config 29
  H 9 H 1 H 1 Y 3 H 10 Y 6 H 6 H 1 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 3 Y Y Y
```
-/
def cf149 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 6, .H, .R 6, .H, .R 1, .H,
               .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf150`:
```
Config 32
  H 10 H 1 Y 9 H 1 Y 8 H 8 H 1 Y 7 H 1 Y 7 H 7 Y 5 H 6 Y 3 Y Y Y 2 Y
```
-/
def cf150 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 1, .Y, .R 7, .H,
               .R 1, .Y, .R 7, .H, .R 7, .Y, .R 5, .H, .R 6, .Y, .R 3, .Y, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf151`:
```
Config 31
  H 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 7 H 7 H 7 Y Y Y Y 3 Y Y
```
-/
def cf151 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H,
               .R 1, .Y, .R 7, .H, .R 7, .H, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf152`:
```
Config 4 5 22 27
  H 2 H 12 Y 3 H 11 Y 4 H 2 H 10 Y 3 H 9 Y 2 H 1 Y 1 Y 1 Y 2 H 5 Y 3 Y Y Y
```
-/
def cf152 : Config :=
  { cfsym := false, cfcontractRef := [4, 5, 22, 27],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 3,
               .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 5, .Y, .R 3, .Y,
               .Y, .Y] }

/-- math-comp `cf153`:
```
Config 32
  H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 8 Y 6 Y 4 H 1 H 1 Y 4 Y Y 1 Y 1 Y
```
-/
def cf153 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H,
               .R 8, .Y, .R 6, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 4, .Y, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf154`:
```
Config 29
  H 9 H 2 H 11 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 1 Y 5 Y 1 Y 3 Y 1 Y Y 1 Y
```
-/
def cf154 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H,
               .R 9, .Y, .R 7, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf155`:
```
Config 26
  H 4 H 11 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 8 Y 5 Y 1 Y 4 H 5 Y Y 1 Y 1 Y
```
-/
def cf155 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1,
               .Y, .R 7, .H, .R 8, .Y, .R 5, .Y, .R 1, .Y, .R 4, .H, .R 5, .Y, .Y, .R 1, .Y, .R 1,
               .Y] }

/-- math-comp `cf156`:
```
Config 29
  H 4 H 11 H 11 H 11 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 8 Y 5 Y 1 Y 3 Y Y 1 Y 1 Y
```
-/
def cf156 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3,
               .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 1, .Y, .R 1,
               .Y] }

/-- math-comp `cf157`:
```
Config 6
  H 10 H 1 Y 3 H 10 Y 3 H 9 Y 5 H 1 Y 7 H 7 H 7 H 7 Y Y 1 Y 3 Y Y Y
```
-/
def cf157 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 5, .H, .R 1, .Y,
               .R 7, .H, .R 7, .H, .R 7, .H, .R 7, .Y, .Y, .R 1, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf158`:
```
Config 6
  H 10 H 1 Y 3 H 10 Y 3 H 9 Y 5 H 1 Y 5 H 7 Y 3 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y
```
-/
def cf158 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 5, .H, .R 1, .Y,
               .R 5, .H, .R 7, .Y, .R 3, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1,
               .Y] }

/-- math-comp `cf159`:
```
Config 1 2 32
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 5 H 3 H 8 H 8 Y 7 H 1 Y 1 Y Y 3 Y 1 Y 2 Y
```
-/
def cf159 : Config :=
  { cfsym := false, cfcontractRef := [1, 2, 32],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 3, .H,
               .R 8, .H, .R 8, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf160`:
```
Config 30
  H 2 H 12 Y 3 H 11 Y 3 H 2 H 10 Y 2 H 9 Y 3 H 8 H 8 Y Y Y 3 H 5 Y 3 Y Y Y
```
-/
def cf160 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 2,
               .H, .R 9, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 3, .H, .R 5, .Y, .R 3, .Y, .Y,
               .Y] }

/-- math-comp `cf161`:
```
Config 30
  H 2 H 12 Y 3 H 11 Y 4 H 2 H 10 Y 9 H 1 Y 3 H 8 H 8 Y Y Y 3 H 5 Y 3 Y Y Y
```
-/
def cf161 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 9,
               .H, .R 1, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 3, .H, .R 5, .Y, .R 3, .Y, .Y,
               .Y] }

/-- math-comp `cf162`:
```
Config 33
  H 4 H 10 H 1 H 1 Y 3 H 11 Y 3 H 2 H 10 Y 2 H 9 Y 2 H 8 Y Y Y 2 Y 3 Y Y Y
```
-/
def cf162 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 4, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 2, .H,
               .R 10, .Y, .R 2, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 2, .Y, .R 3, .Y, .Y,
               .Y] }

/-- math-comp `cf163`:
```
Config 33
  H 4 H 10 H 1 H 1 Y 3 H 11 Y 4 H 2 H 10 Y 9 H 1 Y 2 H 8 Y Y Y 2 Y 3 Y Y Y
```
-/
def cf163 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 4, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 2, .H,
               .R 10, .Y, .R 9, .H, .R 1, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 2, .Y, .R 3, .Y, .Y,
               .Y] }

/-- math-comp `cf164`:
```
Config 35
  H 3 H 11 H 1 Y 4 H 3 H 10 H 1 Y 3 H 10 Y 2 H 1 Y 3 H 8 Y Y 1 Y 1 Y 3 Y Y Y
```
-/
def cf164 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 1, .Y, .R 4, .H, .R 3, .H, .R 10, .H, .R 1, .Y, .R 3, .H,
               .R 10, .Y, .R 2, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y,
               .Y, .Y] }

/-- math-comp `cf165`:
```
Config 36
  H 11 H 1 Y 10 H 1 Y 8 H 9 H 1 Y 8 H 1 Y 8 H 8 Y 4 H 7 Y Y 1 Y 2 H 1 Y 3 Y 1 Y
```
-/
def cf165 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 8, .H,
               .R 1, .Y, .R 8, .H, .R 8, .Y, .R 4, .H, .R 7, .Y, .Y, .R 1, .Y, .R 2, .H, .R 1, .Y,
               .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf166`:
```
Config 11 12 18 19
  H 10 H 2 H 12 Y 8 H 10 H 1 Y 9 H 1 Y 1 Y 8 H 1 Y 1 Y 3 H 6 H 6 Y 5 Y 4 Y Y Y
```
-/
def cf166 : Config :=
  { cfsym := false, cfcontractRef := [11, 12, 18, 19],
    cfprog := [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 8, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 6, .H, .R 6, .Y, .R 5, .Y,
               .R 4, .Y, .Y, .Y] }

/-- math-comp `cf167`:
```
Config 33
  H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 1 H 8 H 1 Y 8 H 1 Y 1 Y 1 Y 5 Y 4 Y Y Y
```
-/
def cf167 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7,
               .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 5, .Y,
               .R 4, .Y, .Y, .Y] }

/-- math-comp `cf168`:
```
Config 35
  H 2 H 12 Y 3 H 2 H 11 Y 4 H 9 H 1 Y 4 H 1 Y 7 H 1 H 1 Y 1 Y 1 Y 4 Y 1 Y 3 Y Y
```
-/
def cf168 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y,
               .R 4, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 4, .Y, .R 1,
               .Y, .R 3, .Y, .Y] }

/-- math-comp `cf169`:
```
Config* 11 12 18 19
  H 10 H 2 H 12 Y 9 H 10 H 1 Y 9 H 1 Y 1 Y 7 H 1 H 1 Y 1 Y 2 H 6 Y 4 Y 1 Y 3 Y Y
```
-/
def cf169 : Config :=
  { cfsym := true, cfcontractRef := [11, 12, 18, 19],
    cfprog := [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 9, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 6, .Y, .R 4, .Y,
               .R 1, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf170`:
```
Config 38
  H 4 H 10 H 1 H 1 Y 3 H 11 Y 5 H 10 H 2 H 10 Y 2 H 9 Y Y 7 H 1 Y 2 Y 4 Y Y Y Y
```
-/
def cf170 : Config :=
  { cfsym := false, cfcontractRef := [38],
    cfprog := [.H, .R 4, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 10,
               .H, .R 2, .H, .R 10, .Y, .R 2, .H, .R 9, .Y, .Y, .R 7, .H, .R 1, .Y, .R 2, .Y, .R 4,
               .Y, .Y, .Y, .Y] }

/-- math-comp `cf171`:
```
Config 26
  H 2 H 12 Y 4 H 2 H 11 Y 4 H 10 H 2 H 10 Y 9 H 1 Y 1 Y 1 Y 4 H 6 H 6 Y 3 Y Y 3
  Y 1 Y
```
-/
def cf171 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 10, .H, .R 2,
               .H, .R 10, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 6, .H, .R 6, .Y,
               .R 3, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf172`:
```
Config 34
  H 2 H 12 Y 3 H 11 Y 4 H 10 H 2 H 10 Y 9 H 1 Y 1 Y 3 H 7 H 7 Y 3 H 6 Y Y 3 Y Y
  Y
```
-/
def cf172 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 10, .H, .R 2, .H, .R 10,
               .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 7, .H, .R 7, .Y, .R 3, .H, .R 6, .Y,
               .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf173`:
```
Config 36
  H 10 H 1 Y 9 H 9 H 1 Y 5 H 1 H 3 H 9 H 9 H 9 H 9 Y Y 1 Y Y Y 4 Y Y Y
```
-/
def cf173 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 3, .H,
               .R 9, .H, .R 9, .H, .R 9, .H, .R 9, .Y, .Y, .R 1, .Y, .Y, .Y, .R 4, .Y, .Y, .Y] }

/-- math-comp `cf174`:
```
Config 36
  H 10 H 1 Y 7 H 9 H 1 Y 9 H 9 H 1 H 1 Y 4 H 8 H 8 H 8 Y Y Y Y 4 Y Y Y
```
-/
def cf174 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 7, .H, .R 9, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .H,
               .R 1, .Y, .R 4, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .R 4, .Y, .Y, .Y] }

/-- math-comp `cf175`:
```
Config 20
  H 2 H 11 Y 3 H 2 H 10 Y 2 H 9 Y 8 H 1 Y 1 Y 2 H 6 Y 2 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf175 : Config :=
  { cfsym := false, cfcontractRef := [20],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 2, .H, .R 9, .Y, .R 8, .H,
               .R 1, .Y, .R 1, .Y, .R 2, .H, .R 6, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y,
               .Y, .R 1, .Y] }

/-- math-comp `cf176`:
```
Config 20
  H 2 H 11 Y 6 H 2 H 10 Y 3 H 1 Y 8 H 1 Y 1 Y 2 H 6 Y 2 H 1 H 1 Y 4 H 1 Y 3 Y 1
  Y
```
-/
def cf176 : Config :=
  { cfsym := false, cfcontractRef := [20],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 6, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 1, .Y, .R 8, .H,
               .R 1, .Y, .R 1, .Y, .R 2, .H, .R 6, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 1,
               .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf177`:
```
Config 26
  H 8 H 3 H 11 H 11 Y 9 H 9 H 1 Y 4 H 1 Y 7 H 1 Y 1 Y 1 Y 3 H 5 H 5 Y 3 Y Y Y
```
-/
def cf177 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 4, .H,
               .R 1, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 5, .H, .R 5, .Y, .R 3,
               .Y, .Y, .Y] }

/-- math-comp `cf178`:
```
Config 29
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 7 H 7 Y 6 Y 4 Y Y 1 Y Y
```
-/
def cf178 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H,
               .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 6, .Y, .R 4, .Y, .Y, .R 1, .Y,
               .Y] }

/-- math-comp `cf179`:
```
Config 32
  H 4 H 11 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 Y 6 H 6 Y 3 Y 3 Y Y 1 Y
```
-/
def cf179 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1,
               .Y, .R 7, .H, .R 1, .Y, .R 7, .Y, .R 6, .H, .R 6, .Y, .R 3, .Y, .R 3, .Y, .Y, .R 1,
               .Y] }

/-- math-comp `cf180`:
```
Config 7
  H 3 H 12 H 12 Y 9 H 2 H 11 Y 8 H 2 H 10 Y 8 H 1 Y 8 Y 6 Y Y 4 Y 2 Y 3 Y Y
```
-/
def cf180 : Config :=
  { cfsym := false, cfcontractRef := [7],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 8, .H, .R 2,
               .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .R 4, .Y, .R 2, .Y, .R 3,
               .Y, .Y] }

/-- math-comp `cf181`:
```
Config 7 29 32
  H 10 H 1 H 1 Y 4 H 10 H 1 Y 4 H 9 H 1 Y 3 H 9 Y 2 Y 3 Y 1 Y 4 Y 3 Y 2 Y Y
```
-/
def cf181 : Config :=
  { cfsym := false, cfcontractRef := [7, 29, 32],
    cfprog := [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 4, .H, .R 9, .H,
               .R 1, .Y, .R 3, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 4, .Y, .R 3, .Y, .R 2,
               .Y, .Y] }

/-- math-comp `cf182`:
```
Config 27
  H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y Y 3 Y 3 Y Y 2 Y
```
-/
def cf182 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8,
               .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .Y, .R 3, .Y, .R 3, .Y, .Y,
               .R 2, .Y] }

/-- math-comp `cf183`:
```
Config 16 32
  H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 4 Y 3 H 6 Y 2 Y 3 Y 3 Y Y
```
-/
def cf183 : Config :=
  { cfsym := false, cfcontractRef := [16, 32],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8,
               .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 4, .Y, .R 3, .H, .R 6, .Y, .R 2, .Y, .R 3, .Y,
               .R 3, .Y, .Y] }

/-- math-comp `cf184`:
```
Config 33
  H 10 H 1 H 1 Y 3 H 11 Y 3 H 2 H 10 Y 3 H 9 Y 2 Y 3 Y 6 Y 3 H 1 Y 4 Y 2 Y Y
```
-/
def cf184 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10,
               .Y, .R 3, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 6, .Y, .R 3, .H, .R 1, .Y, .R 4, .Y,
               .R 2, .Y, .Y] }

/-- math-comp `cf185`:
```
Config 8 31 33
  H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 4 H 8 H 8 Y 3 Y 4 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf185 : Config :=
  { cfsym := false, cfcontractRef := [8, 31, 33],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H,
               .R 9, .Y, .R 4, .H, .R 8, .H, .R 8, .Y, .R 3, .Y, .R 4, .Y, .R 1, .Y, .R 1, .Y, .R 2,
               .Y, .R 1, .Y] }

/-- math-comp `cf186`:
```
Config 14
  H 2 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 1 Y 6 H 6 Y Y 1 Y 2 Y 1 Y
```
-/
def cf186 : Config :=
  { cfsym := false, cfcontractRef := [14],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9,
               .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 1, .Y, .R 6, .H, .R 6, .Y, .Y, .R 1, .Y, .R 2,
               .Y, .R 1, .Y] }

/-- math-comp `cf187`:
```
Config 25 30 33
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 1 H 1 Y 6 Y Y Y 3 Y 1 Y Y
```
-/
def cf187 : Config :=
  { cfsym := false, cfcontractRef := [25, 30, 33],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H,
               .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf188`:
```
Config 32
  H 10 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 2 Y 3 Y 5 Y Y 3 Y 1 Y 1 Y
```
-/
def cf188 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 5,
               .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 5, .Y, .Y, .R 3, .Y, .R 1,
               .Y, .R 1, .Y] }

/-- math-comp `cf189`:
```
Config 33
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 7 H 7 Y 2 Y 2 Y 3 Y Y 2 Y
```
-/
def cf189 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y,
               .R 6, .H, .R 2, .H, .R 8, .Y, .R 7, .H, .R 7, .Y, .R 2, .Y, .R 2, .Y, .R 3, .Y, .Y,
               .R 2, .Y] }

/-- math-comp `cf190`:
```
Config 30
  H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 3 H 8 Y 2 H 1 Y 6 Y 5 Y 3 Y 1 Y 1 Y
```
-/
def cf190 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H,
               .R 9, .Y, .R 3, .H, .R 8, .Y, .R 2, .H, .R 1, .Y, .R 6, .Y, .R 5, .Y, .R 3, .Y, .R 1,
               .Y, .R 1, .Y] }

/-- math-comp `cf191`:
```
Config 31
  H 2 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 2 H 1 H 1 Y 5 Y 1 Y 2 Y 1 Y 1 Y
```
-/
def cf191 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9,
               .Y, .R 3, .H, .R 8, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 2, .Y,
               .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf192`:
```
Config 27
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y Y Y 3 Y 2 Y 2 Y
```
-/
def cf192 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H,
               .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .Y, .Y, .R 3, .Y, .R 2, .Y, .R 2,
               .Y] }

/-- math-comp `cf193`:
```
Config 18 21 30 33
  H 11 H 1 Y 4 H 10 H 1 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 2 Y 4 Y Y 4 Y 3 Y 2 Y Y
```
-/
def cf193 : Config :=
  { cfsym := false, cfcontractRef := [18, 21, 30, 33],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 5, .H, .R 8, .H, .R 1, .H,
               .R 1, .Y, .R 3, .H, .R 9, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 4, .Y, .R 3, .Y, .R 2, .Y,
               .Y] }

/-- math-comp `cf194`:
```
Config 6 10 19 33
  H 4 H 12 H 12 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 8 Y 5 Y 1 Y 3 Y 3 Y Y 2 Y
```
-/
def cf194 : Config :=
  { cfsym := false, cfcontractRef := [6, 10, 19, 33],
    cfprog := [.H, .R 4, .H, .R 12, .H, .R 12, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9,
               .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .R 3, .Y,
               .Y, .R 2, .Y] }

/-- math-comp `cf195`:
```
Config 18
  H 10 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 5 Y 1 Y 3 Y 1 Y Y 1 Y
```
-/
def cf195 : Config :=
  { cfsym := false, cfcontractRef := [18],
    cfprog := [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10,
               .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y,
               .Y, .R 1, .Y] }

/-- math-comp `cf196`:
```
Config 32
  H 4 H 12 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 8 Y 5 Y 1 Y 3 Y Y 1 Y 1 Y
```
-/
def cf196 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 4, .H, .R 12, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 1,
               .Y, .R 1, .Y] }

/-- math-comp `cf197`:
```
Config 24
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 4 H 2 H 9 Y 2 Y 6 H 7 H 7 Y Y 1 Y 3 Y Y Y
```
-/
def cf197 : Config :=
  { cfsym := false, cfcontractRef := [24],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 2,
               .H, .R 9, .Y, .R 2, .Y, .R 6, .H, .R 7, .H, .R 7, .Y, .Y, .R 1, .Y, .R 3, .Y, .Y,
               .Y] }

/-- math-comp `cf198`:
```
Config 33
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 4 H 2 H 9 Y 2 Y 5 H 7 Y 4 Y 3 Y 2 H 4 Y 2 Y Y
```
-/
def cf198 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 2,
               .H, .R 9, .Y, .R 2, .Y, .R 5, .H, .R 7, .Y, .R 4, .Y, .R 3, .Y, .R 2, .H, .R 4, .Y,
               .R 2, .Y, .Y] }

/-- math-comp `cf199`:
```
Config 21 24 30 33
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 6 H 6 H 1 H 1 H 1 Y 2 Y 4 Y 4 Y Y 3 Y 1 Y 1 Y
```
-/
def cf199 : Config :=
  { cfsym := false, cfcontractRef := [21, 24, 30, 33],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 6, .H, .R 6,
               .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 4, .Y, .R 4, .Y, .Y, .R 3, .Y, .R 1,
               .Y, .R 1, .Y] }

/-- math-comp `cf200`:
```
Config 23
  H 3 H 12 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 1 Y 8 Y 5 Y 1 Y Y Y 3 Y Y
```
-/
def cf200 : Config :=
  { cfsym := false, cfcontractRef := [23],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10,
               .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 5, .Y, .R 1, .Y, .Y, .Y, .R 3, .Y,
               .Y] }

/-- math-comp `cf201`:
```
Config 1 2 32
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 1 Y 5 Y 4 Y 1 Y 3 Y 2 Y 1 Y
```
-/
def cf201 : Config :=
  { cfsym := false, cfcontractRef := [1, 2, 32],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H,
               .R 9, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 5, .Y, .R 4, .Y, .R 1, .Y, .R 3, .Y, .R 2,
               .Y, .R 1, .Y] }

/-- math-comp `cf202`:
```
Config 10
  H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H 1 H 2 H 6 Y H 1 Y 3 Y 1 Y 1 Y
```
-/
def cf202 : Config :=
  { cfsym := false, cfcontractRef := [10],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y,
               .R 5, .H, .R 1, .H, .R 2, .H, .R 6, .Y, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf203`:
```
Config 12 13 19 20
  H 2 H 13 Y 3 H 12 Y 3 H 2 H 11 Y 3 H 10 Y Y 3 H 8 H 8 Y Y Y 3 H 5 Y 3 Y Y Y
```
-/
def cf203 : Config :=
  { cfsym := false, cfcontractRef := [12, 13, 19, 20],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 2, .H, .R 11, .Y, .R 3,
               .H, .R 10, .Y, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 3, .H, .R 5, .Y, .R 3,
               .Y, .Y, .Y] }

/-- math-comp `cf204`:
```
Config 36
  H 11 H 1 Y 9 H 2 H 11 Y 7 H 3 H 10 H 10 Y 7 H 1 H 1 Y 7 Y 6 Y 5 Y 1 Y 3 Y Y 2
  Y
```
-/
def cf204 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 7, .H, .R 3, .H, .R 10,
               .H, .R 10, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .R 6, .Y, .R 5, .Y, .R 1, .Y,
               .R 3, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf205`:
```
Config 35
  H 3 H 12 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 9 H 9 Y 7 Y 7 Y 6 H 6 Y Y 3 Y 2 Y 1 Y
```
-/
def cf205 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1,
               .Y, .R 8, .H, .R 9, .H, .R 9, .Y, .R 7, .Y, .R 7, .Y, .R 6, .H, .R 6, .Y, .Y, .R 3,
               .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf206`:
```
Config 36
  H 11 H 1 Y 10 H 1 Y 8 H 9 H 1 Y 7 H 1 H 1 Y 7 Y 5 H 1 H 1 Y 4 Y 1 Y Y 1 Y 1 Y
```
-/
def cf206 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 7, .H,
               .R 1, .H, .R 1, .Y, .R 7, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .Y,
               .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf207`:
```
Config 18 19 25 26
  H 11 H 2 H 13 Y 10 H 2 H 12 Y 10 H 10 H 1 Y 9 H 1 Y 1 Y 8 H 1 Y 1 Y 1 Y 5 Y 4
  Y Y Y
```
-/
def cf207 : Config :=
  { cfsym := false, cfcontractRef := [18, 19, 25, 26],
    cfprog := [.H, .R 11, .H, .R 2, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 10,
               .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y,
               .R 5, .Y, .R 4, .Y, .Y, .Y] }

/-- math-comp `cf208`:
```
Config 35
  H 4 H 12 H 12 H 12 Y 10 H 10 H 1 Y 8 H 2 H 10 Y 9 Y 5 H 1 Y 1 Y 6 Y 4 Y 3 Y 2
  Y 1 Y
```
-/
def cf208 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 4, .H, .R 12, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 8,
               .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .R 6, .Y, .R 4, .Y,
               .R 3, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf209`:
```
Config 26
  H 4 H 12 H 12 H 12 Y 10 H 1 Y 8 H 9 H 1 Y 9 Y 6 Y 1 Y 6 H 6 H 6 Y Y Y 1 Y 1 Y
```
-/
def cf209 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 4, .H, .R 12, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9,
               .H, .R 1, .Y, .R 9, .Y, .R 6, .Y, .R 1, .Y, .R 6, .H, .R 6, .H, .R 6, .Y, .Y, .Y,
               .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf210`:
```
Config 35
  H 11 H 1 Y 8 H 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 8 H 8 H 8 Y Y 1 Y 4 Y Y Y Y
```
-/
def cf210 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 8, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H,
               .R 1, .Y, .R 6, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .Y, .R 1, .Y, .R 4, .Y, .Y, .Y,
               .Y] }

/-- math-comp `cf211`:
```
Config 31
  H 11 H 1 Y 8 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 5 Y 2 H 7 Y Y Y 2 H 1 Y 1 Y Y
```
-/
def cf211 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1,
               .Y, .R 8, .H, .R 1, .Y, .R 5, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .R 2, .H, .R 1, .Y,
               .R 1, .Y, .Y] }

/-- math-comp `cf212`:
```
Config 35
  H 5 H 9 H 1 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 2 H 1 Y 1 Y Y 3 Y 1 Y 1 Y 2 Y
```
-/
def cf212 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H,
               .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y,
               .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf213`:
```
Config 34
  H 2 H 13 Y 3 H 12 Y 3 H 2 H 11 Y 3 H 10 Y 9 H 1 Y 3 H 8 H 8 Y Y Y 3 H 5 Y 3 Y
  Y Y
```
-/
def cf213 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 2, .H, .R 11, .Y, .R 3,
               .H, .R 10, .Y, .R 9, .H, .R 1, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .R 3, .H,
               .R 5, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf214`:
```
Config 37
  H 11 H 1 Y 10 H 1 Y 8 H 9 H 1 Y 9 H 9 H 1 H 1 Y 3 H 8 H 8 Y Y Y Y 4 Y Y Y
```
-/
def cf214 : Config :=
  { cfsym := false, cfcontractRef := [37],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 9, .H,
               .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .R 4, .Y, .Y,
               .Y] }

/-- math-comp `cf215`:
```
Config 27
  H 2 H 13 Y 4 H 2 H 12 Y 3 H 2 H 11 Y 2 H 10 Y 9 H 1 Y 1 Y 1 Y 4 H 1 Y 5 H 1 Y
  4 Y Y 1 Y
```
-/
def cf215 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 4, .H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 2, .H, .R 11,
               .Y, .R 2, .H, .R 10, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 1, .Y,
               .R 5, .H, .R 1, .Y, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf216`:
```
Config 8 9 15 16
  H 2 H 13 Y 3 H 2 H 12 Y 3 H 11 Y Y 4 H 9 H 9 H 9 Y Y Y 5 H 6 H 6 Y Y 3 Y Y Y
```
-/
def cf216 : Config :=
  { cfsym := false, cfcontractRef := [8, 9, 15, 16],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .Y,
               .R 4, .H, .R 9, .H, .R 9, .H, .R 9, .Y, .Y, .Y, .R 5, .H, .R 6, .H, .R 6, .Y, .Y,
               .R 3, .Y, .Y, .Y] }

/-- math-comp `cf217`:
```
Config 8 9 15 16
  H 12 H 1 Y 10 H 11 H 1 Y 10 H 1 Y 1 Y 7 H 1 H 1 H 1 Y 1 Y 2 H 7 Y 4 H 1 Y 1 Y
  4 Y Y Y
```
-/
def cf217 : Config :=
  { cfsym := false, cfcontractRef := [8, 9, 15, 16],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 10, .H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 1,
               .Y, .R 7, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 7, .Y, .R 4, .H,
               .R 1, .Y, .R 1, .Y, .R 4, .Y, .Y, .Y] }

/-- math-comp `cf218`:
```
Config 33
  H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 Y 1 Y 5 H 5 Y Y Y 1 Y
```
-/
def cf218 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8,
               .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .R 5, .H, .R 5, .Y, .Y, .Y,
               .R 1, .Y] }

/-- math-comp `cf219`:
```
Config 28
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y 3 Y 4 Y Y Y 2 Y
```
-/
def cf219 : Config :=
  { cfsym := false, cfcontractRef := [28],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 3, .Y, .R 4, .Y,
               .Y, .Y, .R 2, .Y] }

/-- math-comp `cf220`:
```
Config 36
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 5 H 3 H 8 H 8 Y 1 H 1 Y 5 Y 3 Y 1 Y Y 2 Y
```
-/
def cf220 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y,
               .R 5, .H, .R 3, .H, .R 8, .H, .R 8, .Y, .R 1, .H, .R 1, .Y, .R 5, .Y, .R 3, .Y, .R 1,
               .Y, .Y, .R 2, .Y] }

/-- math-comp `cf221`:
```
Config 31
  H 3 H 12 H 1 Y 3 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 2 H 1 Y 1 Y 5 Y 3 Y 1 Y
  2 Y Y
```
-/
def cf221 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1,
               .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 5, .Y,
               .R 3, .Y, .R 1, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf222`:
```
Config 34
  H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 4 H 9 H 9 Y 3 Y 6 Y Y Y 3 Y 1 Y 1
  Y
```
-/
def cf222 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y,
               .R 3, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 9, .Y, .R 3, .Y, .R 6, .Y, .Y, .Y, .R 3,
               .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf223`:
```
Config 37
  H 12 H 1 Y 11 H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 Y 2 Y 5 H 6 Y 2 Y 4 Y
  1 Y 2 Y
```
-/
def cf223 : Config :=
  { cfsym := false, cfcontractRef := [37],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9,
               .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .R 2, .Y, .R 5, .H, .R 6, .Y,
               .R 2, .Y, .R 4, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf224`:
```
Config 36
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 8 H 8 Y 3 H 7 Y 2 Y 4 Y Y 3 Y
  Y
```
-/
def cf224 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 8, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .R 2, .Y,
               .R 4, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf225`:
```
Config 35
  H 2 H 13 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 6 H 1 Y 6 Y 1 Y 2 Y
  1 Y 1 Y
```
-/
def cf225 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10,
               .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .H, .R 6, .H, .R 1, .Y, .R 6, .Y,
               .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf226`:
```
Config 35 37
  H 12 H 1 Y 10 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 8 H 8 Y 6 Y 5 Y 4 Y Y 2
  Y 1 Y
```
-/
def cf226 : Config :=
  { cfsym := false, cfcontractRef := [35, 37],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8,
               .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .R 6, .Y, .R 5, .Y,
               .R 4, .Y, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf227`:
```
Config 30
  H 12 H 1 Y 10 H 2 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 8 H 8 Y Y Y 4 Y 2 Y 3 Y
  Y
```
-/
def cf227 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11,
               .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .Y, .Y, .R 4, .Y,
               .R 2, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf228`:
```
Config 35
  H 11 H 2 H 13 Y 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y 7 Y 4 Y 4 Y 3 Y
  Y 1 Y
```
-/
def cf228 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 11, .H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11,
               .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .R 7, .Y, .R 4, .Y,
               .R 4, .Y, .R 3, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf229`:
```
Config 36
  H 3 H 13 H 13 Y 10 H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 9 Y 7 Y 3 Y 4 Y 3 Y 1
  Y 2 Y Y
```
-/
def cf229 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1,
               .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .R 3, .Y, .R 4, .Y,
               .R 3, .Y, .R 1, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf230`:
```
Config 7
  H 4 H 13 H 13 H 13 Y 10 H 2 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 9 Y 6 Y 1 Y 4 Y 3 Y Y
  3 Y Y
```
-/
def cf230 : Config :=
  { cfsym := false, cfcontractRef := [7],
    cfprog := [.H, .R 4, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 9,
               .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 6, .Y, .R 1, .Y, .R 4, .Y,
               .R 3, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf231`:
```
Config 19
  H 10 H 1 H 1 H 1 Y 4 H 11 H 1 Y 4 H 10 H 1 Y 3 H 10 Y 2 Y 4 Y Y 5 Y 3 Y 1 Y 2
  Y Y
```
-/
def cf231 : Config :=
  { cfsym := false, cfcontractRef := [19],
    cfprog := [.H, .R 10, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 11, .H, .R 1, .Y, .R 4, .H,
               .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 5, .Y, .R 3, .Y,
               .R 1, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf232`:
```
Config 11 33 37
  H 2 H 13 Y 5 H 10 H 1 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 6 Y 1 Y 1 Y 3 Y 1 Y Y
  1 Y
```
-/
def cf232 : Config :=
  { cfsym := false, cfcontractRef := [11, 33, 37],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 5, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11,
               .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y,
               .R 3, .Y, .R 1, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf233`:
```
Config 35
  H 3 H 13 H 13 Y 11 H 1 Y 9 H 2 H 11 Y 8 H 2 H 10 Y 9 H 9 Y 6 Y 5 Y Y 4 Y Y Y 2
  Y
```
-/
def cf233 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11,
               .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .H, .R 9, .Y, .R 6, .Y, .R 5, .Y, .Y, .R 4,
               .Y, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf234`:
```
Config 6
  H 2 H 13 Y 10 H 2 H 12 Y 7 H 4 H 11 H 11 H 11 Y 9 H 1 Y 9 Y 6 Y Y 5 Y 3 Y Y 3
  Y Y
```
-/
def cf234 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 7, .H, .R 4, .H, .R 11,
               .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 6, .Y, .Y, .R 5, .Y, .R 3,
               .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf235`:
```
Config 32
  H 12 H 1 Y 9 H 11 H 1 Y 10 H 1 Y 9 H 1 Y 9 Y 7 H 1 Y 7 H 1 Y 6 H 6 Y Y Y 1 Y 1
  Y
```
-/
def cf235 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 9, .H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9,
               .H, .R 1, .Y, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 6, .Y,
               .Y, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf236`:
```
Config 10
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H 1 H 6 H 1 H 1 Y 1 Y 1 Y Y Y
```
-/
def cf236 : Config :=
  { cfsym := false, cfcontractRef := [10],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y,
               .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 6, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1,
               .Y, .Y, .Y] }

/-- math-comp `cf237`:
```
Config 36
  H 12 H 1 Y 11 H 9 H 3 H 12 H 12 Y 10 H 1 Y 8 H 1 H 1 Y 8 Y 8 H 8 Y Y 5 Y 4 Y Y
  3 Y Y
```
-/
def cf237 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10,
               .H, .R 1, .Y, .R 8, .H, .R 1, .H, .R 1, .Y, .R 8, .Y, .R 8, .H, .R 8, .Y, .Y, .R 5,
               .Y, .R 4, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf238`:
```
Config 43
  H 12 H 1 Y 11 H 11 H 1 Y 7 H 4 H 11 H 11 H 11 Y 9 H 10 Y 2 H 9 Y Y Y 3 H 1 Y 1
  Y 1 Y 1 Y 2 Y
```
-/
def cf238 : Config :=
  { cfsym := false, cfcontractRef := [43],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 11, .H, .R 1, .Y, .R 7, .H, .R 4, .H, .R 11,
               .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 10, .Y, .R 2, .H, .R 9, .Y, .Y, .Y, .R 3, .H,
               .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf239`:
```
Config 36
  H 4 H 11 H 1 H 1 Y 3 H 2 H 12 Y 4 H 10 H 1 Y 5 H 1 Y 7 H 1 H 1 Y 1 Y 1 Y 1 Y 4
  Y Y Y Y
```
-/
def cf239 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 4, .H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 2, .H, .R 12, .Y, .R 4, .H,
               .R 10, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 1, .Y,
               .R 1, .Y, .R 1, .Y, .R 4, .Y, .Y, .Y, .Y] }

/-- math-comp `cf240`:
```
Config 38
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 H 8 H 8 Y 2 H 1 Y 5 Y Y 3 Y
  1 Y Y
```
-/
def cf240 : Config :=
  { cfsym := false, cfcontractRef := [38],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .R 2, .H, .R 1, .Y,
               .R 5, .Y, .Y, .R 3, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf241`:
```
Config 37
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 1 H 1 H 8 H 8 Y Y Y 2 H 1 Y 1
  Y 1 Y Y
```
-/
def cf241 : Config :=
  { cfsym := false, cfcontractRef := [37],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .H, .R 8, .H, .R 8, .Y, .Y, .Y,
               .R 2, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf242`:
```
Config 14
  H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 5 H 1 H 1 Y H 5 Y 4 Y 1 Y 1 Y
```
-/
def cf242 : Config :=
  { cfsym := false, cfcontractRef := [14],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y,
               .R 5, .H, .R 1, .H, .R 1, .Y, .H, .R 5, .Y, .R 4, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf243`:
```
Config 32
  H 3 H 11 H 11 Y 7 H 3 H 10 H 10 Y 7 H 2 H 9 Y 8 Y 6 Y Y 2 Y 3 Y Y 2 Y
```
-/
def cf243 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 7,
               .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .R 2, .Y, .R 3, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf244`:
```
Config 32
  H 3 H 11 H 11 Y 7 H 3 H 10 H 10 Y 7 H 2 H 9 Y 8 Y 6 Y Y Y 3 Y 1 Y 2 Y
```
-/
def cf244 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 7,
               .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf245`:
```
Config 30
  H 10 H 1 Y 9 H 1 Y 8 H 8 H 1 Y 6 H 1 H 1 Y 6 Y 5 H 1 Y 1 Y Y 3 Y Y
```
-/
def cf245 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 1, .Y, .R 6, .H,
               .R 1, .H, .R 1, .Y, .R 6, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf246`:
```
Config 1 2 30
  H 2 H 11 Y 8 H 2 H 10 Y 8 H 7 H 2 H 9 Y 8 Y 4 H 1 Y 1 Y Y 3 Y 1 Y 2 Y
```
-/
def cf246 : Config :=
  { cfsym := false, cfcontractRef := [1, 2, 30],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 7, .H, .R 2, .H,
               .R 9, .Y, .R 8, .Y, .R 4, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf247`:
```
Config 6
  H 10 H 1 Y 4 H 9 H 1 Y 3 H 9 Y 4 H 1 Y 4 Y Y 3 H 1 Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf247 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H,
               .R 1, .Y, .R 4, .Y, .Y, .R 3, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf248`:
```
Config* 31
  H 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 5 H 1 H 1 H 1 Y 5 Y 1 Y Y Y 3 Y Y
```
-/
def cf248 : Config :=
  { cfsym := true, cfcontractRef := [31],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 5, .H,
               .R 1, .H, .R 1, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf249`:
```
Config 26
  H 2 H 12 Y 3 H 11 Y 6 H 2 H 10 Y 2 H 1 Y 3 H 8 Y Y 1 Y 3 H 5 H 5 Y 3 Y Y Y
```
-/
def cf249 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 6, .H, .R 2, .H, .R 10, .Y, .R 2,
               .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .Y, .R 1, .Y, .R 3, .H, .R 5, .H, .R 5, .Y, .R 3,
               .Y, .Y, .Y] }

/-- math-comp `cf250`:
```
Config 20
  H 8 H 1 H 1 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 2 Y 4 Y 5 H 1 Y 1 Y Y 2 Y
```
-/
def cf250 : Config :=
  { cfsym := false, cfcontractRef := [20],
    cfprog := [.H, .R 8, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y,
               .R 3, .H, .R 8, .Y, .R 2, .Y, .R 4, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf251`:
```
Config 18
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 Y 3 Y 3 H 1 Y H 4 Y Y 1 Y
```
-/
def cf251 : Config :=
  { cfsym := false, cfcontractRef := [18],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y,
               .R 6, .H, .R 1, .Y, .R 3, .Y, .R 3, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf252`:
```
Config 18
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 H 7 Y 3 Y Y 3 Y 1 Y 1 Y
```
-/
def cf252 : Config :=
  { cfsym := false, cfcontractRef := [18],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y,
               .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .H, .R 7, .Y, .R 3, .Y, .Y, .R 3, .Y, .R 1, .Y,
               .R 1, .Y] }

/-- math-comp `cf253`:
```
Config 33
  H 3 H 12 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 8 Y 6 Y Y 5 Y 4 Y Y Y
```
-/
def cf253 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1,
               .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .R 5, .Y, .R 4, .Y, .Y,
               .Y] }

/-- math-comp `cf254`:
```
Config 11 12 33
  H 3 H 12 H 12 Y 8 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 8 Y 6 Y Y Y 3 Y 1 Y 2 Y
```
-/
def cf254 : Config :=
  { cfsym := false, cfcontractRef := [11, 12, 33],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9,
               .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y,
               .R 2, .Y] }

/-- math-comp `cf255`:
```
Config 33
  H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y Y 2 Y 3 Y 3 Y Y
```
-/
def cf255 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8,
               .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .Y, .R 2, .Y, .R 3, .Y, .R 3,
               .Y, .Y] }

/-- math-comp `cf256`:
```
Config 31
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y Y Y 2 Y 2 Y 2 Y
```
-/
def cf256 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H,
               .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y, .R 2,
               .Y] }

/-- math-comp `cf257`:
```
Config 33
  H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 1 H 1 Y 6 Y 3 Y Y 3 Y 1 Y 1 Y
```
-/
def cf257 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8,
               .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .R 3, .Y, .Y, .R 3, .Y, .R 1,
               .Y, .R 1, .Y] }

/-- math-comp `cf258`:
```
Config 24
  H 3 H 11 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 7 Y 5 Y 5 H 5 Y 2 Y Y 2 Y
```
-/
def cf258 : Config :=
  { cfsym := false, cfcontractRef := [24],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y,
               .R 7, .H, .R 1, .Y, .R 7, .Y, .R 5, .Y, .R 5, .H, .R 5, .Y, .R 2, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf259`:
```
Config 4 5 22 29
  H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 4 H 8 H 8 Y 3 Y 5 Y 1 Y 3 Y Y 1 Y
```
-/
def cf259 : Config :=
  { cfsym := false, cfcontractRef := [4, 5, 22, 29],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H,
               .R 9, .Y, .R 4, .H, .R 8, .H, .R 8, .Y, .R 3, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .Y,
               .R 1, .Y] }

/-- math-comp `cf260`:
```
Config 31
  H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 8 H 1 Y 8 Y 6 Y 5 H 1 Y 1 Y Y 3 Y Y
```
-/
def cf260 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8,
               .H, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3,
               .Y, .Y] }

/-- math-comp `cf261`:
```
Config 15 16 33
  H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 4 Y 1 Y 2 H 1 Y 1 Y Y Y
```
-/
def cf261 : Config :=
  { cfsym := false, cfcontractRef := [15, 16, 33],
    cfprog := [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8,
               .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y,
               .Y, .Y] }

/-- math-comp `cf262`:
```
Config 33
  H 11 H 1 Y 4 H 10 H 1 Y 3 H 10 Y 3 H 2 H 9 Y 2 Y 4 Y Y 4 Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf262 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3,
               .H, .R 2, .H, .R 9, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 4, .Y, .R 4, .H, .R 1, .Y, .R 3,
               .Y, .R 1, .Y] }

/-- math-comp `cf263`:
```
Config 21 26 33
  H 11 H 1 Y 4 H 10 H 1 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 2 Y 4 Y Y 4 Y Y 3 Y 1 Y
```
-/
def cf263 : Config :=
  { cfsym := false, cfcontractRef := [21, 26, 33],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5,
               .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 4, .Y, .Y, .R 3, .Y,
               .R 1, .Y] }

/-- math-comp `cf264`:
```
Config* 5 30
  H 2 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 5 H 8 H 8 H 8 Y 4 Y Y 4 Y 1 Y 2 Y 1 Y
```
-/
def cf264 : Config :=
  { cfsym := true, cfcontractRef := [5, 30],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9,
               .Y, .R 5, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .R 4, .Y, .Y, .R 4, .Y, .R 1, .Y, .R 2,
               .Y, .R 1, .Y] }

/-- math-comp `cf265`:
```
Config 14 29 31
  H 4 H 12 H 12 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 8 Y 5 Y 1 Y Y Y 3 Y Y
```
-/
def cf265 : Config :=
  { cfsym := false, cfcontractRef := [14, 29, 31],
    cfprog := [.H, .R 4, .H, .R 12, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2,
               .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 5, .Y, .R 1, .Y, .Y, .Y, .R 3, .Y,
               .Y] }

/-- math-comp `cf266`:
```
Config 1 2 32
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 4 H 1 Y 4 Y 3 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y
```
-/
def cf266 : Config :=
  { cfsym := false, cfcontractRef := [1, 2, 32],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9,
               .Y, .R 4, .H, .R 1, .Y, .R 4, .Y, .R 3, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 3, .Y,
               .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf267`:
```
Config 35
  H 9 H 3 H 12 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y Y Y 3 Y 1 Y 1 Y 2 Y
```
-/
def cf267 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9,
               .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y,
               .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf268`:
```
Config 32
  H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 1 Y 1 Y 1 Y 5 H 5 Y 2 Y Y 2 Y
```
-/
def cf268 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y,
               .R 3, .H, .R 9, .Y, .R 3, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 5, .H, .R 5, .Y, .R 2,
               .Y, .Y, .R 2, .Y] }

/-- math-comp `cf269`:
```
Config 33
  H 10 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 5 H 1 Y 3 Y 5 H 7 H 7 H 7 Y Y 1 Y 3 Y Y Y
```
-/
def cf269 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 5,
               .H, .R 1, .Y, .R 3, .Y, .R 5, .H, .R 7, .H, .R 7, .H, .R 7, .Y, .Y, .R 1, .Y, .R 3,
               .Y, .Y, .Y] }

/-- math-comp `cf270`:
```
Config 33
  H 12 H 1 Y 11 H 1 Y 9 H 10 H 1 Y 9 H 1 Y 9 H 9 H 9 Y 7 H 1 Y 1 Y Y Y 4 Y Y Y
```
-/
def cf270 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 10, .H, .R 1, .Y, .R 9,
               .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .Y, .Y,
               .R 4, .Y, .Y, .Y] }

/-- math-comp `cf271`:
```
Config 18 19 33
  H 3 H 11 H 1 Y 3 H 11 Y 3 H 3 H 9 H 1 Y 3 H 9 Y 6 H 1 Y 1 Y Y 3 Y 1 Y 1 Y 2 Y
```
-/
def cf271 : Config :=
  { cfsym := false, cfcontractRef := [18, 19, 33],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 3, .H, .R 9, .H,
               .R 1, .Y, .R 3, .H, .R 9, .Y, .R 6, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y,
               .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf272`:
```
Config 31
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 8 Y 2 H 7 Y Y Y 2 H 1 Y 1 Y Y
```
-/
def cf272 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H,
               .R 1, .Y, .R 6, .H, .R 8, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1,
               .Y, .Y] }

/-- math-comp `cf273`:
```
Config 8
  H 9 H 1 H 1 H 1 Y 3 H 11 Y 6 H 7 H 1 H 1 H 1 Y 2 Y 4 Y Y 1 Y 1 Y 3 Y Y Y
```
-/
def cf273 : Config :=
  { cfsym := false, cfcontractRef := [8],
    cfprog := [.H, .R 9, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 6, .H, .R 7, .H,
               .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y,
               .Y, .Y] }

/-- math-comp `cf274`:
```
Config 36
  H 2 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 4 H 1 Y 6 H 1 H 1 Y 1 Y 1 Y 3 Y 1 Y 2
  Y
```
-/
def cf274 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3,
               .H, .R 9, .Y, .R 4, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y,
               .R 3, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf275`:
```
Config 26
  H 11 H 1 Y 8 H 10 H 1 Y 8 H 2 H 10 Y 9 Y 5 H 8 Y Y Y 3 H 1 Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf275 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 8, .H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10,
               .Y, .R 9, .Y, .R 5, .H, .R 8, .Y, .Y, .Y, .R 3, .H, .R 1, .Y, .R 4, .H, .R 1, .Y,
               .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf276`:
```
Config 6
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 6 H 1 Y 5 H 8 Y 4 H 7 H 7 H 7 Y Y 1 Y 3 Y Y Y
```
-/
def cf276 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 6, .H, .R 1,
               .Y, .R 5, .H, .R 8, .Y, .R 4, .H, .R 7, .H, .R 7, .H, .R 7, .Y, .Y, .R 1, .Y, .R 3,
               .Y, .Y, .Y] }

/-- math-comp `cf277`:
```
Config 36
  H 12 H 1 Y 11 H 1 Y 10 H 10 H 1 Y 7 H 3 H 10 H 10 H 9 H 1 Y 8 Y 1 Y 1 Y Y Y 4
  Y Y Y
```
-/
def cf277 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 7,
               .H, .R 3, .H, .R 10, .H, .R 10, .H, .R 9, .H, .R 1, .Y, .R 8, .Y, .R 1, .Y, .R 1, .Y,
               .Y, .Y, .R 4, .Y, .Y, .Y] }

/-- math-comp `cf278`:
```
Config 30
  H 2 H 13 Y 3 H 12 Y 5 H 2 H 11 Y 3 H 10 H 2 H 10 Y 3 Y Y Y 1 Y 3 H 5 H 5 Y 3 Y
  Y Y
```
-/
def cf278 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 2, .H, .R 11, .Y, .R 3,
               .H, .R 10, .H, .R 2, .H, .R 10, .Y, .R 3, .Y, .Y, .Y, .R 1, .Y, .R 3, .H, .R 5, .H,
               .R 5, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf279`:
```
Config 40
  H 4 H 11 H 1 H 1 Y 3 H 12 Y 3 H 2 H 11 Y 2 H 10 Y 9 H 1 Y 1 Y 2 H 7 Y 2 Y Y 3
  Y Y 2 Y
```
-/
def cf279 : Config :=
  { cfsym := false, cfcontractRef := [40],
    cfprog := [.H, .R 4, .H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 2, .H,
               .R 11, .Y, .R 2, .H, .R 10, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 7, .Y,
               .R 2, .Y, .Y, .R 3, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf280`:
```
Config 39
  H 2 H 13 Y 3 H 2 H 12 Y 4 H 10 H 1 Y 5 H 1 Y 9 H 1 Y 7 H 1 H 1 Y 1 Y 1 Y 4 Y 1
  Y 3 Y Y
```
-/
def cf280 : Config :=
  { cfsym := false, cfcontractRef := [39],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1,
               .Y, .R 5, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 1, .Y,
               .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf281`:
```
Config 27 30 33
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y 6 Y 4 Y Y 3 Y 1
  Y
```
-/
def cf281 : Config :=
  { cfsym := false, cfcontractRef := [27, 30, 33],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 6, .Y, .R 4, .Y,
               .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf282`:
```
Config 21
  H 2 H 13 Y 4 H 11 H 1 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 2 H 8 Y 2 H 7 Y 5 Y 5 Y Y 3
  Y 1 Y
```
-/
def cf282 : Config :=
  { cfsym := false, cfcontractRef := [21],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 4, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3,
               .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .R 2, .H, .R 7, .Y, .R 5, .Y,
               .R 5, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf283`:
```
Config 7
  H 3 H 13 H 13 Y 10 H 2 H 12 Y 9 H 2 H 11 Y 8 H 2 H 10 Y 9 Y 7 Y Y 3 Y 2 Y 2 Y
  3 Y 2 Y
```
-/
def cf283 : Config :=
  { cfsym := false, cfcontractRef := [7],
    cfprog := [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 9, .H, .R 2,
               .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .Y, .R 3, .Y, .R 2,
               .Y, .R 2, .Y, .R 3, .Y, .R 2, .Y] }

/-- math-comp `cf284`:
```
Config 36
  H 10 H 3 H 13 H 13 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y Y Y 3 Y 1 Y 1 Y
  2 Y
```
-/
def cf284 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 10, .H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1,
               .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .Y, .Y, .R 3, .Y,
               .R 1, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf285`:
```
Config 21
  H 2 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 4 H 8 H 8 Y 3 Y 1 Y 5 H 5 Y 2 Y Y 2
  Y
```
-/
def cf285 : Config :=
  { cfsym := false, cfcontractRef := [21],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3,
               .H, .R 9, .Y, .R 4, .H, .R 8, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 5, .H, .R 5, .Y,
               .R 2, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf286`:
```
Config 31
  H 2 H 13 Y 3 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 1 Y 7 H 7 Y 3 Y 1 Y Y Y
  2 Y
```
-/
def cf286 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3,
               .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .R 3, .Y,
               .R 1, .Y, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf287`:
```
Config 28 33 37
  H 12 H 1 Y 9 H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y Y Y 3 Y 2 Y 2 Y
  1 Y
```
-/
def cf287 : Config :=
  { cfsym := false, cfcontractRef := [28, 33, 37],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1,
               .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .Y, .Y, .R 3, .Y,
               .R 2, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf288`:
```
Config 6 12 32 34
  H 3 H 13 H 13 Y 11 H 1 Y 8 H 3 H 11 H 11 Y 8 H 2 H 10 Y 9 Y 7 Y Y Y 3 Y 2 Y Y
  2 Y
```
-/
def cf288 : Config :=
  { cfsym := false, cfcontractRef := [6, 12, 32, 34],
    cfprog := [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 8, .H, .R 3, .H, .R 11,
               .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .Y, .Y, .R 3, .Y,
               .R 2, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf289`:
```
Config 37
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 8 H 8 H 8 Y 3 Y Y 2 Y 3 Y Y 1
  Y
```
-/
def cf289 : Config :=
  { cfsym := false, cfcontractRef := [37],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .H, .R 8, .H, .R 8, .Y, .R 3, .Y, .Y, .R 2,
               .Y, .R 3, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf290`:
```
Config 27
  H 12 H 1 Y 11 H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 Y 7 H 7 Y 2 Y Y 3 Y Y
  Y
```
-/
def cf290 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9,
               .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .R 7, .H, .R 7, .Y, .R 2, .Y,
               .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf291`:
```
Config 36
  H 11 H 1 H 1 Y 4 H 11 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 2 Y 3 Y 2 Y 4 Y Y 3 Y 1 Y
  1 Y
```
-/
def cf291 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11,
               .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 2, .Y, .R 4, .Y,
               .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf292`:
```
Config 18 19 37
  H 3 H 13 H 13 Y 10 H 2 H 12 Y 10 H 10 H 1 Y 9 H 1 Y 9 Y 7 Y 6 H 1 Y 1 Y Y 3 Y
  1 Y 2 Y
```
-/
def cf292 : Config :=
  { cfsym := false, cfcontractRef := [18, 19, 37],
    cfprog := [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 10,
               .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 7, .Y, .R 6, .H, .R 1, .Y, .R 1, .Y,
               .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf293`:
```
Config 34
  H 11 H 1 H 1 Y 3 H 12 Y 3 H 11 Y 4 H 2 H 10 Y 2 Y 3 Y 4 H 7 H 7 Y Y 1 Y 3 Y Y
  Y
```
-/
def cf293 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4,
               .H, .R 2, .H, .R 10, .Y, .R 2, .Y, .R 3, .Y, .R 4, .H, .R 7, .H, .R 7, .Y, .Y, .R 1,
               .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf294`:
```
Config 28 34 36
  H 11 H 2 H 13 Y 10 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 3 Y Y 5 Y Y Y 3 Y
  1 Y
```
-/
def cf294 : Config :=
  { cfsym := false, cfcontractRef := [28, 34, 36],
    cfprog := [.H, .R 11, .H, .R 2, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1,
               .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 3, .Y, .Y, .R 5, .Y, .Y,
               .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf295`:
```
Config 33
  H 10 H 1 H 1 H 1 Y 3 H 12 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 2 Y 4 Y Y 5 Y Y 3 Y 1 Y 1
  Y
```
-/
def cf295 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 10, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11,
               .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 5, .Y, .Y,
               .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf296`:
```
Config 31
  H 2 H 13 Y 3 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 2 H 1 H 1 H 1 Y 6 Y 1 Y 1 Y 3 Y 3 Y Y
  2 Y
```
-/
def cf296 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9,
               .H, .R 1, .Y, .R 2, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y,
               .R 3, .Y, .R 3, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf297`:
```
Config 8 9 30 37
  H 2 H 13 Y 3 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 7 Y 1 Y 1 Y 2 H 1 Y 1 Y
  Y Y
```
-/
def cf297 : Config :=
  { cfsym := false, cfcontractRef := [8, 9, 30, 37],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3,
               .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .R 1, .Y, .R 2, .H,
               .R 1, .Y, .R 1, .Y, .Y, .Y] }

/-- math-comp `cf298`:
```
Config 26 33 35
  H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 2 H 1 H 1 Y 6 Y 1 Y 1 Y Y Y 3 Y
  Y
```
-/
def cf298 : Config :=
  { cfsym := false, cfcontractRef := [26, 33, 35],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y,
               .R 3, .H, .R 10, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y, .Y,
               .Y, .R 3, .Y, .Y] }

/-- math-comp `cf299`:
```
Config 13 31 37
  H 12 H 1 Y 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 Y 2 H 7 Y Y Y 2 H 1 Y 1 Y
  Y
```
-/
def cf299 : Config :=
  { cfsym := false, cfcontractRef := [13, 31, 37],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9,
               .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .R 2, .H,
               .R 1, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf300`:
```
Config 35
  H 2 H 13 Y 4 H 11 H 1 Y 3 H 2 H 11 Y 3 H 10 Y 2 H 1 Y 7 Y 7 H 7 Y 3 Y Y Y 3 Y
  Y
```
-/
def cf300 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 4, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 2, .H, .R 11,
               .Y, .R 3, .H, .R 10, .Y, .R 2, .H, .R 1, .Y, .R 7, .Y, .R 7, .H, .R 7, .Y, .R 3, .Y,
               .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf301`:
```
Config 17
  H 12 H 1 Y 8 H 4 H 12 H 12 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 9 Y 4 Y Y 4 Y Y 3 Y 1 Y
  1 Y
```
-/
def cf301 : Config :=
  { cfsym := false, cfcontractRef := [17],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 8, .H, .R 4, .H, .R 12, .H, .R 12, .H, .R 12, .Y, .R 9,
               .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 4, .Y, .Y, .R 4, .Y, .Y,
               .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf302`:
```
Config 18 19 37
  H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 3 H 9 Y 2 H 8 Y Y 1 Y 3 Y 1 Y Y 1
  Y
```
-/
def cf302 : Config :=
  { cfsym := false, cfcontractRef := [18, 19, 37],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y,
               .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .R 1, .Y, .R 3, .Y,
               .R 1, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf303`:
```
Config* 24 29 37
  H 12 H 1 Y 3 H 12 Y 3 H 11 Y 7 H 6 H 1 H 1 H 1 H 1 Y 2 Y 4 Y 1 Y 4 Y Y 3 Y 1 Y
  1 Y
```
-/
def cf303 : Config :=
  { cfsym := true, cfcontractRef := [24, 29, 37],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 7, .H, .R 6,
               .H, .R 1, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 4, .Y, .R 1, .Y, .R 4, .Y,
               .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf304`:
```
Config* 32
  H 12 H 1 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 2 H 9 Y 2 Y Y 4 Y 1 H 5 Y 1 H 1 Y 1
  Y Y
```
-/
def cf304 : Config :=
  { cfsym := true, cfcontractRef := [32],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10,
               .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 2, .Y, .Y, .R 4, .Y, .R 1, .H, .R 5, .Y, .R 1,
               .H, .R 1, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf305`:
```
Config 37
  H 2 H 13 Y 3 H 12 Y 5 H 2 H 11 Y 4 H 10 H 10 Y 3 Y 5 H 8 H 8 H 8 Y Y 1 Y 4 Y Y
  Y Y
```
-/
def cf305 : Config :=
  { cfsym := false, cfcontractRef := [37],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 2, .H, .R 11, .Y, .R 4,
               .H, .R 10, .H, .R 10, .Y, .R 3, .Y, .R 5, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .Y, .R 1,
               .Y, .R 4, .Y, .Y, .Y, .Y] }

/-- math-comp `cf306`:
```
Config 35
  H 12 H 1 Y 8 H 4 H 12 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 6 Y Y 2 H 7 Y Y Y 2 H 1 Y 1
  Y Y
```
-/
def cf306 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 8, .H, .R 4, .H, .R 12, .H, .R 12, .H, .R 12, .Y, .R 10,
               .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 6, .Y, .Y, .R 2, .H, .R 7, .Y, .Y, .Y, .R 2, .H,
               .R 1, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf307`:
```
Config 36
  H 2 H 13 Y 4 H 2 H 12 Y 3 H 11 Y 5 H 10 H 10 H 10 H 1 H 1 Y 2 Y Y Y 1 Y 2 H 5
  Y 3 Y Y Y
```
-/
def cf307 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 4, .H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 5,
               .H, .R 10, .H, .R 10, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .Y, .Y, .R 1, .Y,
               .R 2, .H, .R 5, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf308`:
```
Config 7
  H 5 H 13 H 13 H 13 H 13 Y 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 9 Y 7 H 8 Y Y 1 Y 4 Y
  Y Y Y
```
-/
def cf308 : Config :=
  { cfsym := false, cfcontractRef := [7],
    cfprog := [.H, .R 5, .H, .R 13, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 9,
               .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 7, .H, .R 8, .Y, .Y, .R 1,
               .Y, .R 4, .Y, .Y, .Y, .Y] }

/-- math-comp `cf309`:
```
Config 30
  H 2 H 13 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 2 H 1 H 1 H 8 H 8 Y Y 1 Y 3 Y 3
  Y Y 2 Y
```
-/
def cf309 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10,
               .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .H, .R 1, .H, .R 8, .H, .R 8, .Y, .Y, .R 1,
               .Y, .R 3, .Y, .R 3, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf310`:
```
Config 7
  H 3 H 13 H 13 Y 9 H 3 H 12 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 9 Y 6 H 8 Y 2 Y Y 4 Y Y
  Y Y
```
-/
def cf310 : Config :=
  { cfsym := false, cfcontractRef := [7],
    cfprog := [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 9,
               .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 6, .H, .R 8, .Y, .R 2, .Y,
               .Y, .R 4, .Y, .Y, .Y, .Y] }

/-- math-comp `cf311`:
```
Config 34
  H 2 H 13 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 5 H 7 H 1 H 1 Y H 8 Y 3 H 7 Y Y 3 Y 3 Y
  Y 2 Y
```
-/
def cf311 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10,
               .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .H, .R 8, .Y, .R 3, .H, .R 7, .Y, .Y,
               .R 3, .Y, .R 3, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf312`:
```
Config 31
  H 12 H 1 Y 3 H 12 Y 3 H 11 Y 5 H 2 H 10 Y 2 Y 5 H 8 Y 2 H 1 H 7 H 7 Y Y 1 Y 3
  Y Y Y
```
-/
def cf312 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 2,
               .H, .R 10, .Y, .R 2, .Y, .R 5, .H, .R 8, .Y, .R 2, .H, .R 1, .H, .R 7, .H, .R 7, .Y,
               .Y, .R 1, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf313`:
```
Config 42
  H 2 H 13 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 6 H 1 Y 5 H 1 H 1 H 1 H 1 Y 7 H 7 Y Y 3
  Y Y 3 Y Y
```
-/
def cf313 : Config :=
  { cfsym := false, cfcontractRef := [42],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10,
               .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 7, .H,
               .R 7, .Y, .Y, .R 3, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf314`:
```
Config 33
  H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 4 H 9 H 9 H 1 H 1 Y 1 Y Y 5 Y Y 3
  Y 1 Y 1 Y
```
-/
def cf314 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y,
               .R 3, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y,
               .R 5, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf315`:
```
Config 42
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 9 H 9 H 9 H 2 H 9 Y 3 H 8 Y Y 6 Y 4 Y
  3 Y 2 Y Y
```
-/
def cf315 : Config :=
  { cfsym := false, cfcontractRef := [42],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 8, .H, .R 9, .H, .R 9, .H, .R 9, .H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .Y,
               .Y, .R 6, .Y, .R 4, .Y, .R 3, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf316`:
```
Config 6
  H 12 H 1 Y 3 H 12 Y 3 H 11 Y 7 H 1 Y 5 H 9 Y 5 H 8 H 8 H 8 H 8 Y 2 H 1 Y 2 Y 3
  Y 1 Y 2 Y Y
```
-/
def cf316 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 7, .H, .R 1,
               .Y, .R 5, .H, .R 9, .Y, .R 5, .H, .R 8, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .R 2, .H,
               .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf317`:
```
Config 46
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 5 H 1 H 1 H 1 H 1 H 9 H 9 Y 8 H 1 Y 1 Y 2
  Y 4 Y Y 3 Y 2 Y
```
-/
def cf317 : Config :=
  { cfsym := false, cfcontractRef := [46],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 5, .H, .R 1, .H, .R 1, .H, .R 1, .H, .R 1, .H, .R 9, .H, .R 9, .Y, .R 8, .H,
               .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 3, .Y, .R 2, .Y] }

/-- math-comp `cf318`:
```
Config 37
  H 3 H 13 H 13 Y 10 H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 9 Y 7 Y Y 6 Y 4 Y 1 Y
  2 Y 1 Y
```
-/
def cf318 : Config :=
  { cfsym := false, cfcontractRef := [37],
    cfprog := [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1,
               .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .Y, .R 6, .Y, .R 4,
               .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf319`:
```
Config 35
  H 12 H 1 Y 11 H 1 Y 10 H 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 Y 6 H 1 Y 1 Y Y 2 Y 2
  Y 2 Y
```
-/
def cf319 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 9,
               .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 1, .Y,
               .Y, .R 2, .Y, .R 2, .Y, .R 2, .Y] }

/-- math-comp `cf320`:
```
Config 14 32 34
  H 4 H 13 H 13 H 13 Y 11 H 1 Y 9 H 2 H 11 Y 8 H 2 H 10 Y 9 Y 6 Y 1 Y Y Y 3 Y 1
  Y 2 Y
```
-/
def cf320 : Config :=
  { cfsym := false, cfcontractRef := [14, 32, 34],
    cfprog := [.H, .R 4, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2,
               .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 6, .Y, .R 1, .Y, .Y, .Y,
               .R 3, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf321`:
```
Config 1 2 35
  H 2 H 13 Y 11 H 1 Y 10 H 1 Y 8 H 8 H 2 H 10 Y 9 Y 5 H 1 Y 7 H 1 Y 1 Y Y 3 Y 1
  Y 2 Y
```
-/
def cf321 : Config :=
  { cfsym := false, cfcontractRef := [1, 2, 35],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 8,
               .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 5, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y,
               .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf322`:
```
Config 32
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 H 8 H 8 Y 2 H 1 Y 1 Y Y 3 Y
  1 Y 1 Y
```
-/
def cf322 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .R 2, .H, .R 1, .Y,
               .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf323`:
```
Config 30
  H 12 H 1 Y 9 H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 Y 7 H 7 Y 2 Y Y 3
  Y Y Y
```
-/
def cf323 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1,
               .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .R 7, .H, .R 7, .Y,
               .R 2, .Y, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf324`:
```
Config* 6
  H 2 H 8 Y 6 H 1 Y 6 H 6 H 6 H 6 Y 4 Y Y Y Y
```
-/
def cf324 : Config :=
  { cfsym := true, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 8, .Y, .R 6, .H, .R 1, .Y, .R 6, .H, .R 6, .H, .R 6, .H, .R 6, .Y,
               .R 4, .Y, .Y, .Y, .Y] }

/-- math-comp `cf325`:
```
Config* 21
  H 7 H 2 H 9 Y 7 H 6 H 2 H 8 Y 7 H 7 Y Y Y Y Y Y
```
-/
def cf325 : Config :=
  { cfsym := true, cfcontractRef := [21],
    cfprog := [.H, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 6, .H, .R 2, .H, .R 8, .Y, .R 7, .H,
               .R 7, .Y, .Y, .Y, .Y, .Y, .Y] }

/-- math-comp `cf326`:
```
Config* 29
  H 4 H 7 H 1 H 1 Y 4 H 1 H 1 H 1 Y 1 Y 1 Y 1 Y 2 H 4 Y 2 Y 1 Y
```
-/
def cf326 : Config :=
  { cfsym := true, cfcontractRef := [29],
    cfprog := [.H, .R 4, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .H, .R 1, .Y,
               .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 4, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf327`:
```
Config 23
  H 8 H 1 Y 3 H 8 Y 5 H 5 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 2 Y
```
-/
def cf327 : Config :=
  { cfsym := false, cfcontractRef := [23],
    cfprog := [.H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 5, .H, .R 5, .H, .R 1, .H, .R 1, .Y,
               .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf328`:
```
Config* 0 23
  H 8 H 1 Y 3 H 8 Y 4 H 6 H 1 Y 2 H 1 Y 3 Y 1 Y 3 Y Y
```
-/
def cf328 : Config :=
  { cfsym := true, cfcontractRef := [0, 23],
    cfprog := [.H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 6, .H, .R 1, .Y, .R 2, .H,
               .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf329`:
```
Config 6
  H 2 H 9 Y 7 H 1 Y 4 H 7 Y 4 H 1 Y 5 H 1 Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf329 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 4, .H, .R 7, .Y, .R 4, .H, .R 1, .Y,
               .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf330`:
```
Config* 14 15 21 26
  H 3 H 9 H 1 Y 3 H 2 H 9 Y 3 H 8 Y 2 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y
```
-/
def cf330 : Config :=
  { cfsym := true, cfcontractRef := [14, 15, 21, 26],
    cfprog := [.H, .R 3, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 3, .H, .R 8, .Y,
               .R 2, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf331`:
```
Config 30
  H 2 H 10 Y 4 H 4 H 7 H 1 H 1 Y 5 H 1 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf331 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 4, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 5, .H,
               .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf332`:
```
Config 30
  H 9 H 1 Y 7 H 2 H 9 Y 6 H 1 H 7 H 1 Y 7 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y
```
-/
def cf332 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 6, .H, .R 1, .H, .R 7, .H,
               .R 1, .Y, .R 7, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf333`:
```
Config 25
  H 9 H 1 Y 7 H 1 H 8 H 1 Y 7 H 1 H 1 Y 1 Y 1 Y 4 H 1 Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf333 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .H,
               .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1,
               .Y] }

/-- math-comp `cf334`:
```
Config* 24
  H 9 H 1 Y 3 H 9 Y 3 H 8 Y 4 H 6 H 1 Y 2 Y 3 Y 1 Y 1 Y 2 Y
```
-/
def cf334 : Config :=
  { cfsym := true, cfcontractRef := [24],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 4, .H, .R 6, .H,
               .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf335`:
```
Config 6
  H 2 H 10 Y 8 H 1 Y 4 H 4 H 8 H 8 H 8 Y 7 Y 5 Y Y Y 3 Y 1 Y
```
-/
def cf335 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 4, .H, .R 4, .H, .R 8, .H, .R 8, .H,
               .R 8, .Y, .R 7, .Y, .R 5, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf336`:
```
Config 18
  H 9 H 1 Y 7 H 2 H 9 Y 6 H 2 H 8 Y 6 H 1 Y 5 Y Y 3 Y Y 2 Y
```
-/
def cf336 : Config :=
  { cfsym := false, cfcontractRef := [18],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 6, .H, .R 2, .H, .R 8, .Y,
               .R 6, .H, .R 1, .Y, .R 5, .Y, .Y, .R 3, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf337`:
```
Config 6
  H 2 H 10 Y 8 H 1 Y 6 H 2 H 8 Y 6 H 7 Y 5 Y Y 4 H 4 Y 2 Y Y
```
-/
def cf337 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .H,
               .R 7, .Y, .R 5, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf338`:
```
Config 27
  H 2 H 10 Y 8 H 1 Y 5 H 3 H 8 H 8 Y 7 H 7 Y 5 Y Y 2 Y 2 Y 1 Y
```
-/
def cf338 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 3, .H, .R 8, .H, .R 8, .Y,
               .R 7, .H, .R 7, .Y, .R 5, .Y, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf339`:
```
Config 12
  H 2 H 10 Y 4 H 8 H 1 Y 3 H 2 H 8 Y 2 Y 5 H 1 Y 5 Y 1 Y 2 Y 2 Y
```
-/
def cf339 : Config :=
  { cfsym := false, cfcontractRef := [12],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 2, .H, .R 8, .Y,
               .R 2, .Y, .R 5, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 2, .Y, .R 2, .Y] }

/-- math-comp `cf340`:
```
Config 6
  H 2 H 10 Y 8 H 1 Y 7 H 1 Y 5 H 7 Y 5 Y 5 H 1 Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf340 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 7, .Y,
               .R 5, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf341`:
```
Config* 26
  H 8 H 1 H 1 Y 3 H 9 Y 5 H 6 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 2 Y
```
-/
def cf341 : Config :=
  { cfsym := true, cfcontractRef := [26],
    cfprog := [.H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 5, .H, .R 6, .H, .R 1, .H,
               .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf342`:
```
Config 12 13 28
  H 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 6 H 1 Y 5 Y 4 H 5 Y Y 1 Y 2 Y
```
-/
def cf342 : Config :=
  { cfsym := false, cfcontractRef := [12, 13, 28],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 6, .H,
               .R 1, .Y, .R 5, .Y, .R 4, .H, .R 5, .Y, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf343`:
```
Config* 1 2 8 9
  H 2 H 11 Y 3 H 10 Y 3 H 4 H 7 H 1 H 1 Y 6 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf343 : Config :=
  { cfsym := true, cfcontractRef := [1, 2, 8, 9],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 4, .H, .R 7, .H, .R 1, .H,
               .R 1, .Y, .R 6, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1,
               .Y] }

/-- math-comp `cf344`:
```
Config 6
  H 2 H 9 Y 7 H 1 Y 4 H 7 Y 4 H 1 Y 4 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf344 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 4, .H, .R 7, .Y, .R 4, .H, .R 1, .Y,
               .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf345`:
```
Config 25
  H 10 H 1 Y 9 H 9 H 1 Y 7 H 2 H 9 Y 4 H 8 Y Y Y Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf345 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y,
               .R 4, .H, .R 8, .Y, .Y, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf346`:
```
Config 28
  H 2 H 11 Y 4 H 2 H 10 Y 4 H 8 H 1 Y 5 H 1 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf346 : Config :=
  { cfsym := false, cfcontractRef := [28],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y,
               .R 5, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1,
               .Y] }

/-- math-comp `cf347`:
```
Config 4 5 24 29
  H 2 H 11 Y 3 H 10 Y 3 H 3 H 8 H 1 Y 2 H 1 H 1 Y 1 Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf347 : Config :=
  { cfsym := false, cfcontractRef := [4, 5, 24, 29],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 3, .H, .R 8, .H, .R 1, .Y,
               .R 2, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1,
               .Y] }

/-- math-comp `cf348`:
```
Config 25
  H 4 H 9 H 1 H 1 Y 3 H 2 H 10 Y 3 H 9 Y 7 H 8 Y Y Y Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf348 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 4, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 3, .H,
               .R 9, .Y, .R 7, .H, .R 8, .Y, .Y, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf349`:
```
Config* 24
  H 8 H 2 H 10 Y 8 H 6 H 3 H 9 H 9 Y 8 H 8 Y Y Y Y 4 H 4 Y 2 Y Y
```
-/
def cf349 : Config :=
  { cfsym := true, cfcontractRef := [24],
    cfprog := [.H, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y,
               .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf350`:
```
Config 18
  H 8 H 2 H 10 Y 6 H 8 H 1 Y 8 H 8 Y Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf350 : Config :=
  { cfsym := false, cfcontractRef := [18],
    cfprog := [.H, .R 8, .H, .R 2, .H, .R 10, .Y, .R 6, .H, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y,
               .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf351`:
```
Config 34
  H 2 H 11 Y 3 H 2 H 10 Y 4 H 1 H 7 H 1 H 1 Y 2 H 8 Y 2 Y Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf351 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 1, .H, .R 7, .H,
               .R 1, .H, .R 1, .Y, .R 2, .H, .R 8, .Y, .R 2, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y,
               .R 1, .Y] }

/-- math-comp `cf352`:
```
Config 21
  H 10 H 1 Y 8 H 9 H 1 Y 8 H 9 H 2 H 9 Y 8 H 1 Y 7 Y 1 Y Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf352 : Config :=
  { cfsym := false, cfcontractRef := [21],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 2, .H,
               .R 9, .Y, .R 8, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y,
               .R 1, .Y] }

/-- math-comp `cf353`:
```
Config 29
  H 10 H 1 Y 9 H 9 H 1 Y 7 H 1 H 8 H 1 Y 8 H 1 Y 1 Y 1 Y 5 Y 4 H 4 Y 2 Y Y
```
-/
def cf353 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H,
               .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 5, .Y, .R 4, .H, .R 4, .Y, .R 2,
               .Y, .Y] }

/-- math-comp `cf354`:
```
Config 11
  H 10 H 1 Y 8 H 2 H 10 Y 6 H 1 H 8 H 1 Y 8 H 1 Y 1 Y 2 H 6 Y 5 Y 3 Y Y 2 Y
```
-/
def cf354 : Config :=
  { cfsym := false, cfcontractRef := [11],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 6, .H, .R 1, .H, .R 8, .H,
               .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 6, .Y, .R 5, .Y, .R 3, .Y, .Y,
               .R 2, .Y] }

/-- math-comp `cf355`:
```
Config 25
  H 9 H 1 Y 7 H 1 H 8 H 1 Y 7 H 1 H 1 Y 1 Y 1 Y 3 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf355 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .H,
               .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1,
               .Y] }

/-- math-comp `cf356`:
```
Config 27
  H 3 H 11 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 7 Y 5 Y Y Y 2 Y 2 Y
```
-/
def cf356 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y,
               .R 7, .H, .R 1, .Y, .R 7, .Y, .R 5, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y] }

/-- math-comp `cf357`:
```
Config 12 13 29
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 6 H 1 Y 5 Y 3 Y Y 3 Y Y
```
-/
def cf357 : Config :=
  { cfsym := false, cfcontractRef := [12, 13, 29],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H,
               .R 8, .Y, .R 6, .H, .R 1, .Y, .R 5, .Y, .R 3, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf358`:
```
Config 16 17 28
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 7 Y 5 Y 4 H 5 Y 3 Y Y Y
```
-/
def cf358 : Config :=
  { cfsym := false, cfcontractRef := [16, 17, 28],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y,
               .R 6, .H, .R 7, .Y, .R 5, .Y, .R 4, .H, .R 5, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf359`:
```
Config 19
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 2 H 8 Y 7 H 7 Y 5 Y 2 Y 2 Y 2 Y Y
```
-/
def cf359 : Config :=
  { cfsym := false, cfcontractRef := [19],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 2, .H,
               .R 8, .Y, .R 7, .H, .R 7, .Y, .R 5, .Y, .R 2, .Y, .R 2, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf360`:
```
Config 6
  H 2 H 11 Y 9 H 1 Y 6 H 8 H 1 Y 8 Y 5 H 1 Y 6 H 1 Y 5 H 1 Y 4 Y Y 1 Y
```
-/
def cf360 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 8, .H, .R 1, .Y, .R 8, .Y,
               .R 5, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf361`:
```
Config 26
  H 10 H 1 Y 6 H 4 H 10 H 10 H 10 Y 8 H 1 Y 7 H 1 Y 6 Y Y Y 3 Y 1 Y 1 Y
```
-/
def cf361 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 6, .H, .R 4, .H, .R 10, .H, .R 10, .H, .R 10, .Y, .R 8,
               .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf362`:
```
Config 28
  H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 8 H 8 Y 6 Y Y 5 H 5 Y Y 2 Y Y
```
-/
def cf362 : Config :=
  { cfsym := false, cfcontractRef := [28],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H,
               .R 8, .H, .R 8, .Y, .R 6, .Y, .Y, .R 5, .H, .R 5, .Y, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf363`:
```
Config 6
  H 2 H 10 Y 8 H 1 Y 4 H 4 H 8 H 8 H 8 Y 7 Y 5 Y Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf363 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 4, .H, .R 4, .H, .R 8, .H, .R 8, .H,
               .R 8, .Y, .R 7, .Y, .R 5, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf364`:
```
Config 6
  H 2 H 11 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 8 Y 6 Y Y 4 H 1 Y 4 Y 2 Y Y
```
-/
def cf364 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y,
               .R 7, .H, .R 8, .Y, .R 6, .Y, .Y, .R 4, .H, .R 1, .Y, .R 4, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf365`:
```
Config 21
  H 2 H 11 Y 9 H 1 Y 8 H 6 H 3 H 9 H 9 Y 8 Y 5 H 1 Y 6 Y 1 Y 3 Y 2 Y Y
```
-/
def cf365 : Config :=
  { cfsym := false, cfcontractRef := [21],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 6, .H, .R 3, .H, .R 9, .H,
               .R 9, .Y, .R 8, .Y, .R 5, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .R 3, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf366`:
```
Config 29
  H 3 H 11 H 11 Y 9 H 1 Y 5 H 4 H 9 H 9 H 9 Y 8 Y 6 Y Y Y Y 3 Y 1 Y
```
-/
def cf366 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 5, .H, .R 4, .H, .R 9, .H,
               .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf367`:
```
Config 32
  H 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 1 Y 7 H 1 Y 7 H 7 Y Y Y Y 2 Y 2 Y
```
-/
def cf367 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1,
               .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .Y, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y] }

/-- math-comp `cf368`:
```
Config 6
  H 2 H 10 Y 8 H 1 Y 7 H 1 Y 5 H 7 Y 5 Y 4 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf368 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .H, .R 7, .Y,
               .R 5, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf369`:
```
Config 31
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 8 Y 6 Y 5 H 1 H 5 H 1 Y 2 Y Y 3 Y 1 Y
```
-/
def cf369 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 8, .Y,
               .R 6, .Y, .R 5, .H, .R 1, .H, .R 5, .H, .R 1, .Y, .R 2, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf370`:
```
Config 6
  H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 6 H 8 Y 6 Y 4 H 1 H 1 Y 1 Y Y 3 Y 1 Y
```
-/
def cf370 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 6, .H,
               .R 8, .Y, .R 6, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf371`:
```
Config* 4 5 24 29
  H 10 H 1 Y 9 H 1 Y 8 H 6 H 3 H 9 H 9 Y 8 H 8 Y Y Y Y 4 H 4 Y 2 Y Y
```
-/
def cf371 : Config :=
  { cfsym := true, cfcontractRef := [4, 5, 24, 29],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 6, .H, .R 3, .H, .R 9, .H,
               .R 9, .Y, .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf372`:
```
Config 4 5 18 23
  H 10 H 1 Y 9 H 1 Y 6 H 8 H 1 Y 8 H 8 Y Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf372 : Config :=
  { cfsym := false, cfcontractRef := [4, 5, 18, 23],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 8, .H, .R 1, .Y, .R 8, .H,
               .R 8, .Y, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf373`:
```
Config 33
  H 2 H 12 Y 3 H 2 H 11 Y 3 H 2 H 10 Y 2 H 1 H 1 Y 2 H 1 Y 7 Y 1 Y 1 Y 1 Y 2 Y 1
  Y
```
-/
def cf373 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10,
               .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .R 1, .Y,
               .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf374`:
```
Config 30
  H 11 H 1 Y 10 H 10 H 1 Y 8 H 9 H 1 Y 9 H 9 Y 8 H 8 Y 2 Y Y Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf374 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1,
               .Y, .R 9, .H, .R 9, .Y, .R 8, .H, .R 8, .Y, .R 2, .Y, .Y, .Y, .R 4, .H, .R 1, .Y,
               .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf375`:
```
Config 37
  H 2 H 11 Y 3 H 2 H 10 Y 4 H 2 H 6 H 1 H 2 H 9 Y 1 H 1 Y 1 Y Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf375 : Config :=
  { cfsym := false, cfcontractRef := [37],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 2, .H, .R 6, .H,
               .R 1, .H, .R 2, .H, .R 9, .Y, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 1, .Y, .R 1, .Y,
               .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf376`:
```
Config 21
  H 10 H 1 Y 8 H 9 H 1 Y 8 H 8 H 3 H 8 H 1 Y H 8 Y Y 1 Y Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf376 : Config :=
  { cfsym := false, cfcontractRef := [21],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 3, .H,
               .R 8, .H, .R 1, .Y, .H, .R 8, .Y, .Y, .R 1, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y,
               .R 1, .Y] }

/-- math-comp `cf377`:
```
Config 29
  H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 8 H 1 Y 8 Y 6 Y Y 5 H 5 Y 2 Y 3 Y 1 Y
```
-/
def cf377 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8,
               .H, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .R 5, .H, .R 5, .Y, .R 2, .Y, .R 3,
               .Y, .R 1, .Y] }

/-- math-comp `cf378`:
```
Config 18
  H 11 H 1 Y 9 H 2 H 11 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 6 Y Y 3 Y 3 Y 3 Y 1 Y
```
-/
def cf378 : Config :=
  { cfsym := false, cfcontractRef := [18],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10,
               .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .Y, .Y, .R 3, .Y, .R 3, .Y, .R 3,
               .Y, .R 1, .Y] }

/-- math-comp `cf379`:
```
Config 30
  H 11 H 1 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 1 Y 7 H 1 Y 6 Y Y Y 3 Y 1 Y 1 Y
```
-/
def cf379 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10,
               .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y,
               .R 1, .Y] }

/-- math-comp `cf380`:
```
Config 30 33
  H 3 H 12 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 7 H 2 H 9 Y 8 Y 6 Y Y Y 3 Y 2 Y Y
```
-/
def cf380 : Config :=
  { cfsym := false, cfcontractRef := [30, 33],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10,
               .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 2, .Y,
               .Y] }

/-- math-comp `cf381`:
```
Config 31
  H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 8 Y 6 Y Y Y Y 3 Y 1 Y
```
-/
def cf381 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 6,
               .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1,
               .Y] }

/-- math-comp `cf382`:
```
Config 25
  H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 6 H 3 H 9 H 9 Y 8 Y 6 Y 6 Y 4 Y 3 Y Y Y
```
-/
def cf382 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 6,
               .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .R 6, .Y, .R 4, .Y, .R 3, .Y,
               .Y, .Y] }

/-- math-comp `cf383`:
```
Config 14
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 1 Y 5 H 1 H 1 Y H 5 Y Y Y 1 Y
```
-/
def cf383 : Config :=
  { cfsym := false, cfcontractRef := [14],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y,
               .R 7, .H, .R 1, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf384`:
```
Config 33
  H 11 H 1 Y 7 H 4 H 11 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 6 Y Y Y 2 H 1 Y 1 Y 1 Y 1 Y
```
-/
def cf384 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 7, .H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 9,
               .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .Y, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y,
               .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf385`:
```
Config 32
  H 11 H 1 Y 7 H 4 H 11 H 11 H 11 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y Y Y Y 3 Y 1 Y 1 Y
```
-/
def cf385 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 7, .H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 9,
               .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y,
               .R 1, .Y] }

/-- math-comp `cf386`:
```
Config 29
  H 11 H 1 Y 8 H 3 H 11 H 11 Y 8 H 2 H 10 Y 8 H 1 Y 8 H 8 Y Y Y Y 3 Y 2 Y Y
```
-/
def cf386 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 8, .H, .R 2,
               .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .R 3, .Y, .R 2,
               .Y, .Y] }

/-- math-comp `cf387`:
```
Config 6
  H 2 H 11 Y 7 H 3 H 10 H 10 Y 6 H 3 H 9 H 9 Y 8 Y 6 H 7 Y Y 1 Y 3 Y 2 Y Y
```
-/
def cf387 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 6, .H, .R 3,
               .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .H, .R 7, .Y, .Y, .R 1, .Y, .R 3, .Y, .R 2,
               .Y, .Y] }

/-- math-comp `cf388`:
```
Config 6
  H 2 H 11 Y 9 H 1 Y 4 H 5 H 9 H 9 H 9 H 9 Y 8 Y 5 H 7 Y 2 Y Y 3 Y 2 Y Y
```
-/
def cf388 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 4, .H, .R 5, .H, .R 9, .H, .R 9, .H,
               .R 9, .H, .R 9, .Y, .R 8, .Y, .R 5, .H, .R 7, .Y, .R 2, .Y, .Y, .R 3, .Y, .R 2, .Y,
               .Y] }

/-- math-comp `cf389`:
```
Config 18
  H 2 H 11 Y 5 H 2 H 10 Y 3 H 9 Y 2 Y 5 H 1 Y 1 Y 4 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf389 : Config :=
  { cfsym := false, cfcontractRef := [18],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 5, .H, .R 2, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .Y,
               .R 5, .H, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1,
               .Y] }

/-- math-comp `cf390`:
```
Config* 25
  H 10 H 1 Y 9 H 9 H 1 Y 7 H 1 H 8 H 1 Y 2 H 8 Y Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf390 : Config :=
  { cfsym := true, cfcontractRef := [25],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 8, .H,
               .R 1, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y,
               .R 1, .Y] }

/-- math-comp `cf391`:
```
Config* 36
  H 2 H 11 Y 3 H 2 H 10 Y 6 H 9 H 7 H 1 H 1 H 1 H 1 Y 1 Y Y 1 Y 1 Y 4 H 4 Y Y 1
  Y
```
-/
def cf391 : Config :=
  { cfsym := true, cfcontractRef := [36],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 6, .H, .R 9, .H, .R 7, .H,
               .R 1, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H,
               .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf392`:
```
Config 27
  H 10 H 1 Y 9 H 7 H 3 H 10 H 10 Y 7 H 1 H 1 H 9 H 9 Y Y 1 Y Y Y 4 H 4 Y 2 Y Y
```
-/
def cf392 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 7,
               .H, .R 1, .H, .R 1, .H, .R 9, .H, .R 9, .Y, .Y, .R 1, .Y, .Y, .Y, .R 4, .H, .R 4, .Y,
               .R 2, .Y, .Y] }

/-- math-comp `cf393`:
```
Config 21
  H 10 H 1 Y 7 H 9 H 1 Y 7 H 1 H 1 H 9 H 9 Y Y 1 Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf393 : Config :=
  { cfsym := false, cfcontractRef := [21],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 7, .H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .H,
               .R 9, .H, .R 9, .Y, .Y, .R 1, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y,
               .R 1, .Y] }

/-- math-comp `cf394`:
```
Config 16 17 32
  H 2 H 13 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 8 H 1 Y 8 Y 6 Y 5 H 6 Y 3 Y Y 3 Y 1
  Y
```
-/
def cf394 : Config :=
  { cfsym := false, cfcontractRef := [16, 17, 32],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 8, .H, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .R 5, .H, .R 6, .Y, .R 3, .Y,
               .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf395`:
```
Config 30
  H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 3 H 9 Y 2 H 1 Y 2 Y 1 Y 5 H 5 Y Y Y 1 Y
```
-/
def cf395 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y,
               .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 5, .H, .R 5, .Y, .Y,
               .Y, .R 1, .Y] }

/-- math-comp `cf396`:
```
Config 18
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 1 Y 6 H 1 Y H 5 Y Y Y 1 Y
```
-/
def cf396 : Config :=
  { cfsym := false, cfcontractRef := [18],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y,
               .R 7, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .H, .R 5, .Y, .Y, .Y,
               .R 1, .Y] }

/-- math-comp `cf397`:
```
Config 34
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 H 1 H 7 H 7 Y Y Y 1 Y 1 Y 2 Y
```
-/
def cf397 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y,
               .R 7, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 7, .H, .R 7, .Y, .Y, .Y, .R 1, .Y, .R 1,
               .Y, .R 2, .Y] }

/-- math-comp `cf398`:
```
Config 33
  H 12 H 1 Y 10 H 2 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 6 Y Y 2 H 1 Y 4 Y 3 Y 1
  Y 1 Y
```
-/
def cf398 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11,
               .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .Y, .Y, .R 2, .H, .R 1, .Y, .R 4,
               .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf399`:
```
Config 18
  H 12 H 1 Y 11 H 1 Y 10 H 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 1 Y 1 Y Y 3 Y 3 Y 3
  Y 1 Y
```
-/
def cf399 : Config :=
  { cfsym := false, cfcontractRef := [18],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 9, .H, .R 2, .H, .R 11,
               .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3,
               .Y, .R 3, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf400`:
```
Config 26
  H 11 H 1 Y 10 H 10 H 1 Y 9 H 9 H 1 Y 8 H 9 Y 2 H 8 Y Y Y 4 H 1 H 1 Y H 4 Y Y 1
  Y
```
-/
def cf400 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1,
               .Y, .R 8, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H,
               .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf401`:
```
Config 6
  H 2 H 13 Y 9 H 3 H 12 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 9 Y 7 H 8 Y 4 Y 4 Y Y
  1 Y Y Y
```
-/
def cf401 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1,
               .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 9, .Y, .R 7, .H, .R 8, .Y, .R 4, .Y,
               .R 4, .Y, .Y, .R 1, .Y, .Y, .Y] }

/-- math-comp `cf402`:
```
Config 27
  H 2 H 10 Y 5 H 7 H 1 H 1 Y 3 H 8 Y 3 H 7 Y 3 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf402 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 8, .Y,
               .R 3, .H, .R 7, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf403`:
```
Config 26
  H 9 H 1 Y 3 H 9 Y 4 H 2 H 8 Y 2 Y 4 H 6 Y 2 H 5 Y 2 Y Y 2 Y
```
-/
def cf403 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 2, .H, .R 8, .Y, .R 2, .Y,
               .R 4, .H, .R 6, .Y, .R 2, .H, .R 5, .Y, .R 2, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf404`:
```
Config 0 23
  H 9 H 1 Y 3 H 9 Y 4 H 7 H 1 Y 3 H 7 Y 5 Y 1 Y 3 H 1 Y 3 Y 1 Y
```
-/
def cf404 : Config :=
  { cfsym := false, cfcontractRef := [0, 23],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 7, .H, .R 1, .Y, .R 3, .H,
               .R 7, .Y, .R 5, .Y, .R 1, .Y, .R 3, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf405`:
```
Config 6
  H 2 H 10 Y 8 H 1 Y 4 H 8 Y 5 H 1 Y 6 H 1 Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y
```
-/
def cf405 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 4, .H, .R 8, .Y, .R 5, .H, .R 1, .Y,
               .R 6, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf406`:
```
Config 21
  H 8 H 3 H 11 H 11 Y 7 H 9 H 1 Y 9 H 9 Y Y Y Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y
```
-/
def cf406 : Config :=
  { cfsym := false, cfcontractRef := [21],
    cfprog := [.H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 7, .H, .R 9, .H, .R 1, .Y, .R 9, .H,
               .R 9, .Y, .Y, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf407`:
```
Config 18
  H 9 H 2 H 11 Y 6 H 9 H 1 Y 9 H 9 Y Y Y 6 H 1 Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y
```
-/
def cf407 : Config :=
  { cfsym := false, cfcontractRef := [18],
    cfprog := [.H, .R 9, .H, .R 2, .H, .R 11, .Y, .R 6, .H, .R 9, .H, .R 1, .Y, .R 9, .H, .R 9, .Y,
               .Y, .Y, .R 6, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1,
               .Y] }

/-- math-comp `cf408`:
```
Config 34
  H 3 H 10 H 1 Y 3 H 10 Y 5 H 9 H 2 H 9 Y 2 H 8 Y Y 6 H 1 Y 2 Y 1 Y 2 Y 1 Y
```
-/
def cf408 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 3, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 9, .H, .R 2, .H,
               .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .R 6, .H, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 2, .Y,
               .R 1, .Y] }

/-- math-comp `cf409`:
```
Config 25
  H 10 H 1 Y 8 H 1 H 9 H 1 Y 8 H 1 H 1 Y 1 Y 1 Y 5 H 1 Y 4 H 1 H 1 Y 3 Y 1 Y 1
  Y
```
-/
def cf409 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 1, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .H,
               .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 3,
               .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf410`:
```
Config 1 2 28
  H 10 H 1 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 3 H 8 Y 2 Y 3 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf410 : Config :=
  { cfsym := false, cfcontractRef := [1, 2, 28],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y,
               .R 3, .H, .R 8, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf411`:
```
Config 27
  H 2 H 11 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 3 H 7 Y 3 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf411 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H,
               .R 8, .Y, .R 3, .H, .R 7, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf412`:
```
Config 28
  H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 2 H 8 Y 2 Y 3 Y 2 H 1 Y 4 Y 1 Y 2 Y
```
-/
def cf412 : Config :=
  { cfsym := false, cfcontractRef := [28],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 2, .H,
               .R 8, .Y, .R 2, .Y, .R 3, .Y, .R 2, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf413`:
```
Config 25
  H 2 H 11 Y 6 H 7 H 1 H 1 H 1 Y 3 H 9 Y 3 H 8 Y 3 Y 1 Y 1 Y 2 Y 1 Y 1 Y
```
-/
def cf413 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 6, .H, .R 7, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H,
               .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1,
               .Y] }

/-- math-comp `cf414`:
```
Config 27
  H 2 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 3 H 8 Y 4 Y 1 Y 1 Y 4 H 4 Y Y 1 Y
```
-/
def cf414 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y,
               .R 3, .H, .R 8, .Y, .R 4, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf415`:
```
Config 6
  H 2 H 11 Y 9 H 1 Y 6 H 8 H 1 Y 8 Y 5 H 1 Y 6 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y
```
-/
def cf415 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 8, .H, .R 1, .Y, .R 8, .Y,
               .R 5, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1,
               .Y] }

/-- math-comp `cf416`:
```
Config 6
  H 2 H 11 Y 9 H 1 Y 4 H 5 H 9 H 9 H 9 H 9 Y 8 Y 6 Y Y Y 3 Y 1 Y 1 Y
```
-/
def cf416 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 4, .H, .R 5, .H, .R 9, .H, .R 9, .H,
               .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf417`:
```
Config 31
  H 3 H 11 H 11 Y 6 H 4 H 10 H 10 H 10 Y 8 H 1 Y 8 Y 6 Y Y Y 2 Y 2 Y 1 Y
```
-/
def cf417 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 6, .H, .R 4, .H, .R 10, .H, .R 10, .H, .R 10,
               .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf418`:
```
Config 32
  H 8 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 6 H 1 H 1 Y 6 Y Y Y 3 Y Y 2 Y
```
-/
def cf418 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y,
               .R 6, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf419`:
```
Config 29
  H 10 H 1 Y 3 H 10 Y 4 H 2 H 9 Y 2 H 1 Y 4 H 7 Y 2 H 6 Y 3 Y Y Y 2 Y
```
-/
def cf419 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 2, .H, .R 9, .Y, .R 2, .H,
               .R 1, .Y, .R 4, .H, .R 7, .Y, .R 2, .H, .R 6, .Y, .R 3, .Y, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf420`:
```
Config 32
  H 10 H 1 Y 8 H 2 H 10 Y 7 H 2 H 9 Y 6 H 2 H 8 Y 6 Y Y 4 Y Y Y 2 Y
```
-/
def cf420 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 7, .H, .R 2, .H, .R 9, .Y,
               .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .Y, .Y, .R 4, .Y, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf421`:
```
Config 6
  H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 6 H 8 Y 6 Y Y 4 H 5 Y 2 H 4 Y 2 Y Y
```
-/
def cf421 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 6, .H,
               .R 8, .Y, .R 6, .Y, .Y, .R 4, .H, .R 5, .Y, .R 2, .H, .R 4, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf422`:
```
Config 31
  H 10 H 1 Y 7 H 3 H 10 H 10 Y 7 H 2 H 9 Y 7 H 1 Y 6 Y Y 3 Y Y 2 Y 1 Y
```
-/
def cf422 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 7, .H, .R 2,
               .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 6, .Y, .Y, .R 3, .Y, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf423`:
```
Config 26
  H 2 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 3 H 2 H 8 Y 3 Y 1 Y 3 H 1 Y 1 Y 3 Y 1 Y
```
-/
def cf423 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H,
               .R 2, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 3, .H, .R 1, .Y, .R 1, .Y, .R 3, .Y, .R 1,
               .Y] }

/-- math-comp `cf424`:
```
Config 26
  H 9 H 1 Y 3 H 9 Y 4 H 7 H 1 Y 2 H 1 H 1 Y 3 Y 1 Y 2 H 1 Y 1 Y Y
```
-/
def cf424 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 7, .H, .R 1, .Y, .R 2, .H,
               .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf425`:
```
Config 26
  H 2 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 4 H 6 H 1 Y 3 Y 1 Y 4 H 4 Y Y 1 Y
```
-/
def cf425 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 4, .H,
               .R 6, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 4, .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf426`:
```
Config 30
  H 10 H 1 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 3 H 8 Y 5 Y 1 Y 4 H 1 Y 3 Y 1 Y 1 Y
```
-/
def cf426 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y,
               .R 3, .H, .R 8, .Y, .R 5, .Y, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1,
               .Y] }

/-- math-comp `cf427`:
```
Config 28
  H 9 H 1 Y 3 H 9 Y 4 H 2 H 8 Y 2 Y 5 H 6 H 6 Y 1 H 1 Y 1 Y Y 2 Y
```
-/
def cf427 : Config :=
  { cfsym := false, cfcontractRef := [28],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 2, .H, .R 8, .Y, .R 2, .Y,
               .R 5, .H, .R 6, .H, .R 6, .Y, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf428`:
```
Config 19
  H 2 H 11 Y 3 H 2 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 4 H 7 Y 2 Y Y 3 Y 1 Y Y
```
-/
def cf428 : Config :=
  { cfsym := false, cfcontractRef := [19],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y,
               .R 3, .H, .R 8, .Y, .R 4, .H, .R 7, .Y, .R 2, .Y, .Y, .R 3, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf429`:
```
Config 27
  H 10 H 1 Y 3 H 10 Y 3 H 2 H 9 Y 3 H 1 Y 4 H 7 Y 2 Y Y 2 H 1 Y 1 Y Y
```
-/
def cf429 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 3, .H,
               .R 1, .Y, .R 4, .H, .R 7, .Y, .R 2, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf430`:
```
Config 6
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 8 Y 6 Y 6 H 1 Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y
```
-/
def cf430 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 8, .Y,
               .R 6, .Y, .R 6, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1,
               .Y] }

/-- math-comp `cf431`:
```
Config 30
  H 2 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 4 H 8 H 8 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf431 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y,
               .R 4, .H, .R 8, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1,
               .Y] }

/-- math-comp `cf432`:
```
Config 31
  H 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 7 H 1 Y 6 Y 4 H 6 Y Y 1 Y 2 Y 1 Y
```
-/
def cf432 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H,
               .R 7, .H, .R 1, .Y, .R 6, .Y, .R 4, .H, .R 6, .Y, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf433`:
```
Config 6
  H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 1 Y 3 Y 4 H 1 Y H 4 Y Y 1 Y
```
-/
def cf433 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y,
               .R 3, .H, .R 1, .Y, .R 3, .Y, .R 4, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf434`:
```
Config 1 2 9 22
  H 2 H 11 Y 3 H 10 Y 3 H 9 Y 4 H 2 H 8 Y 3 Y 3 H 1 H 1 Y 1 Y Y 3 Y 1 Y
```
-/
def cf434 : Config :=
  { cfsym := false, cfcontractRef := [1, 2, 9, 22],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 2, .H,
               .R 8, .Y, .R 3, .Y, .R 3, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf435`:
```
Config 11 12 30
  H 9 H 2 H 11 Y 9 H 9 H 1 Y 8 H 1 Y 7 H 1 Y 4 H 1 Y 1 Y Y 3 Y Y 2 Y
```
-/
def cf435 : Config :=
  { cfsym := false, cfcontractRef := [11, 12, 30],
    cfprog := [.H, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y,
               .R 7, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf436`:
```
Config 22
  H 10 H 2 H 12 Y 8 H 10 H 1 Y 9 H 1 Y 9 H 9 Y Y Y 6 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y
```
-/
def cf436 : Config :=
  { cfsym := false, cfcontractRef := [22],
    cfprog := [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 8, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 9, .H, .R 9, .Y, .Y, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 3, .Y,
               .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf437`:
```
Config 28
  H 10 H 2 H 12 Y 10 H 8 H 3 H 11 H 11 Y 9 H 1 Y 9 H 9 Y Y Y Y Y 3 Y 1 Y 1 Y
```
-/
def cf437 : Config :=
  { cfsym := false, cfcontractRef := [28],
    cfprog := [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11,
               .Y, .R 9, .H, .R 1, .Y, .R 9, .H, .R 9, .Y, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1,
               .Y] }

/-- math-comp `cf438`:
```
Config 25
  H 11 H 1 Y 10 H 10 H 1 Y 8 H 2 H 10 Y 4 H 9 Y Y Y Y 4 H 1 H 1 Y 3 Y 1 Y 1 Y
```
-/
def cf438 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10,
               .Y, .R 4, .H, .R 9, .Y, .Y, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y,
               .R 1, .Y] }

/-- math-comp `cf439`:
```
Config 35
  H 3 H 11 H 1 Y 3 H 11 Y 5 H 2 H 10 Y 9 H 1 Y 2 H 8 Y Y 6 H 1 Y 2 Y 1 Y 2 Y 1
  Y
```
-/
def cf439 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 2, .H, .R 10,
               .Y, .R 9, .H, .R 1, .Y, .R 2, .H, .R 8, .Y, .Y, .R 6, .H, .R 1, .Y, .R 2, .Y, .R 1,
               .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf440`:
```
Config 12 28 32 35
  H 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 1 H 8 H 1 Y 8 H 1 Y 1 Y 1 Y 5 Y 2 Y 2 Y 1
  Y
```
-/
def cf440 : Config :=
  { cfsym := false, cfcontractRef := [12, 28, 32, 35],
    cfprog := [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7,
               .H, .R 1, .H, .R 8, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 5, .Y,
               .R 2, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf441`:
```
Config 29
  H 11 H 1 Y 10 H 1 Y 8 H 1 H 9 H 1 Y 8 H 1 H 1 Y 1 Y 1 Y 5 H 1 Y 5 H 1 Y 3 Y 1
  Y 1 Y
```
-/
def cf441 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 1, .H, .R 9, .H, .R 1, .Y,
               .R 8, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 5, .H, .R 1,
               .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf442`:
```
Config 32
  H 2 H 11 Y 5 H 8 H 1 H 1 Y 4 H 9 H 2 H 9 Y 2 H 8 Y Y Y 2 Y 2 H 1 Y 1 Y Y
```
-/
def cf442 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 9, .H,
               .R 2, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .Y, .Y, .R 2, .Y, .R 2, .H, .R 1, .Y, .R 1,
               .Y, .Y] }

/-- math-comp `cf443`:
```
Config 35
  H 2 H 11 Y 3 H 10 Y 6 H 9 H 2 H 9 Y 2 H 8 Y Y 5 H 1 H 1 Y 2 Y 4 H 4 Y Y 1 Y
```
-/
def cf443 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 6, .H, .R 9, .H, .R 2, .H, .R 9, .Y,
               .R 2, .H, .R 8, .Y, .Y, .R 5, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 4, .H, .R 4, .Y,
               .Y, .R 1, .Y] }

/-- math-comp `cf444`:
```
Config 6
  H 11 H 1 Y 3 H 11 Y 6 H 7 H 1 H 1 H 1 Y 3 H 9 Y 2 Y 3 Y 1 Y 1 Y 2 Y 1 Y 1 Y
```
-/
def cf444 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 6, .H, .R 7, .H, .R 1, .H, .R 1, .H,
               .R 1, .Y, .R 3, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1,
               .Y, .R 1, .Y] }

/-- math-comp `cf445`:
```
Config 23
  H 2 H 12 Y 10 H 1 Y 6 H 4 H 10 H 10 H 10 Y 8 H 1 Y 8 Y 6 Y Y Y 3 Y 1 Y 1 Y
```
-/
def cf445 : Config :=
  { cfsym := false, cfcontractRef := [23],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 6, .H, .R 4, .H, .R 10, .H, .R 10,
               .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y,
               .R 1, .Y] }

/-- math-comp `cf446`:
```
Config 8
  H 10 H 1 H 1 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 3 H 9 Y 2 Y 3 Y 1 Y 1 Y 3 Y 3 Y 2 Y
```
-/
def cf446 : Config :=
  { cfsym := false, cfcontractRef := [8],
    cfprog := [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H,
               .R 10, .Y, .R 3, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y,
               .R 3, .Y, .R 2, .Y] }

/-- math-comp `cf447`:
```
Config 8 9 30 32
  H 11 H 1 Y 9 H 2 H 11 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 6 Y Y 4 Y Y Y 2 Y
```
-/
def cf447 : Config :=
  { cfsym := false, cfcontractRef := [8, 9, 30, 32],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10,
               .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .Y, .Y, .R 4, .Y, .Y, .Y, .R 2,
               .Y] }

/-- math-comp `cf448`:
```
Config 32
  H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 8 H 1 Y 8 Y 6 Y Y 3 Y 2 H 1 Y 3 Y 1 Y
```
-/
def cf448 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8,
               .H, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .R 3, .Y, .R 2, .H, .R 1, .Y, .R 3,
               .Y, .R 1, .Y] }

/-- math-comp `cf449`:
```
Config 33
  H 11 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 4 H 8 H 1 Y 2 Y 3 Y 1 Y 2 Y 2 Y 3 Y 2 Y
```
-/
def cf449 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y,
               .R 4, .H, .R 8, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .R 2, .Y, .R 3,
               .Y, .R 2, .Y] }

/-- math-comp `cf450`:
```
Config 30
  H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 1 Y 8 H 8 Y 6 Y Y 2 Y 2 Y 1 Y 1 Y
```
-/
def cf450 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10,
               .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .R 6, .Y, .Y, .R 2, .Y, .R 2, .Y, .R 1,
               .Y, .R 1, .Y] }

/-- math-comp `cf451`:
```
Config 27
  H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 4 H 7 H 1 Y 2 Y 3 Y 1 Y 2 H 1 Y 1 Y Y
```
-/
def cf451 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 4, .H,
               .R 7, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf452`:
```
Config 0 27
  H 2 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 3 H 8 Y 3 H 7 Y 3 Y 1 Y 4 H 4 Y Y 1 Y
```
-/
def cf452 : Config :=
  { cfsym := false, cfcontractRef := [0, 27],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .H,
               .R 8, .Y, .R 3, .H, .R 7, .Y, .R 3, .Y, .R 1, .Y, .R 4, .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf453`:
```
Config 27
  H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 2 H 1 Y 3 Y 1 Y 3 H 1 Y 3 Y 1 Y
```
-/
def cf453 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H,
               .R 8, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 3, .H, .R 1, .Y, .R 3, .Y, .R 1,
               .Y] }

/-- math-comp `cf454`:
```
Config 15 30 33
  H 2 H 12 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 3 H 8 Y 3 Y 1 Y 1 Y 2 Y 1 Y 1 Y
```
-/
def cf454 : Config :=
  { cfsym := false, cfcontractRef := [15, 30, 33],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y,
               .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1,
               .Y, .R 1, .Y] }

/-- math-comp `cf455`:
```
Config 27
  H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 3 H 8 Y 4 Y 1 Y 1 Y 4 H 4 Y Y 1 Y
```
-/
def cf455 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H,
               .R 9, .Y, .R 3, .H, .R 8, .Y, .R 4, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 4, .Y, .Y,
               .R 1, .Y] }

/-- math-comp `cf456`:
```
Config 31
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 8 H 1 Y 8 Y 6 Y 6 H 1 Y 5 H 1 Y 3 Y 1 Y 1 Y
```
-/
def cf456 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 8, .H,
               .R 1, .Y, .R 8, .Y, .R 6, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 3, .Y, .R 1,
               .Y, .R 1, .Y] }

/-- math-comp `cf457`:
```
Config 30
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 5 H 4 H 9 H 9 H 9 Y 8 Y 6 Y Y Y 3 Y 1 Y 1 Y
```
-/
def cf457 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 5, .H, .R 4, .H,
               .R 9, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1,
               .Y] }

/-- math-comp `cf458`:
```
Config 30
  H 10 H 1 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 2 H 1 Y 3 Y 1 Y 1 Y 4 Y 3 Y 1 Y
```
-/
def cf458 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y,
               .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 4, .Y, .R 3,
               .Y, .R 1, .Y] }

/-- math-comp `cf459`:
```
Config 31
  H 10 H 1 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 2 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf459 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H,
               .R 1, .Y, .R 3, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2,
               .Y, .R 1, .Y] }

/-- math-comp `cf460`:
```
Config 16 17 32
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 8 Y 6 Y 4 H 6 Y 2 H 5 Y 3 Y Y Y
```
-/
def cf460 : Config :=
  { cfsym := false, cfcontractRef := [16, 17, 32],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y,
               .R 6, .H, .R 8, .Y, .R 6, .Y, .R 4, .H, .R 6, .Y, .R 2, .H, .R 5, .Y, .R 3, .Y, .Y,
               .Y] }

/-- math-comp `cf461`:
```
Config 31
  H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 4 H 8 H 8 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf461 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H,
               .R 9, .Y, .R 4, .H, .R 8, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2,
               .Y, .R 1, .Y] }

/-- math-comp `cf462`:
```
Config 16 17 32
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 7 H 7 H 7 Y 5 Y 4 H 5 Y Y 1 Y 2 Y
```
-/
def cf462 : Config :=
  { cfsym := false, cfcontractRef := [16, 17, 32],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y,
               .R 7, .H, .R 7, .H, .R 7, .Y, .R 5, .Y, .R 4, .H, .R 5, .Y, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf463`:
```
Config 12 13 32
  H 10 H 1 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 5 H 2 H 7 Y 5 Y 2 H 1 Y 1 Y Y 2 Y
```
-/
def cf463 : Config :=
  { cfsym := false, cfcontractRef := [12, 13, 32],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y,
               .R 5, .H, .R 2, .H, .R 7, .Y, .R 5, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf464`:
```
Config 1 2 32
  H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 2 H 9 Y 2 Y 3 Y 3 H 6 Y Y 1 Y 2 Y 1 Y
```
-/
def cf464 : Config :=
  { cfsym := false, cfcontractRef := [1, 2, 32],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H,
               .R 2, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 3, .H, .R 6, .Y, .Y, .R 1, .Y, .R 2, .Y,
               .R 1, .Y] }

/-- math-comp `cf465`:
```
Config 26
  H 10 H 1 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 3 H 8 Y 2 Y 3 Y 2 H 5 Y 2 Y Y 2 Y
```
-/
def cf465 : Config :=
  { cfsym := false, cfcontractRef := [26],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 7, .H, .R 1, .H, .R 1, .Y,
               .R 3, .H, .R 8, .Y, .R 2, .Y, .R 3, .Y, .R 2, .H, .R 5, .Y, .R 2, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf466`:
```
Config 23
  H 2 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 3 Y 5 Y 1 Y 3 Y Y 2 Y
```
-/
def cf466 : Config :=
  { cfsym := false, cfcontractRef := [23],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4,
               .H, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y,
               .Y, .R 2, .Y] }

/-- math-comp `cf467`:
```
Config 32
  H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 8 Y 6 Y 4 H 6 Y Y 1 Y 2 Y 1 Y
```
-/
def cf467 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8,
               .H, .R 1, .Y, .R 7, .H, .R 8, .Y, .R 6, .Y, .R 4, .H, .R 6, .Y, .Y, .R 1, .Y, .R 2,
               .Y, .R 1, .Y] }

/-- math-comp `cf468`:
```
Config 33
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 4 H 1 Y 3 Y 4 H 6 H 6 Y 3 Y 1 Y Y Y
```
-/
def cf468 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9,
               .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 4, .H, .R 6, .H, .R 6, .Y, .R 3, .Y, .R 1, .Y,
               .Y, .Y] }

/-- math-comp `cf469`:
```
Config 1 2 13 23
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 4 H 1 Y 3 Y 3 H 1 H 1 Y 1 Y Y 3 Y 1 Y
```
-/
def cf469 : Config :=
  { cfsym := false, cfcontractRef := [1, 2, 13, 23],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9,
               .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 3, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3,
               .Y, .R 1, .Y] }

/-- math-comp `cf470`:
```
Config 11 12 33
  H 10 H 2 H 12 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 5 Y 1 Y 3 Y Y 3 Y Y
```
-/
def cf470 : Config :=
  { cfsym := false, cfcontractRef := [11, 12, 33],
    cfprog := [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1,
               .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 3,
               .Y, .Y] }

/-- math-comp `cf471`:
```
Config 19 20 33
  H 11 H 1 Y 4 H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 1 Y 4 Y Y 3 H 1 Y 1 Y Y Y
```
-/
def cf471 : Config :=
  { cfsym := false, cfcontractRef := [19, 20, 33],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3,
               .H, .R 9, .Y, .R 3, .H, .R 1, .Y, .R 4, .Y, .Y, .R 3, .H, .R 1, .Y, .R 1, .Y, .Y,
               .Y] }

/-- math-comp `cf472`:
```
Config 33
  H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 2 H 1 H 1 H 1 Y 6 Y 1 Y 1 Y 3 Y Y 1 Y 1 Y
```
-/
def cf472 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y,
               .R 2, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y,
               .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf473`:
```
Config 18
  H 11 H 1 Y 7 H 10 H 1 Y 9 H 1 Y 9 Y 7 H 8 H 8 H 8 H 8 Y Y 1 Y 4 Y Y Y Y
```
-/
def cf473 : Config :=
  { cfsym := false, cfcontractRef := [18],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 7, .H, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y,
               .R 7, .H, .R 8, .H, .R 8, .H, .R 8, .H, .R 8, .Y, .Y, .R 1, .Y, .R 4, .Y, .Y, .Y,
               .Y] }

/-- math-comp `cf474`:
```
Config 21
  H 2 H 12 Y 10 H 1 Y 9 H 6 H 4 H 10 H 10 H 10 Y 9 Y 6 H 1 Y 7 Y 1 Y 3 Y 1 Y 2 Y
  Y
```
-/
def cf474 : Config :=
  { cfsym := false, cfcontractRef := [21],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 6, .H, .R 4, .H, .R 10,
               .H, .R 10, .H, .R 10, .Y, .R 9, .Y, .R 6, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .R 3, .Y,
               .R 1, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf475`:
```
Config 8 33 36
  H 9 H 3 H 12 H 12 Y 10 H 1 Y 9 H 9 H 1 Y 8 H 1 Y 3 H 8 Y 3 Y Y Y 3 Y 1 Y Y
```
-/
def cf475 : Config :=
  { cfsym := false, cfcontractRef := [8, 33, 36],
    cfprog := [.H, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9,
               .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .Y, .Y, .R 3, .Y,
               .R 1, .Y, .Y] }

/-- math-comp `cf476`:
```
Config 33
  H 3 H 12 H 12 Y 10 H 1 Y 5 H 5 H 10 H 10 H 10 H 10 Y 9 Y 7 Y Y Y Y 3 Y 1 Y 1 Y
```
-/
def cf476 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 5, .H, .R 5, .H, .R 10,
               .H, .R 10, .H, .R 10, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1,
               .Y, .R 1, .Y] }

/-- math-comp `cf477`:
```
Config 33 36
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 7 H 1 H 1 Y 7 Y 4 H 7 Y Y 1 Y 2 Y 2 Y Y
```
-/
def cf477 : Config :=
  { cfsym := false, cfcontractRef := [33, 36],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H,
               .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .R 4, .H, .R 7, .Y, .Y, .R 1, .Y, .R 2, .Y,
               .R 2, .Y, .Y] }

/-- math-comp `cf478`:
```
Config 30 32 36
  H 2 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 4 H 9 H 9 Y 8 Y 5 H 7 H 7 Y Y 1 Y 2 Y 1 Y 1 Y
```
-/
def cf478 : Config :=
  { cfsym := false, cfcontractRef := [30, 32, 36],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4,
               .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 5, .H, .R 7, .H, .R 7, .Y, .Y, .R 1, .Y, .R 2,
               .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf479`:
```
Config 15 16 33
  H 11 H 1 Y 4 H 10 H 1 Y 3 H 3 H 9 H 1 Y 2 H 1 Y 5 H 8 Y Y 1 Y 3 Y 1 Y 3 Y 2 Y
```
-/
def cf479 : Config :=
  { cfsym := false, cfcontractRef := [15, 16, 33],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 3, .H, .R 9, .H,
               .R 1, .Y, .R 2, .H, .R 1, .Y, .R 5, .H, .R 8, .Y, .Y, .R 1, .Y, .R 3, .Y, .R 1, .Y,
               .R 3, .Y, .R 2, .Y] }

/-- math-comp `cf480`:
```
Config 20 24 36
  H 2 H 12 Y 9 H 2 H 11 Y 9 H 7 H 3 H 10 H 10 Y 9 Y 5 H 1 Y 1 Y Y 3 Y 1 Y 2 Y Y
```
-/
def cf480 : Config :=
  { cfsym := false, cfcontractRef := [20, 24, 36],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 7, .H, .R 3, .H,
               .R 10, .H, .R 10, .Y, .R 9, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .R 1, .Y,
               .R 2, .Y, .Y] }

/-- math-comp `cf481`:
```
Config 35
  H 11 H 1 Y 10 H 1 Y 9 H 1 Y 5 H 1 H 1 H 1 H 1 Y 5 H 1 Y 1 Y Y 3 Y Y 3 Y Y
```
-/
def cf481 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 5, .H, .R 1, .H,
               .R 1, .H, .R 1, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3, .Y, .Y, .R 3,
               .Y, .Y] }

/-- math-comp `cf482`:
```
Config 30
  H 10 H 1 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 3 H 1 Y 3 H 1 Y 1 Y Y 2 H 1 Y 1 Y Y
```
-/
def cf482 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y,
               .R 3, .H, .R 1, .Y, .R 3, .H, .R 1, .Y, .R 1, .Y, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y,
               .Y] }

/-- math-comp `cf483`:
```
Config 32
  H 9 H 1 H 1 H 1 Y 3 H 11 Y 6 H 7 H 1 H 1 H 1 Y 2 Y 4 Y Y 5 Y 1 Y Y Y Y
```
-/
def cf483 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 9, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 6, .H, .R 7, .H,
               .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 5, .Y, .R 1, .Y, .Y, .Y,
               .Y] }

/-- math-comp `cf484`:
```
Config 23
  H 10 H 1 Y 8 H 9 H 1 Y 7 H 2 H 9 Y 8 Y 3 Y Y 3 H 5 H 1 H 1 Y 1 Y Y Y
```
-/
def cf484 : Config :=
  { cfsym := false, cfcontractRef := [23],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y,
               .R 8, .Y, .R 3, .Y, .Y, .R 3, .H, .R 5, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .Y] }

/-- math-comp `cf485`:
```
Config 30
  H 8 H 3 H 11 H 11 Y 9 H 9 H 1 Y 8 H 1 Y 8 Y 4 H 7 Y Y 1 Y 2 H 1 Y 1 Y Y
```
-/
def cf485 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 8, .H,
               .R 1, .Y, .R 8, .Y, .R 4, .H, .R 7, .Y, .Y, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y,
               .Y] }

/-- math-comp `cf486`:
```
Config 36
  H 11 H 2 H 13 Y 8 H 11 H 1 Y 10 H 1 Y 10 H 10 Y Y Y 6 H 1 H 1 Y 5 H 1 Y 1 Y 3
  Y 1 Y 1 Y
```
-/
def cf486 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 11, .H, .R 2, .H, .R 13, .Y, .R 8, .H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1,
               .Y, .R 10, .H, .R 10, .Y, .Y, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 5, .H, .R 1, .Y,
               .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf487`:
```
Config 36
  H 9 H 4 H 13 H 13 H 13 Y 11 H 1 Y 10 H 10 H 1 Y 10 H 1 Y 9 H 1 Y 1 Y 1 Y 6 Y Y
  3 Y 1 Y 1 Y
```
-/
def cf487 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 9, .H, .R 4, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10,
               .H, .R 10, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y,
               .R 6, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf488`:
```
Config 10 11 40
  H 10 H 3 H 13 H 13 Y 11 H 1 Y 10 H 1 Y 8 H 1 H 9 H 1 Y 9 H 1 Y 1 Y 1 Y 6 Y Y 3
  Y 1 Y 1 Y
```
-/
def cf488 : Config :=
  { cfsym := false, cfcontractRef := [10, 11, 40],
    cfprog := [.H, .R 10, .H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1,
               .Y, .R 8, .H, .R 1, .H, .R 9, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y,
               .R 6, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf489`:
```
Config 8 31 35 37
  H 11 H 2 H 13 Y 11 H 1 Y 9 H 2 H 11 Y 8 H 1 H 9 H 1 Y 9 H 1 Y 1 Y 1 Y 6 Y 2 Y
  2 Y 1 Y 1 Y
```
-/
def cf489 : Config :=
  { cfsym := false, cfcontractRef := [8, 31, 35, 37],
    cfprog := [.H, .R 11, .H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11,
               .Y, .R 8, .H, .R 1, .H, .R 9, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y,
               .R 6, .Y, .R 2, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf490`:
```
Config 19
  H 2 H 13 Y 4 H 2 H 12 Y 4 H 10 H 1 Y 4 H 1 Y 8 H 1 H 1 Y 1 Y 2 H 7 Y 2 Y Y 3 Y
  1 Y Y
```
-/
def cf490 : Config :=
  { cfsym := false, cfcontractRef := [19],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 4, .H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1,
               .Y, .R 4, .H, .R 1, .Y, .R 8, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 2, .H, .R 7, .Y,
               .R 2, .Y, .Y, .R 3, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf491`:
```
Config 6
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 8 Y 4 H 2 H 7 Y H 1 Y 4 H 5 Y 3 H 4 Y Y 1 Y
```
-/
def cf491 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 8, .Y,
               .R 4, .H, .R 2, .H, .R 7, .Y, .H, .R 1, .Y, .R 4, .H, .R 5, .Y, .R 3, .H, .R 4, .Y,
               .Y, .R 1, .Y] }

/-- math-comp `cf492`:
```
Config 34
  H 9 H 1 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 2 H 1 Y 2 H 1 Y 4 Y 1 Y 3 Y 1 Y Y
```
-/
def cf492 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 9, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y,
               .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 3,
               .Y, .R 1, .Y, .Y] }

/-- math-comp `cf493`:
```
Config 26 27 37
  H 10 H 3 H 13 H 13 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 Y Y Y 4 Y 2 Y 3 Y
  Y
```
-/
def cf493 : Config :=
  { cfsym := false, cfcontractRef := [26, 27, 37],
    cfprog := [.H, .R 10, .H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1,
               .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .Y, .Y, .R 4, .Y,
               .R 2, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf494`:
```
Config 37
  H 2 H 13 Y 3 H 12 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 2 H 8 Y 2 Y 3 Y 1 Y 2 Y Y
  2 Y
```
-/
def cf494 : Config :=
  { cfsym := false, cfcontractRef := [37],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8,
               .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .R 2, .Y, .R 3, .Y,
               .R 1, .Y, .R 2, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf495`:
```
Config 37
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 8 H 8 Y 2 Y 3 Y Y 3 Y Y 2
  Y
```
-/
def cf495 : Config :=
  { cfsym := false, cfcontractRef := [37],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 8, .H, .R 8, .Y, .R 2, .Y, .R 3, .Y,
               .Y, .R 3, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf496`:
```
Config 35
  H 2 H 13 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 2 H 1 H 1 H 1 Y 5 Y 1 Y 1 Y 2 Y
  1 Y 1 Y
```
-/
def cf496 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10,
               .Y, .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y,
               .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf497`:
```
Config 8
  H 11 H 1 H 1 Y 5 H 10 H 1 H 1 Y 4 H 10 H 1 Y 3 H 10 Y 2 Y 3 Y 1 Y 1 Y 3 Y 4 Y
  2 Y 1 Y
```
-/
def cf497 : Config :=
  { cfsym := false, cfcontractRef := [8],
    cfprog := [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 5, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 4, .H,
               .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y,
               .R 3, .Y, .R 4, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf498`:
```
Config 29 34 36
  H 3 H 12 H 1 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 4 H 8 H 1 Y 2 H 1 Y 1 Y 6 Y 5 Y 3 Y
  1 Y 2 Y
```
-/
def cf498 : Config :=
  { cfsym := false, cfcontractRef := [29, 34, 36],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3,
               .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 1, .Y, .R 6, .Y,
               .R 5, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf499`:
```
Config 36
  H 11 H 1 H 1 Y 5 H 10 H 1 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 2 Y 3 Y 1 Y 6 Y 3 Y 3 Y 3
  Y 1 Y
```
-/
def cf499 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 5, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H,
               .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 6, .Y,
               .R 3, .Y, .R 3, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf500`:
```
Config 34 37
  H 12 H 1 Y 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 9 H 9 Y 3 H 8 Y 3 Y Y Y 4 Y Y Y
```
-/
def cf500 : Config :=
  { cfsym := false, cfcontractRef := [34, 37],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9,
               .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .Y, .Y,
               .R 4, .Y, .Y, .Y] }

/-- math-comp `cf501`:
```
Config 33
  H 12 H 1 Y 11 H 1 Y 8 H 3 H 11 H 11 Y 8 H 2 H 10 Y 8 H 1 Y 7 Y Y Y 3 Y 1 Y 1 Y
  1 Y
```
-/
def cf501 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 8, .H, .R 3, .H, .R 11, .H, .R 11,
               .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .Y, .Y, .Y, .R 3, .Y,
               .R 1, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf502`:
```
Config 34
  H 11 H 1 H 1 Y 3 H 12 Y 6 H 8 H 1 H 1 H 1 Y 3 H 10 Y 2 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1
  Y 1 Y
```
-/
def cf502 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 6, .H, .R 8, .H, .R 1, .H,
               .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y,
               .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf503`:
```
Config 34
  H 3 H 13 H 13 Y 11 H 1 Y 7 H 4 H 11 H 11 H 11 Y 9 H 1 Y 9 Y 7 Y Y Y Y 3 Y 1 Y
  1 Y
```
-/
def cf503 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 7, .H, .R 4, .H, .R 11,
               .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 7, .Y, .Y, .Y, .Y, .R 3,
               .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf504`:
```
Config 35
  H 11 H 1 H 1 Y 3 H 12 Y 3 H 11 Y 3 H 3 H 9 H 1 Y 2 Y 3 Y 3 H 1 Y 5 Y 1 Y 1 Y 2
  Y 1 Y
```
-/
def cf504 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3,
               .H, .R 3, .H, .R 9, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 3, .H, .R 1, .Y, .R 5, .Y,
               .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf505`:
```
Config 8
  H 11 H 1 H 1 Y 4 H 11 H 1 Y 3 H 2 H 11 Y 3 H 10 Y 2 Y 3 Y 3 H 7 Y Y 1 Y 3 Y 3
  Y 2 Y
```
-/
def cf505 : Config :=
  { cfsym := false, cfcontractRef := [8],
    cfprog := [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 2, .H,
               .R 11, .Y, .R 3, .H, .R 10, .Y, .R 2, .Y, .R 3, .Y, .R 3, .H, .R 7, .Y, .Y, .R 1, .Y,
               .R 3, .Y, .R 3, .Y, .R 2, .Y] }

/-- math-comp `cf506`:
```
Config 36
  H 2 H 13 Y 4 H 11 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 3 Y 2 Y 4 Y Y 3 Y 3 Y
  Y
```
-/
def cf506 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 4, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5,
               .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 3, .Y, .R 2, .Y, .R 4, .Y,
               .Y, .R 3, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf507`:
```
Config 37
  H 11 H 1 H 1 Y 3 H 12 Y 3 H 11 Y 3 H 3 H 9 H 1 Y 2 Y 3 Y 3 H 7 Y 4 Y 1 Y Y Y
  Y
```
-/
def cf507 : Config :=
  { cfsym := false, cfcontractRef := [37],
    cfprog := [.H, .R 11, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3,
               .H, .R 3, .H, .R 9, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 3, .H, .R 7, .Y, .R 4, .Y,
               .R 1, .Y, .Y, .Y, .Y] }

/-- math-comp `cf508`:
```
Config 6
  H 10 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 H 1 Y 3 Y 3 H 2 H 5 Y H 1 Y 3 Y 1 Y
```
-/
def cf508 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y,
               .R 3, .H, .R 1, .Y, .R 3, .Y, .R 3, .H, .R 2, .H, .R 5, .Y, .H, .R 1, .Y, .R 3, .Y,
               .R 1, .Y] }

/-- math-comp `cf509`:
```
Config 35
  H 12 H 1 Y 3 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 4 H 1 Y 3 Y 4 H 1 H 1 Y 1 Y Y 3 Y 1
  Y 1 Y
```
-/
def cf509 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3,
               .H, .R 10, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .R 1, .Y,
               .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf510`:
```
Config 8 9 30 37
  H 12 H 1 Y 11 H 10 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 9 Y 4 Y Y Y 3 H 1 Y 1 Y Y
  Y
```
-/
def cf510 : Config :=
  { cfsym := false, cfcontractRef := [8, 9, 30, 37],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1,
               .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 4, .Y, .Y, .Y, .R 3, .H, .R 1, .Y,
               .R 1, .Y, .Y, .Y] }

/-- math-comp `cf511`:
```
Config 21 25 37
  H 2 H 13 Y 11 H 1 Y 10 H 1 Y 9 H 7 H 3 H 10 H 10 Y 9 Y 5 H 1 Y 1 Y Y 3 Y 1 Y 2
  Y Y
```
-/
def cf511 : Config :=
  { cfsym := false, cfcontractRef := [21, 25, 37],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 7,
               .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 9, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 3,
               .Y, .R 1, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf512`:
```
Config 31
  H 10 H 2 H 12 Y 10 H 1 Y 9 H 9 H 1 Y 8 H 1 Y 8 Y 4 H 7 Y Y 1 Y 3 H 1 Y 3 Y 1
  Y
```
-/
def cf512 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 1,
               .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 4, .H, .R 7, .Y, .Y, .R 1, .Y, .R 3, .H, .R 1,
               .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf513`:
```
Config 37 39
  H 2 H 13 Y 4 H 11 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 1 Y 8 H 8 Y Y 1 Y 4 Y 4 Y
  1 Y 2 Y
```
-/
def cf513 : Config :=
  { cfsym := false, cfcontractRef := [37, 39],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 4, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5,
               .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .Y, .R 1,
               .Y, .R 4, .Y, .R 4, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf514`:
```
Config 36
  H 2 H 12 Y 5 H 9 H 1 H 1 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 4 H 1 Y 7 Y 1 Y 4 Y Y 1 Y
  Y
```
-/
def cf514 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 5, .H, .R 8, .H,
               .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 4, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .R 4,
               .Y, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf515`:
```
Config 34
  H 2 H 12 Y 3 H 11 Y 4 H 2 H 10 Y 3 H 9 Y 6 H 1 H 8 H 8 Y Y 1 Y 1 Y 4 H 4 Y Y 1
  Y
```
-/
def cf515 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 3,
               .H, .R 9, .Y, .R 6, .H, .R 1, .H, .R 8, .H, .R 8, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 4,
               .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf516`:
```
Config 37
  H 12 H 1 Y 11 H 1 Y 10 H 8 H 3 H 11 H 11 Y 2 H 10 Y 8 H 1 H 1 Y 1 Y 1 Y 1 Y 4
  H 1 Y 3 Y 1 Y 1 Y
```
-/
def cf516 : Config :=
  { cfsym := false, cfcontractRef := [37],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 8, .H, .R 3, .H, .R 11,
               .H, .R 11, .Y, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y,
               .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf517`:
```
Config 37
  H 12 H 1 Y 11 H 1 Y 8 H 10 H 1 Y 2 H 1 H 10 H 10 Y 8 H 1 H 1 Y 1 Y 1 Y 1 Y 4 H
  1 Y 3 Y 1 Y 1 Y
```
-/
def cf517 : Config :=
  { cfsym := false, cfcontractRef := [37],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 8, .H, .R 10, .H, .R 1, .Y, .R 2,
               .H, .R 1, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .R 1, .Y,
               .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf518`:
```
Config 25
  H 11 H 1 Y 9 H 10 H 1 Y 8 H 1 H 9 H 1 Y 2 H 9 Y Y Y 4 H 1 H 1 H 1 Y H 5 Y 4 Y
  1 Y 1 Y
```
-/
def cf518 : Config :=
  { cfsym := false, cfcontractRef := [25],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 1, .H, .R 9, .H,
               .R 1, .Y, .R 2, .H, .R 9, .Y, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .H,
               .R 5, .Y, .R 4, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf519`:
```
Config 6
  H 12 H 1 Y 3 H 12 Y 7 H 7 H 1 H 1 H 1 H 1 Y 3 H 10 Y 2 Y 4 H 1 Y 7 Y 1 Y 3 Y 4
  Y 2 Y 1 Y
```
-/
def cf519 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 7, .H, .R 7, .H, .R 1, .H, .R 1, .H,
               .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 2, .Y, .R 4, .H, .R 1, .Y, .R 7, .Y,
               .R 1, .Y, .R 3, .Y, .R 4, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf520`:
```
Config 1 2 31
  H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 7 H 2 H 9 Y 8 Y 6 Y Y Y 3 Y 1 Y 1 Y
```
-/
def cf520 : Config :=
  { cfsym := false, cfcontractRef := [1, 2, 31],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10,
               .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y,
               .R 1, .Y] }

/-- math-comp `cf521`:
```
Config 2 31
  H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 7 H 2 H 9 Y 8 Y 6 Y Y 2 Y 3 Y Y 1 Y
```
-/
def cf521 : Config :=
  { cfsym := false, cfcontractRef := [2, 31],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10,
               .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .R 2, .Y, .R 3, .Y, .Y,
               .R 1, .Y] }

/-- math-comp `cf522`:
```
Config 31
  H 2 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 2 H 9 Y 3 H 8 Y 3 Y 3 H 6 Y Y 1 Y 2 Y 1 Y
```
-/
def cf522 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 2,
               .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 3, .H, .R 6, .Y, .Y, .R 1, .Y, .R 2,
               .Y, .R 1, .Y] }

/-- math-comp `cf523`:
```
Config 34
  H 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 6 H 1 H 1 Y H 6 Y 2 Y Y 3 Y Y
```
-/
def cf523 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 7, .H,
               .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .H, .R 6, .Y, .R 2, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf524`:
```
Config 3 36
  H 3 H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 4 H 8 H 1 Y 2 H 8 Y Y 2 Y 1 Y 2 Y 1 Y 2 Y
```
-/
def cf524 : Config :=
  { cfsym := false, cfcontractRef := [3, 36],
    cfprog := [.H, .R 3, .H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y,
               .R 4, .H, .R 8, .H, .R 1, .Y, .R 2, .H, .R 8, .Y, .Y, .R 2, .Y, .R 1, .Y, .R 2, .Y,
               .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf525`:
```
Config 35
  H 2 H 12 Y 3 H 11 Y 3 H 2 H 10 Y 5 H 7 H 1 H 1 Y 7 Y 1 Y 6 H 6 Y 2 Y Y 3 Y Y
```
-/
def cf525 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 2, .H, .R 10, .Y, .R 5,
               .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y, .R 6, .H, .R 6, .Y, .R 2, .Y,
               .Y, .R 3, .Y, .Y] }

/-- math-comp `cf526`:
```
Config 34
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 5 H 1 H 1 H 2 H 9 Y 6 Y 1 Y Y Y 4 Y Y Y
```
-/
def cf526 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 5, .H,
               .R 1, .H, .R 1, .H, .R 2, .H, .R 9, .Y, .R 6, .Y, .R 1, .Y, .Y, .Y, .R 4, .Y, .Y,
               .Y] }

/-- math-comp `cf527`:
```
Config 27
  H 2 H 12 Y 4 H 2 H 11 Y 5 H 8 H 1 H 1 Y 2 Y 6 Y 1 Y 1 Y 4 H 5 Y 2 H 4 Y Y 1 Y
```
-/
def cf527 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 4, .H, .R 2, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H,
               .R 1, .Y, .R 2, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 5, .Y, .R 2, .H, .R 4,
               .Y, .Y, .R 1, .Y] }

/-- math-comp `cf528`:
```
Config 31
  H 10 H 1 Y 3 H 10 Y 4 H 2 H 9 Y 2 H 1 Y 5 H 7 H 7 Y 1 H 1 Y 2 Y Y Y 2 Y
```
-/
def cf528 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 2, .H, .R 9, .Y, .R 2, .H,
               .R 1, .Y, .R 5, .H, .R 7, .H, .R 7, .Y, .R 1, .H, .R 1, .Y, .R 2, .Y, .Y, .Y, .R 2,
               .Y] }

/-- math-comp `cf529`:
```
Config* 35
  H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 5 H 9 H 9 H 9 Y 4 Y Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf529 : Config :=
  { cfsym := true, cfcontractRef := [35],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y,
               .R 5, .H, .R 9, .H, .R 9, .H, .R 9, .Y, .R 4, .Y, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y,
               .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf530`:
```
Config 35
  H 11 H 1 Y 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 7 H 1 Y 7 H 1 Y H 6 Y 2 Y Y 3 Y Y
```
-/
def cf530 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8,
               .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .H, .R 6, .Y, .R 2, .Y, .Y,
               .R 3, .Y, .Y] }

/-- math-comp `cf531`:
```
Config 34
  H 3 H 13 H 13 Y 11 H 1 Y 10 H 1 Y 8 H 9 H 1 Y 9 Y 7 Y 6 H 1 Y 6 H 1 Y 4 Y Y 1
  Y 1 Y
```
-/
def cf531 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8,
               .H, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 7, .Y, .R 6, .H, .R 1, .Y, .R 6, .H, .R 1, .Y,
               .R 4, .Y, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf532`:
```
Config 37
  H 12 H 1 Y 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 6 H 1 H 1 H 1 Y 6 Y 1 Y Y Y 4 Y Y Y
```
-/
def cf532 : Config :=
  { cfsym := false, cfcontractRef := [37],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9,
               .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .Y, .Y,
               .R 4, .Y, .Y, .Y] }

/-- math-comp `cf533`:
```
Config 12 33 37
  H 2 H 13 Y 3 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 2 H 1 H 1 H 1 Y 6 Y 1 Y 1 Y 3 Y Y 1
  Y 1 Y
```
-/
def cf533 : Config :=
  { cfsym := false, cfcontractRef := [12, 33, 37],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3,
               .H, .R 10, .Y, .R 2, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y,
               .R 3, .Y, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf534`:
```
Config 13 20 30
  H 4 H 13 H 13 H 13 Y 11 H 1 Y 10 H 1 Y 9 H 9 H 1 Y 9 Y 6 Y 1 Y 5 H 1 Y 4 Y Y 1
  Y 1 Y
```
-/
def cf534 : Config :=
  { cfsym := false, cfcontractRef := [13, 20, 30],
    cfprog := [.H, .R 4, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1,
               .Y, .R 9, .H, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 6, .Y, .R 1, .Y, .R 5, .H, .R 1, .Y,
               .R 4, .Y, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf535`:
```
Config 7
  H 3 H 13 H 13 Y 9 H 3 H 12 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 9 Y 7 Y Y Y 3 Y 1 Y 2
  Y Y
```
-/
def cf535 : Config :=
  { cfsym := false, cfcontractRef := [7],
    cfprog := [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10,
               .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .Y, .Y, .R 3, .Y,
               .R 1, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf536`:
```
Config 35
  H 11 H 2 H 13 Y 10 H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 8 H 8 Y Y Y Y 2 Y 2 Y 1
  Y
```
-/
def cf536 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 11, .H, .R 2, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1,
               .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .R 2, .Y,
               .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf537`:
```
Config 6
  H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 6 H 3 H 9 H 9 Y 8 Y 6 Y Y 3 Y 2 H 4 Y 2 Y Y
```
-/
def cf537 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 6,
               .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .R 3, .Y, .R 2, .H, .R 4,
               .Y, .R 2, .Y, .Y] }

/-- math-comp `cf538`:
```
Config 33
  H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 3 H 9 Y 3 H 8 Y 3 Y 1 Y 2 Y 3 H 4 Y Y 1 Y
```
-/
def cf538 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y,
               .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .R 3, .H, .R 4,
               .Y, .Y, .R 1, .Y] }

/-- math-comp `cf539`:
```
Config 6
  H 11 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 2 H 1 Y 3 Y 1 Y 2 Y 2 H 1 Y 3 Y 1
  Y
```
-/
def cf539 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y,
               .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 2, .Y, .R 2, .H, .R 1,
               .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf540`:
```
Config 35
  H 10 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 5 H 7 H 1 H 1 Y 2 Y 3 Y 3 H 1 Y 4 Y 1 Y 1 Y 2
  Y
```
-/
def cf540 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 5,
               .H, .R 7, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 3, .H, .R 1, .Y, .R 4, .Y,
               .R 1, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf541`:
```
Config 37
  H 12 H 1 Y 10 H 2 H 12 Y 10 H 1 Y 8 H 2 H 10 Y 7 H 2 H 9 Y 7 Y 4 Y Y Y 3 Y 1 Y
  Y
```
-/
def cf541 : Config :=
  { cfsym := false, cfcontractRef := [37],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8,
               .H, .R 2, .H, .R 10, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .Y, .R 4, .Y, .Y, .Y,
               .R 3, .Y, .R 1, .Y, .Y] }

/-- math-comp `cf542`:
```
Config 34
  H 3 H 12 H 1 Y 3 H 12 Y 4 H 10 H 1 Y 3 H 10 Y 4 H 9 H 9 Y 3 Y 2 Y Y 1 Y 1 Y 2
  Y 1 Y
```
-/
def cf542 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1,
               .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 9, .Y, .R 3, .Y, .R 2, .Y, .Y, .R 1,
               .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf543`:
```
Config 34
  H 12 H 1 Y 11 H 1 Y 10 H 10 H 1 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y 6 H 1 Y 1 Y Y 3 Y Y
  2 Y
```
-/
def cf543 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 9,
               .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .R 6, .H, .R 1, .Y, .R 1, .Y,
               .Y, .R 3, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf544`:
```
Config 34
  H 10 H 1 H 1 H 1 Y 3 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 2 Y 4 Y Y 1 Y 1 Y 1 Y 2 Y
  1 Y
```
-/
def cf544 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 10, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 9, .H,
               .R 1, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 2, .Y, .R 4, .Y, .Y, .R 1, .Y, .R 1, .Y,
               .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf545`:
```
Config 4 5 36
  H 4 H 10 H 1 H 1 Y 3 H 11 Y 3 H 10 Y 4 H 8 H 1 Y 2 Y 6 Y 1 Y 4 H 5 Y Y 1 Y 2
  Y
```
-/
def cf545 : Config :=
  { cfsym := false, cfcontractRef := [4, 5, 36],
    cfprog := [.H, .R 4, .H, .R 10, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10,
               .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 2, .Y, .R 6, .Y, .R 1, .Y, .R 4, .H, .R 5, .Y,
               .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf546`:
```
Config 36
  H 5 H 13 H 13 H 13 H 13 Y 11 H 1 Y 7 H 4 H 11 H 11 H 11 Y 10 Y 6 Y 1 Y 1 Y 3 Y
  1 Y Y 1 Y 1 Y
```
-/
def cf546 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 5, .H, .R 13, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 7,
               .H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 10, .Y, .R 6, .Y, .R 1, .Y, .R 1,
               .Y, .R 3, .Y, .R 1, .Y, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf547`:
```
Config 34
  H 12 H 1 Y 11 H 11 H 1 Y 8 H 3 H 11 H 11 Y 8 H 2 H 10 Y 7 H 1 Y 7 Y 1 Y 1 Y 4
  Y Y Y 2 Y
```
-/
def cf547 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 11, .H, .R 1, .Y, .R 8, .H, .R 3, .H, .R 11,
               .H, .R 11, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 7, .H, .R 1, .Y, .R 7, .Y, .R 1, .Y,
               .R 1, .Y, .R 4, .Y, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf548`:
```
Config 38
  H 2 H 13 Y 6 H 9 H 1 H 1 H 1 Y 3 H 11 Y 5 H 10 H 10 H 10 Y 4 Y Y 1 Y 1 Y 1 Y 2
  Y 1 Y 1 Y
```
-/
def cf548 : Config :=
  { cfsym := false, cfcontractRef := [38],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 6, .H, .R 9, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H,
               .R 11, .Y, .R 5, .H, .R 10, .H, .R 10, .H, .R 10, .Y, .R 4, .Y, .Y, .R 1, .Y, .R 1,
               .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf549`:
```
Config 33
  H 4 H 13 H 13 H 13 Y 11 H 1 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 9 Y 6 Y 1 Y 3 Y Y 2 H
  1 Y 3 Y 1 Y
```
-/
def cf549 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 4, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1,
               .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 9, .Y, .R 6, .Y, .R 1, .Y, .R 3, .Y,
               .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf550`:
```
Config 38
  H 2 H 13 Y 11 H 1 Y 10 H 1 Y 7 H 9 H 1 Y 9 Y 7 Y 7 H 7 H 7 H 2 H 7 Y 2 Y Y 3 Y
  1 Y 1 Y
```
-/
def cf550 : Config :=
  { cfsym := false, cfcontractRef := [38],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 9,
               .H, .R 1, .Y, .R 9, .Y, .R 7, .Y, .R 7, .H, .R 7, .H, .R 7, .H, .R 2, .H, .R 7, .Y,
               .R 2, .Y, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf551`:
```
Config 6
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 8 Y 6 Y 4 H 1 H 1 H 1 Y H 5 Y 4 Y 1 Y
  1 Y
```
-/
def cf551 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y,
               .R 6, .H, .R 8, .Y, .R 6, .Y, .R 4, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .H, .R 5, .Y,
               .R 4, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf552`:
```
Config 19 20 40
  H 2 H 13 Y 3 H 12 Y 4 H 10 H 1 Y 6 H 7 H 1 H 1 H 1 Y 2 Y 8 H 8 Y 7 Y 1 Y 1 Y 3
  Y Y 2 Y
```
-/
def cf552 : Config :=
  { cfsym := false, cfcontractRef := [19, 20, 40],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 6,
               .H, .R 7, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 8, .H, .R 8, .Y, .R 7, .Y,
               .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf553`:
```
Config 36
  H 4 H 13 H 13 H 13 Y 11 H 1 Y 6 H 5 H 11 H 11 H 11 H 11 Y 10 Y 6 Y 1 Y 1 Y 6 H
  6 Y 5 Y Y 1 Y 1 Y
```
-/
def cf553 : Config :=
  { cfsym := false, cfcontractRef := [36],
    cfprog := [.H, .R 4, .H, .R 13, .H, .R 13, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 6, .H, .R 5,
               .H, .R 11, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 10, .Y, .R 6, .Y, .R 1, .Y, .R 1,
               .Y, .R 6, .H, .R 6, .Y, .R 5, .Y, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf554`:
```
Config 40
  H 12 H 1 Y 11 H 1 Y 10 H 1 Y 9 H 1 Y 5 H 1 H 3 H 9 H 9 Y 2 H 8 Y 7 H 1 Y 1 Y 2
  Y 3 Y Y 1 Y
```
-/
def cf554 : Config :=
  { cfsym := false, cfcontractRef := [40],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1,
               .Y, .R 5, .H, .R 1, .H, .R 3, .H, .R 9, .H, .R 9, .Y, .R 2, .H, .R 8, .Y, .R 7, .H,
               .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 3, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf555`:
```
Config 37
  H 12 H 1 Y 9 H 3 H 12 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y 7 H 7 Y 2 Y Y 3
  Y Y 2 Y
```
-/
def cf555 : Config :=
  { cfsym := false, cfcontractRef := [37],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 9, .H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1,
               .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .R 7, .H, .R 7, .Y,
               .R 2, .Y, .Y, .R 3, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf556`:
```
Config 30
  H 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 1 Y 6 H 2 H 8 Y 6 Y Y Y 4 Y Y Y
```
-/
def cf556 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10, .Y, .R 8, .H, .R 1,
               .Y, .R 6, .H, .R 2, .H, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 4, .Y, .Y, .Y] }

/-- math-comp `cf557`:
```
Config 10 31
  H 10 H 1 Y 8 H 9 H 1 Y 8 H 1 Y 7 H 1 Y 5 H 1 Y 6 H 1 Y 5 Y 1 Y 3 Y Y
```
-/
def cf557 : Config :=
  { cfsym := false, cfcontractRef := [10, 31],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 7, .H,
               .R 1, .Y, .R 5, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 5, .Y, .R 1, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf558`:
```
Config 27
  H 11 H 1 Y 8 H 3 H 11 H 11 Y 9 H 1 Y 8 H 1 Y 7 H 1 Y 6 Y Y Y 4 Y Y Y
```
-/
def cf558 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1,
               .Y, .R 8, .H, .R 1, .Y, .R 7, .H, .R 1, .Y, .R 6, .Y, .Y, .Y, .R 4, .Y, .Y, .Y] }

/-- math-comp `cf559`:
```
Config 32
  H 2 H 12 Y 10 H 1 Y 8 H 9 H 1 Y 8 H 1 Y 8 Y 5 H 1 Y 6 H 1 Y 4 Y 1 Y 1 Y 2 Y
```
-/
def cf559 : Config :=
  { cfsym := false, cfcontractRef := [32],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 9, .H, .R 1, .Y, .R 8, .H,
               .R 1, .Y, .R 8, .Y, .R 5, .H, .R 1, .Y, .R 6, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y, .R 1,
               .Y, .R 2, .Y] }

/-- math-comp `cf560`:
```
Config 23
  H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 1 Y 3 Y Y 3 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf560 : Config :=
  { cfsym := false, cfcontractRef := [23],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 7, .H,
               .R 1, .Y, .R 3, .Y, .Y, .R 3, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf561`:
```
Config 29
  H 10 H 1 Y 8 H 2 H 10 Y 8 H 1 Y 5 H 3 H 8 H 8 Y 6 Y Y 2 H 1 Y 2 Y Y Y
```
-/
def cf561 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 5, .H,
               .R 3, .H, .R 8, .H, .R 8, .Y, .R 6, .Y, .Y, .R 2, .H, .R 1, .Y, .R 2, .Y, .Y, .Y] }

/-- math-comp `cf562`:
```
Config* 33
  H 2 H 13 Y 11 H 1 Y 10 H 1 Y 9 H 9 H 1 Y 8 H 1 Y 8 Y 6 Y 4 Y 2 H 1 Y 4 Y 1 Y 2
  Y
```
-/
def cf562 : Config :=
  { cfsym := true, cfcontractRef := [33],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9,
               .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .R 4, .Y, .R 2, .H, .R 1, .Y,
               .R 4, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf563`:
```
Config 31
  H 2 H 13 Y 3 H 2 H 12 Y 3 H 11 Y 3 H 2 H 10 Y 2 Y 7 H 1 Y 6 Y 1 Y 1 Y 4 H 4 Y
  Y 1 Y
```
-/
def cf563 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3,
               .H, .R 2, .H, .R 10, .Y, .R 2, .Y, .R 7, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .R 1, .Y,
               .R 4, .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf564`:
```
Config 8 9 34
  H 12 H 1 Y 11 H 1 Y 10 H 10 H 1 Y 9 H 1 Y 7 H 1 H 1 Y 7 Y 6 H 7 Y 3 Y Y Y 3 Y
  Y
```
-/
def cf564 : Config :=
  { cfsym := false, cfcontractRef := [8, 9, 34],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 10, .H, .R 1, .Y, .R 9,
               .H, .R 1, .Y, .R 7, .H, .R 1, .H, .R 1, .Y, .R 7, .Y, .R 6, .H, .R 7, .Y, .R 3, .Y,
               .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf565`:
```
Config 34
  H 2 H 12 Y 8 H 3 H 11 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 8 Y 6 H 7 Y Y 1 Y 4 H 4 Y Y 1
  Y
```
-/
def cf565 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 8, .H, .R 3, .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1,
               .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .H, .R 7, .Y, .Y, .R 1, .Y, .R 4,
               .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf566`:
```
Config 17
  H 11 H 1 Y 9 H 2 H 11 Y 9 H 1 Y 8 H 1 Y 8 H 1 Y 6 H 1 H 1 Y H 6 Y 5 Y Y 1 Y 1
  Y
```
-/
def cf566 : Config :=
  { cfsym := false, cfcontractRef := [17],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H,
               .R 1, .Y, .R 8, .H, .R 1, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .H, .R 6, .Y, .R 5, .Y,
               .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf567`:
```
Config* 6
  H 2 H 9 Y 7 H 1 Y 7 H 7 H 7 H 7 H 7 Y 5 Y Y Y Y Y
```
-/
def cf567 : Config :=
  { cfsym := true, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 9, .Y, .R 7, .H, .R 1, .Y, .R 7, .H, .R 7, .H, .R 7, .H, .R 7, .H,
               .R 7, .Y, .R 5, .Y, .Y, .Y, .Y, .Y] }

/-- math-comp `cf568`:
```
Config* 24
  H 8 H 2 H 10 Y 8 H 6 H 3 H 9 H 9 Y 8 H 8 Y Y Y Y Y Y Y
```
-/
def cf568 : Config :=
  { cfsym := true, cfcontractRef := [24],
    cfprog := [.H, .R 8, .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y,
               .R 8, .H, .R 8, .Y, .Y, .Y, .Y, .Y, .Y, .Y] }

/-- math-comp `cf569`:
```
Config* 23
  H 6 H 4 H 10 H 10 H 10 Y 7 H 9 H 9 H 9 Y Y Y Y Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf569 : Config :=
  { cfsym := true, cfcontractRef := [23],
    cfprog := [.H, .R 6, .H, .R 4, .H, .R 10, .H, .R 10, .H, .R 10, .Y, .R 7, .H, .R 9, .H, .R 9,
               .H, .R 9, .Y, .Y, .Y, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf570`:
```
Config 27
  H 9 H 1 Y 3 H 9 Y 6 H 5 H 1 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 2 Y
```
-/
def cf570 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 6, .H, .R 5, .H, .R 1, .H, .R 1, .H,
               .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf571`:
```
Config 27
  H 9 H 1 Y 3 H 9 Y 5 H 6 H 1 H 1 Y 2 H 1 Y 3 Y 1 Y 1 Y 3 Y Y
```
-/
def cf571 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 9, .H, .R 1, .Y, .R 3, .H, .R 9, .Y, .R 5, .H, .R 6, .H, .R 1, .H, .R 1, .Y,
               .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf572`:
```
Config 6
  H 2 H 10 Y 8 H 1 Y 4 H 8 Y 5 H 1 Y 6 H 1 Y 5 H 1 Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf572 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 4, .H, .R 8, .Y, .R 5, .H, .R 1, .Y,
               .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf573`:
```
Config 24
  H 7 H 4 H 11 H 11 H 11 Y 8 H 9 H 1 Y 9 H 9 Y Y Y Y Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf573 : Config :=
  { cfsym := false, cfcontractRef := [24],
    cfprog := [.H, .R 7, .H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11, .Y, .R 8, .H, .R 9, .H, .R 1,
               .Y, .R 9, .H, .R 9, .Y, .Y, .Y, .Y, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf574`:
```
Config 33
  H 3 H 10 H 1 Y 7 H 10 H 2 H 10 Y 2 H 9 Y Y 6 H 1 H 1 Y 2 Y 1 Y 2 H 1 Y 1 Y Y
```
-/
def cf574 : Config :=
  { cfsym := false, cfcontractRef := [33],
    cfprog := [.H, .R 3, .H, .R 10, .H, .R 1, .Y, .R 7, .H, .R 10, .H, .R 2, .H, .R 10, .Y, .R 2,
               .H, .R 9, .Y, .Y, .R 6, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 2, .H, .R 1,
               .Y, .R 1, .Y, .Y] }

/-- math-comp `cf575`:
```
Config 12 13 28
  H 2 H 11 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 1 Y 7 Y 5 Y Y Y 2 Y 2 Y
```
-/
def cf575 : Config :=
  { cfsym := false, cfcontractRef := [12, 13, 28],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y,
               .R 7, .H, .R 1, .Y, .R 7, .Y, .R 5, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y] }

/-- math-comp `cf576`:
```
Config* 27
  H 10 H 1 Y 3 H 10 Y 3 H 9 Y 5 H 6 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 2 Y
```
-/
def cf576 : Config :=
  { cfsym := true, cfcontractRef := [27],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9, .Y, .R 5, .H, .R 6, .H,
               .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf577`:
```
Config 6
  H 2 H 11 Y 9 H 1 Y 4 H 5 H 9 H 9 H 9 H 9 Y 8 Y 6 Y Y Y Y 3 Y 1 Y
```
-/
def cf577 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 4, .H, .R 5, .H, .R 9, .H, .R 9, .H,
               .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf578`:
```
Config 6
  H 2 H 11 Y 9 H 1 Y 6 H 3 H 9 H 9 Y 7 H 8 Y 6 Y Y Y 4 H 4 Y 2 Y Y
```
-/
def cf578 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 6, .H, .R 3, .H, .R 9, .H, .R 9, .Y,
               .R 7, .H, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf579`:
```
Config 30
  H 2 H 11 Y 4 H 9 H 1 Y 5 H 7 H 1 H 1 Y 3 H 8 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf579 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 5, .H, .R 7, .H, .R 1, .H,
               .R 1, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1,
               .Y] }

/-- math-comp `cf580`:
```
Config 6
  H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 6 H 8 Y 6 Y Y 5 H 1 Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf580 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 6, .H,
               .R 8, .Y, .R 6, .Y, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf581`:
```
Config* 31
  H 9 H 1 H 1 Y 4 H 9 H 1 Y 4 H 8 H 1 Y 2 H 1 Y 3 Y 1 Y 1 Y 1 Y 3 Y Y
```
-/
def cf581 : Config :=
  { cfsym := true, cfcontractRef := [31],
    cfprog := [.H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 4, .H, .R 8, .H,
               .R 1, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf582`:
```
Config 6
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 8 Y 6 Y 6 H 1 Y 5 H 1 Y 4 H 1 Y 3 Y 1 Y
```
-/
def cf582 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 8, .Y,
               .R 6, .Y, .R 6, .H, .R 1, .Y, .R 5, .H, .R 1, .Y, .R 4, .H, .R 1, .Y, .R 3, .Y, .R 1,
               .Y] }

/-- math-comp `cf583`:
```
Config 6
  H 2 H 10 Y 8 H 1 Y 4 H 8 Y 5 H 1 Y 6 H 1 Y 4 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf583 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 4, .H, .R 8, .Y, .R 5, .H, .R 1, .Y,
               .R 6, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1, .Y] }

/-- math-comp `cf584`:
```
Config 8 9 33
  H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 2 H 9 Y 2 Y 6 H 1 Y 6 Y 1 Y 2 Y 3 Y Y
```
-/
def cf584 : Config :=
  { cfsym := false, cfcontractRef := [8, 9, 33],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H,
               .R 2, .H, .R 9, .Y, .R 2, .Y, .R 6, .H, .R 1, .Y, .R 6, .Y, .R 1, .Y, .R 2, .Y, .R 3,
               .Y, .Y] }

/-- math-comp `cf585`:
```
Config 30
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 5 H 4 H 9 H 9 H 9 Y 8 Y 6 Y Y Y Y 3 Y 1 Y
```
-/
def cf585 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 5, .H, .R 4, .H,
               .R 9, .H, .R 9, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf586`:
```
Config 30
  H 3 H 12 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 8 H 1 Y 8 Y 6 Y Y Y Y 2 Y 2 Y
```
-/
def cf586 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10,
               .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .Y, .R 2, .Y, .R 2,
               .Y] }

/-- math-comp `cf587`:
```
Config 27
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 7 H 2 H 9 Y 7 H 8 Y 6 Y Y Y 4 H 4 Y 2 Y Y
```
-/
def cf587 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H,
               .R 9, .Y, .R 7, .H, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2, .Y, .Y] }

/-- math-comp `cf588`:
```
Config 24
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 7 H 2 H 9 Y 8 Y 6 Y 6 H 6 Y 2 Y Y 2 Y 2 Y
```
-/
def cf588 : Config :=
  { cfsym := false, cfcontractRef := [24],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 7, .H,
               .R 2, .H, .R 9, .Y, .R 8, .Y, .R 6, .Y, .R 6, .H, .R 6, .Y, .R 2, .Y, .Y, .R 2, .Y,
               .R 2, .Y] }

/-- math-comp `cf589`:
```
Config 16 17 31
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 3 H 9 Y 3 H 1 H 1 Y 3 Y 3 H 1 Y 4 Y 1 Y 1 Y 2 Y
```
-/
def cf589 : Config :=
  { cfsym := false, cfcontractRef := [16, 17, 31],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 3, .H, .R 9,
               .Y, .R 3, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 3, .H, .R 1, .Y, .R 4, .Y, .R 1, .Y,
               .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf590`:
```
Config 7
  H 3 H 12 H 12 Y 7 H 4 H 11 H 11 H 11 Y 8 H 2 H 10 Y 9 Y 7 Y Y Y Y 3 Y 2 Y Y
```
-/
def cf590 : Config :=
  { cfsym := false, cfcontractRef := [7],
    cfprog := [.H, .R 3, .H, .R 12, .H, .R 12, .Y, .R 7, .H, .R 4, .H, .R 11, .H, .R 11, .H, .R 11,
               .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .Y, .Y, .Y, .R 3, .Y, .R 2,
               .Y, .Y] }

/-- math-comp `cf591`:
```
Config 6
  H 2 H 11 Y 9 H 1 Y 7 H 2 H 9 Y 8 H 8 H 8 H 8 Y 6 Y Y 4 H 5 Y 3 Y Y Y
```
-/
def cf591 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 7, .H, .R 2, .H, .R 9, .Y, .R 8, .H,
               .R 8, .H, .R 8, .H, .R 8, .Y, .R 6, .Y, .Y, .R 4, .H, .R 5, .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf592`:
```
Config 6
  H 2 H 11 Y 9 H 1 Y 8 H 1 Y 5 H 8 Y 6 Y 6 H 1 Y 4 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf592 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y, .R 5, .H, .R 8, .Y,
               .R 6, .Y, .R 6, .H, .R 1, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1,
               .Y] }

/-- math-comp `cf593`:
```
Config 15
  H 11 H 1 Y 10 H 1 Y 8 H 2 H 10 Y 7 H 8 H 1 Y 7 Y 5 H 7 H 7 Y Y 1 Y 2 Y 2 Y Y
```
-/
def cf593 : Config :=
  { cfsym := false, cfcontractRef := [15],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 8, .H, .R 2, .H, .R 10, .Y, .R 7,
               .H, .R 8, .H, .R 1, .Y, .R 7, .Y, .R 5, .H, .R 7, .H, .R 7, .Y, .Y, .R 1, .Y, .R 2,
               .Y, .R 2, .Y, .Y] }

/-- math-comp `cf594`:
```
Config 6
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 5 H 9 Y 3 H 1 H 1 H 1 Y 1 Y Y Y 4 H 4 Y 2 Y Y
```
-/
def cf594 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 5, .H, .R 9, .Y,
               .R 3, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2,
               .Y, .Y] }

/-- math-comp `cf595`:
```
Config 41
  H 2 H 12 Y 3 H 2 H 11 Y 4 H 1 H 8 H 1 H 1 Y 3 H 9 H 9 Y 1 H 1 Y 1 Y Y 1 Y 1 Y
  2 Y 1 Y
```
-/
def cf595 : Config :=
  { cfsym := false, cfcontractRef := [41],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 2, .H, .R 11, .Y, .R 4, .H, .R 1, .H, .R 8, .H,
               .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .H, .R 9, .Y, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y,
               .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf596`:
```
Config 16 17 24
  H 2 H 12 Y 10 H 1 Y 9 H 1 Y 8 H 1 Y 6 H 8 Y 6 Y Y 4 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf596 : Config :=
  { cfsym := false, cfcontractRef := [16, 17, 24],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 1, .Y, .R 8, .H, .R 1, .Y,
               .R 6, .H, .R 8, .Y, .R 6, .Y, .Y, .R 4, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y,
               .R 1, .Y] }

/-- math-comp `cf597`:
```
Config* 19 20 36
  H 2 H 13 Y 11 H 1 Y 10 H 1 Y 9 H 9 H 1 Y 8 H 9 Y 5 H 1 Y 1 Y Y 4 H 5 Y 3 Y Y Y
```
-/
def cf597 : Config :=
  { cfsym := true, cfcontractRef := [19, 20, 36],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 10, .H, .R 1, .Y, .R 9, .H, .R 9,
               .H, .R 1, .Y, .R 8, .H, .R 9, .Y, .R 5, .H, .R 1, .Y, .R 1, .Y, .Y, .R 4, .H, .R 5,
               .Y, .R 3, .Y, .Y, .Y] }

/-- math-comp `cf598`:
```
Config 31
  H 2 H 11 Y 6 H 7 H 1 H 1 H 1 Y 3 H 9 Y 3 H 8 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf598 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 6, .H, .R 7, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .H,
               .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1,
               .Y] }

/-- math-comp `cf599`:
```
Config 30
  H 10 H 1 Y 3 H 10 Y 5 H 2 H 9 Y 2 Y 4 H 7 Y 2 H 6 Y 2 H 5 Y 2 Y Y 2 Y
```
-/
def cf599 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5, .H, .R 2, .H, .R 9, .Y, .R 2, .Y,
               .R 4, .H, .R 7, .Y, .R 2, .H, .R 6, .Y, .R 2, .H, .R 5, .Y, .R 2, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf600`:
```
Config 31
  H 10 H 1 Y 3 H 10 Y 4 H 2 H 9 Y 2 H 1 Y 4 H 7 Y 2 H 6 Y 2 Y Y 3 Y Y
```
-/
def cf600 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 2, .H, .R 9, .Y, .R 2, .H,
               .R 1, .Y, .R 4, .H, .R 7, .Y, .R 2, .H, .R 6, .Y, .R 2, .Y, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf601`:
```
Config 1 2 26 32
  H 2 H 12 Y 10 H 1 Y 6 H 4 H 10 H 10 H 10 Y 8 H 1 Y 8 Y 6 Y Y Y 2 Y 2 Y 1 Y
```
-/
def cf601 : Config :=
  { cfsym := false, cfcontractRef := [1, 2, 26, 32],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 6, .H, .R 4, .H, .R 10, .H, .R 10,
               .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .R 2, .Y, .R 2, .Y,
               .R 1, .Y] }

/-- math-comp `cf602`:
```
Config 31
  H 11 H 1 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 2 H 1 Y 3 Y 1 Y 1 Y 4 Y 3 Y 1 Y
```
-/
def cf602 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y,
               .R 3, .H, .R 9, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 4, .Y, .R 3,
               .Y, .R 1, .Y] }

/-- math-comp `cf603`:
```
Config 31
  H 2 H 12 Y 3 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 3 H 8 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1 Y
```
-/
def cf603 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y,
               .R 3, .H, .R 9, .Y, .R 3, .H, .R 8, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2,
               .Y, .R 1, .Y] }

/-- math-comp `cf604`:
```
Config 31
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 4 H 2 H 9 Y 2 Y 3 Y 2 H 6 Y 2 H 5 Y 2 Y Y 2 Y
```
-/
def cf604 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 2,
               .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 2, .H, .R 6, .Y, .R 2, .H, .R 5, .Y, .R 2, .Y,
               .Y, .R 2, .Y] }

/-- math-comp `cf605`:
```
Config 6
  H 2 H 12 Y 10 H 1 Y 7 H 3 H 10 H 10 Y 7 H 9 Y 7 Y Y Y 4 H 5 Y 2 H 4 Y 2 Y Y
```
-/
def cf605 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 7, .H, .R 3, .H, .R 10, .H, .R 10,
               .Y, .R 7, .H, .R 9, .Y, .R 7, .Y, .Y, .Y, .R 4, .H, .R 5, .Y, .R 2, .H, .R 4, .Y,
               .R 2, .Y, .Y] }

/-- math-comp `cf606`:
```
Config 30
  H 2 H 11 Y 5 H 8 H 1 H 1 Y 3 H 9 Y 4 H 7 H 1 Y 3 Y 1 Y 1 Y 4 H 4 Y Y 1 Y
```
-/
def cf606 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 5, .H, .R 8, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 9, .Y,
               .R 4, .H, .R 7, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 4, .Y, .Y,
               .R 1, .Y] }

/-- math-comp `cf607`:
```
Config 31
  H 11 H 1 Y 3 H 11 Y 4 H 2 H 10 Y 3 H 1 Y 4 H 8 Y 2 H 7 Y 2 Y Y 2 H 1 Y 1 Y Y
```
-/
def cf607 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 2, .H, .R 10, .Y, .R 3,
               .H, .R 1, .Y, .R 4, .H, .R 8, .Y, .R 2, .H, .R 7, .Y, .R 2, .Y, .Y, .R 2, .H, .R 1,
               .Y, .R 1, .Y, .Y] }

/-- math-comp `cf608`:
```
Config 35
  H 2 H 12 Y 5 H 9 H 1 H 1 Y 3 H 2 H 10 Y 3 H 9 Y 3 Y 1 Y 3 H 6 Y Y 1 Y 2 Y 1 Y
```
-/
def cf608 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y, .R 3, .H, .R 2, .H,
               .R 10, .Y, .R 3, .H, .R 9, .Y, .R 3, .Y, .R 1, .Y, .R 3, .H, .R 6, .Y, .Y, .R 1, .Y,
               .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf609`:
```
Config 27
  H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 3 H 1 Y 3 Y 1 Y 4 H 1 Y H 4 Y Y 1 Y
```
-/
def cf609 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H,
               .R 9, .Y, .R 3, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 4, .H, .R 1, .Y, .H, .R 4, .Y,
               .Y, .R 1, .Y] }

/-- math-comp `cf610`:
```
Config 29
  H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 2 H 1 H 1 H 1 Y 3 Y 1 Y 5 Y 3 H 1 Y 1 Y Y
```
-/
def cf610 : Config :=
  { cfsym := false, cfcontractRef := [29],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 2, .H,
               .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 5, .Y, .R 3, .H, .R 1, .Y, .R 1,
               .Y, .Y] }

/-- math-comp `cf611`:
```
Config 23
  H 10 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 3 H 8 Y 6 Y 1 Y 3 H 1 H 1 Y H 4 Y Y 1 Y
```
-/
def cf611 : Config :=
  { cfsym := false, cfcontractRef := [23],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .H,
               .R 8, .Y, .R 6, .Y, .R 1, .Y, .R 3, .H, .R 1, .H, .R 1, .Y, .H, .R 4, .Y, .Y, .R 1,
               .Y] }

/-- math-comp `cf612`:
```
Config 23
  H 11 H 1 Y 4 H 10 H 1 Y 3 H 10 Y 5 H 1 Y 4 Y Y 2 H 1 H 1 H 1 Y 1 Y Y Y Y
```
-/
def cf612 : Config :=
  { cfsym := false, cfcontractRef := [23],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 5,
               .H, .R 1, .Y, .R 4, .Y, .Y, .R 2, .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 1, .Y, .Y, .Y,
               .Y] }

/-- math-comp `cf613`:
```
Config 16 17 32
  H 12 H 1 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 2 H 9 Y 2 Y 3 Y 3 H 1 Y 4 Y 1 Y 1 Y
  2 Y
```
-/
def cf613 : Config :=
  { cfsym := false, cfcontractRef := [16, 17, 32],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10,
               .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 3, .H, .R 1, .Y, .R 4, .Y,
               .R 1, .Y, .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf614`:
```
Config 11 12 33
  H 3 H 13 H 13 Y 10 H 2 H 12 Y 8 H 3 H 11 H 11 Y 9 H 1 Y 9 Y 7 Y Y Y Y 2 Y 2 Y
  1 Y
```
-/
def cf614 : Config :=
  { cfsym := false, cfcontractRef := [11, 12, 33],
    cfprog := [.H, .R 3, .H, .R 13, .H, .R 13, .Y, .R 10, .H, .R 2, .H, .R 12, .Y, .R 8, .H, .R 3,
               .H, .R 11, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .Y, .R 7, .Y, .Y, .Y, .Y, .R 2,
               .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf615`:
```
Config 12 13 30 36
  H 2 H 13 Y 11 H 1 Y 9 H 2 H 11 Y 8 H 2 H 10 Y 8 H 1 Y 5 Y Y 3 H 6 Y 3 Y Y Y 2
  Y
```
-/
def cf615 : Config :=
  { cfsym := false, cfcontractRef := [12, 13, 30, 36],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 8,
               .H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 5, .Y, .Y, .R 3, .H, .R 6, .Y, .R 3,
               .Y, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf616`:
```
Config 30
  H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 2 H 1 H 1 Y 3 Y 1 Y 5 Y 4 H 1 Y 3 Y 1
  Y
```
-/
def cf616 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H,
               .R 9, .Y, .R 2, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 5, .Y, .R 4, .H, .R 1,
               .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf617`:
```
Config 30
  H 2 H 12 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 9 Y 4 H 7 H 1 Y 3 Y 1 Y 1 Y 4 H 4 Y Y 1 Y
```
-/
def cf617 : Config :=
  { cfsym := false, cfcontractRef := [30],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H,
               .R 9, .Y, .R 4, .H, .R 7, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 4, .H, .R 4,
               .Y, .Y, .R 1, .Y] }

/-- math-comp `cf618`:
```
Config 35
  H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 4 H 9 H 9 Y 3 Y 1 Y 1 Y 1 Y 1 Y 2
  Y 1 Y
```
-/
def cf618 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y,
               .R 3, .H, .R 10, .Y, .R 4, .H, .R 9, .H, .R 9, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y,
               .R 1, .Y, .R 1, .Y, .R 2, .Y, .R 1, .Y] }

/-- math-comp `cf619`:
```
Config 35
  H 12 H 1 Y 3 H 12 Y 4 H 10 H 1 Y 3 H 2 H 10 Y 2 H 1 Y 3 Y 3 H 7 Y Y 1 Y 4 Y 3
  Y 1 Y
```
-/
def cf619 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 4, .H, .R 10, .H, .R 1, .Y, .R 3,
               .H, .R 2, .H, .R 10, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 3, .H, .R 7, .Y, .Y, .R 1,
               .Y, .R 4, .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf620`:
```
Config* 31
  H 12 H 1 Y 3 H 12 Y 3 H 11 Y 3 H 10 Y 3 H 2 H 9 Y 2 Y 3 Y 2 H 6 Y 1 H 1 Y 1 Y
  Y 2 Y
```
-/
def cf620 : Config :=
  { cfsym := true, cfcontractRef := [31],
    cfprog := [.H, .R 12, .H, .R 1, .Y, .R 3, .H, .R 12, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10,
               .Y, .R 3, .H, .R 2, .H, .R 9, .Y, .R 2, .Y, .R 3, .Y, .R 2, .H, .R 6, .Y, .R 1, .H,
               .R 1, .Y, .R 1, .Y, .Y, .R 2, .Y] }

/-- math-comp `cf621`:
```
Config 34
  H 2 H 13 Y 3 H 12 Y 5 H 9 H 1 H 1 Y 3 H 10 Y 4 H 8 H 1 Y 3 Y 1 Y 1 Y 1 Y 2 Y 1
  Y 1 Y
```
-/
def cf621 : Config :=
  { cfsym := false, cfcontractRef := [34],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 3, .H, .R 12, .Y, .R 5, .H, .R 9, .H, .R 1, .H, .R 1, .Y,
               .R 3, .H, .R 10, .Y, .R 4, .H, .R 8, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y,
               .R 1, .Y, .R 2, .Y, .R 1, .Y, .R 1, .Y] }

/-- math-comp `cf622`:
```
Config* 6
  H 2 H 10 Y 8 H 1 Y 8 H 8 H 8 H 8 H 8 H 8 Y 6 Y Y Y Y Y Y
```
-/
def cf622 : Config :=
  { cfsym := true, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .H, .R 8, .H, .R 8, .H, .R 8, .H,
               .R 8, .H, .R 8, .Y, .R 6, .Y, .Y, .Y, .Y, .Y, .Y] }

/-- math-comp `cf623`:
```
Config 31
  H 10 H 1 Y 3 H 10 Y 7 H 5 H 1 H 1 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 1 Y 2 Y
```
-/
def cf623 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 7, .H, .R 5, .H, .R 1, .H, .R 1, .H,
               .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 2,
               .Y] }

/-- math-comp `cf624`:
```
Config 31
  H 10 H 1 Y 3 H 10 Y 6 H 6 H 1 H 1 H 1 Y 2 H 1 Y 3 Y 1 Y 1 Y 1 Y 3 Y Y
```
-/
def cf624 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 10, .H, .R 1, .Y, .R 3, .H, .R 10, .Y, .R 6, .H, .R 6, .H, .R 1, .H, .R 1, .H,
               .R 1, .Y, .R 2, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .Y, .Y] }

/-- math-comp `cf625`:
```
Config 12 13 32
  H 2 H 12 Y 10 H 1 Y 6 H 4 H 10 H 10 H 10 Y 8 H 1 Y 8 Y 6 Y Y Y Y 2 Y 2 Y
```
-/
def cf625 : Config :=
  { cfsym := false, cfcontractRef := [12, 13, 32],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 6, .H, .R 4, .H, .R 10, .H, .R 10,
               .H, .R 10, .Y, .R 8, .H, .R 1, .Y, .R 8, .Y, .R 6, .Y, .Y, .Y, .Y, .R 2, .Y, .R 2,
               .Y] }

/-- math-comp `cf626`:
```
Config 31
  H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 5 H 7 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 1 Y 2 Y
```
-/
def cf626 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 5, .H,
               .R 7, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 1,
               .Y, .R 2, .Y] }

/-- math-comp `cf627`:
```
Config* 30
  H 11 H 1 Y 3 H 11 Y 3 H 10 Y 6 H 6 H 1 H 1 H 1 Y 2 Y 3 Y 1 Y 1 Y 1 Y 1 Y 2 Y
```
-/
def cf627 : Config :=
  { cfsym := true, cfcontractRef := [30],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 3, .H, .R 10, .Y, .R 6, .H, .R 6,
               .H, .R 1, .H, .R 1, .H, .R 1, .Y, .R 2, .Y, .R 3, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y,
               .R 1, .Y, .R 2, .Y] }

/-- math-comp `cf628`:
```
Config 6
  H 2 H 12 Y 10 H 1 Y 6 H 4 H 10 H 10 H 10 Y 8 H 9 Y 7 Y Y Y Y 4 H 4 Y 2 Y Y
```
-/
def cf628 : Config :=
  { cfsym := false, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 12, .Y, .R 10, .H, .R 1, .Y, .R 6, .H, .R 4, .H, .R 10, .H, .R 10,
               .H, .R 10, .Y, .R 8, .H, .R 9, .Y, .R 7, .Y, .Y, .Y, .Y, .R 4, .H, .R 4, .Y, .R 2,
               .Y, .Y] }

/-- math-comp `cf629`:
```
Config 35
  H 11 H 1 Y 3 H 11 Y 4 H 9 H 1 Y 3 H 1 H 1 H 1 Y 3 Y 1 Y 2 H 1 Y 5 Y 1 Y 3 Y Y
```
-/
def cf629 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 4, .H, .R 9, .H, .R 1, .Y, .R 3, .H,
               .R 1, .H, .R 1, .H, .R 1, .Y, .R 3, .Y, .R 1, .Y, .R 2, .H, .R 1, .Y, .R 5, .Y, .R 1,
               .Y, .R 3, .Y, .Y] }

/-- math-comp `cf630`:
```
Config 27
  H 2 H 13 Y 11 H 1 Y 9 H 2 H 11 Y 9 H 8 H 2 H 10 Y 9 Y 7 Y Y 6 H 6 Y 2 Y Y 2 Y
  2 Y
```
-/
def cf630 : Config :=
  { cfsym := false, cfcontractRef := [27],
    cfprog := [.H, .R 2, .H, .R 13, .Y, .R 11, .H, .R 1, .Y, .R 9, .H, .R 2, .H, .R 11, .Y, .R 9,
               .H, .R 8, .H, .R 2, .H, .R 10, .Y, .R 9, .Y, .R 7, .Y, .Y, .R 6, .H, .R 6, .Y, .R 2,
               .Y, .Y, .R 2, .Y, .R 2, .Y] }

/-- math-comp `cf631`:
```
Config 31
  H 11 H 1 Y 3 H 11 Y 6 H 7 H 1 H 1 H 1 Y 3 H 9 Y 5 Y 1 Y 1 Y 1 Y 3 H 1 Y 3 Y 1
  Y
```
-/
def cf631 : Config :=
  { cfsym := false, cfcontractRef := [31],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 6, .H, .R 7, .H, .R 1, .H, .R 1, .H,
               .R 1, .Y, .R 3, .H, .R 9, .Y, .R 5, .Y, .R 1, .Y, .R 1, .Y, .R 1, .Y, .R 3, .H, .R 1,
               .Y, .R 3, .Y, .R 1, .Y] }

/-- math-comp `cf632`:
```
Config 35
  H 11 H 1 Y 3 H 11 Y 5 H 2 H 10 Y 2 H 1 Y 4 H 8 Y 2 H 7 Y 2 H 6 Y 2 Y Y 3 Y Y
```
-/
def cf632 : Config :=
  { cfsym := false, cfcontractRef := [35],
    cfprog := [.H, .R 11, .H, .R 1, .Y, .R 3, .H, .R 11, .Y, .R 5, .H, .R 2, .H, .R 10, .Y, .R 2,
               .H, .R 1, .Y, .R 4, .H, .R 8, .Y, .R 2, .H, .R 7, .Y, .R 2, .H, .R 6, .Y, .R 2, .Y,
               .Y, .R 3, .Y, .Y] }

/-- math-comp `cf633`:
```
Config* 6
  H 2 H 11 Y 9 H 1 Y 9 H 9 H 9 H 9 H 9 H 9 H 9 Y 7 Y Y Y Y Y Y Y
```
-/
def cf633 : Config :=
  { cfsym := true, cfcontractRef := [6],
    cfprog := [.H, .R 2, .H, .R 11, .Y, .R 9, .H, .R 1, .Y, .R 9, .H, .R 9, .H, .R 9, .H, .R 9, .H,
               .R 9, .H, .R 9, .H, .R 9, .Y, .R 7, .Y, .Y, .Y, .Y, .Y, .Y, .Y] }

/-- math-comp `the_configs`: the list of the 633 reducible configurations; configuration
number `n` (`cfNNN`) has index `n - 1`. -/
def theConfigs : List Config :=
  [cf001, cf002, cf003, cf004, cf005, cf006, cf007, cf008, cf009, cf010, cf011, cf012, cf013, cf014,
   cf015, cf016, cf017, cf018, cf019, cf020, cf021, cf022, cf023, cf024, cf025, cf026, cf027, cf028,
   cf029, cf030, cf031, cf032, cf033, cf034, cf035, cf036, cf037, cf038, cf039, cf040, cf041, cf042,
   cf043, cf044, cf045, cf046, cf047, cf048, cf049, cf050, cf051, cf052, cf053, cf054, cf055, cf056,
   cf057, cf058, cf059, cf060, cf061, cf062, cf063, cf064, cf065, cf066, cf067, cf068, cf069, cf070,
   cf071, cf072, cf073, cf074, cf075, cf076, cf077, cf078, cf079, cf080, cf081, cf082, cf083, cf084,
   cf085, cf086, cf087, cf088, cf089, cf090, cf091, cf092, cf093, cf094, cf095, cf096, cf097, cf098,
   cf099, cf100, cf101, cf102, cf103, cf104, cf105, cf106, cf107, cf108, cf109, cf110, cf111, cf112,
   cf113, cf114, cf115, cf116, cf117, cf118, cf119, cf120, cf121, cf122, cf123, cf124, cf125, cf126,
   cf127, cf128, cf129, cf130, cf131, cf132, cf133, cf134, cf135, cf136, cf137, cf138, cf139, cf140,
   cf141, cf142, cf143, cf144, cf145, cf146, cf147, cf148, cf149, cf150, cf151, cf152, cf153, cf154,
   cf155, cf156, cf157, cf158, cf159, cf160, cf161, cf162, cf163, cf164, cf165, cf166, cf167, cf168,
   cf169, cf170, cf171, cf172, cf173, cf174, cf175, cf176, cf177, cf178, cf179, cf180, cf181, cf182,
   cf183, cf184, cf185, cf186, cf187, cf188, cf189, cf190, cf191, cf192, cf193, cf194, cf195, cf196,
   cf197, cf198, cf199, cf200, cf201, cf202, cf203, cf204, cf205, cf206, cf207, cf208, cf209, cf210,
   cf211, cf212, cf213, cf214, cf215, cf216, cf217, cf218, cf219, cf220, cf221, cf222, cf223, cf224,
   cf225, cf226, cf227, cf228, cf229, cf230, cf231, cf232, cf233, cf234, cf235, cf236, cf237, cf238,
   cf239, cf240, cf241, cf242, cf243, cf244, cf245, cf246, cf247, cf248, cf249, cf250, cf251, cf252,
   cf253, cf254, cf255, cf256, cf257, cf258, cf259, cf260, cf261, cf262, cf263, cf264, cf265, cf266,
   cf267, cf268, cf269, cf270, cf271, cf272, cf273, cf274, cf275, cf276, cf277, cf278, cf279, cf280,
   cf281, cf282, cf283, cf284, cf285, cf286, cf287, cf288, cf289, cf290, cf291, cf292, cf293, cf294,
   cf295, cf296, cf297, cf298, cf299, cf300, cf301, cf302, cf303, cf304, cf305, cf306, cf307, cf308,
   cf309, cf310, cf311, cf312, cf313, cf314, cf315, cf316, cf317, cf318, cf319, cf320, cf321, cf322,
   cf323, cf324, cf325, cf326, cf327, cf328, cf329, cf330, cf331, cf332, cf333, cf334, cf335, cf336,
   cf337, cf338, cf339, cf340, cf341, cf342, cf343, cf344, cf345, cf346, cf347, cf348, cf349, cf350,
   cf351, cf352, cf353, cf354, cf355, cf356, cf357, cf358, cf359, cf360, cf361, cf362, cf363, cf364,
   cf365, cf366, cf367, cf368, cf369, cf370, cf371, cf372, cf373, cf374, cf375, cf376, cf377, cf378,
   cf379, cf380, cf381, cf382, cf383, cf384, cf385, cf386, cf387, cf388, cf389, cf390, cf391, cf392,
   cf393, cf394, cf395, cf396, cf397, cf398, cf399, cf400, cf401, cf402, cf403, cf404, cf405, cf406,
   cf407, cf408, cf409, cf410, cf411, cf412, cf413, cf414, cf415, cf416, cf417, cf418, cf419, cf420,
   cf421, cf422, cf423, cf424, cf425, cf426, cf427, cf428, cf429, cf430, cf431, cf432, cf433, cf434,
   cf435, cf436, cf437, cf438, cf439, cf440, cf441, cf442, cf443, cf444, cf445, cf446, cf447, cf448,
   cf449, cf450, cf451, cf452, cf453, cf454, cf455, cf456, cf457, cf458, cf459, cf460, cf461, cf462,
   cf463, cf464, cf465, cf466, cf467, cf468, cf469, cf470, cf471, cf472, cf473, cf474, cf475, cf476,
   cf477, cf478, cf479, cf480, cf481, cf482, cf483, cf484, cf485, cf486, cf487, cf488, cf489, cf490,
   cf491, cf492, cf493, cf494, cf495, cf496, cf497, cf498, cf499, cf500, cf501, cf502, cf503, cf504,
   cf505, cf506, cf507, cf508, cf509, cf510, cf511, cf512, cf513, cf514, cf515, cf516, cf517, cf518,
   cf519, cf520, cf521, cf522, cf523, cf524, cf525, cf526, cf527, cf528, cf529, cf530, cf531, cf532,
   cf533, cf534, cf535, cf536, cf537, cf538, cf539, cf540, cf541, cf542, cf543, cf544, cf545, cf546,
   cf547, cf548, cf549, cf550, cf551, cf552, cf553, cf554, cf555, cf556, cf557, cf558, cf559, cf560,
   cf561, cf562, cf563, cf564, cf565, cf566, cf567, cf568, cf569, cf570, cf571, cf572, cf573, cf574,
   cf575, cf576, cf577, cf578, cf579, cf580, cf581, cf582, cf583, cf584, cf585, cf586, cf587, cf588,
   cf589, cf590, cf591, cf592, cf593, cf594, cf595, cf596, cf597, cf598, cf599, cf600, cf601, cf602,
   cf603, cf604, cf605, cf606, cf607, cf608, cf609, cf610, cf611, cf612, cf613, cf614, cf615, cf616,
   cf617, cf618, cf619, cf620, cf621, cf622, cf623, cf624, cf625, cf626, cf627, cf628, cf629, cf630,
   cf631, cf632, cf633]

/-- Sanity check (not in the Coq development): `theConfigs` lists 633 configurations
(math-comp `the_configs` is defined with `@seqn config 633`). -/
theorem length_theConfigs : theConfigs.length = 633 := by decide +kernel

/-- Sanity check (not in the Coq development): the construction program of every configuration
satisfies `configProg` (math-comp `config_prog`), which `cfquiz.v` and `cfcontract.v` otherwise
check explicitly. -/
theorem configProg_theConfigs : theConfigs.all (fun cf => configProg cf.cfprog) = true := by
  decide +kernel

end FourColor
