# The Four Color Theorem in Lean 4

A Lean 4 + Mathlib port of Georges Gonthier's Coq/Rocq formal proof of the Four Color Theorem,
[math-comp/fourcolor](https://github.com/math-comp/fourcolor) (ported from commit
`c1d6b1cd5288bea4b067aac13cdde3c18dffe018`). It is written for the Palomar registry's standards:
the proof may use only the axioms `propext`, `Classical.choice` and `Quot.sound`, and every
computation in it is checked by the Lean kernel (`decide +kernel`, never `native_decide`).

The proof is also **self-contained in Lean**. Every file it needs is Lean source in this
repository, and the data of the reducibility certificates is computed by Lean code during the
build. So the Lean toolchain alone builds and checks the whole proof: `lake build` needs no other
program (see [Other formalizations](#other-formalizations) for why this is worth saying).

**Status.** Every Coq file of the proof is ported, replaced by kernel-checkable code (the
reducibility decision procedure), or made unnecessary by Mathlib's real numbers (the reals
libraries), and no Lean file contains `sorry`. The final run passed: the 633 reducibility
certificates and `Solution` build, `FourColor.RealPlane.four_color` depends only on `propext`,
`Classical.choice` and `Quot.sound`, and a rehearsal of Palomar's pipeline accepts the proof:
`lake comparator` with con-ron, nanoda and `leanchecker` prints "Your solution is okay!". The
whole pipeline is estimated at 2.4–3.3 h on Palomar's runner, against its 5.5 h budget.

## AI disclosure

This development was written by AI. Claude Opus 5.5, Anthropic's model, produced essentially all
of it, working as an agent in Claude Code: the Lean definitions and proofs, the reducibility
engine and its certificate generator, the scripts, and this documentation. Robert D. Barish
directed the work: he set the goal and the constraints, made the decisions that were put to him
(such as the licence), and ran the final build and the rehearsal of Palomar's pipeline.
The final review, which compared the statements with Gonthier's, was done by a separate
Claude Opus 5.5 agent that had not written the proof. No human has reviewed the mathematics yet.

So please don't take the theorem on the author's authority, or on the model's. The part a person
has to read is the statement: `Challenge.lean`, 220 lines of elementary definitions transcribed
from Gonthier's `realplane.v` (see [What it proves](#what-it-proves)). Everything else is checked
by machine: by Lean's kernel, and in Palomar's pipeline also by two independently written
checkers, nanoda and con-ron. To check it yourself, run `bash scripts/final_run.sh` (see
[Building and checking](#building-and-checking)).

## What it proves

`Challenge.lean` states the theorem that Palomar checks, and `Solution.lean` proves it:

```lean
theorem FourColor.RealPlane.four_color (m : Map) (h : SimpleMap m) : ColorableWith 4 m
```

In words: **every simple map of the real plane can be colored with at most four colors so that
adjacent regions get different colors.** More precisely:

* A map `m` is a relation on the points of `ℝ × ℝ` that is symmetric and transitive; its
  equivalence classes are the regions of the map. The map is *simple* when its regions are open
  and connected. There may be infinitely many regions, and they may be unbounded. Points outside
  every region, such as the borders, need no color.
* Two regions are *adjacent* when they are different and their closures share a point that lies
  in the closure of at most two regions. Regions that meet only at corners, like diagonally
  opposite squares of a checkerboard, are not adjacent.
* A coloring is itself a map `k`, whose regions are the color classes. It covers the same points
  as `m`, puts each region of `m` inside one color class, and gives different colors to points of
  adjacent regions. `ColorableWith 4 m` asks for a coloring with at most four color classes.

The definitions transcribe Coq's `realplane.v` one for one and in the same order, specialised to
Mathlib's real numbers. Open sets, closure and connectedness are defined directly from open
rectangles, as in Coq, so the statement uses only basic logic, `ℕ` and `<` on `ℝ`; Mathlib's
topology library is not used. `FourColor/RealPlane.lean` contains the same definitions between
the markers `BEGIN SYNCED DEFINITIONS` and `END SYNCED DEFINITIONS`. Palomar's comparator needs
them to be identical to those of `Challenge.lean`, and `python3 scripts/check_challenge_sync.py
--lean` checks that they are.

### The proof, top down

As in Coq's `fourcolor.v` (Lean paths relative to `FourColor/`):

```
four_color                          Solution.lean                fourcolor.v
└─ compactness_extension            Finitize.lean                finitize.v
   └─ four_color_finite             FourColorThm.lean            fourcolor.v
      ├─ discretize_to_hypermap     Discretize.lean              discretize.v
      └─ four_color_hypermap        FourColorThm.lean            combinatorial4ct.v
         ├─ unavoidability          Unavoidability.lean          unavoidability.v
         │  └─ exclude5 … exclude11 Present/P5 … Present/P11     present5.v … present11.v
         └─ theReducibility         Reducibility.lean            reducibility.v
            └─ cf001_reducible … cf633_reducible
                                    Reducibility/CfNNN.lean      job*.v, task*.v
```

* `compactness_extension` extends a coloring theorem from finite simple maps to all simple maps,
  by a compactness argument.
* `discretize_to_hypermap` turns a finite simple map into a planar bridgeless hypermap whose
  four-colorings give colorings of the map, through the grid and matte constructions of `Grid`,
  `Matte`, `GridMap` and `Approx`.
* `four_color_hypermap`: every planar bridgeless hypermap is four colorable. As in Coq, the proof
  passes to the cubic map `cube G` and argues by induction on the number of darts: a smallest
  counter-example would be a `MinimalCounterExample`, which `unavoidability` excludes once the
  633 configurations are known to be C-reducible (`Reducibility`).
* `unavoidability` collates the seven presentations of the discharging argument of Robertson,
  Sanders, Seymour and Thomas: a minimal counter-example has a dart of positive discharge score,
  whose face has 5 to 11 sides, and `exclude5` … `exclude11` exclude each of these sizes.
* `theReducibility`: each of the 633 configurations is C-reducible (`CfReducible`, Coq
  `cfreducible`). Each certificate module runs `#engine_certify cfNNN`, which computes checkpoint
  data at elaboration time and proves `cfNNN_reducible` from checks that the kernel evaluates,
  through `cfreducible_of_engine` (`FourColor/Engine.lean` gives an overview of the engine).

`FourColor/Combinatorial4ct.lean` proves the top of the chain with `Reducibility` as a
hypothesis, the way Coq's `unavoidability` takes it: `four_color_hypermap_of_reducibility`,
`RealPlane.four_color_finite_of_reducibility` and `RealPlane.four_color_of_reducibility`.
`FourColor/FourColorThm.lean` then plugs in `theReducibility`. Everyday builds therefore never
touch the 633 certificates.

## Axioms and what is trusted

* `#print axioms FourColor.RealPlane.four_color_of_reducibility` (the whole proof, with the
  reducibility of the 633 configurations as a hypothesis) prints
  `[propext, Classical.choice, Quot.sound]`, and so do `four_color_hypermap_of_reducibility`,
  `unavoidability`, `discretize_to_hypermap`, `compactness_extension` and
  `cfreducible_of_engine`. The final reducibility run checks the unconditional
  `FourColor.RealPlane.four_color` in the same way.
* No Lean file under `FourColor/`, nor `FourColor.lean` or `Solution.lean`, contains `sorry`,
  `admit`, `native_decide`, an `axiom`, `@[implemented_by]` or `@[extern]`. The only `sorry` is
  the statement in `Challenge.lean`, as Palomar requires.
* Some modules contain meta code, which runs at elaboration time: the certificate generator
  `FourColor/Engine/Gen.lean` (`#engine_nets`, `#engine_certify`), `FourColor/QuizData/Lit.lean`
  and `FourColor/Fast/PruneGen.lean`. They compute data (permutation networks, checkpoints, the
  quiz tree, pruning masks) and add it as literal definitions. The kernel then checks every
  theorem about that data, so a wrong value can only make a check fail.
* What remains to be trusted is the kernel (Palomar replays the proof with three independent
  checkers: Lean's `leanchecker`, nanoda and con-ron), the definitions in `Challenge.lean`, and
  Mathlib's `ℝ` with its order.

## Building and checking

**In one command.** `bash scripts/final_run.sh` does the whole final run:
it downloads Mathlib's prebuilt files, builds the library, the 633 reducibility certificates
(recording each one's time and memory) and `Solution`, checks the axioms of
`FourColor.RealPlane.four_color`, and rehearses Palomar's pipeline (the exports, `lake comparator`
with leanchecker, nanoda and con-ron, and the licence check). It needs Linux or macOS with bash,
git, curl, python3 and [elan](https://github.com/leanprover/elan), about 25 GB of disk and 16 GB
of memory or more. Each stage is timed, and an interrupted run resumes where it stopped. It ends
by writing `final-run-summary-<commit>.txt`, one text file with every result, and
`final-run-results-<commit>.tar.gz` with all the logs. `bash scripts/final_run.sh --help` lists
the options (`-j N`, `--no-palomar`, `--only STAGE`, `--plan`).

Step by step:

```sh
lake exe cache get                              # Mathlib's prebuilt files (elan installs Lean v4.35.0-rc2)
lake build                                      # the library, except the 633 reducibility certificates
bash scripts/build_reducibility.sh build -j N   # the 633 certificates, N Lean processes at a time
lake build Solution                             # the final theorem
```

* [elan](https://github.com/leanprover/elan) installs the Lean version pinned in
  `lean-toolchain` (v4.35.0-rc2), and `lake exe cache get` downloads Mathlib's prebuilt files
  (`lake-manifest.json` pins Mathlib at tag v4.35.0-rc2). Clone math-comp/fourcolor (at the commit
  above) into `.deps/fourcolor` if you want the Coq sources next to the port; the generators in
  `scripts/` read them from there. Don't run `lake update`, which would move the pins.
* `lake build` builds the default target `FourColor` (`FourColor.lean`): everything except
  `FourColor.Reducibility`, the modules under `FourColor/Reducibility/`, `FourColor.FourColorThm`
  and `Solution`. It includes the kernel-heavy unavoidability checks (the presentations, about
  0.4 h of kernel time).
* `scripts/build_reducibility.sh build -j N` builds `FourColor/Reducibility/CfNNN.lean`
  (NNN = 001 … 633) and the networks `FourColor/Reducibility/Nets<r>.lean` they use, with at most
  N Lean processes at a time (each takes up to about 1.5 GB at ring size 14). It records each
  module's wall time, CPU time and peak memory in `.lake/reducibility/timings.tsv`, and ends with
  `FourColor.Reducibility`. `--range A B` and `--only "N …"` select configurations, and
  `scripts/build_reducibility.sh gen` regenerates the 633 files and `FourColor/Reducibility.lean`.
* `lake build Solution` then builds `FourColor.FourColorThm` and `Solution`. Run on its own, it
  also builds the certificates, with Lake's default parallelism. `lake build Challenge` builds the
  statement file.
* To print the axioms, compile a file containing `import Solution` and
  `#print axioms FourColor.RealPlane.four_color` with `lake env lean <file>`.
* `python3 scripts/check_challenge_sync.py` checks textually that `Challenge.lean` and
  `FourColor/RealPlane.lean` agree; with `--lean` it also compiles both and compares their
  constants as the comparator does.
* `scripts/palomar_check.sh [-o DIR] [-t SECONDS] [--csv FILE] [--jobs N] MODULE DECL...` exports
  declarations of a built module with `leanexport` (and Palomar's fixed extra targets), replays
  the export with Palomar's three checkers (`leanchecker`, nanoda and con-ron), and prints each
  verdict with its wall time and peak memory. Example:
  `scripts/palomar_check.sh --jobs 1 Solution FourColor.RealPlane.four_color`.
* `scripts/palomar_dryrun.sh [-o DIR] [--jobs N] [--skip-build] [--no-sandbox]` runs Palomar's whole pipeline locally:
  the builds, the exports, the three checkers and the comparator.

Palomar reads `comparator.json`: challenge module `Challenge`, solution module `Solution`,
theorem `FourColor.RealPlane.four_color`, permitted axioms `propext`, `Quot.sound` and
`Classical.choice`.

## Repository layout

| Path | Contents |
|---|---|
| `Challenge.lean` | the statement Palomar checks: the definitions of `realplane.v` and `four_color := sorry` |
| `Solution.lean` | `FourColor.RealPlane.four_color := compactness_extension four_color_finite` |
| `comparator.json` | Palomar's comparator configuration |
| `formalization.yaml` | Palomar's metadata (format v0.4): authors, licence, sources, scope, deviations, review |
| `FourColor.lean` | umbrella module: everything except `FourColor.Reducibility`, its certificates and `FourColor.FourColorThm` |
| `FourColor/` | the library, by layer below |
| `scripts/` | the final run (`final_run.sh`), generators (`gen_configurations.py`, `present_gen.py`, `build_reducibility.sh`), checks (`check_challenge_sync.py`, `palomar_check.sh`, `palomar_dryrun.sh`), helpers (`engine_memtime.py`, `engine_nets.py`, `lean.sh`, `present_gen_native.lean`) |
| `LICENSE`, `NOTICE`, `LICENSES/CeCILL-B.txt` | licences (see below) |

The library, from the bottom up (a trailing `/` means a directory of modules with an umbrella
module of the same name):

| Layer | Modules |
|---|---|
| math-comp fragments | `Seq` (`seq`, `path`), `FinGraph` (`fingraph`) |
| Planarity | `Hypermap`, `Walkup/`, `Jordan/`, `Geometry`, `Examples` (sanity checks: a planar map, and a torus that is neither planar nor Jordan) |
| Colorings | `Color`, `Chromogram`, `Dyck`, `Coloring`, `Cube`, `Kempe` |
| Map surgery | `Patch`, `Snip`, `Sew`, `Revsnip`, `Birkhoff/`, `Contract`, `Embed/` |
| Configurations | `CfMap/`, `Configurations` (generated), `CfColor`, `CfContract/`, `CfReducible` |
| Reducibility engine | `Engine/` (overview in `Engine.lean`) |
| Reducibility certificates | `Reducibility/Nets2` … `Nets14`, `Reducibility/Cf001` … `Cf633`, `Reducibility` (all generated) |
| Unavoidability | `Part/`, `Discharge`, `Hubcap`, `Quiz`, `CfQuiz`, `QuizTree`, `RedPart/`, `Fast/`, `QuizData/`, `Present/` (`P5` … `P11` generated), `Unavoidability` |
| Real plane | `RealPlane`, `Grid`, `Matte`, `GridMap`, `Approx`, `Discretize`, `Finitize` |
| Top level | `Combinatorial4ct`, `FourColorThm` |

About 65,000 lines were written directly (by Claude Opus 5.5); the rest is generated by scripts: the 633 configurations, the
presentation case trees, and the reducibility certificates.

## How the port maps to the Coq development

Every ported declaration has a docstring naming its Coq original, and each module's docstring
lists its renamings and its deviations from Coq. The files:

| Coq (`theories/proof/`) | Lean (`FourColor/`) | Notes |
|---|---|---|
| `hypermap.v`, `walkup.v`, `jordan.v`, `geometry.v` | `Hypermap`, `Walkup/`, `Jordan/`, `Geometry` | with `Seq` and `FinGraph` for the math-comp fragments they use |
| `color.v`, `chromogram.v`, `dyck.v`, `coloring.v`, `cube.v`, `kempe.v` | `Color`, `Chromogram`, `Dyck`, `Coloring`, `Cube`, `Kempe` | |
| `patch.v`, `snip.v`, `sew.v`, `revsnip.v` | `Patch`, `Snip`, `Sew`, `Revsnip` | |
| `birkhoff.v` | `Birkhoff/` | `Birkhoff_check2` replayed on the reducibility engine |
| `contract.v`, `embed.v` | `Contract`, `Embed/` | |
| `cfmap.v`, `configurations.v` | `CfMap/`, `Configurations` | the data translated by `scripts/gen_configurations.py` |
| `cfcolor.v`, `cfcontract.v`, `cfreducible.v` | `CfColor`, `CfContract/`, `CfReducible` | their `ctree` parts replaced by the engine |
| `ctree.v`, `gtree.v`, `ctreerestrict.v`, `gtreerestrict.v`, `initctree.v`, `initgtree.v`, `kempetree.v` | `Engine/` | not ported: replaced by the new engine |
| `job*.v`, `task*.v`, `reducibility.v` | `Reducibility/CfNNN`, `Reducibility/Nets<r>`, `Reducibility` | generated by `scripts/build_reducibility.sh gen` |
| `part.v`, `discharge.v`, `hubcap.v`, `quiz.v`, `cfquiz.v`, `quiztree.v`, `redpart.v` | `Part/`, `Discharge`, `Hubcap`, `Quiz`, `CfQuiz`, `QuizTree`, `RedPart/` | kernel-fast versions of the checks in `Fast/` |
| `present.v` | `Present` (`Present/Basic`, `Present/Tree`), `QuizData/` | |
| `present5.v` … `present11.v` | `Present/P5` … `Present/P11` | generated by `scripts/present_gen.py` |
| `unavoidability.v` | `Unavoidability` | |
| `realplane.v` | `RealPlane` (and `Challenge.lean`) | |
| `grid.v`, `matte.v`, `gridmap.v`, `approx.v`, `discretize.v`, `finitize.v` | `Grid`, `Matte`, `GridMap`, `Approx`, `Discretize`, `Finitize` | |
| `combinatorial4ct.v`, `fourcolor.v` | `Combinatorial4ct`, `FourColorThm`, `Solution.lean` | |
| `dedekind.v`, `theories/reals/*.v` | none | Mathlib's `ℝ` instead |

The main theorems:

| Coq | Lean |
|---|---|
| `fourcolor.four_color` | `FourColor.RealPlane.four_color` (`Solution.lean`); from a hypothesis: `RealPlane.four_color_of_reducibility` |
| `fourcolor.four_color_finite` | `FourColor.RealPlane.four_color_finite`; from a hypothesis: `RealPlane.four_color_finite_of_reducibility` |
| `finitize.compactness_extension` | `RealPlane.compactness_extension` (four colors), `RealPlane.compactness_extension_with` (any number) |
| `discretize.discretize_to_hypermap` | `RealPlane.discretize_to_hypermap` |
| `combinatorial4ct.four_color_hypermap` | `FourColor.four_color_hypermap`; from a hypothesis: `four_color_hypermap_of_reducibility` |
| `unavoidability.unavoidability` | `FourColor.unavoidability` |
| `present.reducibility`, `excluded_arity`, `valid_hub` | `Reducibility`, `ExcludedArity`, `Hypermap.ValidHub` |
| `present5.exclude5` … `present11.exclude11` | `exclude5` … `exclude11` |
| `reducibility.the_reducibility` | `theReducibility : ReducibleInRange 0 633 theConfigs`, restated as `FourColor.reducibility_holds : Reducibility` |
| `cfreducible.cfreducible`, `reducible_in_range`, `cat_reducible_range` | `CfReducible`, `ReducibleInRange`, `cat_reducible_range` |
| `cfreducible.check_reducible_valid` | `cfreducible_of_engine` |
| `coloring.four_colorable`, `minimal_counter_example`, `C_reducible` | `Hypermap.FourColorable`, `Hypermap.MinimalCounterExample`, `Hypermap.CReducible` |
| `geometry.planar_bridgeless`, `hypermap.planar` | `Hypermap.PlanarBridgeless`, `Hypermap.Planar` |

The appendix below keeps the detailed name maps of the planarity layer.

## Deviations from the Coq development

### In the theorem statement (`Challenge.lean`)

* **The reals.** Coq's `four_color` holds for every model of its axiomatized reals
  (`Real.model`, `reals/real.v`); the Lean statement is about Mathlib's `ℝ`. The definitions use
  only the order of the reals, and all models are isomorphic as ordered fields (Coq's
  `realcategorical.v`; in Mathlib, `ConditionallyCompleteLinearOrderedField.inducedOrderRingIso`),
  so the two statements are equivalent.
* **Strict order.** Coq's `Real.lt x y` is notation for `¬ Real.le y x`; Lean writes `x < y`,
  which is equivalent on the linear order of `ℝ` (`not_le`).
* **Extensionality.** Coq's reals are a setoid of denotations, so a Coq region need not be
  extensional; over `ℝ`, a quotient, every region is. Open regions are extensional in Coq too, so
  simple maps are unaffected.
* **Syntax.** Records whose first field is a coercion (`simple_map_plain`,
  `finite_simple_map_simple`, `coloring_plain`) are structures with `extends` (fields
  `toPlainMap`, `toSimpleMap`). `exists2 x, P & Q` is `∃ x, P ∧ Q`, and `Peano.lt i n` is `i < n`.
  The function of `at_most_regions` gets its inferred type `ℕ → Point`. Names follow Lean's
  conventions (`plain_map` → `PlainMap`, `nonempty` → `NonemptyRegion`, `open` → `Open`,
  `corner_map` → `cornerMap`, …), and the endpoints of an interval are named `lo` and `hi`. None
  of this changes the meaning.

### In the other statements

* **Hypermaps.** Coq's `hypermap` bundles a `finType` of darts. Lean's `Hypermap D` takes the
  dart type as a parameter, with `[Fintype D]` and `[DecidableEq D]` where needed (a `finType`
  has decidable equality). So `discretize_to_hypermap` concludes
  `∃ (D : Type) (_ : Fintype D) (_ : DecidableEq D) (G : Hypermap D), G.PlanarBridgeless ∧
  (G.FourColorable → ColorableWith 4 m0)`, and `four_color_hypermap` and `unavoidability` hold
  for dart types in every universe.
* **Minimality.** `MinimalCounterExample` quantifies its minimality over the hypermaps whose
  darts live in the same universe as `D`, where Coq's covers all hypermaps. Every finite type
  has a copy in every universe, so the two notions agree.
* **Number of colors.** `compactness_extension` is stated for four colors, as `fourcolor.v`
  uses it; Coq's statement for any number of colors is `compactness_extension_with`.
* **Reducibility as a hypothesis.** `four_color_hypermap`, `four_color_finite` and `four_color`
  are first proved from `Reducibility` (the `…_of_reducibility` theorems), then instantiated with
  `theReducibility`. `theReducibility` is stated as `ReducibleInRange 0 633 theConfigs`;
  `FourColor.reducibility_holds` restates it with `theConfigs.length`, as Coq's `reducibility` does,
  using `length_theConfigs`.
* **Props.** Boolean predicates and `reflect` lemmas become `Prop`s and `↔`; `eqm` (equality of
  hypermaps up to extensionality) becomes `=`.

### In the proofs

These are checked by the kernel, so they cannot affect soundness; they matter for comparing the
two developments.

* **Reducibility engine.** Coq's decision procedure on trees of colorings (`ctree.v`, `gtree.v`,
  `ctreerestrict.v`, `gtreerestrict.v`, `initctree.v`, `initgtree.v`, `kempetree.v`, the `ctree`
  parts of `cfcolor.v`, `cfcontract.v` and `cfreducible.v`, and the `job*`/`task*` files) walks
  trees of individual colorings; ported faithfully and run in the kernel, it would take hundreds
  of hours for a single configuration of ring size 14. It is replaced by a bit-parallel engine
  designed for the kernel (`FourColor/Engine/`, with an overview in `FourColor/Engine.lean`).
  What it proves for each configuration is Coq's `cfreducible`, unchanged: `CfReducible cf` is a `CReducible`
  record with the fields of Coq's `C_reducible`. `cfreducible_of_engine` replaces
  `check_reducible_valid`.
* **Birkhoff check.** `birkhoff.v`'s `Birkhoff_check2` game is replayed on the same engine
  (`Engine/Birkhoff.lean`, `bk2_false`), so the check `BirkhoffCheck h m` (Coq `Birkhoff_check`)
  carries the engine's data instead of Coq's trees; the theorem `birkhoff` (Coq `Birkhoff`)
  keeps its Coq statement.
* **Presentations as data.** The Coq tactic scripts `present5.v` … `present11.v` become case
  trees (`PTree`), generated by `scripts/present_gen.py` and checked by `checkTree`, whose
  soundness is proved once (`checkTree_sound`). The leaves use kernel-fast versions of the checks,
  each proved equal to the faithful one (`FourColor/Fast/`), and quiz trees pruned by certificate
  masks, sound for any mask. Coq's `vm_compute`d `the_quiz_tree` and `the_drule_fork` are
  literals that the kernel proves equal to their definitions (`theQuizTree_eq`,
  `theDruleFork_eq`).
* **Configuration data.** `scripts/gen_configurations.py` translates the 633 configurations into
  explicit structure literals, checked against the `Config` notation; each docstring quotes the
  Coq text.
* **Classical logic** is used freely, for instance for the case split on colorability in
  `four_color_hypermap`, which Coq decides constructively with `decide_colorable`. Coq's axioms
  for the reals already imply excluded middle.
* **Planarity layer.** math-comp's `rot n p` is `List.rotate p n` there (they differ only when
  `n` exceeds the length of `p`, and the rotation lemmas hold for all `n`); from `Color.lean` on,
  `rot` and `rotr` are defined literally. `nComp e a` counts the components that meet `a`, which
  equals math-comp's `n_comp` on the closed sets where it is used. `finv` of a hypermap
  permutation is written as the composite of the other two. `froot` uses `Classical.epsilon`,
  `mem2` is defined recursively, and the section-local lemmas of `walkup.v` are public.
* **Structure.** The proofs follow Coq's where practical, and many are restructured; each
  module's docstring lists its porting notes.

## Kernel time and Palomar's budget

Palomar builds `Solution`, exports it, and replays the export with con-ron, nanoda and
`leanchecker`, one after another, within 19,800 s of wall-clock time on a 16-core, 32 GB runner,
setup and build included. A rejection by any checker fails the submission. The proof was
designed for this budget: about 2.3 h of single-threaded `leanchecker` time in all, and rules
that keep nanoda and con-ron fast: no `Nat.pow`, `/`, `%` or `Nat.testBit` on big operands, no
big right shifts, `Nat` literals of at most 8 Kbit, shallow terms, and at most about 1 GB and
30 s per declaration.

| Part | Cost |
|---|---|
| Unavoidability: presentations `P5` … `P11` | about 0.4 h of kernel time at build, estimated (`P7`, `P8`, `P9` about 0.09, 0.13 and 0.13 h; `P10` 124 s; `P11` 18 s; `P6` 8 s; `P5` 0.08 s) |
| Unavoidability: quiz tree and drule forks | about 57 s at build; `theQuizTree_eq` and `theDruleFork_eq` with their dependencies: `leanchecker` 57 s, nanoda 46 s, con-ron 100 s |
| Reducibility: 633 configurations | about 9,400 s of CPU to build the 633 certificates (elaboration and kernel), about 4,800 s of it for the 137 of ring size 14; the slowest, cf613, takes 95 s, and none needs more than 1.4 GB of private memory |
| The whole proof, in Palomar's checkers | `leanchecker` about 4,700 s (1.3 h, single-threaded), nanoda about 1,300 s (4 threads), con-ron about 860 s (16 workers); the export is 570 MB |

The last two rows come from the final run.

## Other formalizations

* **Gonthier and Werner's Coq proof** ([math-comp/fourcolor](https://github.com/math-comp/fourcolor),
  2005; now maintained as coq-community/fourcolor) is the proof this repository ports. It checks
  the reducibility of the 633 configurations with Coq's bytecode virtual machine.
* **Chris Emery's Lean 4 formalization** ([corun1024/4ct](https://github.com/corun1024/4ct)),
  public before this one, is an independent and complete Lean 4 proof of the same statement. It
  also follows Gonthier and Werner's proof, and it too was written mostly by AI (Claude Fable
  5.1). Like this one, it uses only the three standard axioms and checks every computation in
  Lean's kernel, without `native_decide`.

The main difference is where the proof lives. In `corun1024/4ct`, the reducibility certificates
are produced before the Lean build, by C and Python programs (`scripts/gen_certificates.sh` and
`tools/`), and they are not part of that repository. The kernel checks them, so those programs
need not be trusted. But the Lean files of that repository do not prove the theorem on their own,
and building it needs gcc and Python as well as Lean. Here, every file of the proof is Lean
source in this repository. The certificates are computed during the build by Lean code
(`#engine_certify` in `FourColor/Engine/Gen.lean`), so the Lean toolchain alone builds and checks
everything. This is also why Palomar's pipeline, which only runs `lake build` on the committed
files, can build this proof as it stands. Python scripts were used during development to write
some of the Lean files here (the 633 configurations and the unavoidability case trees), but their
output is committed as Lean source, and no program outside Lean runs when the proof is built or
checked.

The two developments also differ in these ways:

* **Statement.** Its statement uses Mathlib's topology and proves its elementary notions equal to
  Mathlib's `IsOpen`, `closure` and `IsPreconnected`. Ours uses only the elementary definitions
  transcribed from `realplane.v`, over Mathlib's `ℝ`.
* **Style.** Its code is rewritten in idiomatic Mathlib style; ours stays close to the Coq files,
  with a Coq → Lean name map.
* **Planarity.** It leaves out the converse direction of the planarity–Jordan equivalence, which
  the proof does not use; this repository ports both directions.
* **Cost.** It reports 7.5 core-hours of kernel work, with single modules needing up to 20 GB of
  memory and its own build scheduler. Here the whole build took about 3.4 core-hours of CPU, with
  at most 1.4 GB of private memory for any certificate, using plain `lake build`.
* **Palomar.** This repository is packaged for the Palomar registry and has passed a rehearsal
  of its pipeline.

## Licence

This repository is a port of math-comp/fourcolor. The Lean port is licensed under the Apache
License 2.0 (`LICENSE`). `NOTICE` credits the Coq development, by Georges Gonthier et al.,
© 2006–2018 Microsoft Corporation and Inria, distributed under CeCILL-B (text in
`LICENSES/CeCILL-B.txt`), and the configurations and discharging rules of Robertson, Sanders,
Seymour and Thomas (J. Combin. Theory Ser. B 70, 1997). Lean and Mathlib, which are not
redistributed here, are under the Apache License 2.0.

## History of this repository

This repository starts from the final state of a private development repository, whose history
is not published. Since the final run, the Lean files have changed only in their comments.

## Appendix: name maps of the planarity layer

The planarity layer (`hypermap.v`, `walkup.v`, `jordan.v`, `geometry.v`) was ported first and
compared with Coq statement by statement. Everything lives in `namespace FourColor.Hypermap` and
is used with dot notation, e.g. `G.Planar`, `G.genus`, `G.WalkupE z`.

<details>
<summary><code>hypermap.v</code></summary>

| Coq | Lean |
|---|---|
| `hypermap`, `Hypermap`, `edgeK`, `faceK`, `nodeK`, `edgeI`, `nodeI`, `faceI` | `Hypermap D`, `.edgeK`, `faceK`, `nodeK`, `edgeI`, `nodeI`, `faceI` |
| `cedge`, `cnode`, `cface`, `cedgeC`, `same_cedge`, `cedge1`, `cedge1r` (and node/face versions) | same names |
| `glink`, `glinkE/N/F`, `glinkC`, `gcomp` | same names |
| `connected` / `connectedb` | `Connected` |
| `Euler_lhs`, `Euler_rhs`, `genus`, `even_genus` | `eulerLhs`, `eulerRhs`, `genus`, `EvenGenus` |
| `planar` / `planarb` | `Planar` |
| `clink` (+ `clinkP`), `clinkN`, `clinkF`, `clinkC`, `clink_glink`, `connected_clink` | `clink` (defined in `clinkP` form), same names |
| `Moebius_path`, `Jordan` | `MoebiusPath`, `Jordan` |
| `permN`, `permF`, `dual`, `mirror` and their `gcomp_*`, `connected_*`, `genus_*`, `planar_*` lemmas | same names |
| `Jordan_dual`, `Jordan_mirror`, `cnode_mirror`, `cface_mirror`, `order_mirror_edge`, `clink_mirror` | `jordan_dual`, `jordan_mirror`, same names |
| `eqm`, `dual_inv`, `mirror_inv` | `=`, `dual_dual`, `mirror_mirror` |

</details>

<details>
<summary><code>walkup.v</code></summary>

| Coq | Lean |
|---|---|
| `skip1`, `skip`, `inj_skip`, `valE_skip`, `base_skip`, `fconnect_skip`, `fcard_skip` | same names |
| `skip_edge1`, `skip_edge`, `skip_edgeK` | `skipEdge1`, `skipEdge`, `skipEdgeK` |
| `WalkupE`, `WalkupN`, `WalkupF`, `WalkupI`, `WalkupI_eq`, `Walkup_seq` | same names |
| `base_skip_edge`, `glink_fp_skip_edge`, `base_clink_Walkup`, `card_Walkup`, `card_S_Walkup` | same names |
| `cross_edge`, `skip_edge_domain`, `same_cskip_edge`, `sub_cskip_edge`, `cskip_edge_merge` | `crossEdge`, `skipEdgeDomain`, same names |
| `genus_WalkupE_eq`, `le_genus_WalkupE`, `planar_WalkupE`, `even_genus_WalkupE`, `planar_WalkupN`, `planar_WalkupF` | same names |
| `Jordan_WalkupE` | `jordan_WalkupE` |
| section `Let`s: `z_comp`, `z_barb`, `z_barb_z`, `clink_at_G`, `z_comp_preimage`, `z_barb_comp`, `disconnected`, `n_comp_z`, `not_cross_edge_Walkup`, `disconnected_cross_edge`, `not_cross_connected`, `fcard_skip_edge`, `n_comp_glink_Walkup`, `Euler_lhs_WalkupE`, `Euler_rhs_WalkupE` | `zComp`, `ZBarb`, `zBarb_iff`, `connect_clink_val`, `zComp_preimage`, `zBarb_comp`, `Disconnected`, `nCompZ`, `not_cross_edge_Walkup`, `disconnected_cross_edge`, `not_cross_connected`, `fcard_skip_edge`, `nComp_glink_Walkup`, `euler_lhs_WalkupE`, `euler_rhs_WalkupE` (made public) |

</details>

<details>
<summary><code>jordan.v</code></summary>

| Coq | Lean |
|---|---|
| `even_genusP` | `evenGenus : G.EvenGenus` |
| `Euler_le` | `euler_le : G.eulerRhs ≤ G.eulerLhs` |
| `planar_Jordan` | `jordan_of_planar : G.Planar → G.Jordan` |
| `Euler_tree` | `euler_tree : G.Jordan → ∃ y, G.cedge x y ∧ (G.clink y y ∨ ¬ G.crossEdge y)` |
| `Jordan_planar` | `planar_of_jordan : G.Jordan → G.Planar` |
| `planarP` | `planar_iff_jordan : G.Planar ↔ G.Jordan` |

</details>

<details>
<summary><code>geometry.v</code></summary>

Every definition and lemma is ported. Prop-valued definitions are in UpperCamelCase; everything
else keeps its Coq name.

| Coq | Lean |
|---|---|
| `bridgeless`/`bridgelessb`, `loopless` | `Bridgeless`, `Loopless` |
| `arity`, `fband`, `kernel`, `fproj` | same names |
| `simple`, `scycle`, `sfcycle`, `simple_rec` | `Simple`, `SCycle`, `SFCycle`, `SimpleRec` |
| `plainb`, `plain`, `cubicb`, `cubic`, `precubic`, `pentagonal`, `quasicubic` | `PlainOn`, `Plain`, `CubicOn`, `Cubic`, `Precubic`, `Pentagonal`, `Quasicubic` |
| `planar_bridgeless`, `plain_cubic`, …, `scycle_planar_bridgeless_plain_quasicubic_connected` (13 records) | `PlanarBridgeless`, `PlainCubic`, …, `SCyclePlanarBridgelessPlainQuasicubicConnected` (structures; `:>` fields become `extends`) |
| `quasicubic_Euler`, `cubic_Euler` | `quasicubic_euler`, `cubic_euler` |
| `rlink`, `srpath`, `srcycle`, `rlink_connected`, `adj`, `chordless`, `insertE` | `rlink`, `SRPath`, `SRCycle`, `RLinkConnected`, `adj`, `Chordless`, `insertE` |
| all other lemmas (`plainP`, `cubicP`, `simple_cat`, `simplify_rlink`, `srcycleI`, `adjC`, `chordless_rot`, `insertE_rot`, …) | same names |

Omitted: `eqm_bridgeless` and `eqm_loopless`, which are trivial because map equality is `=`, and
`adj_app_pred`, a Coq canonical-structure device.

</details>
