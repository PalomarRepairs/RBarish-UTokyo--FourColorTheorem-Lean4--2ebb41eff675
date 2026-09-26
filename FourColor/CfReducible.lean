/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Configurations
import FourColor.CfContract
import FourColor.Engine.Reducible

/-!
# C-reducibility of configurations (port of `cfreducible.v`)

Only C-reducibility is used: the source data of the D-reducible configurations has been
completed with an arbitrary contraction.

* `CfReducible cf` (math-comp `cfreducible`): `cfmap cf` is semantically C-reducible with
  contract `cfcontract cf`.
* `ReducibleInRange j1 j2 cfs` (math-comp `reducible_in_range`): all the configurations in the
  range `[j1, j2)` of `cfs` are C-reducible (`cf000` being the default value of `nth`).
* `cat_reducible_range` (math-comp `cat_reducible_range`): concatenation of ranges.
* `cfreducible_of_engine` (new): `CfReducible cf` from the checks of the reducibility engine,
  via `cReducible_of_checks` (`Engine/Reducible.lean`) and `contractProg_spec`
  (`CfContract/Spec.lean`).  `#engine_certify` (`Engine/Gen.lean`) matches its arguments by
  name.

The ctree-based decision procedure of `cfreducible.v` (`check_reducible`,
`check_reducible_valid`, `check_reducible_in_range` and the tactics `CheckReducible`,
`CatReducible`) is replaced by the engine: `cfreducible_of_engine` plays the role of
`check_reducible_valid`, and the generated modules `FourColor/Reducibility/CfNNN.lean` the role
of the `job*`/`task*` files.  `cf000` (defined in `cfreducible.v`) is in `Configurations.lean`.
-/

namespace FourColor

open Hypermap Engine

/-- math-comp `cfreducible cf`: `cfmap cf` is C-reducible, with ring `cfring cf` and contract
`cfcontract cf`. -/
def CfReducible (cf : Config) : Prop :=
  (cfmap cf).pointee.CReducible (cfring cf) (cfcontract cf)

/-- math-comp `reducible_in_range j1 j2 cfs`: all the configurations of `cfs` with an index in
`[j1, j2)` are C-reducible (`nth cf000 cfs i` is `cfs.getD i cf000`). -/
def ReducibleInRange (j1 j2 : Nat) (cfs : List Config) : Prop :=
  ∀ i, j1 ≤ i → i < j2 → CfReducible (cfs.getD i cf000)

/-- math-comp `cat_reducible_range`. -/
theorem cat_reducible_range {j1 j2 : Nat} {cfs : List Config}
    (red_12 : ReducibleInRange j1 j2 cfs) {j3 : Nat} (red_23 : ReducibleInRange j2 j3 cfs) :
    ReducibleInRange j1 j3 cfs := by
  intro i h1 h3
  rcases Nat.lt_or_ge i j2 with h | h
  · exact red_12 i h1 h
  · exact red_23 i h h3

/-- Not in the Coq development: the empty range. -/
theorem reducible_in_range_nil (j : Nat) (cfs : List Config) : ReducibleInRange j j cfs :=
  fun _ h1 h2 => absurd (Nat.lt_of_le_of_lt h1 h2) (Nat.lt_irrefl _)

/-- Not in the Coq development: a range extended downwards by one configuration (used by the
generated `FourColor/Reducibility.lean`, which collates the certificates in blocks, so that no
proof term is nested deeply). -/
theorem reducible_in_range_cons {j j2 : Nat} {cfs : List Config}
    (h : CfReducible (cfs.getD j cf000)) (t : ReducibleInRange (j + 1) j2 cfs) :
    ReducibleInRange j j2 cfs := by
  intro i h1 h2
  rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
  · exact h
  · exact t i hlt h2

/-- Not in the Coq development: a list all of whose members are C-reducible is C-reducible on
the range `[0, length)`. -/
theorem reducible_in_range_of_forall {cfs : List Config} (h : ∀ cf ∈ cfs, CfReducible cf) :
    ReducibleInRange 0 cfs.length cfs := by
  intro i _ hi
  rw [List.getD_eq_getElem _ _ hi]
  exact h _ (List.getElem_mem hi)

/-- **C-reducibility from the checks of the reducibility engine**: the
replacement for math-comp `check_reducible_valid`.  The binder names are matched by
`#engine_certify`. -/
theorem cfreducible_of_engine {cf : Config} {r : Nat} (hr : cprsize cf.cfprog = r)
    (hr2 : 2 ≤ r) {tau cnv : Net} (htau : TauSpec r tau) (hcnv : CnvSpec r cnv) {cpc : Cprog}
    (hctr : contractProg cf = some cpc) (hrc : cprsize cpc = r) {H0 Hn : List Nat}
    (hinit : checkInit r cnv cf.cfprog H0 = true)
    (hreach : ReachN r tau (expand r H0) (expand r Hn))
    (hfinal : checkFinal r cnv cpc Hn = true) : CfReducible cf := by
  subst hr
  obtain ⟨hv, hcc⟩ := contractProg_spec hctr
  exact cReducible_of_checks hr2 hrc htau hcnv hv
    (fun et het => hcc et (by rw [cfring, List.reverse_reverse]; exact het)) hinit hreach hfinal

end FourColor
