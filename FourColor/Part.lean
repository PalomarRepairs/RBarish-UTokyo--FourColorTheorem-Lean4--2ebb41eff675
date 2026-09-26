/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Part.Basic
import FourColor.Part.Fit
import FourColor.Part.Mirror
import FourColor.Part.Converse
import FourColor.Part.Split

/-!
# Parts  (port of `part.v`)

Umbrella module for the port of `part.v`:

* `FourColor.Part.Basic`: the types `Prange`, `Part`, `SubpartLoc`, `PartRel`, the concrete
  syntax (Coq modules `PartSyntax` and `SublocSyntax`), and all the computable operations on
  ranges and parts (comparison, meet, list operations, accessors, mirror, converse, split) with
  their combinatorial lemmas.
* `FourColor.Part.Fit`: the fitting semantics (`fitp`, `exactFitp`, `tightFitp`), its
  interaction with the list operations, comparison and meet, and `PartUpdate`.
* `FourColor.Part.Mirror`: `fitp_mirror`, `fitp_sym` (plain cubic maps).
* `FourColor.Part.Converse`: `invFace2`, `fitp_converse` (plain cubic pentagonal maps).
* `FourColor.Part.Split`: `fitp_pcons_`, `exact_fitp_pcons_`, `fitc`, `fitp_split`
  (pentagonal maps).
-/
