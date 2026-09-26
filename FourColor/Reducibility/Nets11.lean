/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Gen

/-!
# The delta-swap networks of ring size 11 (generated at elaboration time)

`#engine_nets 11` (see `FourColor/Engine/Gen.lean`) routes, as Beneš networks, the color
transposition `Color1 ↔ Color2` of the packed layout of ring size 11 and the conversion from the
base-3 layout of the prefixes of length 10 into the packed layout, and adds

* `FourColor.Engine.tauNet11 : Net` and `FourColor.Engine.cnvNet11 : Net` (literals);
* `FourColor.Engine.tauSpec11 : TauSpec 11 tauNet11` and
  `FourColor.Engine.cnvSpec11 : CnvSpec 11 cnvNet11`, proved by kernel evaluation of `tauCheck` and
  `cnvCheck` (`tauSpec_of_check`, `cnvSpec_of_check`).

They are used by the certificates of the configurations of ring size 11
(`#engine_certify`).
-/

#engine_nets 11
