/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Gen

/-!
# The delta-swap networks of ring size 6 (generated at elaboration time)

`#engine_nets 6` (see `FourColor/Engine/Gen.lean`) routes, as Beneš networks, the color
transposition `Color1 ↔ Color2` of the packed layout of ring size 6 and the conversion from the
base-3 layout of the prefixes of length 5 into the packed layout, and adds

* `FourColor.Engine.tauNet6 : Net` and `FourColor.Engine.cnvNet6 : Net` (literals);
* `FourColor.Engine.tauSpec6 : TauSpec 6 tauNet6` and
  `FourColor.Engine.cnvSpec6 : CnvSpec 6 cnvNet6`, proved by kernel evaluation of `tauCheck` and
  `cnvCheck` (`tauSpec_of_check`, `cnvSpec_of_check`).

They are used by the certificates of the configurations of ring size 6
(`#engine_certify`).
-/

#engine_nets 6
