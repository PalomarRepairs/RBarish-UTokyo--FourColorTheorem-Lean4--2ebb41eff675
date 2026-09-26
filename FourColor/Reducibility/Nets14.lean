/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Gen

/-!
# The delta-swap networks of ring size 14 (generated at elaboration time)

`#engine_nets 14` (see `FourColor/Engine/Gen.lean`) routes, as Beneš networks, the color
transposition `Color1 ↔ Color2` of the packed layout of ring size 14 and the conversion from the
base-3 layout of the prefixes of length 13 into the packed layout, and adds

* `FourColor.Engine.tauNet14 : Net` and `FourColor.Engine.cnvNet14 : Net` (literals);
* `FourColor.Engine.tauSpec14 : TauSpec 14 tauNet14` and
  `FourColor.Engine.cnvSpec14 : CnvSpec 14 cnvNet14`, proved by kernel evaluation of `tauCheck` and
  `cnvCheck` (`tauSpec_of_check`, `cnvSpec_of_check`).

They are used by the certificates of the configurations of ring size 14
(`#engine_certify`).
-/

#engine_nets 14
