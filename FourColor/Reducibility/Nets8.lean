/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Gen

/-!
# The delta-swap networks of ring size 8 (generated at elaboration time)

`#engine_nets 8` (see `FourColor/Engine/Gen.lean`) routes, as Beneš networks, the color
transposition `Color1 ↔ Color2` of the packed layout of ring size 8 and the conversion from the
base-3 layout of the prefixes of length 7 into the packed layout, and adds

* `FourColor.Engine.tauNet8 : Net` and `FourColor.Engine.cnvNet8 : Net` (literals);
* `FourColor.Engine.tauSpec8 : TauSpec 8 tauNet8` and
  `FourColor.Engine.cnvSpec8 : CnvSpec 8 cnvNet8`, proved by kernel evaluation of `tauCheck` and
  `cnvCheck` (`tauSpec_of_check`, `cnvSpec_of_check`).

They are used by the certificates of the configurations of ring size 8
(`#engine_certify`).
-/

#engine_nets 8
