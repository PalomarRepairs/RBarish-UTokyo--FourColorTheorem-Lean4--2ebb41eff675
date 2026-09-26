/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Gen

/-!
# The delta-swap networks of ring size 12 (generated at elaboration time)

`#engine_nets 12` (see `FourColor/Engine/Gen.lean`) routes, as Beneš networks, the color
transposition `Color1 ↔ Color2` of the packed layout of ring size 12 and the conversion from the
base-3 layout of the prefixes of length 11 into the packed layout, and adds

* `FourColor.Engine.tauNet12 : Net` and `FourColor.Engine.cnvNet12 : Net` (literals);
* `FourColor.Engine.tauSpec12 : TauSpec 12 tauNet12` and
  `FourColor.Engine.cnvSpec12 : CnvSpec 12 cnvNet12`, proved by kernel evaluation of `tauCheck` and
  `cnvCheck` (`tauSpec_of_check`, `cnvSpec_of_check`).

They are used by the certificates of the configurations of ring size 12
(`#engine_certify`).
-/

#engine_nets 12
