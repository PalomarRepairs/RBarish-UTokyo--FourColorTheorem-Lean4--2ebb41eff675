/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Gen

/-!
# The delta-swap networks of ring size 2 (generated at elaboration time)

`#engine_nets 2` (see `FourColor/Engine/Gen.lean`) routes, as Beneš networks, the color
transposition `Color1 ↔ Color2` of the packed layout of ring size 2 and the conversion from the
base-3 layout of the prefixes of length 1 into the packed layout, and adds

* `FourColor.Engine.tauNet2 : Net` and `FourColor.Engine.cnvNet2 : Net` (literals);
* `FourColor.Engine.tauSpec2 : TauSpec 2 tauNet2` and
  `FourColor.Engine.cnvSpec2 : CnvSpec 2 cnvNet2`, proved by kernel evaluation of `tauCheck` and
  `cnvCheck` (`tauSpec_of_check`, `cnvSpec_of_check`).

They are used by the certificates of the configurations of ring size 2
(`#engine_certify`).
-/

#engine_nets 2
