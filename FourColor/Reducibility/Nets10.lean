/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Gen

/-!
# The delta-swap networks of ring size 10 (generated at elaboration time)

`#engine_nets 10` (see `FourColor/Engine/Gen.lean`) routes, as Beneš networks, the color
transposition `Color1 ↔ Color2` of the packed layout of ring size 10 and the conversion from the
base-3 layout of the prefixes of length 9 into the packed layout, and adds

* `FourColor.Engine.tauNet10 : Net` and `FourColor.Engine.cnvNet10 : Net` (literals);
* `FourColor.Engine.tauSpec10 : TauSpec 10 tauNet10` and
  `FourColor.Engine.cnvSpec10 : CnvSpec 10 cnvNet10`, proved by kernel evaluation of `tauCheck` and
  `cnvCheck` (`tauSpec_of_check`, `cnvSpec_of_check`).

They are used by the certificates of the configurations of ring size 10
(`#engine_certify`).
-/

#engine_nets 10
