/-
Copyright (c) 2026. Lean 4 port of the planarity part of the Coq/Rocq formal proof
of the Four Color Theorem by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Walkup.Basic
import FourColor.Walkup.Edge
import FourColor.Walkup.Comp
import FourColor.Walkup.Genus
import FourColor.Walkup.Jordan

/-!
# The Walkup construction  (port of `walkup.v`)

Aside from the definitions (`Walkup/Basic.lean`), the main results are that both the Euler
and Jordan planarity conditions are preserved by all Walkup transforms; these are used to
prove the equivalence of these two conditions in `Jordan.lean`.
-/
