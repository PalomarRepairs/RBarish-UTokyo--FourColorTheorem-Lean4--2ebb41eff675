/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Seq
import FourColor.FinGraph
import FourColor.Hypermap
import FourColor.Walkup
import FourColor.Jordan
import FourColor.Geometry
import FourColor.Examples
import FourColor.Color
import FourColor.Chromogram
import FourColor.Dyck
import FourColor.Grid
import FourColor.Matte
import FourColor.RealPlane
import FourColor.CfMap
import FourColor.Part
import FourColor.Coloring
import FourColor.Cube
import FourColor.Kempe
import FourColor.Patch
import FourColor.Quiz
import FourColor.Approx
import FourColor.Discharge
import FourColor.Configurations
import FourColor.Engine
import FourColor.Snip
import FourColor.Sew
import FourColor.Revsnip
import FourColor.GridMap
import FourColor.Discretize
import FourColor.Finitize
import FourColor.CfQuiz
import FourColor.CfContract
import FourColor.CfColor
import FourColor.Birkhoff
import FourColor.CfReducible
import FourColor.Contract
import FourColor.Embed
import FourColor.QuizTree
import FourColor.RedPart
import FourColor.Hubcap
import FourColor.Fast
import FourColor.QuizData
import FourColor.Present
import FourColor.Present.P5.Exclude
import FourColor.Present.P6.Exclude
import FourColor.Present.P7.Exclude
import FourColor.Present.P8.Exclude
import FourColor.Present.P9.Exclude
import FourColor.Present.P10.Exclude
import FourColor.Present.P11.Exclude
import FourColor.Unavoidability
import FourColor.Combinatorial4ct

/-!
# The Four Color Theorem in Lean 4 (umbrella)

Everything but the reducibility certificates.  `FourColor.Reducibility`, the generated modules
under `FourColor/Reducibility/` and `FourColor.FourColorThm` check the 633 configurations, so they
are built only for `Solution.lean` (by `lake build Solution` or `scripts/build_reducibility.sh`);
`FourColor.Combinatorial4ct` proves the theorems from `Reducibility` as a hypothesis.
-/
