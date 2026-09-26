/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.FourColorThm

/-!
# The Four Color Theorem (Palomar solution module)

`FourColor.RealPlane.four_color`, with exactly the statement of `Challenge.lean`: every simple map
of the real plane has a coloring with at most four colors in which adjacent regions have
different colors.  The definitions used by the statement are the declarations of
`FourColor.RealPlane` (`FourColor/RealPlane.lean`), which are identical to those of
`Challenge.lean` (`scripts/check_challenge_sync.py` checks this).

As in Coq's `fourcolor.v`, the theorem is `compactness_extension` (`FourColor/Finitize.lean`)
applied to `four_color_finite` (`FourColor/FourColorThm.lean`), the Four Color Theorem for finite
simple maps, which rests on `discretize_to_hypermap` (`FourColor/Discretize.lean`) and
`four_color_hypermap`: the combinatorial proof (`FourColor/Combinatorial4ct.lean`,
`unavoidability` in `FourColor/Unavoidability.lean`) together with the C-reducibility of the 633
configurations (`theReducibility` in `FourColor/Reducibility.lean`).
-/

namespace FourColor.RealPlane

/-- **The Four Color Theorem** (Coq `four_color` in `fourcolor.v`): every simple map of the real
plane has a coloring with at most four colors in which adjacent regions have different colors. -/
theorem four_color (m : Map) (h : SimpleMap m) : ColorableWith 4 m :=
  compactness_extension four_color_finite m h

end FourColor.RealPlane
