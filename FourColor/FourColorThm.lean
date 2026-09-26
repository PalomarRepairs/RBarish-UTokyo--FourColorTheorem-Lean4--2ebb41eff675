/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Reducibility
import FourColor.Combinatorial4ct

/-!
# The Four Color Theorem, unconditionally

`FourColor/Combinatorial4ct.lean` proves the theorems from `Reducibility` as a hypothesis;
this module plugs in `theReducibility` (`FourColor/Reducibility.lean`: the 633 configurations
are C-reducible, checked by the kernel through the generated certificates
`FourColor/Reducibility/CfNNN.lean`).  `FourColor.lean` does not import it, so `lake build`
leaves out the 633 configurations.  The final statement, `FourColor.RealPlane.four_color` with
exactly the statement of `Challenge.lean`, is in `Solution.lean`
(`compactness_extension four_color_finite`, as in Coq's `fourcolor.v`).

| Coq | Lean |
|---|---|
| `the_reducibility : reducibility` | `FourColor.theReducibility`, restated as `FourColor.reducibility_holds` |
| `combinatorial4ct.four_color_hypermap` | `FourColor.four_color_hypermap` |
| `fourcolor.four_color_finite` | `FourColor.RealPlane.four_color_finite` |
-/

namespace FourColor

universe u

/-- Coq `the_reducibility : reducibility`: the 633 configurations of `theConfigs` are
C-reducible, in the form of `present.v`'s `reducibility` (`theReducibility`, whose bound `633` is
the length of `theConfigs`). -/
theorem reducibility_holds : Reducibility := by
  unfold Reducibility
  rw [length_theConfigs]
  exact theReducibility

/-- Coq `four_color_hypermap` (`combinatorial4ct.v`): every planar bridgeless finite hypermap is
four colorable. -/
theorem four_color_hypermap {D : Type u} [Fintype D] [DecidableEq D] (G : Hypermap D)
    (hG : G.PlanarBridgeless) : G.FourColorable :=
  four_color_hypermap_of_reducibility reducibility_holds G hG

namespace RealPlane

/-- Coq `four_color_finite` (`fourcolor.v`): every finite simple map of the real plane has a
coloring with at most four colors. -/
theorem four_color_finite (m : Map) (h : FiniteSimpleMap m) : ColorableWith 4 m :=
  four_color_finite_of_reducibility reducibility_holds m h

end RealPlane

end FourColor
