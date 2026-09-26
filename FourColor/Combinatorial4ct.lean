/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Cube
import FourColor.Unavoidability
import FourColor.Discretize
import FourColor.Finitize

/-!
# The Four Color Theorem, from reducibility (ports of `combinatorial4ct.v` and `fourcolor.v`)

The 633 configurations are checked only when `Solution` is built, so this module proves the
theorems from `Reducibility` as a hypothesis, the way Coq's `unavoidability` takes it;
`FourColor/FourColorThm.lean` plugs in
`theReducibility` (`FourColor/Reducibility.lean`) to state them unconditionally.  This module
does not import `FourColor.Reducibility`.

* `four_color_hypermap_of_reducibility` (Coq `four_color_hypermap`): every planar bridgeless
  finite hypermap is four colorable.  As in Coq: its cube map is planar, bridgeless, plain and
  cubic (`planar_cube`, `bridgeless_cube`, `plain_cube`, `cubic_cube`), and is four colorable if
  `G` is (`cube_colorable`); by strong induction on the number of darts, a planar bridgeless
  plain precubic hypermap that is not four colorable while all smaller ones are is a minimal
  counter-example, which `unavoidability` excludes.
* `four_color_finite_of_reducibility` (Coq `four_color_finite` in `fourcolor.v`): every finite
  simple map of the real plane is four colorable (`discretize_to_hypermap`).
* `four_color_of_reducibility` (Coq `four_color`): the statement of `Challenge.lean`, under
  `Reducibility` (`compactness_extension`).

| Coq | Lean |
|---|---|
| `combinatorial4ct.four_color_hypermap` | `FourColor.four_color_hypermap_of_reducibility` |
| `fourcolor.four_color_finite` | `FourColor.RealPlane.four_color_finite_of_reducibility` |
| `fourcolor.four_color` | `FourColor.RealPlane.four_color_of_reducibility` |
-/

namespace FourColor

universe u

/-- The inductive argument of Coq's `four_color_hypermap`: under `Reducibility`, every planar
bridgeless plain precubic hypermap with fewer than `n` darts is four colorable. -/
theorem four_colorable_of_card_lt (hred : Reducibility) :
    ∀ (n : ℕ) (D : Type u) [Fintype D] (G : Hypermap D),
      G.PlanarBridgelessPlainPrecubic → Fintype.card D < n → G.FourColorable := by
  intro n
  induction n with
  | zero => intro D _ G _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro D _ G geoG hcard
    classical
    by_contra noncolG
    rcases Nat.lt_succ_iff_lt_or_eq.1 hcard with hlt | heq
    · exact noncolG (ih D G geoG hlt)
    · exact unavoidability hred G
        { toPlanarBridgelessPlainPrecubic := geoG
          noncolorable := noncolG
          minimal := fun D' _ G' geoG' hlt => ih D' G' geoG' (heq ▸ hlt) }

/-- Coq `four_color_hypermap` (`combinatorial4ct.v`), from `Reducibility`: every planar
bridgeless finite hypermap is four colorable. -/
theorem four_color_hypermap_of_reducibility (hred : Reducibility) {D : Type u} [Fintype D]
    [DecidableEq D] (G : Hypermap D) (hG : G.PlanarBridgeless) : G.FourColorable := by
  classical
  apply G.cube_colorable
  have geoGQ : G.cube.PlanarBridgelessPlainPrecubic :=
    { planar := G.planar_cube.2 hG.planar
      bridgeless := G.bridgeless_cube.2 hG.bridgeless
      plain := G.plain_cube
      precubic := G.cube.cubic_precubic G.cubic_cube }
  exact four_colorable_of_card_lt hred _ _ G.cube geoGQ (Nat.lt_succ_self _)

namespace RealPlane

/-- Coq `four_color_finite` (`fourcolor.v`), from `Reducibility`: every finite simple map of
the real plane has a coloring with at most four colors. -/
theorem four_color_finite_of_reducibility (hred : Reducibility) (m : Map)
    (h : FiniteSimpleMap m) : ColorableWith 4 m := by
  obtain ⟨D, _, _, G, hG, hcol⟩ := discretize_to_hypermap h
  exact hcol (four_color_hypermap_of_reducibility hred G hG)

/-- Coq `four_color` (`fourcolor.v`), from `Reducibility`: the statement of `Challenge.lean`
under the hypothesis that the 633 configurations are C-reducible. -/
theorem four_color_of_reducibility (hred : Reducibility) (m : Map) (h : SimpleMap m) :
    ColorableWith 4 m :=
  compactness_extension (four_color_finite_of_reducibility hred) m h

end RealPlane

end FourColor
