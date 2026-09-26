/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.RedPart.Zipper
import FourColor.RedPart.Pop
import FourColor.RedPart.Search

/-!
# Reducibility check for parts  (port of `redpart.v`)

Umbrella module for the port of `redpart.v`. `redpart qt p` checks that every 2-neighbourhood
that matches the part `p` contains the kernel of one of the configurations of the quiz tree `qt`;
its soundness is `Hypermap.no_fit_redpart`: in a plain cubic pentagonal map `G` in which no quiz
of `qt` fits (`∀ y, ¬ G.QztFit y qt`), if `redpart qt p = true` then no dart of `G` exactly fits
`p`. As in Coq, only soundness is proved: the decision procedure is complete only for quiz trees
with certain properties, which the tree of the 633 configurations has (the unavoidability proof
only performs checks that succeed).

* `FourColor.RedPart.Zipper`: zipper parts (`Zpart`, `ZpartLoc`), their darts (`zmove`, `zorg`,
  `zdart`), ranges (`zrange`), shifts (`zshiftl`, `zshiftr`) and steps (`zstepL`, `zstepR`,
  `zstepLt`, `zstepRt`), and the range arithmetic `topqa`, `fitqa`, `popqa`.
* `FourColor.RedPart.Pop`: popping ranges (`redPcons`, `redPop*`, `redPop`), matching questions
  against zipper parts (`fitqzp`, `redPopqzp`), quiz tree leaves (`redQztLeaf`) and lookup by
  range (`qztGetr`).
* `FourColor.RedPart.Search`: the search `redZpartRec`/`redZpart`, its correctness
  `not_red_zpart`, the check `redpart` and its soundness `no_fit_redpart`.

## Coq → Lean names

| Coq | Lean |
|---|---|
| `zpart_loc` (`Znil`, `Zhub`, ...), `zpart` (`Zpart`) | `ZpartLoc` (same constructor names), `Zpart` (`Zpart.mk`) |
| `zproper`, `zvalid`, `zpvalid` | `zproper`, `Zvalid`, `Zpvalid` |
| `zmove`, `zorg`, `zporg`, `zdart`, `zpfit`, `zpfit_top` | `G.zmove`, `G.zorg`, `G.zporg`, `G.zdart`, `G.Zpfit`, `G.ZpfitTop` |
| `hub_range`, `zrange`, `shift_part` | `hubRange`, `zrange`, `shiftPart` |
| `zshiftl`, `zshiftr`, `zfanL`, `zfanR`, `zstepL`, `zstepR` | same names |
| `topqa`, `fitqa`, `popqa`, `zfanLt`, `zfanRt`, `zstepLt`, `zstepRt` | same names |
| `red_pcons`, `red_popr_spoke`, `red_popr_hat`, `red_popl_spoke`, `red_popl_hat` | `redPcons`, `redPoprSpoke`, `redPoprHat`, `redPoplSpoke`, `redPoplHat` |
| `red_popl_fan[123][lr]`, `red_pop` | `redPoplFan[123][lr]`, `redPop` |
| `fitqzp`, `red_popqzp`, `red_qzt_leaf`, `qzt_getr` | `fitqzp`, `redPopqzp`, `redQztLeaf`, `qztGetr` |
| `red_zpart_rec`, `red_zpart`, `redpart` (local `loop`) | `redZpartRec`, `redZpart`, `redpart` (`redpart.loop`) |
| section `Let`s `De2`, `Dnf`, `Dn3`, `Dn2`, `Dne`, `Dfn`, `Dfnn`, `Ep0r` | `Hypermap.Redpart.De2`, ..., `Hypermap.Redpart.Ep0r` |
| all lemmas (`zvalid_init`, ..., `not_red_zpart`, `no_fit_redpart`) | same names (in `FourColor` or `FourColor.Hypermap`) |
-/
