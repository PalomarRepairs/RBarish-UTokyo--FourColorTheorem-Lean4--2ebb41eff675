/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Birkhoff.Check
import FourColor.Birkhoff.Valid
import FourColor.Birkhoff.Spoke

/-!
# The Birkhoff theorem (port of `birkhoff.v`)

The Birkhoff theorem states that a minimal coloring counter-example must be internally
5-connected; its consequences are that the minimum face arity is 5, and that cartwheels (the
radius-2 submap about a central hub face) are well-formed (in particular, the radius-1 spoke
ring about the hub is chordless).

* `FourColor/Birkhoff/Check.lean`: `cpcard`, `birkhoffCheck1`, the Birkhoff check
  `BirkhoffCheck h m` (reformulated on the reducibility engine, see `Engine/Birkhoff.lean`), and the
  checks `birkhoff2` … `birkhoff5` for the rings of size 2 to 5, by kernel computation (math-comp
  section `BirkhoffCheck` and module `BirkhoffCheckLemmas`).
* `FourColor/Birkhoff/Valid.lean`: `birkhoff_valid` (a successful check excludes nontrivial
  rings in a minimal counter-example, re-proved from the soundness `Engine.bk2_false` of the
  engine's Birkhoff game) and the theorem `birkhoff` (math-comp `Birkhoff_valid`, `Birkhoff`).
* `FourColor/Birkhoff/Spoke.lean`: `nontrivial_cycle2`, `double_dart`, the spoke ring
  (`spoke`, `spokeRing`, `scycle_spoke_ring`, `diskF_spoke_ring`, `chordless_spoke_ring`),
  `min_arity`, `fband_spoke_ring`, `adj11_edge`, `fcard_adj_adj`, `Adj01`, `adj12_edge`,
  `fcard_adj_max`, and `minimal_counter_example_is_plain_cubic_pentagonal`.

## Coq → Lean names

| Coq | Lean |
|---|---|
| `cpcard`, `card_cpmap` | `cpcard`, `card_cpmap` |
| `Birkhoff_check1` | `birkhoffCheck1` |
| `Birkhoff_check`, constructor `BirkhoffCheck` | `BirkhoffCheck`, `BirkhoffCheck.intro` (reformulated) |
| `ctree_pick_rev_rec`, `ctree_pick_rev`, `sumt_ctree_pick_rev`, `size_ctree_pick_rev`, `do_Birkhoff_check2`, `Birkhoff_check2` | not ported (replaced by `Engine.bk2`, `Engine.birkhoffCheck`) |
| `BirkhoffCheckLemmas.Birkhoff2` … `Birkhoff5` | `BirkhoffCheckLemmas.birkhoff2` … `birkhoff5` |
| `Birkhoff_valid` (with its local `chkbP`) | `Hypermap.birkhoff_valid` (`Hypermap.birkhoff_basis_trace`, `Hypermap.birkhoff_basis_den`) |
| `Birkhoff` | `Hypermap.birkhoff` (and `Hypermap.birkhoff_lt5` for rings of size `< 5`) |
| `nontrivial_cycle2`, `double_dart` | `Hypermap.nontrivial_cycle2`, `Hypermap.double_dart` |
| `spoke`, `inj_spoke`, `spoke_ring`, `mem_spoke_ring` | `Hypermap.spoke`, `inj_spoke`, `spokeRing`, `mem_spoke_ring` |
| `next_spoke_ring`, `scycle_spoke_ring`, `diskF_spoke_ring` | same names |
| `chordless_spoke_ring`, `size_spoke_ring`, `min_arity` | same names |
| `fband_spoke_ring`, `adj11_edge`, `fcard_adj_adj` | same names |
| `adj01`, `adj12_edge`, `fcard_adj_max` | `Adj01`, `adj12_edge`, `fcard_adj_max` |
| `minimal_counter_example_is_plain_cubic_pentagonal` (and its coercion) | same name, `MinimalCounterExample.toPlainCubicPentagonal` |
-/
