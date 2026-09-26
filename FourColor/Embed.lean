/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Embed.Basic
import FourColor.Embed.Functor
import FourColor.Embed.HomRing
import FourColor.Embed.Perimeter
import FourColor.Embed.Full
import FourColor.Embed.Embedding
import FourColor.Embed.Disk
import FourColor.Embed.Rem
import FourColor.Embed.Contract

/-!
# Embeddings of C-reducible configurations (port of `embed.v`)

This is the crux of the Four Color Theorem proof: we build an injective embedding of a
configuration map from the partial embedding constructed by the part quiz, and derive a
contradiction from the reducibility property. The context is a C-reducible configuration
remainder hypermap `Gc` with embeddable perimeter `rc`, with a preembedding `h` from
`ac := kernel rc` into a minimal counter-example hypermap `Gm`; the main result is

* `Hypermap.not_embed_reducible : Gm.MinimalCounterExample → Gc.Embeddable rc →
  Gc.Preembedding Gm (Gc.kernel rc) h → Gc.CReducible rc cc → False`.

On the way (with `E : Hypermap.EmbedHyps Gm Gc rc h` bundling the first three hypotheses):

* `Gm.PreHomRing Gc rc h x p` : `x :: p` is an R-path in `ac` whose image by `h` is a simple
  R-cycle (math-comp `pre_hom_ring`);
* `Gm.embed Gc rc h` : an extension of `h` from `ac` to an embedding of `bc := [predC rc]`
  (math-comp `embed`, notation `h1`);
* `E.embedDisk` : the disk hypermap delimited by `rev_ring rc` in `Gc`, constructed explicitly
  on the darts `EmbdDart rc` of `bc` (math-comp `embed_disk`), with its perimeter
  `Gc.embdRing rc` and its injections `embd rc` into `Gc` and `Gm.embdd Gc rc h` into `Gm`
  (math-comp `embd_ring`, `embd`, `embdd`);
* `E.embedRem` : the remainder hypermap whose darts `Gm.EmbrDart Gc rc h` are the complement of
  the image of the disk darts off the border (math-comp `embed_rem`), with its perimeter
  `Gm.embrRing Gc rc h` and its injection `Gm.embr Gc rc h` into `Gm` (math-comp `embr_ring`,
  `embr`);
* `E.embedCotrace et` : `et` is the trace on `rotr 1 embr_ring` of a coloring of the remainder
  map (math-comp `embed_cotrace`).

## Files

* `FourColor/Embed/Basic.lean` : the section hypotheses `EmbedHyps` and the section `Let`s;
  shared helpers (namespace `FourColor.Embed`).
* `FourColor/Embed/Functor.lean` : `embed_functor`.
* `FourColor/Embed/HomRing.lean` : `cface_ac_h`, `cface_h_ac`, `cface_inj_embed`,
  `pre_hom_ring`, `intro_pre_hom_ring`, `trivial_hom_ring`.
* `FourColor/Embed/Perimeter.lean` : `rcN`, `edge_perimeter`, `Drrrc`, `URrrc`, `URerc`,
  `chordless_perimeter`, `fcard_adj_perimeter`, `adj_kernel_min`, `adj_kernel_max`.
* `FourColor/Embed/Full.lean` : `embed_full`.
* `FourColor/Embed/Embedding.lean` : `pre_embed_inj`, `embed`, `embed_cases`, `embedE`,
  `embedN`, `embed_inj`.
* `FourColor/Embed/Disk.lean` : the disk map `embed_disk` and its lemmas.
* `FourColor/Embed/Rem.lean` : the remainder map `embed_rem`, `embed_patch`, `planar_embr`,
  `plain_embr`, `cubic_embr`.
* `FourColor/Embed/Contract.lean` : `embed_sparse`, `embed_valid_contract`, `embed_cotrace`,
  `embed_closure`, `embed_contract`, `not_embed_reducible`.

## Coq → Lean names

In the table `E` is the bundle `E : Hypermap.EmbedHyps Gm Gc rc h`; `E.foo` is the theorem
`Hypermap.EmbedHyps.foo` applied to `E`.

| Coq | Lean |
|---|---|
| section `Embeddings`: variables `Gm Gc rc cc h`, hypotheses `cexGm`, `embedGc`, `embed_h` | `Hypermap.EmbedHyps Gm Gc rc h` (a `Prop` structure with fields `cexGm`, `embedGc`, `embed_h`) |
| hypothesis `Cred_cc : C_reducible rc cc` | explicit argument `Cred_cc : Gc.CReducible rc cc` |
| notations `ac`, `bc`, `hc`, `erc`, `ccr`, `h1`, `Gd`, `Gr`, `ppGm`, `h_spoke`; `Let rrc` | written out: `Gc.kernel rc`, `x ∉ rc`, `Gc.edgeCentral Gm h`, `rc.map Gc.edge`, `cc.map (Gm.embed Gc rc h)`, `Gm.embed Gc rc h`, `E.embedDisk`, `E.embedRem`, `E.embed_patch`, `E.h_spoke`; `rc.reverse` |
| `Let`s `ac_bc`, `acF` | `EmbedHyps.ac_bc`, `EmbedHyps.acF` |
| `Let`s `planarGm`, `bridge'Gm`, `plainGm`, `e2m`, `n3m`, `pentaGm`, `geoGm` | `E.planarGm`, `E.bridge'Gm`, `E.plainGm`, `E.e2m`, `E.n3m`, `E.pentaGm`, `E.geoGm` |
| `Let`s `planarGc`, `bridge'Gc`, `plainGc`, `cubicGc`, `e2c`, `n3c`, `geoGc`, `UNrc`, `cycNrc`, `Urc`, `UrcF` | `E.planarGc`, `E.bridge'Gc`, `E.plainGc`, `E.cubicGc`, `E.e2c`, `E.n3c`, `E.geoGc`, `E.UNrc`, `E.cycNrc`, `E.Urc`, `E.UrcF` |
| `Let`s `hcE`, `hF`, `hFn` | `E.hcE`, `E.hF`, `E.hFn` |
| `embed_functor` | `E.embed_functor` |
| `Let`s `cface_ac_h`, `cface_h_ac`; `cface_inj_embed` | `E.cface_ac_h`, `E.cface_h_ac`; `E.cface_inj_embed` |
| `pre_hom_ring`, `intro_pre_hom_ring`, `trivial_hom_ring` | `Hypermap.PreHomRing` (fields `rpath`, `sub_ac`, `scycle_map`), `E.intro_pre_hom_ring`, `E.trivial_hom_ring` |
| `Let rcN`, `edge_perimeter` | `E.rcN` (one step: `E.rc_node`), `E.edge_perimeter` |
| `Let`s `Drrrc`, `URrrc`, `URerc` | `EmbedHyps.Drrrc`, `E.URrrc`, `E.URerc` |
| `chordless_perimeter` (locals `nt_dFerc`, `dFerc_ac`) | `E.chordless_perimeter` (induction: private `nt_dF_aux`) |
| `fcard_adj_perimeter`, `adj_kernel_min`, `adj_kernel_max` | `E.fcard_adj_perimeter`, `E.adj_kernel_min`, `E.adj_kernel_max` |
| `embed_full` | `E.embed_full` (its three `suffices`: private `full_step2`, `full_shorten`, `full_step3`, `full_step4`) |
| `pre_embed_inj` | `E.pre_embed_inj` |
| `embed` | `Hypermap.embed` (`Gm.embed Gc rc h`), unfolded by `embed_of_mem`, `embed_of_edge`, `embed_of_node`, `embed_of_else` |
| `embed_cases`, `embedE`, `embedN`, `embed_inj` (local `bc_acN`) | `E.embed_cases`, `E.embedE`, `E.embedN`, `E.embed_inj` (`E.bc_acN`) |
| notation `ddart` | `Hypermap.EmbdDart rc` |
| `embd_edge`, `embd_face` | `Gc.embdEdge rc`, `Gc.embdFace rc` |
| `embd_edge_subproof`, `embd_node_subproof`, `embd_face_subproof`, `embed_disk_subproof` | same names (`E.embd_edge_subproof`, ...) |
| `Let`s `dedge`, `dnode`, `dface`; `embed_disk` | `E.embedDiskEdge`, `E.embedDiskNode`, `E.embedDiskFace`; `E.embedDisk` |
| `embd`, `embd_inj`, `codom_embd` | `Hypermap.embd rc`, `embd_inj`, `codom_embd` |
| `embd_ring`, `map_embd_ring`, `cface_embd`, `scycle_embd_ring` | `Gc.embdRing rc`, `E.map_embd_ring` (and `E.mem_embd_ring`), `E.cface_embd`, `E.scycle_embd_ring` |
| `Let`s `bGdE`, `bGd'E` | `E.bGdE`, `E.bGd'E` |
| `embdd`, `embdd_inj`, `embddE`, `embddN` | `Gm.embdd Gc rc h`, `E.embdd_inj`, `E.embddE`, `E.embddN` |
| `Let rdom'`, notation `rdart` | `Gm.embrDom Gc rc h` (and `E.mem_embrDom`), `Gm.EmbrDart Gc rc h` |
| `Let bGd_proj` | inlined: `∃ u, u ∈ Gc.embdRing rc ∧ x = Gm.embdd Gc rc h u` |
| `embr_node`, `embr_face` | `Gm.embrNode Gc rc h`, `Gm.embrFace Gc rc h` (unfolded by `E.embrNode_of_ring`, `embrNode_of_not`, `E.embrFace_of_ring`, `embrFace_of_not`) |
| `embr_edge_subproof`, `embr_node_subproof`, `embr_face_subproof`, `embed_rem_subproof` | same names |
| `Let`s `redge`, `rnode`, `rface`; `embed_rem` | `E.embedRemEdge`, `E.embedRemNode`, `E.embedRemFace`; `E.embedRem` |
| `embr`, `embr_inj`, `codom_embr` | `Gm.embr Gc rc h`, `embr_inj`, `codom_embr` |
| `embr_ring`, `map_embr_ring`, `ucycle_embr_ring` | `Gm.embrRing Gc rc h`, `E.map_embr_ring`, `E.ucycle_embr_ring` |
| `embed_patch`, `planar_embr`, `plain_embr`, `cubic_embr` | `E.embed_patch`, `E.planar_embr`, `E.plain_embr`, `E.cubic_embr` |
| `Let`s `mapEh1`, `ccE`, `cface_ac_h1`, `cface_h1`, `adj_ac_h1`, `orbitF_h1` | `E.mapEh1`, `E.ccE`, `E.cface_ac_h1`, `E.cface_h1`, `E.adj_ac_h1`, `E.orbitF_h1` |
| `embed_sparse`, `embed_valid_contract` | `E.embed_sparse`, `E.embed_valid_contract` |
| `embed_cotrace`, `embed_closure`, `embed_contract` | `E.embedCotrace`, `E.embed_closure`, `E.embed_contract` |
| `not_embed_reducible` | `Hypermap.not_embed_reducible` (explicit hypotheses) and `E.not_embed_reducible` |
| last `suffices` of `not_embed_reducible` (`rc = map face (rot 1 erc)`) | `E.Drc`, and its consequence `E.rc_map_rot` |

Lean-only helpers: in namespace `FourColor.Embed`, the `path.v` lemmas on `next`/`prev`
(`mem_next`, `next_map`, `prev_map`, `next_rev`, `next_cycle`, `prev_cycle`, `cycle_from_next`,
...), `fconnect_invariant`, `exists_first`, `cycle_mono`, `cycle_reverse`, `path_belast`,
`mem_arc`, `rlink_diskN_iff`, `diskN_path`, `diskN_path_rev`, `diskN_subset`, `simple_split`,
`fproj_eq`, `nodup_map_of_imp`; in `Hypermap.EmbedHyps`, `ac_edge_node`, `h_edge_node`,
`h_node`, `cface_edge_node`, `rlink_h`, `embed_node_iter`.

## Porting notes

* All the Coq definitions of this file are local to the section; here the ones that depend only
  on the section variables are definitions of the namespace `Hypermap` (`PreHomRing`, `embed`,
  `EmbdDart`, `embdEdge`, `embdFace`, `embd`, `embdRing`, `embdd`, `embrDom`, `EmbrDart`,
  `embrNode`, `embrFace`, `embr`, `embrRing`), and those whose construction needs the
  hypotheses (the hypermaps and their permutations, `embedCotrace`) take `E`.
* `[DecidableEq Dc]` is assumed throughout (for `next`, `chordRing`, `embdEdge`, ...), and
  `[DecidableEq Dm]` where the Birkhoff theorem, `contract_coloring` or the injectivity of
  `embed` are used. The dart types have classical `Fintype` instances.
* Boolean predicates and `reflect` lemmas are `Prop`s and `↔`; `{in A &, P}` and `{morph}`,
  `{mono}` statements take explicit membership hypotheses; `#|predI (cface x) [preim edge of
  A]|` is `{z | cface x z ∧ edge z ∈ A}.ncard`; `codom f` is `Set.range f`; math-comp's `pick`
  and `preim_seq` choose with `Classical.choose` (`preimSeq`), which is harmless since the
  relevant functions are injective.
* The proofs follow the Coq proofs; the differences are listed in the headers of the parts.
-/
