/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfContract.Prog
import FourColor.CfContract.Enum
import FourColor.CfContract.Ext
import FourColor.CfContract.Correct
import FourColor.CfContract.Sparse
import FourColor.CfContract.Band
import FourColor.CfContract.Spec

/-!
# Configuration contracts  (port of `cfcontract.v`)

Compute the contract of a configuration construction: a construction program whose ring
colorings coincide with the contract colorings of the initial program.  The computation also
checks the validity of the contract (sparseness, and if required the existence of a triad).

Recall that in `coloring.v` we chose to represent contracts as a list of darts that forms a
transversal of the edges deleted by the contract.  The contract annotation represents this list
by a list of the indices of the darts in a transversal of all the kernel edges of the map
constructed by the configuration program.  Out-of-bounds indices are ignored, so contracts are
always off-ring by construction.

The kernel edge transversal lists edges in the reverse order they become kernel edges during
the construction.  Each `Y` step adds a single edge, the "foot" of the `Y`, except the initial
`Y` step, as after this step all edges are still ring edges (note that this initial `Y` is
actually at the end of the construction program, which is interpreted right-to-left).  Each
`H` step adds three edges: the right and left "feet" of the `H`, and the horizontal crossbar, in
that order, by convention; thus in the (reverse order) list they appear in the "crossbar, left,
right" order.

## Definitions (math-comp names in parentheses)

* `cfcontract cf` (`cfcontract`) : a transversal of the contract edges of `cfmap cf`.
* `contractProg cf` : `some cpc` where `cpc` is the construction program of the contract map of
  `cf`, if `cfprog cf` is well-formed (satisfies `configProg`) and `cfcontract cf` is valid
  (sparse, with a triad if of size 4).  It replaces math-comp's `contract_ctree` (`Some` ctree
  of the contract colorings of `cfmap cf`, i.e. `Some (cpcolor cpc)`): the ring colorings of
  `cpc` are computed by the bit-parallel engine.
* `ctrmsize cp` (`ctrmsize`) : the number of "kernel" (non-ring) edges of `cpmap cp`.
* `ctrenum cp` (`ctrenum`) : a transversal sequence of the kernel edges of `cpmap cp`.
* `ctrmask cp cci` (`ctrmask`) : the mask for the contract index list `cci` and program `cp`.
* `cfcontractMask cf` (`cfcontract_mask`) : the contract mask of `cf : Config`.
* `validCtrm cm cp` (`valid_ctrm`) : the contract represented by the mask `cm` is valid for
  `cpmap cp` (size in `[1, 4]`, with a triad for size `4`).
* `ctrband cm cp` (`ctrband`) : the face mask selecting the faces of `cp` incident to one of
  the edges selected by the contract mask `cm`; this may include both kernel and ring faces.
* `cptriad ccm cp i` (`cptriad`) : the kernel of `cpmap cp` has a triad with index `< i`, for
  a contract with band `ccm`: there is a face with index `< i` that is adjacent to at least 3
  of the faces selected by `ccm`, as well as to a face NOT in `ccm`.
* `cfctr mr mk cp` (`cfctr`) : `some` construction program for the application of the
  contract erasing the edges selected by the masks `mk` (for kernel edges) and `mr` (for ring
  edges, in recursive calls), provided `cp` is a `configProg` and the contract is sparse.

## Files

* `FourColor/CfContract/Prog.lean`    : the program-level (kernel-computable) definitions:
  `ctrmsize`, `ctrmaskRec`, `ctrmask`, `size_ctrmask`, `cfcontractMask`, `nsp`, `cfctr`,
  `cfctr_config_prog`, `ctrband`, `cptriad`, `validCtrm`, `contractProg`;
* `FourColor/CfContract/Enum.lean`    : `ctrenum`, `size_ctrenum`, `cfcontract`,
  `insertE_icpY`, `insertE_icpH`, `uniq_ctrenum`, and helpers on masks, rings and the darts of
  the `Y` and `H` steps (namespace `FourColor.CfContract`);
* `FourColor/CfContract/Ext.lean`     : extensions of colorings along the construction steps
  (math-comp's `k' u := oapp h' c0 [pick x | cface u (icp x)]` in `cfctr_correct`);
* `FourColor/CfContract/Correct.lean` : `cfctr_correct`;
* `FourColor/CfContract/Sparse.lean`  : `sparse_cfctr`;
* `FourColor/CfContract/Band.lean`    : `ctrband_correct`;
* `FourColor/CfContract/Spec.lean`    : `contractProg_spec` (replaces `contract_ctreeP`).

Not ported: `contract_ctree` and `contract_ctreeP` (ctree-valued), replaced by `contractProg`
and `contractProg_spec`.

## Porting notes

* math-comp's conclusions `if cfctr mr mc cp is Some cpc then P cpc else True` and
  `cfctr mr mc cp ==> P` are stated with a hypothesis `cfctr mr mc cp = some cpc`.
* The proofs of `cfctr_correct`, `sparse_cfctr` and `ctrband_correct` are by induction on the
  program, with one lemma per construction step (`CfContract.ctrCorrect_Y`, ...); the
  colorings of the contracted maps are built by the generic extension lemmas of `Ext.lean`
  instead of the case-by-case constructions of the Coq proof.
* The triad of a contract of size 4 is extracted from `cptriad` directly (`cptriad_spec`),
  rather than by math-comp's contrapositive argument.
-/
