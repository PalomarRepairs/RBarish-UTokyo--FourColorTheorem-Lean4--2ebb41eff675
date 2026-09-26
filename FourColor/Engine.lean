/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Bits
import FourColor.Engine.SetLevel
import FourColor.Engine.Layout
import FourColor.Engine.Matching
import FourColor.Engine.KempeStep
import FourColor.Engine.Network
import FourColor.Engine.Round
import FourColor.Engine.Succ
import FourColor.Engine.ColorDP
import FourColor.Engine.Check
import FourColor.Engine.SuccSpec
import FourColor.Engine.Reducible
import FourColor.Engine.Birkhoff
import FourColor.Engine.Chunk
import FourColor.Engine.CheckChunk
import FourColor.Engine.NetSplit
import FourColor.Engine.DPChunk
import FourColor.Engine.KempeChunk
import FourColor.Engine.Gen

/-!
# The reducibility engine (umbrella module)

The engine replaces Coq's decision procedure on trees of colorings (`ctree.v`, `gtree.v`,
`ctreerestrict.v`, `gtreerestrict.v`, `initctree.v`, `initgtree.v`, `kempetree.v`, and the
`ctree` parts of `cfcolor.v`, `cfcontract.v` and `cfreducible.v`).  Those procedures walk trees of
individual colorings; run in Lean's kernel, they would take hundreds of hours for a single
configuration of ring size 14, because the kernel is fast only on the big-number primitives it
delegates to GMP.  The engine therefore stores *sets* of ring traces as big natural numbers and
performs each step of the Kempe closure as a few dozen big-number operations on all the traces at
once.  What it proves for each configuration is Coq's `cfreducible`, unchanged.

* `SetLevel`: soundness at the level of sets.  Every set obtained from the ring traces of a
  configuration by unions, color permutations and Kempe steps lies in their Kempe co-closure, so
  no fixpoint is needed: the engine iterates *rounds* until the traces of the contract are
  covered.
* `Bits`, `Layout`: big-number primitives, and the packed graded layout of trace sets.
* `Matching`, `KempeStep`, `Network`, `Round`: the chord flips of non-crossing matchings, the
  bit-parallel Kempe step, the delta-swap networks that permute the layout (routed at elaboration
  time, verified by the kernel), and one round.
* `Succ`, `ColorDP`, `SuccSpec`: the ring traces of a configuration, computed by a bit-parallel
  dynamic program over its construction program, and their geometric meaning.
* `Check`, `Reducible`: the per-configuration kernel checks, cut into declarations between
  *checkpoints* (big-number literals) so that each declaration needs bounded kernel memory, and
  `cReducible_of_checks`, which turns them into `CReducible`.
* `Birkhoff`: the game of Coq's `Birkhoff_check2`, replayed on the same sound sets.
* `Chunk`, `CheckChunk`, `NetSplit`, `DPChunk`, `KempeChunk`: variants of the checks that avoid
  big right shifts and very large declarations, proved equal to or sufficient for the originals,
  so that Palomar's independent checkers nanoda and con-ron stay fast.
* `Gen`: the meta-programs `#engine_nets` and `#engine_certify`, which compute the networks and
  the checkpoints at elaboration time and add them as literal definitions.  Nothing they compute
  is trusted: a wrong literal only makes a kernel check fail.
-/
