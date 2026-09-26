/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Succ
import FourColor.Coloring
import FourColor.CfMap
import FourColor.CfColor

/-!
# Reducibility engine: ring traces of construction programs (geometric meaning)

`RingTraces cp` is the set of ring traces of the configuration map of the program `cp` (Coq
`ring_trace (cpring (cpmap cp))`).  The main theorem, `ringTraces_iff_cpReach`, says that
these are exactly the traces reachable with `cpsucc` (`Succ.lean`), which the bit-parallel DP
computes.  It is the set-level form of `cfcolor.v`'s correctness proof (`cp_extcol`,
`cpcolor1U_correct`, `cpcolor1K_correct`, `cpcolor1A_correct`, `cpcolor1R_correct`,
`cpcolor1R'_correct`, `cpexpand`, `cpcolor1_correct`, `cpcolor0_correct`,
`ctree_mem_cpcolor`): one lemma per step, `ringTraces_cons`,

* (⊆) the restriction `k ∘ icp` of a coloring `k` of `cpmap (s :: cp)` is a coloring of
  `cpmap cp` (restriction along `injcp`: `sub_cface_injcp`, `sub_adj_injcp`, as in Coq's
  `gcol_cface`/`gcol_adj`), whose trace is mapped by `cpsucc s` to the trace of `k`;
* (⊇) every coloring of `cpmap cp` extends, for each successor trace, to a coloring of
  `cpmap (s :: cp)` with that trace (the constructions of the Coq proofs: `k'` in
  `cpcolor1U_correct` etc.; `Y` and `H` handled directly on `ecpY = ecpN ∘ ecpU` and
  `ecpH = ecpN ∘ ecpY` rather than through `cpexpand`).

The per-step lemmas are in `FourColor/CfColor.lean`.
-/

namespace FourColor.Engine

open FourColor Hypermap

/-- The ring traces of the configuration map of `cp` (Coq `ring_trace (cpring (cpmap cp))`). -/
def RingTraces (cp : Cprog) (t : Colseq) : Prop :=
  (cpmap cp).pointee.RingTrace ((cpmap cp).pointee.cpring (cpmap cp).pointer) t

/-- The ring traces of the base map (a single edge). -/
theorem ringTraces_nil (t : Colseq) : RingTraces [] t ↔ t ∈ baseTraces :=
  ringTrace_cpmap0 t

/-- **One construction step** (Coq `cpcolor1*_correct`). -/
theorem ringTraces_cons (s : Cpstep) (cp : Cprog) (t : Colseq) :
    RingTraces (s :: cp) t ↔ ∃ t0, RingTraces cp t0 ∧ t ∈ cpsucc s t0 := by
  cases s with
  | R n => exact (cpmap cp).pointee.ringTrace_ecpR (cpmap cp).pointer n t
  | R' => exact (cpmap cp).pointee.ringTrace_ecpR' (cpmap cp).pointer t
  | Y => exact (cpmap cp).pointee.ringTrace_ecpY (cpmap cp).pointer t
  | H => exact (cpmap cp).pointee.ringTrace_ecpH (cpmap cp).pointer t
  | U => exact (cpmap cp).pointee.ringTrace_ecpU (cpmap cp).pointer t
  | K => exact (cpmap cp).pointee.ringTrace_ecpK (cpmap cp).pointer t
  | A => exact (cpmap cp).pointee.ringTrace_ecpA (cpmap cp).pointer t

/-- The ring traces of a program are the reachable traces. -/
theorem ringTraces_iff_cpReach (cp : Cprog) (t : Colseq) : RingTraces cp t ↔ CpReach cp t := by
  induction cp generalizing t with
  | nil => exact ringTraces_nil t
  | cons s cp ih =>
    rw [ringTraces_cons]
    exact exists_congr fun t0 => and_congr_left fun _ => ih t0

end FourColor.Engine
