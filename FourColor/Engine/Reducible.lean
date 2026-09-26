/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Check
import FourColor.Engine.SuccSpec

/-!
# Reducibility engine: C-reducibility from the kernel checks

`cReducible_of_checks` is the engine's replacement for Coq's `check_reducible_valid`
(`cfreducible.v`): from
* the validity of the contract and the fact that the contract ring traces of `cpmap cp` are
  ring traces of `cpmap cpc` (both provided by the port of `cfcontract.v`, from
  `cfctr … cp = some cpc` and `valid_ctrm …`; see `contractProg_spec`),
* the specifications of the two networks of the ring size (checked once per ring size),
* the chain of per-configuration kernel checks (`checkInit`, `checkStep`, `checkFinal`),
it concludes `CReducible (cfring cf) (cfcontract cf)` for `cp = cfprog cf`, i.e. Coq's
`cfreducible cf` (recall `cfring cf = rev (cpring (cfmap cf))`).
-/

namespace FourColor.Engine

open FourColor Hypermap

/-- Ring traces of a program are valid traces of its ring size. -/
theorem validTrace_of_ringTraces {cp : Cprog} {t : Colseq} (h : RingTraces cp t) :
    ValidTrace (cprsize cp) t := by
  have := cpReach_valid ((ringTraces_iff_cpReach cp t).1 h)
  exact ⟨this.1, this.2.1, this.2.2⟩

/-- **C-reducibility from the engine's checks.** -/
theorem cReducible_of_checks {cp cpc : Cprog} (hr2 : 2 ≤ cprsize cp)
    (hrc : cprsize cpc = cprsize cp) {tau cnv : Net} (htau : TauSpec (cprsize cp) tau)
    (hcnv : CnvSpec (cprsize cp) cnv) {cc : List (cpmap cp).D}
    (hvalid : (cpmap cp).pointee.ValidContract
      ((cpmap cp).pointee.cpring (cpmap cp).pointer).reverse cc)
    (hcc : ∀ et, (cpmap cp).pointee.CcRingTrace cc
      ((cpmap cp).pointee.cpring (cpmap cp).pointer) et → RingTraces cpc et)
    {H0 Hn : List Nat} (hinit : checkInit (cprsize cp) cnv cp H0 = true)
    (hreach : ReachN (cprsize cp) tau (expand (cprsize cp) H0) (expand (cprsize cp) Hn))
    (hfinal : checkFinal (cprsize cp) cnv cpc Hn = true) :
    (cpmap cp).pointee.CReducible ((cpmap cp).pointee.cpring (cpmap cp).pointer).reverse cc := by
  have h0 : SoundFor (RingTraces cp) (den (cprsize cp) (expand (cprsize cp) H0)) := by
    rw [← eq_of_checkInit hinit]
    apply soundFor_of_sub
    intro t ht
    exact (ringTraces_iff_cpReach cp t).2 ((den_dpP1 hcnv rfl hr2).1 ht).2
  have hn := hreach.sound htau h0
  refine ⟨hvalid, ?_⟩
  intro et het
  rw [List.reverse_reverse] at het ⊢
  have hc := hcc et het
  have hv : ValidTrace (cprsize cp) et := by
    have := validTrace_of_ringTraces hc
    rwa [hrc] at this
  have hd : den (cprsize cp) (dpP1 (cprsize cp) cnv cpc) et :=
    (den_dpP1 hcnv hrc hr2).2 ⟨hv, (ringTraces_iff_cpReach cpc et).1 hc⟩
  exact hn et (den_of_covered hfinal hd)

end FourColor.Engine
