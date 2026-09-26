/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Color
import FourColor.CfMap.Prog

/-!
# Reducibility engine: ring traces of construction programs (program level)

`cfcolor.v` computes the ring traces of `cpmap cp` with the higher-order iterator
`cpcolor1 s f et`, which calls the continuation `f` on the traces of the map extended by the
step `s` that restrict to the trace `et`; this set of traces does not depend on the map.
Here it is made explicit as a list, `cpsucc s et`:

`cpcolor1 s f et = ⋃ (map f (cpsucc s et))`   (same case analysis as Coq's `cpcolor1`),

and `CpReach cp` is the set of traces obtained by following `cpsucc` along the program `cp`
(read right to left, like `cpmap`) from the traces `[c, c]` of the base map `cpmap []` (a
single edge).  Unlike `cpcolor0`, no symmetry reduction is made: the bit-parallel DP
processes all traces at once.

The geometric meaning (`CpReach cp` = the ring traces of `cpmap cp`) is proved in
`SuccSpec.lean` from the per-step lemmas of `cfcolor.v`.
-/

namespace FourColor.Engine

open FourColor

/-- The successor traces of `et` by the construction step `s`: the traces of the ring of the
extended map induced by colorings that induce `et` on the ring of the original map
(Coq: the arguments passed to `f` by `cpcolor1 s f et`). -/
def cpsucc (s : Cpstep) (et : Colseq) : List Colseq :=
  match s, et with
  | .R n, _ => [rot n et]
  | .R', _ => if et.length ≤ 1 then [] else [rotr 1 et]
  | .U, _ => [Color1 :: Color1 :: et, Color2 :: Color2 :: et, Color3 :: Color3 :: et]
  | .K, e1 :: e2 :: et' => if e1 = e2 then [] else [addc e1 e2 :: et']
  | .Y, e1 :: et' =>
    [permc Eperm231 e1 :: permc Eperm312 e1 :: et', permc Eperm312 e1 :: permc Eperm231 e1 :: et']
  | .H, e1 :: e2 :: et' =>
    if e1 = e2 then
      [permc Eperm231 e1 :: permc Eperm231 e1 :: et', permc Eperm312 e1 :: permc Eperm312 e1 :: et']
    else [e2 :: e1 :: et']
  | .A, e1 :: e2 :: et' => if e1 = e2 then [match et' with | [] => et | _ => et'] else []
  | _, _ => []

/-- The ring traces of the base map `cpmap []` (a single edge): `[c, c]`, `c ≠ Color0`. -/
def baseTraces : List Colseq := [[Color1, Color1], [Color2, Color2], [Color3, Color3]]

/-- The traces reachable along the program `cp` (read right to left) from the base traces. -/
def CpReach : Cprog → Colseq → Prop
  | [], t => t ∈ baseTraces
  | s :: cp, t => ∃ t0, CpReach cp t0 ∧ t ∈ cpsucc s t0

/-! ### Program-level facts -/

/-- The sum of a rotated trace. -/
theorem sumt_rot (n : Nat) (t : Colseq) : sumt (rot n t) = sumt t := by
  conv_rhs => rw [← List.take_append_drop n t]
  rw [rot, sumt_append, sumt_append, addcC]

/-- Reachable traces have no `Color0`, have sum `Color0`, and have the length `cprsize cp`
of the ring of `cpmap cp`. -/
theorem cpReach_valid {cp : Cprog} {t : Colseq} (h : CpReach cp t) :
    t.length = cprsize cp ∧ Color0 ∉ t ∧ sumt t = Color0 := by
  induction cp generalizing t with
  | nil =>
    simp only [CpReach, baseTraces, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> decide
  | cons s cp ih =>
    obtain ⟨t0, h0, ht⟩ := h
    obtain ⟨hl, hc, hs⟩ := ih h0
    cases s with
    | R n =>
      simp only [cpsucc, List.mem_singleton] at ht; subst ht
      exact ⟨by simp [hl, cprsize], by simpa using hc, by rw [sumt_rot, hs]⟩
    | R' =>
      simp only [cpsucc] at ht
      split at ht
      · simp at ht
      · simp only [List.mem_singleton] at ht; subst ht
        exact ⟨by simp [rotr, hl, cprsize], by simpa [rotr] using hc, by rw [rotr, sumt_rot, hs]⟩
    | U =>
      simp only [cpsucc, List.mem_cons, List.not_mem_nil, or_false] at ht
      refine ⟨?_, ?_, ?_⟩ <;> rcases ht with rfl | rfl | rfl <;>
        simp [hl, cprsize, hc, sumt] <;> simpa [sumt] using hs
    | K =>
      match t0, hl, hc, hs, ht with
      | e1 :: e2 :: et', hl, hc, hs, ht =>
        simp only [cpsucc] at ht
        split at ht
        · simp at ht
        · rename_i hne
          simp only [List.mem_singleton] at ht; subst ht
          simp only [List.mem_cons, not_or] at hc
          refine ⟨?_, ?_, ?_⟩
          · simp [cprsize] at hl ⊢; omega
          · simp only [List.mem_cons, not_or]
            exact ⟨fun h => hne ((addc_eq0 e1 e2).1 h.symm), hc.2.2⟩
          · simpa [sumt, addcA] using hs
    | Y =>
      match t0, hl, hc, hs, ht with
      | e1 :: et', hl, hc, hs, ht =>
        simp only [cpsucc, List.mem_cons, List.not_mem_nil, or_false] at ht
        simp only [List.mem_cons, not_or] at hc
        have key : ∀ c, c ≠ Color0 → addc (permc Eperm231 c) (permc Eperm312 c) = c := by
          intro c; cases c <;> decide
        refine ⟨?_, ?_, ?_⟩ <;> rcases ht with rfl | rfl
        · simp [cprsize] at hl ⊢; omega
        · simp [cprsize] at hl ⊢; omega
        · simp only [List.mem_cons, not_or]
          exact ⟨fun h => hc.1 ((permc_eq0 _ _).1 h.symm).symm,
            fun h => hc.1 ((permc_eq0 _ _).1 h.symm).symm, hc.2⟩
        · simp only [List.mem_cons, not_or]
          exact ⟨fun h => hc.1 ((permc_eq0 _ _).1 h.symm).symm,
            fun h => hc.1 ((permc_eq0 _ _).1 h.symm).symm, hc.2⟩
        · simp only [sumt_cons] at hs ⊢; rw [addcA, key e1 (Ne.symm hc.1), hs]
        · simp only [sumt_cons] at hs ⊢
          rw [addcA, addcC (permc Eperm312 e1), key e1 (Ne.symm hc.1), hs]
    | H =>
      match t0, hl, hc, hs, ht with
      | e1 :: e2 :: et', hl, hc, hs, ht =>
        simp only [List.mem_cons, not_or] at hc
        simp only [cpsucc] at ht
        split at ht
        · rename_i heq
          subst heq
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
          have hs' : sumt et' = Color0 := by simpa [sumt] using hs
          refine ⟨?_, ?_, ?_⟩ <;> rcases ht with rfl | rfl
          · simpa [cprsize] using hl
          · simpa [cprsize] using hl
          · simp only [List.mem_cons, not_or]
            exact ⟨fun h => hc.1 ((permc_eq0 _ _).1 h.symm).symm,
              fun h => hc.1 ((permc_eq0 _ _).1 h.symm).symm, hc.2.2⟩
          · simp only [List.mem_cons, not_or]
            exact ⟨fun h => hc.1 ((permc_eq0 _ _).1 h.symm).symm,
              fun h => hc.1 ((permc_eq0 _ _).1 h.symm).symm, hc.2.2⟩
          · simp [sumt_cons, hs']
          · simp [sumt_cons, hs']
        · simp only [List.mem_singleton] at ht; subst ht
          refine ⟨by simpa [cprsize] using hl, ?_, ?_⟩
          · simp only [List.mem_cons, not_or]; exact ⟨hc.2.1, hc.1, hc.2.2⟩
          · simp only [sumt_cons] at hs ⊢; rw [addcA, addcC e2 e1, ← addcA, hs]
    | A =>
      match t0, hl, hc, hs, ht with
      | e1 :: e2 :: et', hl, hc, hs, ht =>
        simp only [cpsucc] at ht
        split at ht
        · rename_i heq
          subst heq
          simp only [List.mem_singleton] at ht
          have hs' : sumt et' = Color0 := by simpa [sumt] using hs
          cases et' with
          | nil =>
            subst ht
            refine ⟨?_, hc, hs⟩
            simp only [List.length_cons, List.length_nil] at hl
            simp only [cprsize, ← hl]; rfl
          | cons x xs =>
            subst ht
            simp only [List.mem_cons, not_or] at hc
            refine ⟨?_, ?_, hs'⟩
            · simp [cprsize] at hl ⊢; rw [← hl]; rfl
            · simp only [List.mem_cons, not_or]; exact hc.2.2
        · simp at ht

end FourColor.Engine
