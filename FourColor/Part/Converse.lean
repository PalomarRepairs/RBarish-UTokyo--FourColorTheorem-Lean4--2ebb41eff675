/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Part.Fit

/-!
# Parts: converse  (port of `part.v`, section `FitConversePart`)

In a plain cubic pentagonal map `G`, if `x` exactly fits `p`, then the dart
`G.invFace2 (edge (face (face x)))` (Coq `inv_face2`: `face⁻²`) of the third spoke of `x`
tightly fits `conversePart p` (Coq `fitp_converse`).

The proof follows the Coq one: the four components of `conversePart` (`convPart4`,
`convPart5`, `convPart12`, `convPart3`) are handled in turn. The geometric facts used are
identities between darts of the second neighbourhood of `x`; they are all consequences of
`edge ∘ edge = id`, `node ∘ node ∘ node = id` and `face = node ∘ node ∘ edge` (and are proved by
rewriting with these identities), plus the fact that `face^[arity y] y = y`.
-/

namespace FourColor

universe u

variable {D : Type u}

namespace Hypermap

variable (G : Hypermap D)

/-- Coq `inv_face2 x`: `face⁻² x` (used in the `converse_part` specification). -/
def invFace2 (x : D) : D := G.edge (G.node (G.edge (G.node x)))

/-- Coq `fitp_converse`. -/
theorem fitp_converse [Finite D] (hG : G.PlainCubicPentagonal) (p : Part) (x : D)
    (hx : G.exactFitp x p) :
    G.tightFitp (G.invFace2 (G.edge (G.face (G.face x)))) (conversePart p) := by
  have hF : ∀ y, G.face y = G.node (G.node (G.edge y)) := fun y => by
    rw [G.cubic_eq' hG.cubic, G.plain_eq hG.plain]
  have hE : ∀ y, G.edge (G.edge y) = y := G.plain_eq hG.plain
  have hN : ∀ y, G.node (G.node (G.node y)) = y := G.cubic_eq hG.cubic
  have p59 : ∀ y, memRange .pr59 (G.arity y) = true := fun y => decide_eq_true (hG.pentagonal y)
  have arF : ∀ {a b : D}, G.face a = b → G.arity a = G.arity b := fun h =>
    h ▸ (G.arity_face _).symm
  have mem_eq : ∀ {r : Prange} {n m : ℕ}, (∀ k, memRange r k = (k == m)) → memRange r n →
      n = m := fun hr hn => by rw [hr] at hn; simpa using hn
  simp only [exactFitp, Bool.and_eq_true, beq_iff_eq] at hx
  obtain ⟨hsz, hfit⟩ := hx
  set e2 := G.edge (G.face (G.face x)) with he2
  set x' := G.invFace2 e2 with hx'
  /- Dart identities: the new subparts, anchored at `x' = face⁻² e2`, `face x'`, `e2 = face² x'`,
  `face e2` and `face² e2`, in terms of the old ones, anchored at `face^[j] x`. -/
  -- spoke 4 (the old spoke 1)
  have T4b : G.arity (SubpartLoc.spoke.move G (G.face e2)) =
      G.arity (SubpartLoc.spoke.move G (G.face x)) :=
    arF (by simp only [SubpartLoc.move, he2, hF, hE, hN])
  have T4c : G.arity (SubpartLoc.hat.move G (G.face e2)) =
      G.arity (SubpartLoc.spoke.move G x) :=
    arF (by simp only [SubpartLoc.move, he2, Function.iterate_succ_apply',
      Function.iterate_zero_apply, hF, hE, hN])
  have T4d : SubpartLoc.fan1.move G (G.face e2) = SubpartLoc.hat.move G (G.face x) := by
    simp only [SubpartLoc.move, he2, Function.iterate_succ_apply', Function.iterate_zero_apply,
      hF, hE, hN]
  have T4e : SubpartLoc.fan2.move G (G.face e2) = SubpartLoc.fan1.move G (G.face x) := by
    simp only [SubpartLoc.move, he2, Function.iterate_succ_apply', Function.iterate_zero_apply,
      hF, hE, hN]
  have hinv3 : ∀ y, G.edge (G.node (G.edge (G.node (G.edge (G.node (G.face^[3] y)))))) = y := by
    intro y
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, G.faceK]
  have T4a : ∀ m, G.arity (SubpartLoc.spoke.move G (G.face x)) = m → 3 ≤ m →
      G.arity (SubpartLoc.hat.move G (G.face (G.face e2))) =
        G.arity (G.edge (G.face^[m - 3] (SubpartLoc.spoke.move G (G.face x)))) := by
    intro m hm h3
    have hs1 : G.face^[3] (G.face^[m - 3] (SubpartLoc.spoke.move G (G.face x))) =
        SubpartLoc.spoke.move G (G.face x) := by
      rw [← Function.iterate_add_apply, show 3 + (m - 3) = m by omega, ← hm, G.iter_face_arity]
    have hfree : G.face (SubpartLoc.hat.move G (G.face (G.face e2))) =
        G.edge (G.edge (G.node (G.edge (G.node (G.edge (G.node
          (SubpartLoc.spoke.move G (G.face x)))))))) := by
      simp only [SubpartLoc.move, he2, Function.iterate_succ_apply', Function.iterate_zero_apply,
        hF, hE, hN]
    rw [← G.arity_face, hfree]
    conv_lhs => rw [← hs1, hinv3]
  -- spoke 5 (the old hat 2) and the new hub (the old spoke 2)
  have T5a : SubpartLoc.spoke.move G (G.face^[2] x) = e2 := rfl
  have T5b : SubpartLoc.spoke.move G (G.face (G.face e2)) =
      SubpartLoc.hat.move G (G.face^[2] x) := by
    simp only [SubpartLoc.move, he2, Function.iterate_succ_apply', Function.iterate_zero_apply]
  have T5c : SubpartLoc.spoke.move G (G.face (G.face (G.face e2))) =
      SubpartLoc.fan1.move G (G.face^[2] x) := by
    simp only [SubpartLoc.move, he2, Function.iterate_succ_apply', Function.iterate_zero_apply]
  have T5d : SubpartLoc.spoke.move G (G.face (G.face (G.face (G.face e2)))) =
      SubpartLoc.fan2.move G (G.face^[2] x) := by
    simp only [SubpartLoc.move, he2, Function.iterate_succ_apply', Function.iterate_zero_apply]
  -- spokes 1 and 2 (the old hat 3 and spoke 3)
  have T12a : G.arity (SubpartLoc.spoke.move G x') =
      G.arity (SubpartLoc.hat.move G (G.face^[3] x)) :=
    (arF (by simp only [SubpartLoc.move, hx', invFace2, he2, Function.iterate_succ_apply',
      Function.iterate_zero_apply, hF, hE, hN])).symm
  have T12b : G.arity (SubpartLoc.spoke.move G (G.face x')) =
      G.arity (SubpartLoc.spoke.move G (G.face^[3] x)) :=
    (arF (by simp only [SubpartLoc.move, hx', invFace2, he2, Function.iterate_succ_apply',
      Function.iterate_zero_apply, hF, hE, hN])).symm
  have T12c : SubpartLoc.hat.move G (G.face x') = SubpartLoc.fan1.move G (G.face^[3] x) := by
    simp only [SubpartLoc.move, hx', invFace2, he2, Function.iterate_succ_apply',
      Function.iterate_zero_apply, hF, hE, hN]
  have T12d : SubpartLoc.fan1.move G (G.face x') = SubpartLoc.fan2.move G (G.face^[3] x) := by
    simp only [SubpartLoc.move, hx', invFace2, he2, Function.iterate_succ_apply',
      Function.iterate_zero_apply, hF, hE, hN]
  have T12e : SubpartLoc.fan2.move G (G.face x') =
      G.edge (G.face^[5] (SubpartLoc.spoke.move G (G.face^[3] x))) := by
    simp only [SubpartLoc.move, hx', invFace2, he2, Function.iterate_succ_apply',
      Function.iterate_zero_apply, hF, hE, hN]
  have hinv2 : ∀ y, G.edge (G.node (G.edge (G.node (G.face^[2] y)))) = y := by
    intro y
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, G.faceK]
  have T12f : ∀ m, G.arity (SubpartLoc.spoke.move G (G.face^[3] x)) = m → 2 ≤ m →
      G.arity (G.edge (G.face^[m - 2] (SubpartLoc.spoke.move G (G.face^[3] x)))) =
        G.arity (SubpartLoc.hat.move G (G.face (G.face^[3] x))) := by
    intro m hm h2
    have hs3 : G.face^[2] (G.face^[m - 2] (SubpartLoc.spoke.move G (G.face^[3] x))) =
        SubpartLoc.spoke.move G (G.face^[3] x) := by
      rw [← Function.iterate_add_apply, show 2 + (m - 2) = m by omega, ← hm, G.iter_face_arity]
    have hfree : G.edge (G.edge (G.node (G.edge (G.node
        (SubpartLoc.spoke.move G (G.face^[3] x)))))) =
        G.face (SubpartLoc.hat.move G (G.face (G.face^[3] x))) := by
      simp only [SubpartLoc.move, Function.iterate_succ_apply', Function.iterate_zero_apply,
        hF, hE, hN]
    rw [← G.arity_face (SubpartLoc.hat.move G (G.face (G.face^[3] x))), ← hfree]
    conv_rhs => rw [← hs3, hinv2]
  have T12g : SubpartLoc.hat.move G e2 = SubpartLoc.spoke.move G (G.face (G.face^[3] x)) := by
    simp only [SubpartLoc.move, he2, Function.iterate_succ_apply', Function.iterate_zero_apply,
      hE]
  have T12h : G.face (G.face x') = e2 := by
    simp only [hx', invFace2, G.nodeK]
  -- spoke 3 (the old hub)
  have T3a : G.arity (SubpartLoc.spoke.move G e2) = G.arity x := by
    have : SubpartLoc.spoke.move G e2 = G.face^[2] x := by
      simp only [SubpartLoc.move, he2, Function.iterate_succ_apply', Function.iterate_zero_apply,
        hE]
    rw [this, G.arity_iter_face]
  have T3c : SubpartLoc.fan1.move G e2 = SubpartLoc.spoke.move G (G.face^[5] x) := by
    simp only [SubpartLoc.move, he2, Function.iterate_succ_apply', Function.iterate_zero_apply,
      hE]
  have T3d : SubpartLoc.fan2.move G e2 = SubpartLoc.spoke.move G (G.face (G.face^[5] x)) := by
    simp only [SubpartLoc.move, he2, Function.iterate_succ_apply', Function.iterate_zero_apply,
      hE]
  have T3e : SubpartLoc.fan3.move G e2 =
      SubpartLoc.spoke.move G (G.face (G.face (G.face^[5] x))) := by
    simp only [SubpartLoc.move, he2, Function.iterate_succ_apply', Function.iterate_zero_apply,
      hE]
  /- The spoke 4 and spoke 5 subparts (Coq `conv_part4`). -/
  rcases h4 : convPart4 p with ⟨h45, q4⟩
  have C4 : memRange h45 (G.arity (SubpartLoc.hat.move G (G.face (G.face e2)))) ∧
      ∀ q5, G.fitp (G.face (G.face e2)) q5 → G.fitp (G.face e2) (q4 q5) := by
    have triv : h45 = .pr59 → q4 = (fun _ => .nil) →
        memRange h45 (G.arity (SubpartLoc.hat.move G (G.face (G.face e2)))) ∧
          ∀ q5, G.fitp (G.face (G.face e2)) q5 → G.fitp (G.face e2) (q4 q5) := by
      rintro rfl rfl
      exact ⟨p59 _, fun _ _ => rfl⟩
    rcases p with _ | ⟨h34, h, p2⟩ | ⟨_, _, p2⟩ | ⟨_, _, _, p2⟩ | ⟨_, _, _, _, p2⟩
    case cons =>
      simp only [fitp, Bool.and_eq_true] at hfit
      obtain ⟨H34, -, hfit2⟩ := hfit
      rcases p2 with _ | ⟨s4, f41, p3⟩ | ⟨f41, h45', p3⟩ | ⟨f41, f42, h45', p3⟩ |
        ⟨_, _, _, _, p3⟩
      case cons =>
        simp only [fitp, Bool.and_eq_true] at hfit2
        obtain ⟨S4, F41, -⟩ := hfit2
        simp only [convPart4] at h4
        split at h4 <;> simp only [Prod.mk.injEq] at h4 <;> obtain ⟨rfl, rfl⟩ := h4
        · refine ⟨p59 _, fun q5 hq5 => ?_⟩
          simp only [fitp, Bool.and_eq_true, T4b, T4c]
          exact ⟨S4, H34, hq5⟩
        · have hm := mem_eq (fun _ => rfl) S4
          refine ⟨?_, fun q5 hq5 => ?_⟩
          · rw [T4a 5 hm (by omega)]
            exact F41
          · simp only [fitp, Bool.and_eq_true, T4b, T4c]
            exact ⟨S4, H34, hq5⟩
        · refine ⟨p59 _, fun q5 hq5 => ?_⟩
          simp only [fitp, Bool.and_eq_true, T4b, T4c, T4d]
          exact ⟨S4, H34, F41, hq5⟩
        · refine ⟨p59 _, fun q5 hq5 => ?_⟩
          simp only [fitp, Bool.and_eq_true, T4b, T4c, T4d, p59]
          exact ⟨S4, H34, F41, trivial, hq5⟩
        · exact triv rfl rfl
      case cons6 =>
        simp only [fitp, Bool.and_eq_true] at hfit2
        obtain ⟨S4, F41, H45, -⟩ := hfit2
        simp only [convPart4, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        have hm := mem_eq (fun _ => rfl) S4
        refine ⟨?_, fun q5 hq5 => ?_⟩
        · rw [T4a 6 hm (by omega)]
          exact H45
        · simp only [fitp, Bool.and_eq_true, T4b, T4c, T4d]
          exact ⟨S4, H34, F41, hq5⟩
      case cons7 =>
        simp only [fitp, Bool.and_eq_true] at hfit2
        obtain ⟨S4, F41, F42, H45, -⟩ := hfit2
        simp only [convPart4, Prod.mk.injEq] at h4
        obtain ⟨rfl, rfl⟩ := h4
        have hm := mem_eq (fun _ => rfl) S4
        refine ⟨?_, fun q5 hq5 => ?_⟩
        · rw [T4a 7 hm (by omega)]
          exact H45
        · simp only [fitp, Bool.and_eq_true, T4b, T4c, T4d, T4e]
          exact ⟨S4, H34, F41, F42, hq5⟩
      all_goals
        simp only [convPart4, Prod.mk.injEq] at h4
        exact triv h4.1.symm h4.2.symm
    all_goals
      simp only [convPart4, Prod.mk.injEq] at h4
      exact triv h4.1.symm h4.2.symm
  /- The spoke 5 subpart and the new hub (Coq `conv_part5`). -/
  have hfit2 := G.fitp_drop 2 p x hfit
  rcases h5 : convPart5 h45 (dropPart 2 p) with ⟨u, q5⟩
  have C5 : memRange u (G.arity e2) ∧ G.fitp (G.face (G.face e2)) q5 := by
    generalize dropPart 2 p = p3 at hfit2 h5
    rcases p3 with _ | ⟨u', s5, p4⟩ | ⟨_, _, p4⟩ | ⟨s5, s6, s7, p4⟩ | ⟨_, _, _, _, p4⟩
    case cons =>
      simp only [convPart5, Prod.mk.injEq] at h5
      obtain ⟨rfl, rfl⟩ := h5
      simp only [fitp, Bool.and_eq_true] at hfit2
      obtain ⟨U, S5, -⟩ := hfit2
      refine ⟨U, ?_⟩
      simp only [fitp, Bool.and_eq_true, T5b]
      exact ⟨S5, C4.1, trivial⟩
    case cons7 =>
      simp only [convPart5, Prod.mk.injEq] at h5
      obtain ⟨rfl, rfl⟩ := h5
      simp only [fitp, Bool.and_eq_true] at hfit2
      obtain ⟨U, S5, S6, S7, -⟩ := hfit2
      refine ⟨U, ?_⟩
      simp only [pconsS, fitp, Bool.and_eq_true, T5b, T5c, T5d, p59]
      exact ⟨S5, C4.1, S6, trivial, S7, trivial, trivial⟩
    all_goals
      simp only [convPart5, Prod.mk.injEq] at h5
      obtain ⟨rfl, rfl⟩ := h5
      exact ⟨p59 _, rfl⟩
  /- The spoke 1 and spoke 2 subparts (Coq `conv_part12`). -/
  have hfit3 := G.fitp_drop 3 p x hfit
  rcases h12 : convPart12 (dropPart 3 p) with ⟨h23, q12⟩
  have C12 : memRange h23 (G.arity (SubpartLoc.hat.move G e2)) ∧
      ∀ q3, G.fitp e2 q3 → G.fitp x' (q12 q3) := by
    have triv : h23 = .pr59 → q12 = (fun _ => .nil) →
        memRange h23 (G.arity (SubpartLoc.hat.move G e2)) ∧
          ∀ q3, G.fitp e2 q3 → G.fitp x' (q12 q3) := by
      rintro rfl rfl
      exact ⟨p59 _, fun _ _ => rfl⟩
    generalize dropPart 3 p = p4 at hfit3 h12
    rcases p4 with _ | ⟨s2, s1, p5⟩ | ⟨s1, h12', p5⟩ | ⟨s1, h12', f21, p5⟩ | ⟨_, _, _, _, p5⟩
    case cons =>
      rcases p5 with _ | ⟨h23', f2, p6⟩ | ⟨_, _, p6⟩ | ⟨_, _, _, p6⟩ | ⟨_, _, _, _, p6⟩
      case cons =>
        simp only [fitp, Bool.and_eq_true] at hfit3
        obtain ⟨S2, S1, H23, F2, -⟩ := hfit3
        simp only [convPart12] at h12
        split at h12 <;> simp only [Prod.mk.injEq] at h12 <;> obtain ⟨rfl, rfl⟩ := h12
        · refine ⟨by rwa [T12g], fun q3 hq3 => ?_⟩
          simp only [pconsS, fitp, Bool.and_eq_true, T12a, T12b, T12h, p59]
          exact ⟨S1, trivial, S2, trivial, hq3⟩
        · have hm := mem_eq (fun _ => rfl) S2
          refine ⟨by rwa [T12g], fun q3 hq3 => ?_⟩
          simp only [pconsS, fitp, Bool.and_eq_true, T12a, T12b, T12c, T12h, p59]
          refine ⟨S1, trivial, S2, ?_, hq3⟩
          rw [show SubpartLoc.fan1.move G (G.face^[3] x) =
            G.edge (G.face^[5 - 2] (SubpartLoc.spoke.move G (G.face^[3] x))) from rfl,
            T12f 5 hm (by omega)]
          exact F2
        · have hm := mem_eq (fun _ => rfl) S2
          refine ⟨by rwa [T12g], fun q3 hq3 => ?_⟩
          simp only [pconsS, fitp, Bool.and_eq_true, T12a, T12b, T12d, T12h, p59]
          refine ⟨S1, trivial, S2, trivial, ?_, hq3⟩
          rw [show SubpartLoc.fan2.move G (G.face^[3] x) =
            G.edge (G.face^[6 - 2] (SubpartLoc.spoke.move G (G.face^[3] x))) from rfl,
            T12f 6 hm (by omega)]
          exact F2
        · have hm := mem_eq (fun _ => rfl) S2
          refine ⟨by rwa [T12g], fun q3 hq3 => ?_⟩
          simp only [pconsS, fitp, Bool.and_eq_true, T12a, T12b, T12e, T12h, p59]
          refine ⟨S1, trivial, S2, trivial, trivial, ?_, hq3⟩
          rw [show G.edge (G.face^[5] (SubpartLoc.spoke.move G (G.face^[3] x))) =
            G.edge (G.face^[7 - 2] (SubpartLoc.spoke.move G (G.face^[3] x))) from rfl,
            T12f 7 hm (by omega)]
          exact F2
        · exact triv rfl rfl
      all_goals
        simp only [convPart12, Prod.mk.injEq] at h12
        exact triv h12.1.symm h12.2.symm
    case cons6 =>
      rcases p5 with _ | ⟨h23', f21, p6⟩ | ⟨_, _, p6⟩ | ⟨_, _, _, p6⟩ | ⟨_, _, _, _, p6⟩
      case cons =>
        simp only [fitp, Bool.and_eq_true] at hfit3
        obtain ⟨S2, S1, H12, H23, F21, -⟩ := hfit3
        simp only [convPart12, Prod.mk.injEq] at h12
        obtain ⟨rfl, rfl⟩ := h12
        have hm := mem_eq (fun _ => rfl) S2
        refine ⟨by rwa [T12g], fun q3 hq3 => ?_⟩
        simp only [pconsS, fitp, Bool.and_eq_true, T12a, T12b, T12c, T12d, T12h, p59]
        refine ⟨S1, trivial, S2, H12, ?_, hq3⟩
        rw [show SubpartLoc.fan2.move G (G.face^[3] x) =
          G.edge (G.face^[6 - 2] (SubpartLoc.spoke.move G (G.face^[3] x))) from rfl,
          T12f 6 hm (by omega)]
        exact F21
      all_goals
        simp only [convPart12, Prod.mk.injEq] at h12
        exact triv h12.1.symm h12.2.symm
    case cons7 =>
      rcases p5 with _ | ⟨h23', f22, p6⟩ | ⟨_, _, p6⟩ | ⟨_, _, _, p6⟩ | ⟨_, _, _, _, p6⟩
      case cons =>
        simp only [fitp, Bool.and_eq_true] at hfit3
        obtain ⟨S2, S1, H12, F21, H23, F22, -⟩ := hfit3
        simp only [convPart12, Prod.mk.injEq] at h12
        obtain ⟨rfl, rfl⟩ := h12
        have hm := mem_eq (fun _ => rfl) S2
        refine ⟨by rwa [T12g], fun q3 hq3 => ?_⟩
        simp only [pconsS, fitp, Bool.and_eq_true, T12a, T12b, T12c, T12d, T12e, T12h, p59]
        refine ⟨S1, trivial, S2, H12, F21, ?_, hq3⟩
        rw [show G.edge (G.face^[5] (SubpartLoc.spoke.move G (G.face^[3] x))) =
          G.edge (G.face^[7 - 2] (SubpartLoc.spoke.move G (G.face^[3] x))) from rfl,
          T12f 7 hm (by omega)]
        exact F22
      all_goals
        simp only [convPart12, Prod.mk.injEq] at h12
        exact triv h12.1.symm h12.2.symm
    all_goals
      simp only [convPart12, Prod.mk.injEq] at h12
      exact triv h12.1.symm h12.2.symm
  /- The spoke 3 subpart, for the old hub (Coq `conv_part3`). -/
  have hfit5 := G.fitp_drop 5 p x hfit
  have hsz5 : G.arity x = 5 + sizePart (dropPart 5 p) := by
    rw [size_drop_part, ← hsz]
    have := hG.pentagonal x
    omega
  have C3 : ∀ Q, G.fitp (G.face e2) Q → G.fitp e2 (convPart3 h23 (dropPart 5 p) Q) := by
    generalize dropPart 5 p = p6 at hfit5 hsz5
    intro Q hQ
    rcases p6 with _ | ⟨f31, _, p7⟩ | ⟨_, _, p7⟩ | ⟨_, _, _, p7⟩ | ⟨_, _, _, _, p7⟩
    case nil =>
      simp only [convPart3, fitp, Bool.and_eq_true, T3a, hsz5]
      exact ⟨rfl, C12.1, hQ⟩
    case cons =>
      rcases p7 with _ | ⟨f32, _, p8⟩ | ⟨_, _, p8⟩ | ⟨_, _, _, p8⟩ | ⟨_, _, _, _, p8⟩
      case nil =>
        simp only [convPart3, fitp, Bool.and_eq_true, T3a, hsz5]
        exact ⟨rfl, C12.1, hQ⟩
      case cons =>
        rcases p8 with _ | ⟨f33, _, p9⟩ | ⟨_, _, p9⟩ | ⟨_, _, _, p9⟩ | ⟨_, _, _, _, p9⟩
        case nil =>
          simp only [fitp, Bool.and_eq_true] at hfit5
          obtain ⟨F31, -, F32, -, -⟩ := hfit5
          simp only [convPart3]
          split
          · simp only [fitp, Bool.and_eq_true, T3a, hsz5]
            exact ⟨rfl, C12.1, hQ⟩
          · simp only [fitp, Bool.and_eq_true, T3a, T3c, T3d, hsz5]
            exact ⟨rfl, C12.1, F31, F32, hQ⟩
        case cons =>
          rcases p9 with _ | ⟨_, _, p10⟩ | ⟨_, _, p10⟩ | ⟨_, _, _, p10⟩ | ⟨_, _, _, _, p10⟩
          case nil =>
            simp only [fitp, Bool.and_eq_true] at hfit5
            obtain ⟨F31, -, F32, -, F33, -, -⟩ := hfit5
            simp only [convPart3, fitp, Bool.and_eq_true, T3a, T3c, T3d, T3e, hsz5]
            exact ⟨rfl, C12.1, F31, F32, F33, hQ⟩
          all_goals rfl
        all_goals rfl
      all_goals rfl
    all_goals rfl
  /- Assembly (Coq `converse_part`). -/
  have harity : G.arity x' = G.arity e2 := by
    rw [← G.arity_face x', ← G.arity_face (G.face x'), T12h]
  simp only [conversePart, h4, h5, h12, tightFitp, Bool.and_eq_true]
  exact ⟨by rw [harity]; exact C5.1, C12.2 _ (C3 _ (C4.2 _ C5.2))⟩

end Hypermap

end FourColor
