/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Part.Fit

/-!
# Parts: mirror images  (port of `part.v`, section `FitMirrorPart`)

In a plain cubic map `G`:

* `fitp_mirror`: `x` exactly fits `mirrorPart p` in `G` iff it exactly fits `p` in
  `G.mirror`.
* `fitp_sym`: for a symmetric part `p` (one that is contained in its mirror image), fitting
  `p` in `G.mirror` and in `G` are equivalent.

The Coq proof is a tactic-heavy induction; here we prove a "sector" statement by induction on
the part (`mirror_sector`), from three geometric facts: the spoke, hat and fan arities of a
subpart of `G.mirror` anchored at `face w` are the spoke, hat and (reversed) fan arities of the
subpart of `G` anchored at `w` (for the hat: at `face w`).
-/

namespace FourColor

universe u

variable {D : Type u}

/-! ### Auxiliary list lemmas for `mirrorPartRec` -/

private theorem catPart_assoc (a b c : Part) :
    catPart (catPart a b) c = catPart a (catPart b c) := by
  induction a <;> simp only [catPart, *]

/-- `mirrorPartRec h0 rp p` is the mirror image of `p` followed by `rp`. -/
private theorem mirrorPartRec_cat (h0 : Prange) (p rp : Part) :
    mirrorPartRec h0 rp p = catPart (mirrorPartRec h0 .nil p) rp := by
  induction p generalizing rp with
  | nil => rfl
  | cons s _ p ih =>
    show mirrorPartRec h0 (.cons s _ rp) p = catPart (mirrorPartRec h0 (.cons s _ .nil) p) rp
    rw [ih (.cons s _ rp), ih (.cons s _ .nil), catPart_assoc]
    rfl
  | cons6 _ f1 p ih =>
    show mirrorPartRec h0 (.cons6 _ f1 rp) p = catPart (mirrorPartRec h0 (.cons6 _ f1 .nil) p) rp
    rw [ih (.cons6 _ f1 rp), ih (.cons6 _ f1 .nil), catPart_assoc]
    rfl
  | cons7 _ f1 f2 p ih =>
    show mirrorPartRec h0 (.cons7 _ f2 f1 rp) p =
      catPart (mirrorPartRec h0 (.cons7 _ f2 f1 .nil) p) rp
    rw [ih (.cons7 _ f2 f1 rp), ih (.cons7 _ f2 f1 .nil), catPart_assoc]
    rfl
  | cons8 _ f1 f2 f3 p ih =>
    show mirrorPartRec h0 (.cons8 _ f3 f2 f1 rp) p =
      catPart (mirrorPartRec h0 (.cons8 _ f3 f2 f1 .nil) p) rp
    rw [ih (.cons8 _ f3 f2 f1 rp), ih (.cons8 _ f3 f2 f1 .nil), catPart_assoc]
    rfl

private theorem size_mirrorPartRec (h0 : Prange) (p : Part) :
    sizePart (mirrorPartRec h0 .nil p) = sizePart p := by
  induction p with
  | nil => rfl
  | cons _ _ p ih | cons6 _ _ p ih | cons7 _ _ _ p ih | cons8 _ _ _ _ p ih =>
    simp only [mirrorPartRec]
    rw [mirrorPartRec_cat, size_cat_part, ih]
    rfl

/-- The first hat of `mirrorPartRec h0 rp p` is `h0`, for `p` not nil. -/
private theorem nextHat_mirrorPartRec (h0 h' : Prange) (p rp : Part) (hp : p ≠ .nil) :
    nextHat h' (mirrorPartRec h0 rp p) = h0 := by
  induction p generalizing rp with
  | nil => exact absurd rfl hp
  | cons _ _ p ih | cons6 _ _ p ih | cons7 _ _ _ p ih | cons8 _ _ _ _ p ih =>
    simp only [mirrorPartRec]
    cases p with
    | nil => rfl
    | _ => exact ih _ (by simp)

private theorem nextHat_getHat (p : Part) : nextHat (getHat p) p = getHat p := by
  cases p <;> rfl

namespace Hypermap

variable (G : Hypermap D)

/-- The first hat constraint of a fitting part. -/
private theorem fitp_getHat {x : D} {p : Part} (h : G.fitp x p) (hp : p ≠ .nil) :
    memRange (getHat p) (G.arity (SubpartLoc.hat.move G x)) := by
  cases p with
  | nil => exact absurd rfl hp
  | _ => simp only [fitp, Bool.and_eq_true] at h; exact h.2.1

/-! ### Geometry of the mirror map -/

section MirrorGeometry

variable [Finite D]

/-- `mirror` face is the inverse of `face`. -/
private theorem mirror_face_iter (k : ℕ) (w : D) : G.mirror.face^[k] (G.face^[k] w) = w := by
  induction k generalizing w with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply (f := G.mirror.face),
      Function.iterate_succ_apply' (f := G.face)]
    show G.mirror.face^[k] (G.edge (G.node (G.face (G.face^[k] w)))) = w
    rw [G.faceK, ih]

private theorem mirror_edge_face (hG : G.PlainCubic) (w : D) :
    G.mirror.edge (G.face w) = G.face (G.edge w) := by
  rw [mirror_edge, G.plain_eq' hG.plain]

/-- The spoke of the mirror subpart at `face w` is the spoke of the subpart at `w`
(Coq `Ears`). -/
private theorem mirror_arity_spoke (hG : G.PlainCubic) (w : D) :
    G.mirror.arity (SubpartLoc.spoke.move G.mirror (G.face w)) =
      G.arity (SubpartLoc.spoke.move G w) := by
  show G.mirror.arity (G.mirror.edge (G.face w)) = G.arity (G.edge w)
  rw [G.arity_mirror, G.mirror_edge_face hG, G.arity_face]

/-- The hats of `G.mirror` are those of `G` (Coq `Ears2`). -/
private theorem mirror_arity_hat (hG : G.PlainCubic) (y : D) :
    G.mirror.arity (SubpartLoc.hat.move G.mirror y) = G.arity (SubpartLoc.hat.move G y) := by
  have hF : ∀ y, G.face y = G.node (G.node (G.edge y)) := fun y => by
    rw [G.cubic_eq' hG.cubic, G.plain_eq hG.plain]
  have hE : ∀ y, G.edge (G.edge y) = y := G.plain_eq hG.plain
  have hN : ∀ y, G.node (G.node (G.node y)) = y := G.cubic_eq hG.cubic
  have key : G.face (G.edge (G.face (G.face (G.edge y)))) =
      G.node (G.edge (G.node (G.node y))) := by
    simp only [hF, hE, hN]
  have e1 : G.mirror.edge (G.mirror.face (G.mirror.face (G.mirror.edge y))) =
      G.face (G.node (G.edge (G.node (G.node y)))) := by
    simp only [mirror_edge, mirror_face, G.faceK]
  show G.mirror.arity (G.mirror.edge (G.mirror.face (G.mirror.face (G.mirror.edge y)))) =
    G.arity (G.edge (G.face (G.face (G.edge y))))
  rw [G.arity_mirror, e1, G.arity_face, ← key, G.arity_face]

/-- The fans of the mirror subpart at `face w` are the fans of the subpart at `w`, in
reverse order (Coq `Earsf`). -/
private theorem mirror_arity_fan (hG : G.PlainCubic) (n m : ℕ) (w : D)
    (hm : G.arity (G.edge w) = m) (hnm : n ≤ m) :
    G.mirror.arity (G.mirror.edge (G.mirror.face^[n] (G.mirror.edge (G.face w)))) =
      G.arity (G.edge (G.face^[m - n] (G.edge w))) := by
  have hv : G.face (G.edge w) = G.face^[n] (G.face (G.face^[m - n] (G.edge w))) := by
    rw [← Function.iterate_succ_apply' G.face, ← Function.iterate_add_apply,
      show n + (m - n).succ = m + 1 by omega, Function.iterate_succ_apply', ← hm,
      G.iter_face_arity]
  rw [G.mirror_edge_face hG, hv, G.mirror_face_iter, G.mirror_edge_face hG, G.arity_mirror,
    G.arity_face]

end MirrorGeometry

/-! ### Mirror fitting (Coq section `FitMirrorPart`) -/

private theorem memRange_ne {r : Prange} {n m : ℕ} (hr : ∀ k, memRange r k = (k == m))
    (hn : n ≠ m) : memRange r n = false := by
  rw [hr]
  simpa using hn

/-- The sector version of `fitp_mirror`: the mirror image of a sector fits at `z` iff the
sector fits in `G.mirror` at `face^[size p] z`, up to the hat constraints on the boundary. -/
private theorem mirror_sector [Finite D] (hG : G.PlainCubic) (h0 : Prange) (z : D) (p : Part) :
    (G.mirror.fitp (G.face^[sizePart p] z) p &&
        memRange h0 (G.arity (SubpartLoc.hat.move G z))) =
      (G.fitp z (mirrorPartRec h0 .nil p) &&
        memRange (nextHat h0 p) (G.arity (SubpartLoc.hat.move G (G.face^[sizePart p] z)))) := by
  induction p with
  | nil => rfl
  | cons s h p ih =>
    show (G.mirror.fitp (G.face^[sizePart p + 1] z) (.cons s h p) && _) =
      (G.fitp z (mirrorPartRec h0 (.cons s (nextHat h0 p) .nil) p) &&
        memRange h (G.arity (SubpartLoc.hat.move G (G.face^[sizePart p + 1] z))))
    rw [Function.iterate_succ_apply', mirrorPartRec_cat, fitp_cat, size_mirrorPartRec]
    generalize G.face^[sizePart p] z = w at ih ⊢
    simp only [fitp]
    rw [G.mirror_arity_spoke hG w, G.mirror_arity_hat hG (G.face w),
      show G.mirror.face (G.face w) = w from G.faceK w]
    simp only [Bool.and_assoc]
    rw [ih]
    simp only [Bool.true_and, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
  | cons6 h f1 p ih =>
    show (G.mirror.fitp (G.face^[sizePart p + 1] z) (.cons6 h f1 p) && _) =
      (G.fitp z (mirrorPartRec h0 (.cons6 (nextHat h0 p) f1 .nil) p) &&
        memRange h (G.arity (SubpartLoc.hat.move G (G.face^[sizePart p + 1] z))))
    rw [Function.iterate_succ_apply', mirrorPartRec_cat, fitp_cat, size_mirrorPartRec]
    generalize G.face^[sizePart p] z = w at ih ⊢
    simp only [fitp]
    rw [G.mirror_arity_spoke hG w, G.mirror_arity_hat hG (G.face w),
      show G.mirror.face (G.face w) = w from G.faceK w]
    by_cases hm : G.arity (SubpartLoc.spoke.move G w) = 6
    · have f1e : G.mirror.arity (SubpartLoc.fan1.move G.mirror (G.face w)) =
          G.arity (SubpartLoc.fan1.move G w) := G.mirror_arity_fan hG 3 6 w hm (by omega)
      rw [f1e]
      simp only [Bool.and_assoc]
      rw [ih]
      simp only [Bool.true_and, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
    · rw [memRange_ne (fun _ => rfl) hm]
      simp
  | cons7 h f1 f2 p ih =>
    show (G.mirror.fitp (G.face^[sizePart p + 1] z) (.cons7 h f1 f2 p) && _) =
      (G.fitp z (mirrorPartRec h0 (.cons7 (nextHat h0 p) f2 f1 .nil) p) &&
        memRange h (G.arity (SubpartLoc.hat.move G (G.face^[sizePart p + 1] z))))
    rw [Function.iterate_succ_apply', mirrorPartRec_cat, fitp_cat, size_mirrorPartRec]
    generalize G.face^[sizePart p] z = w at ih ⊢
    simp only [fitp]
    rw [G.mirror_arity_spoke hG w, G.mirror_arity_hat hG (G.face w),
      show G.mirror.face (G.face w) = w from G.faceK w]
    by_cases hm : G.arity (SubpartLoc.spoke.move G w) = 7
    · have f1e : G.mirror.arity (SubpartLoc.fan1.move G.mirror (G.face w)) =
          G.arity (SubpartLoc.fan2.move G w) := G.mirror_arity_fan hG 3 7 w hm (by omega)
      have f2e : G.mirror.arity (SubpartLoc.fan2.move G.mirror (G.face w)) =
          G.arity (SubpartLoc.fan1.move G w) := G.mirror_arity_fan hG 4 7 w hm (by omega)
      rw [f1e, f2e]
      simp only [Bool.and_assoc]
      rw [ih]
      simp only [Bool.true_and, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
    · rw [memRange_ne (fun _ => rfl) hm]
      simp
  | cons8 h f1 f2 f3 p ih =>
    show (G.mirror.fitp (G.face^[sizePart p + 1] z) (.cons8 h f1 f2 f3 p) && _) =
      (G.fitp z (mirrorPartRec h0 (.cons8 (nextHat h0 p) f3 f2 f1 .nil) p) &&
        memRange h (G.arity (SubpartLoc.hat.move G (G.face^[sizePart p + 1] z))))
    rw [Function.iterate_succ_apply', mirrorPartRec_cat, fitp_cat, size_mirrorPartRec]
    generalize G.face^[sizePart p] z = w at ih ⊢
    simp only [fitp]
    rw [G.mirror_arity_spoke hG w, G.mirror_arity_hat hG (G.face w),
      show G.mirror.face (G.face w) = w from G.faceK w]
    by_cases hm : G.arity (SubpartLoc.spoke.move G w) = 8
    · have f1e : G.mirror.arity (SubpartLoc.fan1.move G.mirror (G.face w)) =
          G.arity (SubpartLoc.fan3.move G w) := G.mirror_arity_fan hG 3 8 w hm (by omega)
      have f2e : G.mirror.arity (SubpartLoc.fan2.move G.mirror (G.face w)) =
          G.arity (SubpartLoc.fan2.move G w) := G.mirror_arity_fan hG 4 8 w hm (by omega)
      have f3e : G.mirror.arity (SubpartLoc.fan3.move G.mirror (G.face w)) =
          G.arity (SubpartLoc.fan1.move G w) := G.mirror_arity_fan hG 5 8 w hm (by omega)
      rw [f1e, f2e, f3e]
      simp only [Bool.and_assoc]
      rw [ih]
      simp only [Bool.true_and, Bool.and_assoc, Bool.and_comm, Bool.and_left_comm]
    · rw [memRange_ne (fun _ => rfl) hm]
      simp

/-- Coq `fitp_mirror`. -/
theorem fitp_mirror [Finite D] (hG : G.PlainCubic) (p : Part) (x : D) :
    G.exactFitp x (mirrorPart p) = G.mirror.exactFitp x p := by
  unfold exactFitp
  rw [size_mirror_part, G.arity_mirror]
  by_cases hx : G.arity x = sizePart p
  swap
  · have : (G.arity x == sizePart p) = false := by simpa using hx
    rw [this, Bool.false_and, Bool.false_and]
  rw [hx, beq_self_eq_true, Bool.true_and, Bool.true_and]
  rcases eq_or_ne p .nil with rfl | hne
  · rfl
  have key := G.mirror_sector hG (getHat p) x p
  rw [← hx, G.iter_face_arity, nextHat_getHat] at key
  have hM : G.mirror.fitp x p → memRange (getHat p) (G.arity (SubpartLoc.hat.move G x)) :=
    fun h => by
      have := G.mirror.fitp_getHat h hne
      rwa [G.mirror_arity_hat hG] at this
  have hGm : G.fitp x (mirrorPartRec (getHat p) .nil p) →
      memRange (getHat p) (G.arity (SubpartLoc.hat.move G x)) := fun h => by
    have hne' : mirrorPartRec (getHat p) .nil p ≠ .nil := by
      intro h0
      have := size_mirrorPartRec (getHat p) p
      rw [h0] at this
      cases p <;> simp_all [sizePart]
    have := G.fitp_getHat h hne'
    rwa [getHat, nextHat_mirrorPartRec _ _ _ _ hne] at this
  show G.fitp x (mirrorPartRec (getHat p) .nil p) = G.mirror.fitp x p
  revert key hM hGm
  cases G.mirror.fitp x p <;> cases G.fitp x (mirrorPartRec (getHat p) .nil p) <;>
    cases memRange (getHat p) (G.arity (SubpartLoc.hat.move G x)) <;> simp

/-- Coq `fitp_sym`. -/
theorem fitp_sym [Finite D] (hG : G.PlainCubic) (p : Part)
    (hp : cmpPart p (mirrorPart p) = .subset) (x : D) :
    G.mirror.exactFitp x p = G.exactFitp x p := by
  apply Bool.eq_iff_iff.2
  constructor
  · intro h
    simp only [exactFitp, Bool.and_eq_true] at h
    rw [← mirror_mirror_part p, G.fitp_mirror hG (mirrorPart p) x]
    simp only [exactFitp, Bool.and_eq_true, size_mirror_part]
    refine ⟨h.1, ?_⟩
    rw [G.mirror.fitp_cmp p x h.2 (mirrorPart p), hp]
    rfl
  · intro h
    rw [← G.fitp_mirror hG p x]
    simp only [exactFitp, Bool.and_eq_true, size_mirror_part] at h ⊢
    refine ⟨h.1, ?_⟩
    rw [G.fitp_cmp p x h.2 (mirrorPart p), hp]
    rfl

end Hypermap

end FourColor
