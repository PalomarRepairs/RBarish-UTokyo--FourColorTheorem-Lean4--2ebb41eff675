/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Part.Basic

/-!
# Parts: fitting semantics  (port of `part.v`, section `FitPart` and `part_update`)

For a hypermap `G : Hypermap D` and a dart `x : D`:

* `SubpartLoc.move i G x` (Coq `subpart_loc_move`, a coercion `subpart_loc >-> Funclass`):
  the dart of the face at sublocation `i` of the subpart anchored at `x`, e.g.
  `SubpartLoc.spoke.move G x = G.edge x`.
* `G.fitp x p` (Coq `fitp`): the first spokes of `x` fit the (sector) part `p`.
* `G.exactFitp x p` (Coq `exact_fitp`): `x` fits `p`, including at the hub:
  `G.arity x = sizePart p`.
* `G.tightFitp x (u, p)` (Coq `tight_fitp`): `x` fits sector part `p`, and the arity of `x`
  is in the range `u` (used for `conversePart`).
* `PartUpdate fp i` (Coq `part_update`): `fp` is a valid part constructor at `i`: `fp r p`
  adds one subpart to `p`, and any `x` fitting sector `fp r p` fits `fp r' p` iff the arity
  at `i` is in `r'`.

The fitting predicates are `Bool`-valued, as in Coq (they are counted in `discharge`); they
are noncomputable since `Hypermap.arity` is.
-/

namespace FourColor

universe u

variable {D : Type u}

/-- Coq `subpart_loc_move i G x` (a coercion `subpart_loc >-> Funclass` in Coq): maps the
hub dart `x` of a subpart to a dart in the face at sublocation `i`, e.g.,
`SubpartLoc.spoke.move G x = G.edge x`. -/
def SubpartLoc.move (i : SubpartLoc) (G : Hypermap D) (x : D) : D :=
  match i with
  | .spoke => G.edge x
  | .hat => G.edge (G.face^[2] (G.edge x))
  | .fan1 => G.edge (G.face^[3] (G.edge x))
  | .fan2 => G.edge (G.face^[4] (G.edge x))
  | .fan3 => G.edge (G.face^[5] (G.edge x))

namespace Hypermap

variable (G : Hypermap D)

/-! ### Part semantics: matching map (Coq section `FitPart`) -/

/-- Coq `fitp x p`: the first spokes of `x` fit the (sector) part `p`. -/
noncomputable def fitp (x : D) (p : Part) : Bool :=
  match p with
  | .cons s h p' =>
    memRange s (G.arity (SubpartLoc.spoke.move G x)) &&
      (memRange h (G.arity (SubpartLoc.hat.move G x)) && fitp (G.face x) p')
  | .cons6 h f1 p' =>
    memRange .pr66 (G.arity (SubpartLoc.spoke.move G x)) &&
      (memRange h (G.arity (SubpartLoc.hat.move G x)) &&
        (memRange f1 (G.arity (SubpartLoc.fan1.move G x)) && fitp (G.face x) p'))
  | .cons7 h f1 f2 p' =>
    memRange .pr77 (G.arity (SubpartLoc.spoke.move G x)) &&
      (memRange h (G.arity (SubpartLoc.hat.move G x)) &&
        (memRange f1 (G.arity (SubpartLoc.fan1.move G x)) &&
          (memRange f2 (G.arity (SubpartLoc.fan2.move G x)) && fitp (G.face x) p')))
  | .cons8 h f1 f2 f3 p' =>
    memRange .pr88 (G.arity (SubpartLoc.spoke.move G x)) &&
      (memRange h (G.arity (SubpartLoc.hat.move G x)) &&
        (memRange f1 (G.arity (SubpartLoc.fan1.move G x)) &&
          (memRange f2 (G.arity (SubpartLoc.fan2.move G x)) &&
            (memRange f3 (G.arity (SubpartLoc.fan3.move G x)) && fitp (G.face x) p'))))
  | .nil => true

/-- Coq `exact_fitp x p`: `x` fits `p`, including at the hub: `arity x = size_part p`. -/
noncomputable def exactFitp (x : D) (p : Part) : Bool :=
  (G.arity x == sizePart p) && G.fitp x p

/-- Coq `tight_fitp x (u, p)`: `x` fits sector part `p`, and the arity of `x` is in the
range `u` (an intermediate notion, for part converse). -/
noncomputable def tightFitp (x : D) (up : Prange × Part) : Bool :=
  match up with
  | (u, p) => memRange u (G.arity x) && G.fitp x p

/-! Simple properties of `fitp` (that do not require geometrical properties), that is, list
functions, comparison, meet, and split. -/

/-- Coq `fitp_drop`. -/
theorem fitp_drop (n : ℕ) (p : Part) (x : D) (hp : G.fitp x p) :
    G.fitp (G.face^[n] x) (dropPart n p) := by
  induction n generalizing p x with
  | zero => cases p <;> exact hp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases p with
    | nil => rfl
    | cons s h p =>
      simp only [fitp, Bool.and_eq_true] at hp
      exact ih p _ hp.2.2
    | cons6 h f1 p =>
      simp only [fitp, Bool.and_eq_true] at hp
      exact ih p _ hp.2.2.2
    | cons7 h f1 f2 p =>
      simp only [fitp, Bool.and_eq_true] at hp
      exact ih p _ hp.2.2.2.2
    | cons8 h f1 f2 f3 p =>
      simp only [fitp, Bool.and_eq_true] at hp
      exact ih p _ hp.2.2.2.2.2

/-- Coq `fitp_cat`. -/
theorem fitp_cat (x : D) (p1 p2 : Part) :
    G.fitp x (catPart p1 p2) = (G.fitp x p1 && G.fitp (G.face^[sizePart p1] x) p2) := by
  induction p1 generalizing x with
  | nil => simp [catPart, fitp, sizePart]
  | cons _ _ p ih | cons6 _ _ p ih | cons7 _ _ _ p ih | cons8 _ _ _ _ p ih =>
    simp only [catPart, fitp, ih, sizePart, Function.iterate_succ_apply, Bool.and_assoc]

/-- `take`/`drop` split the size of a part. -/
private theorem size_take_add_drop (n : ℕ) (p : Part) :
    sizePart (takePart n p) + sizePart (dropPart n p) = sizePart p := by
  conv_rhs => rw [← cat_take_drop_part n p]
  rw [size_cat_part]

/-- Coq `fitp_rot`. -/
theorem fitp_rot [Finite D] (n : ℕ) (p : Part) (hn : n ≤ sizePart p) (x : D) :
    G.exactFitp x p = G.exactFitp (G.face^[n] x) (rotPart n p) := by
  unfold exactFitp
  rw [size_rot_part, G.arity_iter_face]
  by_cases hx : G.arity x = sizePart p
  · have htd := size_take_add_drop n p
    have hdrop := size_drop_part n p
    have htake : sizePart (takePart n p) = n := by omega
    simp only [hx, beq_self_eq_true, Bool.true_and]
    conv_lhs => rw [← cat_take_drop_part n p]
    rw [rotPart, fitp_cat, fitp_cat, htake, Bool.and_comm, hdrop,
      ← Function.iterate_add_apply, Nat.sub_add_cancel hn, ← hx, G.iter_face_arity]
  · have : (G.arity x == sizePart p) = false := by simpa using hx
    rw [this, Bool.false_and, Bool.false_and]

/-- Coq `fitp_catrev`. -/
theorem fitp_catrev (x : D) (p1 p2 : Part) :
    G.fitp x (catrevPart p1 p2) =
      (G.fitp x (revPart p1) && G.fitp (G.face^[sizePart p1] x) p2) := by
  rw [catrev_part_eq, fitp_cat, size_rev_part]

/-! ### Comparison and meet -/

/-- Coq section `Let Epr`. -/
private theorem epr (m n : ℕ) :
    (m == n) = (match n with
      | 6 => memRange .pr66 m
      | 7 => memRange .pr77 m
      | 8 => memRange .pr88 m
      | _ => m == n) := by
  split <;> simp [memRange]

/-- Soundness of a comparison result `c` for a membership bit `b`. -/
private theorem rel_meet {c1 c2 : PartRel} {b1 b2 : Bool} (h1 : b1 = applyPartRel c1 b1)
    (h2 : b2 = applyPartRel c2 b2) :
    (b1 && b2) = applyPartRel (meetPrel c1 c2) (b1 && b2) := by
  revert h1 h2
  cases c1 <;> cases c2 <;> cases b1 <;> cases b2 <;> decide

private theorem rel_notPsubset {c : PartRel} {b : Bool} (h : b = applyPartRel c b) :
    b = applyPartRel (notPsubset c) b := by
  revert h
  cases c <;> cases b <;> decide

private theorem rel_fan {c : PartRel} {b : Bool} (f : Bool) (h : b = applyPartRel c b) :
    (f && b) = applyPartRel (notPsubset c) (f && b) := by
  revert h
  cases c <;> cases b <;> cases f <;> decide

private theorem rel_fan' {c : PartRel} {b : Bool} (f : Bool)
    (h : b = applyPartRel (notPsubset c) b) :
    (f && b) = applyPartRel (notPsubset c) (f && b) := by
  revert h
  cases c <;> cases b <;> cases f <;> decide

private theorem meetPrel_notPsubset (c1 c2 c3 : PartRel) :
    meetPrel (notPsubset c1) (meetPrel c2 c3) =
      meetPrel (notPsubset c1) (meetPrel c2 (notPsubset c3)) := by
  cases c1 <;> cases c2 <;> cases c3 <;> rfl

/-- The comparison of a subpart without fan constraints to a subpart with fans. -/
private theorem rel_fans {cs ch cr : PartRel} {S H T R : Bool} (hS : S = applyPartRel cs S)
    (hH : H = applyPartRel ch H) (hR : R = applyPartRel cr R)
    (hT : T = applyPartRel (notPsubset cr) T ∨ T = R) :
    (S && (H && T)) = applyPartRel (meetPrel (notPsubset cs) (meetPrel ch cr))
      (S && (H && T)) := by
  rw [meetPrel_notPsubset]
  refine rel_meet (rel_notPsubset hS) (rel_meet hH ?_)
  rcases hT with hT | rfl
  · exact hT
  · exact rel_notPsubset hR

/-- Membership in a singleton range. -/
private theorem memRange_eq {r : Prange} {n m : ℕ} (hr : ∀ k, memRange r k = (k == m))
    (hn : memRange r n) : n = m := by
  rw [hr] at hn
  simpa using hn

/-- Coq `fitp_cmp`. -/
theorem fitp_cmp (p : Part) (x : D) (hp : G.fitp x p) (q : Part) :
    G.fitp x q = applyPartRel (cmpPart p q) (G.fitp x q) := by
  induction p generalizing x q with
  | nil => cases q <;> rfl
  | cons sp hp p ih =>
    simp only [fitp, Bool.and_eq_true] at hp
    obtain ⟨hS, hH, hP⟩ := hp
    have hS' := mem_cmp_range _ _ hS
    have hH' := mem_cmp_range _ _ hH
    cases q with
    | nil => rfl
    | cons sq hq q => exact rel_meet (hS' sq) (rel_meet (hH' hq) (ih _ hP q))
    | cons6 hq f1q q =>
      exact rel_fans (hS' .pr66) (hH' hq) (ih _ hP q)
        (Or.inl (rel_fan _ (ih _ hP q)))
    | cons7 hq f1q f2q q =>
      exact rel_fans (hS' .pr77) (hH' hq) (ih _ hP q)
        (Or.inl (rel_fan' _ (rel_fan _ (ih _ hP q))))
    | cons8 hq f1q f2q f3q q =>
      exact rel_fans (hS' .pr88) (hH' hq) (ih _ hP q)
        (Or.inl (rel_fan' _ (rel_fan' _ (rel_fan _ (ih _ hP q)))))
  | cons6 hp f1p p ih =>
    simp only [fitp, Bool.and_eq_true] at hp
    obtain ⟨hS, hH, hF1, hP⟩ := hp
    have hS6 : G.arity (SubpartLoc.spoke.move G x) = 6 := memRange_eq (fun _ => rfl) hS
    have hS' := mem_cmp_range _ _ hS
    have hH' := mem_cmp_range _ _ hH
    have hF1' := mem_cmp_range _ _ hF1
    cases q with
    | nil => rfl
    | cons sq hq q => exact rel_meet (hS' sq) (rel_meet (hH' hq) (ih _ hP q))
    | cons6 hq f1q q =>
      simp only [fitp, cmpPart, hS, Bool.true_and]
      exact rel_meet (hH' hq) (rel_meet (hF1' f1q) (ih _ hP q))
    | cons7 hq f1q f2q q => simp [fitp, cmpPart, hS6, memRange, applyPartRel]
    | cons8 hq f1q f2q f3q q => simp [fitp, cmpPart, hS6, memRange, applyPartRel]
  | cons7 hp f1p f2p p ih =>
    simp only [fitp, Bool.and_eq_true] at hp
    obtain ⟨hS, hH, hF1, hF2, hP⟩ := hp
    have hS7 : G.arity (SubpartLoc.spoke.move G x) = 7 := memRange_eq (fun _ => rfl) hS
    have hS' := mem_cmp_range _ _ hS
    have hH' := mem_cmp_range _ _ hH
    have hF1' := mem_cmp_range _ _ hF1
    have hF2' := mem_cmp_range _ _ hF2
    cases q with
    | nil => rfl
    | cons sq hq q => exact rel_meet (hS' sq) (rel_meet (hH' hq) (ih _ hP q))
    | cons6 hq f1q q => simp [fitp, cmpPart, hS7, memRange, applyPartRel]
    | cons7 hq f1q f2q q =>
      simp only [fitp, cmpPart, hS, Bool.true_and]
      exact rel_meet (hH' hq) (rel_meet (hF1' f1q) (rel_meet (hF2' f2q) (ih _ hP q)))
    | cons8 hq f1q f2q f3q q => simp [fitp, cmpPart, hS7, memRange, applyPartRel]
  | cons8 hp f1p f2p f3p p ih =>
    simp only [fitp, Bool.and_eq_true] at hp
    obtain ⟨hS, hH, hF1, hF2, hF3, hP⟩ := hp
    have hS8 : G.arity (SubpartLoc.spoke.move G x) = 8 := memRange_eq (fun _ => rfl) hS
    have hS' := mem_cmp_range _ _ hS
    have hH' := mem_cmp_range _ _ hH
    have hF1' := mem_cmp_range _ _ hF1
    have hF2' := mem_cmp_range _ _ hF2
    have hF3' := mem_cmp_range _ _ hF3
    cases q with
    | nil => rfl
    | cons sq hq q => exact rel_meet (hS' sq) (rel_meet (hH' hq) (ih _ hP q))
    | cons6 hq f1q q => simp [fitp, cmpPart, hS8, memRange, applyPartRel]
    | cons7 hq f1q f2q q => simp [fitp, cmpPart, hS8, memRange, applyPartRel]
    | cons8 hq f1q f2q f3q q =>
      simp only [fitp, cmpPart, hS, Bool.true_and]
      exact rel_meet (hH' hq) (rel_meet (hF1' f1q) (rel_meet (hF2' f2q)
        (rel_meet (hF3' f3q) (ih _ hP q))))

/-- Coq `fitp_meet`. -/
theorem fitp_meet (p q : Part) (x : D) (hp : G.fitp x p) (hq : G.fitp x q) :
    G.fitp x (meetPart p q) := by
  induction p generalizing q x with
  | nil => cases q <;> rfl
  | cons sp hp p ih =>
    cases q with
    | nil => exact hp
    | cons sq hq q =>
      simp only [fitp, Bool.and_eq_true, meetPart] at hp hq ⊢
      exact ⟨mem_meet_range _ _ _ hp.1 hq.1, mem_meet_range _ _ _ hp.2.1 hq.2.1,
        ih _ _ hp.2.2 hq.2.2⟩
    | cons6 hq f1 q =>
      simp only [fitp, Bool.and_eq_true, meetPart] at hp hq ⊢
      exact ⟨hq.1, mem_meet_range _ _ _ hp.2.1 hq.2.1, hq.2.2.1, ih _ _ hp.2.2 hq.2.2.2⟩
    | cons7 hq f1 f2 q =>
      simp only [fitp, Bool.and_eq_true, meetPart] at hp hq ⊢
      exact ⟨hq.1, mem_meet_range _ _ _ hp.2.1 hq.2.1, hq.2.2.1, hq.2.2.2.1,
        ih _ _ hp.2.2 hq.2.2.2.2⟩
    | cons8 hq f1 f2 f3 q =>
      simp only [fitp, Bool.and_eq_true, meetPart] at hp hq ⊢
      exact ⟨hq.1, mem_meet_range _ _ _ hp.2.1 hq.2.1, hq.2.2.1, hq.2.2.2.1, hq.2.2.2.2.1,
        ih _ _ hp.2.2 hq.2.2.2.2.2⟩
  | cons6 hp f1p p ih =>
    cases q with
    | nil => exact hp
    | cons sq hq q =>
      simp only [fitp, Bool.and_eq_true, meetPart] at hp hq ⊢
      exact ⟨hp.1, mem_meet_range _ _ _ hp.2.1 hq.2.1, hp.2.2.1, ih _ _ hp.2.2.2 hq.2.2⟩
    | cons6 hq f1q q =>
      simp only [fitp, Bool.and_eq_true, meetPart] at hp hq ⊢
      exact ⟨hp.1, mem_meet_range _ _ _ hp.2.1 hq.2.1, mem_meet_range _ _ _ hp.2.2.1 hq.2.2.1,
        ih _ _ hp.2.2.2 hq.2.2.2⟩
    | cons7 | cons8 => exact hp
  | cons7 hp f1p f2p p ih =>
    cases q with
    | nil => exact hp
    | cons sq hq q =>
      simp only [fitp, Bool.and_eq_true, meetPart] at hp hq ⊢
      exact ⟨hp.1, mem_meet_range _ _ _ hp.2.1 hq.2.1, hp.2.2.1, hp.2.2.2.1,
        ih _ _ hp.2.2.2.2 hq.2.2⟩
    | cons7 hq f1q f2q q =>
      simp only [fitp, Bool.and_eq_true, meetPart] at hp hq ⊢
      exact ⟨hp.1, mem_meet_range _ _ _ hp.2.1 hq.2.1, mem_meet_range _ _ _ hp.2.2.1 hq.2.2.1,
        mem_meet_range _ _ _ hp.2.2.2.1 hq.2.2.2.1, ih _ _ hp.2.2.2.2 hq.2.2.2.2⟩
    | cons6 | cons8 => exact hp
  | cons8 hp f1p f2p f3p p ih =>
    cases q with
    | nil => exact hp
    | cons sq hq q =>
      simp only [fitp, Bool.and_eq_true, meetPart] at hp hq ⊢
      exact ⟨hp.1, mem_meet_range _ _ _ hp.2.1 hq.2.1, hp.2.2.1, hp.2.2.2.1, hp.2.2.2.2.1,
        ih _ _ hp.2.2.2.2.2 hq.2.2⟩
    | cons8 hq f1q f2q f3q q =>
      simp only [fitp, Bool.and_eq_true, meetPart] at hp hq ⊢
      exact ⟨hp.1, mem_meet_range _ _ _ hp.2.1 hq.2.1, mem_meet_range _ _ _ hp.2.2.1 hq.2.2.1,
        mem_meet_range _ _ _ hp.2.2.2.1 hq.2.2.2.1,
        mem_meet_range _ _ _ hp.2.2.2.2.1 hq.2.2.2.2.1, ih _ _ hp.2.2.2.2.2 hq.2.2.2.2.2⟩
    | cons6 | cons7 => exact hp

/-- Coq `exact_fitp_meet`. -/
theorem exact_fitp_meet (p q : Part) (x : D) (hp : G.exactFitp x p) (hq : G.fitp x q) :
    G.exactFitp x (meetPart p q) := by
  simp only [exactFitp, Bool.and_eq_true, size_meet_part] at hp ⊢
  exact ⟨hp.1, G.fitp_meet p q x hp.2 hq⟩

end Hypermap

/-! ### Part location semantics

A constructor function is valid with respect to a location if it only affects the validity
of the range at that location. This definition quantifies over all hypermaps. -/

/-- Coq `part_update fp i`: `fp` is a valid part constructor at `i : SubpartLoc`: `fp r p`
adds one subpart to `p`, and any `x` fitting sector `fp r p` fits `fp r' p` iff the arity at
`i` is in `r'`. (The Coq version quantifies over all (finite) hypermaps; here we quantify over
all hypermaps with darts in `Type u`, which is stronger.) -/
def PartUpdate (fp : Prange → Part → Part) (i : SubpartLoc) : Prop :=
  ∀ (r : Prange) (p : Part), sizePart (fp r p) = sizePart p + 1 ∧
    ∀ (D : Type u) (G : Hypermap D) (x : D), G.fitp x (fp r p) →
      memRange r (G.arity (i.move G x)) ∧
        ∀ r' : Prange, memRange r' (G.arity (i.move G x)) → G.fitp x (fp r' p)

/-- Coq `updatePs`. -/
theorem updatePs (h : Prange) : PartUpdate.{u} (fun r => Part.cons r h) .spoke := by
  intro r p
  refine ⟨rfl, fun D G x hx => ?_⟩
  simp only [Hypermap.fitp, Bool.and_eq_true] at hx ⊢
  exact ⟨hx.1, fun r' hr' => ⟨hr', hx.2⟩⟩

/-- Coq `updatePh`. -/
theorem updatePh (s : Prange) : PartUpdate.{u} (fun r => Part.cons s r) .hat := by
  intro r p
  refine ⟨rfl, fun D G x hx => ?_⟩
  simp only [Hypermap.fitp, Bool.and_eq_true] at hx ⊢
  exact ⟨hx.2.1, fun r' hr' => ⟨hx.1, hr', hx.2.2⟩⟩

/-- Coq `updateP6h`. -/
theorem updateP6h (f1 : Prange) : PartUpdate.{u} (fun r => Part.cons6 r f1) .hat := by
  intro r p
  refine ⟨rfl, fun D G x hx => ?_⟩
  simp only [Hypermap.fitp, Bool.and_eq_true] at hx ⊢
  exact ⟨hx.2.1, fun r' hr' => ⟨hx.1, hr', hx.2.2⟩⟩

/-- Coq `updateP6f1`. -/
theorem updateP6f1 (h : Prange) : PartUpdate.{u} (fun r => Part.cons6 h r) .fan1 := by
  intro r p
  refine ⟨rfl, fun D G x hx => ?_⟩
  simp only [Hypermap.fitp, Bool.and_eq_true] at hx ⊢
  exact ⟨hx.2.2.1, fun r' hr' => ⟨hx.1, hx.2.1, hr', hx.2.2.2⟩⟩

/-- Coq `updateP7h`. -/
theorem updateP7h (f1 f2 : Prange) : PartUpdate.{u} (fun r => Part.cons7 r f1 f2) .hat := by
  intro r p
  refine ⟨rfl, fun D G x hx => ?_⟩
  simp only [Hypermap.fitp, Bool.and_eq_true] at hx ⊢
  exact ⟨hx.2.1, fun r' hr' => ⟨hx.1, hr', hx.2.2⟩⟩

/-- Coq `updateP7f1`. -/
theorem updateP7f1 (h f2 : Prange) : PartUpdate.{u} (fun r => Part.cons7 h r f2) .fan1 := by
  intro r p
  refine ⟨rfl, fun D G x hx => ?_⟩
  simp only [Hypermap.fitp, Bool.and_eq_true] at hx ⊢
  exact ⟨hx.2.2.1, fun r' hr' => ⟨hx.1, hx.2.1, hr', hx.2.2.2⟩⟩

/-- Coq `updateP7f2`. -/
theorem updateP7f2 (h f1 : Prange) : PartUpdate.{u} (fun r => Part.cons7 h f1 r) .fan2 := by
  intro r p
  refine ⟨rfl, fun D G x hx => ?_⟩
  simp only [Hypermap.fitp, Bool.and_eq_true] at hx ⊢
  exact ⟨hx.2.2.2.1, fun r' hr' => ⟨hx.1, hx.2.1, hx.2.2.1, hr', hx.2.2.2.2⟩⟩

/-- Coq `updateP8h`. -/
theorem updateP8h (f1 f2 f3 : Prange) :
    PartUpdate.{u} (fun r => Part.cons8 r f1 f2 f3) .hat := by
  intro r p
  refine ⟨rfl, fun D G x hx => ?_⟩
  simp only [Hypermap.fitp, Bool.and_eq_true] at hx ⊢
  exact ⟨hx.2.1, fun r' hr' => ⟨hx.1, hr', hx.2.2⟩⟩

/-- Coq `updateP8f1`. -/
theorem updateP8f1 (h f2 f3 : Prange) :
    PartUpdate.{u} (fun r => Part.cons8 h r f2 f3) .fan1 := by
  intro r p
  refine ⟨rfl, fun D G x hx => ?_⟩
  simp only [Hypermap.fitp, Bool.and_eq_true] at hx ⊢
  exact ⟨hx.2.2.1, fun r' hr' => ⟨hx.1, hx.2.1, hr', hx.2.2.2⟩⟩

/-- Coq `updateP8f2`. -/
theorem updateP8f2 (h f1 f3 : Prange) :
    PartUpdate.{u} (fun r => Part.cons8 h f1 r f3) .fan2 := by
  intro r p
  refine ⟨rfl, fun D G x hx => ?_⟩
  simp only [Hypermap.fitp, Bool.and_eq_true] at hx ⊢
  exact ⟨hx.2.2.2.1, fun r' hr' => ⟨hx.1, hx.2.1, hx.2.2.1, hr', hx.2.2.2.2⟩⟩

/-- Coq `updateP8f3`. -/
theorem updateP8f3 (h f1 f2 : Prange) :
    PartUpdate.{u} (fun r => Part.cons8 h f1 f2 r) .fan3 := by
  intro r p
  refine ⟨rfl, fun D G x hx => ?_⟩
  simp only [Hypermap.fitp, Bool.and_eq_true] at hx ⊢
  exact ⟨hx.2.2.2.2.1, fun r' hr' => ⟨hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1, hr', hx.2.2.2.2.2⟩⟩

end FourColor
