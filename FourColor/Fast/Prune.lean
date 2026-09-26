/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Fast.RedPart

/-!
# Pruned quiz trees: certificate-guided `redpart`

Almost all the work of `redpart qt p` is spent trying the leaves (question triples) of the quiz
tree `qt` that do not fit (98% of the quiz matches fail).
But the soundness of `redpart` (`Hypermap.no_fit_redpart`) holds for *any* quiz tree none of
whose quizzes fits the map, and removing leaves from a quiz tree can only remove fits. So a
certificate for a `redpart` check is a *pruning mask* `m : QztMask` that keeps only the leaves
the check needs: the kernel evaluates `redpartFast (qztPrune qt m) p`, which is sound by
`no_fit_redpart_prune`:

* `QztMask`: for each leaf list of the tree, the leaves to keep, as skip counts; `QztMask.none`
  keeps no leaf of a subtree (its internal nodes are kept, so that the lookups of `redpart` and
  its test `qztProper` behave as in the full tree), and `QztMask.nil` removes a whole subtree
  (then the test `qztProper` of `redpart` fails on it, and the rotations of the search whose
  spoke arity selects that subtree are skipped).
* `qztPrune t m`: the tree `t` with only the leaves selected by `m` (structurally recursive,
  computable, evaluated lazily by the kernel: only the looked-up leaf lists are pruned).
* `Hypermap.qztFit_prune`: a quiz of `qztPrune t m` that fits is a quiz of `t` that fits.
* `Hypermap.no_fit_redpart_prune`: the soundness of `redpart` (or `redpartFast`) on a pruned
  tree: if `redpart (qztPrune qt m) p` then no dart fits `p` exactly, when no quiz of `qt` fits.

## Choosing the mask

Keep the *first fitting* leaf of every `redQztLeaf` call made by the check on the full tree
(`FourColor.Fast.PruneGen` computes this set natively). Then every `redQztLeaf` call of the check on
the pruned tree finds the same first fitting leaf (the kept leaves before it are leaves of the
full tree before it, which do not fit), so the check on the pruned tree makes exactly the same
calls with the same results, and succeeds. A mask can serve several checks: the union of their
kept leaves works for each of them, for the same reason.
-/

namespace FourColor

/-- A pruning mask for quiz trees (the certificate of a `redpart` check, see the module
docstring). -/
inductive QztMask : Type where
  /-- Keep no leaf in this subtree (its internal nodes are kept). -/
  | none
  /-- A leaf list: keep the leaves selected by the skip counts `skips` (skip `n₁` leaves, keep
  one, skip `n₂` leaves, keep one, ...). -/
  | leaves (skips : List ℕ)
  /-- An internal node (`QztNode` or `QztHubNode`): the masks of its four subtrees. -/
  | node (m1 m2 m3 m4 : QztMask)
  /-- Prune the whole subtree (to `QztNil`). -/
  | nil
  deriving DecidableEq, Repr, Inhabited

/-- The leaf list `t` without its first `n` leaves. -/
def qztDropLeaves : ℕ → QuizTree → QuizTree
  | n + 1, QztLeaf _ _ _ t => qztDropLeaves n t
  | _, t => t

/-- The leaves of the leaf list `t` selected by the skip counts `ns`. -/
def qztPruneLeaves : List ℕ → QuizTree → QuizTree
  | [], _ => QztNil
  | n :: ns, t =>
    match qztDropLeaves n t with
    | QztLeaf q1 q2 q3 t' => QztLeaf q1 q2 q3 (qztPruneLeaves ns t')
    | _ => QztNil

/-- The quiz tree `t` pruned by the mask `m`: its internal nodes are kept, and its leaf lists
are replaced by the sublists selected by `m`. -/
def qztPrune : QuizTree → QztMask → QuizTree
  | _, .nil => QztNil
  | QztNil, _ => QztNil
  | QztLeaf q1 q2 q3 t, .leaves ns => qztPruneLeaves ns (QztLeaf q1 q2 q3 t)
  | QztLeaf _ _ _ _, _ => QztNil
  | QztNode a b c d, .node ma mb mc md =>
    QztNode (qztPrune a ma) (qztPrune b mb) (qztPrune c mc) (qztPrune d md)
  | QztNode a b c d, _ =>
    QztNode (qztPrune a .none) (qztPrune b .none) (qztPrune c .none) (qztPrune d .none)
  | QztHubNode a b c d, .node ma mb mc md =>
    QztHubNode (qztPrune a ma) (qztPrune b mb) (qztPrune c mc) (qztPrune d md)
  | QztHubNode a b c d, _ =>
    QztHubNode (qztPrune a .none) (qztPrune b .none) (qztPrune c .none) (qztPrune d .none)

/-! ### Kernel-fast pruning -/

/-- Kernel-fast `qztDropLeaves`: `Nat.rec` on the count, then a `QuizTree.rec` with closed minor
premises. -/
noncomputable def qztDropLeavesFast (n : ℕ) (t : QuizTree) : QuizTree :=
  Nat.rec (motive := fun _ => QuizTree → QuizTree) (fun t => t)
    (fun _ ih t => QuizTree.rec (motive := fun _ => (QuizTree → QuizTree) → QuizTree)
      (fun _ => QztNil) (fun _ _ _ t _ ih => ih t)
      (fun a b c d _ _ _ _ _ => QztNode a b c d) (fun a b c d _ _ _ _ _ => QztHubNode a b c d)
      t ih) n t

/-- `qztDropLeavesFast` is `qztDropLeaves`. -/
theorem qztDropLeavesFast_eq (n : ℕ) (t : QuizTree) : qztDropLeavesFast n t = qztDropLeaves n t := by
  induction n generalizing t with
  | zero => cases t <;> rfl
  | succ n ih => cases t with
    | QztLeaf q1 q2 q3 t => exact ih t
    | _ => rfl

/-- Kernel-fast `qztPruneLeaves`. -/
noncomputable def qztPruneLeavesFast (ns : List ℕ) (t : QuizTree) : QuizTree :=
  List.rec (motive := fun _ => QuizTree → QuizTree) (fun _ => QztNil)
    (fun n _ ih t => QuizTree.rec (motive := fun _ => (QuizTree → QuizTree) → QuizTree)
      (fun _ => QztNil) (fun q1 q2 q3 t' _ ih => QztLeaf q1 q2 q3 (ih t'))
      (fun _ _ _ _ _ _ _ _ _ => QztNil) (fun _ _ _ _ _ _ _ _ _ => QztNil)
      (qztDropLeavesFast n t) ih) ns t

/-- `qztPruneLeavesFast` is `qztPruneLeaves`. -/
theorem qztPruneLeavesFast_eq (ns : List ℕ) (t : QuizTree) :
    qztPruneLeavesFast ns t = qztPruneLeaves ns t := by
  induction ns generalizing t with
  | nil => rfl
  | cons n ns ih =>
    show QuizTree.rec (motive := fun _ => (QuizTree → QuizTree) → QuizTree) _ _ _ _
      (qztDropLeavesFast n t) (qztPruneLeavesFast ns) = _
    rw [qztDropLeavesFast_eq, qztPruneLeaves]
    cases qztDropLeaves n t with
    | QztLeaf q1 q2 q3 t' => exact congrArg (QztLeaf q1 q2 q3) (ih t')
    | _ => rfl

/-- Kernel-fast `qztPrune`: `QuizTree.rec` on the tree, then `QztMask.rec` on the mask. -/
noncomputable def qztPruneFast (t : QuizTree) (m : QztMask) : QuizTree :=
  QuizTree.rec (motive := fun _ => QztMask → QuizTree)
    (fun _ => QztNil)
    (fun q1 q2 q3 t _ m => QztMask.rec (motive := fun _ => QuizTree) QztNil
      (fun ns => qztPruneLeavesFast ns (QztLeaf q1 q2 q3 t)) (fun _ _ _ _ _ _ _ _ => QztNil) QztNil
      m)
    (fun _ _ _ _ iha ihb ihc ihd m => QztMask.rec (motive := fun _ => QuizTree)
      (QztNode (iha .none) (ihb .none) (ihc .none) (ihd .none))
      (fun _ => QztNode (iha .none) (ihb .none) (ihc .none) (ihd .none))
      (fun ma mb mc md _ _ _ _ => QztNode (iha ma) (ihb mb) (ihc mc) (ihd md)) QztNil m)
    (fun _ _ _ _ iha ihb ihc ihd m => QztMask.rec (motive := fun _ => QuizTree)
      (QztHubNode (iha .none) (ihb .none) (ihc .none) (ihd .none))
      (fun _ => QztHubNode (iha .none) (ihb .none) (ihc .none) (ihd .none))
      (fun ma mb mc md _ _ _ _ => QztHubNode (iha ma) (ihb mb) (ihc mc) (ihd md)) QztNil m)
    t m

/-- `qztPruneFast` is `qztPrune`. -/
theorem qztPruneFast_eq (t : QuizTree) (m : QztMask) : qztPruneFast t m = qztPrune t m := by
  induction t generalizing m with
  | QztNil => cases m <;> rfl
  | QztLeaf q1 q2 q3 t _ =>
    cases m with
    | leaves ns => exact qztPruneLeavesFast_eq ns _
    | none => rfl
    | node => rfl
    | nil => rfl
  | QztNode a b c d iha ihb ihc ihd =>
    cases m with
    | node ma mb mc md =>
      show QztNode (qztPruneFast a ma) (qztPruneFast b mb) (qztPruneFast c mc)
        (qztPruneFast d md) = _
      rw [iha, ihb, ihc, ihd]; rfl
    | none =>
      show QztNode (qztPruneFast a .none) (qztPruneFast b .none) (qztPruneFast c .none)
        (qztPruneFast d .none) = _
      rw [iha, ihb, ihc, ihd]; rfl
    | leaves ns =>
      show QztNode (qztPruneFast a .none) (qztPruneFast b .none) (qztPruneFast c .none)
        (qztPruneFast d .none) = _
      rw [iha, ihb, ihc, ihd]; rfl
    | nil => rfl
  | QztHubNode a b c d iha ihb ihc ihd =>
    cases m with
    | node ma mb mc md =>
      show QztHubNode (qztPruneFast a ma) (qztPruneFast b mb) (qztPruneFast c mc)
        (qztPruneFast d md) = _
      rw [iha, ihb, ihc, ihd]; rfl
    | none =>
      show QztHubNode (qztPruneFast a .none) (qztPruneFast b .none) (qztPruneFast c .none)
        (qztPruneFast d .none) = _
      rw [iha, ihb, ihc, ihd]; rfl
    | leaves ns =>
      show QztHubNode (qztPruneFast a .none) (qztPruneFast b .none) (qztPruneFast c .none)
        (qztPruneFast d .none) = _
      rw [iha, ihb, ihc, ihd]; rfl
    | nil => rfl

/-- A pruned leaf list is a leaf list. -/
private theorem qztPruneLeaves_cases (ns : List ℕ) (t : QuizTree) :
    qztPruneLeaves ns t = QztNil ∨ ∃ q1 q2 q3 t', qztPruneLeaves ns t = QztLeaf q1 q2 q3 t' := by
  cases ns with
  | nil => exact Or.inl rfl
  | cons n ns =>
    simp only [qztPruneLeaves]
    split
    · exact Or.inr ⟨_, _, _, _, rfl⟩
    · exact Or.inl rfl

/-- Pruning by `QztMask.nil` gives the empty tree. -/
theorem qztPrune_nil (t : QuizTree) : qztPrune t .nil = QztNil := by
  cases t <;> rfl

/-- Looking up a pruned tree gives a pruned subtree. -/
theorem qztGet1_qztPrune (qa : Qarity) (t : QuizTree) (m : QztMask) :
    ∃ m', qztGet1 qa (qztPrune t m) = qztPrune (qztGet1 qa t) m' := by
  induction t generalizing m qa with
  | QztNil => exact ⟨.none, by cases m <;> cases qa <;> rfl⟩
  | QztLeaf q1 q2 q3 t _ =>
    refine ⟨.none, ?_⟩
    have hnil : qztGet1 qa (QztLeaf q1 q2 q3 t) = QztNil := by cases qa <;> rfl
    rw [hnil]
    cases m with
    | leaves ns =>
      rcases qztPruneLeaves_cases ns (QztLeaf q1 q2 q3 t) with h | ⟨a, b, c, t', h⟩ <;>
        simp only [qztPrune, h] <;> cases qa <;> rfl
    | none => cases qa <;> rfl
    | node => cases qa <;> rfl
    | nil => cases qa <;> rfl
  | QztNode a b c d _ _ _ _ =>
    cases m with
    | node ma mb mc md => cases qa <;> first | exact ⟨_, rfl⟩ | exact ⟨.none, rfl⟩
    | none => cases qa <;> exact ⟨.none, rfl⟩
    | leaves _ => cases qa <;> exact ⟨.none, rfl⟩
    | nil => exact ⟨.nil, by rw [qztPrune_nil, qztPrune_nil]; cases qa <;> rfl⟩
  | QztHubNode a b c d iha _ _ _ =>
    cases m with
    | node ma mb mc md =>
      cases qa <;> first | exact ⟨_, rfl⟩ | exact iha _ ma
    | none => cases qa <;> first | exact ⟨.none, rfl⟩ | exact iha _ .none
    | leaves _ => cases qa <;> first | exact ⟨.none, rfl⟩ | exact iha _ .none
    | nil => exact ⟨.nil, by rw [qztPrune_nil, qztPrune_nil]; cases qa <;> rfl⟩

/-- Looking up a pruned tree gives a pruned subtree (three levels). -/
theorem qztGet3_qztPrune (qa1 qa2 qa3 : Qarity) (t : QuizTree) (m : QztMask) :
    ∃ m', qztGet3 qa1 qa2 qa3 (qztPrune t m) = qztPrune (qztGet3 qa1 qa2 qa3 t) m' := by
  obtain ⟨m1, h1⟩ := qztGet1_qztPrune qa1 t m
  obtain ⟨m2, h2⟩ := qztGet1_qztPrune qa2 (qztGet1 qa1 t) m1
  obtain ⟨m3, h3⟩ := qztGet1_qztPrune qa3 (qztGet1 qa2 (qztGet1 qa1 t)) m2
  exact ⟨m3, by rw [qztGet3, qztGet2, h1, h2, h3]; rfl⟩

namespace Hypermap

universe u

variable {D : Type u} (G : Hypermap D) (x : D)

/-- Dropping leaves can only remove fits. -/
theorem qztFitl_dropLeaves (n : ℕ) (t : QuizTree) :
    G.QztFitl x (qztDropLeaves n t) → G.QztFitl x t := by
  induction n generalizing t with
  | zero => intro h; cases t <;> exact h
  | succ n ih =>
    intro h
    cases t with
    | QztLeaf q1 q2 q3 t => exact Or.inr (ih t h)
    | _ => exact h

/-- Pruning a leaf list can only remove fits. -/
theorem qztFitl_pruneLeaves (ns : List ℕ) (t : QuizTree) :
    G.QztFitl x (qztPruneLeaves ns t) → G.QztFitl x t := by
  induction ns generalizing t with
  | nil => intro h; exact h.elim
  | cons n ns ih =>
    intro h
    apply G.qztFitl_dropLeaves x n t
    simp only [qztPruneLeaves] at h
    split at h
    · rename_i q1 q2 q3 t' heq
      rw [heq]
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (ih t' h)
    · exact h.elim

/-- Pruning a quiz tree can only remove fits (of leaf lists). -/
theorem qztFitl_prune (t : QuizTree) (m : QztMask) :
    G.QztFitl x (qztPrune t m) → G.QztFitl x t := by
  intro h
  cases t with
  | QztNil => cases m <;> exact h
  | QztLeaf q1 q2 q3 t =>
    cases m with
    | leaves ns => exact G.qztFitl_pruneLeaves x ns _ h
    | none => exact h.elim
    | node => exact h.elim
    | nil => exact h.elim
  | QztNode => cases m <;> exact h.elim
  | QztHubNode => cases m <;> exact h.elim

/-- Pruning a quiz tree can only remove fits. -/
theorem qztFit_prune (t : QuizTree) (m : QztMask) : G.QztFit x (qztPrune t m) → G.QztFit x t := by
  rintro ⟨ha, hl⟩
  refine ⟨ha, ?_⟩
  obtain ⟨m', h⟩ := qztGet3_qztPrune (qarityOfNat (G.arity x)) (qarityOfNat (G.arity (G.node x)))
    (qarityOfNat (G.arity (G.node (G.node x)))) t m
  rw [h] at hl
  exact G.qztFitl_prune x _ m' hl

variable {G}

/-- The soundness of `redpart` on a pruned quiz tree: in a plain cubic pentagonal map in which no
quiz of `qt` fits, if `redpart (qztPrune qt m) p` succeeds then no dart fits `p` exactly. -/
theorem no_fit_redpart_prune [Finite D] (geoG : G.PlainCubicPentagonal) {qt : QuizTree}
    (fit'qt : ∀ y : D, ¬ G.QztFit y qt) (m : QztMask) (p : Part)
    (hp : redpart (qztPrune qt m) p = true) (x : D) : G.exactFitp x p = false :=
  no_fit_redpart geoG (fun y hy => fit'qt y (G.qztFit_prune y qt m hy)) p hp x

/-- The soundness of `redpartFast` on a pruned quiz tree (see `no_fit_redpart_prune`). -/
theorem no_fit_redpartFast_prune [Finite D] (geoG : G.PlainCubicPentagonal) {qt : QuizTree}
    (fit'qt : ∀ y : D, ¬ G.QztFit y qt) (m : QztMask) (p : Part)
    (hp : redpartFast (qztPrune qt m) p = true) (x : D) : G.exactFitp x p = false :=
  no_fit_redpart_prune geoG fit'qt m p (by rwa [← redpartFast_eq]) x

/-- The soundness of `redpartFast` on a quiz tree pruned by `qztPruneFast` (see
`no_fit_redpart_prune`). -/
theorem no_fit_redpartFast_pruneFast [Finite D] (geoG : G.PlainCubicPentagonal) {qt : QuizTree}
    (fit'qt : ∀ y : D, ¬ G.QztFit y qt) (m : QztMask) (p : Part)
    (hp : redpartFast (qztPruneFast qt m) p = true) (x : D) : G.exactFitp x p = false :=
  no_fit_redpartFast_prune geoG fit'qt m p (by rwa [← qztPruneFast_eq]) x

end Hypermap

end FourColor
