/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.QuizTree

/-!
# Checking the quizzes and building the quiz tree (no data)

The kernel check of `theQuizTree = cfquizTree theConfigs` (`FourColor.QuizData.Tree`) is split in
two: the quiz `cfquiz cf` of each configuration is checked against a literal, one configuration
per declaration (`FourColor.QuizData.Quizzes1` to `Quizzes4`), and the tree is then built from the
literal quizzes and compared with the literal tree, in one declaration. This file provides the
functions and lemmas for both parts. The functions evaluated by the kernel are written with
recursors (`QuizTree.rec`, `Question.rec`, `List.rec`, `casesOn`), which the kernel reduces
about three times faster than compiled `match`es, and are `noncomputable`;
each one is proved equal to its specification.

## Checking the quizzes

Most of the kernel cost of `cfquiz cf` is its radius test `cpradius2 cp (cpksize cp)`, which tries
the kernel faces `k - 1`, `k - 2`, ... in turn as the center (up to 11 tries). The check is given
the successful face as a certificate:

* `cpradius2At cp i`: one try of `cpradius2`, with the face `i` as the center
  (`cpradius2_succ`; `cpradius2_of_at`: if `cpradius2At cp i` and `i < k`, then `cpradius2 cp k`).
* `cfquizCheck cf i qz`: `i < cpksize cp`, `cpradius2At cp i`, and the quiz construction
  `cfquizRec` gives `qz` (`cfquiz_eq_of_cfquizCheck`: then `cfquiz cf = qz`).

## Building the tree

* `qztBuild qt cfs qzs`: `cfquizTreeRec qt cfs`, with the quizzes `qzs` of `cfs` given
  (`cfquizTreeRec_eq_qztBuild`: `cfquizTreeRec qt cfs = qztBuild qt cfs (cfs.map cfquiz)`).
* `qztBuild` stores the quizzes with *strict* versions of the store functions of
  `FourColor.QuizTree` (`qztPut1S`, `qztPut3S`, `qztPut3rotS`, `qztPutS`, `storeQzS`,
  `storeCfQzS`, each proved equal to the original). The originals are lazy for the kernel:
  `qztPut1 Qa5 qr (QztNode t5 t6 t7 t8)` reduces to `QztNode (qr t5) t6 t7 t8` without reducing
  `qr t5`, so storing the 3361 triples one after the other would pile up thousands of nested
  unevaluated `qztPut1` steps in the branches of the tree, which Palomar's checkers nanoda and
  con-ron do not accept. The strict versions
  reduce each updated branch to a constructor (`qztForce`) before rebuilding its parent, and
  `qztBuild` matches the tree after each configuration, so every intermediate tree is a
  constructor term.
* `qarityBeq`, `questionBeq`, `quizBeq`, `quizTreeBeq`: Boolean equality tests, with
  `eq_of_qarityBeq`, `eq_of_questionBeq`, `eq_of_quizBeq` and `eq_of_quizTreeBeq`.
-/

namespace FourColor.QuizData

/-! ### Boolean equality -/

/-- `x && y`, as a recursor. -/
@[reducible] def band (x y : Bool) : Bool := Bool.casesOn (motive := fun _ => Bool) x false y

theorem band_eq_true {x y : Bool} : band x y = true ↔ x = true ∧ y = true := by
  cases x <;> simp [band]

/-- Boolean equality of qarities. -/
def qarityBeq (a b : Qarity) : Bool := Nat.beq (natOfQarity a) (natOfQarity b)

theorem eq_of_qarityBeq {a b : Qarity} (h : qarityBeq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | simp [qarityBeq, natOfQarity] at h

/-- Boolean equality of questions. -/
noncomputable def questionBeq (q : Question) : Question → Bool :=
  Question.rec (motive := fun _ => Question → Bool)
    (fun q' => Question.casesOn (motive := fun _ => Bool) q' true (fun _ => false)
      (fun _ _ => false) (fun _ _ => false) (fun _ _ _ => false) (fun _ _ => false)
      (fun _ _ => false))
    (fun a q' => Question.casesOn (motive := fun _ => Bool) q' false (fun b => qarityBeq a b)
      (fun _ _ => false) (fun _ _ => false) (fun _ _ _ => false) (fun _ _ => false)
      (fun _ _ => false))
    (fun a _ ih q' => Question.casesOn (motive := fun _ => Bool) q' false (fun _ => false)
      (fun b q'' => band (qarityBeq a b) (ih q'')) (fun _ _ => false) (fun _ _ _ => false)
      (fun _ _ => false) (fun _ _ => false))
    (fun a _ ih q' => Question.casesOn (motive := fun _ => Bool) q' false (fun _ => false)
      (fun _ _ => false) (fun b q'' => band (qarityBeq a b) (ih q'')) (fun _ _ _ => false)
      (fun _ _ => false) (fun _ _ => false))
    (fun a _ _ ihl ihr q' => Question.casesOn (motive := fun _ => Bool) q' false (fun _ => false)
      (fun _ _ => false) (fun _ _ => false)
      (fun b ql qr => band (qarityBeq a b) (band (ihl ql) (ihr qr)))
      (fun _ _ => false) (fun _ _ => false))
    (fun a _ ih q' => Question.casesOn (motive := fun _ => Bool) q' false (fun _ => false)
      (fun _ _ => false) (fun _ _ => false) (fun _ _ _ => false)
      (fun b q'' => band (qarityBeq a b) (ih q'')) (fun _ _ => false))
    (fun a _ ih q' => Question.casesOn (motive := fun _ => Bool) q' false (fun _ => false)
      (fun _ _ => false) (fun _ _ => false) (fun _ _ _ => false) (fun _ _ => false)
      (fun b q'' => band (qarityBeq a b) (ih q'')))
    q

theorem eq_of_questionBeq {q q' : Question} (h : questionBeq q q' = true) : q = q' := by
  induction q generalizing q' with
  | Qask0 => cases q' <;> first | rfl | exact absurd h Bool.false_ne_true
  | Qask1 a =>
    cases q' <;> first | exact absurd h Bool.false_ne_true | skip
    case Qask1 b => exact congrArg _ (eq_of_qarityBeq h)
  | QaskL a q ih =>
    cases q' <;> first | exact absurd h Bool.false_ne_true | skip
    case QaskL b q' =>
      obtain ⟨h1, h2⟩ := band_eq_true.1 (h : band (qarityBeq a b) (questionBeq q q') = true)
      rw [eq_of_qarityBeq h1, ih h2]
  | QaskR a q ih =>
    cases q' <;> first | exact absurd h Bool.false_ne_true | skip
    case QaskR b q' =>
      obtain ⟨h1, h2⟩ := band_eq_true.1 (h : band (qarityBeq a b) (questionBeq q q') = true)
      rw [eq_of_qarityBeq h1, ih h2]
  | QaskLR a ql qr ihl ihr =>
    cases q' <;> first | exact absurd h Bool.false_ne_true | skip
    case QaskLR b ql' qr' =>
      obtain ⟨h1, h2⟩ := band_eq_true.1
        (h : band (qarityBeq a b) (band (questionBeq ql ql') (questionBeq qr qr')) = true)
      obtain ⟨h2, h3⟩ := band_eq_true.1 h2
      rw [eq_of_qarityBeq h1, ihl h2, ihr h3]
  | QaskLL a q ih =>
    cases q' <;> first | exact absurd h Bool.false_ne_true | skip
    case QaskLL b q' =>
      obtain ⟨h1, h2⟩ := band_eq_true.1 (h : band (qarityBeq a b) (questionBeq q q') = true)
      rw [eq_of_qarityBeq h1, ih h2]
  | QaskRR a q ih =>
    cases q' <;> first | exact absurd h Bool.false_ne_true | skip
    case QaskRR b q' =>
      obtain ⟨h1, h2⟩ := band_eq_true.1 (h : band (qarityBeq a b) (questionBeq q q') = true)
      rw [eq_of_qarityBeq h1, ih h2]

/-- Boolean equality of quizzes. -/
noncomputable def quizBeq (qz qz' : Quiz) : Bool :=
  band (questionBeq qz.q0 qz'.q0) (questionBeq qz.q1 qz'.q1)

theorem eq_of_quizBeq {qz qz' : Quiz} (h : quizBeq qz qz' = true) : qz = qz' := by
  obtain ⟨q0, q1⟩ := qz
  obtain ⟨q0', q1'⟩ := qz'
  obtain ⟨h1, h2⟩ := band_eq_true.1 h
  have h1 : questionBeq q0 q0' = true := h1
  have h2 : questionBeq q1 q1' = true := h2
  rw [eq_of_questionBeq h1, eq_of_questionBeq h2]

/-- Boolean equality of quiz trees (the rest of a leaf list is compared last, so that long leaf
lists are compared by a loop). -/
noncomputable def quizTreeBeq (t : QuizTree) : QuizTree → Bool :=
  QuizTree.rec (motive := fun _ => QuizTree → Bool)
    (fun t' => QuizTree.casesOn (motive := fun _ => Bool) t' true (fun _ _ _ _ => false)
      (fun _ _ _ _ => false) (fun _ _ _ _ => false))
    (fun q1 q2 q3 _ ih t' => QuizTree.casesOn (motive := fun _ => Bool) t' false
      (fun q1' q2' q3' t'' =>
        band (questionBeq q1 q1') (band (questionBeq q2 q2') (band (questionBeq q3 q3') (ih t''))))
      (fun _ _ _ _ => false) (fun _ _ _ _ => false))
    (fun _ _ _ _ ih5 ih6 ih7 ih8 t' => QuizTree.casesOn (motive := fun _ => Bool) t' false
      (fun _ _ _ _ => false)
      (fun t5 t6 t7 t8 => band (ih5 t5) (band (ih6 t6) (band (ih7 t7) (ih8 t8))))
      (fun _ _ _ _ => false))
    (fun _ _ _ _ ih58 ih9 ih10 ih11 t' => QuizTree.casesOn (motive := fun _ => Bool) t' false
      (fun _ _ _ _ => false) (fun _ _ _ _ => false)
      (fun t58 t9 t10 t11 => band (ih58 t58) (band (ih9 t9) (band (ih10 t10) (ih11 t11)))))
    t

theorem eq_of_quizTreeBeq {t t' : QuizTree} (h : quizTreeBeq t t' = true) : t = t' := by
  induction t generalizing t' with
  | QztNil => cases t' <;> first | rfl | exact absurd h Bool.false_ne_true
  | QztLeaf q1 q2 q3 t ih =>
    cases t' <;> first | exact absurd h Bool.false_ne_true | skip
    case QztLeaf q1' q2' q3' t' =>
      obtain ⟨h1, h2⟩ := band_eq_true.1 (h : band (questionBeq q1 q1')
        (band (questionBeq q2 q2') (band (questionBeq q3 q3') (quizTreeBeq t t'))) = true)
      obtain ⟨h2, h3⟩ := band_eq_true.1 h2
      obtain ⟨h3, h4⟩ := band_eq_true.1 h3
      rw [eq_of_questionBeq h1, eq_of_questionBeq h2, eq_of_questionBeq h3, ih h4]
  | QztNode t5 t6 t7 t8 ih5 ih6 ih7 ih8 =>
    cases t' <;> first | exact absurd h Bool.false_ne_true | skip
    case QztNode t5' t6' t7' t8' =>
      obtain ⟨h1, h2⟩ := band_eq_true.1 (h : band (quizTreeBeq t5 t5')
        (band (quizTreeBeq t6 t6') (band (quizTreeBeq t7 t7') (quizTreeBeq t8 t8'))) = true)
      obtain ⟨h2, h3⟩ := band_eq_true.1 h2
      obtain ⟨h3, h4⟩ := band_eq_true.1 h3
      rw [ih5 h1, ih6 h2, ih7 h3, ih8 h4]
  | QztHubNode t58 t9 t10 t11 ih58 ih9 ih10 ih11 =>
    cases t' <;> first | exact absurd h Bool.false_ne_true | skip
    case QztHubNode t58' t9' t10' t11' =>
      obtain ⟨h1, h2⟩ := band_eq_true.1 (h : band (quizTreeBeq t58 t58')
        (band (quizTreeBeq t9 t9') (band (quizTreeBeq t10 t10') (quizTreeBeq t11 t11'))) = true)
      obtain ⟨h2, h3⟩ := band_eq_true.1 h2
      obtain ⟨h3, h4⟩ := band_eq_true.1 h3
      rw [ih58 h1, ih9 h2, ih10 h3, ih11 h4]

/-! ### Checking the quizzes, with radius certificates -/

/-- One try of `cpradius2 cp`: the kernel face `i` of `cpmap cp` is at distance at most 2 from
every kernel face (`cpradius2 cp (i + 1)` is `cpradius2At cp i || cpradius2 cp i`). -/
def cpradius2At (cp : Cprog) (i : ℕ) : Bool :=
  let cm0 := cfmask1 cp i
  match cm0 with
  | ⟨mr1, _⟩ =>
    match cpadj cm0 cp with
    | ⟨_, mk1⟩ =>
      match cpadj ⟨mr1, mk1⟩ cp with
      | ⟨_, mk2⟩ => mk2.all id

theorem cpradius2_succ (cp : Cprog) (i : ℕ) :
    cpradius2 cp (i + 1) = (cpradius2At cp i || cpradius2 cp i) := by
  simp only [cpradius2, cpradius2At]
  split <;> simp_all

theorem cpradius2_of_at {cp : Cprog} {i k : ℕ} (hi : i < k) (h : cpradius2At cp i = true) :
    cpradius2 cp k = true := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [cpradius2_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · simp [ih hi]
    · simp [h]

/-- The check of `cfquiz cf = qz`, given the certificate `i` for the radius test: `i` is a
kernel face, `cpradius2At cp i` holds, and the quiz construction gives `qz`. -/
noncomputable def cfquizCheck (cf : Config) (i : ℕ) (qz : Quiz) : Bool :=
  band (Nat.blt i (cpksize cf.cfprog)) (band (cpradius2At cf.cfprog i)
    (quizBeq (cfquizRec (List.replicate (cprsize cf.cfprog) ⟨false, 0, Qask0⟩) cf.cfprog) qz))

theorem cfquiz_eq_of_cfquizCheck {cf : Config} {i : ℕ} {qz : Quiz}
    (h : cfquizCheck cf i qz = true) : cfquiz cf = qz := by
  obtain ⟨hi, h⟩ := band_eq_true.1 h
  obtain ⟨hr, hq⟩ := band_eq_true.1 h
  simp only [cfquiz, cpradius2_of_at (Nat.blt_eq.mp hi) hr, ite_true]
  exact eq_of_quizBeq hq

/-! ### Strict store operations -/

/-- Reduce `t` to a constructor before passing it to `k` (`qztForce t k = k t`). -/
noncomputable def qztForce (t : QuizTree) (k : QuizTree → QuizTree) : QuizTree :=
  QuizTree.casesOn (motive := fun _ => QuizTree) t (k QztNil)
    (fun q1 q2 q3 t' => k (QztLeaf q1 q2 q3 t')) (fun t5 t6 t7 t8 => k (QztNode t5 t6 t7 t8))
    (fun t58 t9 t10 t11 => k (QztHubNode t58 t9 t10 t11))

theorem qztForce_eq (t : QuizTree) (k : QuizTree → QuizTree) : qztForce t k = k t := by
  cases t <;> rfl

/-- Strict `qztPut1`: the updated branch is reduced to a constructor before the node is
rebuilt. -/
noncomputable def qztPut1S (qa : Qarity) (qr : QuizTree → QuizTree) (t : QuizTree) : QuizTree :=
  QuizTree.rec (motive := fun _ => QuizTree)
    QztNil
    (fun q1 q2 q3 t' _ => QztLeaf q1 q2 q3 t')
    (fun t5 t6 t7 t8 _ _ _ _ =>
      Qarity.casesOn (motive := fun _ => QuizTree) qa
        (qztForce (qr t5) fun c => QztNode c t6 t7 t8)
        (qztForce (qr t6) fun c => QztNode t5 c t7 t8)
        (qztForce (qr t7) fun c => QztNode t5 t6 c t8)
        (qztForce (qr t8) fun c => QztNode t5 t6 t7 c)
        (QztNode t5 t6 t7 t8) (QztNode t5 t6 t7 t8) (QztNode t5 t6 t7 t8))
    (fun t58 t9 t10 t11 r58 _ _ _ =>
      Qarity.casesOn (motive := fun _ => QuizTree) qa
        (qztForce r58 fun c => QztHubNode c t9 t10 t11)
        (qztForce r58 fun c => QztHubNode c t9 t10 t11)
        (qztForce r58 fun c => QztHubNode c t9 t10 t11)
        (qztForce r58 fun c => QztHubNode c t9 t10 t11)
        (qztForce (qr t9) fun c => QztHubNode t58 c t10 t11)
        (qztForce (qr t10) fun c => QztHubNode t58 t9 c t11)
        (qztForce (qr t11) fun c => QztHubNode t58 t9 t10 c))
    t

theorem qztPut1S_eq : qztPut1S = qztPut1 := by
  funext qa qr t
  induction t with
  | QztNil => cases qa <;> rfl
  | QztLeaf q1 q2 q3 t _ => cases qa <;> rfl
  | QztNode t5 t6 t7 t8 _ _ _ _ => cases qa <;> simp [qztPut1S, qztPut1, qztForce_eq]
  | QztHubNode t58 t9 t10 t11 ih _ _ _ =>
    have e : qztPut1S qa qr (QztHubNode t58 t9 t10 t11) =
        Qarity.casesOn (motive := fun _ => QuizTree) qa
          (qztForce (qztPut1S qa qr t58) fun c => QztHubNode c t9 t10 t11)
          (qztForce (qztPut1S qa qr t58) fun c => QztHubNode c t9 t10 t11)
          (qztForce (qztPut1S qa qr t58) fun c => QztHubNode c t9 t10 t11)
          (qztForce (qztPut1S qa qr t58) fun c => QztHubNode c t9 t10 t11)
          (qztForce (qr t9) fun c => QztHubNode t58 c t10 t11)
          (qztForce (qr t10) fun c => QztHubNode t58 t9 c t11)
          (qztForce (qr t11) fun c => QztHubNode t58 t9 t10 c) := rfl
    rw [e]
    cases qa <;> simp only [qztForce_eq, ih] <;> simp [qztPut1]

/-- Strict `qztPut3`. -/
noncomputable def qztPut3S (qa1 qa2 qa3 : Qarity) (q1 q2 q3 : Question) : QuizTree → QuizTree :=
  qztPut1S qa1 (qztPut1S qa2 (qztPut1S qa3 (QztLeaf q1 q2 q3)))

theorem qztPut3S_eq : qztPut3S = qztPut3 := by
  funext qa1 qa2 qa3 q1 q2 q3
  simp only [qztPut3S, qztPut3, qztPut1S_eq]

/-- Strict `qztPut3rot`. -/
noncomputable def qztPut3rotS (qa1 qa2 qa3 : Qarity) (q1 q2 q3 : Question) (t : QuizTree) :
    QuizTree :=
  qztPut3S qa1 qa2 qa3 q1 q2 q3
    (qztPut3S qa2 qa3 qa1 q2 q3 q1 (qztPut3S qa3 qa1 qa2 q3 q1 q2 t))

theorem qztPut3rotS_eq : qztPut3rotS = qztPut3rot := by
  funext qa1 qa2 qa3 q1 q2 q3 t
  simp only [qztPut3rotS, qztPut3rot, qztPut3S_eq]

/-- Strict `qztPut` (the test `8 < qa1` is a case analysis on `qa1`). -/
noncomputable def qztPutS (qa1 qa2 qa3 : Qarity) (q1 q2 q3 : Question) : QuizTree → QuizTree :=
  Qarity.casesOn (motive := fun _ => QuizTree → QuizTree) qa1
    (qztPut3rotS qa1 qa2 qa3 q1 q2 q3) (qztPut3rotS qa1 qa2 qa3 q1 q2 q3)
    (qztPut3rotS qa1 qa2 qa3 q1 q2 q3) (qztPut3rotS qa1 qa2 qa3 q1 q2 q3)
    (qztPut3S qa1 qa2 qa3 q1 q2 q3) (qztPut3S qa1 qa2 qa3 q1 q2 q3)
    (qztPut3S qa1 qa2 qa3 q1 q2 q3)

theorem qztPutS_eq : qztPutS = qztPut := by
  funext qa1 qa2 qa3 q1 q2 q3
  cases qa1 <;> simp [qztPutS, qztPut, natOfQarity, qztPut3S_eq, qztPut3rotS_eq]

/-- `normq q`, in continuation-passing style: `k qa ql qr` if `normq q` is `QaskLR qa ql qr`,
and `d` otherwise. -/
noncomputable def normqLR {β : Sort _} (q : Question) (k : Qarity → Question → Question → β)
    (d : β) : β :=
  Question.casesOn (motive := fun _ => β) q d (fun qa => k qa Qask0 Qask0)
    (fun qa ql => k qa ql Qask0) (fun qa qr => k qa Qask0 qr) (fun qa ql qr => k qa ql qr)
    (fun _ _ => d) (fun _ _ => d)

/-- `storeQz ⟨QaskR qa1 q1, QaskR qa2 q2⟩`, strict. -/
noncomputable def storeQzAux (qa1 : Qarity) (q1 : Question) (qa2 : Qarity) (q2 : Question) :
    QuizTree → QuizTree :=
  normqLR q1
    (fun qa1r q1l q1r => normqLR q2
      (fun qa2r q2l q2r =>
        Bool.casesOn (motive := fun _ => QuizTree → QuizTree) (Nat.blt qa1r qa2r)
          (qztPutS qa1 qa2r qa2 q1 q2r q2l) (qztPutS qa1 qa2 qa1r q1l q2 q1r))
      (qztPutS qa1 qa2 qa1r q1l q2 q1r))
    (normqLR q2 (fun qa2r q2l q2r => qztPutS qa1 qa2r qa2 q1 q2r q2l) fun t => t)

/-- Strict `storeQz`. -/
noncomputable def storeQzS (qz : Quiz) : QuizTree → QuizTree :=
  Quiz.casesOn (motive := fun _ => QuizTree → QuizTree) qz fun q0 q1 =>
    Question.casesOn (motive := fun _ => QuizTree → QuizTree) q0 (fun t => t) (fun _ t => t)
      (fun _ _ t => t)
      (fun qa1 q1' => Question.casesOn (motive := fun _ => QuizTree → QuizTree) q1 (fun t => t)
        (fun _ t => t) (fun _ _ t => t) (fun qa2 q2' => storeQzAux qa1 q1' qa2 q2')
        (fun _ _ _ t => t) (fun _ _ t => t) (fun _ _ t => t))
      (fun _ _ _ t => t) (fun _ _ t => t) (fun _ _ t => t)

private theorem boolCasesOn_blt {α : Sort _} (a b : ℕ) (x y : α) :
    Bool.casesOn (motive := fun _ => α) (Nat.blt a b) y x = if a < b then x else y := by
  by_cases hab : a < b
  · rw [Nat.blt_eq.mpr hab]
    simp [hab]
  · rw [show Nat.blt a b = false from Bool.eq_false_iff.mpr (mt Nat.blt_eq.mp hab)]
    simp [hab]

theorem storeQzS_eq : storeQzS = storeQz := by
  funext qz
  obtain ⟨q0, q1⟩ := qz
  cases q0 with
  | QaskR qa1 q1' =>
    cases q1 with
    | QaskR qa2 q2' =>
      show storeQzAux qa1 q1' qa2 q2' = _
      cases q1' <;> cases q2' <;>
        simp only [storeQzAux, normqLR, storeQz, normq, qztPutS_eq, boolCasesOn_blt]
    | _ => rfl
  | _ => rfl

/-- Strict `storeCfQz`. -/
noncomputable def storeCfQzS (qz : Quiz) (sym : Bool) (t : QuizTree) : QuizTree :=
  storeQzS qz (Bool.casesOn (motive := fun _ => QuizTree) sym (storeQzS (flipqz qz) t) t)

theorem storeCfQzS_eq : storeCfQzS = storeCfQz := by
  funext qz sym t
  cases sym <;> simp [storeCfQzS, storeCfQz, storeQzS_eq]

/-! ### Building the tree from the quizzes -/

/-- `cfquizTreeRec qt cfs`, with the quizzes `qzs` of the configurations `cfs` given (strict:
the tree is matched after each configuration). -/
noncomputable def qztBuild (qt : QuizTree) (cfs : List Config) (qzs : List Quiz) : QuizTree :=
  List.rec (motive := fun _ => QuizTree → List Quiz → QuizTree) (fun qt _ => qt)
    (fun cf _ ih qt qzs => List.casesOn (motive := fun _ => QuizTree) qzs qt fun qz qzs' =>
      QuizTree.casesOn (motive := fun _ => QuizTree) (storeCfQzS qz cf.cfsym qt) QztNil
        (fun _ _ _ _ => QztNil) (fun _ _ _ _ => QztNil)
        (fun t58 t9 t10 t11 => ih (QztHubNode t58 t9 t10 t11) qzs'))
    cfs qt qzs

theorem cfquizTreeRec_eq_qztBuild (qt : QuizTree) (cfs : List Config) :
    cfquizTreeRec qt cfs = qztBuild qt cfs (cfs.map cfquiz) := by
  induction cfs generalizing qt with
  | nil => rfl
  | cons cf cfs ih =>
    have e : qztBuild qt (cf :: cfs) ((cf :: cfs).map cfquiz) =
        QuizTree.casesOn (motive := fun _ => QuizTree) (storeCfQzS (cfquiz cf) cf.cfsym qt)
          QztNil (fun _ _ _ _ => QztNil) (fun _ _ _ _ => QztNil)
          (fun t58 t9 t10 t11 => qztBuild (QztHubNode t58 t9 t10 t11) cfs (cfs.map cfquiz)) :=
      rfl
    rw [e, cfquizTreeRec, storeCfQzS_eq]
    generalize storeCfQz (cfquiz cf) cf.cfsym qt = t
    cases t with
    | QztHubNode t58 t9 t10 t11 => exact ih _
    | _ => rfl

end FourColor.QuizData
