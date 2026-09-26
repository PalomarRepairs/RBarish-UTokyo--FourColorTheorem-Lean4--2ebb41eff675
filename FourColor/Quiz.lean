/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Coloring
import Mathlib.Data.List.GetD

/-!
# Quizzes  (port of `quiz.v`)

A quiz is a pair of binary trees - questions - that covers the inner regions of a configuration
and stores their arities. The embedding lemmas allow us to use questions to actually test for an
isomorphic embedding of the configuration in a minimal uncolorable cubic map. We define:

* `Qarity`          : an explicit enumeration of the possible face arities in a configuration
  (`QaN`, with `5 ≤ N ≤ 11`); a `Qarity` coerces to `ℕ` (Coq `nat_of_qarity`, here
  `natOfQarity`).
* `qarityOfNat n`   : the qarity with value `n : ℕ`, defaulting to `Qa11`.
* `Question`        : the type of embedding test trees, with leaves `Qask0` (no check) and
  `Qask1 qa` (check arity `qa`), unary nodes `QaskD qa q`, which check arity `qa` then do a
  `qstepD` move in the hypermap before checking recursively `q : Question`, with `D` in `{L, R}`,
  unary `QaskDD qa q` nodes that do a `qstepD` move BEFORE doing a `QaskD qa q` check, and binary
  nodes `QaskLR qa ql qr` which recurse twice, after `qstepL` and `qstepR` moves, respectively.
* `G.qstepL x`      : the left move at a cubic hypermap node (`= node (edge (node x))`).
* `G.qstepR x`      : the right move at a cubic hypermap node (`= node (edge x)`).
* `isQaskR q`       : `q` is a `QaskR` node.
* `flatq q`         : the list of the qarities occurring in `q`, collected in prefix order.
* `flipq q`         : the mirror image of `q`, with `L` and `R` exchanged.
* `G.walkq x q`     : the sequence of darts visited while testing `q` at `x`, in prefix order.
  The first dart of the sequence is usually `x`, except that the sequence for `Qask0` is empty,
  the one for `QaskRR` starts with `qstepR x`, and the one for `QaskLL` with
  `face⁻¹ (qstepL x) = edge (node (qstepL x))` (the additional face shift ensures the edge
  closure of the traversal stays within the configuration kernel, while not affecting the outcome
  of arity tests).
* `G.fitq x q`      : `q` fits at `x`: the arities in `walkq x q` match those in `flatq q`.
* `Quiz`            : the type of embedding tests, consisting of a pair of `Question`s that test
  for a preembedding starting from the initial edge of the configuration construction program
  (see `cfmap.v`); the Coq constructor `Quiz q0 q1` is `Quiz.mk q0 q1`.
* `isQuizR qz`      : `qz` consists of two `QaskR` questions.
* `flatqz qz`       : the list of the qarities occurring in the questions of `qz`.
* `flipqz qz`       : the mirror image of `qz`, with `L` and `R` exchanged.
* `G.walkqz x qz`   : the sequence of darts visited while testing `qz` at `x`.
* `G.fitqz x qz`    : `qz` fits at `x`: the arities in `walkqz x qz` match `flatqz qz`.
* `Gc.ValidQuiz rc x0c qz` : `qz` tests for the configuration with perimeter `rc`, at the initial
  dart `x0c`: `qz` satisfies `isQuizR`, fits at `x0c`, and `walkqz x0c qz` is a transversal of
  the faces in `kernel rc` (Coq `valid_quiz`).
* `embedqz Gm Gc x0m x0c qz` : a preembedding of `kernel rc` into a map `Gm` that maps `x0c` to
  `x0m`, assuming `qz` tests for `kernel rc` at `x0c` and fits `Gm` at `x0m`
  (`quiz_preembedding`).

## Porting notes

* The quiz data (`Qarity`, `Question`, `Quiz`) and the functions on it (`natOfQarity`,
  `qarityOfNat`, `isQaskR`, `flatq`, `flipq`, `isQuizR`, `flatqz`, `flipqz`) are first-order and
  structurally recursive, so they reduce in the kernel. The constructor names are Coq's.
* `fitq` and `fitqz` are the Coq boolean tests `flatq q == map arity (walkq x q)`. Since `arity`
  (`order face`) is not computable here, they are the `Prop`s `flatq q = (walkq x q).map arity`
  (they are only ever applied to abstract hypermaps), and `fitq_cat` and `fitqz_flip` are `↔`
  statements.
* `valid_quiz`, a Coq `[/\ _, _, _ & _]` conjunction, is the structure `ValidQuiz` with fields
  `quizR`, `fit`, `simple` and `fband_eq`; `fband s0c =i kernel rc` is the set equality
  `fband s0c = kernel rc`.
* In `embedqz`, math-comp's `find (cface x) s`, `nth x0 s i`, `iter n f x` and `findex f x y`
  become `s.findIdx fun y => decide (cface x y)` (with classical decidability), `s.getD i x0`,
  `f^[n] x`, and a private `findex f x y := (orbit f x).idxOf y`.
* The Coq section-local lemmas `Dhx0`, `Dhs0` and `Dhex0` are the private theorems
  `embedqz_x0c`, `embedqz_nth` and `embedqz_edge_x0c`; the proof-local lemmas `hc_walk`,
  `ccRfband` and `ccRwalk` are `have`s inside the proofs, as in Coq.
-/

namespace FourColor

open Function

/-! ### Question arities -/

/-- Coq `qarity`: an explicit enumeration of the possible face arities in a configuration,
`QaN` for `5 ≤ N ≤ 11` (in fact `9`, `10` and `11` only occur at the hub). -/
inductive Qarity : Type where
  /-- Coq `Qa5`. -/
  | Qa5
  /-- Coq `Qa6`. -/
  | Qa6
  /-- Coq `Qa7`. -/
  | Qa7
  /-- Coq `Qa8`. -/
  | Qa8
  /-- Coq `Qa9`. -/
  | Qa9
  /-- Coq `Qa10`. -/
  | Qa10
  /-- Coq `Qa11`. -/
  | Qa11
  deriving DecidableEq, Repr, Inhabited

export Qarity (Qa5 Qa6 Qa7 Qa8 Qa9 Qa10 Qa11)

/-- Coq `nat_of_qarity`: the value of a qarity (a coercion `qarity >-> nat` in Coq). -/
@[coe] def natOfQarity : Qarity → ℕ
  | Qa5 => 5
  | Qa6 => 6
  | Qa7 => 7
  | Qa8 => 8
  | Qa9 => 9
  | Qa10 => 10
  | Qa11 => 11

/-- Coq `Coercion nat_of_qarity : qarity >-> nat`. -/
instance : Coe Qarity ℕ := ⟨natOfQarity⟩

/-- Coq `qarity_of_nat n`: the qarity with value `n`, defaulting to `Qa11`. -/
def qarityOfNat : ℕ → Qarity
  | 5 => Qa5
  | 6 => Qa6
  | 7 => Qa7
  | 8 => Qa8
  | 9 => Qa9
  | 10 => Qa10
  | _ => Qa11

/-- Coq `qarity_of_qarity`. -/
theorem qarity_of_qarity (qa : Qarity) : qarityOfNat qa = qa := by
  cases qa <;> rfl

/-! ### Questions -/

/-- Coq `question`: embedding test trees. -/
inductive Question : Type where
  /-- Coq `Qask0`: no check. -/
  | Qask0
  /-- Coq `Qask1 qa`: check arity `qa`. -/
  | Qask1 (qa : Qarity)
  /-- Coq `QaskL qa ql`: check arity `qa`, then check `ql` after a `qstepL` move. -/
  | QaskL (qa : Qarity) (ql : Question)
  /-- Coq `QaskR qa qr`: check arity `qa`, then check `qr` after a `qstepR` move. -/
  | QaskR (qa : Qarity) (qr : Question)
  /-- Coq `QaskLR qa ql qr`: check arity `qa`, then check `ql` after a `qstepL` move and `qr`
  after a `qstepR` move. -/
  | QaskLR (qa : Qarity) (ql qr : Question)
  /-- Coq `QaskLL qa qll`: do a `qstepL` move before a `QaskL qa qll` check. -/
  | QaskLL (qa : Qarity) (qll : Question)
  /-- Coq `QaskRR qa qrr`: do a `qstepR` move before a `QaskR qa qrr` check. -/
  | QaskRR (qa : Qarity) (qrr : Question)
  deriving DecidableEq, Repr, Inhabited

export Question (Qask0 Qask1 QaskL QaskR QaskLR QaskLL QaskRR)

/-- Coq `isQaskR q`: `q` is a `QaskR` node. -/
def isQaskR : Question → Bool
  | QaskR _ _ => true
  | _ => false

/-- Coq `flatq q`: the list of the arities occurring in `q`, collected in prefix order. -/
def flatq : Question → List ℕ
  | Qask0 => []
  | Qask1 qa => [(qa : ℕ)]
  | QaskL qa ql => (qa : ℕ) :: flatq ql
  | QaskR qa qr => (qa : ℕ) :: flatq qr
  | QaskLR qa ql qr => (qa : ℕ) :: (flatq ql ++ flatq qr)
  | QaskLL qa qll => (qa : ℕ) :: flatq qll
  | QaskRR qa qrr => (qa : ℕ) :: flatq qrr

/-- Coq `flipq q`: the mirror image of `q`, with `L` and `R` exchanged. -/
def flipq : Question → Question
  | QaskL qa ql => QaskR qa (flipq ql)
  | QaskR qa qr => QaskL qa (flipq qr)
  | QaskLR qa ql qr => QaskLR qa (flipq qr) (flipq ql)
  | QaskLL qa qll => QaskRR qa (flipq qll)
  | QaskRR qa qrr => QaskLL qa (flipq qrr)
  | q => q

/-! ### Quizzes -/

/-- Coq `quiz`: an embedding test, a pair of questions that test for a preembedding starting from
the initial edge of the configuration construction program (the Coq constructor `Quiz` is
`Quiz.mk`). -/
structure Quiz : Type where
  /-- Coq constructor `Quiz`. -/
  mk ::
  /-- The question asked at the initial dart `x`. -/
  q0 : Question
  /-- The question asked at `edge x`. -/
  q1 : Question
  deriving DecidableEq, Repr, Inhabited

/-- Coq `isQuizR qz`: `qz` consists of two `QaskR` questions. -/
def isQuizR : Quiz → Bool
  | ⟨q0, q1⟩ => isQaskR q0 && isQaskR q1

/-- Coq `flatqz qz`: the list of the arities occurring in the questions of `qz`. -/
def flatqz : Quiz → List ℕ
  | ⟨q0, q1⟩ => flatq q0 ++ flatq q1

/-- Coq `flipqz qz`: the mirror image of `qz`, with `L` and `R` exchanged. -/
def flipqz : Quiz → Quiz
  | ⟨QaskR qa0 q01, QaskR qa1 q10⟩ => ⟨QaskR qa0 (flipq q10), QaskR qa1 (flipq q01)⟩
  | qz => qz

/-- The quizzes satisfying `isQuizR` are the pairs of `QaskR` questions. -/
private theorem isQuizR_exists {qz : Quiz} (h : isQuizR qz = true) :
    ∃ qa0 q01 qa1 q10, qz = ⟨QaskR qa0 q01, QaskR qa1 q10⟩ := by
  obtain ⟨q0, q1⟩ := qz
  cases q0 <;> cases q1 <;> simp_all [isQuizR, isQaskR]

namespace Hypermap

variable {D : Type*} (G : Hypermap D)

/-- Coq `qstepL x`: the left move at a cubic hypermap node. -/
def qstepL (x : D) : D := G.node (G.edge (G.node x))

/-- Coq `qstepR x`: the right move at a cubic hypermap node. -/
def qstepR (x : D) : D := G.node (G.edge x)

/-! ### Fitting quizzes (Coq section `FitQuiz`) -/

/-- Coq `walkq x q`: the sequence of darts visited while testing `q` at `x`, in prefix order.
(The Coq `let xl := qstepL x in ...` and `let xr := qstepR x in ...` are inlined.) -/
def walkq : D → Question → List D
  | _, Qask0 => []
  | x, Qask1 _ => [x]
  | x, QaskL _ ql => x :: walkq (G.qstepL x) ql
  | x, QaskR _ qr => x :: walkq (G.qstepR x) qr
  | x, QaskLR _ ql qr => x :: (walkq (G.qstepL x) ql ++ walkq (G.qstepR x) qr)
  | x, QaskLL _ qll => G.edge (G.node (G.qstepL x)) :: walkq (G.qstepL (G.qstepL x)) qll
  | x, QaskRR _ qrr => G.qstepR x :: walkq (G.qstepR (G.qstepR x)) qrr

/-- Coq `fitq x q`: `q` fits at `x`, i.e., the arities of the darts in `walkq x q` match those
in `flatq q` (a boolean `==` test in Coq). -/
def fitq (x : D) (q : Question) : Prop := flatq q = (G.walkq x q).map G.arity

/-- Coq `size_walkq`. -/
theorem size_walkq (x : D) (q : Question) : (G.walkq x q).length = (flatq q).length := by
  induction q generalizing x with
  | Qask0 => rfl
  | Qask1 qa => rfl
  | QaskL qa ql ih => simp only [walkq, flatq, List.length_cons, ih]
  | QaskR qa qr ih => simp only [walkq, flatq, List.length_cons, ih]
  | QaskLR qa ql qr ihl ihr =>
    simp only [walkq, flatq, List.length_cons, List.length_append, ihl, ihr]
  | QaskLL qa qll ih => simp only [walkq, flatq, List.length_cons, ih]
  | QaskRR qa qrr ih => simp only [walkq, flatq, List.length_cons, ih]

/-- Coq `fitq_cat`. -/
theorem fitq_cat (x : D) (q : Question) (sa : List ℕ) (s : List D) :
    flatq q ++ sa = (G.walkq x q ++ s).map G.arity ↔ G.fitq x q ∧ sa = s.map G.arity := by
  rw [List.map_append]
  constructor
  · intro h
    exact List.append_inj h (by rw [List.length_map, size_walkq])
  · rintro ⟨h1, h2⟩
    rw [← h1, ← h2]

end Hypermap

/-- Coq `size_flipq`. -/
theorem size_flipq (q : Question) : (flatq (flipq q)).length = (flatq q).length := by
  induction q with
  | Qask0 => rfl
  | Qask1 qa => rfl
  | QaskL qa ql ih => simp only [flipq, flatq, List.length_cons, ih]
  | QaskR qa qr ih => simp only [flipq, flatq, List.length_cons, ih]
  | QaskLR qa ql qr ihl ihr =>
    simp only [flipq, flatq, List.length_cons, List.length_append, ihl, ihr]
    omega
  | QaskLL qa qll ih => simp only [flipq, flatq, List.length_cons, ih]
  | QaskRR qa qrr ih => simp only [flipq, flatq, List.length_cons, ih]

namespace Hypermap

variable {D : Type*} (G : Hypermap D)

/-- Coq `walkqz x qz`: the sequence of darts visited while testing `qz` at `x`. -/
def walkqz (x : D) : Quiz → List D
  | ⟨q0, q1⟩ => G.walkq x q0 ++ G.walkq (G.edge x) q1

/-- Coq `size_walkqz`. -/
theorem size_walkqz (x : D) (qz : Quiz) : (G.walkqz x qz).length = (flatqz qz).length := by
  obtain ⟨q0, q1⟩ := qz
  simp only [walkqz, flatqz, List.length_append, size_walkq]

/-- Coq `fitqz x qz`: `qz` fits at `x`, i.e., the arities of the darts in `walkqz x qz` match
those in `flatqz qz` (a boolean `==` test in Coq). -/
def fitqz (x : D) (qz : Quiz) : Prop := flatqz qz = (G.walkqz x qz).map G.arity

/-! Unfolding `fitq` and `fitqz` (helpers). -/

/-- `fitq` on a `Qask0` question. -/
private theorem fitq_Qask0 (x : D) : G.fitq x Qask0 ↔ True := by
  simp [fitq, flatq, walkq]

/-- `fitq` on a `Qask1` question. -/
private theorem fitq_Qask1 (x : D) (qa : Qarity) :
    G.fitq x (Qask1 qa) ↔ (qa : ℕ) = G.arity x := by
  simp [fitq, flatq, walkq]

/-- `fitq` on a `QaskL` question. -/
private theorem fitq_QaskL (x : D) (qa : Qarity) (ql : Question) :
    G.fitq x (QaskL qa ql) ↔ (qa : ℕ) = G.arity x ∧ G.fitq (G.qstepL x) ql := by
  simp only [fitq, flatq, walkq, List.map_cons, List.cons.injEq]

/-- `fitq` on a `QaskR` question. -/
private theorem fitq_QaskR (x : D) (qa : Qarity) (qr : Question) :
    G.fitq x (QaskR qa qr) ↔ (qa : ℕ) = G.arity x ∧ G.fitq (G.qstepR x) qr := by
  simp only [fitq, flatq, walkq, List.map_cons, List.cons.injEq]

/-- `fitq` on a `QaskLR` question. -/
private theorem fitq_QaskLR (x : D) (qa : Qarity) (ql qr : Question) :
    G.fitq x (QaskLR qa ql qr) ↔
      (qa : ℕ) = G.arity x ∧ G.fitq (G.qstepL x) ql ∧ G.fitq (G.qstepR x) qr := by
  rw [fitq, flatq, walkq, List.map_cons, List.cons.injEq, fitq_cat]
  exact Iff.rfl

/-- `fitq` on a `QaskLL` question. -/
private theorem fitq_QaskLL (x : D) (qa : Qarity) (qll : Question) :
    G.fitq x (QaskLL qa qll) ↔
      (qa : ℕ) = G.arity (G.edge (G.node (G.qstepL x))) ∧
        G.fitq (G.qstepL (G.qstepL x)) qll := by
  simp only [fitq, flatq, walkq, List.map_cons, List.cons.injEq]

/-- `fitq` on a `QaskRR` question. -/
private theorem fitq_QaskRR (x : D) (qa : Qarity) (qrr : Question) :
    G.fitq x (QaskRR qa qrr) ↔
      (qa : ℕ) = G.arity (G.qstepR x) ∧ G.fitq (G.qstepR (G.qstepR x)) qrr := by
  simp only [fitq, flatq, walkq, List.map_cons, List.cons.injEq]

/-- `fitqz` on a quiz `⟨q0, q1⟩`. -/
private theorem fitqz_mk (x : D) (q0 q1 : Question) :
    G.fitqz x ⟨q0, q1⟩ ↔ G.fitq x q0 ∧ G.fitq (G.edge x) q1 := by
  rw [fitqz, flatqz, walkqz, fitq_cat]
  rfl

/-- Coq `fitqz_flip`: flipping a quiz amounts to testing it in the mirror map. -/
theorem fitqz_flip [Finite D] (x : D) (qz : Quiz) (hG : G.PlainCubic) (hqz : isQuizR qz = true) :
    G.fitqz x (flipqz qz) ↔ G.mirror.fitqz (G.face x) qz := by
  obtain ⟨qa0, q01, qa1, q10, rfl⟩ := isQuizR_exists hqz
  have e2 := G.plain_eq hG.plain
  -- `face ∘ edge ∘ face = node ∘ edge` in a plain cubic map
  have hFEF : ∀ y, G.face (G.edge (G.face y)) = G.node (G.edge y) := by
    intro y
    calc G.face (G.edge (G.face y)) = G.face (G.edge (G.face (G.edge (G.edge y)))) := by
          rw [e2]
      _ = G.face (G.edge (G.node (G.node (G.edge y)))) := by rw [G.cubic_eq' hG.cubic]
      _ = G.node (G.edge y) := G.nodeK _
  have nFh : ∀ y, G.mirror.arity y = G.arity y := G.arity_mirror
  have hL : ∀ y, G.mirror.qstepL y = G.qstepR y := by
    intro y
    show G.face (G.edge (G.face (G.node (G.face (G.edge y))))) = G.node (G.edge y)
    rw [G.edgeK]
    exact hFEF y
  have hR : ∀ y, G.mirror.qstepR y = G.qstepL y := fun y => hFEF (G.node y)
  have hE : ∀ y, G.mirror.edge (G.face y) = G.face (G.edge y) := fun y => by
    rw [mirror_edge, G.plain_eq' hG.plain]
  have nFen : ∀ (G1 : Hypermap D) (y : D), G1.arity (G1.edge (G1.node y)) = G1.arity y :=
    fun G1 y => by rw [← G1.arity_face, G1.nodeK]
  have fit_flip : ∀ (q : Question) (y : D), G.fitq y (flipq q) ↔ G.mirror.fitq y q := by
    intro q
    induction q with
    | Qask0 =>
      intro y
      show G.fitq y Qask0 ↔ G.mirror.fitq y Qask0
      rw [fitq_Qask0, fitq_Qask0]
    | Qask1 qa =>
      intro y
      show G.fitq y (Qask1 qa) ↔ G.mirror.fitq y (Qask1 qa)
      rw [fitq_Qask1, fitq_Qask1, nFh]
    | QaskL qa ql ih =>
      intro y
      rw [flipq, fitq_QaskR, fitq_QaskL, ih, hL, nFh]
    | QaskR qa qr ih =>
      intro y
      rw [flipq, fitq_QaskL, fitq_QaskR, ih, hR, nFh]
    | QaskLR qa ql qr ihl ihr =>
      intro y
      rw [flipq, fitq_QaskLR, fitq_QaskLR, ihl, ihr, hL, hR, nFh,
        and_comm (a := G.mirror.fitq _ qr)]
    | QaskLL qa qll ih =>
      intro y
      rw [flipq, fitq_QaskRR, fitq_QaskLL, ih, hL, hL, nFen, nFh]
    | QaskRR qa qrr ih =>
      intro y
      rw [flipq, fitq_QaskLL, fitq_QaskRR, ih, hR, hR, nFen, nFh]
  rw [flipqz, fitqz_mk, fitqz_mk, fitq_QaskR, fitq_QaskR, fitq_QaskR, fitq_QaskR, fit_flip,
    fit_flip, nFh, nFh, G.arity_face, hE, hR, hR, G.arity_face]
  have h1 : G.qstepL (G.face x) = G.qstepR (G.edge x) := by
    rw [qstepL, qstepR, G.plain_eq' hG.plain]
  have h2 : G.qstepL (G.face (G.edge x)) = G.qstepR x := by
    rw [qstepL, qstepR, G.edgeK]
  rw [h1, h2]
  constructor
  · rintro ⟨⟨a1, a2⟩, a3, a4⟩
    exact ⟨⟨a1, a4⟩, a3, a2⟩
  · rintro ⟨⟨a1, a2⟩, a3, a4⟩
    exact ⟨⟨a1, a4⟩, a3, a2⟩

end Hypermap

/-! ### math-comp `findex` (helpers) -/

section Findex

variable {α : Type*}

open Classical in
/-- math-comp `findex f x y`: the index of `y` in the orbit of `x` under `f` (the order of `x` if
`y` is not in this orbit). -/
private noncomputable def findex (f : α → α) (x y : α) : ℕ := (orbit f x).idxOf y

variable [Finite α] {f : α → α}

open Classical in
/-- math-comp `findex0`. -/
private theorem findex0 (hf : Injective f) (x : α) : findex f x x = 0 := by
  obtain ⟨n, hn⟩ : ∃ n, order f x = n + 1 :=
    ⟨order f x - 1, by have := order_pos hf x; omega⟩
  unfold findex orbit
  rw [hn]
  exact List.idxOf_cons_self

open Classical in
/-- math-comp `iter_findex`. -/
private theorem iter_findex (hf : Injective f) {x y : α} (h : fconnect f x y) :
    f^[findex f x y] x = y := by
  have hy : y ∈ orbit f x := (fconnect_orbit hf).1 h
  unfold findex
  unfold orbit at hy ⊢
  have hlt := List.idxOf_lt_length_of_mem hy
  rw [← List.getElem_iterate f x (order f x) _ hlt]
  exact List.getElem_idxOf hlt

open Classical in
/-- math-comp `findex_max`. -/
private theorem findex_max (hf : Injective f) {x y : α} (h : fconnect f x y) :
    findex f x y < order f x := by
  have hy : y ∈ orbit f x := (fconnect_orbit hf).1 h
  rw [← length_orbit]
  exact List.idxOf_lt_length_of_mem hy

open Classical in
/-- math-comp `findex_iter`. -/
private theorem findex_iter (hf : Injective f) {x : α} {i : ℕ} (hi : i < order f x) :
    findex f x (f^[i] x) = i := by
  have hlt : i < (orbit f x).length := by rw [length_orbit]; exact hi
  have h1 : (orbit f x)[i] = f^[i] x := List.getElem_iterate f x (order f x) i hlt
  unfold findex
  rw [← h1]
  exact (orbit_uniq hf x).idxOf_getElem i hlt

end Findex

namespace Hypermap

/-! ### Quiz embeddings (Coq section `QuizEmbedding`)

The main result of this file: the construction of a preembedding of a configuration map `Gc`
into a plain cubic hypermap `Gm` from a quiz valid for `Gc` that also fits into `Gm`. -/

section QuizEmbedding

variable {Dm Dc : Type*} (Gm : Hypermap Dm) (Gc : Hypermap Dc)

/-- Coq `valid_quiz rc x0c qz` (a `[/\ _, _, _ & _]` conjunction in Coq): `qz` tests for the
configuration with perimeter `rc`, at the initial dart `x0c`: `qz` satisfies `isQuizR`, fits at
`x0c`, and `walkqz x0c qz` is a transversal of the faces in `kernel rc`. -/
structure ValidQuiz (rc : List Dc) (x0c : Dc) (qz : Quiz) : Prop where
  /-- `isQuizR qz`. -/
  quizR : isQuizR qz = true
  /-- `fitqz x0c qz`. -/
  fit : Gc.fitqz x0c qz
  /-- `simple (walkqz x0c qz)`. -/
  simple : Gc.Simple (Gc.walkqz x0c qz)
  /-- `fband (walkqz x0c qz) =i kernel rc`. -/
  fband_eq : Gc.fband (Gc.walkqz x0c qz) = Gc.kernel rc

open Classical in
/-- Coq `embedqz x0m x0c qz`: a preembedding of `kernel rc` into `Gm` that maps `x0c` to `x0m`,
assuming `qz` tests for `kernel rc` at `x0c` and fits `Gm` at `x0m` (see `quiz_preembedding`):
the dart `x` is mapped to the dart at the same position in the face of the `i`-th dart of
`walkqz x0m qz`, where the face of `x` contains the `i`-th dart of `walkqz x0c qz`. -/
noncomputable def embedqz (x0m : Dm) (x0c : Dc) (qz : Quiz) (x : Dc) : Dm :=
  let s0c := Gc.walkqz x0c qz
  let i := s0c.findIdx fun y => decide (Gc.cface x y)
  Gm.face^[findex Gc.face (s0c.getD i x0c) x] ((Gm.walkqz x0m qz).getD i x0m)

variable {Gm Gc} {rc : List Dc} {x0m : Dm} {x0c : Dc} {qz : Quiz}

open Classical in
/-- `embedqz` at a dart `x` whose face first meets `walkqz x0c qz` at position `i`. -/
private theorem embedqz_at {x : Dc} {i : ℕ} (hi : i < (Gc.walkqz x0c qz).length)
    (hxi : Gc.cface x (Gc.walkqz x0c qz)[i])
    (hlt : ∀ j (hj : j < i), ¬ Gc.cface x ((Gc.walkqz x0c qz)[j]'(Nat.lt_trans hj hi))) :
    embedqz Gm Gc x0m x0c qz x =
      Gm.face^[findex Gc.face (Gc.walkqz x0c qz)[i] x] ((Gm.walkqz x0m qz).getD i x0m) := by
  have hf : ((Gc.walkqz x0c qz).findIdx fun y => decide (Gc.cface x y)) = i :=
    (List.findIdx_eq hi).2 ⟨decide_eq_true hxi, fun j hj => decide_eq_false (hlt j hj)⟩
  simp only [embedqz, hf, List.getD_eq_getElem _ _ hi]

open Classical in
/-- The first position at which the face of `x` meets `s` (Coq `find (cface x) s`). -/
private theorem exists_first {s : List Dc} {x : Dc} (hx : x ∈ Gc.fband s) :
    ∃ i, ∃ hi : i < s.length, Gc.cface x s[i] ∧
      ∀ j (hj : j < i), ¬ Gc.cface x (s[j]'(Nat.lt_trans hj hi)) := by
  obtain ⟨y, hy, hxy⟩ := hx
  have hlt : (s.findIdx fun y => decide (Gc.cface x y)) < s.length :=
    List.findIdx_lt_length_of_exists ⟨y, hy, decide_eq_true hxy⟩
  exact ⟨_, hlt, of_decide_eq_true (List.findIdx_getElem (w := hlt)),
    fun j hj => of_decide_eq_false (List.not_of_lt_findIdx hj)⟩

variable [Finite Dm] [Finite Dc]

omit [Finite Dm] in
/-- Coq section-local `Dhx0`: `embedqz` maps `x0c` to `x0m`. -/
private theorem embedqz_x0c (hqz : isQuizR qz = true) : embedqz Gm Gc x0m x0c qz x0c = x0m := by
  obtain ⟨qa0, q01, qa1, q10, rfl⟩ := isQuizR_exists hqz
  have hi : 0 < (Gc.walkqz x0c ⟨QaskR qa0 q01, QaskR qa1 q10⟩).length := by
    simp [walkqz, walkq]
  have e0 : (Gc.walkqz x0c ⟨QaskR qa0 q01, QaskR qa1 q10⟩)[0] = x0c := rfl
  rw [embedqz_at hi (connect_refl x0c) (fun j hj => absurd hj (Nat.not_lt_zero j)), e0,
    findex0 Gc.faceI, Function.iterate_zero_apply]
  rfl

omit [Finite Dm] in
/-- Coq section-local `Dhs0`: `embedqz` maps `walkqz x0c qz` to `walkqz x0m qz`. -/
private theorem embedqz_nth (qz_ok : Gc.ValidQuiz rc x0c qz) (i : ℕ) :
    embedqz Gm Gc x0m x0c qz ((Gc.walkqz x0c qz).getD i x0c) = (Gm.walkqz x0m qz).getD i x0m := by
  have hlen : (Gm.walkqz x0m qz).length = (Gc.walkqz x0c qz).length := by
    rw [size_walkqz, size_walkqz]
  by_cases hi : i < (Gc.walkqz x0c qz).length
  · have hU := Gc.simple_uniq qz_ok.simple
    rw [List.getD_eq_getElem _ _ hi, embedqz_at hi (connect_refl _) ?_, findex0 Gc.faceI,
      Function.iterate_zero_apply]
    intro j hj hji
    have := Gc.simple_cface qz_ok.simple _ (List.getElem_mem hi) _ (List.getElem_mem _) hji
    exact absurd (hU.getElem_inj_iff.1 this) (Nat.ne_of_gt hj)
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hi),
      List.getD_eq_default _ _ (by rw [hlen]; exact Nat.le_of_not_lt hi)]
    exact embedqz_x0c qz_ok.quizR

omit [Finite Dm] in
/-- Coq section-local `Dhex0`: `embedqz` maps `edge x0c` to `edge x0m`. -/
private theorem embedqz_edge_x0c (qz_ok : Gc.ValidQuiz rc x0c qz) :
    embedqz Gm Gc x0m x0c qz (Gc.edge x0c) = Gm.edge x0m := by
  have h := embedqz_nth (Gm := Gm) (x0m := x0m) qz_ok (flatq qz.q0).length
  obtain ⟨qa0, q01, qa1, q10, rfl⟩ := isQuizR_exists qz_ok.quizR
  simp only [walkqz] at h
  rw [List.getD_append_right _ _ _ _ (by rw [size_walkq]),
    List.getD_append_right _ _ _ _ (by rw [size_walkq]), size_walkq, size_walkq, Nat.sub_self] at h
  exact h

omit [Finite Dm] [Finite Dc] in
/-- The arities at the same position of `walkqz x0c qz` and `walkqz x0m qz` coincide. -/
private theorem arity_nth (qz_ok : Gc.ValidQuiz rc x0c qz) (qz_x0m : Gm.fitqz x0m qz) {i : ℕ}
    (hi : i < (Gc.walkqz x0c qz).length) :
    Gm.arity ((Gm.walkqz x0m qz).getD i x0m) = Gc.arity (Gc.walkqz x0c qz)[i] := by
  have hmap : (Gm.walkqz x0m qz).map Gm.arity = (Gc.walkqz x0c qz).map Gc.arity :=
    qz_x0m.symm.trans qz_ok.fit
  have hi' : i < (Gm.walkqz x0m qz).length := by rwa [size_walkqz, ← size_walkqz Gc x0c]
  rw [List.getD_eq_getElem _ _ hi']
  have := congrArg (fun l => l[i]?) hmap
  simpa [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] using this

/-- Coq `embedqz_arity`: `embedqz` preserves arities on `kernel rc`. -/
theorem embedqz_arity (qz_ok : Gc.ValidQuiz rc x0c qz) (qz_x0m : Gm.fitqz x0m qz) {x : Dc}
    (hx : x ∈ Gc.kernel rc) : Gm.arity (embedqz Gm Gc x0m x0c qz x) = Gc.arity x := by
  rw [← qz_ok.fband_eq] at hx
  obtain ⟨i, hi, hxi, hlt⟩ := exists_first hx
  rw [embedqz_at hi hxi hlt, Gm.arity_iter_face, Gc.arity_cface hxi]
  exact arity_nth qz_ok qz_x0m hi

/-- Coq `embedqz_face`: `embedqz` commutes with `face` on `kernel rc`. -/
theorem embedqz_face (qz_ok : Gc.ValidQuiz rc x0c qz) (qz_x0m : Gm.fitqz x0m qz) :
    ∀ x ∈ Gc.kernel rc,
      embedqz Gm Gc x0m x0c qz (Gc.face x) = Gm.face (embedqz Gm Gc x0m x0c qz x) := by
  intro x hx
  rw [← qz_ok.fband_eq] at hx
  obtain ⟨i, hi, hxi, hlt⟩ := exists_first hx
  have hfxi : Gc.cface (Gc.face x) (Gc.walkqz x0c qz)[i] := (Gc.cface1 x _).1 hxi
  have hflt : ∀ j (hj : j < i),
      ¬ Gc.cface (Gc.face x) ((Gc.walkqz x0c qz)[j]'(Nat.lt_trans hj hi)) :=
    fun j hj h => hlt j hj ((Gc.cface1 x _).2 h)
  have har := arity_nth qz_ok qz_x0m hi
  rw [embedqz_at hi hfxi hflt, embedqz_at hi hxi hlt]
  generalize (Gc.walkqz x0c qz)[i] = yc at hxi har ⊢
  generalize (Gm.walkqz x0m qz).getD i x0m = ym at har ⊢
  have ycFx : Gc.cface yc x := Gc.cfaceC.1 hxi
  have hj : findex Gc.face yc x < Gc.arity yc := findex_max Gc.faceI ycFx
  have hx' := iter_findex Gc.faceI ycFx
  generalize findex Gc.face yc x = j at hj hx' ⊢
  subst hx'
  have e1 : Gc.face (Gc.face^[j] yc) = Gc.face^[j + 1] yc :=
    (Function.iterate_succ_apply' _ _ _).symm
  have e2 : Gm.face (Gm.face^[j] ym) = Gm.face^[j + 1] ym :=
    (Function.iterate_succ_apply' _ _ _).symm
  rw [e1, e2]
  rcases Nat.lt_or_ge (j + 1) (Gc.arity yc) with hlt' | hge
  · rw [findex_iter Gc.faceI hlt']
  · have hj1 : j + 1 = Gc.arity yc := le_antisymm hj hge
    rw [hj1, Gc.iter_face_arity, findex0 Gc.faceI, Function.iterate_zero_apply, ← har,
      Gm.iter_face_arity]

/-- Coq `embedqz_central`: `embedqz` commutes with `edge` on `walkqz x0c qz`. -/
theorem embedqz_central (geoGm : Gm.PlainCubic) (geoGc : Gc.PlainQuasicubic rc)
    (qz_ok : Gc.ValidQuiz rc x0c qz) (qz_x0m : Gm.fitqz x0m qz) :
    ∀ x ∈ Gc.walkqz x0c qz, x ∈ Gc.edgeCentral Gm (embedqz Gm Gc x0m x0c qz) := by
  have hF := embedqz_face qz_ok qz_x0m
  have Dhx0 := embedqz_x0c (Gm := Gm) (Gc := Gc) (x0m := x0m) (x0c := x0c) qz_ok.quizR
  have Dhex0 := embedqz_edge_x0c (Gm := Gm) (x0m := x0m) qz_ok
  have hcE := Gc.edge_central_edge Gm geoGc.plain geoGm.plain (embedqz Gm Gc x0m x0c qz)
  have Ehs0 : (Gc.walkqz x0c qz).map (embedqz Gm Gc x0m x0c qz) = Gm.walkqz x0m qz := by
    apply List.ext_getElem
    · rw [List.length_map, size_walkqz, size_walkqz]
    · intro i h1 h2
      rw [List.getElem_map, ← List.getD_eq_getElem _ x0c, embedqz_nth qz_ok,
        List.getD_eq_getElem]
  have s0_ac : ∀ x ∈ Gc.walkqz x0c qz, x ∈ Gc.kernel rc := fun x hx =>
    qz_ok.fband_eq ▸ Gc.ring_fband _ x hx
  obtain ⟨qa0, q01, qa1, q10, rfl⟩ := isQuizR_exists qz_ok.quizR
  generalize embedqz Gm Gc x0m x0c _ = h at *
  have e2m := Gm.plain_eq geoGm.plain
  have e2c := Gc.plain_eq geoGc.plain
  have nn_m : ∀ y, Gm.node (Gm.node y) = Gm.face (Gm.edge y) := Gm.cubic_eq' geoGm.cubic
  have n3c : ∀ x ∈ Gc.kernel rc, Gc.node (Gc.node (Gc.node x)) = x := fun x hx =>
    Gc.quasicubic_eq geoGc.quasicubic x (Gc.kernel_off_ring rc hx)
  have nn_c : ∀ x ∈ Gc.kernel rc, Gc.node (Gc.node x) = Gc.face (Gc.edge x) := fun x hx => by
    have := Gc.nodeK (Gc.node (Gc.node x))
    rw [n3c x hx] at this
    exact this.symm
  have acF : ∀ x, x ∈ Gc.kernel rc ↔ Gc.face x ∈ Gc.kernel rc := fun x =>
    Gc.kernelF rc x _ rfl
  have ac_en : ∀ x ∈ Gc.kernel rc, Gc.edge (Gc.node x) ∈ Gc.kernel rc := fun x hx =>
    (acF _).2 (by rw [Gc.nodeK]; exact hx)
  -- `h (edge (node z)) = edge (node (h z))` (from `faceK` and `embedqz_face`)
  have hEN : ∀ z, Gc.edge (Gc.node z) ∈ Gc.kernel rc →
      h (Gc.edge (Gc.node z)) = Gm.edge (Gm.node (h z)) := by
    intro z hz
    calc h (Gc.edge (Gc.node z)) = Gm.edge (Gm.node (Gm.face (h (Gc.edge (Gc.node z))))) :=
          (Gm.faceK _).symm
      _ = Gm.edge (Gm.node (h z)) := by rw [← hF _ hz, Gc.nodeK]
  -- Coq `hc_nx`
  have hc_n : ∀ x ∈ Gc.kernel rc, h (Gc.node x) = Gm.node (h x) →
      Gc.node x ∈ Gc.edgeCentral Gm h := by
    intro x ac_x hnx
    show h (Gc.edge (Gc.node x)) = Gm.edge (h (Gc.node x))
    rw [hEN x (ac_en x ac_x), hnx]
  -- Coq `hc_ennx`
  have hc_enn : ∀ x ∈ Gc.kernel rc, Gc.edge x ∈ Gc.kernel rc → x ∈ Gc.edgeCentral Gm h →
      Gc.node x ∈ Gc.kernel rc → h (Gc.node x) = Gm.node (h x) →
      Gc.edge (Gc.node (Gc.node x)) ∈ Gc.edgeCentral Gm h := by
    intro x ac_x ac_ex hex ac_nx hnx
    have hex' : h (Gc.edge x) = Gm.edge (h x) := hex
    show h (Gc.edge (Gc.edge (Gc.node (Gc.node x)))) = Gm.edge (h (Gc.edge (Gc.node (Gc.node x))))
    rw [e2c, hEN _ (ac_en _ ac_nx), hnx, e2m, nn_c x ac_x, hF _ ac_ex, hex', nn_m]
  have hc_walk : ∀ (q : Question) (x : Dc), x ∈ Gc.kernel rc → Gc.edge x ∈ Gc.kernel rc →
      x ∈ Gc.edgeCentral Gm h → (∀ y ∈ Gc.walkq (Gc.node x) q, y ∈ Gc.kernel rc) →
      (Gc.walkq (Gc.node x) q).map h = Gm.walkq (Gm.node (h x)) q →
      ∀ y ∈ Gc.walkq (Gc.node x) q, y ∈ Gc.edgeCentral Gm h := by
    intro q
    induction q with
    | Qask0 => intro x _ _ _ _ _ y hy; simp [walkq] at hy
    | Qask1 qa =>
      intro x ac_x _ _ _ hs y hy
      simp only [walkq, List.map_cons, List.map_nil, List.cons.injEq, and_true,
        List.mem_singleton] at hs hy
      subst hy
      exact hc_n x ac_x hs
    | QaskL qa q ih =>
      intro x ac_x ac_ex hex ac_s hs
      simp only [walkq, List.map_cons, List.cons.injEq] at hs
      obtain ⟨hnx, h_q⟩ := hs
      have ac_nx : Gc.node x ∈ Gc.kernel rc := ac_s _ List.mem_cons_self
      have hc_nx := hc_n x ac_x hnx
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hc_nx
      · refine ih (Gc.edge (Gc.node (Gc.node x))) (ac_en _ ac_nx) ?_
          (hc_enn x ac_x ac_ex hex ac_nx hnx) (fun y hy => ac_s y (List.mem_cons_of_mem _ hy))
          ?_ y hy
        · rw [e2c, nn_c x ac_x]
          exact (acF _).1 ac_ex
        · change List.map h (Gc.walkq (Gc.qstepL (Gc.node x)) q) = _
          rw [h_q, hEN _ (ac_en _ ac_nx), hnx]
          rfl
    | QaskR qa q ih =>
      intro x ac_x ac_ex hex ac_s hs
      simp only [walkq, List.map_cons, List.cons.injEq] at hs
      obtain ⟨hnx, h_q⟩ := hs
      have ac_nx : Gc.node x ∈ Gc.kernel rc := ac_s _ List.mem_cons_self
      have hc_nx := hc_n x ac_x hnx
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hc_nx
      · refine ih (Gc.edge (Gc.node x)) (ac_en _ ac_x) (by rw [e2c]; exact ac_nx)
          ((hcE _).2 hc_nx) (fun y hy => ac_s y (List.mem_cons_of_mem _ hy)) ?_ y hy
        change List.map h (Gc.walkq (Gc.qstepR (Gc.node x)) q) = _
        rw [h_q, hEN _ (ac_en _ ac_x)]
        rfl
    | QaskLR qa ql qr ihl ihr =>
      intro x ac_x ac_ex hex ac_s hs
      simp only [walkq, List.map_cons, List.map_append, List.cons.injEq] at hs
      obtain ⟨hnx, h_q⟩ := hs
      obtain ⟨h_ql, h_qr⟩ :=
        List.append_inj h_q (by rw [List.length_map, size_walkq, size_walkq])
      have ac_nx : Gc.node x ∈ Gc.kernel rc := ac_s _ List.mem_cons_self
      have hc_nx := hc_n x ac_x hnx
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hc_nx
      rcases List.mem_append.1 hy with hy | hy
      · refine ihl (Gc.edge (Gc.node (Gc.node x))) (ac_en _ ac_nx) ?_
          (hc_enn x ac_x ac_ex hex ac_nx hnx)
          (fun y hy => ac_s y (List.mem_cons_of_mem _ (List.mem_append_left _ hy))) ?_ y hy
        · rw [e2c, nn_c x ac_x]
          exact (acF _).1 ac_ex
        · change List.map h (Gc.walkq (Gc.qstepL (Gc.node x)) ql) = _
          rw [h_ql, hEN _ (ac_en _ ac_nx), hnx]
          rfl
      · refine ihr (Gc.edge (Gc.node x)) (ac_en _ ac_x) (by rw [e2c]; exact ac_nx)
          ((hcE _).2 hc_nx)
          (fun y hy => ac_s y (List.mem_cons_of_mem _ (List.mem_append_right _ hy))) ?_ y hy
        change List.map h (Gc.walkq (Gc.qstepR (Gc.node x)) qr) = _
        rw [h_qr, hEN _ (ac_en _ ac_x)]
        rfl
    | QaskLL qa q ih =>
      intro x ac_x ac_ex hex ac_s hs
      simp only [walkq, List.map_cons, List.cons.injEq] at hs
      obtain ⟨henLnx, h_q⟩ := hs
      have hex' : h (Gc.edge x) = Gm.edge (h x) := hex
      have ac_enLnx : Gc.edge (Gc.node (Gc.qstepL (Gc.node x))) ∈ Gc.kernel rc :=
        ac_s _ List.mem_cons_self
      have ac_fex : Gc.face (Gc.edge x) ∈ Gc.kernel rc := (acF _).1 ac_ex
      have ac_ffex : Gc.face (Gc.face (Gc.edge x)) ∈ Gc.kernel rc := (acF _).1 ac_fex
      -- `node (qstepL (node x)) = face (face (edge x))`, in `Gc` and in `Gm`
      have Dffc : Gc.node (Gc.qstepL (Gc.node x)) = Gc.face (Gc.face (Gc.edge x)) := by
        show Gc.node (Gc.node (Gc.edge (Gc.node (Gc.node x)))) = _
        rw [nn_c x ac_x, ← Gc.plain_eq' geoGc.plain (Gc.face (Gc.edge x))]
        exact n3c _ ac_ffex
      have Dffm : Gm.node (Gm.qstepL (Gm.node (h x))) = Gm.face (Gm.face (Gm.edge (h x))) := by
        show Gm.node (Gm.node (Gm.edge (Gm.node (Gm.node (h x))))) = _
        rw [nn_m (h x), nn_m, e2m]
      have hc_enLnx : Gc.edge (Gc.node (Gc.qstepL (Gc.node x))) ∈ Gc.edgeCentral Gm h := by
        show h (Gc.edge (Gc.edge (Gc.node (Gc.qstepL (Gc.node x))))) =
          Gm.edge (h (Gc.edge (Gc.node (Gc.qstepL (Gc.node x)))))
        rw [e2c, henLnx, e2m, Dffc, Dffm, hF _ ac_fex, hF _ ac_ex, hex']
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hc_enLnx
      · refine ih (Gc.edge (Gc.node (Gc.qstepL (Gc.node x)))) ac_enLnx
          (by rw [e2c, Dffc]; exact ac_ffex) hc_enLnx
          (fun y hy => ac_s y (List.mem_cons_of_mem _ hy)) ?_ y hy
        change List.map h (Gc.walkq (Gc.qstepL (Gc.qstepL (Gc.node x))) q) = _
        rw [h_q, henLnx]
        rfl
    | QaskRR qa q ih =>
      intro x ac_x ac_ex hex ac_s hs
      simp only [walkq, List.map_cons, List.cons.injEq] at hs
      obtain ⟨hRnx, h_q⟩ := hs
      have ac_Rnx : Gc.qstepR (Gc.node x) ∈ Gc.kernel rc := ac_s _ List.mem_cons_self
      have ac_enx : Gc.edge (Gc.node x) ∈ Gc.kernel rc := ac_en _ ac_x
      have ac_enenx : Gc.edge (Gc.node (Gc.edge (Gc.node x))) ∈ Gc.kernel rc := ac_en _ ac_enx
      have hc_Rnx : Gc.qstepR (Gc.node x) ∈ Gc.edgeCentral Gm h := by
        refine hc_n _ ac_enx ?_
        rw [hEN _ ac_enx]
        exact hRnx
      intro y hy
      rcases List.mem_cons.1 hy with rfl | hy
      · exact hc_Rnx
      · refine ih (Gc.edge (Gc.qstepR (Gc.node x))) ac_enenx (by rw [e2c]; exact ac_Rnx)
          ((hcE _).2 hc_Rnx) (fun y hy => ac_s y (List.mem_cons_of_mem _ hy)) ?_ y hy
        have hc_Rnx' : h (Gc.edge (Gc.qstepR (Gc.node x))) = Gm.edge (h (Gc.qstepR (Gc.node x))) :=
          hc_Rnx
        change List.map h (Gc.walkq (Gc.qstepR (Gc.qstepR (Gc.node x))) q) = _
        rw [h_q, hc_Rnx', hRnx]
        rfl
  have hc_x0 : x0c ∈ Gc.edgeCentral Gm h := by
    show h (Gc.edge x0c) = Gm.edge (h x0c)
    rw [Dhex0, Dhx0]
  have hc_ex0 : Gc.edge x0c ∈ Gc.edgeCentral Gm h := (hcE _).2 hc_x0
  simp only [walkqz, walkq, List.map_cons, List.map_append, List.cons_append,
    List.cons.injEq] at Ehs0
  obtain ⟨-, Ehs0⟩ := Ehs0
  obtain ⟨h_q01, h_q10⟩ :=
    List.append_inj Ehs0 (by rw [List.length_map, size_walkq, size_walkq])
  obtain ⟨-, h_q10⟩ := List.cons.inj h_q10
  have s0_ac' : ∀ y, y ∈ Gc.walkqz x0c ⟨QaskR qa0 q01, QaskR qa1 q10⟩ →
      y ∈ Gc.kernel rc :=
    s0_ac
  simp only [walkqz, walkq, List.cons_append, List.mem_cons, List.mem_append] at s0_ac' ⊢
  have ac_x0 := s0_ac' x0c (Or.inl rfl)
  have ac_ex0 := s0_ac' (Gc.edge x0c) (Or.inr (Or.inr (Or.inl rfl)))
  rintro y (rfl | hy | rfl | hy)
  · exact hc_x0
  · refine hc_walk q01 (Gc.edge x0c) ac_ex0 (by rw [e2c]; exact ac_x0) hc_ex0
      (fun y hy => s0_ac' y (Or.inr (Or.inl hy))) ?_ y hy
    change List.map h (Gc.walkq (Gc.qstepR x0c) q01) = _
    rw [h_q01, Dhex0]
    rfl
  · exact hc_ex0
  · have e : Gc.qstepR (Gc.edge x0c) = Gc.node x0c := by rw [qstepR, e2c]
    rw [e] at hy h_q10 s0_ac'
    refine hc_walk q10 x0c ac_x0 ac_ex0 hc_x0
      (fun y hy => s0_ac' y (Or.inr (Or.inr (Or.inr hy)))) ?_ y hy
    rw [h_q10, Dhx0, qstepR, e2m]

/-- Coq `embedqz_rlinked`: the darts of `kernel rc` at which `embedqz` commutes with `edge` form
an R-link connected set. -/
theorem embedqz_rlinked (geoGm : Gm.PlainCubic) (geoGc : Gc.PlainQuasicubic rc)
    (qz_ok : Gc.ValidQuiz rc x0c qz) (qz_x0m : Gm.fitqz x0m qz) :
    Gc.RLinkConnected (Gc.kernel rc ∩ Gc.edgeCentral Gm (embedqz Gm Gc x0m x0c qz)) := by
  have hcent := embedqz_central geoGm geoGc qz_ok qz_x0m
  have hcE := Gc.edge_central_edge Gm geoGc.plain geoGm.plain (embedqz Gm Gc x0m x0c qz)
  have s0_ac : ∀ x ∈ Gc.walkqz x0c qz, x ∈ Gc.kernel rc := fun x hx =>
    qz_ok.fband_eq ▸ Gc.ring_fband _ x hx
  obtain ⟨qa0, q01, qa1, q10, rfl⟩ := isQuizR_exists qz_ok.quizR
  generalize Gc.edgeCentral Gm (embedqz Gm Gc x0m x0c _) = hc at *
  have e2c := Gc.plain_eq geoGc.plain
  have n3c : ∀ x ∈ Gc.kernel rc, Gc.node (Gc.node (Gc.node x)) = x := fun x hx =>
    Gc.quasicubic_eq geoGc.quasicubic x (Gc.kernel_off_ring rc hx)
  have nn_c' : ∀ x, Gc.node x ∈ Gc.kernel rc → Gc.node (Gc.node x) = Gc.face (Gc.edge x) := by
    intro x hx
    have h3 : Gc.node (Gc.node (Gc.node x)) = x := Gc.nodeI (n3c _ hx)
    have := Gc.nodeK (Gc.node (Gc.node x))
    rw [h3] at this
    exact this.symm
  have acF : ∀ x, x ∈ Gc.kernel rc ↔ Gc.face x ∈ Gc.kernel rc := fun x =>
    Gc.kernelF rc x _ rfl
  have fbF : ∀ (a : List Dc) (x : Dc), x ∈ Gc.fband a ↔ Gc.face x ∈ Gc.fband a :=
    fun a x => Gc.fbandF a x _ rfl
  have ac_of_fband : ∀ a : List Dc, (∀ y ∈ a, y ∈ Gc.kernel rc) →
      ∀ x ∈ Gc.fband a, x ∈ Gc.kernel rc := by
    rintro a a_ac x ⟨y, hy, hxy⟩
    exact ((Gc.kernelF rc).connect_iff hxy).2 (a_ac y hy)
  have cfEN : ∀ y, Gc.cface (Gc.edge (Gc.node y)) y := fun y => by
    have := fconnect1 Gc.face (Gc.edge (Gc.node y))
    rwa [Gc.nodeK] at this
  -- Coq `ccRfband`
  have ccRfband : ∀ (x : Dc) (a : List Dc), x ∈ Gc.fband a →
      Gc.RLinkConnected (Gc.fband a ∩ hc) → Gc.node x ∈ hc →
      Gc.RLinkConnected (Gc.fband (a ++ [Gc.node x]) ∩ hc) := by
    intro x a aFx ccFa hc_nx y hy z hz
    have aFenx : Gc.edge (Gc.node x) ∈ Gc.fband a ∩ hc :=
      ⟨(fbF a _).2 (by rw [Gc.nodeK]; exact aFx), (hcE _).2 hc_nx⟩
    have sub : ∀ w ∈ Gc.fband a ∩ hc, w ∈ Gc.fband (a ++ [Gc.node x]) ∩ hc :=
      fun w hw => ⟨(Gc.fband_rcons _ _ _).2 (Or.inr hw.1), hw.2⟩
    obtain ⟨hyF, hyc⟩ := hy
    obtain ⟨hzF, hzc⟩ := hz
    rw [Gc.fband_rcons] at hyF hzF
    by_cases yFnx : Gc.cface y (Gc.node x)
    · by_cases zFnx : Gc.cface z (Gc.node x)
      · refine ⟨[], ⟨?_, trivial⟩, fun w hw => absurd hw List.not_mem_nil⟩
        show Gc.cface (Gc.edge (Gc.node (Gc.face y))) z
        rw [Gc.faceK]
        exact connect_trans yFnx (Gc.cfaceC.1 zFnx)
      · obtain ⟨p, hp, hpa⟩ := ccFa _ aFenx z ⟨hzF.resolve_left zFnx, hzc⟩
        rw [Gc.edgeK] at hp
        refine ⟨Gc.node x :: p, ⟨?_, hp⟩, ?_⟩
        · show Gc.cface (Gc.edge (Gc.node (Gc.face y))) (Gc.node x)
          rw [Gc.faceK]
          exact yFnx
        · intro w hw
          rcases List.mem_cons.1 hw with rfl | hw
          · exact ⟨(Gc.fband_rcons _ _ _).2 (Or.inl (connect_refl _)), hc_nx⟩
          · exact sub w (hpa w hw)
    · have hya : y ∈ Gc.fband a ∩ hc := ⟨hyF.resolve_left yFnx, hyc⟩
      by_cases zFnx : Gc.cface z (Gc.node x)
      · obtain ⟨p, hp, hpa⟩ := ccFa y hya _ aFenx
        refine ⟨p ++ [Gc.edge (Gc.node x)], ?_, ?_⟩
        · rw [path_concat, last_concat]
          refine ⟨hp, ?_⟩
          show Gc.cface (Gc.edge (Gc.edge (Gc.node x))) z
          rw [e2c]
          exact Gc.cfaceC.1 zFnx
        · intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · exact sub w (hpa w hw)
          · rw [List.mem_singleton.1 hw]
            exact sub _ aFenx
      · obtain ⟨p, hp, hpa⟩ := ccFa y hya z ⟨hzF.resolve_left zFnx, hzc⟩
        exact ⟨p, hp, fun w hw => sub w (hpa w hw)⟩
  -- Coq `ccRwalk`
  have ccRwalk : ∀ (q : Question) (x : Dc) (a : List Dc), x ∈ Gc.fband a →
      Gc.edge x ∈ Gc.fband a → (∀ y ∈ a, y ∈ Gc.kernel rc) →
      Gc.RLinkConnected (Gc.fband a ∩ hc) →
      (∀ y ∈ Gc.walkq (Gc.node x) q, y ∈ Gc.kernel rc ∩ hc) →
      Gc.RLinkConnected (Gc.fband (a ++ Gc.walkq (Gc.node x) q) ∩ hc) := by
    intro q
    induction q with
    | Qask0 =>
      intro x a _ _ _ ccRa _
      simpa only [walkq, List.append_nil] using ccRa
    | Qask1 qa =>
      intro x a aFx _ _ ccRa hs
      exact ccRfband x a aFx ccRa (hs _ List.mem_cons_self).2
    | QaskL qa ql ih =>
      intro x a aFx aFex a_ac ccRa hs
      have hnx := hs (Gc.node x) List.mem_cons_self
      have e : a ++ Gc.walkq (Gc.node x) (QaskL qa ql) =
          (a ++ [Gc.node x]) ++ Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.node x)))) ql := by
        rw [List.append_assoc]
        rfl
      rw [e]
      refine ih _ _ ((Gc.fband_rcons _ _ _).2 (Or.inl (cfEN _))) ?_ ?_
        (ccRfband x a aFx ccRa hnx.2) (fun y hy => hs y (List.mem_cons_of_mem _ hy))
      · rw [e2c, nn_c' x hnx.1]
        exact (Gc.fband_rcons _ _ _).2 (Or.inr ((fbF a _).1 aFex))
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact a_ac y hy
        · rw [List.mem_singleton.1 hy]
          exact hnx.1
    | QaskR qa qr ih =>
      intro x a aFx aFex a_ac ccRa hs
      have hnx := hs (Gc.node x) List.mem_cons_self
      have e : a ++ Gc.walkq (Gc.node x) (QaskR qa qr) =
          (a ++ [Gc.node x]) ++ Gc.walkq (Gc.node (Gc.edge (Gc.node x))) qr := by
        rw [List.append_assoc]
        rfl
      rw [e]
      refine ih _ _ ?_ ?_ ?_ (ccRfband x a aFx ccRa hnx.2)
        (fun y hy => hs y (List.mem_cons_of_mem _ hy))
      · exact (Gc.fband_rcons _ _ _).2 (Or.inr ((fbF a _).2 (by rw [Gc.nodeK]; exact aFx)))
      · rw [e2c]
        exact (Gc.fband_rcons _ _ _).2 (Or.inl (connect_refl _))
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact a_ac y hy
        · rw [List.mem_singleton.1 hy]
          exact hnx.1
    | QaskLR qa ql qr ihl ihr =>
      intro x a aFx aFex a_ac ccRa hs
      have hnx := hs (Gc.node x) List.mem_cons_self
      have hs_l : ∀ y ∈ Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.node x)))) ql,
          y ∈ Gc.kernel rc ∩ hc :=
        fun y hy => hs y (List.mem_cons_of_mem _ (List.mem_append_left _ hy))
      have hs_r : ∀ y ∈ Gc.walkq (Gc.node (Gc.edge (Gc.node x))) qr,
          y ∈ Gc.kernel rc ∩ hc :=
        fun y hy => hs y (List.mem_cons_of_mem _ (List.mem_append_right _ hy))
      have e : a ++ Gc.walkq (Gc.node x) (QaskLR qa ql qr) =
          ((a ++ [Gc.node x]) ++ Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.node x)))) ql) ++
            Gc.walkq (Gc.node (Gc.edge (Gc.node x))) qr := by
        rw [List.append_assoc, List.append_assoc]
        rfl
      rw [e]
      have a1_ac : ∀ y ∈ a ++ [Gc.node x], y ∈ Gc.kernel rc := by
        intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact a_ac y hy
        · rw [List.mem_singleton.1 hy]
          exact hnx.1
      have ccR1 := ihl _ (a ++ [Gc.node x]) ((Gc.fband_rcons _ _ _).2 (Or.inl (cfEN _)))
        (by
          rw [e2c, nn_c' x hnx.1]
          exact (Gc.fband_rcons _ _ _).2 (Or.inr ((fbF a _).1 aFex)))
        a1_ac (ccRfband x a aFx ccRa hnx.2) hs_l
      refine ihr _ _ ?_ ?_ ?_ ccR1 hs_r
      · exact (Gc.fband_cat _ _ _).2 (Or.inl ((Gc.fband_rcons _ _ _).2
          (Or.inr ((fbF a _).2 (by rw [Gc.nodeK]; exact aFx)))))
      · rw [e2c]
        exact (Gc.fband_cat _ _ _).2 (Or.inl ((Gc.fband_rcons _ _ _).2 (Or.inl (connect_refl _))))
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact a1_ac y hy
        · exact (hs_l y hy).1
    | QaskLL qa qll ih =>
      intro x a aFx aFex a_ac ccRa hs
      have hx' := hs _ List.mem_cons_self
      have ac_ex : Gc.edge x ∈ Gc.kernel rc := ac_of_fband a a_ac _ aFex
      have ac_fex : Gc.face (Gc.edge x) ∈ Gc.kernel rc := (acF _).1 ac_ex
      have ac_ffex : Gc.face (Gc.face (Gc.edge x)) ∈ Gc.kernel rc := (acF _).1 ac_fex
      have hnn : Gc.node (Gc.node x) = Gc.face (Gc.edge x) := by
        have := n3c _ ac_fex
        rwa [Gc.edgeK] at this
      have Dffex : Gc.node (Gc.qstepL (Gc.node x)) = Gc.face (Gc.face (Gc.edge x)) := by
        show Gc.node (Gc.node (Gc.edge (Gc.node (Gc.node x)))) = _
        rw [hnn, ← Gc.plain_eq' geoGc.plain (Gc.face (Gc.edge x))]
        exact n3c _ ac_ffex
      have e : a ++ Gc.walkq (Gc.node x) (QaskLL qa qll) =
          (a ++ [Gc.edge (Gc.node (Gc.qstepL (Gc.node x)))]) ++
            Gc.walkq (Gc.node (Gc.edge (Gc.node (Gc.qstepL (Gc.node x))))) qll := by
        rw [List.append_assoc]
        rfl
      rw [e]
      have ex' : Gc.edge (Gc.node (Gc.qstepL (Gc.node x))) =
          Gc.node (Gc.face (Gc.face (Gc.face (Gc.edge x)))) := by
        rw [Dffex, Gc.plain_eq' geoGc.plain]
      refine ih _ _ ((Gc.fband_rcons _ _ _).2 (Or.inl (connect_refl _))) ?_ ?_ ?_
        (fun y hy => hs y (List.mem_cons_of_mem _ hy))
      · rw [e2c, Dffex]
        exact (Gc.fband_rcons _ _ _).2 (Or.inr ((fbF a _).1 ((fbF a _).1 aFex)))
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact a_ac y hy
        · rw [List.mem_singleton.1 hy]
          exact hx'.1
      · rw [ex'] at hx' ⊢
        exact ccRfband _ a ((fbF a _).1 ((fbF a _).1 ((fbF a _).1 aFex))) ccRa hx'.2
    | QaskRR qa qrr ih =>
      intro x a aFx aFex a_ac ccRa hs
      have hr := hs _ List.mem_cons_self
      have e : a ++ Gc.walkq (Gc.node x) (QaskRR qa qrr) =
          (a ++ [Gc.qstepR (Gc.node x)]) ++
            Gc.walkq (Gc.node (Gc.edge (Gc.qstepR (Gc.node x)))) qrr := by
        rw [List.append_assoc]
        rfl
      rw [e]
      refine ih _ _ ?_ ?_ ?_ ?_ (fun y hy => hs y (List.mem_cons_of_mem _ hy))
      · refine (Gc.fband_rcons _ _ _).2 (Or.inr ?_)
        rw [fbF, fbF]
        show Gc.face (Gc.face (Gc.edge (Gc.node (Gc.edge (Gc.node x))))) ∈ Gc.fband a
        rw [Gc.nodeK, Gc.nodeK]
        exact aFx
      · rw [e2c]
        exact (Gc.fband_rcons _ _ _).2 (Or.inl (connect_refl _))
      · intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact a_ac y hy
        · rw [List.mem_singleton.1 hy]
          exact hr.1
      · exact ccRfband (Gc.edge (Gc.node x)) a ((fbF a _).2 (by rw [Gc.nodeK]; exact aFx)) ccRa
          hr.2
  have all_s0 : ∀ y ∈ Gc.walkqz x0c ⟨QaskR qa0 q01, QaskR qa1 q10⟩,
      y ∈ Gc.kernel rc ∩ hc :=
    fun y hy => ⟨s0_ac y hy, hcent y hy⟩
  have e10 : Gc.qstepR (Gc.edge x0c) = Gc.node x0c := by rw [qstepR, e2c]
  simp only [walkqz, walkq, e10, List.cons_append, List.mem_cons, List.mem_append] at all_s0
  have hx0 := all_s0 x0c (Or.inl rfl)
  have hex0 := all_s0 (Gc.edge x0c) (Or.inr (Or.inr (Or.inl rfl)))
  have h01 : ∀ y ∈ Gc.walkq (Gc.node (Gc.edge x0c)) q01, y ∈ Gc.kernel rc ∩ hc :=
    fun y hy => all_s0 y (Or.inr (Or.inl hy))
  have h10 : ∀ y ∈ Gc.walkq (Gc.node x0c) q10, y ∈ Gc.kernel rc ∩ hc :=
    fun y hy => all_s0 y (Or.inr (Or.inr (Or.inr hy)))
  have ccR0 : Gc.RLinkConnected (Gc.fband [x0c] ∩ hc) := by
    rintro y ⟨hy, -⟩ z ⟨hz, -⟩
    have hy' : Gc.cface y x0c := by simpa [Gc.fband_cons, mem_fband] using hy
    have hz' : Gc.cface z x0c := by simpa [Gc.fband_cons, mem_fband] using hz
    refine ⟨[], ⟨?_, trivial⟩, fun w hw => absurd hw List.not_mem_nil⟩
    show Gc.cface (Gc.edge (Gc.node (Gc.face y))) z
    rw [Gc.faceK]
    exact connect_trans hy' (Gc.cfaceC.1 hz')
  have ccR1 : Gc.RLinkConnected (Gc.fband [x0c, Gc.edge x0c] ∩ hc) := by
    have e : [x0c, Gc.edge x0c] = [x0c] ++ [Gc.node (Gc.face x0c)] := by
      rw [Gc.plain_eq' geoGc.plain]
      rfl
    rw [e]
    refine ccRfband (Gc.face x0c) [x0c] ?_ ccR0 ?_
    · exact (Gc.fband_cons _ _ _).2 (Or.inl (Gc.cfaceC.1 (fconnect1 _ _)))
    · rw [Gc.plain_eq' geoGc.plain]
      exact hex0.2
  have ccRa := ccRwalk q01 (Gc.edge x0c) [x0c, Gc.edge x0c]
    (Gc.ring_fband _ _ (by simp)) (by rw [e2c]; exact Gc.ring_fband _ _ (by simp))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro y (rfl | rfl)
        · exact hx0.1
        · exact hex0.1)
    ccR1 h01
  have ccRa2 := ccRwalk q10 x0c ([x0c, Gc.edge x0c] ++ Gc.walkq (Gc.node (Gc.edge x0c)) q01)
    (Gc.ring_fband _ _ (by simp)) (Gc.ring_fband _ _ (by simp))
    (by
      intro y hy
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hy
      rcases hy with rfl | rfl | hy
      · exact hx0.1
      · exact hex0.1
      · exact (h01 y hy).1)
    ccRa h10
  have hmem : ∀ z, z ∈ Gc.walkqz x0c ⟨QaskR qa0 q01, QaskR qa1 q10⟩ ↔
      z ∈ ([x0c, Gc.edge x0c] ++ Gc.walkq (Gc.node (Gc.edge x0c)) q01) ++
        Gc.walkq (Gc.node x0c) q10 := by
    intro z
    simp only [walkqz, walkq, qstepR, e2c, List.cons_append, List.nil_append, List.mem_cons,
      List.mem_append]
    tauto
  have Dac : Gc.kernel rc =
      Gc.fband (([x0c, Gc.edge x0c] ++ Gc.walkq (Gc.node (Gc.edge x0c)) q01) ++
        Gc.walkq (Gc.node x0c) q10) := by
    rw [← qz_ok.fband_eq]
    ext z
    exact exists_congr fun w => and_congr_left' (hmem w)
  rw [Dac]
  exact ccRa2

/-- Coq `quiz_preembedding`: a quiz valid for the configuration `Gc` with ring `rc` at `x0c`, that
fits the plain cubic map `Gm` at `x0m`, yields a preembedding of `kernel rc` into `Gm`. -/
theorem quiz_preembedding (geoGm : Gm.PlainCubic) (geoGc : Gc.PlainQuasicubic rc)
    (qz_ok : Gc.ValidQuiz rc x0c qz) (qz_x0m : Gm.fitqz x0m qz) :
    Gc.Preembedding Gm (Gc.kernel rc) (embedqz Gm Gc x0m x0c qz) where
  face := embedqz_face qz_ok qz_x0m
  arity := fun _ hx => embedqz_arity qz_ok qz_x0m hx
  cover := by
    intro x hx
    rw [← qz_ok.fband_eq] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    exact ⟨y, embedqz_central geoGm geoGc qz_ok qz_x0m y hy, hxy⟩
  rlinked := embedqz_rlinked geoGm geoGc qz_ok qz_x0m

end QuizEmbedding

end Hypermap

end FourColor
