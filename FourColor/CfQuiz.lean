/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Quiz
import FourColor.CfMap

/-!
# Configuration quizzes  (port of `cfquiz.v`)

Compile the quiz that tests for the occurrence of a configuration. Since this requires to
compute arities, we also check that the arity of ring regions are in the `[3,6]` range along
the way. The procedure here is valid but not complete, e.g., it assumes that skews only occur
at articulations. The configuration data has been carefully knobbed to meet this constraint.

The algorithm walks the map construction program backwards, keeping track of kernel faces and
of arities on the submap ring. During the traversal a list of questions is kept, that covers
exactly the kernel faces that are disjoint from the current submap ring.

Each of these questions is rooted at `node (ic x)` for some dart `x` of the submap ring, where
`ic` is the injection from the current submap to the full configuration map (crucially, this
implies that `node` is computed in the full map). As the ring shrinks, questions are linked to
form trees, until we arrive at the initial two-dart graph, where we have just two questions that
form a proper quiz.

H-type steps could be somewhat of a problem for this algorithm, but it turns out that (with a
little fiddling) in all the programs we consider we never need to join trees in an H step, so
the code below doesn't handle that case (we'd need to generate more LL and RR questions).

## Definitions

* `cpradius2 cp i`   : the kernel of `cpmap cp` has radius at most 2 (we test each of the first
  `i` kernel faces as a possible hub).
* `noquiz`           : an invalid quiz (fails `isQuizR`).
* `cfquiz cf`        : a valid quiz that tests for embedding of a copy of `cfmap cf`, or `noquiz`
  if `cfprog cf` is not a `configProg`, has radius > 2, bad ring or kernel face arities, or
  encounters an unhandled case.

We check dynamically that `cfquiz cf` returns a quiz satisfying `isQuizR` for each of the 633
configuration programs we use. We show here that this guarantees that `cfquiz cf` is valid for
`cfring cf` at some dart in `cfmap cf`, and that `cfring cf` is embeddable with a kernel that has
radius at most 2.

* `largeQarity a`    : the qarity value corresponding to `a + 2`.
* `smallQarity a`    : the qarity value corresponding to `a + 2` if `a + 2 ∈ [5,8]`, and some
  DIFFERENT qarity greater than 8 otherwise.
* `badSmallArity qa` : the qarity `qa` is greater than 8.
* `badRingArity a`   : `a + 2` is not in the `[3,6]` range for ring face arities.
* `RingQuestion`     : record type for the question testing kernel faces from a dart on the
  perimeter ring of an intermediate stage of the map construction. It contains a question
  (`nodeQuestion`), the outer arity of the dart (`outerArity`, the number of adjacent faces NOT
  in the submap), and a flag `isKernel` indicating whether the dart is in the kernel of the
  final map. (In Coq it coerces to both a `question` and a `nat`.)
* `cfquizRec qs cp`  : recursive configuration quiz generation, from a sequence `qs` of
  `RingQuestion`s testing for the faces created by the start of its `cfprog`, and `cp`, the rest
  of its `cfprog` (recall `cp` is executed first).
* `rqsY rq1 rq3 qs q1'` : the `RingQuestion` sequence for a `Y` step, when the previous sequence
  was `rq1 :: _ :: rq3 :: qs`, and `q1'` is the new question for the first ring face.
* `cfquizY rq1 rq2 kqs` : computes the ring question for the first ring face of a `Y` step,
  given the first two ring questions, and passes it to `kqs` (which will be a partly applied
  `rqsY`) or fails with `[]`.
* `rqsH rq1 rq3 qs q1' q2'`, `cfquizH rq1 rq2 kqs` : similar functions for `H`.
* `RqsFit G0 G h qs p` : `p.map h` fits the `RingQuestion` sequence `qs`: each `h x` in
  `p.map h` fits the corresponding `q` in `qs` (at `node (h x)`), and has arity
  `q.outerArity + arity x` (Coq `rqs_fit`).
* `rqsWalk G0 qs p`  : the darts visited by the questions of `qs` asked at the nodes of the darts
  of `p`, each preceded by the dart itself if its question is a kernel one (Coq `rqs_walk`).
* `RqsProper G0 G h qs` : the invariant of the quiz construction (Coq `rqs_proper`).

## Main results

For a configuration `cf` with `qzR : isQuizR (cfquiz cf) = true` (the Coq section hypothesis
`qzR`):

* `cpradius2P qzR`        : `radius2 (kernel (cfring cf))`;
* `cfquizP qzR`           : the ring faces of `cpmap cf.cfprog` have good arities, and
  `cfquiz cf` is a valid quiz for `cpring (cpmap cf.cfprog)` at some dart;
* `embeddable_cfquiz qzR` : `cfring cf` is embeddable;
* `valid_cfquiz qzR`      : `cfquiz cf` is a valid quiz for `cfring cf` at some dart.

## Porting notes

* The computational definitions (`smallQarity`, `badSmallArity`, `largeQarity`, `badRingArity`,
  `noquiz`, `rqsY`, `cfquizY`, `rqsH`, `cfquizH`, `cfquizRec`, `cpradius2`, `cfquiz`) are
  first-order (except for the continuation arguments of `cfquizY`/`cfquizH`, as in Coq) and
  structurally recursive, so that they reduce in the kernel (`decide +kernel`).
* The Coq record `ring_question` is the structure `RingQuestion` with constructor
  `RingQuestion.mk`; its coercions to `nat` and `question` are the projections `outerArity`
  and `nodeQuestion`, and `ring_question_is_kernel` is `isKernel`.
* `rqs_fit` and `rqs_proper` involve arities, which are not computable here, so they are the
  `Prop`s `RqsFit` and `RqsProper`; `rqs_proper`, a `[/\ _, _, _ & _]` conjunction, is a
  structure with fields `fit`, `ring`, `simple` and `fband_eq`, where `fband_eq` is a set
  equality. The Coq section `RqsWalk` is parametrized by pointed maps `G0 G` and `h : G → G0`;
  `RqsFit` and `rqsWalk` only use the underlying hypermaps (so they take the hypermaps, and
  `rqsWalk` only `G0`), while `RqsProper` uses the pointed maps (for their rings).
* math-comp's `codom h` is `Set.range h`, and `nseq (isk rq) u` is
  `List.replicate rq.isKernel.toNat u`.
* The Coq section `ConfigQuiz` has the variable `cf` and the hypothesis `qzR`; here `cf` is an
  implicit argument and `qzR` an explicit one of `cpradius2P`, `cfquizP`, `embeddable_cfquiz`
  and `valid_cfquiz` (`cfquiz` takes `cf` explicitly). The section `Let`s `noquiz` (a public
  definition), `cp_rad2`, `qs0_notR` and `cp_ok` (private theorems) are kept.
* The long Coq proof of `cfquizP` (an induction on the program, with one case per construction
  step) is split into private lemmas: `rqsProper_init` (the initial invariant), `cfquiz_base`
  (the empty program), `rqsProper_R`, `rqsProper_Y` and `rqsProper_H` (the `R`, `Y` and `H`
  steps) and `cfquizP_rec` (the induction). The parts common to the `Y` and `H` steps are
  factored out as private lemmas: the arity count `nFiG` (`arity_inj`, used by `arity_icpY` and
  `arity_icpH`), the face-closure `outY1F`/`rH1F` (`closed_range_band`), the band equations
  `EpY1`/`EpH1` (`band_step`) and the ring arity facts `nFr0_Y1`/`nFr0_H1` (`ring_step`). The
  case analyses of `cfquiz_Y` and `cfquiz_H` are done once in `cfquizY_kernel`, `cfquizY_ring`,
  `cfquizH_kernel` and `cfquizH_ring` (the Coq `simq`/`selq` devices become `yq_sim` and
  explicit `flatq`/`walkq` equalities). Where Coq proves equalities of face bands with `=i`
  and `eq_simple`, we do the same with `Hypermap.eq_simple`.
-/

namespace FourColor

open Function CfMap Hypermap

/-! ### Ring questions -/

/-- Coq `ring_question`: a question testing kernel faces from a dart on the perimeter ring of an
intermediate stage of the map construction (we use a single sequence of records rather than
three parallel sequences). -/
structure RingQuestion : Type where
  /-- Coq constructor `RingQuestion`. -/
  mk ::
  /-- Coq `ring_question_is_kernel`: whether the dart is in the kernel of the final map. -/
  isKernel : Bool
  /-- Coq `ring_question_outer_arity` (a coercion to `nat` in Coq): the number of adjacent
  faces NOT in the submap. -/
  outerArity : ℕ
  /-- Coq `ring_question_node_question` (a coercion to `question` in Coq). -/
  nodeQuestion : Question
  deriving DecidableEq, Repr, Inhabited

/-! ### Arity checks

We only compile questions for maps with kernel arities between 5 and 11; in fact only the most
central face (the one to which the "true" dart of the central submap belongs) can have more than
8 sides. We check and use this fact during the compilation. We also check that the ring arities
are in the 3..6 range; this property allows us to lift the preembedding constructed in `quiz.v`
into an actual embedding (see `embed.v`). All the functions below work with the arities offset
by two, because each time a face is detached from the submap, it had at least two neighbors in
that submap. -/

/-- Coq `small_qarity a`: the qarity value corresponding to `a + 2` if `a + 2 ∈ [5,8]`, and some
different qarity greater than 8 otherwise. -/
def smallQarity : ℕ → Qarity
  | 3 => Qa5
  | 4 => Qa6
  | 5 => Qa7
  | 6 => Qa8
  | 7 => Qa10
  | _ => Qa9

/-- Coq `bad_small_arity qa`: the qarity `qa` is greater than 8. -/
def badSmallArity : Qarity → Bool
  | Qa9 => true
  | Qa10 => true
  | Qa11 => true
  | _ => false

/-- Coq `small_qarityP`. -/
theorem small_qarityP (a : ℕ) :
    badSmallArity (smallQarity a) = ((smallQarity a : ℕ) != a + 2) := by
  match a with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl
  | a + 8 =>
    show badSmallArity Qa9 = ((9 : ℕ) != a + 8 + 2)
    simp [badSmallArity]

/-- Coq `large_qarity a`: the qarity value corresponding to `a + 2`. -/
def largeQarity : ℕ → Qarity
  | 7 => Qa9
  | 8 => Qa10
  | 9 => Qa11
  | a => smallQarity a

/-- Coq `bad_ring_arity a`: `a + 2` is not in the `[3,6]` range for ring face arities
(`match a with 0 | _.+4.+1 => true | _ => false end`). -/
def badRingArity : ℕ → Bool
  | 0 => true
  | _ + 5 => true
  | _ => false

/-- Coq `not_bad_ring_arity`. -/
theorem not_bad_ring_arity {D : Type*} [Finite D] (G : Hypermap D) (x : D)
    (h : badRingArity (G.arity x - 2) = false) : G.GoodRingArity x := by
  rw [goodRingArity_iff]
  generalize G.arity x = n at h ⊢
  match n, h with
  | 3, _ | 4, _ | 5, _ | 6, _ => omega

/-- Coq `noquiz` (a section `Let`): an invalid quiz (it fails `isQuizR`). -/
def noquiz : Quiz := ⟨Qask0, Qask0⟩

/-! ### The quiz construction proper -/

/-- Coq `rqs_Y rq1 rq3 qs q1'`: the ring question sequence for a `Y` step, when the previous
sequence was `rq1 :: _ :: rq3 :: qs`, and `q1'` is the new question for the first ring face. -/
def rqsY (rq1 rq3 : RingQuestion) (qs : List RingQuestion) (q1' : Question) :
    List RingQuestion :=
  match rq1, rq3 with
  | ⟨k1, a1, _⟩, ⟨k3, a3, q3⟩ => ⟨k1, a1 + 1, q1'⟩ :: ⟨k3, a3 + 1, q3⟩ :: qs

/-- Coq `cfquiz_Y rq1 rq2 rqs'`: computes the ring question for the first ring face of a `Y`
step, given the first two ring questions, and passes it to `rqs'`, or fails with `[]`. -/
def cfquizY (rq1 rq2 : RingQuestion) (rqs' : Question → List RingQuestion) :
    List RingQuestion :=
  match rq1, rq2 with
  | ⟨_, _, q1⟩, ⟨k2, a2, q2⟩ =>
    if k2 then
      let qa2 := smallQarity a2
      if badSmallArity qa2 then [] else
      rqs' (match q1, q2 with
        | Qask0, Qask0 => Qask1 qa2
        | Qask0, _ => QaskL qa2 q2
        | _, Qask0 => QaskR qa2 q1
        | _, _ => QaskLR qa2 q2 q1)
    else
      if badRingArity a2 then [] else
      match q1, q2 with
      | Qask0, Qask0 => rqs' Qask0
      | QaskR qa1 q1r, Qask0 => rqs' (QaskRR qa1 q1r)
      | Qask0, QaskL qa1 q1l => rqs' (QaskLL qa1 q1l)
      | _, _ => []

/-- Coq `rqs_H rq1 rq3 qs q1' q2'`: the ring question sequence for an `H` step, when the previous
sequence was `rq1 :: _ :: rq3 :: qs`, and `q1'`, `q2'` are the new questions for the first two
ring faces. -/
def rqsH (rq1 rq3 : RingQuestion) (qs : List RingQuestion) (q1' q2' : Question) :
    List RingQuestion :=
  match rq1, rq3 with
  | ⟨k1, a1, _⟩, ⟨k3, a3, q3⟩ =>
    ⟨k1, a1 + 1, q1'⟩ :: ⟨true, 1, q2'⟩ :: ⟨k3, a3 + 1, q3⟩ :: qs

/-- Coq `cfquiz_H rq1 rq2 rqs'`: computes the ring questions for the first two ring faces of an
`H` step, given the first two ring questions, and passes them to `rqs'`, or fails with `[]`. -/
def cfquizH (rq1 rq2 : RingQuestion) (rqs' : Question → Question → List RingQuestion) :
    List RingQuestion :=
  match rq1, rq2 with
  | ⟨k1, _, q1⟩, ⟨k2, a2, q2⟩ =>
    if k2 then
      let qa2 := smallQarity (a2 + 1)
      if badSmallArity qa2 then [] else
      match q1, q2, k1 with
      | Qask0, Qask0, true => rqs' (Qask1 qa2) q2
      | Qask0, Qask0, _ => rqs' q1 (Qask1 qa2)
      | Qask0, _, _ => rqs' q1 (QaskL qa2 q2)
      | _, Qask0, _ => rqs' (QaskR qa2 q1) q2
      | _, _, _ => []
    else
      if badRingArity (a2 + 1) then [] else
      match q1, q2 with
      | Qask0, Qask0 => rqs' q1 q2
      | _, _ => []

/-- Coq `cfquiz_rec qs cp`: recursive configuration quiz generation, from a sequence `qs` of ring
questions testing for the faces created by the start of the configuration program, and `cp`,
the rest of the program (recall `cp` is executed first). -/
def cfquizRec : List RingQuestion → Cprog → Quiz
  | rq1 :: rq2 :: _, [] =>
    match rq1, rq2 with
    | ⟨k1, a1, q1⟩, ⟨k2, a2, q2⟩ =>
      if !(k1 && k2) then noquiz else
      let qa1 := largeQarity (a1 - 1)
      let qa2 := smallQarity (a2 - 1)
      if ((qa1 : ℕ) != a1 + 1) || badSmallArity qa2 then noquiz else
      ⟨QaskR qa1 q2, QaskR qa2 q1⟩
  | qs@(rq1 :: rq2 :: rq3 :: qs'), s :: cp' =>
    match s with
    | .R n => cfquizRec (rotr n qs) cp'
    | .Y => cfquizRec (cfquizY rq1 rq2 (rqsY rq1 rq3 qs')) cp'
    | .H => cfquizRec (cfquizH rq1 rq2 (rqsH rq1 rq3 qs')) cp'
    | _ => noquiz
  | _, _ => noquiz

/-! ### Radius check

We check separately the radius of the configuration (the initial face of the quiz might not be
at the center of the kernel). -/

/-- Coq `cpradius2 cp i`: some of the first `i` faces of `cpker cp` is at distance at most 2 from
every kernel face (so the kernel of `cpmap cp` has radius at most 2). -/
def cpradius2 (cp : Cprog) : ℕ → Bool
  | 0 => false
  | i' + 1 =>
    let cm0 := cfmask1 cp i'
    match cm0 with
    | ⟨mr1, _⟩ =>
      match cpadj cm0 cp with
      | ⟨_, mk1⟩ =>
        match cpadj ⟨mr1, mk1⟩ cp with
        | ⟨_, mk2⟩ => if mk2.all id then true else cpradius2 cp i'

/-- Coq `cfquiz cf`: a valid quiz that tests for embedding of a copy of `cfmap cf`, or `noquiz`
if `cfprog cf` is not a `configProg`, has radius > 2, bad ring or kernel face arities, or
encounters an unhandled case. -/
def cfquiz (cf : Config) : Quiz :=
  let cp := cf.cfprog
  if cpradius2 cp (cpksize cp) then
    cfquizRec (List.replicate (cprsize cp) ⟨false, 0, Qask0⟩) cp
  else noquiz

/-! ### Fitting ring question sequences (Coq section `RqsWalk`) -/

section RqsWalk

variable {D0 D : Type*} (G0 : Hypermap D0) (G : Hypermap D) (h : D → D0)

/-- Coq `rqs_fit h qs p`: `p.map h` fits the ring question sequence `qs`: each `h x` fits the
corresponding question `q` of `qs` (at `node (h x)`), and has arity `q.outerArity + arity x`. -/
def RqsFit : List RingQuestion → List D → Prop
  | rq :: qs, x :: p =>
    G0.arity (h x) = rq.outerArity + G.arity x ∧ G0.fitq (G0.node (h x)) rq.nodeQuestion ∧
      RqsFit qs p
  | [], [] => True
  | _, _ => False

/-- Coq `rqs_fit_cons`. -/
theorem rqs_fit_cons (rq : RingQuestion) (qs : List RingQuestion) (x : D) (p : List D) :
    RqsFit G0 G h (rq :: qs) (x :: p) ↔
      G0.arity (h x) = rq.outerArity + G.arity x ∧ G0.fitq (G0.node (h x)) rq.nodeQuestion ∧
        RqsFit G0 G h qs p :=
  Iff.rfl

/-- Coq `rqs_fit_size`. -/
theorem rqs_fit_size {qs : List RingQuestion} {p : List D} (hf : RqsFit G0 G h qs p) :
    qs.length = p.length := by
  induction qs generalizing p with
  | nil => cases p with
    | nil => rfl
    | cons _ _ => exact hf.elim
  | cons rq qs ih => cases p with
    | nil => exact hf.elim
    | cons x p => simp [ih hf.2.2]

/-- Coq `rqs_walk qs p`: the darts visited by the questions of `qs` asked at the nodes of the
darts of `p`, each preceded by the dart itself if its question is a kernel one (Coq
`nseq (isk rq) u` is `List.replicate rq.isKernel.toNat u`). -/
def rqsWalk : List RingQuestion → List D0 → List D0
  | rq :: qs, u :: p =>
    List.replicate rq.isKernel.toNat u ++ (G0.walkq (G0.node u) rq.nodeQuestion ++ rqsWalk qs p)
  | _, _ => []

/-- Coq `rqs_walk_cons`. -/
theorem rqs_walk_cons (rq : RingQuestion) (qs : List RingQuestion) (u : D0) (p : List D0) :
    rqsWalk G0 (rq :: qs) (u :: p) =
      List.replicate rq.isKernel.toNat u ++ (G0.walkq (G0.node u) rq.nodeQuestion ++ rqsWalk G0 qs p) :=
  rfl

end RqsWalk

/-- Coq `rqs_proper qs` (a `[/\ _, _, _ & _]` conjunction in Coq), for pointed maps `G0`, `G`
and `h : G → G0`, with `r0 := cpring G0`, `r := cpring G` and `hr := map h r`: `qs` fits `hr`,
the faces of `r0` that are neither in the image of `h` nor in `fband hr` have good ring arities,
`rqs_walk qs hr ++ r0` is simple, and its face band consists of the faces outside the image of
`h`, and those of `hr`. -/
structure RqsProper (G0 G : PointedMap) (h : G.D → G0.D) (qs : List RingQuestion) : Prop where
  /-- `rqs_fit qs r`. -/
  fit : RqsFit G0.pointee G.pointee h qs (G.pointee.cpring G.pointer)
  /-- `{subset [predD r0 & [predU codom h & fband hr]] <= good_ring_arity}`. -/
  ring : ∀ x ∈ G0.pointee.cpring G0.pointer, x ∉ Set.range h →
    x ∉ G0.pointee.fband ((G.pointee.cpring G.pointer).map h) → G0.pointee.GoodRingArity x
  /-- `simple (rqs_walk qs hr ++ r0)`. -/
  simple : G0.pointee.Simple
    (rqsWalk G0.pointee qs ((G.pointee.cpring G.pointer).map h) ++ G0.pointee.cpring G0.pointer)
  /-- `fband (rqs_walk qs hr ++ r0) =i [predU [predC codom h] & fband hr]`. -/
  fband_eq : G0.pointee.fband
      (rqsWalk G0.pointee qs ((G.pointee.cpring G.pointer).map h) ++
        G0.pointee.cpring G0.pointer) =
    (Set.range h)ᶜ ∪ G0.pointee.fband ((G.pointee.cpring G.pointer).map h)

/-! ### Helper lemmas (not in Coq) -/

section Helpers

variable {D0 D : Type*}

/-- `rqs_fit` of concatenations. -/
private theorem rqsFit_append (G0 : Hypermap D0) (G : Hypermap D) (h : D → D0)
    {qs1 qs2 : List RingQuestion} {p1 p2 : List D} (hl : qs1.length = p1.length) :
    RqsFit G0 G h (qs1 ++ qs2) (p1 ++ p2) ↔ RqsFit G0 G h qs1 p1 ∧ RqsFit G0 G h qs2 p2 := by
  induction qs1 generalizing p1 with
  | nil =>
    cases p1 with
    | nil => simp [RqsFit]
    | cons _ _ => simp at hl
  | cons rq qs1 ih =>
    cases p1 with
    | nil => simp at hl
    | cons x p1 =>
      simp only [List.cons_append, rqs_fit_cons]
      rw [ih (by simpa using hl)]
      tauto

/-- `rqs_walk` of concatenations. -/
private theorem rqsWalk_append (G0 : Hypermap D0) {qs1 qs2 : List RingQuestion}
    {p1 p2 : List D0} (hl : qs1.length = p1.length) :
    rqsWalk G0 (qs1 ++ qs2) (p1 ++ p2) = rqsWalk G0 qs1 p1 ++ rqsWalk G0 qs2 p2 := by
  induction qs1 generalizing p1 with
  | nil =>
    cases p1 with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons rq qs1 ih =>
    cases p1 with
    | nil => simp at hl
    | cons x p1 =>
      simp only [List.cons_append, rqs_walk_cons, ih (by simpa using hl), List.append_assoc]

/-- `rqs_fit` of rotations. -/
private theorem rqsFit_rot (G0 : Hypermap D0) (G : Hypermap D) (h : D → D0) (n : ℕ)
    {qs : List RingQuestion} {p : List D} (hl : qs.length = p.length) :
    RqsFit G0 G h (rot n qs) (rot n p) ↔ RqsFit G0 G h qs p := by
  have e1 : (qs.drop n).length = (p.drop n).length := by simp [hl]
  have e2 : (qs.take n).length = (p.take n).length := by simp [hl]
  conv_rhs => rw [← List.take_append_drop n qs, ← List.take_append_drop n p]
  rw [rot, rot, rqsFit_append G0 G h e1, rqsFit_append G0 G h e2, and_comm]

/-- `rqs_walk` of rotations. -/
private theorem rqsWalk_rot_perm (G0 : Hypermap D0) (n : ℕ) {qs : List RingQuestion}
    {p : List D0} (hl : qs.length = p.length) :
    (rqsWalk G0 (rot n qs) (rot n p)).Perm (rqsWalk G0 qs p) := by
  have e1 : (qs.drop n).length = (p.drop n).length := by simp [hl]
  have e2 : (qs.take n).length = (p.take n).length := by simp [hl]
  have := rqsWalk_append G0 (qs2 := qs.drop n) (p2 := p.drop n) e2
  rw [List.take_append_drop, List.take_append_drop] at this
  rw [this, rot, rot, rqsWalk_append G0 e1]
  exact List.perm_append_comm

/-- `simple` is invariant under permutation. -/
private theorem simple_of_perm (G : Hypermap D) {p q : List D} (hpq : p.Perm q) :
    G.Simple p ↔ G.Simple q :=
  (hpq.map _).nodup_iff

/-- `fband` is invariant under permutation. -/
private theorem fband_of_perm (G : Hypermap D) {p q : List D} (hpq : p.Perm q) :
    G.fband p = G.fband q := by
  ext x
  simp only [Hypermap.mem_fband, hpq.mem_iff]

/-- A `Qask0` question always fits. -/
private theorem fitq_Qask0' (G : Hypermap D) (x : D) : G.fitq x Qask0 := rfl

/-- Unfolding `fitq` for `Qask1`. -/
private theorem fitq_Qask1' (G : Hypermap D) (x : D) (qa : Qarity) :
    G.fitq x (Qask1 qa) ↔ (qa : ℕ) = G.arity x := by
  simp [Hypermap.fitq, flatq, Hypermap.walkq]

/-- Unfolding `fitq` for a question with a head arity and a single subquestion. -/
private theorem fitq_head (G : Hypermap D) {x y z : D} {q q' : Question} {qa : Qarity}
    (hf : flatq q = (qa : ℕ) :: flatq q') (hw : G.walkq x q = y :: G.walkq z q') :
    G.fitq x q ↔ (qa : ℕ) = G.arity y ∧ G.fitq z q' := by
  simp only [Hypermap.fitq, hf, hw, List.map_cons, List.cons.injEq]

/-- Unfolding `fitq` for `QaskR`. -/
private theorem fitq_QaskR' (G : Hypermap D) (x : D) (qa : Qarity) (q : Question) :
    G.fitq x (QaskR qa q) ↔ (qa : ℕ) = G.arity x ∧ G.fitq (G.qstepR x) q :=
  fitq_head G rfl rfl

/-- Unfolding `fitq` for `QaskL`. -/
private theorem fitq_QaskL' (G : Hypermap D) (x : D) (qa : Qarity) (q : Question) :
    G.fitq x (QaskL qa q) ↔ (qa : ℕ) = G.arity x ∧ G.fitq (G.qstepL x) q :=
  fitq_head G rfl rfl

/-- Unfolding `fitq` for `QaskRR`. -/
private theorem fitq_QaskRR' (G : Hypermap D) (x : D) (qa : Qarity) (q : Question) :
    G.fitq x (QaskRR qa q) ↔
      (qa : ℕ) = G.arity (G.qstepR x) ∧ G.fitq (G.qstepR (G.qstepR x)) q :=
  fitq_head G rfl rfl

/-- Unfolding `fitq` for `QaskLL`. -/
private theorem fitq_QaskLL' (G : Hypermap D) (x : D) (qa : Qarity) (q : Question) :
    G.fitq x (QaskLL qa q) ↔
      (qa : ℕ) = G.arity (G.edge (G.node (G.qstepL x))) ∧ G.fitq (G.qstepL (G.qstepL x)) q :=
  fitq_head G rfl rfl

/-- Unfolding `fitq` for `QaskLR`. -/
private theorem fitq_QaskLR' (G : Hypermap D) (x : D) (qa : Qarity) (ql qr : Question) :
    G.fitq x (QaskLR qa ql qr) ↔
      (qa : ℕ) = G.arity x ∧ G.fitq (G.qstepL x) ql ∧ G.fitq (G.qstepR x) qr := by
  simp only [Hypermap.fitq, flatq, Hypermap.walkq, List.map_cons, List.cons.injEq,
    List.map_append]
  apply and_congr_right'
  constructor
  · intro h
    exact List.append_inj h (by rw [List.length_map, Hypermap.size_walkq])
  · rintro ⟨h1, h2⟩
    rw [h1, h2]

/-- Unfolding `fitqz`. -/
private theorem fitqz_mk (G : Hypermap D) (x : D) (q0 q1 : Question) :
    G.fitqz x ⟨q0, q1⟩ ↔ G.fitq x q0 ∧ G.fitq (G.edge x) q1 := by
  simp only [Hypermap.fitqz, flatqz, Hypermap.walkqz, List.map_append]
  constructor
  · intro h
    exact List.append_inj h (by rw [List.length_map, Hypermap.size_walkq])
  · rintro ⟨h1, h2⟩
    rw [← h1, ← h2]

end Helpers

/-! ### Generic lemmas for the construction steps (not in Coq)

These factor out the parts of the Coq proof of `cfquizP` that are common to the `Y` and `H`
steps. -/

section StepLemmas

variable {D0 D D' : Type*}

/-- `fband` of a rotation. -/
private theorem fband_rot' (G : Hypermap D) (n : ℕ) (p : List D) :
    G.fband (rot n p) = G.fband p := by
  ext x
  simp only [Hypermap.mem_fband, mem_rot]

open Classical in
/-- The arity of an injected dart (the counting argument of the Coq `nFiG`): if the face of every
injected dart `i x` consists of injected darts and of darts of the simple sequence `b`, then its
arity is that of `x`, plus one if `i x` meets `b`. -/
private theorem arity_inj [Finite D] [Finite D'] (G : Hypermap D) (G' : Hypermap D') (i : D → D')
    (hi : Injective i) (hF : ∀ x y, G'.cface (i x) (i y) ↔ G.cface x y) {b : List D'}
    (hb : G'.Simple b) (hbi : ∀ u ∈ b, u ∉ Set.range i)
    (hcov : ∀ x u, G'.cface (i x) u → u ∈ b ∨ u ∈ Set.range i) (x : D) :
    G'.arity (i x) = (if i x ∈ G'.fband b then 1 else 0) + G.arity x := by
  have hS : {u | G'.cface (i x) u} = {u | G'.cface (i x) u ∧ u ∈ b} ∪ i '' {y | G.cface x y} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_image]
    constructor
    · intro hu
      rcases hcov x u hu with hub | ⟨y, rfl⟩
      · exact Or.inl ⟨hu, hub⟩
      · exact Or.inr ⟨y, (hF x y).1 hu, rfl⟩
    · rintro (⟨hu, _⟩ | ⟨y, hy, rfl⟩)
      · exact hu
      · exact (hF x y).2 hy
  have hdisj : Disjoint {u | G'.cface (i x) u ∧ u ∈ b} (i '' {y | G.cface x y}) := by
    rw [Set.disjoint_left]
    rintro u ⟨_, hub⟩ ⟨y, _, rfl⟩
    exact hbi _ hub ⟨y, rfl⟩
  show order G'.face (i x) = _ + order G.face x
  rw [order, order]
  change {u | G'.cface (i x) u}.ncard = _ + {y | G.cface x y}.ncard
  rw [hS, Set.ncard_union_eq hdisj, G'.predI_cface_simple (i x) hb,
    Set.ncard_image_of_injective _ hi]

/-- The face-closure of the set of darts outside the image of `h1`, or in the faces of
`r.map h1` (the Coq `outY1F` and `rH1F`). -/
private theorem closed_range_band [Finite D0] (G0 : Hypermap D0) (G : Hypermap D) (h1 : D → D0)
    (r : List D) (hE : ∀ x, h1 (G.edge x) = G0.edge (h1 x))
    (hN : ∀ x, x ∉ r → h1 (G.node x) = G0.node (h1 x)) :
    Closed (frel G0.face) ((Set.range h1)ᶜ ∪ G0.fband (r.map h1)) := by
  refine Closed.of_forward G0.cface_sym fun u v huv hu => ?_
  subst huv
  by_contra hv
  simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hv
  obtain ⟨⟨x, hx⟩, hxF⟩ := hv
  have hxr : x ∉ r := fun hxr => hxF (hx ▸ G0.ring_fband _ _ (List.mem_map_of_mem hxr))
  have hu' : u = h1 (G.edge (G.node x)) := by rw [hE, hN x hxr, hx, G0.faceK]
  rcases hu with hu | hu
  · exact hu ⟨_, hu'.symm⟩
  · exact hxF ((G0.fbandF _ u (G0.face u) rfl).1 hu)

/-- The face band of the new ring questions (the Coq `EpY1` and `EpH1`). -/
private theorem band_step [Finite D0] [Finite D'] (G0 : Hypermap D0) (G' : Hypermap D')
    (h : D' → D0) (i : D → D') (Ih : Injective h) (hF : ∀ x y, G0.cface (h x) (h y) ↔ G'.cface x y)
    (u0 : D') (hdich : ∀ w, (∃ y, G'.cface w (i y)) ∨ G'.cface u0 w)
    (hu0 : ∀ y, ¬ G'.cface u0 (i y)) {e rOld rNew : List D0}
    (hcl : Closed (frel G0.face) ((Set.range (h ∘ i))ᶜ ∪ G0.fband rNew))
    (hE : ∀ u, u ∈ G0.fband (e ++ rOld) ↔ G0.cface u (h u0) ∨ u ∈ G0.fband rNew) (u : D0) :
    (u ∈ G0.fband e ∨ u ∈ (Set.range h)ᶜ ∪ G0.fband rOld) ↔
      u ∈ (Set.range (h ∘ i))ᶜ ∪ G0.fband rNew := by
  by_cases hu : u ∈ Set.range h
  · obtain ⟨w, rfl⟩ := hu
    have hL : (h w ∈ G0.fband e ∨ h w ∈ (Set.range h)ᶜ ∪ G0.fband rOld) ↔
        h w ∈ G0.fband (e ++ rOld) := by
      simp [G0.fband_cat]
    rw [hL, hE]
    rcases hdich w with ⟨y, hwy⟩ | hw
    · have h1 : ¬ G0.cface (h w) (h u0) := fun h' =>
        hu0 y (connect_trans (G'.cfaceC.1 ((hF _ _).1 h')) hwy)
      have hwy' : G0.cface (h w) (h (i y)) := (hF _ _).2 hwy
      rw [hcl.connect_iff hwy', (G0.fbandF rNew).connect_iff hwy']
      simp only [h1, false_or, Set.mem_union, Set.mem_compl_iff, Set.mem_range, Function.comp,
        exists_apply_eq_apply, not_true_eq_false]
    · refine iff_of_true (Or.inl ((hF _ _).2 (G'.cfaceC.1 hw))) (Or.inl ?_)
      rintro ⟨y, hy⟩
      exact hu0 y (Ih hy ▸ hw)
  · have h1 : u ∉ Set.range (h ∘ i) := fun ⟨y, hy⟩ => hu ⟨i y, hy⟩
    simp only [Set.mem_union, Set.mem_compl_iff, hu, h1, not_false_eq_true, true_or, or_true]

/-- The good ring arities of the new ring questions (the Coq `nFr0_Y1` and `nFr0_H1`). -/
private theorem ring_step [Finite D0] (G0 : Hypermap D0) (h : D' → D0) (S : Set D0) (u0 : D')
    {r0 e rOld rNew : List D0}
    (hold : ∀ x ∈ r0, x ∉ Set.range h → x ∉ G0.fband rOld → G0.GoodRingArity x)
    (hstep : ∀ u, (u ∈ G0.fband e ∨ u ∈ (Set.range h)ᶜ ∪ G0.fband rOld) ↔ u ∈ Sᶜ ∪ G0.fband rNew)
    (hE : ∀ u, u ∈ G0.fband (e ++ rOld) ↔ G0.cface u (h u0) ∨ u ∈ G0.fband rNew)
    (hu0 : ∀ u ∈ r0, G0.cface (h u0) u → G0.GoodRingArity u) :
    ∀ x ∈ r0, x ∉ S → x ∉ G0.fband rNew → G0.GoodRingArity x := by
  intro u hu hS hF
  by_cases hu0u : G0.cface (h u0) u
  · exact hu0 u hu hu0u
  have h1 : u ∉ G0.fband (e ++ rOld) := by
    rw [hE]
    rintro (h' | h')
    · exact hu0u (G0.cfaceC.1 h')
    · exact hF h'
  rw [G0.fband_cat, not_or] at h1
  have h2 := (hstep u).2 (Or.inl hS)
  simp only [h1.1, h1.2, Set.mem_union, Set.mem_compl_iff, false_or, or_false] at h2
  exact hold u hu h2 h1.2

end StepLemmas

/-! ### The steps of the quiz construction (the cases of the Coq proof of `cfquizP`) -/

/-- The `R n` step of the Coq proof of `cfquizP`. -/
private theorem rqsProper_R (G0 G : PointedMap) (n : ℕ) (h : G.D → G0.D) {qs : List RingQuestion}
    (hp : RqsProper G0 (G.pointee.ecpR n G.pointer) h qs) : RqsProper G0 G h (rotr n qs) := by
  obtain ⟨hfit, hring, hsimple, hband⟩ := hp
  have hr : (G.pointee.ecpR n G.pointer).pointee.cpring (G.pointee.ecpR n G.pointer).pointer =
      rot n (G.pointee.cpring G.pointer) := G.pointee.cpring_ecpR n G.pointer
  rw [hr] at hfit hring hsimple hband
  set r := G.pointee.cpring G.pointer
  set r0 := G0.pointee.cpring G0.pointer
  have hl : (rotr n qs).length = r.length := by
    rw [length_rotr, rqs_fit_size _ _ _ hfit, length_rot]
  have hqs : qs = rot n (rotr n qs) := (rot_rotr n qs).symm
  rw [hqs] at hfit hsimple hband
  rw [map_rot] at hsimple hband
  have hperm : (rqsWalk G0.pointee (rot n (rotr n qs)) (rot n (r.map h)) ++ r0).Perm
      (rqsWalk G0.pointee (rotr n qs) (r.map h) ++ r0) :=
    (rqsWalk_rot_perm G0.pointee n (by rw [hl, List.length_map])).append_right r0
  rw [map_rot, fband_rot'] at hring
  rw [fband_rot'] at hband
  refine ⟨(rqsFit_rot _ _ _ n hl).1 hfit, hring, (simple_of_perm _ hperm).1 hsimple, ?_⟩
  rw [← fband_of_perm _ hperm, hband]

/-- The initial ring question sequence (the start of the Coq proof of `cfquizP`). -/
private theorem rqsProper_init {cp : Cprog} (hcp : configProg cp) :
    RqsProper (cpmap cp) (cpmap cp) id (List.replicate (cprsize cp) ⟨false, 0, Qask0⟩) := by
  set G := (cpmap cp).pointee
  set r := G.cpring (cpmap cp).pointer
  have hsz : cprsize cp = r.length := (size_ring_cpmap cp).symm
  have hwalk : ∀ l : List (cpmap cp).D,
      rqsWalk G (List.replicate l.length ⟨false, 0, Qask0⟩) l = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih => exact ih
  have hfit : ∀ l : List (cpmap cp).D,
      RqsFit G G id (List.replicate l.length ⟨false, 0, Qask0⟩) l := by
    intro l
    induction l with
    | nil => trivial
    | cons x l ih => exact ⟨(Nat.zero_add _).symm, fitq_Qask0' G _, ih⟩
  rw [hsz]
  refine ⟨hfit r, ?_, ?_, ?_⟩
  · intro x _ hx
    exact absurd ⟨x, rfl⟩ hx
  · rw [List.map_id, hwalk, List.nil_append]
    exact ((G.simple_cat _ _).1 (cpmap_simple hcp)).1
  · rw [List.map_id, hwalk, List.nil_append, Set.range_id, Set.compl_univ, Set.empty_union]

/-- The arity of the darts of the base map `cpmap0`. -/
private theorem arity_cpmap0 (b : Bool) : cpmap0.arity b = 1 := by
  have hc : fcycle cpmap0.face [b] := ⟨rfl, trivial⟩
  exact order_cycle hc (List.nodup_singleton b) List.mem_cons_self

/-- The base case of the Coq proof of `cfquizP`, for the empty program. -/
private theorem cfquiz_base (G0 G : PointedMap) (h : G.D → G0.D) (y0 y1 : G.D)
    (hr : G.pointee.cpring G.pointer = [y0, y1]) (ar0 : G.pointee.arity y0 = 1)
    (ar1 : G.pointee.arity y1 = 1) (e0 : G0.pointee.edge (h y0) = h y1)
    (e1 : G0.pointee.edge (h y1) = h y0) (hall : ∀ y : G.D, y ∈ [y0, y1])
    {qs : List RingQuestion} (hp : RqsProper G0 G h qs) (hR : isQuizR (cfquizRec qs []) = true) :
    (∀ x ∈ G0.pointee.cpring G0.pointer, G0.pointee.GoodRingArity x) ∧
      ∃ x0, G0.pointee.ValidQuiz (G0.pointee.cpring G0.pointer) x0 (cfquizRec qs []) := by
  obtain ⟨hfit, hring, hsimple, hband⟩ := hp
  rw [hr] at hfit hring hsimple hband
  set M := G0.pointee
  set r0 := M.cpring G0.pointer
  have hl := rqs_fit_size _ _ _ hfit
  match qs, hl, hfit with
  | [⟨k1, a1, q1⟩, ⟨k2, a2, q2⟩], _, hfit =>
  obtain ⟨Ea1, fit1, Ea2, fit2, -⟩ := hfit
  have Ea1' : M.arity (h y0) = a1 + 1 := by rw [Ea1, ar0]
  have Ea2' : M.arity (h y1) = a2 + 1 := by rw [Ea2, ar1]
  clear Ea1 Ea2
  have hk : k1 = true ∧ k2 = true := by
    cases k1 <;> cases k2 <;> first
      | exact ⟨rfl, rfl⟩
      | exact absurd hR (by simp [cfquizRec, noquiz, isQuizR, isQaskR])
  obtain ⟨rfl, rfl⟩ := hk
  have hq : cfquizRec [⟨true, a1, q1⟩, ⟨true, a2, q2⟩] [] =
      if (((largeQarity (a1 - 1) : Qarity) : ℕ) != a1 + 1 ||
          badSmallArity (smallQarity (a2 - 1))) = true then noquiz
      else ⟨QaskR (largeQarity (a1 - 1)) q2, QaskR (smallQarity (a2 - 1)) q1⟩ := rfl
  rw [hq] at hR ⊢
  split_ifs at hR ⊢ with hc
  · exact absurd hR (by decide)
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, not_not, Bool.not_eq_true] at hc
  obtain ⟨hqa1, hbad⟩ := hc
  have hqa2 : ((smallQarity (a2 - 1) : Qarity) : ℕ) = a2 + 1 := by
    have := small_qarityP (a2 - 1)
    rw [hbad] at this
    cases a2 with
    | zero => exact absurd hbad (by decide)
    | succ a2 =>
      simp only [Nat.add_sub_cancel] at this ⊢
      exact (bne_eq_false_iff_eq.1 this.symm).trans (by omega)
  -- the walks
  have hW : rqsWalk M [⟨true, a1, q1⟩, ⟨true, a2, q2⟩] ([y0, y1].map h) =
      h y0 :: (M.walkq (M.node (h y0)) q1 ++ h y1 :: M.walkq (M.node (h y1)) q2) := by
    simp [rqsWalk]
  have hZ : M.walkqz (h y0) ⟨QaskR (largeQarity (a1 - 1)) q2, QaskR (smallQarity (a2 - 1)) q1⟩ =
      h y0 :: (M.walkq (M.node (h y1)) q2 ++ h y1 :: M.walkq (M.node (h y0)) q1) := by
    simp only [Hypermap.walkqz, Hypermap.walkq, Hypermap.qstepR, e0, e1, List.cons_append]
  have hperm : (M.walkqz (h y0) ⟨QaskR (largeQarity (a1 - 1)) q2,
      QaskR (smallQarity (a2 - 1)) q1⟩).Perm
        (rqsWalk M [⟨true, a1, q1⟩, ⟨true, a2, q2⟩] ([y0, y1].map h)) := by
    rw [hW, hZ]
    exact List.Perm.cons _ (List.perm_middle.trans ((List.perm_append_comm.cons _).trans
      List.perm_middle.symm))
  rw [hW] at hsimple hband
  have hsc := (M.simple_cat _ _).1 hsimple
  have hnot : ∀ x ∈ r0, x ∉ M.fband ([y0, y1].map h) := by
    rintro x hx ⟨y, hy, hxy⟩
    apply hsc.2.1
    refine ⟨x, hx, y, ?_, hxy⟩
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> simp
  refine ⟨fun x hx => hring x hx ?_ (hnot x hx), h y0, hR, ?_, ?_, ?_⟩
  · rintro ⟨b, rfl⟩
    exact hnot _ hx (M.ring_fband _ _ (List.mem_map_of_mem (hall b)))
  · rw [fitqz_mk, fitq_QaskR', fitq_QaskR']
    simp only [Hypermap.qstepR, e0, e1]
    exact ⟨⟨by rw [hqa1, Ea1'], fit2⟩, ⟨by rw [hqa2, Ea2'], fit1⟩⟩
  · rw [simple_of_perm M hperm, hW]
    exact hsc.1
  · rw [fband_of_perm M hperm, hW]
    ext u
    simp only [Hypermap.kernel, Set.mem_compl_iff]
    constructor
    · rintro ⟨w, hw, huw⟩ ⟨y, hy, huy⟩
      exact hsc.2.1 ⟨y, hy, w, hw, connect_trans (M.cfaceC.1 huy) huw⟩
    · intro hu
      have h1 : u ∈ (Set.range h)ᶜ ∪ M.fband ([y0, y1].map h) := by
        by_cases hr : u ∈ Set.range h
        · obtain ⟨b, rfl⟩ := hr
          exact Or.inr (M.ring_fband _ _ (List.mem_map_of_mem (hall b)))
        · exact Or.inl hr
      rw [← hband, M.fband_cat] at h1
      exact h1.resolve_right hu

/-! ### Decoding the `Y` and `H` steps of `cfquizRec` (helpers, not in Coq) -/

/-- The question built by a `Y` step for a kernel face (the inner `match` of Coq `cfquiz_Y`). -/
private def yq (qa2 : Qarity) (q1 q2 : Question) : Question :=
  match q1, q2 with
  | Qask0, Qask0 => Qask1 qa2
  | Qask0, _ => QaskL qa2 q2
  | _, Qask0 => QaskR qa2 q1
  | _, _ => QaskLR qa2 q2 q1

/-- `cfquiz_Y` for a kernel face. -/
private theorem cfquizY_kernel (k1 : Bool) (a1 a2 : ℕ) (q1 q2 : Question)
    (rqs' : Question → List RingQuestion) :
    cfquizY ⟨k1, a1, q1⟩ ⟨true, a2, q2⟩ rqs' =
      if badSmallArity (smallQarity a2) then [] else rqs' (yq (smallQarity a2) q1 q2) :=
  rfl

/-- The question `yq qa2 q1 q2` is a simplification of `QaskLR qa2 q2 q1` (the Coq `simq`). -/
private theorem yq_sim {D : Type*} (G : Hypermap D) (qa2 : Qarity) (q1 q2 : Question) (x : D) :
    flatq (yq qa2 q1 q2) = flatq (QaskLR qa2 q2 q1) ∧
      G.walkq x (yq qa2 q1 q2) = G.walkq x (QaskLR qa2 q2 q1) := by
  cases q1 <;> cases q2 <;> simp [yq, flatq, Hypermap.walkq]

/-- `cfquiz_Y` for a ring face. -/
private theorem cfquizY_ring (k1 : Bool) (a1 a2 : ℕ) (q1 q2 : Question)
    (rqs' : Question → List RingQuestion) (hne : cfquizY ⟨k1, a1, q1⟩ ⟨false, a2, q2⟩ rqs' ≠ []) :
    badRingArity a2 = false ∧
      ((q1 = Qask0 ∧ q2 = Qask0 ∧ cfquizY ⟨k1, a1, q1⟩ ⟨false, a2, q2⟩ rqs' = rqs' Qask0) ∨
        (∃ qa q, q1 = QaskR qa q ∧ q2 = Qask0 ∧
          cfquizY ⟨k1, a1, q1⟩ ⟨false, a2, q2⟩ rqs' = rqs' (QaskRR qa q)) ∨
        (∃ qa q, q1 = Qask0 ∧ q2 = QaskL qa q ∧
          cfquizY ⟨k1, a1, q1⟩ ⟨false, a2, q2⟩ rqs' = rqs' (QaskLL qa q))) := by
  cases hb : badRingArity a2
  · refine ⟨rfl, ?_⟩
    simp only [cfquizY, hb, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    cases q1 <;> cases q2 <;> simp_all
  · simp [cfquizY, hb] at hne

/-- `cfquiz_H` for a kernel face. -/
private theorem cfquizH_kernel {D : Type*} (G : Hypermap D) (k1 : Bool) (a1 a2 : ℕ)
    (q1 q2 : Question) (rqs' : Question → Question → List RingQuestion)
    (hne : cfquizH ⟨k1, a1, q1⟩ ⟨true, a2, q2⟩ rqs' ≠ []) :
    badSmallArity (smallQarity (a2 + 1)) = false ∧
      ((q2 = Qask0 ∧ ∃ q, cfquizH ⟨k1, a1, q1⟩ ⟨true, a2, q2⟩ rqs' = rqs' q q2 ∧
          flatq q = flatq (QaskR (smallQarity (a2 + 1)) q1) ∧
          ∀ x, G.walkq x q = G.walkq x (QaskR (smallQarity (a2 + 1)) q1)) ∨
        (q1 = Qask0 ∧ ∃ q, cfquizH ⟨k1, a1, q1⟩ ⟨true, a2, q2⟩ rqs' = rqs' q1 q ∧
          flatq q = flatq (QaskL (smallQarity (a2 + 1)) q2) ∧
          ∀ x, G.walkq x q = G.walkq x (QaskL (smallQarity (a2 + 1)) q2))) := by
  cases hb : badSmallArity (smallQarity (a2 + 1))
  · refine ⟨rfl, ?_⟩
    simp only [cfquizH, hb, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    cases q1 <;> cases q2 <;> cases k1 <;> first
      | exact Or.inl ⟨rfl, _, rfl, rfl, fun _ => rfl⟩
      | exact Or.inr ⟨rfl, _, rfl, rfl, fun _ => rfl⟩
      | exact (hne rfl).elim
  · simp [cfquizH, hb] at hne

/-- `cfquiz_H` for a ring face. -/
private theorem cfquizH_ring (k1 : Bool) (a1 a2 : ℕ) (q1 q2 : Question)
    (rqs' : Question → Question → List RingQuestion)
    (hne : cfquizH ⟨k1, a1, q1⟩ ⟨false, a2, q2⟩ rqs' ≠ []) :
    badRingArity (a2 + 1) = false ∧ q1 = Qask0 ∧ q2 = Qask0 ∧
      cfquizH ⟨k1, a1, q1⟩ ⟨false, a2, q2⟩ rqs' = rqs' Qask0 Qask0 := by
  cases hb : badRingArity (a2 + 1)
  · refine ⟨rfl, ?_⟩
    simp only [cfquizH, hb, Bool.false_eq_true, ↓reduceIte] at hne ⊢
    cases q1 <;> cases q2 <;> simp_all
  · simp [cfquizH, hb] at hne

/-! ### Facts about the `Y` and `H` constructions (helpers, not in Coq) -/

section EcpFacts

/-- Membership in the face band of the empty sequence. -/
private theorem mem_fband_nil {D : Type*} (G : Hypermap D) (x : D) : x ∉ G.fband [] := by
  simp [Hypermap.mem_fband]

/-- Replacing the prefix of a concatenation by one with the same face band. -/
private theorem fband_append_left {D : Type*} (G : Hypermap D) {p p' : List D}
    (hp : G.fband p = G.fband p') (q : List D) : G.fband (p ++ q) = G.fband (p' ++ q) := by
  ext u
  rw [G.fband_cat, G.fband_cat, hp]

/-- `rqs_fit` through an injection that preserves the arities of the darts of the sequence. -/
private theorem rqsFit_map {D0 D D' : Type*} (G0 : Hypermap D0) (G : Hypermap D)
    (G' : Hypermap D') (h : D' → D0) (i : D → D') {qs : List RingQuestion} {l : List D}
    (hf : RqsFit G0 G' h qs (l.map i)) (ha : ∀ x ∈ l, G'.arity (i x) = G.arity x) :
    RqsFit G0 G (h ∘ i) qs l := by
  induction l generalizing qs with
  | nil =>
    cases qs with
    | nil => trivial
    | cons _ _ => exact hf.elim
  | cons x l ih =>
    cases qs with
    | nil => exact hf.elim
    | cons rq qs =>
      obtain ⟨h1, h2, h3⟩ := hf
      refine ⟨?_, h2, ih h3 fun y hy => ha y (List.mem_cons_of_mem _ hy)⟩
      rw [Function.comp_apply, h1, ha x List.mem_cons_self]

variable {D : Type*} [Fintype D] [DecidableEq D] (G : Hypermap D) (x0 : D)

/-- The new face of `ecpY x0` has arity 2 (the Coq `nFu0`). -/
private theorem arity_ecpY_pointer :
    (G.ecpY x0).pointee.arity (G.ecpY x0).pointer = 2 :=
  order_cycle (G.fcycle_ecpY x0)
    (show ([EcpDart.IcpX, EcpDart.Icp EcpDart.IcpX] : List (EcpDart (EcpDart D))).Nodup by simp)
    List.mem_cons_self

/-- The new face of `ecpY x0` does not meet the injected darts. -/
private theorem not_cface_ecpY_icpY (y : D) :
    ¬ (G.ecpY x0).pointee.cface (G.ecpY x0).pointer (G.icpY x0 y) := by
  rw [G.cface_ecpY x0, face_ecpY]
  simp

open Classical in
/-- The arity of the injected darts in `ecpY x0` (the Coq `nFiG`). -/
private theorem arity_icpY (x0gt1 : G.ProperCpring x0) (hsep : ¬ G.cface (G.node x0) x0) (x : D) :
    (G.ecpY x0).pointee.arity (G.icpY x0 x) =
      (if x ∈ G.fband [G.node x0, x0] then 1 else 0) + G.arity x := by
  set M := (G.ecpY x0).pointee
  set u0 := (G.ecpY x0).pointer
  have hb1 : M.cface (M.edge u0) (G.icpY x0 x0) := connect_of_rel (G.face_edge_ecpY x0 x0gt1)
  have hb2 : M.cface (M.edge (M.face u0)) (G.icpY x0 (G.node x0)) :=
    connect_of_rel (G.face_edge_face_ecpY x0)
  have hbs : M.Simple [M.edge u0, M.edge (M.face u0)] := by
    rw [M.simple_cons]
    refine ⟨?_, List.nodup_singleton _⟩
    rintro ⟨y, hy, hy'⟩
    rw [List.mem_singleton] at hy
    subst hy
    apply hsep
    rw [← G.cface_icpY x0]
    exact connect_trans (M.cfaceC.1 hb2) (connect_trans (M.cfaceC.1 hy') hb1)
  have hbv : [M.edge u0, M.edge (M.face u0)] =
      ([EcpDart.IcpXe, EcpDart.Icp EcpDart.IcpXe] : List (EcpDart (EcpDart D))) := rfl
  have key := arity_inj G M (G.icpY x0) (G.icpY_inj x0) (G.cface_icpY x0) hbs ?_ ?_ x
  · rw [key]
    congr 1
    have hiff : G.icpY x0 x ∈ M.fband [M.edge u0, M.edge (M.face u0)] ↔
        x ∈ G.fband [G.node x0, x0] := by
      simp only [Hypermap.fband_cons, mem_fband_nil, or_false]
      have e1 : M.cface (G.icpY x0 x) (M.edge u0) ↔ G.cface x x0 := by
        rw [← G.cface_icpY x0]
        exact ⟨fun h => connect_trans h hb1, fun h => connect_trans h (M.cfaceC.1 hb1)⟩
      have e2 : M.cface (G.icpY x0 x) (M.edge (M.face u0)) ↔ G.cface x (G.node x0) := by
        rw [← G.cface_icpY x0]
        exact ⟨fun h => connect_trans h hb2, fun h => connect_trans h (M.cfaceC.1 hb2)⟩
      rw [e1, e2, or_comm]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl
  · rw [hbv]
    rintro u hu ⟨y, rfl⟩
    simp at hu
  · intro y u hu
    rw [hbv]
    rcases u with _ | _ | (_ | _ | z)
    · exact absurd (M.cfaceC.1 hu) (not_cface_ecpY_icpY G x0 y)
    · simp
    · exact absurd (connect_trans (fconnect1 M.face u0) (M.cfaceC.1 hu))
        (not_cface_ecpY_icpY G x0 y)
    · simp
    · exact Or.inr ⟨z, rfl⟩

end EcpFacts

/-! ### The `Y` step of the Coq proof of `cfquizP` -/

open Classical in
/-- The `Y` step of the Coq proof of `cfquizP`: from ring questions proper for `ecpY x0` (the
map after the step), `cfquiz_Y` computes ring questions proper for `G` (the map before the
step), provided it does not fail. -/
private theorem rqsProper_Y {D : Type*} [Fintype D] [DecidableEq D] (G0 : PointedMap)
    (G : Hypermap D) (x0 : D) (h : (G.ecpY x0).D → G0.D) (Ih : Injective h)
    (hE : ∀ x, h ((G.ecpY x0).pointee.edge x) = G0.pointee.edge (h x))
    (hN : ∀ x, x ∉ (G.ecpY x0).pointee.cpring (G.ecpY x0).pointer →
      h ((G.ecpY x0).pointee.node x) = G0.pointee.node (h x))
    (hF : ∀ x y, G0.pointee.cface (h x) (h y) ↔ (G.ecpY x0).pointee.cface x y)
    (ntG : G.ProperCpring x0) (Ur : G.Simple (G.cpring x0))
    {rq1 rq2 rq3 : RingQuestion} {qs3 : List RingQuestion}
    (hp : RqsProper G0 (G.ecpY x0) h (rq1 :: rq2 :: rq3 :: qs3))
    (hne : cfquizY rq1 rq2 (rqsY rq1 rq3 qs3) ≠ []) :
    RqsProper G0 (PointedMap.mk D G x0) (h ∘ G.icpY x0) (cfquizY rq1 rq2 (rqsY rq1 rq3 qs3)) := by
  obtain ⟨k1, a1, q1⟩ := rq1
  obtain ⟨k2, a2, q2⟩ := rq2
  obtain ⟨k3, a3, q3⟩ := rq3
  obtain ⟨hfit, hring, hsimple, hband⟩ := hp
  set M := G0.pointee with hM
  set r0 := M.cpring G0.pointer with hr0
  set M' := (G.ecpY x0).pointee with hM'
  set u0 := (G.ecpY x0).pointer with hu0
  set i := G.icpY x0 with hi
  set r := G.cpring x0 with hr
  set r1 := r.drop 2 with hr1
  set nu0 := M'.node u0 with hnu0
  set v1 := i (G.node x0) with hv1
  have Dr : r = G.node x0 :: x0 :: r1 := G.head_proper_cpring x0 ntG
  have DrY : M'.cpring u0 = nu0 :: u0 :: i x0 :: r1.map i := by
    rw [hM', hu0, G.cpring_ecpY x0, ← hr, Dr]
    rfl
  rw [DrY] at hfit hring hsimple hband
  -- separation facts from the simplicity of the ring of `G`
  have Ur' : G.Simple ([G.node x0, x0] ++ r1) := by
    have := Ur
    rw [Dr] at this
    exact this
  have hsep : ¬ G.cface (G.node x0) x0 := by
    have := ((G.simple_cons _ _).1 Ur').1
    exact fun h' => this ⟨x0, by simp, h'⟩
  have hr1sep : ∀ x ∈ r1, x ∉ G.fband [G.node x0, x0] := fun x hx hxF =>
    ((G.simple_cat _ _).1 Ur').2.1 ⟨x, hx, hxF⟩
  have hnd : (G.node x0 :: x0 :: r1).Nodup := by
    have := G.simple_uniq Ur
    rw [Dr] at this
    exact this
  -- arities
  have nFu0 : M'.arity u0 = 2 := arity_ecpY_pointer G x0
  have nFiG := arity_icpY G x0 ntG hsep
  have nFv1 : M'.arity v1 = 1 + G.arity (G.node x0) := by
    rw [hv1, nFiG, ite_eq_left ⟨G.node x0, by simp, connect_refl _⟩]
  have nFx0 : M'.arity (i x0) = 1 + G.arity x0 := by
    rw [nFiG, ite_eq_left ⟨x0, by simp, connect_refl _⟩]
  have nFr1 : ∀ x ∈ r1, M'.arity (i x) = G.arity x := fun x hx => by
    rw [nFiG, ite_eq_right (hr1sep x hx), Nat.zero_add]
  have hnu0v1 : M'.cface nu0 v1 := G.cface_node_ecpY x0
  have hnu0v1' : M.cface (h nu0) (h v1) := (hF _ _).2 hnu0v1
  obtain ⟨Ea1, q1nG, Ea2, q2nu0, Ea3, q3iG, q_r1⟩ := hfit
  simp only at Ea1 q1nG Ea2 q2nu0 Ea3 q3iG
  have Ea1' : M.arity (h v1) = a1 + 1 + G.arity (G.node x0) := by
    rw [← M.arity_cface hnu0v1', Ea1, M'.arity_cface hnu0v1, nFv1, Nat.add_assoc]
  have Ea2' : M.arity (h u0) = a2 + 2 := by rw [Ea2, nFu0]
  have Ea3' : M.arity (h (i x0)) = a3 + 1 + G.arity x0 := by rw [Ea3, nFx0, Nat.add_assoc]
  have q_r1' : RqsFit M G (h ∘ i) qs3 r1 := rqsFit_map M G M' h i q_r1 nFr1
  clear Ea1 Ea2 Ea3 q_r1
  -- the darts around the new face
  have hnu0c : nu0 = EcpDart.Icp EcpDart.IcpXe := G.node_ecpY x0
  have hfu0c : M'.face u0 = EcpDart.Icp EcpDart.IcpX := rfl
  have hv1ring : v1 ∉ M'.cpring u0 := by
    rw [DrY, hnu0c]
    have := (List.nodup_cons.1 hnd).1
    simp only [List.mem_cons, List.mem_map, not_or, hv1, hi, Hypermap.icpY, Hypermap.icpN,
      Hypermap.icpU] at this ⊢
    refine ⟨by simp, by simp, fun h' => this.1 (by simpa using h'), ?_⟩
    rintro ⟨y, hy, hyv⟩
    simp only [EcpDart.Icp.injEq] at hyv
    exact this.2 (hyv ▸ hy)
  have hfu0ring : M'.face u0 ∉ M'.cpring u0 := by
    rw [DrY, hnu0c, hfu0c]
    simp [hi]
  have hnv1 : M'.node v1 = M'.face u0 := by
    have h1 : M'.face (M'.edge (M'.face u0)) = v1 := G.face_edge_face_ecpY x0
    apply M'.edgeI
    rw [← h1, M'.faceK]
  have en_v1' : M'.edge (M'.node v1) = nu0 := by
    have h2 : M'.face nu0 = v1 := G.face_node_ecpY x0
    rw [← h2, M'.faceK]
  have en_v1 : M.edge (M.node (h v1)) = h nu0 := by rw [← hN v1 hv1ring, ← hE, en_v1']
  have enn_v1 : M.edge (M.node (M.node (h v1))) = h u0 := by
    rw [← hN v1 hv1ring, hnv1, ← hN _ hfu0ring, ← hE, M'.faceK]
  have hR1 : M.qstepR (M.node (h v1)) = M.node (h nu0) := by
    simp only [Hypermap.qstepR, en_v1]
  have hL1 : M.qstepL (M.node (h v1)) = M.node (h u0) := by
    simp only [Hypermap.qstepL, enn_v1]
  have hu0v1 : M.cface (h u0) (M.node (h v1)) := by
    apply connect_of_rel
    show M.face (h u0) = _
    rw [← enn_v1, M.nodeK]
  have hA : ∀ u, M.cface u (h v1) ↔ M.cface u (h nu0) := fun u =>
    ⟨fun h' => connect_trans h' (M.cfaceC.1 hnu0v1'), fun h' => connect_trans h' hnu0v1'⟩
  have hB : ∀ u, M.cface u (M.node (h v1)) ↔ M.cface u (h u0) := fun u =>
    ⟨fun h' => connect_trans h' (M.cfaceC.1 hu0v1), fun h' => connect_trans h' hu0v1⟩
  -- the face band of the new ring questions (the Coq `EpY1`)
  have hN1 : ∀ x, x ∉ r → (h ∘ i) (G.node x) = M.node ((h ∘ i) x) := by
    intro x hx
    have hx' : x ∉ [G.node x0, x0] := by
      rw [Dr] at hx
      simp only [List.mem_cons, not_or, List.not_mem_nil] at hx ⊢
      exact ⟨hx.1, hx.2.1, not_false⟩
    show h (i (G.node x)) = _
    rw [hi, G.icpY_node x0 x hx']
    exact hN _ fun h' => hx (G.mem_cpring_ecpY_icpY x0 h')
  have hcl := closed_range_band M G (h ∘ i) r (fun x => hE (i x)) hN1
  have hEq : ∀ u, u ∈ M.fband ([] ++ (nu0 :: u0 :: i x0 :: r1.map i).map h) ↔
      M.cface u (h u0) ∨ u ∈ M.fband (r.map (h ∘ i)) := by
    intro u
    rw [Dr]
    simp only [List.nil_append, List.map_cons, List.map_map, Hypermap.fband_cons,
      Function.comp_apply, ← hv1, hA]
    (clear * -; tauto)
  have EpY1 := band_step M M' h i Ih hF u0 (G.fband_icpY x0) (not_cface_ecpY_icpY G x0) hcl hEq
  -- the old walk
  set A := List.replicate k1.toNat (h nu0) ++ (M.walkq (M.node (h nu0)) q1 ++
    (List.replicate k2.toNat (h u0) ++ M.walkq (M.node (h u0)) q2)) with hAdef
  set T := List.replicate k3.toNat (h (i x0)) ++ (M.walkq (M.node (h (i x0))) q3 ++
    rqsWalk M qs3 (r1.map (h ∘ i))) with hTdef
  have hW : rqsWalk M (⟨k1, a1, q1⟩ :: ⟨k2, a2, q2⟩ :: ⟨k3, a3, q3⟩ :: qs3)
      ((nu0 :: u0 :: i x0 :: r1.map i).map h) = A ++ T := by
    simp only [List.map_cons, List.map_map, rqs_walk_cons, List.append_assoc, hAdef, hTdef]
  rw [hW] at hsimple hband
  -- the ring arities (the Coq `nFr0_Y1`)
  have hu0good : ∀ u ∈ r0, M.cface (h u0) u → M.GoodRingArity u := by
    intro u hu hu0u
    have hau : M.arity u = a2 + 2 := by rw [← M.arity_cface hu0u, Ea2']
    apply not_bad_ring_arity
    rw [hau, Nat.add_sub_cancel]
    cases k2
    · exact (cfquizY_ring k1 a1 a2 q1 q2 _ hne).1
    · exfalso
      refine ((M.simple_cat _ _).1 hsimple).2.1 ⟨u, hu, h u0, ?_, M.cfaceC.1 hu0u⟩
      simp [hAdef]
  have hringNew := ring_step M h (Set.range (h ∘ i)) u0 hring EpY1 hEq hu0good
  -- the conclusion, given the new question for the first ring face
  have finish : ∀ q1' : Question, M.fitq (M.node (h v1)) q1' →
      M.fband (List.replicate k1.toNat (h v1) ++ M.walkq (M.node (h v1)) q1') = M.fband A →
      (List.replicate k1.toNat (h v1) ++ M.walkq (M.node (h v1)) q1').length = A.length →
      RqsProper G0 (PointedMap.mk D G x0) (h ∘ i) (rqsY ⟨k1, a1, q1⟩ ⟨k3, a3, q3⟩ qs3 q1') := by
    intro q1' hfit1 hbandA hlenA
    have hW' : rqsWalk M (rqsY ⟨k1, a1, q1⟩ ⟨k3, a3, q3⟩ qs3 q1') (r.map (h ∘ i)) =
        (List.replicate k1.toNat (h v1) ++ M.walkq (M.node (h v1)) q1') ++ T := by
      rw [Dr]
      simp only [rqsY, List.map_cons, rqs_walk_cons, List.append_assoc, hTdef]
      rfl
    have hBd : M.fband ((List.replicate k1.toNat (h v1) ++ M.walkq (M.node (h v1)) q1') ++ T ++
        r0) = M.fband (A ++ T ++ r0) :=
      fband_append_left M (fband_append_left M hbandA T) r0
    have hLn : ((List.replicate k1.toNat (h v1) ++ M.walkq (M.node (h v1)) q1') ++ T ++
        r0).length = (A ++ T ++ r0).length := by
      simp only [List.length_append, hlenA]
    refine ⟨?_, ?_, ?_, ?_⟩
    · show RqsFit M G (h ∘ i) (rqsY ⟨k1, a1, q1⟩ ⟨k3, a3, q3⟩ qs3 q1') r
      rw [Dr]
      exact ⟨by rw [Function.comp_apply, ← hv1, Ea1'], hfit1, by rw [Function.comp_apply, Ea3'],
        q3iG, q_r1'⟩
    · exact hringNew
    · show M.Simple (rqsWalk M (rqsY ⟨k1, a1, q1⟩ ⟨k3, a3, q3⟩ qs3 q1') (r.map (h ∘ i)) ++ r0)
      rw [hW', M.eq_simple hBd hLn]
      exact hsimple
    · show M.fband (rqsWalk M (rqsY ⟨k1, a1, q1⟩ ⟨k3, a3, q3⟩ qs3 q1') (r.map (h ∘ i)) ++ r0) =
        (Set.range (h ∘ i))ᶜ ∪ M.fband (r.map (h ∘ i))
      rw [hW', hBd, hband]
      ext u
      have := EpY1 u
      simp only [mem_fband_nil, false_or] at this
      exact this
  cases k2
  · -- a ring face: the new question is a flattened version of the old ones
    obtain ⟨-, hc⟩ := cfquizY_ring k1 a1 a2 q1 q2 _ hne
    rcases hc with ⟨rfl, rfl, he⟩ | ⟨qa, q, rfl, rfl, he⟩ | ⟨qa, q, rfl, rfl, he⟩ <;> rw [he] <;>
      apply finish
    · exact fitq_Qask0' M _
    · ext u
      cases k1 <;> simp [hAdef, Hypermap.walkq, Hypermap.fband_cons, mem_fband_nil, hA]
    · cases k1 <;> simp [hAdef, Hypermap.walkq]
    · rw [fitq_QaskRR', hR1]
      exact (fitq_QaskR' M _ qa q).1 q1nG
    · have hw : M.walkq (M.node (h v1)) (QaskRR qa q) = M.walkq (M.node (h nu0)) (QaskR qa q) := by
        simp only [Hypermap.walkq, hR1]
      rw [hw]
      ext u
      cases k1 <;> simp [hAdef, Hypermap.walkq, Hypermap.fband_cons,
        hA]
    · have hw : M.walkq (M.node (h v1)) (QaskRR qa q) = M.walkq (M.node (h nu0)) (QaskR qa q) := by
        simp only [Hypermap.walkq, hR1]
      rw [hw]
      cases k1 <;> simp [hAdef, Hypermap.walkq]
    · have hC : M.face (M.edge (M.node (M.node (h u0)))) = M.node (h u0) := M.nodeK _
      rw [fitq_QaskLL', hL1, ← M.arity_face, hC]
      exact (fitq_QaskL' M _ qa q).1 q2nu0
    · have hC : M.cface (M.edge (M.node (M.node (h u0)))) (M.node (h u0)) :=
        connect_of_rel (M.nodeK _)
      have hC' : ∀ u, M.cface u (M.edge (M.node (M.node (h u0)))) ↔ M.cface u (M.node (h u0)) :=
        fun u => ⟨fun h' => connect_trans h' hC, fun h' => connect_trans h' (M.cfaceC.1 hC)⟩
      ext u
      cases k1 <;> simp [hAdef, Hypermap.walkq, hL1, Hypermap.fband_cons,
        hA, hC']
    · cases k1 <;> simp [hAdef, Hypermap.walkq, hL1]
  · -- a kernel face: the new question joins the old ones
    rw [cfquizY_kernel] at hne ⊢
    have hbad : badSmallArity (smallQarity a2) = false := by
      cases hb : badSmallArity (smallQarity a2)
      · rfl
      · simp [hb] at hne
    rw [hbad]
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hqa2 : ((smallQarity a2 : Qarity) : ℕ) = a2 + 2 := by
      have := small_qarityP a2
      rw [hbad] at this
      exact bne_eq_false_iff_eq.1 this.symm
    obtain ⟨hfl, hwk⟩ := yq_sim M (smallQarity a2) q1 q2 (M.node (h v1))
    have hwk' : M.walkq (M.node (h v1)) (QaskLR (smallQarity a2) q2 q1) =
        M.node (h v1) :: (M.walkq (M.node (h u0)) q2 ++ M.walkq (M.node (h nu0)) q1) := by
      simp only [Hypermap.walkq, hL1, hR1]
    apply finish
    · have hf : M.fitq (M.node (h v1)) (yq (smallQarity a2) q1 q2) ↔
          M.fitq (M.node (h v1)) (QaskLR (smallQarity a2) q2 q1) := by
        unfold Hypermap.fitq
        rw [hfl, hwk]
      rw [hf, fitq_QaskLR', hL1, hR1]
      exact ⟨by rw [hqa2, ← M.arity_cface hu0v1, Ea2'], q2nu0, q1nG⟩
    · rw [hwk, hwk']
      ext u
      cases k1 <;> simp [hAdef, Hypermap.fband_cat, Hypermap.fband_cons, hA, hB] <;>
        (clear * -; tauto)
    · rw [hwk, hwk']
      cases k1 <;> simp [hAdef] <;> omega

/-! ### Facts about the `H` construction (helpers, not in Coq) -/

section EcpHFacts

variable {D : Type*} [Fintype D] [DecidableEq D] (G : Hypermap D) (x0 : D)

/-- The face of the `node` of the reference dart of `ecpH x0` is `node x0` (the first step of
`cface_node_ecpH`). -/
private theorem face_node_ecpH (x0gt1 : G.ProperCpring x0) :
    (G.ecpH x0).pointee.face ((G.ecpH x0).pointee.node (G.ecpH x0).pointer) =
      G.icpH x0 (G.node x0) := by
  have e1 : (G.ecpY x0).pointee.edge ((G.ecpY x0).pointee.node (G.ecpY x0).pointer) =
      EcpDart.Icp EcpDart.IcpX := by
    rw [G.node_ecpY x0]; rfl
  have e2 : (G.ecpY x0).pointee.edge ((G.ecpY x0).pointee.face ((G.ecpY x0).pointee.edge
      (G.ecpY x0).pointer)) = EcpDart.Icp (EcpDart.Icp (G.edge x0)) := by
    rw [G.face_edge_ecpY x0 x0gt1]; rfl
  show (G.ecpY x0).pointee.ecpNFace (G.ecpY x0).pointer
    ((G.ecpY x0).pointee.ecpNNode (G.ecpY x0).pointer EcpDart.IcpX) =
      EcpDart.Icp (G.icpY x0 (G.node x0))
  rw [ecpNNode, ite_eq_left (G.long_ecpY x0 x0gt1), ecpNFace, G.face_node_ecpY x0,
    ite_eq_right, ite_eq_right]
  · rw [e1, G.node_ecpY x0]; simp
  · rw [e2, G.node_ecpY x0]; simp

/-- The `node` of `icpH x0 x0` is the second dart of the new face (the Coq `n_v2`). -/
private theorem node_icpH_x0 (x0gt1 : G.ProperCpring x0) :
    (G.ecpH x0).pointee.node (G.icpH x0 x0) = (G.ecpH x0).pointee.face (G.ecpH x0).pointer := by
  have hp : x0 ≠ G.node x0 := x0gt1
  show (G.ecpY x0).pointee.ecpNNode (G.ecpY x0).pointer
    (EcpDart.Icp (EcpDart.Icp (EcpDart.Icp x0))) = EcpDart.Icp EcpDart.IcpX
  simp [ecpNNode, ecpUNode, hp, G.long_ecpU x0]

/-- The `node` of `icpH x0 (node x0)` is the third dart of the new face. -/
private theorem node_icpH_node (x0gt1 : G.ProperCpring x0) :
    (G.ecpH x0).pointee.node (G.icpH x0 (G.node x0)) =
      (G.ecpH x0).pointee.face ((G.ecpH x0).pointee.face (G.ecpH x0).pointer) := by
  have hp : x0 ≠ G.node x0 := x0gt1
  rw [G.face_face_ecpH x0 x0gt1]
  show (G.ecpY x0).pointee.ecpNNode (G.ecpY x0).pointer
    (EcpDart.Icp (EcpDart.Icp (EcpDart.Icp (G.node x0)))) = _
  simp [ecpNNode, ecpUNode]

/-- The new face of `ecpH x0` is a triangle. -/
private theorem fcycle_ecpH (x0gt1 : G.ProperCpring x0) :
    fcycle (G.ecpH x0).pointee.face
      [(G.ecpH x0).pointer, (G.ecpH x0).pointee.face (G.ecpH x0).pointer,
        (G.ecpH x0).pointee.face ((G.ecpH x0).pointee.face (G.ecpH x0).pointer)] :=
  ⟨rfl, rfl, G.face_face_face_ecpH x0 x0gt1, trivial⟩

/-- The new face of `ecpH x0` has arity 3 (the Coq `nFu0`). -/
private theorem arity_ecpH_pointer (x0gt1 : G.ProperCpring x0) :
    (G.ecpH x0).pointee.arity (G.ecpH x0).pointer = 3 := by
  refine order_cycle (fcycle_ecpH G x0 x0gt1) ?_ List.mem_cons_self
  rw [G.face_face_ecpH x0 x0gt1]
  show ([EcpDart.IcpX, EcpDart.Icp EcpDart.IcpX, EcpDart.Icp (EcpDart.Icp EcpDart.IcpX)] :
    List (EcpDart (EcpDart (EcpDart D)))).Nodup
  simp

/-- The new face of `ecpH x0` does not meet the injected darts. -/
private theorem not_cface_ecpH_icpH (x0gt1 : G.ProperCpring x0) (y : D) :
    ¬ (G.ecpH x0).pointee.cface (G.ecpH x0).pointer (G.icpH x0 y) := by
  rw [G.cface_ecpH x0 x0gt1, G.face_face_ecpH x0 x0gt1, face_ecpH]
  simp

open Classical in
/-- The arity of the injected darts in `ecpH x0` (the Coq `nFiG`). -/
private theorem arity_icpH (x0gt1 : G.ProperCpring x0)
    (hs : G.Simple [G.node x0, x0, G.face (G.edge x0)]) (x : D) :
    (G.ecpH x0).pointee.arity (G.icpH x0 x) =
      (if x ∈ G.fband [G.node x0, x0, G.face (G.edge x0)] then 1 else 0) + G.arity x := by
  set M := (G.ecpH x0).pointee
  set u0 := (G.ecpH x0).pointer
  set au0 := [G.node x0, x0, G.face (G.edge x0)]
  set b := [M.edge u0, M.edge (M.face u0), M.edge (M.face (M.face u0))]
  have horb : orbit M.face u0 = [u0, M.face u0, M.face (M.face u0)] := by
    rw [orbit, show order M.face u0 = 3 from arity_ecpH_pointer G x0 x0gt1]
    rfl
  have hbF : M.fband b = M.fband (au0.map (G.icpH x0)) := by
    ext w
    rw [← G.adj_ecpH x0 x0gt1]
    show _ ↔ ∃ z ∈ orbit M.face u0, M.rlink z w
    rw [horb]
    simp only [Hypermap.rlink, Hypermap.mem_fband, b, List.mem_cons,
      List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left]
    simp only [M.cfaceC (x := w)]
  have hbs : M.Simple b := by
    rw [M.eq_simple hbF (by simp [b, au0]), simple_map (G.cface_icpH x0)]
    exact hs
  have hbv : b = ([EcpDart.IcpXe, EcpDart.Icp EcpDart.IcpXe,
      EcpDart.Icp (EcpDart.Icp EcpDart.IcpXe)] : List (EcpDart (EcpDart (EcpDart D)))) := by
    simp only [b]
    rw [G.face_face_ecpH x0 x0gt1]
    rfl
  have key := arity_inj G M (G.icpH x0) (G.icpH_inj x0) (G.cface_icpH x0) hbs ?_ ?_ x
  · rw [key]
    congr 1
    have hiff : G.icpH x0 x ∈ M.fband b ↔ x ∈ G.fband au0 := by
      rw [hbF]
      simp only [Hypermap.mem_fband, List.mem_map]
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, hxz⟩
        exact ⟨z, hz, (G.cface_icpH x0 x z).1 hxz⟩
      · rintro ⟨z, hz, hxz⟩
        exact ⟨_, ⟨z, hz, rfl⟩, (G.cface_icpH x0 x z).2 hxz⟩
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hiff.1 h1) h2
    · exact absurd (hiff.2 h2) h1
    · rfl
  · rw [hbv]
    rintro u hu ⟨y, rfl⟩
    simp at hu
  · intro y u hu
    rw [hbv]
    have h02 : M.cface u0 (EcpDart.Icp (EcpDart.Icp EcpDart.IcpX)) := by
      rw [← G.face_face_ecpH x0 x0gt1]
      exact connect_trans (fconnect1 _ _) (fconnect1 _ _)
    rcases u with _ | _ | (_ | _ | (_ | _ | z))
    · exact absurd (M.cfaceC.1 hu) (not_cface_ecpH_icpH G x0 x0gt1 y)
    · simp
    · exact absurd (connect_trans (fconnect1 M.face u0) (M.cfaceC.1 hu))
        (not_cface_ecpH_icpH G x0 x0gt1 y)
    · simp
    · exact absurd (connect_trans h02 (M.cfaceC.1 hu)) (not_cface_ecpH_icpH G x0 x0gt1 y)
    · simp
    · exact Or.inr ⟨z, rfl⟩

end EcpHFacts

/-- The arity of a dart whose face lies in the image of an injection (the Coq `nFv2`). -/
private theorem arity_of_range {D0 D' : Type*} [Finite D0] [Finite D'] (G0 : Hypermap D0)
    (G' : Hypermap D') (h : D' → D0) (Ih : Injective h)
    (hF : ∀ x y, G0.cface (h x) (h y) ↔ G'.cface x y) (w : D')
    (hw : ∀ u, G0.cface (h w) u → u ∈ Set.range h) : G0.arity (h w) = G'.arity w := by
  have hS : {u | G0.cface (h w) u} = h '' {y | G'.cface w y} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hu
      obtain ⟨y, rfl⟩ := hw u hu
      exact ⟨y, (hF w y).1 hu, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact (hF w y).2 hy
  show order G0.face (h w) = order G'.face w
  rw [order, order]
  change {u | G0.cface (h w) u}.ncard = {y | G'.cface w y}.ncard
  rw [hS, Set.ncard_image_of_injective _ Ih]

/-! ### The `H` step of the Coq proof of `cfquizP` -/

open Classical in
/-- The `H` step of the Coq proof of `cfquizP`: from ring questions proper for `ecpH x0` (the
map after the step), `cfquiz_H` computes ring questions proper for `G` (the map before the
step), provided it does not fail. -/
private theorem rqsProper_H {D : Type*} [Fintype D] [DecidableEq D] (G0 : PointedMap)
    (G : Hypermap D) (x0 : D) (h : (G.ecpH x0).D → G0.D) (Ih : Injective h)
    (hE : ∀ x, h ((G.ecpH x0).pointee.edge x) = G0.pointee.edge (h x))
    (hN : ∀ x, x ∉ (G.ecpH x0).pointee.cpring (G.ecpH x0).pointer →
      h ((G.ecpH x0).pointee.node x) = G0.pointee.node (h x))
    (hF : ∀ x y, G0.pointee.cface (h x) (h y) ↔ (G.ecpH x0).pointee.cface x y)
    (ntG : G.ProperCpring x0) (longG : G.LongCpring x0) (Ur : G.Simple (G.cpring x0))
    {rq1 rq2 rq3 : RingQuestion} {qs3 : List RingQuestion}
    (hp : RqsProper G0 (G.ecpH x0) h (rq1 :: rq2 :: rq3 :: qs3))
    (hne : cfquizH rq1 rq2 (rqsH rq1 rq3 qs3) ≠ []) :
    RqsProper G0 (PointedMap.mk D G x0) (h ∘ G.icpH x0) (cfquizH rq1 rq2 (rqsH rq1 rq3 qs3)) := by
  obtain ⟨k1, a1, q1⟩ := rq1
  obtain ⟨k2, a2, q2⟩ := rq2
  obtain ⟨k3, a3, q3⟩ := rq3
  obtain ⟨hfit, hring, hsimple, hband⟩ := hp
  set M := G0.pointee with hM
  set r0 := M.cpring G0.pointer with hr0
  set M' := (G.ecpH x0).pointee with hM'
  set u0 := (G.ecpH x0).pointer with hu0
  set i := G.icpH x0 with hi
  set r := G.cpring x0 with hr
  set r1 := r.drop 3 with hr1
  set nu0 := M'.node u0 with hnu0
  set v1 := i (G.node x0) with hv1
  set v2 := i x0 with hv2
  set v3 := i (G.face (G.edge x0)) with hv3
  have Dr : r = G.node x0 :: x0 :: G.face (G.edge x0) :: r1 := G.head_long_cpring x0 longG
  have DrH : M'.cpring u0 = nu0 :: u0 :: v3 :: r1.map i := by
    rw [hM', hu0, G.cpring_ecpH x0 ntG, ← hr, Dr]
    rfl
  rw [DrH] at hfit hring hsimple hband
  -- separation facts from the simplicity of the ring of `G`
  have Ur' : G.Simple ([G.node x0, x0, G.face (G.edge x0)] ++ r1) := by
    have := Ur
    rw [Dr] at this
    exact this
  have hs3 := ((G.simple_cat _ _).1 Ur').1
  have hr1sep : ∀ x ∈ r1, x ∉ G.fband [G.node x0, x0, G.face (G.edge x0)] := fun x hx hxF =>
    ((G.simple_cat _ _).1 Ur').2.1 ⟨x, hx, hxF⟩
  have hnd : (G.node x0 :: x0 :: G.face (G.edge x0) :: r1).Nodup := by
    have := G.simple_uniq Ur
    rw [Dr] at this
    exact this
  have hx0sep : x0 ∉ G.fband (G.node x0 :: G.face (G.edge x0) :: r1) := by
    have := Ur
    rw [Dr] at this
    have h' := (G.simple_catCA [G.node x0] [x0] (G.face (G.edge x0) :: r1)).1 this
    exact ((G.simple_cons _ _).1 h').1
  -- arities
  have nFu0 : M'.arity u0 = 3 := arity_ecpH_pointer G x0 ntG
  have nFiG := arity_icpH G x0 ntG hs3
  have nFv1 : M'.arity v1 = 1 + G.arity (G.node x0) := by
    rw [hv1, nFiG, ite_eq_left ⟨G.node x0, by simp, connect_refl _⟩]
  have nFv2 : M'.arity v2 = 1 + G.arity x0 := by
    rw [hv2, nFiG, ite_eq_left ⟨x0, by simp, connect_refl _⟩]
  have nFv3 : M'.arity v3 = 1 + G.arity (G.face (G.edge x0)) := by
    rw [hv3, nFiG, ite_eq_left ⟨G.face (G.edge x0), by simp, connect_refl _⟩]
  have nFr1 : ∀ x ∈ r1, M'.arity (i x) = G.arity x := fun x hx => by
    rw [nFiG, ite_eq_right (hr1sep x hx), Nat.zero_add]
  have hnu0v1 : M'.cface nu0 v1 := G.cface_node_ecpH x0 ntG
  have hnu0v1' : M.cface (h nu0) (h v1) := (hF _ _).2 hnu0v1
  obtain ⟨Ea1, q1nu0, Ea2, q2u0, Ea3, q3v3, q_r1⟩ := hfit
  simp only at Ea1 q1nu0 Ea2 q2u0 Ea3 q3v3
  have Ea1' : M.arity (h v1) = a1 + 1 + G.arity (G.node x0) := by
    rw [← M.arity_cface hnu0v1', Ea1, M'.arity_cface hnu0v1, nFv1, Nat.add_assoc]
  have Ea2' : M.arity (h u0) = a2 + 3 := by rw [Ea2, nFu0]
  have Ea3' : M.arity (h v3) = a3 + 1 + G.arity (G.face (G.edge x0)) := by
    rw [Ea3, nFv3, Nat.add_assoc]
  have q_r1' : RqsFit M G (h ∘ i) qs3 r1 := rqsFit_map M G M' h i q_r1 nFr1
  clear Ea1 Ea2 Ea3 q_r1
  -- the darts around the new face
  have hnu0c : nu0 = EcpDart.Icp (EcpDart.Icp EcpDart.IcpXe) := by
    show (G.ecpY x0).pointee.ecpNNode (G.ecpY x0).pointer EcpDart.IcpX = _
    rw [ecpNNode, ite_eq_left (G.long_ecpY x0 ntG), G.node_ecpY x0]
  have hfu0c : M'.face u0 = EcpDart.Icp EcpDart.IcpX := rfl
  have hnd' := hnd
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd'
  have hv1ring : v1 ∉ M'.cpring u0 := by
    rw [DrH, hnu0c]
    simp only [List.mem_cons, List.mem_map, not_or, hv1, hv3, hi, Hypermap.icpH, Hypermap.icpY,
      Hypermap.icpN, Hypermap.icpU, EcpDart.Icp.injEq, reduceCtorEq, not_false_eq_true,
      true_and, not_exists, not_and]
    exact ⟨hnd'.1.2.1, fun y hy hyv => hnd'.1.2.2 (hyv ▸ hy)⟩
  have hv2ring : v2 ∉ M'.cpring u0 := by
    rw [DrH, hnu0c]
    simp only [List.mem_cons, List.mem_map, not_or, hv2, hv3, hi, Hypermap.icpH, Hypermap.icpY,
      Hypermap.icpN, Hypermap.icpU, EcpDart.Icp.injEq, reduceCtorEq, not_false_eq_true,
      true_and, not_exists, not_and]
    exact ⟨hnd'.2.1.1, fun y hy hyv => hnd'.2.1.2 (hyv ▸ hy)⟩
  have hfu0ring : M'.face u0 ∉ M'.cpring u0 := by
    rw [DrH, hnu0c, hfu0c]
    simp [hi, hv3]
  have en_v1' : M'.edge (M'.node v1) = nu0 := by
    have h2 : M'.face nu0 = v1 := face_node_ecpH G x0 ntG
    rw [← h2, M'.faceK]
  have en_v1 : M.edge (M.node (h v1)) = h nu0 := by rw [← hN v1 hv1ring, ← hE, en_v1']
  have nv1Fu0 : M.cface (M.node (h v1)) (h u0) := by
    rw [← hN v1 hv1ring, hv1, node_icpH_node G x0 ntG, hF]
    exact M'.cfaceC.1 (connect_trans (fconnect1 _ _) (fconnect1 _ _))
  have enn_v2 : M.edge (M.node (M.node (h v2))) = h u0 := by
    rw [← hN v2 hv2ring, hv2, node_icpH_x0 G x0 ntG, ← hN _ hfu0ring, ← hE, M'.faceK]
  have hR1 : M.qstepR (M.node (h v1)) = M.node (h nu0) := by
    simp only [Hypermap.qstepR, en_v1]
  have hL2 : M.qstepL (M.node (h v2)) = M.node (h u0) := by
    simp only [Hypermap.qstepL, enn_v2]
  have hu0v2 : M.cface (h u0) (M.node (h v2)) := by
    apply connect_of_rel
    show M.face (h u0) = _
    rw [← enn_v2, M.nodeK]
  have hA : ∀ u, M.cface u (h v1) ↔ M.cface u (h nu0) := fun u =>
    ⟨fun h' => connect_trans h' (M.cfaceC.1 hnu0v1'), fun h' => connect_trans h' hnu0v1'⟩
  have hB : ∀ u, M.cface u (M.node (h v1)) ↔ M.cface u (h u0) := fun u =>
    ⟨fun h' => connect_trans h' nv1Fu0, fun h' => connect_trans h' (M.cfaceC.1 nv1Fu0)⟩
  have hC : ∀ u, M.cface u (M.node (h v2)) ↔ M.cface u (h u0) := fun u =>
    ⟨fun h' => connect_trans h' (M.cfaceC.1 hu0v2), fun h' => connect_trans h' hu0v2⟩
  -- the face band of the new ring questions (the Coq `EpH1`)
  have hN1 : ∀ x, x ∉ r → (h ∘ i) (G.node x) = M.node ((h ∘ i) x) := by
    intro x hx
    have hx' : x ∉ [G.node x0, x0, G.face (G.edge x0)] := by
      rw [Dr] at hx
      simp only [List.mem_cons, not_or, List.not_mem_nil] at hx ⊢
      exact ⟨hx.1, hx.2.1, hx.2.2.1, not_false⟩
    show h (i (G.node x)) = _
    rw [hi, G.icpH_node x0 x hx']
    exact hN _ fun h' => hx (G.mem_cpring_ecpH_icpH x0 h')
  have hcl := closed_range_band M G (h ∘ i) r (fun x => hE (i x)) hN1
  have hEq : ∀ u, u ∈ M.fband ([h v2] ++ (nu0 :: u0 :: v3 :: r1.map i).map h) ↔
      M.cface u (h u0) ∨ u ∈ M.fband (r.map (h ∘ i)) := by
    intro u
    rw [Dr]
    simp only [List.singleton_append, List.map_cons, List.map_map, Hypermap.fband_cons,
      Function.comp_apply, ← hv1, ← hv2, ← hv3, hA]
    (clear * -; tauto)
  have EpH1 := band_step M M' h i Ih hF u0 (G.fband_icpH x0) (not_cface_ecpH_icpH G x0 ntG) hcl
    hEq
  -- the old walk
  set A := List.replicate k1.toNat (h nu0) ++ (M.walkq (M.node (h nu0)) q1 ++
    (List.replicate k2.toNat (h u0) ++ M.walkq (M.node (h u0)) q2)) with hAdef
  set T := List.replicate k3.toNat (h v3) ++ (M.walkq (M.node (h v3)) q3 ++
    rqsWalk M qs3 (r1.map (h ∘ i))) with hTdef
  have hW : rqsWalk M (⟨k1, a1, q1⟩ :: ⟨k2, a2, q2⟩ :: ⟨k3, a3, q3⟩ :: qs3)
      ((nu0 :: u0 :: v3 :: r1.map i).map h) = A ++ T := by
    simp only [List.map_cons, List.map_map, rqs_walk_cons, List.append_assoc, hAdef, hTdef]
  rw [hW] at hsimple hband
  -- `h v2` is a new face of the old walk (the Coq `rHF'v2`, `pHF'v2`, `Uv2pH` and `nFv2`)
  have rHF'v2 : h v2 ∉ M.fband ((nu0 :: u0 :: v3 :: r1.map i).map h) := by
    rintro ⟨y, hy, hxy⟩
    simp only [List.map_cons, List.map_map, List.mem_cons, List.mem_map, Function.comp_apply]
      at hy
    have hx0 : ∀ z, G.cface x0 z → z ∈ G.node x0 :: G.face (G.edge x0) :: r1 → False :=
      fun z hz hzr => hx0sep ⟨z, hzr, hz⟩
    rcases hy with rfl | rfl | rfl | ⟨z, hz, rfl⟩
    · have := connect_trans ((hF _ _).1 hxy) hnu0v1
      exact hx0 _ ((G.cface_icpH x0 _ _).1 this) (by simp)
    · exact not_cface_ecpH_icpH G x0 ntG x0 (M'.cfaceC.1 ((hF _ _).1 hxy))
    · exact hx0 _ ((G.cface_icpH x0 _ _).1 ((hF _ _).1 hxy)) (by simp)
    · exact hx0 _ ((G.cface_icpH x0 _ _).1 ((hF _ _).1 hxy)) (by simp [hz])
  have pHF'v2 : h v2 ∉ M.fband (A ++ T ++ r0) := by
    rw [hband]
    rintro (h' | h')
    · exact h' ⟨v2, rfl⟩
    · exact rHF'v2 h'
  have Uv2pH : M.Simple (h v2 :: (A ++ T ++ r0)) := (M.simple_cons _ _).2 ⟨pHF'v2, hsimple⟩
  have nFv2h : M.arity (h v2) = 1 + G.arity x0 := by
    rw [← nFv2]
    refine arity_of_range M M' h Ih hF v2 fun u hu => ?_
    by_contra hur
    have : u ∈ M.fband (A ++ T ++ r0) := by rw [hband]; exact Or.inl hur
    exact pHF'v2 (((M.fbandF _).connect_iff hu).2 this)
  -- the ring arities (the Coq `nFr0_H1`)
  have hu0good : ∀ u ∈ r0, M.cface (h u0) u → M.GoodRingArity u := by
    intro u hu hu0u
    have hau : M.arity u = a2 + 1 + 2 := by rw [← M.arity_cface hu0u, Ea2']
    apply not_bad_ring_arity
    rw [hau, Nat.add_sub_cancel]
    cases k2
    · exact (cfquizH_ring k1 a1 a2 q1 q2 _ hne).1
    · exfalso
      refine ((M.simple_cat _ _).1 hsimple).2.1 ⟨u, hu, h u0, ?_, M.cfaceC.1 hu0u⟩
      simp [hAdef]
  have hringNew := ring_step M h (Set.range (h ∘ i)) u0 hring EpH1 hEq hu0good
  -- the conclusion, given the new questions for the first two ring faces
  have finish : ∀ q1' q2' : Question, M.fitq (M.node (h v1)) q1' →
      M.fitq (M.node (h v2)) q2' →
      M.fband (List.replicate k1.toNat (h v1) ++ (M.walkq (M.node (h v1)) q1' ++
        (h v2 :: M.walkq (M.node (h v2)) q2'))) = M.fband (h v2 :: A) →
      (List.replicate k1.toNat (h v1) ++ (M.walkq (M.node (h v1)) q1' ++
        (h v2 :: M.walkq (M.node (h v2)) q2'))).length = (h v2 :: A).length →
      RqsProper G0 (PointedMap.mk D G x0) (h ∘ i)
        (rqsH ⟨k1, a1, q1⟩ ⟨k3, a3, q3⟩ qs3 q1' q2') := by
    intro q1' q2' hfit1 hfit2 hbandA hlenA
    have hW' : rqsWalk M (rqsH ⟨k1, a1, q1⟩ ⟨k3, a3, q3⟩ qs3 q1' q2') (r.map (h ∘ i)) =
        (List.replicate k1.toNat (h v1) ++ (M.walkq (M.node (h v1)) q1' ++
          (h v2 :: M.walkq (M.node (h v2)) q2'))) ++ T := by
      rw [Dr]
      simp only [rqsH, List.map_cons, rqs_walk_cons, List.append_assoc, hTdef]
      rfl
    have hBd : M.fband ((List.replicate k1.toNat (h v1) ++ (M.walkq (M.node (h v1)) q1' ++
        (h v2 :: M.walkq (M.node (h v2)) q2'))) ++ T ++ r0) = M.fband (h v2 :: (A ++ T ++ r0)) :=
      fband_append_left M (fband_append_left M hbandA T) r0
    have hLn : ((List.replicate k1.toNat (h v1) ++ (M.walkq (M.node (h v1)) q1' ++
        (h v2 :: M.walkq (M.node (h v2)) q2'))) ++ T ++ r0).length =
        (h v2 :: (A ++ T ++ r0)).length := by
      simp only [List.length_append, List.length_cons] at hlenA ⊢
      omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · show RqsFit M G (h ∘ i) (rqsH ⟨k1, a1, q1⟩ ⟨k3, a3, q3⟩ qs3 q1' q2') r
      rw [Dr]
      exact ⟨by rw [Function.comp_apply, ← hv1, Ea1'], hfit1, by rw [Function.comp_apply, nFv2h],
        hfit2, by rw [Function.comp_apply, ← hv3, Ea3'], q3v3, q_r1'⟩
    · exact hringNew
    · show M.Simple (rqsWalk M (rqsH ⟨k1, a1, q1⟩ ⟨k3, a3, q3⟩ qs3 q1' q2') (r.map (h ∘ i)) ++ r0)
      rw [hW', M.eq_simple hBd hLn]
      exact Uv2pH
    · show M.fband (rqsWalk M (rqsH ⟨k1, a1, q1⟩ ⟨k3, a3, q3⟩ qs3 q1' q2') (r.map (h ∘ i)) ++
          r0) = (Set.range (h ∘ i))ᶜ ∪ M.fband (r.map (h ∘ i))
      rw [hW', hBd]
      ext u
      have := EpH1 u
      rw [M.fband_cons, hband]
      simp only [Hypermap.fband_cons, mem_fband_nil, or_false] at this
      exact this
  cases k2
  · -- a ring face
    obtain ⟨-, rfl, rfl, he⟩ := cfquizH_ring k1 a1 a2 q1 q2 _ hne
    rw [he]
    apply finish Qask0 Qask0 (fitq_Qask0' M _) (fitq_Qask0' M _)
    · ext u
      cases k1 <;> simp only [hAdef, Hypermap.walkq, Bool.toNat_false, Bool.toNat_true,
        List.replicate_zero, List.replicate_one, List.nil_append, List.append_nil,
        List.cons_append, Hypermap.fband_cons, mem_fband_nil, hA,
        or_false]
      exact or_comm
    · cases k1 <;> simp [hAdef, Hypermap.walkq]
  · -- a kernel face
    obtain ⟨hbad, hc⟩ := cfquizH_kernel M k1 a1 a2 q1 q2 _ hne
    have hqa2 : ((smallQarity (a2 + 1) : Qarity) : ℕ) = a2 + 3 := by
      have := small_qarityP (a2 + 1)
      rw [hbad] at this
      exact bne_eq_false_iff_eq.1 this.symm
    rcases hc with ⟨rfl, q, he, hfl, hwk⟩ | ⟨rfl, q, he, hfl, hwk⟩ <;> rw [he]
    · have hwk' : M.walkq (M.node (h v1)) q =
          M.node (h v1) :: M.walkq (M.node (h nu0)) q1 := by
        rw [hwk]
        simp only [Hypermap.walkq, hR1]
      apply finish q Qask0 _ (fitq_Qask0' M _)
      · rw [hwk']
        ext u
        cases k1 <;> simp only [hAdef, Hypermap.walkq, Bool.toNat_false, Bool.toNat_true,
          List.replicate_zero, List.replicate_one, List.nil_append, List.append_nil,
          List.cons_append, Hypermap.fband_cons, Hypermap.fband_cat,
          mem_fband_nil, hA, hB, or_false]
        all_goals (clear * -; tauto)
      · rw [hwk']
        cases k1 <;> simp [hAdef, Hypermap.walkq]
      · have hf : M.fitq (M.node (h v1)) q ↔
            M.fitq (M.node (h v1)) (QaskR (smallQarity (a2 + 1)) q1) := by
          unfold Hypermap.fitq
          rw [hfl, hwk]
        rw [hf, fitq_QaskR', hR1]
        exact ⟨by rw [hqa2, M.arity_cface nv1Fu0, Ea2'], q1nu0⟩
    · have hwk' : M.walkq (M.node (h v2)) q =
          M.node (h v2) :: M.walkq (M.node (h u0)) q2 := by
        rw [hwk]
        simp only [Hypermap.walkq, hL2]
      apply finish Qask0 q (fitq_Qask0' M _)
      · have hf : M.fitq (M.node (h v2)) q ↔
            M.fitq (M.node (h v2)) (QaskL (smallQarity (a2 + 1)) q2) := by
          unfold Hypermap.fitq
          rw [hfl, hwk]
        rw [hf, fitq_QaskL', hL2]
        exact ⟨by rw [hqa2, ← M.arity_cface hu0v2, Ea2'], q2u0⟩
      · rw [hwk']
        ext u
        cases k1 <;> simp only [hAdef, Hypermap.walkq, Bool.toNat_false, Bool.toNat_true,
          List.replicate_zero, List.replicate_one, List.nil_append,
          List.cons_append, Hypermap.fband_cons, hA, hC]
        all_goals (clear * -; tauto)
      · rw [hwk']
        cases k1 <;> simp [hAdef, Hypermap.walkq]

/-! ### The main results (end of the Coq section `ConfigQuiz`) -/

/-- The lengths of the ring question sequences computed by a `Y` step. -/
private theorem length_cfquizY (rq1 rq2 rq3 : RingQuestion) (qs3 : List RingQuestion)
    (hne : cfquizY rq1 rq2 (rqsY rq1 rq3 qs3) ≠ []) :
    (cfquizY rq1 rq2 (rqsY rq1 rq3 qs3)).length = qs3.length + 2 := by
  obtain ⟨k1, a1, q1⟩ := rq1
  obtain ⟨k2, a2, q2⟩ := rq2
  obtain ⟨k3, a3, q3⟩ := rq3
  cases k2
  · obtain ⟨-, hc⟩ := cfquizY_ring k1 a1 a2 q1 q2 _ hne
    rcases hc with ⟨-, -, he⟩ | ⟨_, _, -, -, he⟩ | ⟨_, _, -, -, he⟩ <;> rw [he] <;> rfl
  · rw [cfquizY_kernel] at hne ⊢
    split_ifs at hne ⊢
    · exact absurd rfl hne
    · rfl

/-- The lengths of the ring question sequences computed by an `H` step. -/
private theorem length_cfquizH (rq1 rq2 rq3 : RingQuestion) (qs3 : List RingQuestion)
    (hne : cfquizH rq1 rq2 (rqsH rq1 rq3 qs3) ≠ []) :
    (cfquizH rq1 rq2 (rqsH rq1 rq3 qs3)).length = qs3.length + 3 := by
  obtain ⟨k1, a1, q1⟩ := rq1
  obtain ⟨k2, a2, q2⟩ := rq2
  obtain ⟨k3, a3, q3⟩ := rq3
  cases k2
  · obtain ⟨-, -, -, he⟩ := cfquizH_ring k1 a1 a2 q1 q2 _ hne
    rw [he]
    rfl
  · obtain ⟨-, hc⟩ := cfquizH_kernel cpmap0 k1 a1 a2 q1 q2 _ hne
    rcases hc with ⟨-, _, he, -⟩ | ⟨-, _, he, -⟩ <;> rw [he] <;> rfl

/-- `cfquiz_rec` of short ring question sequences (and of unexpected steps) is `noquiz`. -/
private theorem cfquizRec_short {qs : List RingQuestion} {s : Cpstep} {cp : Cprog}
    (h : qs.length < 3) : cfquizRec qs (s :: cp) = noquiz := by
  match qs, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], _ => rfl

/-- Coq `qs0_notR` (a section `Let`). -/
private theorem qs0_notR (cp1 : Cprog) : isQuizR (cfquizRec [] cp1) = false := by
  cases cp1 <;> rfl

/-- The steps of `cfquiz_rec` that are not `R`, `Y` or `H` steps yield `noquiz`. -/
private theorem cfquizRec_other {rq1 rq2 rq3 : RingQuestion} {qs3 : List RingQuestion}
    {s : Cpstep} {cp : Cprog} (hs : ∀ n, s ≠ .R n) (hY : s ≠ .Y) (hH : s ≠ .H) :
    cfquizRec (rq1 :: rq2 :: rq3 :: qs3) (s :: cp) = noquiz := by
  cases s with
  | R n => exact absurd rfl (hs n)
  | Y => exact absurd rfl hY
  | H => exact absurd rfl hH
  | _ => rfl

/-- The program of a configuration whose quiz is valid is a configuration program (the
induction of the Coq `cp_ok`). -/
private theorem configProg_of_cfquizRec :
    ∀ (cp : Cprog) (qs : List RingQuestion), qs.length = cprsize cp → cp ≠ [] →
      isQuizR (cfquizRec qs cp) = true → configProg cp = true := by
  intro cp
  induction cp with
  | nil => intro _ _ h; exact absurd rfl h
  | cons s cp ih =>
    intro qs hl _ hR
    match qs, hl, hR with
    | [], _, hR | [_], _, hR | [_, _], _, hR =>
      rw [cfquizRec_short (by simp)] at hR
      exact absurd hR (by decide)
    | rq1 :: rq2 :: rq3 :: qs3, hl, hR =>
    cases s with
    | R n =>
      cases cp with
      | nil => simp [cprsize] at hl
      | cons s' cp' =>
        exact ih (rotr n (rq1 :: rq2 :: rq3 :: qs3)) (by rw [length_rotr, hl]; rfl)
          (List.cons_ne_nil _ _) hR
    | Y =>
      cases cp with
      | nil => rfl
      | cons s' cp' =>
        have hne : cfquizY rq1 rq2 (rqsY rq1 rq3 qs3) ≠ [] := by
          intro he
          change isQuizR (cfquizRec (cfquizY rq1 rq2 (rqsY rq1 rq3 qs3)) (s' :: cp')) = true at hR
          rw [he, qs0_notR] at hR
          exact absurd hR (by decide)
        refine ih _ ?_ (List.cons_ne_nil _ _) hR
        rw [length_cfquizY _ _ _ _ hne]
        simp only [List.length_cons, cprsize] at hl
        omega
    | H =>
      cases cp with
      | nil => simp [cprsize] at hl
      | cons s' cp' =>
        have hne : cfquizH rq1 rq2 (rqsH rq1 rq3 qs3) ≠ [] := by
          intro he
          change isQuizR (cfquizRec (cfquizH rq1 rq2 (rqsH rq1 rq3 qs3)) (s' :: cp')) = true at hR
          rw [he, qs0_notR] at hR
          exact absurd hR (by decide)
        refine ih _ ?_ (List.cons_ne_nil _ _) hR
        rw [length_cfquizH _ _ _ _ hne]
        simp only [List.length_cons, cprsize] at hl
        omega
    | _ =>
      rw [cfquizRec_other (by simp) (by simp) (by simp)] at hR
      exact absurd hR (by decide)

section ConfigQuiz

variable (cf : Config)

/-- The unfolding of `cfquiz` when the radius check succeeds. -/
private theorem cfquiz_eq (h : cpradius2 cf.cfprog (cpksize cf.cfprog) = true) :
    cfquiz cf = cfquizRec (List.replicate (cprsize cf.cfprog) ⟨false, 0, Qask0⟩) cf.cfprog := by
  simp [cfquiz, h]

variable {cf} (qzR : isQuizR (cfquiz cf) = true)
include qzR

/-- Coq `cp_rad2` (a section `Let`). -/
private theorem cp_rad2 : cpradius2 cf.cfprog (cpksize cf.cfprog) = true := by
  by_contra h
  simp only [cfquiz, h, ↓reduceIte] at qzR
  exact absurd qzR (by decide)

/-- Coq `cp_ok` (a section `Let`). -/
private theorem cp_ok : configProg cf.cfprog = true := by
  have h := cp_rad2 qzR
  rw [cfquiz_eq cf h] at qzR
  refine configProg_of_cfquizRec _ _ (List.length_replicate ..) ?_ qzR
  intro he
  rw [he] at h
  exact absurd h (by decide)

end ConfigQuiz

/-- The induction of the Coq proof of `cfquizP`: the program `catrev cp1 cp2` has been split
into its first steps `cp1` (already processed, in reverse order) and the rest `cp2`. -/
private theorem cfquizP_rec : ∀ (cp2 cp1 : Cprog), cubicProg cp1 = true →
    (cp2 = [] ∨ configProg cp2 = true) → ∀ qs : List RingQuestion,
    RqsProper (cpmap (cp1.reverseAux cp2)) (cpmap cp2) (injcp cp1 cp2) qs →
    isQuizR (cfquizRec qs cp2) = true →
    (∀ x ∈ (cpmap (cp1.reverseAux cp2)).pointee.cpring (cpmap (cp1.reverseAux cp2)).pointer,
        (cpmap (cp1.reverseAux cp2)).pointee.GoodRingArity x) ∧
      ∃ x0, (cpmap (cp1.reverseAux cp2)).pointee.ValidQuiz
        ((cpmap (cp1.reverseAux cp2)).pointee.cpring (cpmap (cp1.reverseAux cp2)).pointer) x0
        (cfquizRec qs cp2) := by
  intro cp2
  induction cp2 with
  | nil =>
    intro cp1 hcp1 _ qs hp hR
    have hall : ∀ y : (cpmap []).D, y ∈ ([false, true] : List (cpmap []).D) := by
      show ∀ y : Bool, y ∈ [false, true]
      decide
    exact cfquiz_base _ (cpmap []) (injcp cp1 []) false true (cpring0 true) (arity_cpmap0 false)
      (arity_cpmap0 true) (edge_injcp hcp1 [] false).symm (edge_injcp hcp1 [] true).symm hall hp hR
  | cons s cp2 ih =>
    intro cp1 hcp1 hcp2 qs hp hR
    have hcp2' : configProg (s :: cp2) = true := hcp2.resolve_left (List.cons_ne_nil _ _)
    match qs, hp, hR with
    | [], _, hR | [_], _, hR | [_, _], _, hR =>
      rw [cfquizRec_short (by simp)] at hR
      exact absurd hR (by decide)
    | rq1 :: rq2 :: rq3 :: qs3, hp, hR =>
    have hE := edge_injcp hcp1 (s :: cp2)
    have hN := node_injcp hcp1 (s :: cp2)
    have hF := cface_injcp hcp1 (s :: cp2)
    have Ih := injcp_inj cp1 (s :: cp2)
    cases s with
    | R n =>
      exact ih (.R n :: cp1) hcp1 (Or.inr hcp2') _
        (rqsProper_R _ (cpmap cp2) n (injcp cp1 (.R n :: cp2)) hp) hR
    | Y =>
      have hcp2Y : cp2 = [] ∨ configProg cp2 = true := by
        cases cp2 with
        | nil => exact Or.inl rfl
        | cons s' cp' => exact Or.inr hcp2'
      have hcub : cubicProg cp2 = true := by
        rcases hcp2Y with rfl | h
        · rfl
        · exact config_prog_cubic h
      have Ur : (cpmap cp2).pointee.Simple ((cpmap cp2).pointee.cpring (cpmap cp2).pointer) := by
        rcases hcp2Y with rfl | h
        · show cpmap0.Simple (cpmap0.cpring true)
          rw [cpring0, cpmap0.simple_cons, cpmap0.simple_cons]
          refine ⟨?_, ?_, List.nodup_nil⟩
          · rintro ⟨y, hy, hxy⟩
            rw [cface_cpmap0] at hxy
            subst hxy
            simp at hy
          · exact mem_fband_nil _ _
        · exact ((cpmap cp2).pointee.simple_cat _ _).1 (cpmap_simple h) |>.1
      have hne : cfquizY rq1 rq2 (rqsY rq1 rq3 qs3) ≠ [] := by
        intro he
        change isQuizR (cfquizRec (cfquizY rq1 rq2 (rqsY rq1 rq3 qs3)) cp2) = true at hR
        rw [he, qs0_notR] at hR
        exact absurd hR (by decide)
      exact ih (.Y :: cp1) hcp1 hcp2Y _
        (rqsProper_Y _ (cpmap cp2).pointee (cpmap cp2).pointer (injcp cp1 (.Y :: cp2)) Ih
          hE hN hF (cpmap_proper hcub) Ur hp hne) hR
    | H =>
      have hcp2H : configProg cp2 = true := hcp2'
      have Ur : (cpmap cp2).pointee.Simple ((cpmap cp2).pointee.cpring (cpmap cp2).pointer) :=
        ((cpmap cp2).pointee.simple_cat _ _).1 (cpmap_simple hcp2H) |>.1
      have hne : cfquizH rq1 rq2 (rqsH rq1 rq3 qs3) ≠ [] := by
        intro he
        change isQuizR (cfquizRec (cfquizH rq1 rq2 (rqsH rq1 rq3 qs3)) cp2) = true at hR
        rw [he, qs0_notR] at hR
        exact absurd hR (by decide)
      exact ih (.H :: cp1) hcp1 (Or.inr hcp2H) _
        (rqsProper_H _ (cpmap cp2).pointee (cpmap cp2).pointer (injcp cp1 (.H :: cp2)) Ih
          hE hN hF (cpmap_proper (config_prog_cubic hcp2H))
          (cfmap_long hcp2H) Ur hp hne) hR
    | _ =>
      rw [cfquizRec_other (by simp) (by simp) (by simp)] at hR
      exact absurd hR (by decide)

/-- The unfolding of `cpradius2`. -/
private theorem cpradius2_succ (cp : Cprog) (i : ℕ) :
    cpradius2 cp (i + 1) =
      ((cpadj ⟨(cfmask1 cp i).mr, (cpadj (cfmask1 cp i) cp).mk⟩ cp).mk.all id ||
        cpradius2 cp i) := by
  show (match cfmask1 cp i with
    | ⟨mr1, _⟩ =>
      match cpadj (cfmask1 cp i) cp with
      | ⟨_, mk1⟩ =>
        match cpadj ⟨mr1, mk1⟩ cp with
        | ⟨_, mk2⟩ => if mk2.all id then true else cpradius2 cp i) = _
  rcases cfmask1 cp i with ⟨mr1, mk0⟩
  rcases cpadj ⟨mr1, mk0⟩ cp with ⟨mr1', mk1⟩
  dsimp only
  rcases cpadj ⟨mr1, mk1⟩ cp with ⟨mr2, mk2⟩
  dsimp only
  cases mk2.all id <;> rfl

section ConfigQuiz

variable {cf : Config} (qzR : isQuizR (cfquiz cf) = true)
include qzR

/-- Coq `cpradius2P`: the kernel of a configuration whose quiz is valid has radius 2. -/
theorem cpradius2P : (cfmap cf).pointee.Radius2 ((cfmap cf).pointee.kernel (cfring cf)) := by
  have hcp := cp_ok qzR
  have hrad := cp_rad2 qzR
  set cp := cf.cfprog with hcpdef
  set M := (cpmap cp).pointee
  set r := M.cpring (cpmap cp).pointer
  have hker : M.kernel (cfring cf) = M.kernel r := by
    simp only [Hypermap.kernel, cfring, M.fband_rev]
    rfl
  rw [hker]
  have DkG : ∀ x, x ∈ M.kernel r ↔ x ∈ M.fband (cpker cp) := by
    intro x
    have hs := (M.simple_cat _ _).1 (cpmap_simple hcp)
    have hc := cpmap_cover hcp x
    rw [M.fband_cat] at hc
    constructor
    · intro hx
      exact hc.resolve_left hx
    · rintro ⟨z, hz, hxz⟩ ⟨y, hy, hxy⟩
      exact hs.2.1 ⟨z, hz, y, hy, connect_trans (M.cfaceC.1 hxz) hxy⟩
  suffices key : ∀ i, i ≤ cpksize cp → cpradius2 cp i = true → M.Radius2 (M.kernel r) from
    key _ le_rfl hrad
  intro i
  induction i with
  | zero => intro _ h; simp [cpradius2] at h
  | succ i ih =>
    intro hi hradi
    rw [cpradius2_succ, Bool.or_eq_true] at hradi
    rcases hradi with hall | hradi
    swap
    · exact ih (by omega) hradi
    set cm0 := cfmask1 cp i with hcm0
    set cm1 : Cfmask := ⟨cm0.mr, (cpadj cm0 cp).mk⟩ with hcm1
    have cm0ok : ProperCpmask cp cm0 := proper_cpmask1 cp i
    have cm1ok : ProperCpmask cp cm1 := ⟨cm0ok.1, (cpadj_proper cp cm0 cm0ok).2⟩
    have Dcm0 := cpmask1 (show i < cpksize cp by omega) hcp
    set x0 := (cpker cp).getD i (cpmap cp).pointer with hx0def
    have Ecm1 := cpmask_adj hcp cm0ok
    have Ecm2 := cpmask_adj hcp cm1ok
    have hmk2 : (cpadj cm1 cp).mk = List.replicate (cpker cp).length true := by
      rw [List.eq_replicate_iff]
      refine ⟨by rw [(cpadj_proper cp cm1 cm1ok).2, size_cpker hcp], fun b hb => ?_⟩
      exact List.all_eq_true.1 hall b hb
    have hx0 : x0 ∈ cpker cp := by
      rw [hx0def, List.getD_eq_getElem _ _ (by rw [size_cpker hcp]; omega)]
      exact List.getElem_mem _
    refine ⟨x0, (DkG x0).2 (M.ring_fband _ _ hx0), fun x hx => ?_⟩
    rw [M.at_radius2P (M.kernelF r)]
    have hx1 : x ∈ M.fband (cpmask (cpadj cm1 cp) cp) := by
      obtain ⟨y, hy, hxy⟩ := (DkG x).1 hx
      refine ⟨y, ?_, hxy⟩
      unfold cpmask
      rw [hmk2, mask_true le_rfl]
      exact List.mem_append_right _ hy
    obtain ⟨y, hy, hxy⟩ := (Ecm2 x).1 hx1
    have hy' : y ∈ mask (cpadj cm0 cp).mk (cpker cp) := by
      unfold cpmask at hy
      simp only [hcm1, hcm0, cfmask1, mask_false, List.nil_append] at hy
      exact hy
    obtain ⟨z, hxz, hzy⟩ := M.adjP.1 hxy
    have hz1 : M.edge z ∈ M.fband (cpmask (cpadj cm0 cp) cp) :=
      ⟨y, List.mem_append_right _ hy', hzy⟩
    obtain ⟨y', hy'0, hzy'⟩ := (Ecm1 _).1 hz1
    rw [Dcm0, List.mem_singleton] at hy'0
    subst hy'0
    rw [M.adjC (cpmap_plain (config_prog_cubic hcp))] at hzy'
    obtain ⟨t, htF, htR⟩ := M.adjP.1 hzy'
    exact ⟨t, z, ⟨htF, hxz⟩, (DkG _).2 ⟨y, mem_of_mem_mask hy', connect_trans htR hzy⟩, htR⟩

/-- Coq `cfquizP`: the ring faces of a configuration whose quiz is valid have good arities, and
its quiz is valid for its ring at some dart. -/
theorem cfquizP :
    (∀ x ∈ (cpmap cf.cfprog).pointee.cpring (cpmap cf.cfprog).pointer,
        (cpmap cf.cfprog).pointee.GoodRingArity x) ∧
      ∃ x0, (cpmap cf.cfprog).pointee.ValidQuiz
        ((cpmap cf.cfprog).pointee.cpring (cpmap cf.cfprog).pointer) x0 (cfquiz cf) := by
  have hcp := cp_ok qzR
  have hrad := cp_rad2 qzR
  rw [cfquiz_eq cf hrad] at qzR ⊢
  exact cfquizP_rec cf.cfprog [] rfl (Or.inr hcp) _ (rqsProper_init hcp) qzR

/-- Coq `embeddable_cfquiz`: a configuration whose quiz is valid is embeddable. -/
theorem embeddable_cfquiz : (cfmap cf).pointee.Embeddable (cfring cf) := by
  have hcp := cp_ok qzR
  have cpQ := config_prog_cubic hcp
  have hs := ((cpmap cf.cfprog).pointee.simple_cat _ _).1 (cpmap_simple hcp)
  exact
    { plain := cpmap_plain cpQ
      quasicubic := cpmap_cubic cpQ
      ucycle := (cpmap cf.cfprog).pointee.ucycle_rev_cpring _
      connected := cpmap_connected cpQ
      simple := ((cpmap cf.cfprog).pointee.simple_rev _).2 hs.1
      planar := cpmap_planar cpQ
      bridgeless := cpmap_bridgeless cpQ
      ring := fun x hx => (cfquizP qzR).1 x (List.mem_reverse.1 hx)
      kernel := cpradius2P qzR }

/-- Coq `valid_cfquiz`: the quiz of a configuration whose quiz is valid (i.e., satisfies
`isQuizR`) is valid for its ring at some dart. -/
theorem valid_cfquiz : ∃ u, (cfmap cf).pointee.ValidQuiz (cfring cf) u (cfquiz cf) := by
  obtain ⟨u, qz_ok, qz_u, Uqz, Eqz⟩ := (cfquizP qzR).2
  refine ⟨u, qz_ok, qz_u, Uqz, ?_⟩
  rw [Eqz]
  simp only [Hypermap.kernel, cfring, Hypermap.fband_rev]

end ConfigQuiz

end FourColor
