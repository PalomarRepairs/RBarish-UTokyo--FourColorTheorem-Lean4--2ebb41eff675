/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfQuiz
import FourColor.Configurations

/-!
# Quiz trees  (port of `quiztree.v`)

Compile a sequence of (reducible) configurations into a set of quizzes, and store them in a tree
structure according to the arities of the three center regions. Rotations and reflections are
also stored, so that the reducibility search can do a single lookup per triangle in the searched
part (see `redpart.v`). Reflections are not stored when the `cfsym` attribute is set (this
indicates a symmetrical configuration, for which this reflection would be redundant).

The middle nodes of the tree have four branches, for each of the arities 5, 6, 7 and 8; the top
node also has four branches, but with a different interpretation: the first is a subtree for
arities less than 9, and the other three for arities 9, 10, and 11; we don't need to store those
lower arities in the tree, since only the central region of our configurations can have more than
8 sides. Also, since such a large region can only match the hub, we don't store the rotations of
its quiz.

The quiz fork and trees are traversed in the inner loop of the unavoidability computation, so
their representation, like that of parts (see `part.v`), has been compressed, with the quiz
triples integrated in the list structure, and the tree structure feeding directly in the list
structure.

## Definitions (Coq name → Lean name)

* `quiz_tree` → `QuizTree` (constructors `QztNil`, `QztLeaf`, `QztNode`, `QztHubNode`, with
  Coq's names): the type of the tree storing the quizzes that test for the occurrence of any of
  the 633 reducible configurations, or of their rotation and/or reflection variants.
* `qzt_proper qt` → `qztProper qt`: `qt` is not `QztNil`.
* `qzt_put1 qa qr qt` → `qztPut1 qa qr qt`: `qt` with the branch `qt_a` corresponding to
  `qa : Qarity` replaced with `qr qt_a`, or `qt` if there is no such branch.
* `qzt_put3 qa1 qa2 qa3 q1 q2 q3 qt` → `qztPut3 ...`: `qt` extended with the triple
  `(q1, q2, q3)` stored under the arities `qa1`, `qa2`, `qa3`.
* `qzt_put3rot ...` → `qztPut3rot ...`: `qt` extended with the 3 rotations of `(q1, q2, q3)` at
  the 3 rotations of `(qa1, qa2, qa3)`.
* `qzt_put` → `qztPut`: `qztPut3` if `qa1 > 8`, `qztPut3rot` otherwise.
* `qzt_empty` → `qztEmpty`: the empty quiz tree, with the branching structure for all arities at
  the top, and the two small qarities below that.
* `normq q` → `normq q`: `q` with a top `Qask1`/`QaskL`/`QaskR` node replaced by an equivalent
  `QaskLR`.
* `store_qz qz qt` → `storeQz qz qt`: `qt` extended with `qz`.
* `store_cf_qz qz sym qt` → `storeCfQz qz sym qt`: `qt` extended with `qz`, plus `flipqz qz`
  unless `sym`.
* `cfquiz_tree_rec qt cfs`, `cfquiz_tree cfs` → `cfquizTreeRec qt cfs`, `cfquizTree cfs`: the
  quiz tree testing for all configurations in `cfs`. The quiz of each one is broken down into the
  arities of the faces incident to its central node, and a triple of residual questions; the tree
  sorts the triples according to the 3 arities (see above).
* `qzt_size qt` → `qztSize qt`: the number of triples stored in `qt`.
* `cf_main_arity cf` → `cfMainArity cf`: the arity of the face of the initial reference point in
  `cfmap cf` (the arity tested by the first question of `cfquiz cf`).
* `cf_qzt_size1 cf`, `cf_qzt_size cfs` → `cfQztSize1 cf`, `cfQztSize cfs`: the expected number
  of triples needed to store `cfs` in a quiz tree.
* `configs_compiled cfs` → `ConfigsCompiled cfs`: `cfQztSize cfs` and `qztSize (cfquizTree cfs)`
  match (a sanity check; the Coq file ends with it, commented out, for the 633 configurations,
  where both sides are 3361). It has a `Decidable` instance, so that it can be checked with
  `decide +kernel` on a list of configurations.
* `qzt_get1 qa qt` → `qztGet1 qa qt`: the subtree of `qt` corresponding to arity `qa`, defaulting
  to `QztNil` if `qa > 8` and `qt` is not a `QztHubNode`.
* `qzt_get2 qa2 qa3 qt`, `qzt_get3 qa1 qa2 qa3 qt` → `qztGet2`, `qztGet3`: the subtrees of `qt`
  indexed by `qa2, qa3` and by `qa1, qa2, qa3`.
* `qzt_truncate qt` → `qztTruncate qt`: `qt` with the top `QztHubNode` popped.

Section `FitQuizTree` (in `namespace FourColor.Hypermap`, for a hypermap `G` and a dart `x1`,
with `x2 = node x1` and `x3 = node x2`):

* `qzt_fita` → `G.QztFita x1`: the darts in the node of `x1` have arities in the `[5,11]` range.
* `qzt_fitl` → `G.QztFitl x1 qt`: some triple stored in the leaf list `qt` fits at the right
  steps of `x1`, `x2`, `x3`.
* `qzt_fit` → `G.QztFit x1 qt`: some quiz stored in `qt` fits at some dart in the node of `x1`.
* the local notation `quiz3` → `quiz3` (a definition).
* The main result, `qzt_fit_cfquiz`: if the quiz tree of `cfs1` fits at `x1` in a plain cubic
  map `G`, then some configuration of `cfs1` is embeddable and has a valid quiz that fits `G` or
  its mirror image.

## Porting notes

* The computational definitions (`qztProper`, `qztPut1`, `qztPut3`, `qztPut3rot`, `qztPut`,
  `qztEmpty`, `normq`, `storeQz`, `storeCfQz`, `cfquizTreeRec`, `cfquizTree`, `qztSize`,
  `cfMainArity`, `cfQztSize1`, `cfQztSize`, `qztGet1`, `qztGet2`, `qztGet3`, `qztTruncate`) are
  first-order (except for the function argument `qr` of `qztPut1`, as in Coq) and structurally
  recursive, so that they reduce in the kernel (`decide +kernel`). The comparisons of qarities
  (`8 < qa1`, `qa1r < qa2r`) compare their values in `ℕ`, as the Coq coercion does.
* `fitq` and `fitqz` are `Prop`s in `FourColor.Quiz` (arities are not computable here), so the
  Coq boolean tests `qzt_fita`, `qzt_fitl` and `qzt_fit` are the `Prop`s `QztFita`, `QztFitl` and
  `QztFit`, and the boolean equations `fit_normq`, `fitqz_rot` and `fitqz_swap` are `↔`
  statements. `configs_compiled` is the `Prop` `ConfigsCompiled`.
* The section variable `x1` is an explicit argument of `QztFita`, `QztFitl` and `QztFit`, and an
  implicit one of the lemmas; the section hypothesis `geoG : plain_cubic G` is the explicit
  argument `hG : G.PlainCubic` of the lemmas that use it (the section `Let`s `De2`, `Dn3` and
  `qgp1` are inlined). The unused section variable `cfs` is dropped.
* The Coq section `FitQuizTree` also contains `quiz3`, `qzt_get_put1`, `qzt_truncate` and
  `qzt_get1_truncate`, which do not depend on the hypermap; they are in `namespace FourColor`.
* In `qzt_fit_cfquiz` and `qzt_get1_truncate`, the Coq statement-level `let`s are unfolded;
  math-comp's `nth cf000 cfs1 i` is `cfs1.getD i cf000`. The Coq file imports `cfreducible` only
  for `cf000`, which is in `FourColor.Configurations` here.
* The final Coq comment (the sanity check `configs_compiled the_configs`, computed with
  `Eval compute`) is not a declaration. Evaluating `cfquizTree theConfigs` in the kernel in one
  declaration is too costly; the precomputed tree and its chunked kernel check belong to
  `FourColor.QuizData`.
-/

namespace FourColor

/-! ### The quiz tree type -/

/-- Coq `quiz_tree`: the tree storing the quizzes that test for the occurrence of the reducible
configurations. A `QztLeaf` holds a triple of questions and the rest of the leaf list; a
`QztNode` has four branches for the arities 5, 6, 7 and 8; a `QztHubNode` has a branch for the
arities less than 9, and three branches for the arities 9, 10 and 11. -/
inductive QuizTree : Type where
  /-- Coq `QztNil`: the empty tree. -/
  | QztNil
  /-- Coq `QztLeaf q1 q2 q3 t`: the question triple `(q1, q2, q3)`, followed by the leaves of
  `t`. -/
  | QztLeaf (q1 q2 q3 : Question) (t : QuizTree)
  /-- Coq `QztNode t5 t6 t7 t8`: branches for the arities 5, 6, 7 and 8. -/
  | QztNode (t5 t6 t7 t8 : QuizTree)
  /-- Coq `QztHubNode t58 t9 t10 t11`: a branch for the arities 5 to 8, and branches for the
  arities 9, 10 and 11. -/
  | QztHubNode (t58 t9 t10 t11 : QuizTree)
  deriving DecidableEq, Repr, Inhabited

export QuizTree (QztNil QztLeaf QztNode QztHubNode)

/-- Coq `qzt_proper qt`: the not-nil test. -/
def qztProper : QuizTree → Bool
  | QztNil => false
  | _ => true

/-! ### Update/store operations -/

/-- Coq `qzt_put1 qa qr t`: `t` with the branch `t_a` corresponding to `qa` replaced with
`qr t_a`, or `t` if there is no such branch. -/
def qztPut1 (qa : Qarity) (qr : QuizTree → QuizTree) (t : QuizTree) : QuizTree :=
  match t, qa with
  | QztNode t5 t6 t7 t8, Qa5 => QztNode (qr t5) t6 t7 t8
  | QztNode t5 t6 t7 t8, Qa6 => QztNode t5 (qr t6) t7 t8
  | QztNode t5 t6 t7 t8, Qa7 => QztNode t5 t6 (qr t7) t8
  | QztNode t5 t6 t7 t8, Qa8 => QztNode t5 t6 t7 (qr t8)
  | QztHubNode t58 t9 t10 t11, Qa9 => QztHubNode t58 (qr t9) t10 t11
  | QztHubNode t58 t9 t10 t11, Qa10 => QztHubNode t58 t9 (qr t10) t11
  | QztHubNode t58 t9 t10 t11, Qa11 => QztHubNode t58 t9 t10 (qr t11)
  | QztHubNode t58 t9 t10 t11, _ => QztHubNode (qztPut1 qa qr t58) t9 t10 t11
  | _, _ => t
termination_by structural t

/-- Coq `qzt_put3 qa1 qa2 qa3 q1 q2 q3`: store the triple `(q1, q2, q3)` under the arities
`qa1`, `qa2`, `qa3`. -/
def qztPut3 (qa1 qa2 qa3 : Qarity) (q1 q2 q3 : Question) : QuizTree → QuizTree :=
  qztPut1 qa1 (qztPut1 qa2 (qztPut1 qa3 (QztLeaf q1 q2 q3)))

/-- Coq `qzt_put3rot qa1 qa2 qa3 q1 q2 q3 t`: `t` extended with the 3 rotations of
`(q1, q2, q3)` at the 3 rotations of `(qa1, qa2, qa3)`. -/
def qztPut3rot (qa1 qa2 qa3 : Qarity) (q1 q2 q3 : Question) (t : QuizTree) : QuizTree :=
  qztPut3 qa1 qa2 qa3 q1 q2 q3
    (qztPut3 qa2 qa3 qa1 q2 q3 q1 (qztPut3 qa3 qa1 qa2 q3 q1 q2 t))

/-- Coq `qzt_put qa1 qa2 qa3 q1 q2 q3`: store the triple, and its rotations unless `qa1 > 8`
(a large central region can only match the hub). -/
def qztPut (qa1 qa2 qa3 : Qarity) (q1 q2 q3 : Question) : QuizTree → QuizTree :=
  if 8 < (qa1 : ℕ) then qztPut3 qa1 qa2 qa3 q1 q2 q3 else
  qztPut3rot qa1 qa2 qa3 q1 q2 q3

/-- Coq `qzt_empty`: the empty quiz tree, with the branching structure for all arities at the
top, and the two small qarities below that. -/
def qztEmpty : QuizTree :=
  let mkn (t : QuizTree) := QztNode t t t t
  let n2 := mkn (mkn QztNil)
  QztHubNode (mkn n2) n2 n2 n2

/-- Coq `normq q`: `q` with a top `Qask1`, `QaskL` or `QaskR` node replaced by an equivalent
`QaskLR` node. -/
def normq (q : Question) : Question :=
  match q with
  | Qask1 qa => QaskLR qa Qask0 Qask0
  | QaskL qa ql => QaskLR qa ql Qask0
  | QaskR qa qr => QaskLR qa Qask0 qr
  | _ => q

/-- Coq `store_qz qz`: store the quiz `qz` (which must consist of two `QaskR` questions, one of
which is binary after normalization) in a quiz tree. -/
def storeQz (qz : Quiz) : QuizTree → QuizTree :=
  match qz with
  | ⟨QaskR qa1 q1, QaskR qa2 q2⟩ =>
    match normq q1, normq q2 with
    | QaskLR qa1r q1l q1r, QaskLR qa2r q2l q2r =>
      if (qa1r : ℕ) < qa2r then qztPut qa1 qa2 qa1r q1l q2 q1r else
                                qztPut qa1 qa2r qa2 q1 q2r q2l
    | QaskLR qa1r q1l q1r, _ => qztPut qa1 qa2 qa1r q1l q2 q1r
    | _, QaskLR qa2r q2l q2r => qztPut qa1 qa2r qa2 q1 q2r q2l
    | _, _ => fun t => t
  | _ => fun t => t

/-- Coq `store_cf_qz qz sym t`: `t` extended with `qz`, plus `flipqz qz` unless `sym`. -/
def storeCfQz (qz : Quiz) (sym : Bool) (t : QuizTree) : QuizTree :=
  storeQz qz (if sym then t else storeQz (flipqz qz) t)

/-- Coq `cfquiz_tree_rec qt cfs`: `qt` extended with the quizzes of the configurations in `cfs`
(`QztNil` if some store operation fails to return a `QztHubNode`). -/
def cfquizTreeRec (qt : QuizTree) : List Config → QuizTree
  | [] => qt
  | cf :: cfs' =>
    let qt' := storeCfQz (cfquiz cf) cf.cfsym qt
    match qt' with
    | QztHubNode _ _ _ _ => cfquizTreeRec qt' cfs'
    | _ => QztNil

/-- Coq `cfquiz_tree cfs`: the quiz tree testing for all configurations in `cfs`. -/
def cfquizTree : List Config → QuizTree := cfquizTreeRec qztEmpty

/-! ### Sanity checks

Both computations should return the same result (3361 for the full configuration list). -/

/-- Coq `qzt_size t`: the number of triples stored in `t`. -/
def qztSize : QuizTree → ℕ
  | QztLeaf _ _ _ t' => qztSize t' + 1
  | QztNode t5 t6 t7 t8 => qztSize t5 + (qztSize t6 + (qztSize t7 + qztSize t8))
  | QztHubNode t58 t9 t10 t11 => qztSize t58 + (qztSize t9 + (qztSize t10 + qztSize t11))
  | _ => 0

/-- Coq `cf_main_arity cf`: the arity of the face of the initial reference point in `cfmap cf`
(the arity tested by the first question of `cfquiz cf`). -/
def cfMainArity (cf : Config) : ℕ :=
  match cfquiz cf with
  | ⟨QaskR qa _, _⟩ => qa
  | _ => 0

/-- Coq `cf_qzt_size1 cf`: the expected number of triples needed to store `cf` in a quiz tree
(math-comp's `double n` is `2 * n`). -/
def cfQztSize1 (cf : Config) : ℕ :=
  let nperm := if cfMainArity cf ≤ 8 then 3 else 1
  if cf.cfsym then nperm else 2 * nperm

/-- Coq `cf_qzt_size cfs`: the expected number of triples needed to store `cfs` in a quiz
tree. -/
def cfQztSize (cfs : List Config) : ℕ := cfs.foldr (fun cf n => cfQztSize1 cf + n) 0

/-- Coq `configs_compiled cfs`: `cfQztSize cfs` and `qztSize (cfquizTree cfs)` match. -/
def ConfigsCompiled (cfs : List Config) : Prop := qztSize (cfquizTree cfs) = cfQztSize cfs

/-- `ConfigsCompiled cfs` is decided by computing both sides (Coq proves the sanity check
`configs_compiled the_configs` by computation), e.g. with `decide +kernel`. -/
instance (cfs : List Config) : Decidable (ConfigsCompiled cfs) :=
  inferInstanceAs (Decidable (qztSize (cfquizTree cfs) = cfQztSize cfs))

/-! ### Lookup -/

/-- Coq `qzt_get1 qa t`: the subtree of `t` corresponding to arity `qa`, defaulting to `QztNil`
if `qa > 8` and `t` is not a `QztHubNode`. -/
def qztGet1 (qa : Qarity) (t : QuizTree) : QuizTree :=
  match t, qa with
  | QztNode t' _ _ _, Qa5 => t'
  | QztNode _ t' _ _, Qa6 => t'
  | QztNode _ _ t' _, Qa7 => t'
  | QztNode _ _ _ t', Qa8 => t'
  | QztHubNode _ t' _ _, Qa9 => t'
  | QztHubNode _ _ t' _, Qa10 => t'
  | QztHubNode _ _ _ t', Qa11 => t'
  | QztHubNode t' _ _ _, _ => qztGet1 qa t'
  | _, _ => QztNil
termination_by structural t

/-- Coq `qzt_get2 qa2 qa3 t`: the subtree of `t` indexed by `qa2`, `qa3`. -/
def qztGet2 (qa2 qa3 : Qarity) (t : QuizTree) : QuizTree := qztGet1 qa3 (qztGet1 qa2 t)

/-- Coq `qzt_get3 qa1 qa2 qa3 t`: the subtree of `t` indexed by `qa1`, `qa2`, `qa3`. -/
def qztGet3 (qa1 qa2 qa3 : Qarity) (t : QuizTree) : QuizTree := qztGet2 qa2 qa3 (qztGet1 qa1 t)

/-! ### Fitting quiz trees (Coq section `FitQuizTree`) -/

namespace Hypermap

section FitQuizTree

variable {D : Type*} (G : Hypermap D)

/-- Coq `fit_normq`. -/
theorem fit_normq (x : D) (q : Question) : G.fitq x (normq q) ↔ G.fitq x q := by
  cases q <;> simp [normq, fitq, flatq, walkq]

variable (x1 : D)

/-- Coq `qzt_fita` (a boolean test in Coq): the darts `x1`, `x2 = node x1` and `x3 = node x2`
have arities in the `[5,11]` range, i.e., their arities are the values of their qarities
`qarityOfNat (arity xi)` (Coq section `Let`s `ax1`, `ax2`, `ax3`). -/
def QztFita : Prop :=
  (qarityOfNat (G.arity x1) : ℕ) = G.arity x1 ∧
    (qarityOfNat (G.arity (G.node x1)) : ℕ) = G.arity (G.node x1) ∧
    (qarityOfNat (G.arity (G.node (G.node x1))) : ℕ) = G.arity (G.node (G.node x1))

/-- Coq `qzt_fitl t` (a boolean test in Coq): some triple `(q1, q2, q3)` in the leaf list `t`
fits at `qstepR x1`, `qstepR x2`, `qstepR x3`, where `x2 = node x1` and `x3 = node x2`. -/
def QztFitl : QuizTree → Prop
  | QztLeaf q1 q2 q3 t' =>
    (G.fitq (G.qstepR x1) q1 ∧ G.fitq (G.qstepR (G.node x1)) q2 ∧
        G.fitq (G.qstepR (G.node (G.node x1))) q3) ∨ QztFitl t'
  | _ => False

/-- Coq `qzt_fit t` (a boolean test in Coq): some quiz stored in `t` fits at some dart in the
node of `x1`. -/
def QztFit (t : QuizTree) : Prop :=
  G.QztFita x1 ∧
    G.QztFitl x1 (qztGet3 (qarityOfNat (G.arity x1)) (qarityOfNat (G.arity (G.node x1)))
      (qarityOfNat (G.arity (G.node (G.node x1)))) t)

end FitQuizTree

end Hypermap

/-- Coq local notation `quiz3` (section `FitQuizTree`): the quiz
`Quiz (QaskR qa1 (QaskLR qa3 q1 q3)) (QaskR qa2 q2)` stored by `qztPut3 qa1 qa2 qa3 q1 q2 q3`. -/
def quiz3 (qa1 qa2 qa3 : Qarity) (q1 q2 q3 : Question) : Quiz :=
  ⟨QaskR qa1 (QaskLR qa3 q1 q3), QaskR qa2 q2⟩

/-- Coq `qzt_get_put1` (section `FitQuizTree`). -/
theorem qzt_get_put1 (qa qa' : Qarity) (qr : QuizTree → QuizTree) (t : QuizTree) :
    (qa = qa' ∧ qr (qztGet1 qa t) = qztGet1 qa (qztPut1 qa' qr t)) ∨
      qztGet1 qa t = qztGet1 qa (qztPut1 qa' qr t) := by
  induction t with
  | QztNil => right; cases qa' <;> rfl
  | QztLeaf q1 q2 q3 t _ => right; cases qa' <;> rfl
  | QztNode t5 t6 t7 t8 _ _ _ _ => cases qa' <;> cases qa <;> simp [qztPut1, qztGet1]
  | QztHubNode t58 t9 t10 t11 ih _ _ _ =>
    cases qa' <;> cases qa <;> first | exact ih | simp [qztPut1, qztGet1]

namespace Hypermap

section FitQuizTree

variable {D : Type*} (G : Hypermap D)

/-! Unfolding `fitq` and `fitqz` (helpers). -/

/-- `fitq` on a `QaskR` question. -/
private theorem fitq_askR (x : D) (qa : Qarity) (q : Question) :
    G.fitq x (QaskR qa q) ↔ (qa : ℕ) = G.arity x ∧ G.fitq (G.qstepR x) q := by
  simp only [fitq, flatq, walkq, List.map_cons, List.cons.injEq]

/-- `fitq` on a `QaskLR` question. -/
private theorem fitq_askLR (x : D) (qa : Qarity) (ql qr : Question) :
    G.fitq x (QaskLR qa ql qr) ↔
      (qa : ℕ) = G.arity x ∧ G.fitq (G.qstepL x) ql ∧ G.fitq (G.qstepR x) qr := by
  rw [fitq, flatq, walkq, List.map_cons, List.cons.injEq, fitq_cat]
  exact Iff.rfl

/-- `fitqz` on a quiz `⟨q0, q1⟩`. -/
private theorem fitqz_mk' (x : D) (q0 q1 : Question) :
    G.fitqz x ⟨q0, q1⟩ ↔ G.fitq x q0 ∧ G.fitq (G.edge x) q1 := by
  rw [fitqz, flatqz, walkqz, fitq_cat]
  rfl

variable [Finite D]

/-- `fitqz` on a `quiz3` quiz at `edge z`, in a plain cubic map: the three questions fit at the
right steps of the three darts `z`, `node z`, `node (node z)` of the node of `z`, which have the
corresponding arities. -/
private theorem fitqz_quiz3 (hG : G.PlainCubic) (z : D) (qa1 qa2 qa3 : Qarity)
    (q1 q2 q3 : Question) :
    G.fitqz (G.edge z) (quiz3 qa1 qa2 qa3 q1 q2 q3) ↔
      ((qa1 : ℕ) = G.arity (G.node (G.node z)) ∧ G.fitq (G.qstepR (G.node (G.node z))) q1) ∧
      ((qa2 : ℕ) = G.arity z ∧ G.fitq (G.qstepR z) q2) ∧
      ((qa3 : ℕ) = G.arity (G.node z) ∧ G.fitq (G.qstepR (G.node z)) q3) := by
  have hA : G.arity (G.edge z) = G.arity (G.node (G.node z)) := by
    rw [G.cubic_eq' hG.cubic, G.arity_face]
  have hR : G.qstepR (G.edge z) = G.node z := by rw [qstepR, G.plain_eq hG.plain]
  rw [quiz3, fitqz_mk', fitq_askR, fitq_askR, hA, hR, fitq_askLR, G.plain_eq hG.plain]
  constructor
  · rintro ⟨⟨h1, h3, f1, f3⟩, h2, f2⟩
    exact ⟨⟨h1, f1⟩, ⟨h2, f2⟩, ⟨h3, f3⟩⟩
  · rintro ⟨⟨h1, f1⟩, ⟨h2, f2⟩, ⟨h3, f3⟩⟩
    exact ⟨⟨h1, h3, f1, f3⟩, h2, f2⟩

variable {x1 : D}

/-- Coq `qzt_fit_put3`. -/
theorem qzt_fit_put3 (hG : G.PlainCubic) (qa1 qa2 qa3 : Qarity) (q1 q2 q3 : Question)
    (t : QuizTree) :
    G.QztFit x1 (qztPut3 qa1 qa2 qa3 q1 q2 q3 t) →
      G.fitqz (G.edge (G.node x1)) (quiz3 qa1 qa2 qa3 q1 q2 q3) ∨ G.QztFit x1 t := by
  rintro ⟨hfa, hfl⟩
  obtain ⟨e1, e2, e3⟩ := hfa
  generalize ha1 : qarityOfNat (G.arity x1) = a1 at e1 hfl
  generalize ha2 : qarityOfNat (G.arity (G.node x1)) = a2 at e2 hfl
  generalize ha3 : qarityOfNat (G.arity (G.node (G.node x1))) = a3 at e3 hfl
  have key : qztGet3 a1 a2 a3 (qztPut3 qa1 qa2 qa3 q1 q2 q3 t) = qztGet3 a1 a2 a3 t ∨
      (a1 = qa1 ∧ a2 = qa2 ∧ a3 = qa3 ∧
        qztGet3 a1 a2 a3 (qztPut3 qa1 qa2 qa3 q1 q2 q3 t) =
          QztLeaf q1 q2 q3 (qztGet3 a1 a2 a3 t)) := by
    unfold qztGet3 qztGet2 qztPut3
    rcases qzt_get_put1 a1 qa1 (qztPut1 qa2 (qztPut1 qa3 (QztLeaf q1 q2 q3))) t with
      ⟨h1, h1'⟩ | h1
    · rw [← h1']
      rcases qzt_get_put1 a2 qa2 (qztPut1 qa3 (QztLeaf q1 q2 q3)) (qztGet1 a1 t) with
        ⟨h2, h2'⟩ | h2
      · rw [← h2']
        rcases qzt_get_put1 a3 qa3 (QztLeaf q1 q2 q3) (qztGet1 a2 (qztGet1 a1 t)) with
          ⟨h3, h3'⟩ | h3
        · exact Or.inr ⟨h1, h2, h3, h3'.symm⟩
        · exact Or.inl h3.symm
      · rw [← h2]
        exact Or.inl rfl
    · rw [← h1]
      exact Or.inl rfl
  have hfit : G.QztFita x1 := by
    refine ⟨?_, ?_, ?_⟩
    · rw [ha1]; exact e1
    · rw [ha2]; exact e2
    · rw [ha3]; exact e3
  rcases key with hk | ⟨rfl, rfl, rfl, hk⟩
  · right
    refine ⟨hfit, ?_⟩
    rw [ha1, ha2, ha3, ← hk]
    exact hfl
  · rw [hk] at hfl
    rcases hfl with ⟨f1, f2, f3⟩ | hfl
    · left
      rw [fitqz_quiz3 G hG, G.cubic_eq hG.cubic]
      exact ⟨⟨e1, f1⟩, ⟨e2, f2⟩, ⟨e3, f3⟩⟩
    · right
      refine ⟨hfit, ?_⟩
      rw [ha1, ha2, ha3]
      exact hfl

/-- Coq `fitqz_rot`. -/
theorem fitqz_rot (hG : G.PlainCubic) (y : D) (qa1 qa2 qa3 : Qarity) (q1 q2 q3 : Question) :
    G.fitqz y (quiz3 qa1 qa2 qa3 q1 q2 q3) ↔
      G.fitqz (G.edge (G.face y)) (quiz3 qa3 qa1 qa2 q3 q1 q2) := by
  obtain ⟨z, rfl⟩ : ∃ z, y = G.edge z := ⟨G.edge y, (G.plain_eq hG.plain y).symm⟩
  have hz : G.face (G.edge z) = G.node (G.node z) := (G.cubic_eq' hG.cubic z).symm
  have h4 : G.node (G.node (G.node (G.node z))) = G.node z := G.cubic_eq hG.cubic (G.node z)
  rw [hz, fitqz_quiz3 G hG, fitqz_quiz3 G hG, h4, G.cubic_eq hG.cubic]
  constructor
  · rintro ⟨a, b, c⟩
    exact ⟨c, a, b⟩
  · rintro ⟨c, a, b⟩
    exact ⟨a, b, c⟩

/-- Coq `qzt_fit_put`. -/
theorem qzt_fit_put (hG : G.PlainCubic) (qa1 qa2 qa3 : Qarity) (q1 q2 q3 : Question)
    (t : QuizTree) :
    G.QztFit x1 (qztPut qa1 qa2 qa3 q1 q2 q3 t) →
      (∃ y, G.fitqz y (quiz3 qa1 qa2 qa3 q1 q2 q3)) ∨ G.QztFit x1 t := by
  unfold qztPut qztPut3rot
  split
  · intro h
    rcases G.qzt_fit_put3 hG _ _ _ _ _ _ _ h with h | h
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr h
  · intro h
    rcases G.qzt_fit_put3 hG _ _ _ _ _ _ _ h with h | h
    · exact Or.inl ⟨_, h⟩
    rcases G.qzt_fit_put3 hG _ _ _ _ _ _ _ h with h | h
    · rw [fitqz_rot G hG, G.nodeK] at h
      exact Or.inl ⟨_, h⟩
    rcases G.qzt_fit_put3 hG _ _ _ _ _ _ _ h with h | h
    · rw [fitqz_rot G hG, fitqz_rot G hG, G.nodeK, ← G.cubic_eq' hG.cubic] at h
      exact Or.inl ⟨_, h⟩
    · exact Or.inr h

/-- Coq `fitqz_swap`. -/
theorem fitqz_swap (hG : G.PlainCubic) (y : D) (qa1 qa2 qa3 : Qarity) (q1 q2 q3 : Question) :
    G.fitqz y (quiz3 qa1 qa2 qa3 q1 q2 q3) ↔
      G.fitqz (G.face y) ⟨QaskR qa1 q1, QaskR qa3 (QaskLR qa2 q3 q2)⟩ := by
  obtain ⟨z, rfl⟩ : ∃ z, y = G.edge z := ⟨G.edge y, (G.plain_eq hG.plain y).symm⟩
  have hz : G.face (G.edge z) = G.node (G.node z) := (G.cubic_eq' hG.cubic z).symm
  have hA : G.arity (G.edge (G.node (G.node z))) = G.arity (G.node z) := by
    rw [← G.arity_face, ← G.cubic_eq' hG.cubic, G.cubic_eq hG.cubic]
  have hR : G.qstepR (G.edge (G.node (G.node z))) = z := by
    rw [qstepR, G.plain_eq hG.plain, G.cubic_eq hG.cubic]
  rw [fitqz_quiz3 G hG, hz, fitqz_mk', fitq_askR, fitq_askR, hA, hR, fitq_askLR]
  constructor
  · rintro ⟨⟨h1, f1⟩, ⟨h2, f2⟩, ⟨h3, f3⟩⟩
    exact ⟨⟨h1, f1⟩, h3, h2, f3, f2⟩
  · rintro ⟨⟨h1, f1⟩, h3, h2, f3, f2⟩
    exact ⟨⟨h1, f1⟩, ⟨h2, f2⟩, ⟨h3, f3⟩⟩

omit [Finite D] in
/-- A quiz `⟨QaskR qa q, q'⟩` only depends on `q` through `fitq`. -/
private theorem fitqz_askR_congr {q q' : Question} (hq : ∀ x, G.fitq x q ↔ G.fitq x q')
    (y : D) (qa : Qarity) (q1 : Question) :
    G.fitqz y ⟨QaskR qa q, q1⟩ ↔ G.fitqz y ⟨QaskR qa q', q1⟩ := by
  rw [fitqz_mk', fitqz_mk', fitq_askR, fitq_askR, hq]

/-- Coq `qzt_fit_store`. -/
theorem qzt_fit_store (hG : G.PlainCubic) (qz : Quiz) (t : QuizTree) :
    G.QztFit x1 (storeQz qz t) →
      (isQuizR qz = true ∧ ∃ y, G.fitqz y qz) ∨ G.QztFit x1 t := by
  obtain ⟨q1, q2⟩ := qz
  cases q1 with
  | QaskR qa1 q1 =>
    cases q2 with
    | QaskR qa2 q2 =>
      intro qz_t
      suffices fit_qzt : (∃ y, G.fitqz y ⟨QaskR qa1 q1, QaskR qa2 q2⟩) ∨ G.QztFit x1 t by
        rcases fit_qzt with h | h
        · exact Or.inl ⟨rfl, h⟩
        · exact Or.inr h
      have fit_q1LR : ∀ qa1r q1l q1r, normq q1 = QaskLR qa1r q1l q1r →
          G.QztFit x1 (qztPut qa1 qa2 qa1r q1l q2 q1r t) →
            (∃ y, G.fitqz y ⟨QaskR qa1 q1, QaskR qa2 q2⟩) ∨ G.QztFit x1 t := by
        intro qa1r q1l q1r Dq1 h
        rcases G.qzt_fit_put hG _ _ _ _ _ _ _ h with ⟨y, fit_y⟩ | h
        · refine Or.inl ⟨y, ?_⟩
          rw [quiz3, ← Dq1, fitqz_askR_congr G (G.fit_normq · q1)] at fit_y
          exact fit_y
        · exact Or.inr h
      have fit_q2LR : ∀ qa2r q2l q2r, normq q2 = QaskLR qa2r q2l q2r →
          G.QztFit x1 (qztPut qa1 qa2r qa2 q1 q2r q2l t) →
            (∃ y, G.fitqz y ⟨QaskR qa1 q1, QaskR qa2 q2⟩) ∨ G.QztFit x1 t := by
        intro qa2r q2l q2r Dq2 h
        rcases G.qzt_fit_put hG _ _ _ _ _ _ _ h with ⟨y, fit_y⟩ | h
        · refine Or.inl ⟨G.face y, ?_⟩
          rw [fitqz_swap G hG, ← Dq2] at fit_y
          rw [fitqz_mk', fitq_askR, fitq_askR, ← G.fit_normq _ q2]
          rw [fitqz_mk', fitq_askR, fitq_askR] at fit_y
          exact fit_y
        · exact Or.inr h
      cases hq1 : normq q1 <;> cases hq2 : normq q2 <;>
        simp only [storeQz, hq1, hq2] at qz_t <;>
        first
        | exact Or.inr qz_t
        | exact fit_q1LR _ _ _ hq1 qz_t
        | exact fit_q2LR _ _ _ hq2 qz_t
        | (split at qz_t
           · exact fit_q1LR _ _ _ hq1 qz_t
           · exact fit_q2LR _ _ _ hq2 qz_t)
    | _ => intro h; exact Or.inr h
  | _ => intro h; exact Or.inr h

/-- `flipqz` only changes the quizzes satisfying `isQuizR`, into quizzes satisfying `isQuizR`. -/
private theorem isQuizR_of_flipqz {qz : Quiz} (h : isQuizR (flipqz qz) = true) :
    isQuizR qz = true := by
  obtain ⟨q0, q1⟩ := qz
  cases q0 <;> cases q1 <;> simp_all [flipqz, isQuizR, isQaskR]

/-- Coq `qzt_fit_store_cf`. -/
theorem qzt_fit_store_cf (hG : G.PlainCubic) (qz : Quiz) (sym : Bool) (t : QuizTree) :
    G.QztFit x1 (storeCfQz qz sym t) →
      (isQuizR qz = true ∧ ((∃ y, G.fitqz y qz) ∨ (∃ y, G.mirror.fitqz y qz))) ∨
        G.QztFit x1 t := by
  unfold storeCfQz
  intro h
  rcases G.qzt_fit_store hG _ _ h with ⟨qzR, y, fit_y⟩ | h
  · exact Or.inl ⟨qzR, Or.inl ⟨y, fit_y⟩⟩
  cases sym with
  | true => exact Or.inr h
  | false =>
    rcases G.qzt_fit_store hG _ _ h with ⟨qzR, y, fit_y⟩ | h
    · have qzR' := isQuizR_of_flipqz qzR
      rw [G.fitqz_flip y qz hG qzR'] at fit_y
      exact Or.inl ⟨qzR', Or.inr ⟨G.face y, fit_y⟩⟩
    · exact Or.inr h

omit [Finite D] in
/-- `QztFitl` fails on `QztNil`. -/
private theorem not_qztFit_nil : ¬ G.QztFit x1 QztNil := by
  rintro ⟨_, hfl⟩
  have e : ∀ a1 a2 a3, qztGet3 a1 a2 a3 QztNil = QztNil := by
    intro a1 a2 a3
    cases a1 <;> cases a2 <;> cases a3 <;> rfl
  rw [e] at hfl
  exact hfl

omit [Finite D] in
/-- `QztFitl` fails on `qztEmpty`. -/
private theorem not_qztFit_empty : ¬ G.QztFit x1 qztEmpty := by
  rintro ⟨_, hfl⟩
  have e : ∀ a1 a2 a3, qztGet3 a1 a2 a3 qztEmpty = QztNil := by
    intro a1 a2 a3
    cases a1 <;> cases a2 <;> cases a3 <;> rfl
  rw [e] at hfl
  exact hfl

/-- Coq `qzt_fit_cfquiz`: if the quiz tree of `cfs1` fits at `x1`, then some configuration of
`cfs1` is embeddable and has a valid quiz that fits `G` or its mirror image. -/
theorem qzt_fit_cfquiz (hG : G.PlainCubic) (cfs1 : List Config) :
    G.QztFit x1 (cfquizTree cfs1) →
      ∃ i, i < cfs1.length ∧ ∃ qz : Quiz,
        ((∃ y, G.fitqz y qz) ∨ (∃ y, G.mirror.fitqz y qz)) ∧
          ((cfmap (cfs1.getD i cf000)).pointee.Embeddable (cfring (cfs1.getD i cf000)) ∧
            ∃ u, (cfmap (cfs1.getD i cf000)).pointee.ValidQuiz (cfring (cfs1.getD i cf000)) u
              qz) := by
  unfold cfquizTree
  have fit'qt0 := G.not_qztFit_empty (x1 := x1)
  generalize qztEmpty = qt0 at fit'qt0
  induction cfs1 generalizing qt0 with
  | nil => intro h; exact absurd h fit'qt0
  | cons cf cfs1 IHcfs =>
    intro fit_cfs1
    simp only [cfquizTreeRec] at fit_cfs1
    split at fit_cfs1
    · by_cases fit_qt : G.QztFit x1 (storeCfQz (cfquiz cf) cf.cfsym qt0)
      · rcases G.qzt_fit_store_cf hG _ _ _ fit_qt with ⟨cfR, fit_cf⟩ | h
        · -- `(cf :: cfs1).getD 0 cf000` is `cf` by definition
          exact ⟨0, Nat.succ_pos _, cfquiz cf, fit_cf, embeddable_cfquiz cfR, valid_cfquiz cfR⟩
        · exact absurd h fit'qt0
      · obtain ⟨i, hi, rest⟩ := IHcfs _ fit_qt fit_cfs1
        -- `(cf :: cfs1).getD (i + 1) cf000` is `cfs1.getD i cf000` by definition
        exact ⟨i + 1, Nat.succ_lt_succ hi, rest⟩
    · exact absurd fit_cfs1 G.not_qztFit_nil

end FitQuizTree

end Hypermap

/-- Coq `qzt_truncate t` (section `FitQuizTree`): `t` with the top `QztHubNode` popped. -/
def qztTruncate (t : QuizTree) : QuizTree :=
  match t with
  | QztHubNode t58@(QztNode _ _ _ _) _ _ _ => t58
  | _ => t

/-- Coq `qzt_get1_truncate` (section `FitQuizTree`; the Coq statement names
`t' := qzt_get1 qa (qzt_truncate t)` with a `let`). -/
theorem qzt_get1_truncate (qa : Qarity) (t : QuizTree) :
    qztProper (qztGet1 qa (qztTruncate t)) = true →
      qztGet1 qa (qztTruncate t) = qztGet1 qa t := by
  cases t with
  | QztHubNode t58 t9 t10 t11 =>
    cases t58 with
    | QztNode t5 t6 t7 t8 => cases qa <;> simp [qztTruncate, qztGet1, qztProper]
    | _ => intro _; rfl
  | _ => intro _; rfl

end FourColor
