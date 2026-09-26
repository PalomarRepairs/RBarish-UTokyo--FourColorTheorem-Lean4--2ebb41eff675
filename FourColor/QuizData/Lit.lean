/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.QuizData.Basic
import FourColor.Discharge

/-!
# Literal injection for the precomputed data (meta code)

Coq's `present.v` defines two values with `Eval vm_compute`: `the_quiz_tree`, the fully evaluated
quiz tree of the 633 configurations, and `the_drule_fork n`, the drule forks for the hub sizes
below 12. Here they become literal definitions: the commands of this file compute the values with
the compiled code of the library (at elaboration time), turn them into `Expr`s made of
constructors only, and add them to the environment with `addDecl` (the kernel type-checks them;
the elaborator never sees the terms, which would be far too slow). The agreement of each literal
with the defining computation is proved by kernel computation, in the other
`FourColor.QuizData.*` modules.

This module contains only meta code: nothing in it is used by a statement or a proof, only by the
commands that create the literal definitions (and the simp set `quizdata_cfquiz`).

* `#quizdata_quizzes i k` defines `FourColor.QuizData.qzNNN : Quiz`, the literal value of
  `cfquiz cfNNN`, for the `k` configurations numbered `NNN = i, ..., i + k - 1` (as in Coq,
  configuration `cfNNN` has index `NNN - 1` in `theConfigs`).
* `#quizdata_print_checks i k` prints the source of the theorems
  `cfquiz_cfNNN : cfquiz cfNNN = qzNNN` of the files `FourColor/QuizData/Quizzes*.lean`, with
  their radius certificates (`radiusCert`); it is how those files were written.
* `#quizdata_blocks cb qb n` defines `cb : List (List Config)`, the constants `cfNNN` of
  `theConfigs` cut into blocks of `n`, and `qb : List (List Quiz)`, the constants `qzNNN` in the
  same blocks.
* `#quizdata_tree t` defines `t : QuizTree` as the literal value of `cfquizTree theConfigs`.
* `#quizdata_drules r n source` (resp. `target`) defines `r : Drules` as the literal value of
  `pickSourceDrules n theDrules` (resp. `pickTargetDrules n theDrules`).

The terms are closed and made of constructors, `List.nil`/`List.cons`, and constants; they are
at most a few hundred levels deep (the longest leaf list of the quiz tree has 239 triples), below
the nesting limit of Palomar's checkers.
-/

/-- The simp set of the lemmas `cfquiz_cfNNN : cfquiz cfNNN = qzNNN`. -/
register_simp_attr quizdata_cfquiz

namespace FourColor.QuizData

open Lean Elab Command Meta

/-! ### From values to `Expr`s -/

/-- The `Expr` of a `Qarity` value. -/
def qarityExpr : Qarity → Expr
  | Qa5 => mkConst ``Qarity.Qa5
  | Qa6 => mkConst ``Qarity.Qa6
  | Qa7 => mkConst ``Qarity.Qa7
  | Qa8 => mkConst ``Qarity.Qa8
  | Qa9 => mkConst ``Qarity.Qa9
  | Qa10 => mkConst ``Qarity.Qa10
  | Qa11 => mkConst ``Qarity.Qa11

/-- The `Expr` of a `Question` value. -/
def questionExpr : Question → Expr
  | Qask0 => mkConst ``Question.Qask0
  | Qask1 qa => mkApp (mkConst ``Question.Qask1) (qarityExpr qa)
  | QaskL qa q => mkApp2 (mkConst ``Question.QaskL) (qarityExpr qa) (questionExpr q)
  | QaskR qa q => mkApp2 (mkConst ``Question.QaskR) (qarityExpr qa) (questionExpr q)
  | QaskLR qa ql qr =>
    mkApp3 (mkConst ``Question.QaskLR) (qarityExpr qa) (questionExpr ql) (questionExpr qr)
  | QaskLL qa q => mkApp2 (mkConst ``Question.QaskLL) (qarityExpr qa) (questionExpr q)
  | QaskRR qa q => mkApp2 (mkConst ``Question.QaskRR) (qarityExpr qa) (questionExpr q)

/-- The `Expr` of a `Quiz` value. -/
def quizExpr (qz : Quiz) : Expr :=
  mkApp2 (mkConst ``Quiz.mk) (questionExpr qz.q0) (questionExpr qz.q1)

/-- The `Expr` of a `QuizTree` value. -/
def quizTreeExpr : QuizTree → Expr
  | QztNil => mkConst ``QuizTree.QztNil
  | QztLeaf q1 q2 q3 t =>
    mkApp4 (mkConst ``QuizTree.QztLeaf) (questionExpr q1) (questionExpr q2) (questionExpr q3)
      (quizTreeExpr t)
  | QztNode t5 t6 t7 t8 =>
    mkApp4 (mkConst ``QuizTree.QztNode) (quizTreeExpr t5) (quizTreeExpr t6) (quizTreeExpr t7)
      (quizTreeExpr t8)
  | QztHubNode t58 t9 t10 t11 =>
    mkApp4 (mkConst ``QuizTree.QztHubNode) (quizTreeExpr t58) (quizTreeExpr t9)
      (quizTreeExpr t10) (quizTreeExpr t11)

/-- The `Expr` of a `Prange` value. -/
def prangeExpr : Prange → Expr
  | .pr55 => mkConst ``Prange.pr55
  | .pr66 => mkConst ``Prange.pr66
  | .pr77 => mkConst ``Prange.pr77
  | .pr88 => mkConst ``Prange.pr88
  | .pr99 => mkConst ``Prange.pr99
  | .pr56 => mkConst ``Prange.pr56
  | .pr67 => mkConst ``Prange.pr67
  | .pr78 => mkConst ``Prange.pr78
  | .pr89 => mkConst ``Prange.pr89
  | .pr57 => mkConst ``Prange.pr57
  | .pr68 => mkConst ``Prange.pr68
  | .pr79 => mkConst ``Prange.pr79
  | .pr58 => mkConst ``Prange.pr58
  | .pr69 => mkConst ``Prange.pr69
  | .pr59 => mkConst ``Prange.pr59

/-- The `Expr` of a `Part` value. -/
def partExpr : Part → Expr
  | .nil => mkConst ``Part.nil
  | .cons s h p => mkApp3 (mkConst ``Part.cons) (prangeExpr s) (prangeExpr h) (partExpr p)
  | .cons6 h f1 p => mkApp3 (mkConst ``Part.cons6) (prangeExpr h) (prangeExpr f1) (partExpr p)
  | .cons7 h f1 f2 p =>
    mkApp4 (mkConst ``Part.cons7) (prangeExpr h) (prangeExpr f1) (prangeExpr f2) (partExpr p)
  | .cons8 h f1 f2 f3 p =>
    mkApp5 (mkConst ``Part.cons8) (prangeExpr h) (prangeExpr f1) (prangeExpr f2)
      (prangeExpr f3) (partExpr p)

/-- The `Expr` of the list `[x₀, ..., xₙ₋₁] : List α`, from `α` and the `Expr`s of the
elements. -/
def listExpr (α : Expr) (xs : List Expr) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) α x acc)
    (mkApp (mkConst ``List.nil [Level.zero]) α)

/-- The `Expr` of the type `List α`. -/
def listTypeExpr (α : Expr) : Expr := mkApp (mkConst ``List [Level.zero]) α

/-! ### Adding literal definitions -/

/-- Add the closed definition `name : type := value` with the docstring `doc` (checked by the
kernel), and compile it, so that computable definitions may use it. -/
def addLiteralDef (name : Name) (type value : Expr) (doc : String) : CoreM Unit := do
  let value := ShareCommon.shareCommon' value
  addDecl (.defnDecl {
    name, levelParams := [], type, value, safety := .safe,
    hints := .regular (getMaxHeight (← getEnv) value + 1) })
  enableRealizationsForConst name
  addDocStringCore name doc
  compileDecls #[name]

/-- `i` with three digits. -/
def threeDigits (i : ℕ) : String :=
  let s := toString i
  "".pushn '0' (3 - s.length) ++ s

/-- The name `FourColor.cfNNN` of configuration number `i`. -/
def configName (i : ℕ) : Name := .str `FourColor ("cf" ++ threeDigits i)

/-- The name `FourColor.QuizData.qzNNN` of the literal quiz of configuration number `i`. -/
def quizName (i : ℕ) : Name := .str `FourColor.QuizData ("qz" ++ threeDigits i)

/-- The configurations numbered `i, ..., i + k - 1`, with their numbers. -/
def configRange (i k : ℕ) : CommandElabM (List (ℕ × Config)) := do
  let cfs := (theConfigs.drop (i - 1)).take k
  unless 1 ≤ i ∧ cfs.length = k do
    throwError "configurations {i} to {i + k - 1} do not exist"
  for j in [i:i + k] do
    unless (← getEnv).contains (configName j) do
      throwError "unknown constant {configName j}"
  return (List.range' i k).zip cfs

/-- The radius certificate of the program `cp`: the kernel face with which `cpradius2 cp
(cpksize cp)` succeeds (the last `i < cpksize cp` such that `cpradius2At cp i`), if any. -/
def radiusCert (cp : Cprog) : Option ℕ :=
  (List.range (cpksize cp)).reverse.find? (cpradius2At cp ·)

/-! ### The commands -/

/-- `#quizdata_quizzes i k` defines `FourColor.QuizData.qzNNN : Quiz`, the literal value of
`cfquiz cfNNN`, for `NNN = i, ..., i + k - 1`. -/
elab "#quizdata_quizzes " i:num k:num : command => do
  for (j, cf) in ← configRange i.getNat k.getNat do
    liftCoreM <| addLiteralDef (quizName j) (mkConst ``Quiz) (quizExpr (cfquiz cf))
      s!"The quiz `cfquiz cf{threeDigits j}`, as a literal (computed by `#quizdata_quizzes`)."

/-- `#quizdata_print_checks i k` prints the source of the theorems
`cfquiz_cfNNN : cfquiz cfNNN = qzNNN` for `NNN = i, ..., i + k - 1`, each proved by
`cfquiz_eq_of_cfquizCheck` with its radius certificate. -/
elab "#quizdata_print_checks " i:num k:num : command => do
  let mut out := ""
  for (j, cf) in ← configRange i.getNat k.getNat do
    let some c := radiusCert cf.cfprog
      | throwError "configuration {j} fails the radius test"
    let n := threeDigits j
    out := out ++ s!"@[quizdata_cfquiz] theorem cfquiz_cf{n} : cfquiz cf{n} = qz{n} :=\n" ++
      s!"  cfquiz_eq_of_cfquizCheck (i := {c}) (by decide +kernel)\n"
  logInfo out

/-- `#quizdata_blocks cb qb n` defines `cb : List (List Config)`, the constants `cfNNN` of
`theConfigs` cut into blocks of `n` (the last one may be shorter), and `qb : List (List Quiz)`,
the constants `qzNNN` in the same blocks. -/
elab "#quizdata_blocks " cb:ident qb:ident n:num : command => do
  let ns ← getCurrNamespace
  let n := n.getNat
  let total := theConfigs.length
  let blocks := (List.range ((total + n - 1) / n)).map fun b =>
    List.range' (b * n + 1) (min n (total - b * n))
  for j in [1:total + 1] do
    unless (← getEnv).contains (configName j) && (← getEnv).contains (quizName j) do
      throwError "#quizdata_blocks: {configName j} or {quizName j} is missing"
  let cfg := mkConst ``Config
  let qz := mkConst ``Quiz
  liftCoreM <| addLiteralDef (ns ++ cb.getId) (listTypeExpr (listTypeExpr cfg))
    (listExpr (listTypeExpr cfg)
      (blocks.map fun b => listExpr cfg (b.map (mkConst ∘ configName))))
    s!"The configurations `cfNNN` of `theConfigs`, in blocks of {n} (computed by \
      `#quizdata_blocks`)."
  liftCoreM <| addLiteralDef (ns ++ qb.getId) (listTypeExpr (listTypeExpr qz))
    (listExpr (listTypeExpr qz)
      (blocks.map fun b => listExpr qz (b.map (mkConst ∘ quizName))))
    s!"The literal quizzes `qzNNN`, in blocks of {n} (computed by `#quizdata_blocks`)."

/-- `#quizdata_tree t` defines `t : QuizTree` as the literal value of
`cfquizTree theConfigs`. -/
elab "#quizdata_tree " id:ident : command => do
  let t := (← getCurrNamespace) ++ id.getId
  liftCoreM <| addLiteralDef t (mkConst ``QuizTree) (quizTreeExpr (cfquizTree theConfigs))
    "Coq `the_quiz_tree` (`Eval vm_compute in cfquiz_tree the_configs`): the fully evaluated \
      quiz tree of the 633 configurations, as a literal (computed by `#quizdata_tree`; see \
      `theQuizTree_eq`)."

/-- `#quizdata_drules r n source` (resp. `target`) defines `r : Drules` as the literal value of
`pickSourceDrules n theDrules` (resp. `pickTargetDrules n theDrules`). -/
elab "#quizdata_drules " id:ident n:num side:ident : command => do
  let r := (← getCurrNamespace) ++ id.getId
  let n := n.getNat
  let (rs, what) ← match side.getId with
    | `source => pure (pickSourceDrules n theDrules, "pickSourceDrules")
    | `target => pure (pickTargetDrules n theDrules, "pickTargetDrules")
    | _ => throwError "#quizdata_drules: expected `source` or `target`"
  liftCoreM <| addLiteralDef r (mkConst ``Drules) (listExpr (mkConst ``Part) (rs.map partExpr))
    s!"`{what} {n} theDrules`, as a literal (computed by `#quizdata_drules`)."

end FourColor.QuizData
