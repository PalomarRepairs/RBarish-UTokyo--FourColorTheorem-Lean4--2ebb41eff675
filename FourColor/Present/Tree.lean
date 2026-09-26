/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Present.Basic

/-!
# Presentations as data: case trees and their checker (port of `present.v`, second part)

Coq proves the seven presentation lemmas `exclude5` … `exclude11` (`presentN.v`) with scripts
in a small tactic language defined in `present.v` (`Presentation`, `Pcase`, `Reducible`,
`Hubcap`, `Similar`). Here a script is data: a case tree `PTree`, checked by the kernel-fast
boolean function `checkTree`, whose soundness theorem `checkTree_sound` replaces the tactics.

## The script semantics

A goal of a script is `Check p in p0` (`SucceedsIn p0 p`), in a context of labelled hypotheses
`L : successful ps` introduced by the named `Pcase` steps. The tree node for each step:

* `PTree.pcase i j k lo named t e` is `Pcase [L]: i[j+1] <= k` (`lo = true`) or `> k`
  (`lo = false`), i.e. Coq `succeed_by_split i j k lo`: the check `goodSplit i j k p`, then the
  first subgoal `Check pl in p0l` (the subtree `t`), then the second subgoal `Check pr in p0`
  (the subtree `e`), with the new hypothesis `L : successful p0l` in its context if `named`.
* `PTree.reducible m` is `Reducible` (Coq `succeed_by_reducibility`), checked by
  `redpartFast (qztPruneFast theQuizTree m) p`: `m` is the pruning mask of the check
  (`FourColor.Fast.Prune`, computed natively by `FourColor.PruneGen.redpartMask`).
* `PTree.hubcap hc m` is `Hubcap hc` (Coq `succeed_by_hubcap`), checked by
  `hubcapCoverFast n hc && hubcapFitFast n (redpartFast (qztPruneFast theQuizTree m)) rs rt p hc`
  for the hub size `n = sizePart p` and the rules `rs`, `rt` of the fork `rf : DruleFork n` given
  to the checker (`FourColor.PruneGen.hubcapMask` computes `m`).
* `PTree.similar lbl j mir` is `Similar to [*]L[j]` (Coq `succeed_by_similarity j mir L`),
  checked by `similarCheckFast ps p j mir`. The label `L` is the de Bruijn index `lbl` in the
  context: `0` is the most recent named hypothesis in scope. Labels are resolved lexically, as in
  the scripts: `L` is in scope in the second subtree of its `Pcase` (and everything nested in
  it), and a later `Pcase` with the same name shadows it.
* `PTree.ext k` is a subtree checked elsewhere (chunking): its goal must be the `k`-th goal of
  the list `gs` given to the checker, which is established by a separate theorem.

The context `ctx : List Part` of a goal lists the parts `ps` of the hypotheses in scope, the
most recent first. `PGoal` bundles a goal `(p0, p, ctx)`, and `PGoal.OK g` states it: assuming
`Reducibility` and the hypotheses of `ctx` (`CtxOK ctx`), `SucceedsIn g.p0 g.p`.

## Main definitions and results

* `checkTree rf gs t p0 p ctx`: the checker, in recursor style (a `PTree.rec`; the leaves use
  the fast checks of `FourColor.Fast`).
* `checkTree_sound`: if `ChunksOK gs` (every goal of `gs` holds), `Reducibility`, and
  `CtxOK ctx`, then `checkTree rf gs t p0 p ctx = true` proves `SucceedsIn p0 p`.
* `PGoal.ok_of_checkTree`: the form used by the chunk theorems: a successful check proves
  `PGoal.OK ⟨p0, p, ctx⟩`, given the theorems `ChunksOK gs` of the chunks its `ext` leaves
  refer to (built with `ChunksOK.cons` and `ChunksOK.nil` from those theorems).
* `excludedArity_of_ok` and `excludedArity_of_checkTree`: the composition lemmas: the goal
  `Check pcons_ n in pcons_ n` (the root chunk) proves `ExcludedArity n` (Coq `exclude_arity`,
  the tactic `Presentation`).
* `PGoal.ok_of_hubcap` and the unfolding lemmas `hubcapFitFast_cons1_of`,
  `hubcapFitFast_cons2_of`, `hubcapFitFast_nil`: a Hubcap leaf proved from separate checks of
  its constraints (for splitting a heavy leaf over several declarations). A constraint can be
  split further, rule by rule: `checkDbound2Fast_of_rec_lit` and `check2Dbound2Fast_of_rec_lit`
  (literal forms of `checkDbound2Fast_of_rec` and `check2Dbound2Fast_of_rec` of
  `FourColor.Fast.Hubcap`) enter its recursive check, and `checkDbound2RecFast_cons_of`,
  `check2Dbound2RecFast_cons_of` (and `check2Dbound2RecFast_succ_nil_cons`) peel off one target
  rule at a time, each with its own declaration for the work of that rule.

## Chunking

A presentation is checked as a set of chunk theorems, one declaration each, built bottom-up:

```
theorem chunk_c : PGoal.OK ⟨p0_c, p_c, ctx_c⟩ :=
  PGoal.ok_of_checkTree rf (.cons chunk_c1 (.cons chunk_c2 .nil)) tree_c (by decide +kernel)
```
where the goals are literal parts, `tree_c` has leaves `ext 0` and `ext 1` at the goals of the
chunks `chunk_c1` and `chunk_c2` (the list `gs` is read off the types of those theorems), and
the root chunk's goal is `⟨pcons_ n, pcons_ n, []⟩`, so that
`excludedArity_of_ok root : ExcludedArity n`.
The checker compares the goal at an `ext` leaf with the chunk's goal (`pgoalBeqFast`). A heavy
Hubcap leaf is an `ext` leaf whose chunk theorem is `PGoal.ok_of_hubcap`, applied to one
declaration per constraint (or per target rule of a constraint, see above); all the pieces of a
leaf use the leaf's mask.

## Measured costs (Lean v4.35.0-rc2, kernel time at build)

* The presentation data generated by `scripts/present_gen.py` (chunks of at most about 400 ms
  of estimated kernel time, heavy Hubcap leaves split per constraint and per target rule),
  kernel time at build: present5 0.08 s (1 chunk), present6 8.0 s (25 chunks), present7 ≈ 0.09 h
  (647 chunks), present8 ≈ 0.13 h (842), present9 ≈ 0.13 h (600), present10 124 s (154),
  present11 18 s (27); at most 1.9 s per declaration.
* A first test of present6 (318 Pcase, 21 Reducible, 236 Hubcap, 62 Similar): 12 chunks of 0.4
  to 1.3 s, 8.8 s in all.
* The heaviest Hubcap leaf of present6 (3 dual constraints): 1.5 s in one declaration; split into
  one declaration per target rule (`check2Dbound2Fast_of_rec_lit`,
  `check2Dbound2RecFast_cons_of`), 0.9 s in all, at most 0.19 s per declaration.
-/

namespace FourColor

universe u

/-- `bif% c a b` is `if c then a else b` for booleans, as one `Bool.rec`. -/
local macro "bif% " c:term:max a:term:max b:term:max : term =>
  `(Bool.rec (motive := fun _ => Bool) $b $a $c)

/-- `Bool.rec` with a `false` first branch is `&&`. -/
private theorem bool_rec_false_eq_and (a b : Bool) :
    Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

/-! ### Case trees and goals -/

/-- A presentation script as a case tree (see the module docstring). -/
inductive PTree : Type where
  /-- `Pcase [L]: i[j+1] <= k` (`lo = true`) or `Pcase [L]: i[j+1] > k` (`lo = false`); `named`
  if the label `L` is given. The subtree `t` proves the first subgoal, `e` the second. -/
  | pcase (i : SubpartLoc) (j k : ℕ) (lo named : Bool) (t e : PTree)
  /-- `Reducible`, with the pruning mask `m` of the check. -/
  | reducible (m : QztMask)
  /-- `Hubcap hc`, with the pruning mask `m` of the check. -/
  | hubcap (hc : Hubcap) (m : QztMask)
  /-- `Similar to L[j]` (`mir = false`) or `Similar to *L[j]` (`mir = true`), with `L` the de
  Bruijn index `lbl` in the context. -/
  | similar (lbl j : ℕ) (mir : Bool)
  /-- A subtree checked elsewhere: the goal here is the `k`-th chunk goal. -/
  | ext (k : ℕ)
  deriving Inhabited, Repr

/-- A goal `Check p in p0` of a presentation script, with the parts `ctx` of the hypotheses in
scope (the most recent first). -/
structure PGoal : Type where
  /-- The part `p0` of `Check p in p0`. -/
  p0 : Part
  /-- The part `p` of `Check p in p0`. -/
  p : Part
  /-- The parts of the labelled hypotheses `L : successful ps` in scope. -/
  ctx : List Part
  deriving Inhabited, Repr

/-- The hypotheses of the context `ctx` hold: all its parts are successful. -/
def CtxOK (ctx : List Part) : Prop := ∀ ps ∈ ctx, Successful.{u} ps

/-- The empty context holds. -/
theorem CtxOK.nil : CtxOK.{u} [] := fun _ h => absurd h List.not_mem_nil

/-- Adding a successful part to a context. -/
theorem CtxOK.cons {ps : Part} {ctx : List Part} (hps : Successful.{u} ps) (hctx : CtxOK.{u} ctx) :
    CtxOK.{u} (ps :: ctx) := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact hps
  · exact hctx q hq

/-- The hypothesis of a label: the part at index `i` of a context is successful (`.nil` out of
range, which is successful too). -/
theorem CtxOK.getD {ctx : List Part} (hctx : CtxOK.{u} ctx) (i : ℕ) :
    Successful.{u} (ctx.getD i .nil) := by
  rcases Nat.lt_or_ge i ctx.length with hi | hi
  · rw [List.getD_eq_getElem _ _ hi]
    exact hctx _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ hi]
    exact successful_nil

/-- A goal holds: assuming reducibility and the hypotheses of its context, `Check g.p in g.p0`. -/
def PGoal.OK (g : PGoal) : Prop := Reducibility → CtxOK.{u} g.ctx → SucceedsIn.{u} g.p0 g.p

/-- The default goal (`Check nil in nil`, in the empty context) holds. -/
theorem PGoal.ok_default : PGoal.OK.{u} ⟨.nil, .nil, []⟩ :=
  fun _ _ _ => successful_nil

/-- The chunk goals `gs` all hold (they are given by separate theorems). -/
def ChunksOK (gs : List PGoal) : Prop := ∀ g ∈ gs, PGoal.OK.{u} g

/-- No chunk goals. -/
theorem ChunksOK.nil : ChunksOK.{u} [] := fun _ h => absurd h List.not_mem_nil

/-- Adding a chunk goal proved by `hg`. -/
theorem ChunksOK.cons {g : PGoal} {gs : List PGoal} (hg : PGoal.OK.{u} g) (hgs : ChunksOK.{u} gs) :
    ChunksOK.{u} (g :: gs) := by
  intro g' hg'
  rcases List.mem_cons.1 hg' with rfl | hg'
  · exact hg
  · exact hgs g' hg'

/-- The `k`-th chunk goal holds (the default goal out of range). -/
theorem ChunksOK.getD {gs : List PGoal} (hgs : ChunksOK.{u} gs) (k : ℕ) :
    PGoal.OK.{u} (gs.getD k ⟨.nil, .nil, []⟩) := by
  rcases Nat.lt_or_ge k gs.length with hk | hk
  · rw [List.getD_eq_getElem _ _ hk]
    exact hgs _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ hk]
    exact PGoal.ok_default

/-! ### Kernel-fast lookups and comparisons -/

/-- Kernel-fast `ctx.getD n .nil`: the part of the label with de Bruijn index `n`. -/
noncomputable def nthPartFast (ctx : List Part) (n : ℕ) : Part :=
  List.rec (motive := fun _ => ℕ → Part) (fun _ => Part.nil)
    (fun x _ ih n => Nat.rec (motive := fun _ => Part) x (fun n' _ => ih n') n) ctx n

/-- `nthPartFast` is `List.getD`. -/
theorem nthPartFast_eq (ctx : List Part) (n : ℕ) : nthPartFast ctx n = ctx.getD n .nil := by
  induction ctx generalizing n with
  | nil => simp [nthPartFast]
  | cons x ctx ih =>
    cases n with
    | zero => rfl
    | succ n => rw [List.getD_cons_succ, ← ih]; rfl

/-- Kernel-fast `gs.getD n ⟨.nil, .nil, []⟩`: the `n`-th chunk goal. -/
noncomputable def nthGoalFast (gs : List PGoal) (n : ℕ) : PGoal :=
  List.rec (motive := fun _ => ℕ → PGoal) (fun _ => ⟨Part.nil, Part.nil, []⟩)
    (fun g _ ih n => Nat.rec (motive := fun _ => PGoal) g (fun n' _ => ih n') n) gs n

/-- `nthGoalFast` is `List.getD`. -/
theorem nthGoalFast_eq (gs : List PGoal) (n : ℕ) :
    nthGoalFast gs n = gs.getD n ⟨.nil, .nil, []⟩ := by
  induction gs generalizing n with
  | nil => simp [nthGoalFast]
  | cons g gs ih =>
    cases n with
    | zero => rfl
    | succ n => rw [List.getD_cons_succ, ← ih]; rfl

/-- A code for arity ranges (the index of the constructor). -/
noncomputable def prangeCodeFast (r : Prange) : ℕ :=
  Prange.rec (motive := fun _ => ℕ) (nat_lit 0) (nat_lit 1) (nat_lit 2) (nat_lit 3) (nat_lit 4)
    (nat_lit 5) (nat_lit 6) (nat_lit 7) (nat_lit 8) (nat_lit 9) (nat_lit 10) (nat_lit 11)
    (nat_lit 12) (nat_lit 13) (nat_lit 14) r

/-- The inverse of `prangeCodeFast`. -/
private def prangeOfCode : ℕ → Prange
  | 0 => .pr55 | 1 => .pr66 | 2 => .pr77 | 3 => .pr88 | 4 => .pr99 | 5 => .pr56 | 6 => .pr67
  | 7 => .pr78 | 8 => .pr89 | 9 => .pr57 | 10 => .pr68 | 11 => .pr79 | 12 => .pr58
  | 13 => .pr69 | _ => .pr59

private theorem prangeOfCode_code (r : Prange) : prangeOfCode (prangeCodeFast r) = r := by
  cases r <;> rfl

/-- Kernel-fast equality test of arity ranges. -/
noncomputable def prangeBeqFast (r r' : Prange) : Bool :=
  Nat.beq (prangeCodeFast r) (prangeCodeFast r')

/-- `prangeBeqFast` decides equality. -/
theorem prangeBeqFast_iff (r r' : Prange) : prangeBeqFast r r' = true ↔ r = r' := by
  constructor
  · intro h
    rw [← prangeOfCode_code r, Nat.eq_of_beq_eq_true h, prangeOfCode_code]
  · rintro rfl
    exact Nat.beq_refl _

/-- Kernel-fast equality test of parts. -/
noncomputable def partBeqFast (p q : Part) : Bool :=
  Part.rec (motive := fun _ => Part → Bool)
    (fun q => Part.rec (motive := fun _ => Bool) true (fun _ _ _ _ => false)
      (fun _ _ _ _ => false) (fun _ _ _ _ _ => false) (fun _ _ _ _ _ _ => false) q)
    (fun s h _ ih q => Part.rec (motive := fun _ => Bool) false
      (fun s' h' q' _ => bif% (prangeBeqFast s s') (bif% (prangeBeqFast h h') (ih q') false) false)
      (fun _ _ _ _ => false) (fun _ _ _ _ _ => false) (fun _ _ _ _ _ _ => false) q)
    (fun h f1 _ ih q => Part.rec (motive := fun _ => Bool) false (fun _ _ _ _ => false)
      (fun h' f1' q' _ =>
        bif% (prangeBeqFast h h') (bif% (prangeBeqFast f1 f1') (ih q') false) false)
      (fun _ _ _ _ _ => false) (fun _ _ _ _ _ _ => false) q)
    (fun h f1 f2 _ ih q => Part.rec (motive := fun _ => Bool) false (fun _ _ _ _ => false)
      (fun _ _ _ _ => false)
      (fun h' f1' f2' q' _ => bif% (prangeBeqFast h h')
        (bif% (prangeBeqFast f1 f1') (bif% (prangeBeqFast f2 f2') (ih q') false) false) false)
      (fun _ _ _ _ _ _ => false) q)
    (fun h f1 f2 f3 _ ih q => Part.rec (motive := fun _ => Bool) false (fun _ _ _ _ => false)
      (fun _ _ _ _ => false) (fun _ _ _ _ _ => false)
      (fun h' f1' f2' f3' q' _ => bif% (prangeBeqFast h h')
        (bif% (prangeBeqFast f1 f1') (bif% (prangeBeqFast f2 f2')
          (bif% (prangeBeqFast f3 f3') (ih q') false) false) false) false) q)
    p q

/-- `partBeqFast` decides equality. -/
theorem partBeqFast_iff (p q : Part) : partBeqFast p q = true ↔ p = q := by
  induction p generalizing q with
  | nil => cases q <;> simp [partBeqFast]
  | cons s h p ih =>
    cases q <;> simp only [partBeqFast, reduceCtorEq, Bool.false_eq_true]
    rename_i s' h' q
    rw [bool_rec_false_eq_and, bool_rec_false_eq_and, Bool.and_eq_true, Bool.and_eq_true,
      prangeBeqFast_iff, prangeBeqFast_iff, show Part.rec _ _ _ _ _ p q = partBeqFast p q from rfl,
      ih, Part.cons.injEq]
  | cons6 h f1 p ih =>
    cases q <;> simp only [partBeqFast, reduceCtorEq, Bool.false_eq_true]
    rename_i h' f1' q
    rw [bool_rec_false_eq_and, bool_rec_false_eq_and, Bool.and_eq_true, Bool.and_eq_true,
      prangeBeqFast_iff, prangeBeqFast_iff, show Part.rec _ _ _ _ _ p q = partBeqFast p q from rfl,
      ih, Part.cons6.injEq]
  | cons7 h f1 f2 p ih =>
    cases q <;> simp only [partBeqFast, reduceCtorEq, Bool.false_eq_true]
    rename_i h' f1' f2' q
    rw [bool_rec_false_eq_and, bool_rec_false_eq_and, bool_rec_false_eq_and, Bool.and_eq_true,
      Bool.and_eq_true, Bool.and_eq_true, prangeBeqFast_iff, prangeBeqFast_iff,
      prangeBeqFast_iff, show Part.rec _ _ _ _ _ p q = partBeqFast p q from rfl, ih,
      Part.cons7.injEq]
  | cons8 h f1 f2 f3 p ih =>
    cases q <;> simp only [partBeqFast, reduceCtorEq, Bool.false_eq_true]
    rename_i h' f1' f2' f3' q
    rw [bool_rec_false_eq_and, bool_rec_false_eq_and, bool_rec_false_eq_and,
      bool_rec_false_eq_and, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true, prangeBeqFast_iff, prangeBeqFast_iff, prangeBeqFast_iff,
      prangeBeqFast_iff, show Part.rec _ _ _ _ _ p q = partBeqFast p q from rfl, ih,
      Part.cons8.injEq]

/-- Kernel-fast equality test of lists of parts. -/
noncomputable def partsBeqFast (l l' : List Part) : Bool :=
  List.rec (motive := fun _ => List Part → Bool)
    (fun l' => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l')
    (fun x _ ih l' => List.rec (motive := fun _ => Bool) false
      (fun y l'' _ => bif% (partBeqFast x y) (ih l'') false) l')
    l l'

/-- `partsBeqFast` decides equality. -/
theorem partsBeqFast_iff (l l' : List Part) : partsBeqFast l l' = true ↔ l = l' := by
  induction l generalizing l' with
  | nil => cases l' <;> simp [partsBeqFast]
  | cons x l ih =>
    cases l' with
    | nil => simp [partsBeqFast]
    | cons y l' =>
      rw [List.cons.injEq, ← partBeqFast_iff, ← ih, ← Bool.and_eq_true,
        ← bool_rec_false_eq_and]
      rfl

/-- Kernel-fast test that the goal `g` is `⟨p0, p, ctx⟩`. -/
noncomputable def pgoalBeqFast (g : PGoal) (p0 p : Part) (ctx : List Part) : Bool :=
  PGoal.rec (motive := fun _ => Bool) (fun gp0 gp gctx =>
    bif% (partBeqFast gp0 p0) (bif% (partBeqFast gp p) (partsBeqFast gctx ctx) false) false) g

/-- `pgoalBeqFast` decides equality. -/
theorem pgoalBeqFast_iff (g : PGoal) (p0 p : Part) (ctx : List Part) :
    pgoalBeqFast g p0 p ctx = true ↔ g = ⟨p0, p, ctx⟩ := by
  obtain ⟨gp0, gp, gctx⟩ := g
  show Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false (partsBeqFast gctx ctx) (partBeqFast gp p))
    (partBeqFast gp0 p0) = true ↔ _
  rw [bool_rec_false_eq_and, bool_rec_false_eq_and, Bool.and_eq_true, Bool.and_eq_true,
    partBeqFast_iff, partBeqFast_iff, partsBeqFast_iff, PGoal.mk.injEq]

/-! ### The checker -/

/-- The presentation checker: `checkTree rf gs t p0 p ctx` checks the script `t` on the goal
`Check p in p0` with the hypotheses `ctx` in scope, for the drule fork `rf` of the hub size `n`
and the chunk goals `gs` (see the module docstring). Recursor style: a `PTree.rec`, with
`Bool.rec` for the tests and the fast checks of `FourColor.Fast` at the leaves. -/
noncomputable def checkTree {n : ℕ} (rf : DruleFork n) (gs : List PGoal) (t : PTree) :
    Part → Part → List Part → Bool :=
  PTree.rec (motive := fun _ => Part → Part → List Part → Bool)
    -- `Pcase`: `p0l` is the part `p0` refined by the assumption, or `pl` if that is not a good
    -- split of `p0`
    (fun i j k lo named _ _ iht ihe p0 p ctx =>
      bif% (goodSplitFast i j k p)
        ((fun p0l =>
          bif% (iht p0l (splitPartFast i j k lo p) ctx)
            (ihe p0 (splitPartFast i j k (Bool.rec (motive := fun _ => Bool) true false lo) p)
              (Bool.rec (motive := fun _ => List Part) ctx (p0l :: ctx) named))
            false)
          (Bool.rec (motive := fun _ => Part) (splitPartFast i j k lo p)
            (splitPartFast i j k lo p0) (goodSplitFast i j k p0)))
        false)
    -- `Reducible`
    (fun m _ p _ => redpartFast (qztPruneFast theQuizTree m) p)
    -- `Hubcap hc`
    (fun hc m _ p _ =>
      bif% (Nat.beq (sizePartFast p) n)
        (bif% (hubcapCoverFast n hc)
          (hubcapFitFast n (redpartFast (qztPruneFast theQuizTree m)) rf.sourceDrules
            rf.targetDrules p hc)
          false)
        false)
    -- `Similar to [*]L[j]`
    (fun lbl j mir _ p ctx => similarCheckFast (nthPartFast ctx lbl) p j mir)
    -- a chunk checked elsewhere
    (fun k p0 p ctx => pgoalBeqFast (nthGoalFast gs k) p0 p ctx)
    t

section Equations

variable {n : ℕ} (rf : DruleFork n) (gs : List PGoal)

/-- `checkTree` at a `Pcase` node. -/
theorem checkTree_pcase (i : SubpartLoc) (j k : ℕ) (lo named : Bool) (t e : PTree)
    (p0 p : Part) (ctx : List Part) :
    checkTree rf gs (.pcase i j k lo named t e) p0 p ctx =
      (goodSplitFast i j k p &&
        (checkTree rf gs t
            (if goodSplitFast i j k p0 then splitPartFast i j k lo p0 else splitPartFast i j k lo p)
            (splitPartFast i j k lo p) ctx &&
          checkTree rf gs e p0 (splitPartFast i j k (!lo) p)
            (if named then
              (if goodSplitFast i j k p0 then splitPartFast i j k lo p0
                else splitPartFast i j k lo p) :: ctx
            else ctx))) := by
  show Bool.rec (motive := fun _ => Bool) false _ (goodSplitFast i j k p) = _
  rw [bool_rec_false_eq_and]
  congr 1
  generalize goodSplitFast i j k p0 = g0
  cases g0 <;> cases named <;> cases lo <;> exact bool_rec_false_eq_and _ _

/-- `checkTree` at a `Reducible` leaf. -/
theorem checkTree_reducible (m : QztMask) (p0 p : Part) (ctx : List Part) :
    checkTree rf gs (.reducible m) p0 p ctx = redpartFast (qztPruneFast theQuizTree m) p := rfl

/-- `checkTree` at a `Hubcap` leaf. -/
theorem checkTree_hubcap (hc : Hubcap) (m : QztMask) (p0 p : Part) (ctx : List Part) :
    checkTree rf gs (.hubcap hc m) p0 p ctx =
      (Nat.beq (sizePartFast p) n && (hubcapCoverFast n hc &&
        hubcapFitFast n (redpartFast (qztPruneFast theQuizTree m)) rf.sourceDrules
          rf.targetDrules p hc)) := by
  show Bool.rec (motive := fun _ => Bool) false
    (Bool.rec (motive := fun _ => Bool) false _ (hubcapCoverFast n hc))
    (Nat.beq (sizePartFast p) n) = _
  rw [bool_rec_false_eq_and, bool_rec_false_eq_and]

/-- `checkTree` at a `Similar` leaf. -/
theorem checkTree_similar (lbl j : ℕ) (mir : Bool) (p0 p : Part) (ctx : List Part) :
    checkTree rf gs (.similar lbl j mir) p0 p ctx =
      similarCheckFast (nthPartFast ctx lbl) p j mir :=
  rfl

/-- `checkTree` at an `ext` leaf. -/
theorem checkTree_ext (k : ℕ) (p0 p : Part) (ctx : List Part) :
    checkTree rf gs (.ext k) p0 p ctx = pgoalBeqFast (nthGoalFast gs k) p0 p ctx := rfl

end Equations

/-! ### Soundness -/

/-- **Soundness of the checker** (Coq: the tactics of `present.v`, i.e. the lemmas
`succeed_by_split`, `succeed_by_reducibility`, `succeed_by_hubcap` and
`succeed_by_similarity`): if the chunk goals `gs` hold, then assuming reducibility and the
hypotheses of the context `ctx`, a successful check of `t` proves `Check p in p0`. -/
theorem checkTree_sound {n : ℕ} (rf : DruleFork n) {gs : List PGoal} (hgs : ChunksOK.{u} gs)
    (red : Reducibility) (t : PTree) :
    ∀ (p0 p : Part) (ctx : List Part), CtxOK.{u} ctx → checkTree rf gs t p0 p ctx = true →
      SucceedsIn.{u} p0 p := by
  induction t with
  | pcase i j k lo named t e iht ihe =>
    intro p0 p ctx hctx h
    rw [checkTree_pcase, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨hg, ht, he⟩ := h
    simp only [goodSplitFast_eq, splitPartFast_eq] at hg ht he
    refine succeed_by_split i j k lo hg (iht _ _ ctx hctx ht) (fun L => ihe _ _ _ ?_ he)
    cases named
    · exact hctx
    · exact hctx.cons L
  | reducible m =>
    intro p0 p ctx _ h
    exact succeed_by_reducibility_fast red m h
  | hubcap hc m =>
    intro p0 p ctx _ h
    rw [checkTree_hubcap, Bool.and_eq_true] at h
    obtain ⟨hn, h⟩ := h
    rw [sizePartFast_eq] at hn
    exact succeed_by_hubcap_fast rf m hc red (Nat.eq_of_beq_eq_true hn) h
  | similar lbl j mir =>
    intro p0 p ctx hctx h
    rw [checkTree_similar, similarCheckFast_eq, similarCheck_iff, nthPartFast_eq] at h
    exact succeed_by_similarity j mir (hctx.getD lbl) h
  | ext k =>
    intro p0 p ctx hctx h
    rw [checkTree_ext, pgoalBeqFast_iff, nthGoalFast_eq] at h
    have hk := hgs.getD k
    rw [h] at hk
    exact hk red hctx

/-! ### Composition -/

/-- A chunk theorem: a successful check of the tree `t` on the goal `⟨p0, p, ctx⟩`, whose `ext`
leaves refer to the chunk goals `gs` (proved by `hgs`), proves the goal. -/
theorem PGoal.ok_of_checkTree {n : ℕ} (rf : DruleFork n) {gs : List PGoal} (hgs : ChunksOK.{u} gs)
    (t : PTree) {p0 p : Part} {ctx : List Part} (h : checkTree rf gs t p0 p ctx = true) :
    PGoal.OK.{u} ⟨p0, p, ctx⟩ :=
  fun red hctx => checkTree_sound rf hgs red t p0 p ctx hctx h

/-- **Composition** (Coq `exclude_arity`, the tactic `Presentation`): the root goal
`Check pcons_ n in pcons_ n`, in the empty context, proves `ExcludedArity n`. -/
theorem excludedArity_of_ok {n : ℕ} (h : PGoal.OK.{u} ⟨pcons_ n, pcons_ n, []⟩) :
    ExcludedArity.{u} n :=
  exclude_arity n fun red => h red CtxOK.nil

/-- **Composition**: a presentation for hub size `n` whose `ext` leaves refer to the chunk
goals `gs`, proved by separate theorems (`hgs`), and whose check succeeds on the root goal,
proves `ExcludedArity n`. -/
theorem excludedArity_of_checkTree {n : ℕ} (rf : DruleFork n) {gs : List PGoal}
    (hgs : ChunksOK.{u} gs) (t : PTree)
    (h : checkTree rf gs t (pcons_Fast n) (pcons_Fast n) [] = true) : ExcludedArity.{u} n := by
  rw [pcons_Fast_eq] at h
  exact excludedArity_of_ok (PGoal.ok_of_checkTree rf hgs t h)

/-! ### Hubcap leaves checked by parts -/

/-- A `Hubcap hc` leaf proved from separate checks: the hub size, the cover, and the fit (which
can itself be assembled from checks of the constraints with `hubcapFitFast_cons1_of` and
`hubcapFitFast_cons2_of`). -/
theorem PGoal.ok_of_hubcap {n : ℕ} (rf : DruleFork n) (m : QztMask) (hc : Hubcap)
    {p0 p : Part} {ctx : List Part} (hn : Nat.beq (sizePartFast p) n = true)
    (hcov : hubcapCoverFast n hc = true)
    (hfit : hubcapFitFast n (redpartFast (qztPruneFast theQuizTree m)) rf.sourceDrules
      rf.targetDrules p hc = true) :
    PGoal.OK.{u} ⟨p0, p, ctx⟩ := by
  intro red _
  rw [sizePartFast_eq] at hn
  exact succeed_by_hubcap_fast rf m hc red (Nat.eq_of_beq_eq_true hn) (by rw [hcov, hfit]; rfl)

/-- `hubcapFitFast` on a hubcap `cons1 j b hc`: the single constraint and the rest. -/
theorem hubcapFitFast_cons1_of {nhub : ℕ} {redp : Part → Bool} {rs rt : Drules} {p : Part}
    {j : ℕ} {b : ℤ} {hc : Hubcap}
    (h1 : checkDbound2Fast redp rs rt (hubcapRotFast nhub j p) b = true)
    (h2 : hubcapFitFast nhub redp rs rt p hc = true) :
    hubcapFitFast nhub redp rs rt p (.cons1 j b hc) = true := by
  show Bool.rec (motive := fun _ => Bool) false (hubcapFitFast nhub redp rs rt p hc)
    (checkDbound2Fast redp rs rt (hubcapRotFast nhub j p) b) = true
  rw [h1, h2]

/-- `hubcapFitFast` on a hubcap `cons2 j1 j2 b hc`: the dual constraint and the rest. -/
theorem hubcapFitFast_cons2_of {nhub : ℕ} {redp : Part → Bool} {rs rt : Drules} {p : Part}
    {j1 j2 : ℕ} {b : ℤ} {hc : Hubcap}
    (h1 : check2Dbound2Fast nhub redp rs rt (hubcapRotFast nhub j1 p) (hubSubnFast nhub j2 j1) b
      = true)
    (h2 : hubcapFitFast nhub redp rs rt p hc = true) :
    hubcapFitFast nhub redp rs rt p (.cons2 j1 j2 b hc) = true := by
  show Bool.rec (motive := fun _ => Bool) false (hubcapFitFast nhub redp rs rt p hc)
    (check2Dbound2Fast nhub redp rs rt (hubcapRotFast nhub j1 p) (hubSubnFast nhub j2 j1) b) =
      true
  rw [h1, h2]

/-- `hubcapFitFast` on the empty hubcap. -/
theorem hubcapFitFast_nil {nhub : ℕ} {redp : Part → Bool} {rs rt : Drules} {p : Part} :
    hubcapFitFast nhub redp rs rt p .nil = true := rfl

/-- Entry into the recursive check of a single-target constraint, with literal data: the
rotated part `P`, the sorted rule lists, the bound `nt` and the fuel `M` are given as values
(each side condition is a closed equation, for `decide +kernel`, once `h` fixes the values), so
that the recursive check `h` can be stated (and split with `checkDbound2RecFast_cons_of`) on
literals. -/
theorem checkDbound2Fast_of_rec_lit (redp : Part → Bool) (rs rt : Drules) (p : Part) (b : ℤ)
    {P : Part} {M nt : ℕ} {rt' rs' : Drules} (hp : p = P)
    (ht : (sortDrulesFast P rt).straddlingDrules = rt')
    (hs : (sortDrulesFast P rs).straddlingDrules = rs')
    (hnt : Int.add (Int.sub (Int.ofNat (sortDrulesFast P rs).nbForcedDrules)
      (Int.ofNat (sortDrulesFast P rt).nbForcedDrules)) b = Int.ofNat nt)
    (hM : Nat.succ (Nat.succ (lengthFast rt')) = M)
    (h : checkDbound2RecFast redp M P rt' rs' [] nt = true) :
    checkDbound2Fast redp rs rt p b = true := by
  subst hp hM
  exact checkDbound2Fast_of_rec redp rs rt p b rfl ht rfl hs hnt h

/-- Entry into the recursive check of a dual constraint, with literal data: the parts `P1`
(`p1`) and `P2` (its rotation by `I = i`), the sorted rule lists, the bound `nt` and the fuel `M`
are given as values (each side condition is a closed equation, for `decide +kernel`, once `h`
fixes the values), so that the recursive check `h` can be stated (and split with
`check2Dbound2RecFast_cons_of`) on literals. -/
theorem check2Dbound2Fast_of_rec_lit (nhub : ℕ) (redp : Part → Bool) (rs rt : Drules)
    (p1 : Part) (i : ℕ) (b : ℤ) {P1 P2 : Part} {I M nt : ℕ} {rt1 rs1 rt2 rs2 : Drules}
    (hp1 : p1 = P1) (hi : i = I) (hp2 : rotPartFast I P1 = P2)
    (ht1 : (sortDrulesFast P1 rt).straddlingDrules = rt1)
    (hs1 : (sortDrulesFast P1 rs).straddlingDrules = rs1)
    (ht2 : (sortDrulesFast P2 rt).straddlingDrules = rt2)
    (hs2 : (sortDrulesFast P2 rs).straddlingDrules = rs2)
    (hnt : Int.add (Int.sub
      (Int.ofNat (Nat.add (sortDrulesFast P1 rs).nbForcedDrules
        (sortDrulesFast P2 rs).nbForcedDrules))
      (Int.ofNat (Nat.add (sortDrulesFast P1 rt).nbForcedDrules
        (sortDrulesFast P2 rt).nbForcedDrules))) b = Int.ofNat nt)
    (hM : Nat.add (lengthFast rt1) (Nat.add (lengthFast rt2) (nat_lit 3)) = M)
    (h : check2Dbound2RecFast nhub redp M P1 P2 rt1 rs1 [] rt2 rs2 [] I nt = true) :
    check2Dbound2Fast nhub redp rs rt p1 i b = true := by
  subst hp1 hi hp2 hM
  exact check2Dbound2Fast_of_rec nhub redp rs rt p1 i b rfl ht1 rfl hs1 rfl ht2 rfl hs2 hnt h

/-- One step of a single-target bound check (`checkDbound2RecFast`, entered from
`checkDbound2Fast` by `checkDbound2Fast_of_rec`) from separate checks of the work for its first
target rule `r` and of the rest (for splitting a heavy constraint over several declarations). -/
theorem checkDbound2RecFast_cons_of {redp : Part → Bool} {m : ℕ} {p r : Part}
    {rt' rs ru : Drules} {nt : ℕ}
    (hhead : checkDbound2HeadFast redp (checkDbound2RecFast redp m) p r rt' rs ru nt = true)
    (hrest : checkDbound2RecFast redp m p rt' rs (r :: ru) nt = true) :
    checkDbound2RecFast redp (m + 1) p (r :: rt') rs ru nt = true := by
  rw [checkDbound2RecFast_succ_cons, hhead, hrest, Bool.and_self, Bool.or_true]

/-- One step of a dual-target bound check (`check2Dbound2RecFast`, entered from
`check2Dbound2Fast` by `check2Dbound2Fast_of_rec`) from separate checks of the work for the first
target rule `r` of the first part and of the rest (for splitting a heavy dual constraint over
several declarations; when the first part has no target rule left, the roles of the parts are
swapped by `check2Dbound2RecFast_succ_nil_cons`). -/
theorem check2Dbound2RecFast_cons_of {nhub : ℕ} {redp : Part → Bool} {m : ℕ} {p1 p2 r : Part}
    {rt1' rs1 ru1 rt2 rs2 ru2 : Drules} {i nt : ℕ}
    (hhead : check2Dbound2HeadFast redp (check2Dbound2RecFast nhub redp m) p1 r rt1' rs1 ru1 rt2
      rs2 ru2 i nt = true)
    (hrest : check2Dbound2RecFast nhub redp m p1 p2 rt1' rs1 (r :: ru1) rt2 rs2 ru2 i nt = true) :
    check2Dbound2RecFast nhub redp (m + 1) p1 p2 (r :: rt1') rs1 ru1 rt2 rs2 ru2 i nt = true := by
  rw [check2Dbound2RecFast_succ_cons, hhead, hrest, Bool.and_self, Bool.or_true]

end FourColor
