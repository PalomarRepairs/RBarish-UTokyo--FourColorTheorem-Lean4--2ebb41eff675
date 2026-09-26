/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Present.Tree
import FourColor.Fast.PruneGen

/-!
# Native helper of `scripts/present_gen.py` (not part of the library)

Run by the generator as

    lake env lean --run scripts/present_gen_native.lean TREE OUT EXPAND SUBEXPAND [time]

It reads the case tree of one presentation (`TREE`, the text format written by
`present_gen.py`), walks it with the faithful (computable) functions of the library, and writes
`OUT`, one JSON object per line:

* `{"t":"rules", ...}`: the rules of the drule fork of the hub size (its source and target rules,
  without repetition), as Lean terms; rule lists below are lists of indices into this table.
* `{"t":"node", ...}` for each node of the tree, in preorder: its kind (`P`, `R`, `H`, `S`), the
  result of its check (`ok`), its cost (`hb`, and `cmp` for a Hubcap leaf), the goal parts `p0`
  and `p` (Lean terms), and for the Reducible and Hubcap leaves the pruning mask
  (`FourColor.PruneGen.redpartMask`, `FourColor.PruneGen.hubcapMask`), as a Lean term. For a
  Hubcap leaf, `cons` lists the costs `[hb, cmp]` of its constraints.
* `{"t":"cons", ...}` for each Hubcap constraint of cost `3 hb + cmp` above `EXPAND` (a heartbeat
  costs about three comparison steps in the kernel): the literal data of its
  recursive check (`check2Dbound2RecFast` / `checkDbound2RecFast`, entered with
  `check2Dbound2Fast_of_rec_lit` / `checkDbound2Fast_of_rec_lit`) and its chain of steps: the work
  for one target rule at a time (a "head", `check2Dbound2HeadFast` / `checkDbound2HeadFast`, with
  its cost), the swaps of the two parts of a dual check, and the end of the chain. A head of cost
  above `SUBEXPAND` is expanded the same way: the literal data of its recursive call and its
  chain (the generator does not use these yet: it passes a threshold that expands nothing).
* With the optional argument `time`, the node rows also give the native time `ns` of the leaf
  checks (for calibrating the cost model only; times are not deterministic).

## Costs

The cost of a check has two deterministic parts: `hb`, the number of heartbeats (small
allocations of the Lean runtime) of its evaluation by the interpreter, with the faithful
functions and the quiz tree pruned by the check's mask (measured on a second evaluation, so that
one-time initializations are not counted), and `cmp`, the number of `cmpPart` calls of the
hubcap checks (which allocate nothing), counted by copies of the recursive checks.
`present_gen.py` converts `hb + cmp` to kernel time with a calibrated factor. Everything here is
deterministic, so the generator's output is too.

This file is a tool: it is not imported by the library, and nothing in the proof depends on it
(a wrong mask or a wrong literal only makes a kernel check fail).
-/

open FourColor

namespace PresentGen

/-! ### The case tree -/

/-- A presentation script as a case tree (as `FourColor.PTree`, without the masks). -/
inductive RTree where
  | pcase (i : SubpartLoc) (j k : Nat) (lo named : Bool) (t e : RTree)
  | red
  | hubcap (hc : Hubcap)
  | similar (lbl j : Nat) (mir : Bool)
  deriving Inhabited

def locOf : String → Option SubpartLoc
  | "s" => some .spoke | "h" => some .hat | "f1" => some .fan1 | "f2" => some .fan2
  | "f3" => some .fan3 | _ => none

def tokNat (ts : Array String) (i : Nat) : Except String Nat :=
  match (ts.getD i "").toNat? with
  | some n => .ok n
  | none => .error s!"expected a number at token {i}: {ts.getD i ""}"

def tokInt (ts : Array String) (i : Nat) : Except String Int :=
  match (ts.getD i "").toInt? with
  | some n => .ok n
  | none => .error s!"expected an integer at token {i}: {ts.getD i ""}"

partial def parseHubcap (ts : Array String) (i m : Nat) : Except String (Hubcap × Nat) := do
  if m == 0 then return (.nil, i)
  match ts.getD i "" with
  | "1" =>
    let j ← tokNat ts (i+1); let b ← tokInt ts (i+2)
    let (hc, i') ← parseHubcap ts (i+3) (m-1)
    return (.cons1 j b hc, i')
  | "2" =>
    let j1 ← tokNat ts (i+1); let j2 ← tokNat ts (i+2); let b ← tokInt ts (i+3)
    let (hc, i') ← parseHubcap ts (i+4) (m-1)
    return (.cons2 j1 j2 b hc, i')
  | t => throw s!"bad hubcap token {t}"

partial def parseTree (ts : Array String) (i : Nat) : Except String (RTree × Nat) := do
  match ts.getD i "" with
  | "P" =>
    let some loc := locOf (ts.getD (i+1) "") | throw "bad loc"
    let j ← tokNat ts (i+2); let k ← tokNat ts (i+3)
    let lo ← tokNat ts (i+4); let named ← tokNat ts (i+5)
    let (t, i1) ← parseTree ts (i+6)
    let (e, i2) ← parseTree ts i1
    return (.pcase loc j k (lo == 1) (named == 1) t e, i2)
  | "R" => return (.red, i+1)
  | "H" =>
    let m ← tokNat ts (i+1)
    let (hc, i') ← parseHubcap ts (i+2) m
    return (.hubcap hc, i')
  | "S" =>
    let l ← tokNat ts (i+1); let j ← tokNat ts (i+2); let mir ← tokNat ts (i+3)
    return (.similar l j (mir == 1), i+4)
  | t => throw s!"bad tree token {t} at {i}"

def loadTree (path : String) : IO (Nat × RTree) := do
  let s ← IO.FS.readFile path
  let ts := (s.splitOn "\n" |>.flatMap (fun l => l.splitOn " ")).filter (· ≠ "") |>.toArray
  let n := (ts.getD 0 "0").toNat!
  match parseTree ts 1 with
  | .ok (t, i) =>
    if i != ts.size then throw (IO.userError s!"{path}: trailing tokens")
    return (n, t)
  | .error e => throw (IO.userError s!"{path}: {e}")

/-! ### Lean source of the data -/

def prSrc : Prange → String
  | .pr55 => ".pr55" | .pr66 => ".pr66" | .pr77 => ".pr77" | .pr88 => ".pr88" | .pr99 => ".pr99"
  | .pr56 => ".pr56" | .pr67 => ".pr67" | .pr78 => ".pr78" | .pr89 => ".pr89" | .pr57 => ".pr57"
  | .pr68 => ".pr68" | .pr79 => ".pr79" | .pr58 => ".pr58" | .pr69 => ".pr69" | .pr59 => ".pr59"

def partSrc : Part → String
  | .nil => ".nil"
  | .cons s h p => s!"(.cons {prSrc s} {prSrc h} {partSrc p})"
  | .cons6 h f p => s!"(.cons6 {prSrc h} {prSrc f} {partSrc p})"
  | .cons7 h f f' p => s!"(.cons7 {prSrc h} {prSrc f} {prSrc f'} {partSrc p})"
  | .cons8 h f f' f'' p => s!"(.cons8 {prSrc h} {prSrc f} {prSrc f'} {prSrc f''} {partSrc p})"

partial def maskSrc : QztMask → String
  | .none => ".none"
  | .nil => ".nil"
  | .leaves ns => s!"(.leaves {ns})"
  | .node a b c d => s!"(.node {maskSrc a} {maskSrc b} {maskSrc c} {maskSrc d})"

/-- A JSON string (the data here has no quotes or backslashes). -/
def jstr (s : String) : String := "\"" ++ s ++ "\""

def jlist (l : List String) : String := "[" ++ ",".intercalate l ++ "]"

def jnats (l : List Nat) : String := jlist (l.map toString)

def jbool (b : Bool) : String := if b then "true" else "false"

/-! ### Measuring -/

/-- Evaluate `f ()` (not inlined, so that the evaluation happens between the two heartbeat
counts of `measure`). -/
@[noinline] def evalBool (f : Unit → Bool) : IO Bool := pure (f ())

/-- The result of `f ()` and the number of heartbeats (small allocations) of one evaluation. -/
def measureOnce (f : Unit → Bool) : IO (Bool × Nat) := do
  let h0 ← IO.getNumHeartbeats
  let r ← evalBool f
  let h1 ← IO.getNumHeartbeats
  return (r, h1 - h0)

/-- The result of `f ()` and the number of heartbeats of its evaluation, measured on a second
evaluation (the first one may include the one-time initialization of shared constants). -/
def measure (f : Unit → Bool) : IO (Bool × Nat) := do
  let _ ← measureOnce f
  measureOnce f

/-- The native time (ns) of an evaluation of `f ()`, the least of three (only for calibrating the
cost model: `present_gen.py --calibrate`; the generator never uses times). -/
def timeNs (f : Unit → Bool) : IO Nat := do
  let mut best := 0
  for k in [0, 1, 2] do
    let t0 ← IO.monoNanosNow
    let _ ← evalBool f
    let t1 ← IO.monoNanosNow
    best := if k == 0 then t1 - t0 else min best (t1 - t0)
  return best

/-! ### Counting the comparisons of parts

`cmpPart` allocates nothing, so heartbeats do not see it; the hubcap checks call it for every
rule of every `sortDrules`, and the subset test for the rules of every `checkUnfit`. These
functions count the steps of the kernel's (lazy) versions of those comparisons, and copies of
the recursive checks add them up (the checks here all succeed, so every call of the
reducibility check that the lazy `&&` reaches returns `true`, and the copies take `true` for it
without evaluating it). -/

/-- One plus the number of range comparisons that `cmpPartFast p q` makes: it walks the
subparts of `q` and stops at the first disjoint pair of ranges. -/
partial def cmpSteps (p q : Part) : Nat :=
  let st (c : PartRel) (rest : Unit → Nat) : Nat :=
    match c with
    | .disjoint => 1
    | _ => 1 + rest ()
  match q, p with
  | .cons sq hq q', .cons sp hp p' =>
    st (cmpRange sp sq) fun _ => st (cmpRange hp hq) fun _ => cmpSteps p' q'
  | .cons sq hq q', .cons6 hp _ p' =>
    st (cmpRange .pr66 sq) fun _ => st (cmpRange hp hq) fun _ => cmpSteps p' q'
  | .cons sq hq q', .cons7 hp _ _ p' =>
    st (cmpRange .pr77 sq) fun _ => st (cmpRange hp hq) fun _ => cmpSteps p' q'
  | .cons sq hq q', .cons8 hp _ _ _ p' =>
    st (cmpRange .pr88 sq) fun _ => st (cmpRange hp hq) fun _ => cmpSteps p' q'
  | .cons6 hq _ q', .cons sp hp p' =>
    st (notPsubset (cmpRange sp .pr66)) fun _ => st (cmpRange hp hq) fun _ => cmpSteps p' q'
  | .cons7 hq _ _ q', .cons sp hp p' =>
    st (notPsubset (cmpRange sp .pr77)) fun _ => st (cmpRange hp hq) fun _ => cmpSteps p' q'
  | .cons8 hq _ _ _ q', .cons sp hp p' =>
    st (notPsubset (cmpRange sp .pr88)) fun _ => st (cmpRange hp hq) fun _ => cmpSteps p' q'
  | .cons6 hq f1q q', .cons6 hp f1p p' =>
    st (cmpRange hp hq) fun _ => st (cmpRange f1p f1q) fun _ => cmpSteps p' q'
  | .cons7 hq f1q f2q q', .cons7 hp f1p f2p p' =>
    st (cmpRange hp hq) fun _ => st (cmpRange f1p f1q) fun _ => st (cmpRange f2p f2q) fun _ =>
      cmpSteps p' q'
  | .cons8 hq f1q f2q f3q q', .cons8 hp f1p f2p f3p p' =>
    st (cmpRange hp hq) fun _ => st (cmpRange f1p f1q) fun _ => st (cmpRange f2p f2q) fun _ =>
      st (cmpRange f3p f3q) fun _ => cmpSteps p' q'
  | _, _ => 1

/-- One plus the number of range tests that `subsetPartFast' p q` makes: it walks the subparts
of `q` and stops at the first range of `p` that is not a subset. -/
partial def subsetSteps (p q : Part) : Nat :=
  let st (c : PartRel) (rest : Unit → Nat) : Nat :=
    match c with
    | .subset => 1 + rest ()
    | _ => 1
  match q, p with
  | .cons sq hq q', .cons sp hp p' =>
    st (cmpRange sp sq) fun _ => st (cmpRange hp hq) fun _ => subsetSteps p' q'
  | .cons sq hq q', .cons6 hp _ p' =>
    st (cmpRange .pr66 sq) fun _ => st (cmpRange hp hq) fun _ => subsetSteps p' q'
  | .cons sq hq q', .cons7 hp _ _ p' =>
    st (cmpRange .pr77 sq) fun _ => st (cmpRange hp hq) fun _ => subsetSteps p' q'
  | .cons sq hq q', .cons8 hp _ _ _ p' =>
    st (cmpRange .pr88 sq) fun _ => st (cmpRange hp hq) fun _ => subsetSteps p' q'
  | .cons6 hq f1q q', .cons6 hp f1p p' =>
    st (cmpRange hp hq) fun _ => st (cmpRange f1p f1q) fun _ => subsetSteps p' q'
  | .cons7 hq f1q f2q q', .cons7 hp f1p f2p p' =>
    st (cmpRange hp hq) fun _ => st (cmpRange f1p f1q) fun _ => st (cmpRange f2p f2q) fun _ =>
      subsetSteps p' q'
  | .cons8 hq f1q f2q f3q q', .cons8 hp f1p f2p f3p p' =>
    st (cmpRange hp hq) fun _ => st (cmpRange f1p f1q) fun _ => st (cmpRange f2p f2q) fun _ =>
      st (cmpRange f3p f3q) fun _ => subsetSteps p' q'
  | _, _ => 1

/-- The comparison steps of `sortDrules p r`. -/
def sortSteps (p : Part) (r : Drules) : Nat := r.foldl (fun acc q => acc + cmpSteps p q) 0

/-- `checkUnfit p ru` and the steps of its subset tests (it stops at the first subset). -/
def checkUnfitCnt (p : Part) : Drules → Bool × Nat
  | [] => (false, 0)
  | r :: ru' =>
    match cmpPart p r with
    | .subset => (true, subsetSteps p r)
    | _ => let (b, c) := checkUnfitCnt p ru'; (b, c + subsetSteps p r)

mutual

/-- The comparison steps of `checkDbound2Rec (fun _ => true) p rt rs ru nt m`. -/
partial def checkDbound2RecCnt (p : Part) (rt rs ru : Drules) (nt : Nat) : Nat → Nat
  | 0 => 0
  | m' + 1 =>
    match rt with
    | [] => 0
    | r :: rt' =>
      if rt'.length < nt then 0 else
      headSingleCnt p r rt' rs ru nt m' + checkDbound2RecCnt p rt' rs (r :: ru) nt m'

/-- The comparison steps of the work of `checkDbound2Rec` for its first rule `r` (at fuel
`m + 1`, Lean `checkDbound2HeadFast`). -/
partial def headSingleCnt (p r : Part) (rt' rs ru : Drules) (nt m : Nat) : Nat :=
  let p' := meetPart p r
  match checkUnfitCnt p' ru with
  | (true, cu) => cu
  | (false, cu) =>
    match sortDrules p' rt', sortDrules p' rs with
    | ⟨dnt, rt''⟩, ⟨dns, rs'⟩ =>
      cu + sortSteps p' rt' + sortSteps p' rs +
        match dns + nt - dnt with
        | nt' + 1 => checkDbound2RecCnt p' rt'' rs' ru nt' m
        | 0 => 0

end

mutual

/-- The comparison steps of `check2Dbound2Rec nhub (fun _ => true) p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i
nt m`. -/
partial def check2Dbound2RecCnt (nhub : Nat) (p1 p2 : Part) (rt1 rs1 ru1 rt2 rs2 ru2 : Drules)
    (i nt : Nat) : Nat → Nat
  | 0 => 0
  | m' + 1 =>
    match rt1 with
    | [] =>
      match rt2 with
      | [] => 0
      | _ :: _ => check2Dbound2RecCnt nhub p2 p1 rt2 rs2 ru2 rt1 rs1 ru1 (nhub - i) nt m'
    | r :: rt1' =>
      if rt1'.length + rt2.length < nt then 0 else
      headDualCnt nhub p1 r rt1' rs1 ru1 rt2 rs2 ru2 i nt m' +
        check2Dbound2RecCnt nhub p1 p2 rt1' rs1 (r :: ru1) rt2 rs2 ru2 i nt m'

/-- The comparison steps of the work of `check2Dbound2Rec` for its first rule `r` (at fuel
`m + 1`, Lean `check2Dbound2HeadFast`). -/
partial def headDualCnt (nhub : Nat) (p1 r : Part) (rt1' rs1 ru1 rt2 rs2 ru2 : Drules)
    (i nt m : Nat) : Nat :=
  let p1' := meetPart p1 r
  let p2' := rotPart i p1'
  match checkUnfitCnt p1' ru1 with
  | (true, cu1) => cu1
  | (false, cu1) =>
    match checkUnfitCnt p2' ru2 with
    | (true, cu2) => cu1 + cu2
    | (false, cu2) =>
      match sortDrules p1' rt1', sortDrules p1' rs1, sortDrules p2' rt2, sortDrules p2' rs2 with
      | ⟨dnt1, rt1''⟩, ⟨dns1, rs1'⟩, ⟨dnt2, rt2'⟩, ⟨dns2, rs2'⟩ =>
        cu1 + cu2 + sortSteps p1' rt1' + sortSteps p1' rs1 + sortSteps p2' rt2 +
          sortSteps p2' rs2 +
          match dns1 + (dns2 + nt) - (dnt1 + dnt2) with
          | nt' + 1 => check2Dbound2RecCnt nhub p1' p2' rt1'' rs1' ru1 rt2' rs2' ru2 i nt' m
          | 0 => 0

end

/-- The comparison steps of `checkDbound2 (fun _ => true) rf p b`. -/
def checkDbound2Cnt {nhub : Nat} (rf : DruleFork nhub) (p : Part) (b : Int) : Nat :=
  match sortDrules p rf.targetDrules, sortDrules p rf.sourceDrules with
  | ⟨dnt, rt'⟩, ⟨dns, rs'⟩ =>
    sortSteps p rf.targetDrules + sortSteps p rf.sourceDrules +
      match (dns : Int) - (dnt : Int) + b with
      | .ofNat nt => checkDbound2RecCnt p rt' rs' [] nt (rt'.length + 2)
      | .negSucc _ => 0

/-- The comparison steps of `check2Dbound2 (fun _ => true) rf p1 i b`. -/
def check2Dbound2Cnt {nhub : Nat} (rf : DruleFork nhub) (p1 : Part) (i : Nat) (b : Int) : Nat :=
  let p2 := rotPart i p1
  match sortDrules p1 rf.targetDrules, sortDrules p1 rf.sourceDrules,
      sortDrules p2 rf.targetDrules, sortDrules p2 rf.sourceDrules with
  | ⟨dnt1, rt1⟩, ⟨dns1, rs1⟩, ⟨dnt2, rt2⟩, ⟨dns2, rs2⟩ =>
    sortSteps p1 rf.targetDrules + sortSteps p1 rf.sourceDrules + sortSteps p2 rf.targetDrules +
      sortSteps p2 rf.sourceDrules +
      match ((dns1 + dns2 : Nat) : Int) - ((dnt1 + dnt2 : Nat) : Int) + b with
      | .ofNat nt => check2Dbound2RecCnt nhub p1 p2 rt1 rs1 [] rt2 rs2 [] i nt
          (rt1.length + (rt2.length + 3))
      | .negSucc _ => 0

/-! ### Chains of the recursive hubcap checks -/

/-- The context of the chain computations: the hub size, the reducibility check (with the
leaf's pruned quiz tree), the rule table, the expansion threshold. -/
structure Ctx where
  nhub : Nat
  redp : Part → Bool
  rules : Array Part
  subexpand : Nat

def ruleIdx (c : Ctx) (r : Part) : Nat := (c.rules.findIdx? (· == r)).getD 1000000

def rulesJ (c : Ctx) (l : Drules) : String := jnats (l.map (ruleIdx c))

/-- The work of `check2Dbound2Rec` at fuel `m + 1` for its first target rule `r` (Lean
`check2Dbound2HeadFast`), with the faithful functions. -/
def headDual (nhub : Nat) (redp : Part → Bool) (m : Nat) (p1 r : Part)
    (rt1' rs1 ru1 rt2 rs2 ru2 : Drules) (i nt : Nat) : Bool :=
  let p1' := meetPart p1 r
  let p2' := rotPart i p1'
  if checkUnfit p1' ru1 || checkUnfit p2' ru2 then true else
  match sortDrules p1' rt1', sortDrules p1' rs1, sortDrules p2' rt2, sortDrules p2' rs2 with
  | ⟨dnt1, rt1''⟩, ⟨dns1, rs1'⟩, ⟨dnt2, rt2'⟩, ⟨dns2, rs2'⟩ =>
    match dns1 + (dns2 + nt) - (dnt1 + dnt2) with
    | nt' + 1 => check2Dbound2Rec nhub redp p1' p2' rt1'' rs1' ru1 rt2' rs2' ru2 i nt' m
    | 0 => redp p1'

/-- The work of `checkDbound2Rec` at fuel `m + 1` for its first target rule `r` (Lean
`checkDbound2HeadFast`), with the faithful functions. -/
def headSingle (redp : Part → Bool) (m : Nat) (p r : Part) (rt' rs ru : Drules) (nt : Nat) :
    Bool :=
  let p' := meetPart p r
  if checkUnfit p' ru then true else
  match sortDrules p' rt', sortDrules p' rs with
  | ⟨dnt, rt''⟩, ⟨dns, rs'⟩ =>
    match dns + nt - dnt with
    | nt' + 1 => checkDbound2Rec redp p' rt'' rs' ru nt' m
    | 0 => redp p'

/-- The state of a dual chain: `check2Dbound2RecFast nhub redp m p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i
nt`. -/
structure DState where
  m : Nat
  p1 : Part
  p2 : Part
  rt1 : Drules
  rs1 : Drules
  ru1 : Drules
  rt2 : Drules
  rs2 : Drules
  ru2 : Drules
  i : Nat
  nt : Nat

def DState.json (c : Ctx) (s : DState) : String :=
  "{" ++ s!"\"m\":{s.m},\"P1\":{jstr (partSrc s.p1)},\"P2\":{jstr (partSrc s.p2)}," ++
    s!"\"rt1\":{rulesJ c s.rt1},\"rs1\":{rulesJ c s.rs1},\"ru1\":{rulesJ c s.ru1}," ++
    s!"\"rt2\":{rulesJ c s.rt2},\"rs2\":{rulesJ c s.rs2},\"ru2\":{rulesJ c s.ru2}," ++
    s!"\"i\":{s.i},\"nt\":{s.nt}" ++ "}"

/-- The state of a single chain: `checkDbound2RecFast redp m p rt rs ru nt`. -/
structure SState where
  m : Nat
  p : Part
  rt : Drules
  rs : Drules
  ru : Drules
  nt : Nat

def SState.json (c : Ctx) (s : SState) : String :=
  "{" ++ s!"\"m\":{s.m},\"P\":{jstr (partSrc s.p)},\"rt\":{rulesJ c s.rt}," ++
    s!"\"rs\":{rulesJ c s.rs},\"ru\":{rulesJ c s.ru},\"nt\":{s.nt}" ++ "}"

mutual

/-- The chain of a dual check from the state `s`, as JSON: its steps (heads, with their costs
and, above the expansion threshold, their own chains; swaps) and its end. -/
partial def chainDual (c : Ctx) (s0 : DState) : IO String := do
  let mut s := s0
  let mut steps : Array String := #[]
  let mut fin := ""
  repeat
    match s.m with
    | 0 => fin := "fuel0"; break
    | m + 1 =>
      match s.rt1 with
      | [] =>
        match s.rt2 with
        | [] => fin := "nil"; break
        | _ :: _ =>
          steps := steps.push ("{\"t\":\"W\",\"st\":" ++ s.json c ++ "}")
          s := { s with m := m, p1 := s.p2, p2 := s.p1, rt1 := s.rt2, rs1 := s.rs2, ru1 := s.ru2,
                        rt2 := [], rs2 := s.rs1, ru2 := s.ru1, i := c.nhub - s.i }
      | r :: rt1' =>
        if rt1'.length + s.rt2.length < s.nt then fin := "blt"; break
        let st := s
        let (ok, hb) ← measure fun _ =>
          headDual c.nhub c.redp m st.p1 r rt1' st.rs1 st.ru1 st.rt2 st.rs2 st.ru2 st.i st.nt
        let cmp := headDualCnt c.nhub st.p1 r rt1' st.rs1 st.ru1 st.rt2
          st.rs2 st.ru2 st.i st.nt m
        let sub ← if 3 * hb + cmp > c.subexpand then headDualSub c st m r rt1' else pure "null"
        steps := steps.push ("{\"t\":\"H\",\"st\":" ++ st.json c ++
          s!",\"r\":{ruleIdx c r},\"ok\":{jbool ok},\"hb\":{hb},\"cmp\":{cmp}," ++
          s!"\"sub\":{sub}" ++ "}")
        s := { s with m := m, rt1 := rt1', ru1 := r :: s.ru1 }
  return "{" ++ s!"\"steps\":{jlist steps.toList},\"end\":{jstr fin}" ++ "}"

/-- The expansion of a dual head (rule `r` of the state `st`, recursive fuel `m`): its literal
intermediate values and the chain of its recursive call, or `"unfit"`/`"red"` if it has none. -/
partial def headDualSub (c : Ctx) (st : DState) (m : Nat) (r : Part) (rt1' : Drules) :
    IO String := do
  let p1' := meetPart st.p1 r
  let p2' := rotPart st.i p1'
  if checkUnfit p1' st.ru1 || checkUnfit p2' st.ru2 then return jstr "unfit"
  match sortDrules p1' rt1', sortDrules p1' st.rs1, sortDrules p2' st.rt2,
      sortDrules p2' st.rs2 with
  | ⟨dnt1, rt1''⟩, ⟨dns1, rs1'⟩, ⟨dnt2, rt2'⟩, ⟨dns2, rs2'⟩ =>
    match dns1 + (dns2 + st.nt) - (dnt1 + dnt2) with
    | 0 => return jstr "red"
    | nt' + 1 =>
      let s' : DState := ⟨m, p1', p2', rt1'', rs1', st.ru1, rt2', rs2', st.ru2, st.i, nt'⟩
      let ch ← chainDual c s'
      return "{" ++ s!"\"P1\":{jstr (partSrc p1')},\"P2\":{jstr (partSrc p2')}," ++
        s!"\"dnt1\":{dnt1},\"dns1\":{dns1},\"dnt2\":{dnt2},\"dns2\":{dns2}," ++
        s!"\"st\":{s'.json c},\"chain\":{ch}" ++ "}"

end

mutual

/-- The chain of a single check from the state `s`, as JSON (as `chainDual`). -/
partial def chainSingle (c : Ctx) (s0 : SState) : IO String := do
  let mut s := s0
  let mut steps : Array String := #[]
  let mut fin := ""
  repeat
    match s.m with
    | 0 => fin := "fuel0"; break
    | m + 1 =>
      match s.rt with
      | [] => fin := "nil"; break
      | r :: rt' =>
        if rt'.length < s.nt then fin := "blt"; break
        let st := s
        let (ok, hb) ← measure fun _ => headSingle c.redp m st.p r rt' st.rs st.ru st.nt
        let cmp := headSingleCnt st.p r rt' st.rs st.ru st.nt m
        let sub ← if 3 * hb + cmp > c.subexpand then headSingleSub c st m r rt' else pure "null"
        steps := steps.push ("{\"t\":\"H\",\"st\":" ++ st.json c ++
          s!",\"r\":{ruleIdx c r},\"ok\":{jbool ok},\"hb\":{hb},\"cmp\":{cmp}," ++
          s!"\"sub\":{sub}" ++ "}")
        s := { s with m := m, rt := rt', ru := r :: s.ru }
  return "{" ++ s!"\"steps\":{jlist steps.toList},\"end\":{jstr fin}" ++ "}"

/-- The expansion of a single head (as `headDualSub`). -/
partial def headSingleSub (c : Ctx) (st : SState) (m : Nat) (r : Part) (rt' : Drules) :
    IO String := do
  let p' := meetPart st.p r
  if checkUnfit p' st.ru then return jstr "unfit"
  match sortDrules p' rt', sortDrules p' st.rs with
  | ⟨dnt, rt''⟩, ⟨dns, rs'⟩ =>
    match dns + st.nt - dnt with
    | 0 => return jstr "red"
    | nt' + 1 =>
      let s' : SState := ⟨m, p', rt'', rs', st.ru, nt'⟩
      let ch ← chainSingle c s'
      return "{" ++ s!"\"P\":{jstr (partSrc p')},\"dnt\":{dnt},\"dns\":{dns}," ++
        s!"\"st\":{s'.json c},\"chain\":{ch}" ++ "}"

end

/-- The entry of a dual constraint `$[j1+1, j2+1] <= b` of the part `p` (Lean
`check2Dbound2Fast_of_rec_lit`) and its chain, as JSON. -/
def consDual (c : Ctx) (rf : DruleFork c.nhub) (p : Part) (j1 j2 : Nat) (b : Int) :
    IO String := do
  let p1 := hubcapRot c.nhub j1 p
  let i := hubSubn c.nhub j2 j1
  let p2 := rotPart i p1
  match sortDrules p1 rf.targetDrules, sortDrules p1 rf.sourceDrules,
      sortDrules p2 rf.targetDrules, sortDrules p2 rf.sourceDrules with
  | ⟨dnt1, rt1⟩, ⟨dns1, rs1⟩, ⟨dnt2, rt2⟩, ⟨dns2, rs2⟩ =>
    match ((dns1 + dns2 : Nat) : Int) - ((dnt1 + dnt2 : Nat) : Int) + b with
    | .negSucc _ => return jstr "neg"
    | .ofNat nt =>
      let s : DState := ⟨rt1.length + (rt2.length + 3), p1, p2, rt1, rs1, [], rt2, rs2, [], i, nt⟩
      let ch ← chainDual c s
      return "{" ++ s!"\"st\":{s.json c},\"chain\":{ch}" ++ "}"

/-- The entry of a single constraint `$[j+1] <= b` of the part `p` (Lean
`checkDbound2Fast_of_rec_lit`) and its chain, as JSON. -/
def consSingle (c : Ctx) (rf : DruleFork c.nhub) (p : Part) (j : Nat) (b : Int) :
    IO String := do
  let p1 := hubcapRot c.nhub j p
  match sortDrules p1 rf.targetDrules, sortDrules p1 rf.sourceDrules with
  | ⟨dnt, rt'⟩, ⟨dns, rs'⟩ =>
    match (dns : Int) - (dnt : Int) + b with
    | .negSucc _ => return jstr "neg"
    | .ofNat nt =>
      let s : SState := ⟨rt'.length + 2, p1, rt', rs', [], nt⟩
      let ch ← chainSingle c s
      return "{" ++ s!"\"st\":{s.json c},\"chain\":{ch}" ++ "}"

/-! ### The walk -/

/-- The constraints of a hubcap: `(j1, some j2, b)` for `$[j1+1, j2+1] <= b`, `(j, none, b)` for
`$[j+1] <= b`. -/
def hubcapCons : Hubcap → List (Nat × Option Nat × Int)
  | .nil => []
  | .cons1 j b hc => (j, none, b) :: hubcapCons hc
  | .cons2 j1 j2 b hc => (j1, some j2, b) :: hubcapCons hc

structure Out where
  lines : Array String := #[]
  idx : Nat := 0
  fails : Nat := 0

/-- The parameters of a walk: the hub size, its drule fork, the rule table, the expansion
threshold, and whether to record native times (for calibration only). -/
structure Params where
  n : Nat
  rf : DruleFork n
  rules : Array Part
  expand : Nat
  subexpand : Nat
  timing : Bool

partial def walk (P : Params) (t : RTree) (p0 p : Part) (ctx : List Part) (o : Out) :
    IO Out := do
  let n := P.n
  let rf := P.rf
  let idx := o.idx
  let o := { o with idx := idx + 1 }
  let row (kind : String) (ok : Bool) (hb : Nat) (extra : String) : String :=
    "{" ++ s!"\"t\":\"node\",\"idx\":{idx},\"kind\":{jstr kind},\"ok\":{jbool ok},\"hb\":{hb}," ++
      s!"\"p0\":{jstr (partSrc p0)},\"p\":{jstr (partSrc p)}{extra}" ++ "}"
  let timeJ (f : Unit → Bool) : IO String := do
    if P.timing then return s!",\"ns\":{← timeNs f}" else return ""
  match t with
  | .pcase i j k lo named t e =>
    let (_, hb) ← measure fun _ => goodSplit i j k p && goodSplit i j k p0 &&
      sizePart (splitPart i j k lo p) + sizePart (splitPart i j k (!lo) p) +
        sizePart (splitPart i j k lo p0) > 0
    let ok := goodSplit i j k p
    let o := { o with lines := o.lines.push (row "P" ok hb ""),
                      fails := if ok then o.fails else o.fails + 1 }
    let pl := splitPart i j k lo p
    let pr := splitPart i j k (!lo) p
    let p0l := if goodSplit i j k p0 then splitPart i j k lo p0 else pl
    let o ← walk P t p0l pl ctx o
    walk P e p0 pr (if named then p0l :: ctx else ctx) o
  | .red =>
    let mask := PruneGen.redpartMask theQuizTree p
    let qt := qztPrune theQuizTree mask
    let (ok, hb) ← measure fun _ => redpart qt p
    let tj ← timeJ fun _ => redpart qt p
    return { o with lines := o.lines.push (row "R" ok hb s!",\"mask\":{jstr (maskSrc mask)}{tj}"),
                    fails := if ok then o.fails else o.fails + 1 }
  | .hubcap hc =>
    let mask := PruneGen.hubcapMask theQuizTree rf p hc
    let qt := qztPrune theQuizTree mask
    let redp := redpart qt
    let (ok, hb) ← measure fun _ =>
      sizePart p == n && hubcapCover n hc && hubcapFit redp rf p hc
    let tj ← timeJ fun _ => sizePart p == n && hubcapCover n hc && hubcapFit redp rf p hc
    let c : Ctx := ⟨n, redp, P.rules, P.subexpand⟩
    let mut costs : Array String := #[]
    let mut consLines : Array String := #[]
    let mut ci := 0
    let mut cmpAll := 0
    for (j1, oj2, b) in hubcapCons hc do
      let (_, chb) ← measure fun _ => match oj2 with
        | some j2 => check2Dbound2 redp rf (hubcapRot n j1 p) (hubSubn n j2 j1) b
        | none => checkDbound2 redp rf (hubcapRot n j1 p) b
      let ccmp := match oj2 with
        | some j2 => check2Dbound2Cnt rf (hubcapRot n j1 p) (hubSubn n j2 j1) b
        | none => checkDbound2Cnt rf (hubcapRot n j1 p) b
      costs := costs.push s!"[{chb},{ccmp}]"
      cmpAll := cmpAll + ccmp
      if 3 * chb + ccmp > P.expand then
        let body ← match oj2 with
          | some j2 => consDual c rf p j1 j2 b
          | none => consSingle c rf p j1 b
        consLines := consLines.push ("{" ++
          s!"\"t\":\"cons\",\"idx\":{idx},\"ci\":{ci},\"hb\":{chb},\"cmp\":{ccmp}," ++
          s!"\"dual\":{jbool oj2.isSome},\"data\":{body}" ++ "}")
      ci := ci + 1
    let extra := s!",\"cmp\":{cmpAll},\"mask\":{jstr (maskSrc mask)}," ++
      s!"\"cons\":{jlist costs.toList}{tj}"
    -- the node row, then the rows of its expanded constraints
    return { o with lines := o.lines.push (row "H" ok hb extra) ++ consLines,
                    fails := if ok then o.fails else o.fails + 1 }
  | .similar lbl j mir =>
    let ps := ctx.getD lbl .nil
    let (ok, hb) ← measure fun _ => similarCheck ps p j mir
    let ok := ok && lbl < ctx.length
    return { o with lines := o.lines.push (row "S" ok hb ""),
                    fails := if ok then o.fails else o.fails + 1 }

def run (args : List String) : IO UInt32 := do
  let timing := args.getD 4 "" == "time"
  let [treePath, outPath, expandS, subexpandS] := args.take 4
    | IO.eprintln "usage: present_gen_native.lean TREE OUT EXPAND SUBEXPAND [time]"; return 2
  let expand := expandS.toNat!
  let subexpand := subexpandS.toNat!
  let (n, t) ← loadTree treePath
  let rf := theDruleFork n
  -- force the shared data before measuring
  let qs := qztSize theQuizTree
  let rules := (rf.targetDrules ++ rf.sourceDrules).foldl
    (fun (acc : Array Part) r => if acc.contains r then acc else acc.push r) #[]
  let root := pcons_ n
  let o ← walk ⟨n, rf, rules, expand, subexpand, timing⟩ t root root [] {}
  let hdr := "{" ++ s!"\"t\":\"rules\",\"n\":{n},\"qztSize\":{qs}," ++
    s!"\"rules\":{jlist (rules.toList.map (jstr ∘ partSrc))}," ++
    s!"\"target\":{jnats (rf.targetDrules.map fun r => (rules.findIdx? (· == r)).getD 0)}," ++
    s!"\"source\":{jnats (rf.sourceDrules.map fun r => (rules.findIdx? (· == r)).getD 0)}" ++ "}"
  IO.FS.writeFile outPath ("\n".intercalate (hdr :: o.lines.toList) ++ "\n")
  IO.println s!"present{n}: {o.idx} nodes, {o.fails} failed checks"
  return (if o.fails == 0 then 0 else 1)

end PresentGen

def main (args : List String) : IO UInt32 := PresentGen.run args
