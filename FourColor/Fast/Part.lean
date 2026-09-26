/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Part.Basic

/-!
# Kernel-fast part operations

Fast versions, for evaluation by the kernel (`decide +kernel`), of the operations on parts of
`FourColor.Part.Basic` (Coq `part.v`) that the presentation checks use (Coq `present.v`:
`succeed_by_split`, `succeed_by_similarity`, and the part operations inside `redpart` and the
hubcap checks). Each fast definition `fooFast` comes with a theorem `fooFast_eq` stating that
it is equal to the faithful definition `foo` (for all arguments), so that a check evaluated
with the fast operations can be rewritten to the faithful statement; e.g.
`cmpPartFast_eq : cmpPartFast p q = cmpPart p q`.

## Definitions (faithful name → fast name, with its theorem `_eq`)

* ranges: `notPsubset`, `meetPrel`, `applyPartRel`, `cmpRange`, `meetRange`, `memRange`,
  `prangeLo`, `prangeHi`, `goodRsplit`, `splitRange` → `notPsubsetFast`, `meetPrelFast`,
  `applyPartRelFast`, `cmpRangeFast`, `meetRangeFast`, `memRangeFast`, `prangeLoFast`,
  `prangeHiFast`, `goodRsplitFast`, `splitRangeFast`;
* list operations: `sizePart`, `dropPart`, `takePart`, `catPart`, `rotPart`, `catrevPart`,
  `revPart`, `pcons_` → `sizePartFast`, `dropPartFast`, `takePartFast`, `catPartFast`,
  `rotPartFast` (with the one-pass `rotPartRecFast`), `catrevPartFast`, `revPartFast`,
  `pcons_Fast`;
* accessors: `getSpoke`, `nextHat`, `getHat`, `getFan1r`, `getFan2r`, `getFan3r`, `getFan1l`,
  `getFan2l`, `getFan3l` → `getSpokeFast`, ..., `getFan3lFast`;
* mirror image: `mirrorPartRec`, `mirrorPart` → `mirrorPartRecFast`, `mirrorPartFast`;
* splitting: `goodSplit`, `splitPart` → `goodSplitFast`, `splitPartFast`;
* comparison and meet: `cmpPart`, `meetPart` → `cmpPartFast`, `meetPartFast`; and the subset
  test `subsetPartFast p q`, which decides `cmpPart p q = .subset` (`subsetPartFast_eq`).

The semantic fit predicates (`fitp`, `exactFitp`, ...) are not computable and have no fast
version; the converse part (`conversePart`) is only used to compute the discharge rule forks.

## Style

* Recursor style: every recursion and case analysis is a direct application of a recursor
  (`Part.rec`, `Prange.rec`, `PartRel.rec`, `SubpartLoc.rec`, `Nat.rec`, `Bool.rec`), with no
  `match` (matcher auxiliaries and `casesOn`), `ite`/`Decidable`, `brecOn`/`below` tuples of
  structural recursion, or typeclass arithmetic: `Nat.succ`, `Nat.beq`, `Nat.ble` and raw
  literals instead.
* Range tables: `cmpRangeFast` and `meetRangeFast` are two-level `Prange.rec` tables (generated
  from the faithful definitions); the kernel caches each looked-up pair.
* Closed minor premises: where a recursion on one part contains a case analysis on another part
  (`cmpPartFast`, `meetPartFast`, and on a count in `dropPartFast`, `takePartFast`,
  `rotPartRecFast`), the inner recursor's minor premises mention none of the outer bound
  variables, which are passed as arguments instead (the motive is a function type). Then an
  iota reduction instantiates only the branch it takes. In `cmpPartFast`, `meetPrel` is also
  unfolded. Together these make `cmpPart` about 1.5 times faster than recursor style
  alone (`meetPart` about 1.2 times, and `rotPart`, with the one-pass rotation below, 1.7).
* `rotPartFast` walks the rotated prefix once (a continuation collects it), where `rotPart`
  walks it twice (in `dropPart` and `takePart`).
* All the definitions are `noncomputable`: the code generator does not compile recursors.

## Measured speed-ups

Kernel time of `decide +kernel` on workloads extracted from the presentations (Lean
v4.35.0-rc2, the fastest of three runs, faithful → fast): all hub parts of size 7 and 8 against
their forks' rules (`cmpPart`, 4,224 calls): 906 ms → 187 ms (harness alone 34 ms); `meetPart`
then `cmpPart` for straddling rules: 2.57 s → 0.48 s; 400 `Similar` side conditions
(`sizePart`, `mirrorPart`, `rotPart`, `cmpPart`): 1.16 s → 0.17 s; 600 `Pcase` nodes
(`goodSplit`, three `splitPart`s): 1.35 s → 0.35 s; all rotations of 96 hub parts: 535 ms →
104 ms; mirror images: 53 ms → 16 ms; `revPart`/`dropPart`/`catPart`/`takePart`/accessors:
295 ms → 67 ms; `sizePart`: 23 ms → 4.5 ms. The same workloads replayed with Palomar's
checkers (`scripts/palomar_check.sh`): `leanchecker` 7.63 s → 1.61 s, nanoda 7.45 s → 1.12 s,
con-ron 22.3 s → 11.9 s (including its fixed start of about 8 s), and peak memory 551, 432,
1335 MB → 213, 101, 140 MB.
-/

namespace FourColor

/-! ### Range relations and range tables -/

/-- Kernel-fast `notPsubset` (Coq `notPsubset`). -/
noncomputable def notPsubsetFast (c : PartRel) : PartRel :=
  PartRel.rec (motive := fun _ => PartRel) .disjoint .straddle .straddle c

/-- `notPsubsetFast` is `notPsubset`. -/
theorem notPsubsetFast_eq (c : PartRel) : notPsubsetFast c = notPsubset c := by
  cases c <;> rfl

/-- Kernel-fast `meetPrel` (Coq `meet_prel`). -/
noncomputable def meetPrelFast (c c' : PartRel) : PartRel :=
  PartRel.rec (motive := fun _ => PartRel) .disjoint (notPsubsetFast c') c' c

/-- `meetPrelFast` is `meetPrel`. -/
theorem meetPrelFast_eq (c c' : PartRel) : meetPrelFast c c' = meetPrel c c' := by
  cases c <;> cases c' <;> rfl

/-- Kernel-fast `applyPartRel` (Coq `apply_part_rel`). -/
noncomputable def applyPartRelFast (c : PartRel) (b : Bool) : Bool :=
  PartRel.rec (motive := fun _ => Bool) false b true c

/-- `applyPartRelFast` is `applyPartRel`. -/
theorem applyPartRelFast_eq (c : PartRel) (b : Bool) : applyPartRelFast c b = applyPartRel c b := by
  cases c <;> cases b <;> rfl

/-- Kernel-fast `cmpRange` (Coq `cmp_range`): a two-level `Prange.rec` table, row `r`,
column `r'`. -/
noncomputable def cmpRangeFast (r r' : Prange) : PartRel :=
  Prange.rec (motive := fun _ => Prange → PartRel)
    -- pr55
    (fun r' => Prange.rec (motive := fun _ => PartRel) .subset .disjoint .disjoint .disjoint
      .disjoint .subset .disjoint .disjoint .disjoint .subset .disjoint .disjoint .subset
      .disjoint .subset r')
    -- pr66
    (fun r' => Prange.rec (motive := fun _ => PartRel) .disjoint .subset .disjoint .disjoint
      .disjoint .subset .subset .disjoint .disjoint .subset .subset .disjoint .subset .subset
      .subset r')
    -- pr77
    (fun r' => Prange.rec (motive := fun _ => PartRel) .disjoint .disjoint .subset .disjoint
      .disjoint .disjoint .subset .subset .disjoint .subset .subset .subset .subset .subset
      .subset r')
    -- pr88
    (fun r' => Prange.rec (motive := fun _ => PartRel) .disjoint .disjoint .disjoint .subset
      .disjoint .disjoint .disjoint .subset .subset .disjoint .subset .subset .subset .subset
      .subset r')
    -- pr99
    (fun r' => Prange.rec (motive := fun _ => PartRel) .disjoint .disjoint .disjoint .disjoint
      .subset .disjoint .disjoint .disjoint .subset .disjoint .disjoint .subset .disjoint
      .subset .subset r')
    -- pr56
    (fun r' => Prange.rec (motive := fun _ => PartRel) .straddle .straddle .disjoint .disjoint
      .disjoint .subset .straddle .disjoint .disjoint .subset .straddle .disjoint .subset
      .straddle .subset r')
    -- pr67
    (fun r' => Prange.rec (motive := fun _ => PartRel) .disjoint .straddle .straddle .disjoint
      .disjoint .straddle .subset .straddle .disjoint .subset .subset .straddle .subset .subset
      .subset r')
    -- pr78
    (fun r' => Prange.rec (motive := fun _ => PartRel) .disjoint .disjoint .straddle .straddle
      .disjoint .disjoint .straddle .subset .straddle .straddle .subset .subset .subset .subset
      .subset r')
    -- pr89
    (fun r' => Prange.rec (motive := fun _ => PartRel) .disjoint .disjoint .disjoint .straddle
      .straddle .disjoint .disjoint .straddle .subset .disjoint .straddle .subset .straddle
      .subset .subset r')
    -- pr57
    (fun r' => Prange.rec (motive := fun _ => PartRel) .straddle .straddle .straddle .disjoint
      .disjoint .straddle .straddle .straddle .disjoint .subset .straddle .straddle .subset
      .straddle .subset r')
    -- pr68
    (fun r' => Prange.rec (motive := fun _ => PartRel) .disjoint .straddle .straddle .straddle
      .disjoint .straddle .straddle .straddle .straddle .straddle .subset .straddle .subset
      .subset .subset r')
    -- pr79
    (fun r' => Prange.rec (motive := fun _ => PartRel) .disjoint .disjoint .straddle .straddle
      .straddle .disjoint .straddle .straddle .straddle .straddle .straddle .subset .straddle
      .subset .subset r')
    -- pr58
    (fun r' => Prange.rec (motive := fun _ => PartRel) .straddle .straddle .straddle .straddle
      .disjoint .straddle .straddle .straddle .straddle .straddle .straddle .straddle .subset
      .straddle .subset r')
    -- pr69
    (fun r' => Prange.rec (motive := fun _ => PartRel) .disjoint .straddle .straddle .straddle
      .straddle .straddle .straddle .straddle .straddle .straddle .straddle .straddle .straddle
      .subset .subset r')
    -- pr59
    (fun r' => Prange.rec (motive := fun _ => PartRel) .straddle .straddle .straddle .straddle
      .straddle .straddle .straddle .straddle .straddle .straddle .straddle .straddle .straddle
      .straddle .subset r')
    r r'

/-- `cmpRangeFast` is `cmpRange`. -/
theorem cmpRangeFast_eq (r r' : Prange) : cmpRangeFast r r' = cmpRange r r' := by
  cases r <;> cases r' <;> rfl

/-- Kernel-fast `meetRange` (Coq `meet_range`): a two-level `Prange.rec` table, row `r`,
column `r'`. -/
noncomputable def meetRangeFast (r r' : Prange) : Prange :=
  Prange.rec (motive := fun _ => Prange → Prange)
    -- pr55
    (fun r' => Prange.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr55 .pr55
      .pr55 .pr55 .pr55 .pr55 .pr55 .pr55 .pr55 .pr55 r')
    -- pr66
    (fun r' => Prange.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr66 .pr66
      .pr66 .pr66 .pr66 .pr66 .pr66 .pr66 .pr66 .pr66 r')
    -- pr77
    (fun r' => Prange.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr77 .pr77
      .pr77 .pr77 .pr77 .pr77 .pr77 .pr77 .pr77 .pr77 r')
    -- pr88
    (fun r' => Prange.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr88 .pr88
      .pr88 .pr88 .pr88 .pr88 .pr88 .pr88 .pr88 .pr88 r')
    -- pr99
    (fun r' => Prange.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr99 .pr99
      .pr99 .pr99 .pr99 .pr99 .pr99 .pr99 .pr99 .pr99 r')
    -- pr56
    (fun r' => Prange.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr56 .pr66
      .pr56 .pr56 .pr56 .pr66 .pr56 .pr56 .pr66 .pr56 r')
    -- pr67
    (fun r' => Prange.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr66 .pr67
      .pr77 .pr67 .pr67 .pr67 .pr77 .pr67 .pr67 .pr67 r')
    -- pr78
    (fun r' => Prange.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr78 .pr77
      .pr78 .pr88 .pr77 .pr78 .pr78 .pr78 .pr78 .pr78 r')
    -- pr89
    (fun r' => Prange.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr89 .pr89
      .pr88 .pr89 .pr89 .pr88 .pr89 .pr88 .pr89 .pr89 r')
    -- pr57
    (fun r' => Prange.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr56 .pr67
      .pr77 .pr89 .pr57 .pr67 .pr77 .pr57 .pr67 .pr57 r')
    -- pr68
    (fun r' => Prange.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr66 .pr67
      .pr78 .pr88 .pr67 .pr68 .pr78 .pr68 .pr68 .pr68 r')
    -- pr79
    (fun r' => Prange.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr56 .pr77
      .pr78 .pr89 .pr77 .pr78 .pr79 .pr78 .pr79 .pr79 r')
    -- pr58
    (fun r' => Prange.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr56 .pr67
      .pr78 .pr88 .pr57 .pr68 .pr78 .pr58 .pr68 .pr58 r')
    -- pr69
    (fun r' => Prange.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr66 .pr67
      .pr78 .pr89 .pr67 .pr68 .pr79 .pr68 .pr69 .pr69 r')
    -- pr59
    (fun r' => Prange.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr56 .pr67
      .pr78 .pr89 .pr57 .pr68 .pr79 .pr58 .pr69 .pr59 r')
    r r'

/-- `meetRangeFast` is `meetRange`. -/
theorem meetRangeFast_eq (r r' : Prange) : meetRangeFast r r' = meetRange r r' := by
  cases r <;> cases r' <;> rfl

/-- Kernel-fast `memRange` (Coq `mem_range`): a `Prange.rec` over the kernel-accelerated tests
`Nat.beq` and `Nat.ble`, with the same disjunctions as `memRange`. -/
noncomputable def memRangeFast (r : Prange) (n : ℕ) : Bool :=
  Prange.rec (motive := fun _ => Bool)
    (Nat.beq n (nat_lit 5)) (Nat.beq n (nat_lit 6)) (Nat.beq n (nat_lit 7))
    (Nat.beq n (nat_lit 8)) (Nat.ble (nat_lit 9) n)
    -- pr56, pr67, pr78
    (Bool.rec (motive := fun _ => Bool) (Nat.beq n (nat_lit 6)) true (Nat.beq n (nat_lit 5)))
    (Bool.rec (motive := fun _ => Bool) (Nat.beq n (nat_lit 7)) true (Nat.beq n (nat_lit 6)))
    (Bool.rec (motive := fun _ => Bool) (Nat.beq n (nat_lit 8)) true (Nat.beq n (nat_lit 7)))
    -- pr89
    (Nat.ble (nat_lit 8) n)
    -- pr57, pr68
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (Nat.beq n (nat_lit 7)) true (Nat.beq n (nat_lit 6)))
      true (Nat.beq n (nat_lit 5)))
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool) (Nat.beq n (nat_lit 8)) true (Nat.beq n (nat_lit 7)))
      true (Nat.beq n (nat_lit 6)))
    -- pr79
    (Nat.ble (nat_lit 7) n)
    -- pr58
    (Bool.rec (motive := fun _ => Bool)
      (Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool) (Nat.beq n (nat_lit 8)) true (Nat.beq n (nat_lit 7)))
        true (Nat.beq n (nat_lit 6)))
      true (Nat.beq n (nat_lit 5)))
    -- pr69, pr59
    (Nat.ble (nat_lit 6) n)
    (Nat.ble (nat_lit 5) n)
    r

/-- `memRangeFast` is `memRange`. -/
theorem memRangeFast_eq (r : Prange) (n : ℕ) : memRangeFast r n = memRange r n := by
  cases r <;> rfl

/-! ### Splitting ranges -/

/-- Kernel-fast `prangeLo` (Coq `prange_lo`): nested `Nat.rec` on the arity. -/
noncomputable def prangeLoFast (k : ℕ) : Prange :=
  Nat.rec (motive := fun _ => Prange) .pr59 (fun k1 _ =>
    Nat.rec (motive := fun _ => Prange) .pr59 (fun k2 _ =>
      Nat.rec (motive := fun _ => Prange) .pr59 (fun k3 _ =>
        Nat.rec (motive := fun _ => Prange) .pr59 (fun k4 _ =>
          Nat.rec (motive := fun _ => Prange) .pr59 (fun k5 _ =>
            Nat.rec (motive := fun _ => Prange) .pr55 (fun k6 _ =>
              Nat.rec (motive := fun _ => Prange) .pr56 (fun k7 _ =>
                Nat.rec (motive := fun _ => Prange) .pr57 (fun k8 _ =>
                  Nat.rec (motive := fun _ => Prange) .pr58 (fun _ _ => .pr59) k8) k7) k6) k5)
            k4) k3) k2) k1) k

/-- `prangeLoFast` is `prangeLo`. -/
theorem prangeLoFast_eq (k : ℕ) : prangeLoFast k = prangeLo k := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> rfl

/-- Kernel-fast `prangeHi` (Coq `prange_hi`): nested `Nat.rec` on the arity. -/
noncomputable def prangeHiFast (k : ℕ) : Prange :=
  Nat.rec (motive := fun _ => Prange) .pr59 (fun k1 _ =>
    Nat.rec (motive := fun _ => Prange) .pr59 (fun k2 _ =>
      Nat.rec (motive := fun _ => Prange) .pr59 (fun k3 _ =>
        Nat.rec (motive := fun _ => Prange) .pr59 (fun k4 _ =>
          Nat.rec (motive := fun _ => Prange) .pr59 (fun k5 _ =>
            Nat.rec (motive := fun _ => Prange) .pr69 (fun k6 _ =>
              Nat.rec (motive := fun _ => Prange) .pr79 (fun k7 _ =>
                Nat.rec (motive := fun _ => Prange) .pr89 (fun k8 _ =>
                  Nat.rec (motive := fun _ => Prange) .pr99 (fun _ _ => .pr59) k8) k7) k6) k5)
            k4) k3) k2) k1) k

/-- `prangeHiFast` is `prangeHi`. -/
theorem prangeHiFast_eq (k : ℕ) : prangeHiFast k = prangeHi k := by
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | k <;> rfl

/-- Kernel-fast `goodRsplit` (Coq `good_rsplit`). -/
noncomputable def goodRsplitFast (k : ℕ) (r : Prange) : Bool :=
  PartRel.rec (motive := fun _ => Bool) false true false (cmpRangeFast r (prangeLoFast k))

/-- `goodRsplitFast` is `goodRsplit`. -/
theorem goodRsplitFast_eq (k : ℕ) (r : Prange) : goodRsplitFast k r = goodRsplit k r := by
  unfold goodRsplitFast goodRsplit
  rw [prangeLoFast_eq, cmpRangeFast_eq]
  cases cmpRange r (prangeLo k) <;> rfl

/-- Kernel-fast `splitRange` (Coq `split_range`). -/
noncomputable def splitRangeFast (k : ℕ) (lo : Bool) (r : Prange) : Prange :=
  meetRangeFast (Bool.rec (motive := fun _ => Prange) (prangeHiFast k) (prangeLoFast k) lo) r

/-- `splitRangeFast` is `splitRange`. -/
theorem splitRangeFast_eq (k : ℕ) (lo : Bool) (r : Prange) :
    splitRangeFast k lo r = splitRange k lo r := by
  cases lo <;> simp only [splitRangeFast, splitRange, meetRangeFast_eq, prangeLoFast_eq,
    prangeHiFast_eq] <;> rfl

/-! ### List operations on parts -/

/-- Kernel-fast `sizePart` (Coq `size_part`): `Nat.succ` over `Part.rec`, which the kernel
folds into a literal. -/
noncomputable def sizePartFast (p : Part) : ℕ :=
  Part.rec (motive := fun _ => ℕ) Nat.zero (fun _ _ _ n => Nat.succ n)
    (fun _ _ _ n => Nat.succ n) (fun _ _ _ _ n => Nat.succ n) (fun _ _ _ _ _ n => Nat.succ n) p

/-- `sizePartFast` is `sizePart`. -/
theorem sizePartFast_eq (p : Part) : sizePartFast p = sizePart p := by
  induction p with
  | nil => rfl
  | cons _ _ _ ih | cons6 _ _ _ ih | cons7 _ _ _ _ ih | cons8 _ _ _ _ _ ih =>
    exact congrArg Nat.succ ih

/-- Kernel-fast `dropPart` (Coq `drop_part`): `Nat.rec` on the count, then a `Part.rec` whose
minor premises are closed (the recursive call is passed as an argument, so the iota reduction
does not rebuild the branches it does not take). -/
noncomputable def dropPartFast (n : ℕ) : Part → Part :=
  Nat.rec (motive := fun _ => Part → Part) (fun p => p)
    (fun _ ih p => Part.rec (motive := fun _ => (Part → Part) → Part) (fun _ => .nil)
      (fun _ _ p' _ ih => ih p') (fun _ _ p' _ ih => ih p') (fun _ _ _ p' _ ih => ih p')
      (fun _ _ _ _ p' _ ih => ih p') p ih) n

/-- `dropPartFast` is `dropPart`. -/
theorem dropPartFast_eq (n : ℕ) (p : Part) : dropPartFast n p = dropPart n p := by
  induction n generalizing p with
  | zero => cases p <;> rfl
  | succ n ih =>
    cases p with
    | nil => rfl
    | cons _ _ p | cons6 _ _ p | cons7 _ _ _ p | cons8 _ _ _ _ p => exact ih p

/-- Kernel-fast `takePart` (Coq `take_part`), with closed minor premises. -/
noncomputable def takePartFast (n : ℕ) : Part → Part :=
  Nat.rec (motive := fun _ => Part → Part) (fun _ => .nil)
    (fun _ ih p => Part.rec (motive := fun _ => (Part → Part) → Part) (fun _ => .nil)
      (fun s h p' _ ih => .cons s h (ih p')) (fun h f1 p' _ ih => .cons6 h f1 (ih p'))
      (fun h f1 f2 p' _ ih => .cons7 h f1 f2 (ih p'))
      (fun h f1 f2 f3 p' _ ih => .cons8 h f1 f2 f3 (ih p')) p ih) n

/-- `takePartFast` is `takePart`. -/
theorem takePartFast_eq (n : ℕ) (p : Part) : takePartFast n p = takePart n p := by
  induction n generalizing p with
  | zero => cases p <;> rfl
  | succ n ih =>
    cases p with
    | nil => rfl
    | cons s h p => exact congrArg (Part.cons s h) (ih p)
    | cons6 h f1 p => exact congrArg (Part.cons6 h f1) (ih p)
    | cons7 h f1 f2 p => exact congrArg (Part.cons7 h f1 f2) (ih p)
    | cons8 h f1 f2 f3 p => exact congrArg (Part.cons8 h f1 f2 f3) (ih p)

/-- Kernel-fast `catPart` (Coq `cat_part`). -/
noncomputable def catPartFast (p q : Part) : Part :=
  Part.rec (motive := fun _ => Part) q (fun s h _ p' => .cons s h p')
    (fun h f1 _ p' => .cons6 h f1 p') (fun h f1 f2 _ p' => .cons7 h f1 f2 p')
    (fun h f1 f2 f3 _ p' => .cons8 h f1 f2 f3 p') p

/-- `catPartFast` is `catPart`. -/
theorem catPartFast_eq (p q : Part) : catPartFast p q = catPart p q := by
  induction p with
  | nil => rfl
  | cons s h p ih => exact congrArg (Part.cons s h) ih
  | cons6 h f1 p ih => exact congrArg (Part.cons6 h f1) ih
  | cons7 h f1 f2 p ih => exact congrArg (Part.cons7 h f1 f2) ih
  | cons8 h f1 f2 f3 p ih => exact congrArg (Part.cons8 h f1 f2 f3) ih

/-- The one-pass rotation behind `rotPartFast`: `rotPartRecFast n p k` drops the first `n`
subparts of `p` while collecting them in the continuation `k`, and then appends `k .nil` to
the rest (see `rotPartRecFast_eq`). -/
noncomputable def rotPartRecFast (n : ℕ) : Part → (Part → Part) → Part :=
  Nat.rec (motive := fun _ => Part → (Part → Part) → Part) (fun p k => catPartFast p (k .nil))
    (fun _ ih p k => Part.rec
      (motive := fun _ => (Part → (Part → Part) → Part) → (Part → Part) → Part)
      (fun _ k => k .nil)
      (fun s h p' _ ih k => ih p' (fun t => k (.cons s h t)))
      (fun h f1 p' _ ih k => ih p' (fun t => k (.cons6 h f1 t)))
      (fun h f1 f2 p' _ ih k => ih p' (fun t => k (.cons7 h f1 f2 t)))
      (fun h f1 f2 f3 p' _ ih k => ih p' (fun t => k (.cons8 h f1 f2 f3 t))) p ih k) n

/-- The specification of the one-pass rotation: `rotPartRecFast n p k` is `dropPart n p`
followed by `k (takePart n p)`. -/
theorem rotPartRecFast_eq (n : ℕ) (p : Part) (k : Part → Part) :
    rotPartRecFast n p k = catPart (dropPart n p) (k (takePart n p)) := by
  induction n generalizing p k with
  | zero =>
    show catPartFast p (k .nil) = _
    rw [catPartFast_eq]
    cases p <;> rfl
  | succ n ih =>
    cases p with
    | nil => rfl
    | cons s h p => exact ih p (fun t => k (.cons s h t))
    | cons6 h f1 p => exact ih p (fun t => k (.cons6 h f1 t))
    | cons7 h f1 f2 p => exact ih p (fun t => k (.cons7 h f1 f2 t))
    | cons8 h f1 f2 f3 p => exact ih p (fun t => k (.cons8 h f1 f2 f3 t))

/-- Kernel-fast `rotPart` (Coq `rot_part`): one pass over the dropped prefix (the faithful
definition walks it twice, in `dropPart` and `takePart`). -/
noncomputable def rotPartFast (n : ℕ) (p : Part) : Part := rotPartRecFast n p (fun t => t)

/-- `rotPartFast` is `rotPart`. -/
theorem rotPartFast_eq (n : ℕ) (p : Part) : rotPartFast n p = rotPart n p :=
  rotPartRecFast_eq n p (fun t => t)

/-- Kernel-fast `catrevPart` (Coq `catrev_part`). -/
noncomputable def catrevPartFast (p1 p2 : Part) : Part :=
  Part.rec (motive := fun _ => Part → Part) (fun p2 => p2)
    (fun s h _ ih p2 => ih (.cons s h p2)) (fun h f1 _ ih p2 => ih (.cons6 h f1 p2))
    (fun h f1 f2 _ ih p2 => ih (.cons7 h f1 f2 p2))
    (fun h f1 f2 f3 _ ih p2 => ih (.cons8 h f1 f2 f3 p2)) p1 p2

/-- `catrevPartFast` is `catrevPart`. -/
theorem catrevPartFast_eq (p1 p2 : Part) : catrevPartFast p1 p2 = catrevPart p1 p2 := by
  induction p1 generalizing p2 with
  | nil => rfl
  | cons s h p ih => exact ih (.cons s h p2)
  | cons6 h f1 p ih => exact ih (.cons6 h f1 p2)
  | cons7 h f1 f2 p ih => exact ih (.cons7 h f1 f2 p2)
  | cons8 h f1 f2 f3 p ih => exact ih (.cons8 h f1 f2 f3 p2)

/-- Kernel-fast `revPart` (Coq `rev_part`). -/
noncomputable def revPartFast (p : Part) : Part := catrevPartFast p .nil

/-- `revPartFast` is `revPart`. -/
theorem revPartFast_eq (p : Part) : revPartFast p = revPart p := catrevPartFast_eq p .nil

/-- Kernel-fast `pcons_` (Coq `pcons_`). -/
noncomputable def pcons_Fast (n : ℕ) : Part :=
  Nat.rec (motive := fun _ => Part) .nil (fun _ p => .cons .pr59 .pr59 p) n

/-- `pcons_Fast` is `pcons_`. -/
theorem pcons_Fast_eq (n : ℕ) : pcons_Fast n = pcons_ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pcons_, Function.iterate_succ_apply', ← pcons_, ← ih]
    rfl

/-! ### Accessors -/

/-- Kernel-fast `getSpoke` (Coq `get_spoke`). -/
noncomputable def getSpokeFast (p : Part) : Prange :=
  Part.rec (motive := fun _ => Prange) .pr59 (fun s _ _ _ => s) (fun _ _ _ _ => .pr66)
    (fun _ _ _ _ _ => .pr77) (fun _ _ _ _ _ _ => .pr88) p

/-- `getSpokeFast` is `getSpoke`. -/
theorem getSpokeFast_eq (p : Part) : getSpokeFast p = getSpoke p := by cases p <;> rfl

/-- Kernel-fast `nextHat` (Coq `next_hat`). -/
noncomputable def nextHatFast (h0 : Prange) (p : Part) : Prange :=
  Part.rec (motive := fun _ => Prange) h0 (fun _ h _ _ => h) (fun h _ _ _ => h)
    (fun h _ _ _ _ => h) (fun h _ _ _ _ _ => h) p

/-- `nextHatFast` is `nextHat`. -/
theorem nextHatFast_eq (h0 : Prange) (p : Part) : nextHatFast h0 p = nextHat h0 p := by
  cases p <;> rfl

/-- Kernel-fast `getHat` (Coq `get_hat`). -/
noncomputable def getHatFast (p : Part) : Prange :=
  Part.rec (motive := fun _ => Prange) .pr59 (fun _ h _ _ => h) (fun h _ _ _ => h)
    (fun h _ _ _ _ => h) (fun h _ _ _ _ _ => h) p

/-- `getHatFast` is `getHat`. -/
theorem getHatFast_eq (p : Part) : getHatFast p = getHat p := by cases p <;> rfl

/-- Kernel-fast `getFan1r` (Coq `get_fan1r`). -/
noncomputable def getFan1rFast (p : Part) : Prange :=
  Part.rec (motive := fun _ => Prange) .pr59 (fun _ _ _ _ => .pr59) (fun _ f1 _ _ => f1)
    (fun _ f1 _ _ _ => f1) (fun _ f1 _ _ _ _ => f1) p

/-- `getFan1rFast` is `getFan1r`. -/
theorem getFan1rFast_eq (p : Part) : getFan1rFast p = getFan1r p := by cases p <;> rfl

/-- Kernel-fast `getFan2r` (Coq `get_fan2r`). -/
noncomputable def getFan2rFast (p : Part) : Prange :=
  Part.rec (motive := fun _ => Prange) .pr59 (fun _ _ _ _ => .pr59) (fun _ _ _ _ => .pr59)
    (fun _ _ f2 _ _ => f2) (fun _ _ f2 _ _ _ => f2) p

/-- `getFan2rFast` is `getFan2r`. -/
theorem getFan2rFast_eq (p : Part) : getFan2rFast p = getFan2r p := by cases p <;> rfl

/-- Kernel-fast `getFan3r` (Coq `get_fan3r`). -/
noncomputable def getFan3rFast (p : Part) : Prange :=
  Part.rec (motive := fun _ => Prange) .pr59 (fun _ _ _ _ => .pr59) (fun _ _ _ _ => .pr59)
    (fun _ _ _ _ _ => .pr59) (fun _ _ _ f3 _ _ => f3) p

/-- `getFan3rFast` is `getFan3r`. -/
theorem getFan3rFast_eq (p : Part) : getFan3rFast p = getFan3r p := by cases p <;> rfl

/-- Kernel-fast `getFan1l` (Coq `get_fan1l`). -/
noncomputable def getFan1lFast (p : Part) : Prange :=
  Part.rec (motive := fun _ => Prange) .pr59 (fun _ _ _ _ => .pr59) (fun _ f1 _ _ => f1)
    (fun _ _ f2 _ _ => f2) (fun _ _ _ f3 _ _ => f3) p

/-- `getFan1lFast` is `getFan1l`. -/
theorem getFan1lFast_eq (p : Part) : getFan1lFast p = getFan1l p := by cases p <;> rfl

/-- Kernel-fast `getFan2l` (Coq `get_fan2l`). -/
noncomputable def getFan2lFast (p : Part) : Prange :=
  Part.rec (motive := fun _ => Prange) .pr59 (fun _ _ _ _ => .pr59) (fun _ _ _ _ => .pr59)
    (fun _ f1 _ _ _ => f1) (fun _ _ f2 _ _ _ => f2) p

/-- `getFan2lFast` is `getFan2l`. -/
theorem getFan2lFast_eq (p : Part) : getFan2lFast p = getFan2l p := by cases p <;> rfl

/-- Kernel-fast `getFan3l` (Coq `get_fan3l`). -/
noncomputable def getFan3lFast (p : Part) : Prange :=
  Part.rec (motive := fun _ => Prange) .pr59 (fun _ _ _ _ => .pr59) (fun _ _ _ _ => .pr59)
    (fun _ _ _ _ _ => .pr59) (fun _ f1 _ _ _ _ => f1) p

/-- `getFan3lFast` is `getFan3l`. -/
theorem getFan3lFast_eq (p : Part) : getFan3lFast p = getFan3l p := by cases p <;> rfl

/-! ### Mirror image -/

/-- Kernel-fast `mirrorPartRec` (Coq `mirror_part_rec`). -/
noncomputable def mirrorPartRecFast (h0 : Prange) (rp p : Part) : Part :=
  Part.rec (motive := fun _ => Part → Part) (fun rp => rp)
    (fun s _ p' ih rp => ih (.cons s (nextHatFast h0 p') rp))
    (fun _ f1 p' ih rp => ih (.cons6 (nextHatFast h0 p') f1 rp))
    (fun _ f1 f2 p' ih rp => ih (.cons7 (nextHatFast h0 p') f2 f1 rp))
    (fun _ f1 f2 f3 p' ih rp => ih (.cons8 (nextHatFast h0 p') f3 f2 f1 rp)) p rp

/-- `mirrorPartRecFast` is `mirrorPartRec`. -/
theorem mirrorPartRecFast_eq (h0 : Prange) (rp p : Part) :
    mirrorPartRecFast h0 rp p = mirrorPartRec h0 rp p := by
  induction p generalizing rp with
  | nil => rfl
  | cons s h p ih =>
    rw [mirrorPartRec, ← nextHatFast_eq]
    exact ih _
  | cons6 h f1 p ih =>
    rw [mirrorPartRec, ← nextHatFast_eq]
    exact ih _
  | cons7 h f1 f2 p ih =>
    rw [mirrorPartRec, ← nextHatFast_eq]
    exact ih _
  | cons8 h f1 f2 f3 p ih =>
    rw [mirrorPartRec, ← nextHatFast_eq]
    exact ih _

/-- Kernel-fast `mirrorPart` (Coq `mirror_part`). -/
noncomputable def mirrorPartFast (p : Part) : Part := mirrorPartRecFast (getHatFast p) .nil p

/-- `mirrorPartFast` is `mirrorPart`. -/
theorem mirrorPartFast_eq (p : Part) : mirrorPartFast p = mirrorPart p := by
  rw [mirrorPartFast, mirrorPart, mirrorPartRecFast_eq, getHatFast_eq]

/-! ### Part splitting -/

/-- Kernel-fast `goodSplit` (Coq `good_split`): a `SubpartLoc.rec` on the sublocation, then a
`Part.rec` on the subpart. -/
noncomputable def goodSplitFast (i : SubpartLoc) (j k : ℕ) (p : Part) : Bool :=
  SubpartLoc.rec (motive := fun _ => Bool)
    -- spoke
    (Part.rec (motive := fun _ => Bool) false (fun s _ _ _ => goodRsplitFast k s)
      (fun _ _ _ _ => false) (fun _ _ _ _ _ => false) (fun _ _ _ _ _ _ => false)
      (dropPartFast j p))
    -- hat
    (Part.rec (motive := fun _ => Bool) false (fun _ h _ _ => goodRsplitFast k h)
      (fun h _ _ _ => goodRsplitFast k h) (fun h _ _ _ _ => goodRsplitFast k h)
      (fun h _ _ _ _ _ => goodRsplitFast k h) (dropPartFast j p))
    -- fan1
    (Part.rec (motive := fun _ => Bool) false
      (fun s _ _ _ => Prange.rec (motive := fun _ => Bool) false (goodRsplitFast k .pr59)
        (goodRsplitFast k .pr59) (goodRsplitFast k .pr59) false false false false false false
        false false false false false s)
      (fun _ f1 _ _ => goodRsplitFast k f1) (fun _ f1 _ _ _ => goodRsplitFast k f1)
      (fun _ f1 _ _ _ _ => goodRsplitFast k f1) (dropPartFast j p))
    -- fan2
    (Part.rec (motive := fun _ => Bool) false
      (fun s _ _ _ => Prange.rec (motive := fun _ => Bool) false false (goodRsplitFast k .pr59)
        (goodRsplitFast k .pr59) false false false false false false false false false false
        false s)
      (fun _ _ _ _ => false) (fun _ _ f2 _ _ => goodRsplitFast k f2)
      (fun _ _ f2 _ _ _ => goodRsplitFast k f2) (dropPartFast j p))
    -- fan3
    (Part.rec (motive := fun _ => Bool) false
      (fun s _ _ _ => Prange.rec (motive := fun _ => Bool) false false false
        (goodRsplitFast k .pr59) false false false false false false false false false false
        false s)
      (fun _ _ _ _ => false) (fun _ _ _ _ _ => false)
      (fun _ _ _ f3 _ _ => goodRsplitFast k f3) (dropPartFast j p))
    i

/-- `goodSplitFast` is `goodSplit`. -/
theorem goodSplitFast_eq (i : SubpartLoc) (j k : ℕ) (p : Part) :
    goodSplitFast i j k p = goodSplit i j k p := by
  have e : goodRsplitFast = goodRsplit := funext fun k => funext fun r => goodRsplitFast_eq k r
  unfold goodSplitFast goodSplit
  rw [e, dropPartFast_eq]
  generalize dropPart j p = q
  cases i <;> rcases q with _ | ⟨s, h, q⟩ | ⟨h, f1, q⟩ | ⟨h, f1, f2, q⟩ | ⟨h, f1, f2, f3, q⟩ <;>
    (try cases s) <;> rfl

/-- Kernel-fast `splitPart` (Coq `split_part`): a `SubpartLoc.rec` on the sublocation, then a
`Part.rec` on the subpart. -/
noncomputable def splitPartFast (i : SubpartLoc) (j k : ℕ) (lo : Bool) (p : Part) : Part :=
  SubpartLoc.rec (motive := fun _ => Part)
    -- spoke
    (Part.rec (motive := fun _ => Part) p
      (fun s h p' _ => catPartFast (takePartFast j p) (.cons (splitRangeFast k lo s) h p'))
      (fun _ _ _ _ => p) (fun _ _ _ _ _ => p) (fun _ _ _ _ _ _ => p) (dropPartFast j p))
    -- hat
    (Part.rec (motive := fun _ => Part) p
      (fun s h p' _ => catPartFast (takePartFast j p) (.cons s (splitRangeFast k lo h) p'))
      (fun h f1 p' _ => catPartFast (takePartFast j p) (.cons6 (splitRangeFast k lo h) f1 p'))
      (fun h f1 f2 p' _ =>
        catPartFast (takePartFast j p) (.cons7 (splitRangeFast k lo h) f1 f2 p'))
      (fun h f1 f2 f3 p' _ =>
        catPartFast (takePartFast j p) (.cons8 (splitRangeFast k lo h) f1 f2 f3 p'))
      (dropPartFast j p))
    -- fan1
    (Part.rec (motive := fun _ => Part) p
      (fun s h p' _ => Prange.rec (motive := fun _ => Part) p
        (catPartFast (takePartFast j p) (.cons6 h (splitRangeFast k lo .pr59) p'))
        (catPartFast (takePartFast j p) (.cons7 h (splitRangeFast k lo .pr59) .pr59 p'))
        (catPartFast (takePartFast j p) (.cons8 h (splitRangeFast k lo .pr59) .pr59 .pr59 p'))
        p p p p p p p p p p p s)
      (fun h f1 p' _ => catPartFast (takePartFast j p) (.cons6 h (splitRangeFast k lo f1) p'))
      (fun h f1 f2 p' _ =>
        catPartFast (takePartFast j p) (.cons7 h (splitRangeFast k lo f1) f2 p'))
      (fun h f1 f2 f3 p' _ =>
        catPartFast (takePartFast j p) (.cons8 h (splitRangeFast k lo f1) f2 f3 p'))
      (dropPartFast j p))
    -- fan2
    (Part.rec (motive := fun _ => Part) p
      (fun s h p' _ => Prange.rec (motive := fun _ => Part) p p
        (catPartFast (takePartFast j p) (.cons7 h .pr59 (splitRangeFast k lo .pr59) p'))
        (catPartFast (takePartFast j p) (.cons8 h .pr59 (splitRangeFast k lo .pr59) .pr59 p'))
        p p p p p p p p p p p s)
      (fun _ _ _ _ => p)
      (fun h f1 f2 p' _ =>
        catPartFast (takePartFast j p) (.cons7 h f1 (splitRangeFast k lo f2) p'))
      (fun h f1 f2 f3 p' _ =>
        catPartFast (takePartFast j p) (.cons8 h f1 (splitRangeFast k lo f2) f3 p'))
      (dropPartFast j p))
    -- fan3
    (Part.rec (motive := fun _ => Part) p
      (fun s h p' _ => Prange.rec (motive := fun _ => Part) p p p
        (catPartFast (takePartFast j p) (.cons8 h .pr59 .pr59 (splitRangeFast k lo .pr59) p'))
        p p p p p p p p p p p s)
      (fun _ _ _ _ => p) (fun _ _ _ _ _ => p)
      (fun h f1 f2 f3 p' _ =>
        catPartFast (takePartFast j p) (.cons8 h f1 f2 (splitRangeFast k lo f3) p'))
      (dropPartFast j p))
    i

/-- `splitPartFast` is `splitPart`. -/
theorem splitPartFast_eq (i : SubpartLoc) (j k : ℕ) (lo : Bool) (p : Part) :
    splitPartFast i j k lo p = splitPart i j k lo p := by
  have e1 : splitRangeFast = splitRange :=
    funext fun k => funext fun lo => funext fun r => splitRangeFast_eq k lo r
  have e2 : catPartFast = catPart := funext fun p => funext fun q => catPartFast_eq p q
  unfold splitPartFast splitPart
  rw [e1, e2, dropPartFast_eq, takePartFast_eq]
  generalize dropPart j p = q
  cases i <;> rcases q with _ | ⟨s, h, q⟩ | ⟨h, f1, q⟩ | ⟨h, f1, f2, q⟩ | ⟨h, f1, f2, f3, q⟩ <;>
    (try cases s) <;> rfl

/-! ### Part comparison and intersection -/

/-- `mp% c rest` is `meetPrelFast c rest` unfolded: a `PartRel.rec` on `c` (the result of a
range comparison, which the kernel caches) choosing `.disjoint`, `notPsubset rest` or `rest`. -/
local macro "mp% " c:term:max rest:term:max : term =>
  `(PartRel.rec (motive := fun _ => PartRel) PartRel.disjoint
      (PartRel.rec (motive := fun _ => PartRel) PartRel.disjoint PartRel.straddle
        PartRel.straddle $rest) $rest $c)

/-- Kernel-fast `cmpPart` (Coq `cmp_part`): `Part.rec` on `q`, then on `p`. The inner
`Part.rec` has closed minor premises (the ranges of `q`'s subpart and the recursive call are
passed as arguments), so that the iota reduction does not rebuild the branches it does not
take, and `meetPrel` is unfolded (`mp%`). -/
noncomputable def cmpPartFast (p q : Part) : PartRel :=
  Part.rec (motive := fun _ => Part → PartRel)
    (fun _ => .subset)
    (fun sq hq _ ih p => Part.rec
      (motive := fun _ => Prange → Prange → (Part → PartRel) → PartRel)
      (fun _ _ _ => .straddle)
      (fun sp hp p' _ sq hq ih => mp% (cmpRangeFast sp sq) (mp% (cmpRangeFast hp hq) (ih p')))
      (fun hp _ p' _ sq hq ih =>
        mp% (cmpRangeFast .pr66 sq) (mp% (cmpRangeFast hp hq) (ih p')))
      (fun hp _ _ p' _ sq hq ih =>
        mp% (cmpRangeFast .pr77 sq) (mp% (cmpRangeFast hp hq) (ih p')))
      (fun hp _ _ _ p' _ sq hq ih =>
        mp% (cmpRangeFast .pr88 sq) (mp% (cmpRangeFast hp hq) (ih p')))
      p sq hq ih)
    (fun hq f1q _ ih p => Part.rec
      (motive := fun _ => Prange → Prange → (Part → PartRel) → PartRel)
      (fun _ _ _ => .straddle)
      (fun sp hp p' _ hq _ ih =>
        mp% (notPsubsetFast (cmpRangeFast sp .pr66)) (mp% (cmpRangeFast hp hq) (ih p')))
      (fun hp f1p p' _ hq f1q ih =>
        mp% (cmpRangeFast hp hq) (mp% (cmpRangeFast f1p f1q) (ih p')))
      (fun _ _ _ _ _ _ _ _ => .disjoint) (fun _ _ _ _ _ _ _ _ _ => .disjoint)
      p hq f1q ih)
    (fun hq f1q f2q _ ih p => Part.rec
      (motive := fun _ => Prange → Prange → Prange → (Part → PartRel) → PartRel)
      (fun _ _ _ _ => .straddle)
      (fun sp hp p' _ hq _ _ ih =>
        mp% (notPsubsetFast (cmpRangeFast sp .pr77)) (mp% (cmpRangeFast hp hq) (ih p')))
      (fun _ _ _ _ _ _ _ _ => .disjoint)
      (fun hp f1p f2p p' _ hq f1q f2q ih => mp% (cmpRangeFast hp hq)
        (mp% (cmpRangeFast f1p f1q) (mp% (cmpRangeFast f2p f2q) (ih p'))))
      (fun _ _ _ _ _ _ _ _ _ _ => .disjoint)
      p hq f1q f2q ih)
    (fun hq f1q f2q f3q _ ih p => Part.rec
      (motive := fun _ =>
        Prange → Prange → Prange → Prange → (Part → PartRel) → PartRel)
      (fun _ _ _ _ _ => .straddle)
      (fun sp hp p' _ hq _ _ _ ih =>
        mp% (notPsubsetFast (cmpRangeFast sp .pr88)) (mp% (cmpRangeFast hp hq) (ih p')))
      (fun _ _ _ _ _ _ _ _ _ => .disjoint) (fun _ _ _ _ _ _ _ _ _ _ => .disjoint)
      (fun hp f1p f2p f3p p' _ hq f1q f2q f3q ih => mp% (cmpRangeFast hp hq)
        (mp% (cmpRangeFast f1p f1q) (mp% (cmpRangeFast f2p f2q)
          (mp% (cmpRangeFast f3p f3q) (ih p')))))
      p hq f1q f2q f3q ih)
    q p

/-- `cmpPartFast` is `cmpPart`. -/
theorem cmpPartFast_eq (p q : Part) : cmpPartFast p q = cmpPart p q := by
  have e1 : cmpRangeFast = cmpRange := funext fun r => funext fun r' => cmpRangeFast_eq r r'
  have e2 : meetPrelFast = meetPrel := funext fun c => funext fun c' => meetPrelFast_eq c c'
  have e3 : notPsubsetFast = notPsubset := funext fun c => notPsubsetFast_eq c
  induction q generalizing p with
  | nil => cases p <;> rfl
  | cons sq hq q ih =>
    cases p <;> simp only [cmpPart, ← ih, ← e1, ← e2] <;> rfl
  | cons6 hq f1q q ih =>
    cases p <;> simp only [cmpPart, ← ih, ← e1, ← e2, ← e3] <;> rfl
  | cons7 hq f1q f2q q ih =>
    cases p <;> simp only [cmpPart, ← ih, ← e1, ← e2, ← e3] <;> rfl
  | cons8 hq f1q f2q f3q q ih =>
    cases p <;> simp only [cmpPart, ← ih, ← e1, ← e2, ← e3] <;> rfl

/-- The subset test on parts: `cmpPart p q = .subset`, i.e., every dart that fits `p` fits `q`
(`fitp_cmp`). It is the test of Coq `succeed_by_similarity` (`cmp_part p2 ps = Psubset`) and
of `check_unfit`. -/
noncomputable def subsetPartFast (p q : Part) : Bool :=
  PartRel.rec (motive := fun _ => Bool) false false true (cmpPartFast p q)

/-- `subsetPartFast p q` decides `cmpPart p q = .subset`. -/
theorem subsetPartFast_eq (p q : Part) :
    subsetPartFast p q = decide (cmpPart p q = .subset) := by
  unfold subsetPartFast
  rw [cmpPartFast_eq]
  cases cmpPart p q <;> rfl

/-- Kernel-fast `meetPart` (Coq `meet_part`): `Part.rec` on `q`, then a `Part.rec` on `p` with
closed minor premises. -/
noncomputable def meetPartFast (p q : Part) : Part :=
  Part.rec (motive := fun _ => Part → Part)
    (fun p => p)
    (fun sq hq _ ih p => Part.rec
      (motive := fun _ => Prange → Prange → (Part → Part) → Part)
      (fun _ _ _ => .nil)
      (fun sp hp p' _ sq hq ih => .cons (meetRangeFast sp sq) (meetRangeFast hp hq) (ih p'))
      (fun hp f1 p' _ _ hq ih => .cons6 (meetRangeFast hp hq) f1 (ih p'))
      (fun hp f1 f2 p' _ _ hq ih => .cons7 (meetRangeFast hp hq) f1 f2 (ih p'))
      (fun hp f1 f2 f3 p' _ _ hq ih => .cons8 (meetRangeFast hp hq) f1 f2 f3 (ih p'))
      p sq hq ih)
    (fun hq f1q _ ih p => Part.rec
      (motive := fun _ => Prange → Prange → (Part → Part) → Part)
      (fun _ _ _ => .nil)
      (fun _ hp p' _ hq f1q ih => .cons6 (meetRangeFast hp hq) f1q (ih p'))
      (fun hp f1p p' _ hq f1q ih => .cons6 (meetRangeFast hp hq) (meetRangeFast f1p f1q) (ih p'))
      (fun h f1 f2 p' _ _ _ _ => .cons7 h f1 f2 p')
      (fun h f1 f2 f3 p' _ _ _ _ => .cons8 h f1 f2 f3 p')
      p hq f1q ih)
    (fun hq f1q f2q _ ih p => Part.rec
      (motive := fun _ => Prange → Prange → Prange → (Part → Part) → Part)
      (fun _ _ _ _ => .nil)
      (fun _ hp p' _ hq f1q f2q ih => .cons7 (meetRangeFast hp hq) f1q f2q (ih p'))
      (fun h f1 p' _ _ _ _ _ => .cons6 h f1 p')
      (fun hp f1p f2p p' _ hq f1q f2q ih =>
        .cons7 (meetRangeFast hp hq) (meetRangeFast f1p f1q) (meetRangeFast f2p f2q) (ih p'))
      (fun h f1 f2 f3 p' _ _ _ _ _ => .cons8 h f1 f2 f3 p')
      p hq f1q f2q ih)
    (fun hq f1q f2q f3q _ ih p => Part.rec
      (motive := fun _ => Prange → Prange → Prange → Prange → (Part → Part) → Part)
      (fun _ _ _ _ _ => .nil)
      (fun _ hp p' _ hq f1q f2q f3q ih => .cons8 (meetRangeFast hp hq) f1q f2q f3q (ih p'))
      (fun h f1 p' _ _ _ _ _ _ => .cons6 h f1 p')
      (fun h f1 f2 p' _ _ _ _ _ _ => .cons7 h f1 f2 p')
      (fun hp f1p f2p f3p p' _ hq f1q f2q f3q ih => .cons8 (meetRangeFast hp hq)
        (meetRangeFast f1p f1q) (meetRangeFast f2p f2q) (meetRangeFast f3p f3q) (ih p'))
      p hq f1q f2q f3q ih)
    q p

/-- `meetPartFast` is `meetPart`. -/
theorem meetPartFast_eq (p q : Part) : meetPartFast p q = meetPart p q := by
  have e1 : meetRangeFast = meetRange := funext fun r => funext fun r' => meetRangeFast_eq r r'
  induction q generalizing p with
  | nil => cases p <;> rfl
  | cons sq hq q ih =>
    cases p <;> simp only [meetPart, ← ih, ← e1] <;> rfl
  | cons6 hq f1q q ih =>
    cases p <;> simp only [meetPart, ← ih, ← e1] <;> rfl
  | cons7 hq f1q f2q q ih =>
    cases p <;> simp only [meetPart, ← ih, ← e1] <;> rfl
  | cons8 hq f1q f2q f3q q ih =>
    cases p <;> simp only [meetPart, ← ih, ← e1] <;> rfl

end FourColor
