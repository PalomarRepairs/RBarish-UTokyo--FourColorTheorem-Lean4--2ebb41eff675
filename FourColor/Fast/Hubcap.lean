/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Hubcap
import FourColor.Fast.Part

/-!
# Kernel-fast hubcap checks

Fast versions, for evaluation by the kernel (`decide +kernel`), of the hubcap checks of
`FourColor.Hubcap` (Coq `hubcap.v`) and of the similarity test of Coq `present.v`, each with a
theorem `fooFast_eq` stating that it is equal to the faithful definition (for all arguments,
including the reducibility check `redp`, which the checks take as an argument). The checks that
take a drule fork `rf : DruleFork nhub` in `FourColor.Hubcap` take its rule lists
`rs = rf.sourceDrules` and `rt = rf.targetDrules` (and the hub size `nhub`) here.

## Definitions (faithful name → fast name, each with its theorem `_eq`)

* discharge rules: `List.length`, `sortDrulesRec`, `sortDrules` → `lengthFast`,
  `sortDrulesRecFast`, `sortDrulesFast`;
* the subset test `cmpPart p q = .subset` → `subsetPartFast'` (it stops at the first range that
  is not a subset; `subsetPartFast'_iff`), and `checkUnfit` → `checkUnfitFast`;
* bounds: `checkDbound1Rec`, `checkDbound1`, `checkDbound2Rec`, `checkDbound2`,
  `check2Dbound2Rec`, `check2Dbound2` → `checkDbound1RecFast`, ..., `check2Dbound2Fast`;
* the hubcap: `hubcapRot`, `hubSubn`, `hubcapFit` → `hubcapRotFast`, `hubSubnFast`,
  `hubcapFitFast`; `incrNth`, `tallyHubcap`, `dboundK`, `hubcapCoverRec`, `hubcapCover` →
  `incrNthFast`, `tallyHubcapFast`, `dboundKFast`, `hubcapCoverRecFast`, `hubcapCoverFast`;
* the side condition of Coq `succeed_by_similarity` (`similarCheck`): `similarCheckFast`.

## Style

As in `FourColor.Fast.Part`: recursors only (no `match`, `ite`, `Decidable`, `brecOn` or
typeclass arithmetic in the loops), `Bool.rec` for the tests, `Nat.beq`/`Nat.ble`/`Nat.blt` and
`Nat.add`/`Nat.sub` for the arithmetic, and the fast part operations of `FourColor.Fast.Part`.
All definitions are `noncomputable`.
-/

namespace FourColor

/-- `bif% c a b` is `if c then a else b` for booleans, as one `Bool.rec`. -/
local macro "bif% " c:term:max a:term:max b:term:max : term =>
  `(Bool.rec (motive := fun _ => Bool) $b $a $c)

/-- `Bool.rec` is `if`. -/
private theorem bool_rec_eq_ite {α : Sort _} (c : Bool) (a b : α) :
    Bool.rec (motive := fun _ => α) b a c = if c = true then a else b := by
  cases c <;> rfl

/-- `a && b` as an `if`. -/
private theorem and_eq_ite (a b : Bool) : (a && b) = if a = true then b else false := by
  cases a <;> rfl

/-- `a || b` as an `if`. -/
private theorem or_eq_ite (a b : Bool) : (a || b) = if a = true then true else b := by
  cases a <;> rfl

/-- `Bool.rec` with a `false` first branch is `&&`. -/
private theorem bool_rec_false_eq_and (a b : Bool) :
    Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

/-- `Bool.rec` with a `false` second branch is `!c && x`. -/
private theorem bool_rec_false_eq_not_and (c x : Bool) :
    Bool.rec (motive := fun _ => Bool) x false c = (!c && x) := by
  cases c <;> rfl

/-- `Nat.ble` decides `≤`. -/
private theorem nat_ble_eq (a b : ℕ) : Nat.ble a b = decide (a ≤ b) := by
  rw [Bool.eq_iff_iff, Nat.ble_eq, decide_eq_true_iff]

/-- `Nat.blt` decides `<`. -/
private theorem nat_blt_eq (a b : ℕ) : Nat.blt a b = decide (a < b) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

/-! ### Discharge rules -/

/-- Kernel-fast `List.length`. -/
noncomputable def lengthFast {α : Type} (l : List α) : ℕ :=
  List.rec (motive := fun _ => ℕ) Nat.zero (fun _ _ n => Nat.succ n) l

/-- `lengthFast` is `List.length`. -/
theorem lengthFast_eq {α : Type} (l : List α) : lengthFast l = l.length := by
  induction l with
  | nil => rfl
  | cons _ l ih => exact congrArg Nat.succ ih

/-- Kernel-fast `sortDrulesRec` (Coq `sort_drules_rec`). -/
noncomputable def sortDrulesRecFast (p : Part) (n : ℕ) (rs r : Drules) : SortDrulesResult :=
  List.rec (motive := fun _ => Part → ℕ → Drules → SortDrulesResult)
    (fun _ n rs => ⟨n, rs⟩)
    (fun p' _ ih p n rs => PartRel.rec (motive := fun _ => SortDrulesResult)
      (ih p n rs) (ih p n (p' :: rs)) (ih p (Nat.succ n) rs) (cmpPartFast p p'))
    r p n rs

/-- `sortDrulesRecFast` is `sortDrulesRec`. -/
theorem sortDrulesRecFast_eq (p : Part) (n : ℕ) (rs r : Drules) :
    sortDrulesRecFast p n rs r = sortDrulesRec p n rs r := by
  induction r generalizing n rs with
  | nil => rfl
  | cons p' r ih =>
    show PartRel.rec (motive := fun _ => SortDrulesResult) (sortDrulesRecFast p n rs r)
      (sortDrulesRecFast p n (p' :: rs) r) (sortDrulesRecFast p (Nat.succ n) rs r)
      (cmpPartFast p p') = _
    rw [cmpPartFast_eq, sortDrulesRec]
    cases cmpPart p p' <;> simp only [ih]

/-- Kernel-fast `sortDrules` (Coq `sort_drules`). -/
noncomputable def sortDrulesFast (p : Part) (r : Drules) : SortDrulesResult :=
  sortDrulesRecFast p Nat.zero [] r

/-- `sortDrulesFast` is `sortDrules`. -/
theorem sortDrulesFast_eq (p : Part) (r : Drules) : sortDrulesFast p r = sortDrules p r :=
  sortDrulesRecFast_eq p 0 [] r

/-! ### The subset test and `checkUnfit` -/

/-- `cmpRange r r' = .subset`, as a two-level table (a row of `subRangeFast`). -/
noncomputable def subRangeFast (r r' : Prange) : Bool :=
  PartRel.rec (motive := fun _ => Bool) false false true (cmpRangeFast r r')

/-- `subRangeFast r r'` decides `cmpRange r r' = .subset`. -/
theorem subRangeFast_iff (r r' : Prange) : subRangeFast r r' = true ↔ cmpRange r r' = .subset := by
  unfold subRangeFast
  rw [cmpRangeFast_eq]
  cases cmpRange r r' <;> simp

/-- `meetPrel c c'` is a subset exactly when `c` and `c'` are. -/
private theorem meetPrel_eq_subset (c c' : PartRel) :
    meetPrel c c' = .subset ↔ c = .subset ∧ c' = .subset := by
  cases c <;> cases c' <;> simp [meetPrel, notPsubset]

/-- `notPsubset c` is never a subset. -/
private theorem notPsubset_ne_subset (c : PartRel) : notPsubset c ≠ .subset := by
  cases c <;> simp [notPsubset]

/-- The subset test `cmpPart p q = .subset` (`subsetPartFast'_iff`), stopping at the first range
of `p` that is not a subset of the range of `q` it is compared with (`cmpPart` computes the full
three-way comparison). -/
noncomputable def subsetPartFast' (p q : Part) : Bool :=
  Part.rec (motive := fun _ => Part → Bool)
    (fun _ => true)
    (fun sq hq _ ih p => Part.rec (motive := fun _ => Prange → Prange → (Part → Bool) → Bool)
      (fun _ _ _ => false)
      (fun sp hp p' _ sq hq ih => bif% (subRangeFast sp sq) (bif% (subRangeFast hp hq) (ih p') false)
        false)
      (fun hp _ p' _ sq hq ih =>
        bif% (subRangeFast .pr66 sq) (bif% (subRangeFast hp hq) (ih p') false) false)
      (fun hp _ _ p' _ sq hq ih =>
        bif% (subRangeFast .pr77 sq) (bif% (subRangeFast hp hq) (ih p') false) false)
      (fun hp _ _ _ p' _ sq hq ih =>
        bif% (subRangeFast .pr88 sq) (bif% (subRangeFast hp hq) (ih p') false) false)
      p sq hq ih)
    (fun hq f1q _ ih p => Part.rec (motive := fun _ => Prange → Prange → (Part → Bool) → Bool)
      (fun _ _ _ => false)
      (fun _ _ _ _ _ _ _ => false)
      (fun hp f1p p' _ hq f1q ih =>
        bif% (subRangeFast hp hq) (bif% (subRangeFast f1p f1q) (ih p') false) false)
      (fun _ _ _ _ _ _ _ _ => false) (fun _ _ _ _ _ _ _ _ _ => false)
      p hq f1q ih)
    (fun hq f1q f2q _ ih p => Part.rec
      (motive := fun _ => Prange → Prange → Prange → (Part → Bool) → Bool)
      (fun _ _ _ _ => false)
      (fun _ _ _ _ _ _ _ _ => false)
      (fun _ _ _ _ _ _ _ _ => false)
      (fun hp f1p f2p p' _ hq f1q f2q ih => bif% (subRangeFast hp hq)
        (bif% (subRangeFast f1p f1q) (bif% (subRangeFast f2p f2q) (ih p') false) false) false)
      (fun _ _ _ _ _ _ _ _ _ _ => false)
      p hq f1q f2q ih)
    (fun hq f1q f2q f3q _ ih p => Part.rec
      (motive := fun _ => Prange → Prange → Prange → Prange → (Part → Bool) → Bool)
      (fun _ _ _ _ _ => false)
      (fun _ _ _ _ _ _ _ _ _ => false)
      (fun _ _ _ _ _ _ _ _ _ => false)
      (fun _ _ _ _ _ _ _ _ _ _ => false)
      (fun hp f1p f2p f3p p' _ hq f1q f2q f3q ih => bif% (subRangeFast hp hq)
        (bif% (subRangeFast f1p f1q) (bif% (subRangeFast f2p f2q)
          (bif% (subRangeFast f3p f3q) (ih p') false) false) false) false)
      p hq f1q f2q f3q ih)
    q p

/-- `subsetPartFast' p q` decides `cmpPart p q = .subset`. -/
theorem subsetPartFast'_iff (p q : Part) : subsetPartFast' p q = true ↔ cmpPart p q = .subset := by
  induction q generalizing p with
  | nil => cases p <;> simp [subsetPartFast', cmpPart]
  | cons sq hq q ih =>
    cases p with
    | nil => simp [subsetPartFast', cmpPart]
    | cons sp hp p =>
      have := ih p
      simp only [subsetPartFast'] at this ⊢
      rw [cmpPart, meetPrel_eq_subset, meetPrel_eq_subset, ← subRangeFast_iff, ← subRangeFast_iff,
        ← this]
      cases subRangeFast sp sq <;> cases subRangeFast hp hq <;> simp
    | cons6 hp f1 p =>
      have := ih p
      simp only [subsetPartFast'] at this ⊢
      rw [cmpPart, meetPrel_eq_subset, meetPrel_eq_subset, ← subRangeFast_iff, ← subRangeFast_iff,
        ← this]
      cases subRangeFast .pr66 sq <;> cases subRangeFast hp hq <;> simp
    | cons7 hp f1 f2 p =>
      have := ih p
      simp only [subsetPartFast'] at this ⊢
      rw [cmpPart, meetPrel_eq_subset, meetPrel_eq_subset, ← subRangeFast_iff, ← subRangeFast_iff,
        ← this]
      cases subRangeFast .pr77 sq <;> cases subRangeFast hp hq <;> simp
    | cons8 hp f1 f2 f3 p =>
      have := ih p
      simp only [subsetPartFast'] at this ⊢
      rw [cmpPart, meetPrel_eq_subset, meetPrel_eq_subset, ← subRangeFast_iff, ← subRangeFast_iff,
        ← this]
      cases subRangeFast .pr88 sq <;> cases subRangeFast hp hq <;> simp
  | cons6 hq f1q q ih =>
    cases p with
    | nil => simp [subsetPartFast', cmpPart]
    | cons sp hp p =>
      simp only [subsetPartFast', cmpPart, Bool.false_eq_true, false_iff, meetPrel_eq_subset]
      exact fun h => notPsubset_ne_subset _ h.1
    | cons6 hp f1p p =>
      have := ih p
      simp only [subsetPartFast'] at this ⊢
      rw [cmpPart, meetPrel_eq_subset, meetPrel_eq_subset, ← subRangeFast_iff, ← subRangeFast_iff,
        ← this]
      cases subRangeFast hp hq <;> cases subRangeFast f1p f1q <;> simp
    | cons7 => simp [subsetPartFast', cmpPart]
    | cons8 => simp [subsetPartFast', cmpPart]
  | cons7 hq f1q f2q q ih =>
    cases p with
    | nil => simp [subsetPartFast', cmpPart]
    | cons sp hp p =>
      simp only [subsetPartFast', cmpPart, Bool.false_eq_true, false_iff, meetPrel_eq_subset]
      exact fun h => notPsubset_ne_subset _ h.1
    | cons6 => simp [subsetPartFast', cmpPart]
    | cons7 hp f1p f2p p =>
      have := ih p
      simp only [subsetPartFast'] at this ⊢
      rw [cmpPart, meetPrel_eq_subset, meetPrel_eq_subset, meetPrel_eq_subset, ← subRangeFast_iff,
        ← subRangeFast_iff, ← subRangeFast_iff, ← this]
      cases subRangeFast hp hq <;> cases subRangeFast f1p f1q <;> cases subRangeFast f2p f2q <;>
        simp
    | cons8 => simp [subsetPartFast', cmpPart]
  | cons8 hq f1q f2q f3q q ih =>
    cases p with
    | nil => simp [subsetPartFast', cmpPart]
    | cons sp hp p =>
      simp only [subsetPartFast', cmpPart, Bool.false_eq_true, false_iff, meetPrel_eq_subset]
      exact fun h => notPsubset_ne_subset _ h.1
    | cons6 => simp [subsetPartFast', cmpPart]
    | cons7 => simp [subsetPartFast', cmpPart]
    | cons8 hp f1p f2p f3p p =>
      have := ih p
      simp only [subsetPartFast'] at this ⊢
      rw [cmpPart, meetPrel_eq_subset, meetPrel_eq_subset, meetPrel_eq_subset, meetPrel_eq_subset,
        ← subRangeFast_iff, ← subRangeFast_iff, ← subRangeFast_iff, ← subRangeFast_iff, ← this]
      cases subRangeFast hp hq <;> cases subRangeFast f1p f1q <;> cases subRangeFast f2p f2q <;>
        cases subRangeFast f3p f3q <;> simp

/-- `subsetPartFast' p q` is `decide (cmpPart p q = .subset)`. -/
theorem subsetPartFast'_eq (p q : Part) : subsetPartFast' p q = decide (cmpPart p q = .subset) := by
  rw [Bool.eq_iff_iff, subsetPartFast'_iff, decide_eq_true_iff]

/-- Kernel-fast `checkUnfit` (Coq `check_unfit`). -/
noncomputable def checkUnfitFast (p : Part) (ru : Drules) : Bool :=
  List.rec (motive := fun _ => Part → Bool) (fun _ => false)
    (fun r _ ih p => bif% (subsetPartFast' p r) true (ih p)) ru p

/-- `checkUnfitFast` is `checkUnfit`. -/
theorem checkUnfitFast_eq (p : Part) (ru : Drules) : checkUnfitFast p ru = checkUnfit p ru := by
  induction ru with
  | nil => rfl
  | cons r ru ih =>
    show Bool.rec (motive := fun _ => Bool) (checkUnfitFast p ru) true (subsetPartFast' p r) = _
    rw [ih, checkUnfit, subsetPartFast'_eq]
    cases h : cmpPart p r <;> simp

/-! ### Source bounds -/

/-- The work of `checkDbound1RecFast` (at fuel `m + 1`) for its first rule `r`, the recursive
check `rec` being `checkDbound1RecFast redp m`: `redp` holds on the part refined by `r` when the
bound is reached, else the refined part satisfies the recursive check. -/
noncomputable def checkDbound1HeadFast (redp : Part → Bool) (rec : Part → Drules → ℕ → Bool)
    (p r : Part) (rs' : Drules) (ns : ℕ) : Bool :=
  (fun p' => SortDrulesResult.rec (motive := fun _ => Bool) (fun dns rs'' =>
      Nat.rec (motive := fun _ => Bool) (redp p') (fun ns' _ => rec p' rs'' ns') (Nat.sub ns dns))
    (sortDrulesFast p' rs')) (meetPartFast p r)

/-- Kernel-fast `checkDbound1Rec` (Coq `check_dbound1_rec`): `Nat.rec` on the fuel `m`. -/
noncomputable def checkDbound1RecFast (redp : Part → Bool) (m : ℕ) : Part → Drules → ℕ → Bool :=
  Nat.rec (motive := fun _ => Part → Drules → ℕ → Bool) (fun _ _ _ => false)
    (fun _ ih p rs ns => List.rec (motive := fun _ => Bool) true
      (fun r rs' _ => bif% (Nat.blt (lengthFast rs') ns) true
        (bif% (checkDbound1HeadFast redp ih p r rs' ns) (ih p rs' ns) false))
      rs)
    m

/-- One step of `checkDbound1RecFast` (for splitting a check into several declarations). -/
theorem checkDbound1RecFast_succ_cons (redp : Part → Bool) (m : ℕ) (p r : Part) (rs' : Drules)
    (ns : ℕ) :
    checkDbound1RecFast redp (m + 1) p (r :: rs') ns =
      (Nat.blt (lengthFast rs') ns ||
        (checkDbound1HeadFast redp (checkDbound1RecFast redp m) p r rs' ns &&
          checkDbound1RecFast redp m p rs' ns)) := rfl

/-- `checkDbound1RecFast` (fuel first) is `checkDbound1Rec`. -/
theorem checkDbound1RecFast_eq (redp : Part → Bool) (m : ℕ) (p : Part) (rs : Drules) (ns : ℕ) :
    checkDbound1RecFast redp m p rs ns = checkDbound1Rec redp p rs ns m := by
  induction m generalizing p rs ns with
  | zero => rfl
  | succ m ih =>
    cases rs with
    | nil => rfl
    | cons r rs =>
      rw [checkDbound1RecFast_succ_cons, checkDbound1HeadFast, checkDbound1Rec]
      simp only [lengthFast_eq, nat_blt_eq, meetPartFast_eq, sortDrulesFast_eq, ih, and_eq_ite,
        or_eq_ite, decide_eq_true_eq, Nat.sub_eq]
      by_cases hlt : rs.length < ns
      · simp only [hlt, ite_true]
      · simp only [hlt, ite_false]
        rcases sortDrules (meetPart p r) rs with ⟨dns, rs''⟩
        simp only
        rcases ns - dns with _ | ns' <;> rfl

/-- Kernel-fast `checkDbound1` (Coq `check_dbound1`), for the source rules `rs` of a fork. -/
noncomputable def checkDbound1Fast (redp : Part → Bool) (rs : Drules) (p : Part) (ns : ℕ) : Bool :=
  checkDbound1RecFast redp (Nat.succ (lengthFast rs)) p rs ns

/-- `checkDbound1Fast` on the source rules of a fork is `checkDbound1`. -/
theorem checkDbound1Fast_eq {nhub : ℕ} (redp : Part → Bool) (rf : DruleFork nhub) (p : Part)
    (ns : ℕ) : checkDbound1Fast redp rf.sourceDrules p ns = checkDbound1 redp rf p ns := by
  rw [checkDbound1Fast, checkDbound1RecFast_eq, lengthFast_eq]
  rfl

/-! ### Single target bounds -/

/-- The work of `checkDbound2RecFast` (at fuel `m + 1`) for its first target rule `r`, the
recursive check `rec` being `checkDbound2RecFast redp m`: the part refined by `r` implies an
excluded rule, or `redp` holds on it when the bound is reached, or it satisfies the recursive
check. -/
noncomputable def checkDbound2HeadFast (redp : Part → Bool)
    (rec : Part → Drules → Drules → Drules → ℕ → Bool) (p r : Part) (rt' rs ru : Drules) (nt : ℕ) :
    Bool :=
  (fun p' => bif% (checkUnfitFast p' ru) true
      (SortDrulesResult.rec (motive := fun _ => Bool) (fun dnt rt'' =>
        SortDrulesResult.rec (motive := fun _ => Bool) (fun dns rs' =>
          Nat.rec (motive := fun _ => Bool) (redp p') (fun nt' _ => rec p' rt'' rs' ru nt')
            (Nat.sub (Nat.add dns nt) dnt))
          (sortDrulesFast p' rs))
        (sortDrulesFast p' rt'))) (meetPartFast p r)

/-- Kernel-fast `checkDbound2Rec` (Coq `check_dbound2_rec`): `Nat.rec` on the fuel `m`. -/
noncomputable def checkDbound2RecFast (redp : Part → Bool) (m : ℕ) :
    Part → Drules → Drules → Drules → ℕ → Bool :=
  Nat.rec (motive := fun _ => Part → Drules → Drules → Drules → ℕ → Bool)
    (fun _ _ _ _ _ => false)
    (fun _ ih p rt rs ru nt => List.rec (motive := fun _ => Bool) true
      (fun r rt' _ => bif% (Nat.blt (lengthFast rt') nt) true
        (bif% (checkDbound2HeadFast redp ih p r rt' rs ru nt) (ih p rt' rs (r :: ru) nt) false))
      rt)
    m

/-- One step of `checkDbound2RecFast` (for splitting a check into several declarations). -/
theorem checkDbound2RecFast_succ_cons (redp : Part → Bool) (m : ℕ) (p r : Part)
    (rt' rs ru : Drules) (nt : ℕ) :
    checkDbound2RecFast redp (m + 1) p (r :: rt') rs ru nt =
      (Nat.blt (lengthFast rt') nt ||
        (checkDbound2HeadFast redp (checkDbound2RecFast redp m) p r rt' rs ru nt &&
          checkDbound2RecFast redp m p rt' rs (r :: ru) nt)) := rfl

/-- `checkDbound2RecFast` (fuel first) is `checkDbound2Rec`. -/
theorem checkDbound2RecFast_eq (redp : Part → Bool) (m : ℕ) (p : Part) (rt rs ru : Drules)
    (nt : ℕ) : checkDbound2RecFast redp m p rt rs ru nt = checkDbound2Rec redp p rt rs ru nt m := by
  induction m generalizing p rt rs ru nt with
  | zero => rfl
  | succ m ih =>
    cases rt with
    | nil => rfl
    | cons r rt =>
      rw [checkDbound2RecFast_succ_cons, checkDbound2HeadFast, checkDbound2Rec]
      simp only [lengthFast_eq, nat_blt_eq, meetPartFast_eq, checkUnfitFast_eq, sortDrulesFast_eq,
        ih, bool_rec_eq_ite, and_eq_ite, or_eq_ite, decide_eq_true_eq, Nat.sub_eq, Nat.add_eq]
      by_cases hlt : rt.length < nt
      · simp only [hlt, ite_true]
      · simp only [hlt, ite_false]
        by_cases hu : checkUnfit (meetPart p r) ru = true
        · simp only [hu, ite_true]
        · simp only [hu]
          rcases sortDrules (meetPart p r) rt with ⟨dnt, rt''⟩
          rcases sortDrules (meetPart p r) rs with ⟨dns, rs'⟩
          simp only
          rcases dns + nt - dnt with _ | nt' <;> rfl

/-- Kernel-fast `checkDbound2` (Coq `check_dbound2`), for the source and target rules `rs`, `rt`
of a fork. -/
noncomputable def checkDbound2Fast (redp : Part → Bool) (rs rt : Drules) (p : Part) (b : ℤ) :
    Bool :=
  SortDrulesResult.rec (motive := fun _ => Bool) (fun dnt rt' =>
    SortDrulesResult.rec (motive := fun _ => Bool) (fun dns rs' =>
      Int.rec (motive := fun _ => Bool)
        (fun nt => checkDbound2RecFast redp (Nat.succ (Nat.succ (lengthFast rt'))) p rt' rs' [] nt)
        (fun _ => false) (Int.add (Int.sub (Int.ofNat dns) (Int.ofNat dnt)) b))
      (sortDrulesFast p rs))
    (sortDrulesFast p rt)

/-- `checkDbound2Fast` on the rules of a fork is `checkDbound2`. -/
theorem checkDbound2Fast_eq {nhub : ℕ} (redp : Part → Bool) (rf : DruleFork nhub) (p : Part)
    (b : ℤ) : checkDbound2Fast redp rf.sourceDrules rf.targetDrules p b = checkDbound2 redp rf p b := by
  rw [checkDbound2Fast, checkDbound2, sortDrulesFast_eq, sortDrulesFast_eq]
  rcases sortDrules p rf.targetDrules with ⟨dnt, rt'⟩
  rcases sortDrules p rf.sourceDrules with ⟨dns, rs'⟩
  simp only
  show Int.rec (motive := fun _ => Bool) _ _ ((dns : ℤ) - (dnt : ℤ) + b) = _
  rcases (dns : ℤ) - (dnt : ℤ) + b with nt | _
  · simp only [checkDbound2RecFast_eq, lengthFast_eq]
  · rfl

/-! ### Dual target bounds -/

/-- The work of `check2Dbound2RecFast` (at fuel `m + 1`) for its first target rule `r` of the
first part, the recursive check `rec` being `check2Dbound2RecFast nhub redp m`: the part refined
by `r` (or its rotation) implies an excluded rule, or `redp` holds on it when the bound is
reached, or it satisfies the recursive check. -/
noncomputable def check2Dbound2HeadFast (redp : Part → Bool)
    (rec : Part → Part → Drules → Drules → Drules → Drules → Drules → Drules → ℕ → ℕ → Bool)
    (p1 r : Part) (rt1' rs1 ru1 rt2 rs2 ru2 : Drules) (i nt : ℕ) : Bool :=
  (fun p1' => (fun p2' =>
    bif% (bif% (checkUnfitFast p1' ru1) true (checkUnfitFast p2' ru2)) true
      (SortDrulesResult.rec (motive := fun _ => Bool) (fun dnt1 rt1'' =>
        SortDrulesResult.rec (motive := fun _ => Bool) (fun dns1 rs1' =>
          SortDrulesResult.rec (motive := fun _ => Bool) (fun dnt2 rt2' =>
            SortDrulesResult.rec (motive := fun _ => Bool) (fun dns2 rs2' =>
              Nat.rec (motive := fun _ => Bool) (redp p1')
                (fun nt' _ => rec p1' p2' rt1'' rs1' ru1 rt2' rs2' ru2 i nt')
                (Nat.sub (Nat.add dns1 (Nat.add dns2 nt)) (Nat.add dnt1 dnt2)))
              (sortDrulesFast p2' rs2))
            (sortDrulesFast p2' rt2))
          (sortDrulesFast p1' rs1))
        (sortDrulesFast p1' rt1')))
    (rotPartFast i p1')) (meetPartFast p1 r)

/-- Kernel-fast `check2Dbound2Rec` (Coq `check_2dbound2_rec`): `Nat.rec` on the fuel `m`. -/
noncomputable def check2Dbound2RecFast (nhub : ℕ) (redp : Part → Bool) (m : ℕ) :
    Part → Part → Drules → Drules → Drules → Drules → Drules → Drules → ℕ → ℕ → Bool :=
  Nat.rec (motive := fun _ => Part → Part → Drules → Drules → Drules → Drules → Drules → Drules →
      ℕ → ℕ → Bool)
    (fun _ _ _ _ _ _ _ _ _ _ => false)
    (fun _ ih p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i nt => List.rec (motive := fun _ => Bool)
      (List.rec (motive := fun _ => Bool) true
        (fun _ _ _ => ih p2 p1 rt2 rs2 ru2 rt1 rs1 ru1 (Nat.sub nhub i) nt) rt2)
      (fun r rt1' _ =>
        bif% (Nat.blt (Nat.add (lengthFast rt1') (lengthFast rt2)) nt) true
        (bif% (check2Dbound2HeadFast redp ih p1 r rt1' rs1 ru1 rt2 rs2 ru2 i nt)
          (ih p1 p2 rt1' rs1 (r :: ru1) rt2 rs2 ru2 i nt) false))
      rt1)
    m

/-- One step of `check2Dbound2RecFast` (for splitting a check into several declarations). -/
theorem check2Dbound2RecFast_succ_cons (nhub : ℕ) (redp : Part → Bool) (m : ℕ) (p1 p2 r : Part)
    (rt1' rs1 ru1 rt2 rs2 ru2 : Drules) (i nt : ℕ) :
    check2Dbound2RecFast nhub redp (m + 1) p1 p2 (r :: rt1') rs1 ru1 rt2 rs2 ru2 i nt =
      (Nat.blt (Nat.add (lengthFast rt1') (lengthFast rt2)) nt ||
        (check2Dbound2HeadFast redp (check2Dbound2RecFast nhub redp m) p1 r rt1' rs1 ru1 rt2 rs2
            ru2 i nt &&
          check2Dbound2RecFast nhub redp m p1 p2 rt1' rs1 (r :: ru1) rt2 rs2 ru2 i nt)) := rfl

/-- One step of `check2Dbound2RecFast` when the first part has no target rule left: the roles
of the two parts are swapped. -/
theorem check2Dbound2RecFast_succ_nil_cons (nhub : ℕ) (redp : Part → Bool) (m : ℕ) (p1 p2 r : Part)
    (rs1 ru1 rt2' rs2 ru2 : Drules) (i nt : ℕ) :
    check2Dbound2RecFast nhub redp (m + 1) p1 p2 [] rs1 ru1 (r :: rt2') rs2 ru2 i nt =
      check2Dbound2RecFast nhub redp m p2 p1 (r :: rt2') rs2 ru2 [] rs1 ru1 (Nat.sub nhub i) nt :=
  rfl

/-- `check2Dbound2RecFast` (fuel first) is `check2Dbound2Rec`. -/
theorem check2Dbound2RecFast_eq (nhub : ℕ) (redp : Part → Bool) (m : ℕ) (p1 p2 : Part)
    (rt1 rs1 ru1 rt2 rs2 ru2 : Drules) (i nt : ℕ) :
    check2Dbound2RecFast nhub redp m p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i nt =
      check2Dbound2Rec nhub redp p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i nt m := by
  induction m generalizing p1 p2 rt1 rs1 ru1 rt2 rs2 ru2 i nt with
  | zero => rfl
  | succ m ih =>
    cases rt1 with
    | nil =>
      cases rt2 with
      | nil => rfl
      | cons r rt2 =>
        rw [check2Dbound2Rec]
        exact ih _ _ _ _ _ _ _ _ _ _
    | cons r rt1 =>
      rw [check2Dbound2RecFast_succ_cons, check2Dbound2HeadFast, check2Dbound2Rec]
      simp only [lengthFast_eq, meetPartFast_eq, rotPartFast_eq, checkUnfitFast_eq,
        sortDrulesFast_eq, ih, bool_rec_eq_ite, and_eq_ite, or_eq_ite, nat_blt_eq,
        decide_eq_true_eq, Nat.sub_eq, Nat.add_eq]
      by_cases hlt : rt1.length + rt2.length < nt
      · simp only [hlt, ite_true]
      · simp only [hlt, ite_false]
        by_cases hu : (if checkUnfit (meetPart p1 r) ru1 = true then true
            else checkUnfit (rotPart i (meetPart p1 r)) ru2) = true
        · simp only [hu, ite_true]
        · simp only [hu]
          rcases sortDrules (meetPart p1 r) rt1 with ⟨dnt1, rt1''⟩
          rcases sortDrules (meetPart p1 r) rs1 with ⟨dns1, rs1'⟩
          rcases sortDrules (rotPart i (meetPart p1 r)) rt2 with ⟨dnt2, rt2'⟩
          rcases sortDrules (rotPart i (meetPart p1 r)) rs2 with ⟨dns2, rs2'⟩
          simp only
          rcases dns1 + (dns2 + nt) - (dnt1 + dnt2) with _ | nt' <;> rfl

/-- Kernel-fast `check2Dbound2` (Coq `check_2dbound2`), for the source and target rules `rs`,
`rt` of a fork for hub size `nhub`. -/
noncomputable def check2Dbound2Fast (nhub : ℕ) (redp : Part → Bool) (rs rt : Drules) (p1 : Part)
    (i : ℕ) (b : ℤ) : Bool :=
  (fun p2 =>
    SortDrulesResult.rec (motive := fun _ => Bool) (fun dnt1 rt1 =>
      SortDrulesResult.rec (motive := fun _ => Bool) (fun dns1 rs1 =>
        SortDrulesResult.rec (motive := fun _ => Bool) (fun dnt2 rt2 =>
          SortDrulesResult.rec (motive := fun _ => Bool) (fun dns2 rs2 =>
            Int.rec (motive := fun _ => Bool)
              (fun nt => check2Dbound2RecFast nhub redp
                (Nat.add (lengthFast rt1) (Nat.add (lengthFast rt2) (nat_lit 3)))
                p1 p2 rt1 rs1 [] rt2 rs2 [] i nt)
              (fun _ => false)
              (Int.add (Int.sub (Int.ofNat (Nat.add dns1 dns2)) (Int.ofNat (Nat.add dnt1 dnt2)))
                b))
            (sortDrulesFast p2 rs))
          (sortDrulesFast p2 rt))
        (sortDrulesFast p1 rs))
      (sortDrulesFast p1 rt))
    (rotPartFast i p1)

/-- `check2Dbound2Fast` on the rules of a fork is `check2Dbound2`. -/
theorem check2Dbound2Fast_eq {nhub : ℕ} (redp : Part → Bool) (rf : DruleFork nhub) (p1 : Part)
    (i : ℕ) (b : ℤ) :
    check2Dbound2Fast nhub redp rf.sourceDrules rf.targetDrules p1 i b =
      check2Dbound2 redp rf p1 i b := by
  rw [check2Dbound2Fast, check2Dbound2]
  simp only [rotPartFast_eq, sortDrulesFast_eq]
  rcases sortDrules p1 rf.targetDrules with ⟨dnt1, rt1⟩
  rcases sortDrules p1 rf.sourceDrules with ⟨dns1, rs1⟩
  rcases sortDrules (rotPart i p1) rf.targetDrules with ⟨dnt2, rt2⟩
  rcases sortDrules (rotPart i p1) rf.sourceDrules with ⟨dns2, rs2⟩
  simp only
  show Int.rec (motive := fun _ => Bool) _ _
    (((dns1 + dns2 : ℕ) : ℤ) - ((dnt1 + dnt2 : ℕ) : ℤ) + b) = _
  rcases ((dns1 + dns2 : ℕ) : ℤ) - ((dnt1 + dnt2 : ℕ) : ℤ) + b with nt | _
  · simp only [check2Dbound2RecFast_eq, lengthFast_eq]
    rfl
  · rfl

/-- Entry into `checkDbound2RecFast` from `checkDbound2Fast`, given the sorted rule lists (for
splitting a check into several declarations: the hypotheses are closed equations). -/
theorem checkDbound2Fast_of_rec (redp : Part → Bool) (rs rt : Drules) (p : Part) (b : ℤ)
    {dnt dns nt : ℕ} {rt' rs' : Drules}
    (ht1 : (sortDrulesFast p rt).nbForcedDrules = dnt)
    (ht2 : (sortDrulesFast p rt).straddlingDrules = rt')
    (hs1 : (sortDrulesFast p rs).nbForcedDrules = dns)
    (hs2 : (sortDrulesFast p rs).straddlingDrules = rs')
    (hnt : Int.add (Int.sub (Int.ofNat dns) (Int.ofNat dnt)) b = Int.ofNat nt)
    (h : checkDbound2RecFast redp (Nat.succ (Nat.succ (lengthFast rt'))) p rt' rs' [] nt = true) :
    checkDbound2Fast redp rs rt p b = true := by
  have e1 : sortDrulesFast p rt = ⟨dnt, rt'⟩ := by rw [← ht1, ← ht2]
  have e2 : sortDrulesFast p rs = ⟨dns, rs'⟩ := by rw [← hs1, ← hs2]
  rw [checkDbound2Fast, e1, e2]
  simp only
  rw [hnt]
  exact h

/-- Entry into `check2Dbound2RecFast` from `check2Dbound2Fast`, given the sorted rule lists (for
splitting a check into several declarations: the hypotheses are closed equations). -/
theorem check2Dbound2Fast_of_rec (nhub : ℕ) (redp : Part → Bool) (rs rt : Drules) (p1 : Part)
    (i : ℕ) (b : ℤ) {dnt1 dns1 dnt2 dns2 nt : ℕ} {rt1 rs1 rt2 rs2 : Drules}
    (ht11 : (sortDrulesFast p1 rt).nbForcedDrules = dnt1)
    (ht12 : (sortDrulesFast p1 rt).straddlingDrules = rt1)
    (hs11 : (sortDrulesFast p1 rs).nbForcedDrules = dns1)
    (hs12 : (sortDrulesFast p1 rs).straddlingDrules = rs1)
    (ht21 : (sortDrulesFast (rotPartFast i p1) rt).nbForcedDrules = dnt2)
    (ht22 : (sortDrulesFast (rotPartFast i p1) rt).straddlingDrules = rt2)
    (hs21 : (sortDrulesFast (rotPartFast i p1) rs).nbForcedDrules = dns2)
    (hs22 : (sortDrulesFast (rotPartFast i p1) rs).straddlingDrules = rs2)
    (hnt : Int.add (Int.sub (Int.ofNat (Nat.add dns1 dns2)) (Int.ofNat (Nat.add dnt1 dnt2))) b =
      Int.ofNat nt)
    (h : check2Dbound2RecFast nhub redp
      (Nat.add (lengthFast rt1) (Nat.add (lengthFast rt2) (nat_lit 3)))
      p1 (rotPartFast i p1) rt1 rs1 [] rt2 rs2 [] i nt = true) :
    check2Dbound2Fast nhub redp rs rt p1 i b = true := by
  have e1 : sortDrulesFast p1 rt = ⟨dnt1, rt1⟩ := by rw [← ht11, ← ht12]
  have e2 : sortDrulesFast p1 rs = ⟨dns1, rs1⟩ := by rw [← hs11, ← hs12]
  have e3 : sortDrulesFast (rotPartFast i p1) rt = ⟨dnt2, rt2⟩ := by rw [← ht21, ← ht22]
  have e4 : sortDrulesFast (rotPartFast i p1) rs = ⟨dns2, rs2⟩ := by rw [← hs21, ← hs22]
  rw [check2Dbound2Fast]
  simp only
  rw [e1, e2, e3, e4]
  simp only
  rw [hnt]
  exact h

/-! ### Hubcaps -/

/-- Kernel-fast `hubcapRot` (Coq `hubcap_rot`). -/
noncomputable def hubcapRotFast (nhub j : ℕ) (p : Part) : Part :=
  rotPartFast (Nat.rec (motive := fun _ => ℕ) (Nat.sub (Nat.add nhub j) (nat_lit 2))
    (fun j1 _ => Nat.rec (motive := fun _ => ℕ) (Nat.sub (Nat.add nhub j) (nat_lit 2))
      (fun j' _ => j') j1) j) p

/-- `hubcapRotFast` is `hubcapRot`. -/
theorem hubcapRotFast_eq (nhub j : ℕ) (p : Part) : hubcapRotFast nhub j p = hubcapRot nhub j p := by
  show rotPartFast _ p = _
  rw [rotPartFast_eq]
  rcases j with _ | _ | j <;> rfl

/-- Kernel-fast `hubSubn` (Coq `hub_subn`). -/
noncomputable def hubSubnFast (nhub i j : ℕ) : ℕ :=
  Nat.sub (Bool.rec (motive := fun _ => ℕ) (Nat.add i nhub) i (Nat.ble j i)) j

/-- `hubSubnFast` is `hubSubn`. -/
theorem hubSubnFast_eq (nhub i j : ℕ) : hubSubnFast nhub i j = hubSubn nhub i j := by
  rw [hubSubnFast, hubSubn, nat_ble_eq]
  by_cases h : j ≤ i
  · simp only [h, decide_true, ite_true]
    rfl
  · simp only [h, decide_false, ite_false]
    rfl

/-- Kernel-fast `hubcapFit` (Coq `hubcap_fit`), for the source and target rules `rs`, `rt` of a
fork for hub size `nhub`. -/
noncomputable def hubcapFitFast (nhub : ℕ) (redp : Part → Bool) (rs rt : Drules) (p : Part)
    (hc : Hubcap) : Bool :=
  Hubcap.rec (motive := fun _ => Bool) true
    (fun j b _ ih => bif% (checkDbound2Fast redp rs rt (hubcapRotFast nhub j p) b) ih false)
    (fun j1 j2 b _ ih =>
      bif% (check2Dbound2Fast nhub redp rs rt (hubcapRotFast nhub j1 p) (hubSubnFast nhub j2 j1) b)
        ih false)
    hc

/-- `hubcapFitFast` on the rules of a fork is `hubcapFit`. -/
theorem hubcapFitFast_eq {nhub : ℕ} (redp : Part → Bool) (rf : DruleFork nhub) (p : Part)
    (hc : Hubcap) :
    hubcapFitFast nhub redp rf.sourceDrules rf.targetDrules p hc = hubcapFit redp rf p hc := by
  induction hc with
  | nil => rfl
  | cons1 j b hc ih =>
    show Bool.rec (motive := fun _ => Bool) false
      (hubcapFitFast nhub redp rf.sourceDrules rf.targetDrules p hc)
      (checkDbound2Fast redp rf.sourceDrules rf.targetDrules (hubcapRotFast nhub j p) b) = _
    rw [ih, hubcapFit, hubcapRotFast_eq, checkDbound2Fast_eq, bool_rec_eq_ite, and_eq_ite]
  | cons2 j1 j2 b hc ih =>
    show Bool.rec (motive := fun _ => Bool) false
      (hubcapFitFast nhub redp rf.sourceDrules rf.targetDrules p hc)
      (check2Dbound2Fast nhub redp rf.sourceDrules rf.targetDrules (hubcapRotFast nhub j1 p)
        (hubSubnFast nhub j2 j1) b) = _
    rw [ih, hubcapFit, hubcapRotFast_eq, hubSubnFast_eq, check2Dbound2Fast_eq, bool_rec_eq_ite,
      and_eq_ite]

/-! ### Hubcap cover -/

/-- Kernel-fast `List.replicate i 0 ++ [1]`. -/
noncomputable def replicateOneFast (i : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ => List ℕ) [nat_lit 1] (fun _ l => Nat.zero :: l) i

/-- `replicateOneFast i` is `List.replicate i 0 ++ [1]`. -/
theorem replicateOneFast_eq (i : ℕ) : replicateOneFast i = List.replicate i 0 ++ [1] := by
  induction i with
  | zero => rfl
  | succ i ih => rw [List.replicate_succ, List.cons_append, ← ih]; rfl

/-- Kernel-fast `incrNth` (math-comp `incr_nth`). -/
noncomputable def incrNthFast (v : List ℕ) (i : ℕ) : List ℕ :=
  List.rec (motive := fun _ => ℕ → List ℕ) (fun i => replicateOneFast i)
    (fun n v' ih i => Nat.rec (motive := fun _ => List ℕ) (Nat.succ n :: v')
      (fun i' _ => n :: ih i') i) v i

/-- `incrNthFast` is `incrNth`. -/
theorem incrNthFast_eq (v : List ℕ) (i : ℕ) : incrNthFast v i = incrNth v i := by
  induction v generalizing i with
  | nil => rw [incrNth, ← replicateOneFast_eq]; rfl
  | cons n v ih =>
    cases i with
    | zero => rfl
    | succ i => rw [incrNth, ← ih]; rfl

/-- Kernel-fast `tallyHubcap` (Coq `tally_hubcap`). -/
noncomputable def tallyHubcapFast (hc : Hubcap) : List ℕ :=
  Hubcap.rec (motive := fun _ => List ℕ) []
    (fun i _ _ ih => incrNthFast ih i) (fun i j _ _ ih => incrNthFast (incrNthFast ih i) j) hc

/-- `tallyHubcapFast` is `tallyHubcap`. -/
theorem tallyHubcapFast_eq (hc : Hubcap) : tallyHubcapFast hc = tallyHubcap hc := by
  induction hc with
  | nil => rfl
  | cons1 i b hc ih => rw [tallyHubcap, ← ih, ← incrNthFast_eq]; rfl
  | cons2 i j b hc ih => rw [tallyHubcap, ← ih, ← incrNthFast_eq, ← incrNthFast_eq]; rfl

/-- Kernel-fast `v.getD i 0`. -/
noncomputable def getDZeroFast (v : List ℕ) (i : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => Nat.zero)
    (fun n _ ih i => Nat.rec (motive := fun _ => ℕ) n (fun i' _ => ih i') i) v i

/-- `getDZeroFast v i` is `v.getD i 0`. -/
theorem getDZeroFast_eq (v : List ℕ) (i : ℕ) : getDZeroFast v i = v.getD i 0 := by
  induction v generalizing i with
  | nil => simp [getDZeroFast]
  | cons n v ih =>
    cases i with
    | zero => rfl
    | succ i => rw [List.getD_cons_succ, ← ih]; rfl

/-- Kernel-fast `v.contains 0`. -/
noncomputable def containsZeroFast (v : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun n _ ih => bif% (Nat.beq n Nat.zero) true ih) v

/-- `containsZeroFast v` is `v.contains 0`. -/
theorem containsZeroFast_eq (v : List ℕ) : containsZeroFast v = v.contains 0 := by
  induction v with
  | nil => rfl
  | cons n v ih =>
    cases n with
    | zero => rfl
    | succ k => exact ih

/-- Kernel-fast `!decide (0 < b)` for an integer `b`. -/
noncomputable def nonposFast (b : ℤ) : Bool :=
  Int.rec (motive := fun _ => Bool) (fun n => Nat.beq n Nat.zero) (fun _ => true) b

/-- `nonposFast b` is `!decide (0 < b)`. -/
theorem nonposFast_eq (b : ℤ) : nonposFast b = !decide (0 < b) := by
  rcases b with n | n
  · cases n with
    | zero => rfl
    | succ k => exact (by simp : (!decide (0 < Int.ofNat (k + 1))) = false).symm
  · exact (by simp : (!decide (0 < Int.negSucc n)) = true).symm

/-- Kernel-fast `hubcapCoverRec` (Coq `hubcap_cover_rec`). -/
noncomputable def hubcapCoverRecFast (v : List ℕ) (b : ℤ) (hc : Hubcap) : Bool :=
  Hubcap.rec (motive := fun _ => ℤ → Bool) (fun b => nonposFast b)
    (fun i b' _ ih b => bif% (Nat.beq (getDZeroFast v i) (nat_lit 1))
      (ih (Int.add (Int.mul b' (Int.ofNat (nat_lit 2))) b)) false)
    (fun i j b' _ ih b => (fun ni => bif% (Nat.beq ni (getDZeroFast v j))
      (bif% (Nat.ble ni (nat_lit 2))
        (ih (Int.add (Int.mul b' (Int.ofNat (Bool.rec (motive := fun _ => ℕ) (nat_lit 1)
          (nat_lit 2) (Nat.beq ni (nat_lit 1))))) b)) false) false) (getDZeroFast v i))
    hc b

/-- `hubcapCoverRecFast` is `hubcapCoverRec`. -/
theorem hubcapCoverRecFast_eq (v : List ℕ) (b : ℤ) (hc : Hubcap) :
    hubcapCoverRecFast v b hc = hubcapCoverRec v b hc := by
  induction hc generalizing b with
  | nil => rw [hubcapCoverRec, ← nonposFast_eq]; rfl
  | cons1 i b' hc ih =>
    show Bool.rec (motive := fun _ => Bool) false
      (hubcapCoverRecFast v (Int.add (Int.mul b' (Int.ofNat 2)) b) hc)
      (Nat.beq (getDZeroFast v i) 1) = _
    rw [ih, getDZeroFast_eq, hubcapCoverRec, bool_rec_false_eq_and]
    rfl
  | cons2 i j b' hc ih =>
    show Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
      (hubcapCoverRecFast v (Int.add (Int.mul b' (Int.ofNat (Bool.rec (motive := fun _ => ℕ) 1 2
        (Nat.beq (getDZeroFast v i) 1)))) b) hc) (Nat.ble (getDZeroFast v i) 2))
      (Nat.beq (getDZeroFast v i) (getDZeroFast v j)) = _
    rw [ih, getDZeroFast_eq, getDZeroFast_eq, hubcapCoverRec, bool_rec_false_eq_and,
      bool_rec_false_eq_and, nat_ble_eq,
      show ∀ c : Bool, Bool.rec (motive := fun _ => ℕ) 1 2 c = c.toNat + 1 from
        fun c => by cases c <;> rfl]
    rfl

/-- Kernel-fast `dboundK` (Coq `dboundK`). -/
noncomputable def dboundKFast (nhub : ℕ) : ℤ :=
  Nat.rec (motive := fun _ => ℤ) (Int.ofNat (nat_lit 10))
    (fun n _ => Int.neg (Int.ofNat (Nat.mul n (nat_lit 10)))) (Nat.sub nhub (nat_lit 5))

/-- `dboundKFast` is `dboundK`. -/
theorem dboundKFast_eq (nhub : ℕ) : dboundKFast nhub = dboundK nhub := by
  rw [dboundKFast, dboundK]
  show Nat.rec (motive := fun _ => ℤ) _ _ (nhub - 5) = _
  rcases nhub - 5 with _ | n <;> rfl

/-- Kernel-fast `hubcapCover` (Coq `hubcap_cover`). -/
noncomputable def hubcapCoverFast (nhub : ℕ) (hc : Hubcap) : Bool :=
  (fun v => bif% (Nat.beq (lengthFast v) nhub)
    (bif% (containsZeroFast v) false
      (hubcapCoverRecFast v (Int.sub (Int.mul (dboundKFast nhub) (Int.ofNat (nat_lit 2)))
        (Int.ofNat (nat_lit 1))) hc)) false)
  (tallyHubcapFast hc)

/-- `hubcapCoverFast` is `hubcapCover`. -/
theorem hubcapCoverFast_eq (nhub : ℕ) (hc : Hubcap) :
    hubcapCoverFast nhub hc = hubcapCover nhub hc := by
  rw [hubcapCoverFast, hubcapCover]
  simp only [tallyHubcapFast_eq, lengthFast_eq, containsZeroFast_eq, dboundKFast_eq,
    hubcapCoverRecFast_eq, bool_rec_false_eq_and, bool_rec_false_eq_not_and]
  rfl

/-! ### Similarity -/

/-- The side condition of Coq `succeed_by_similarity` (`present.v`): `p` (mirrored if `mir`),
rotated by `j`, has the size of `ps` and is a subset of `ps`. -/
def similarCheck (ps p : Part) (j : ℕ) (mir : Bool) : Bool :=
  let p1 := if mir then mirrorPart p else p
  let p2 := rotPart j p1
  (sizePart ps == sizePart p2) && decide (cmpPart p2 ps = .subset)

/-- `similarCheck` is the side condition of Coq `succeed_by_similarity`. -/
theorem similarCheck_iff (ps p : Part) (j : ℕ) (mir : Bool) :
    similarCheck ps p j mir = true ↔
      sizePart ps = sizePart (rotPart j (if mir then mirrorPart p else p)) ∧
        cmpPart (rotPart j (if mir then mirrorPart p else p)) ps = .subset := by
  simp [similarCheck]

/-- Kernel-fast `similarCheck`. -/
noncomputable def similarCheckFast (ps p : Part) (j : ℕ) (mir : Bool) : Bool :=
  (fun p2 => bif% (Nat.beq (sizePartFast ps) (sizePartFast p2)) (subsetPartFast' p2 ps) false)
    (rotPartFast j (Bool.rec (motive := fun _ => Part) p (mirrorPartFast p) mir))

/-- `similarCheckFast` is `similarCheck`. -/
theorem similarCheckFast_eq (ps p : Part) (j : ℕ) (mir : Bool) :
    similarCheckFast ps p j mir = similarCheck ps p j mir := by
  have e : Bool.rec (motive := fun _ => Part) p (mirrorPartFast p) mir =
      (if mir then mirrorPart p else p) := by
    cases mir <;> simp [mirrorPartFast_eq]
  simp only [similarCheckFast, similarCheck, e, rotPartFast_eq, sizePartFast_eq, subsetPartFast'_eq,
    bool_rec_false_eq_and]
  rfl

end FourColor
