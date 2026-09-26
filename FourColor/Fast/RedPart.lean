/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.RedPart
import FourColor.Fast.Part

/-!
# Kernel-fast `redpart`

A fast version, for evaluation by the kernel (`decide +kernel`), of the reducibility check of
parts `redpart qt p` (Coq `redpart.v`, `FourColor.RedPart`), including the quiz-tree matching it
does, with the theorem `redpartFast_eq : redpartFast qt p = redpart qt p` (for every quiz tree
`qt` and part `p`). Every function of the search has a fast version `fooFast` with a theorem
`fooFast_eq` stating that it is equal to the faithful `foo`.

## Definitions (faithful name → fast name, each with its theorem `_eq`)

* qarities and ranges: `natOfQarity`, `qarityOfNat`, `hubRange`, `topqa`, `fitqa` →
  `natOfQarityFast`, `qarityOfNatFast`, `hubRangeFast`, `topqaFast`, `fitqaFast`;
* zipper parts: `shiftPart`, `dropPart 1`, `zshiftl`, `zshiftr`, `zfanL`, `zfanR`, `zfanLt`,
  `zfanRt`, `zstepL`, `zstepR`, `zstepLt`, `zstepRt`, `zrange` → `shiftPartFast`,
  `dropPart1Fast`, `zshiftlFast`, `zshiftrFast` (and `zshiftlPartsFast`, `zshiftrPartsFast`,
  on the sectors of a zipper part), `zfanLFast`, ..., `zrangeFast`;
* popping ranges: `redPcons`, `redPoprSpoke`, `redPoprHat`, `redPoplSpoke`, `redPoplHat`,
  `redPoplFan[123][lr]`, `redPop` → `redPconsFast`, ..., `redPopFast`;
* quiz matching: `fitqzp`, `redPopqzp`, `redQztLeaf` → `fitqzpFast`, `redPopqzpFast`,
  `redQztLeafFast`;
* quiz-tree lookup: `qztProper`, `qztGetr`, `qztGet1`, `qztTruncate` → `qztProperFast`, ...;
* the search: `redZpartRec` (its loop body is `redZpartFoundFast`), `redZpart`,
  `redpart.loop`, `redpart` → `redZpartRecFast`, `redZpartFast`, `redpartLoopFast`,
  `redpartFast`.

## Style

As in `FourColor.Fast.Part`: every
recursion and case analysis is a direct recursor application (no `match`, `ite`, `Decidable`,
`brecOn` or typeclass arithmetic), the boolean tests are `Bool.rec`s (lazy in the branch not
taken, like `&&` and `if`), and the case analyses on zipper locations have closed minor premises
(the arguments they use are passed after the major premise, the motive being a function type),
so that unfolding a definition or an iota reduction only instantiates the branch taken. All
definitions are `noncomputable`.
-/

namespace FourColor

/-- `bif% c a b` is `if c then a else b` for booleans, as one `Bool.rec`. -/
local macro "bif% " c:term:max a:term:max b:term:max : term =>
  `(Bool.rec (motive := fun _ => Bool) $b $a $c)

/-- `Bool.rec` is `if`. -/
private theorem bool_rec_eq_ite {α : Sort _} (c : Bool) (a b : α) :
    Bool.rec (motive := fun _ => α) b a c = if c = true then a else b := by
  cases c <;> rfl

/-- `Bool.rec` with a `false` first branch is `&&`. -/
private theorem bool_rec_false_eq_and (a b : Bool) :
    Bool.rec (motive := fun _ => Bool) false b a = (a && b) := by
  cases a <;> rfl

/-! ### Qarities and ranges -/

/-- Kernel-fast `natOfQarity` (Coq `nat_of_qarity`). -/
noncomputable def natOfQarityFast (qa : Qarity) : ℕ :=
  Qarity.rec (motive := fun _ => ℕ) (nat_lit 5) (nat_lit 6) (nat_lit 7) (nat_lit 8) (nat_lit 9)
    (nat_lit 10) (nat_lit 11) qa

/-- `natOfQarityFast` is `natOfQarity`. -/
theorem natOfQarityFast_eq (qa : Qarity) : natOfQarityFast qa = natOfQarity qa := by
  cases qa <;> rfl

/-- Kernel-fast `qarityOfNat` (Coq `qarity_of_nat`): nested `Nat.rec`s. -/
noncomputable def qarityOfNatFast (n : ℕ) : Qarity :=
  Nat.rec (motive := fun _ => Qarity) Qa11 (fun n1 _ =>
    Nat.rec (motive := fun _ => Qarity) Qa11 (fun n2 _ =>
      Nat.rec (motive := fun _ => Qarity) Qa11 (fun n3 _ =>
        Nat.rec (motive := fun _ => Qarity) Qa11 (fun n4 _ =>
          Nat.rec (motive := fun _ => Qarity) Qa11 (fun n5 _ =>
            Nat.rec (motive := fun _ => Qarity) Qa5 (fun n6 _ =>
              Nat.rec (motive := fun _ => Qarity) Qa6 (fun n7 _ =>
                Nat.rec (motive := fun _ => Qarity) Qa7 (fun n8 _ =>
                  Nat.rec (motive := fun _ => Qarity) Qa8 (fun n9 _ =>
                    Nat.rec (motive := fun _ => Qarity) Qa9 (fun n10 _ =>
                      Nat.rec (motive := fun _ => Qarity) Qa10 (fun _ _ => Qa11) n10)
                      n9) n8) n7) n6) n5) n4) n3) n2) n1) n

/-- `qarityOfNatFast` is `qarityOfNat`. -/
theorem qarityOfNatFast_eq (n : ℕ) : qarityOfNatFast n = qarityOfNat n := by
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n <;> rfl

/-- Kernel-fast `hubRange` (Coq `hub_range`). -/
noncomputable def hubRangeFast (ahub : Qarity) : Prange :=
  Qarity.rec (motive := fun _ => Prange) .pr55 .pr66 .pr77 .pr88 .pr99 .pr99 .pr99 ahub

/-- `hubRangeFast` is `hubRange`. -/
theorem hubRangeFast_eq (ahub : Qarity) : hubRangeFast ahub = hubRange ahub := by
  cases ahub <;> rfl

/-- Kernel-fast `topqa` (Coq `topqa`). -/
noncomputable def topqaFast (r : Prange) : Qarity :=
  Prange.rec (motive := fun _ => Qarity) Qa5 Qa6 Qa7 Qa8 Qa9 Qa6 Qa7 Qa8 Qa9 Qa7 Qa8 Qa9 Qa8 Qa9
    Qa9 r

/-- `topqaFast` is `topqa`. -/
theorem topqaFast_eq (r : Prange) : topqaFast r = topqa r := by
  cases r <;> rfl

/-- `fitqa` for a range whose top arity is 5 (a row of `fitqaFast`). -/
noncomputable def fitqaRow5 (qa : Qarity) : Bool :=
  Qarity.rec (motive := fun _ => Bool) true false false false false false false qa
/-- `fitqa` for a range whose top arity is 6 (a row of `fitqaFast`). -/
noncomputable def fitqaRow6 (qa : Qarity) : Bool :=
  Qarity.rec (motive := fun _ => Bool) false true false false false false false qa
/-- `fitqa` for a range whose top arity is 7 (a row of `fitqaFast`). -/
noncomputable def fitqaRow7 (qa : Qarity) : Bool :=
  Qarity.rec (motive := fun _ => Bool) false false true false false false false qa
/-- `fitqa` for a range whose top arity is 8 (a row of `fitqaFast`). -/
noncomputable def fitqaRow8 (qa : Qarity) : Bool :=
  Qarity.rec (motive := fun _ => Bool) false false false true false false false qa
/-- `fitqa` for an unbounded range (a row of `fitqaFast`). -/
noncomputable def fitqaRowNo (_ : Qarity) : Bool := false

/-- Kernel-fast `fitqa` (Coq `fitqa`): a two-level table. -/
noncomputable def fitqaFast (r : Prange) (qa : Qarity) : Bool :=
  Prange.rec (motive := fun _ => Qarity → Bool) fitqaRow5 fitqaRow6 fitqaRow7 fitqaRow8 fitqaRowNo
    fitqaRow6 fitqaRow7 fitqaRow8 fitqaRowNo fitqaRow7 fitqaRow8 fitqaRowNo fitqaRow8 fitqaRowNo
    fitqaRowNo r qa

/-- `fitqaFast` is `fitqa`. -/
theorem fitqaFast_eq (r : Prange) (qa : Qarity) : fitqaFast r qa = fitqa r qa := by
  cases r <;> cases qa <;> rfl

/-! ### Zipper parts -/

/-- Kernel-fast `shiftPart` (Coq `shift_part`): prepend the first subpart of `p1` to `p2`. -/
noncomputable def shiftPartFast (p1 p2 : Part) : Part :=
  Part.rec (motive := fun _ => Part → Part) (fun p2 => p2) (fun s h _ _ p2 => .cons s h p2)
    (fun h f1 _ _ p2 => .cons6 h f1 p2) (fun h f1 f2 _ _ p2 => .cons7 h f1 f2 p2)
    (fun h f1 f2 f3 _ _ p2 => .cons8 h f1 f2 f3 p2) p1 p2

/-- `shiftPartFast` is `shiftPart`. -/
theorem shiftPartFast_eq (p1 p2 : Part) : shiftPartFast p1 p2 = shiftPart p1 p2 := by
  cases p1 <;> rfl

/-- Kernel-fast `dropPart 1`. -/
noncomputable def dropPart1Fast (p : Part) : Part :=
  Part.rec (motive := fun _ => Part) .nil (fun _ _ p' _ => p') (fun _ _ p' _ => p')
    (fun _ _ _ p' _ => p') (fun _ _ _ _ p' _ => p') p

/-- `dropPart1Fast` is `dropPart 1`. -/
theorem dropPart1Fast_eq (p : Part) : dropPart1Fast p = dropPart 1 p := by
  cases p <;> rfl

/-- `zshiftl` on the sectors `pl`, `pr` of a zipper part (the location of the zipper part is
not used): case analysis on `pl`, then on its tail. -/
noncomputable def zshiftlPartsFast (p0l p0r : Part) (zi : ZpartLoc) (pl pr : Part) : Zpart :=
  Part.rec (motive := fun _ => Part → Part → ZpartLoc → Part → Zpart)
    (fun p0l p0r zi _ => .mk zi (dropPart1Fast p0l) (shiftPartFast p0l p0r))
    (fun s h pl' _ p0l p0r zi pr => Part.rec (motive := fun _ => Zpart) (.mk zi p0l p0r)
      (fun _ _ _ _ => .mk zi pl' (.cons s h pr)) (fun _ _ _ _ => .mk zi pl' (.cons s h pr))
      (fun _ _ _ _ _ => .mk zi pl' (.cons s h pr))
      (fun _ _ _ _ _ _ => .mk zi pl' (.cons s h pr)) pl')
    (fun h f1 pl' _ p0l p0r zi pr => Part.rec (motive := fun _ => Zpart) (.mk zi p0l p0r)
      (fun _ _ _ _ => .mk zi pl' (.cons6 h f1 pr)) (fun _ _ _ _ => .mk zi pl' (.cons6 h f1 pr))
      (fun _ _ _ _ _ => .mk zi pl' (.cons6 h f1 pr))
      (fun _ _ _ _ _ _ => .mk zi pl' (.cons6 h f1 pr)) pl')
    (fun h f1 f2 pl' _ p0l p0r zi pr => Part.rec (motive := fun _ => Zpart) (.mk zi p0l p0r)
      (fun _ _ _ _ => .mk zi pl' (.cons7 h f1 f2 pr))
      (fun _ _ _ _ => .mk zi pl' (.cons7 h f1 f2 pr))
      (fun _ _ _ _ _ => .mk zi pl' (.cons7 h f1 f2 pr))
      (fun _ _ _ _ _ _ => .mk zi pl' (.cons7 h f1 f2 pr)) pl')
    (fun h f1 f2 f3 pl' _ p0l p0r zi pr => Part.rec (motive := fun _ => Zpart) (.mk zi p0l p0r)
      (fun _ _ _ _ => .mk zi pl' (.cons8 h f1 f2 f3 pr))
      (fun _ _ _ _ => .mk zi pl' (.cons8 h f1 f2 f3 pr))
      (fun _ _ _ _ _ => .mk zi pl' (.cons8 h f1 f2 f3 pr))
      (fun _ _ _ _ _ _ => .mk zi pl' (.cons8 h f1 f2 f3 pr)) pl')
    pl p0l p0r zi pr

/-- `zshiftr` on the sectors `pl`, `pr` of a zipper part: case analysis on `pr`, then on its
tail. -/
noncomputable def zshiftrPartsFast (p0l p0r : Part) (zi : ZpartLoc) (pl pr : Part) : Zpart :=
  Part.rec (motive := fun _ => Part → Part → ZpartLoc → Part → Zpart)
    (fun p0l p0r zi _ => .mk zi (shiftPartFast p0r p0l) (dropPart1Fast p0r))
    (fun s h pr' _ p0l p0r zi pl => Part.rec (motive := fun _ => Zpart) (.mk zi p0l p0r)
      (fun _ _ _ _ => .mk zi (.cons s h pl) pr') (fun _ _ _ _ => .mk zi (.cons s h pl) pr')
      (fun _ _ _ _ _ => .mk zi (.cons s h pl) pr')
      (fun _ _ _ _ _ _ => .mk zi (.cons s h pl) pr') pr')
    (fun h f1 pr' _ p0l p0r zi pl => Part.rec (motive := fun _ => Zpart) (.mk zi p0l p0r)
      (fun _ _ _ _ => .mk zi (.cons6 h f1 pl) pr') (fun _ _ _ _ => .mk zi (.cons6 h f1 pl) pr')
      (fun _ _ _ _ _ => .mk zi (.cons6 h f1 pl) pr')
      (fun _ _ _ _ _ _ => .mk zi (.cons6 h f1 pl) pr') pr')
    (fun h f1 f2 pr' _ p0l p0r zi pl => Part.rec (motive := fun _ => Zpart) (.mk zi p0l p0r)
      (fun _ _ _ _ => .mk zi (.cons7 h f1 f2 pl) pr')
      (fun _ _ _ _ => .mk zi (.cons7 h f1 f2 pl) pr')
      (fun _ _ _ _ _ => .mk zi (.cons7 h f1 f2 pl) pr')
      (fun _ _ _ _ _ _ => .mk zi (.cons7 h f1 f2 pl) pr') pr')
    (fun h f1 f2 f3 pr' _ p0l p0r zi pl => Part.rec (motive := fun _ => Zpart) (.mk zi p0l p0r)
      (fun _ _ _ _ => .mk zi (.cons8 h f1 f2 f3 pl) pr')
      (fun _ _ _ _ => .mk zi (.cons8 h f1 f2 f3 pl) pr')
      (fun _ _ _ _ _ => .mk zi (.cons8 h f1 f2 f3 pl) pr')
      (fun _ _ _ _ _ _ => .mk zi (.cons8 h f1 f2 f3 pl) pr') pr')
    pr p0l p0r zi pl

/-- `zshiftlPartsFast` is `zshiftl` on the sectors of a zipper part (whatever its location). -/
theorem zshiftlPartsFast_eq (p0l p0r : Part) (zi zi' : ZpartLoc) (pl pr : Part) :
    zshiftlPartsFast p0l p0r zi pl pr = zshiftl p0l p0r zi ⟨zi', pl, pr⟩ := by
  rcases pl with _ | ⟨_, _, pl⟩ | ⟨_, _, pl⟩ | ⟨_, _, _, pl⟩ | ⟨_, _, _, _, pl⟩
  · simp only [zshiftlPartsFast, zshiftl, dropPart1Fast_eq, shiftPartFast_eq]
  all_goals cases pl <;> rfl

/-- `zshiftrPartsFast` is `zshiftr` on the sectors of a zipper part (whatever its location). -/
theorem zshiftrPartsFast_eq (p0l p0r : Part) (zi zi' : ZpartLoc) (pl pr : Part) :
    zshiftrPartsFast p0l p0r zi pl pr = zshiftr p0l p0r zi ⟨zi', pl, pr⟩ := by
  rcases pr with _ | ⟨_, _, pr⟩ | ⟨_, _, pr⟩ | ⟨_, _, _, pr⟩ | ⟨_, _, _, _, pr⟩
  · simp only [zshiftrPartsFast, zshiftr, dropPart1Fast_eq, shiftPartFast_eq]
  all_goals cases pr <;> rfl

/-- Kernel-fast `zshiftl` (Coq `zshiftl`). -/
noncomputable def zshiftlFast (p0l p0r : Part) (zi : ZpartLoc) (zp : Zpart) : Zpart :=
  Zpart.rec (motive := fun _ => Part → Part → ZpartLoc → Zpart)
    (fun _ pl pr p0l p0r zi => zshiftlPartsFast p0l p0r zi pl pr) zp p0l p0r zi

/-- `zshiftlFast` is `zshiftl`. -/
theorem zshiftlFast_eq (p0l p0r : Part) (zi : ZpartLoc) (zp : Zpart) :
    zshiftlFast p0l p0r zi zp = zshiftl p0l p0r zi zp := by
  obtain ⟨zi', pl, pr⟩ := zp
  exact zshiftlPartsFast_eq p0l p0r zi zi' pl pr

/-- Kernel-fast `zshiftr` (Coq `zshiftr`). -/
noncomputable def zshiftrFast (p0l p0r : Part) (zi : ZpartLoc) (zp : Zpart) : Zpart :=
  Zpart.rec (motive := fun _ => Part → Part → ZpartLoc → Zpart)
    (fun _ pl pr p0l p0r zi => zshiftrPartsFast p0l p0r zi pl pr) zp p0l p0r zi

/-- `zshiftrFast` is `zshiftr`. -/
theorem zshiftrFast_eq (p0l p0r : Part) (zi : ZpartLoc) (zp : Zpart) :
    zshiftrFast p0l p0r zi zp = zshiftr p0l p0r zi zp := by
  obtain ⟨zi', pl, pr⟩ := zp
  exact zshiftrPartsFast_eq p0l p0r zi zi' pl pr

/-- Kernel-fast `zfanL` (Coq `zfanL`). -/
noncomputable def zfanLFast (pr : Part) : ZpartLoc :=
  Part.rec (motive := fun _ => ZpartLoc) Znil
    (fun s _ _ _ => Prange.rec (motive := fun _ => ZpartLoc) Zfan0l Znil Znil Znil Znil Znil Znil
      Znil Znil Znil Znil Znil Znil Znil Znil s)
    (fun _ _ _ _ => Zfan1l) (fun _ _ _ _ _ => Zfan2l) (fun _ _ _ _ _ _ => Zfan3l) pr

/-- `zfanLFast` is `zfanL`. -/
theorem zfanLFast_eq (pr : Part) : zfanLFast pr = zfanL pr := by
  rcases pr with _ | ⟨s, _, _⟩ | _ | _ | _ <;> try rfl
  cases s <;> rfl

/-- Kernel-fast `zfanR` (Coq `zfanR`). -/
noncomputable def zfanRFast (pl : Part) : ZpartLoc :=
  Part.rec (motive := fun _ => ZpartLoc) Znil
    (fun s _ _ _ => Prange.rec (motive := fun _ => ZpartLoc) Zfan0r Znil Znil Znil Znil Znil Znil
      Znil Znil Znil Znil Znil Znil Znil Znil s)
    (fun _ _ _ _ => Zfan1r) (fun _ _ _ _ _ => Zfan2r) (fun _ _ _ _ _ _ => Zfan3r) pl

/-- `zfanRFast` is `zfanR`. -/
theorem zfanRFast_eq (pl : Part) : zfanRFast pl = zfanR pl := by
  rcases pl with _ | ⟨s, _, _⟩ | _ | _ | _ <;> try rfl
  cases s <;> rfl

/-- Kernel-fast `zfanLt` (Coq `zfanLt`). -/
noncomputable def zfanLtFast (pr : Part) : ZpartLoc :=
  Part.rec (motive := fun _ => ZpartLoc) Znil
    (fun s _ _ _ => Prange.rec (motive := fun _ => ZpartLoc) Zfan0l Zfan1l Znil Znil Znil Zfan1l
      Znil Znil Znil Znil Znil Znil Znil Znil Znil s)
    (fun _ _ _ _ => Zfan1l) (fun _ _ _ _ _ => Zfan2l) (fun _ _ _ _ _ _ => Zfan3l) pr

/-- `zfanLtFast` is `zfanLt`. -/
theorem zfanLtFast_eq (pr : Part) : zfanLtFast pr = zfanLt pr := by
  rcases pr with _ | ⟨s, _, _⟩ | _ | _ | _ <;> try rfl
  cases s <;> rfl

/-- Kernel-fast `zfanRt` (Coq `zfanRt`). -/
noncomputable def zfanRtFast (pl : Part) : ZpartLoc :=
  Part.rec (motive := fun _ => ZpartLoc) Znil
    (fun s _ _ _ => Prange.rec (motive := fun _ => ZpartLoc) Zfan0r Zfan1r Znil Znil Znil Zfan1r
      Znil Znil Znil Znil Znil Znil Znil Znil Znil s)
    (fun _ _ _ _ => Zfan1r) (fun _ _ _ _ _ => Zfan2r) (fun _ _ _ _ _ _ => Zfan3r) pl

/-- `zfanRtFast` is `zfanRt`. -/
theorem zfanRtFast_eq (pl : Part) : zfanRtFast pl = zfanRt pl := by
  rcases pl with _ | ⟨s, _, _⟩ | _ | _ | _ <;> try rfl
  cases s <;> rfl

/-- Kernel-fast `zstepL` (Coq `zstepL`): a `ZpartLoc.rec` with closed minor premises. -/
noncomputable def zstepLFast (p0l p0r : Part) (zp : Zpart) : Zpart :=
  Zpart.rec (motive := fun _ => Part → Part → Zpart) (fun zi pl pr p0l p0r =>
    ZpartLoc.rec (motive := fun _ => Part → Part → Part → Part → Zpart)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr p0l p0r => zshiftlPartsFast p0l p0r Zhubl pl pr)
      (fun pl pr _ _ => .mk Zhat pl pr)
      (fun pl pr p0l p0r => zshiftrPartsFast p0l p0r Zhubr pl pr)
      (fun pl pr p0l p0r => zshiftrPartsFast p0l p0r (zfanLFast pr) pl pr)
      (fun pl pr _ _ => .mk (zfanRFast pl) pl pr)
      (fun pl pr _ _ => .mk Zhub pl pr)
      (fun pl pr _ _ => .mk Zhatr pl pr)
      (fun pl pr _ _ => .mk Zfan0l pl pr)
      (fun pl pr _ _ => .mk Zfan1l pl pr)
      (fun pl pr _ _ => .mk Zfan2l pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      zi pl pr p0l p0r) zp p0l p0r

/-- `zstepLFast` is `zstepL`. -/
theorem zstepLFast_eq (p0l p0r : Part) (zp : Zpart) : zstepLFast p0l p0r zp = zstepL p0l p0r zp := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi <;> simp only [zstepLFast, zstepL, zfanLFast_eq, zfanRFast_eq] <;>
    first | exact zshiftlPartsFast_eq _ _ _ _ _ _ | exact zshiftrPartsFast_eq _ _ _ _ _ _

/-- Kernel-fast `zstepR` (Coq `zstepR`). -/
noncomputable def zstepRFast (p0l p0r : Part) (zp : Zpart) : Zpart :=
  Zpart.rec (motive := fun _ => Part → Part → Zpart) (fun zi pl pr p0l p0r =>
    ZpartLoc.rec (motive := fun _ => Part → Part → Part → Part → Zpart)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr p0l p0r => zshiftrPartsFast p0l p0r Zhubr pl pr)
      (fun pl pr p0l p0r => zshiftlPartsFast p0l p0r Zhubl pl pr)
      (fun pl pr _ _ => .mk Zhat pl pr)
      (fun pl pr _ _ => .mk (zfanRFast pl) pl pr)
      (fun pl pr _ _ => .mk Zhub pl pr)
      (fun pl pr p0l p0r => zshiftrPartsFast p0l p0r (zfanLFast pr) pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr p0l p0r => zshiftlPartsFast p0l p0r Zhatl pl pr)
      (fun pl pr _ _ => .mk Zfan0r pl pr)
      (fun pl pr _ _ => .mk Zfan1r pl pr)
      (fun pl pr _ _ => .mk Zfan2r pl pr)
      zi pl pr p0l p0r) zp p0l p0r

/-- `zstepRFast` is `zstepR`. -/
theorem zstepRFast_eq (p0l p0r : Part) (zp : Zpart) : zstepRFast p0l p0r zp = zstepR p0l p0r zp := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi <;> simp only [zstepRFast, zstepR, zfanLFast_eq, zfanRFast_eq] <;>
    first | exact zshiftlPartsFast_eq _ _ _ _ _ _ | exact zshiftrPartsFast_eq _ _ _ _ _ _

/-- Kernel-fast `zstepLt` (Coq `zstepLt`). -/
noncomputable def zstepLtFast (p0l p0r : Part) (zp : Zpart) : Zpart :=
  Zpart.rec (motive := fun _ => Part → Part → Zpart) (fun zi pl pr p0l p0r =>
    ZpartLoc.rec (motive := fun _ => Part → Part → Part → Part → Zpart)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr p0l p0r => zshiftlPartsFast p0l p0r Zhubl pl pr)
      (fun pl pr _ _ => .mk Zhat pl pr)
      (fun pl pr p0l p0r => zshiftrPartsFast p0l p0r Zhubr pl pr)
      (fun pl pr p0l p0r => zshiftrPartsFast p0l p0r (zfanLFast pr) pl pr)
      (fun pl pr _ _ => .mk (zfanRtFast pl) pl pr)
      (fun pl pr _ _ => .mk Zhub pl pr)
      (fun pl pr _ _ => .mk Zhatr pl pr)
      (fun pl pr _ _ => .mk Zfan0l pl pr)
      (fun pl pr _ _ => .mk Zfan1l pl pr)
      (fun pl pr _ _ => .mk Zfan2l pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      zi pl pr p0l p0r) zp p0l p0r

/-- `zstepLtFast` is `zstepLt`. -/
theorem zstepLtFast_eq (p0l p0r : Part) (zp : Zpart) :
    zstepLtFast p0l p0r zp = zstepLt p0l p0r zp := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi <;> simp only [zstepLtFast, zstepLt, zfanLFast_eq, zfanRtFast_eq] <;>
    first | exact zshiftlPartsFast_eq _ _ _ _ _ _ | exact zshiftrPartsFast_eq _ _ _ _ _ _

/-- Kernel-fast `zstepRt` (Coq `zstepRt`). -/
noncomputable def zstepRtFast (p0l p0r : Part) (zp : Zpart) : Zpart :=
  Zpart.rec (motive := fun _ => Part → Part → Zpart) (fun zi pl pr p0l p0r =>
    ZpartLoc.rec (motive := fun _ => Part → Part → Part → Part → Zpart)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr p0l p0r => zshiftrPartsFast p0l p0r Zhubr pl pr)
      (fun pl pr p0l p0r => zshiftlPartsFast p0l p0r Zhubl pl pr)
      (fun pl pr _ _ => .mk Zhat pl pr)
      (fun pl pr _ _ => .mk (zfanRFast pl) pl pr)
      (fun pl pr _ _ => .mk Zhub pl pr)
      (fun pl pr p0l p0r => zshiftrPartsFast p0l p0r (zfanLtFast pr) pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr _ _ => .mk Znil pl pr)
      (fun pl pr p0l p0r => zshiftlPartsFast p0l p0r Zhatl pl pr)
      (fun pl pr _ _ => .mk Zfan0r pl pr)
      (fun pl pr _ _ => .mk Zfan1r pl pr)
      (fun pl pr _ _ => .mk Zfan2r pl pr)
      zi pl pr p0l p0r) zp p0l p0r

/-- `zstepRtFast` is `zstepRt`. -/
theorem zstepRtFast_eq (p0l p0r : Part) (zp : Zpart) :
    zstepRtFast p0l p0r zp = zstepRt p0l p0r zp := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi <;> simp only [zstepRtFast, zstepRt, zfanLtFast_eq, zfanRFast_eq] <;>
    first | exact zshiftlPartsFast_eq _ _ _ _ _ _ | exact zshiftrPartsFast_eq _ _ _ _ _ _

/-- Kernel-fast `zrange` (Coq `zrange`): a `ZpartLoc.rec` with closed minor premises. -/
noncomputable def zrangeFast (ahub : Qarity) (zp : Zpart) : Prange :=
  Zpart.rec (motive := fun _ => Qarity → Prange) (fun zi pl pr ahub =>
    ZpartLoc.rec (motive := fun _ => Qarity → Part → Part → Prange)
      (fun _ _ _ => .pr59)
      (fun ahub _ _ => hubRangeFast ahub)
      (fun _ pl _ => getSpokeFast pl)
      (fun _ _ pr => getSpokeFast pr)
      (fun _ _ pr => getHatFast pr)
      (fun _ pl _ => getSpokeFast pl)
      (fun _ _ pr => getSpokeFast pr)
      (fun _ _ pr => getHatFast pr)
      (fun _ pl _ => getFan1lFast pl)
      (fun _ pl _ => getFan2lFast pl)
      (fun _ pl _ => getFan3lFast pl)
      (fun _ pl _ => getHatFast pl)
      (fun _ pl _ => getFan1rFast pl)
      (fun _ pl _ => getFan2rFast pl)
      (fun _ pl _ => getFan3rFast pl)
      zi ahub pl pr) zp ahub

/-- `zrangeFast` is `zrange`. -/
theorem zrangeFast_eq (ahub : Qarity) (zp : Zpart) : zrangeFast ahub zp = zrange ahub zp := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi <;> simp only [zrangeFast, zrange, hubRangeFast_eq, getSpokeFast_eq, getHatFast_eq,
    getFan1lFast_eq, getFan2lFast_eq, getFan3lFast_eq, getFan1rFast_eq, getFan2rFast_eq,
    getFan3rFast_eq]

/-! ### Popping ranges -/

/-- Kernel-fast `redPcons` (Coq `red_pcons`): a `Prange.rec` on `r` with closed minor premises,
applied to the recursive check `rpc` of the popped part. -/
noncomputable def redPconsFast (ahub : Qarity) (redRec : Part → Bool) (p0r : Part)
    (pc : Prange → Part → Part) (r : Prange) (pr : Part) : Bool :=
  Prange.rec (motive := fun _ => (Prange → Bool) → Bool)
    (fun _ => true) (fun _ => true) (fun _ => true) (fun _ => true) (fun _ => true)
    (fun rpc => rpc .pr55) (fun rpc => rpc .pr66) (fun rpc => rpc .pr77) (fun _ => true)
    (fun rpc => rpc .pr56) (fun rpc => rpc .pr67) (fun _ => true)
    (fun rpc => rpc .pr57) (fun _ => true) (fun _ => true) r
    (fun r' => redRec (takePartFast (natOfQarityFast ahub) (catPartFast (pc r' pr) p0r)))

/-- `redPconsFast` is `redPcons`. -/
theorem redPconsFast_eq (ahub : Qarity) (redRec : Part → Bool) (p0r : Part)
    (pc : Prange → Part → Part) (r : Prange) (pr : Part) :
    redPconsFast ahub redRec p0r pc r pr = redPcons ahub redRec p0r pc r pr := by
  cases r <;> simp only [redPconsFast, redPcons, takePartFast_eq, catPartFast_eq,
    natOfQarityFast_eq]

/-- Kernel-fast `redPoprSpoke` (Coq `red_popr_spoke`). -/
noncomputable def redPoprSpokeFast (ahub : Qarity) (redRec : Part → Bool) (p0r pr : Part) :
    Bool :=
  Part.rec (motive := fun _ => Bool) true
    (fun s h p _ => redPconsFast ahub redRec p0r (fun r => .cons r h) s p)
    (fun _ _ _ _ => true) (fun _ _ _ _ _ => true) (fun _ _ _ _ _ _ => true) pr

/-- `redPoprSpokeFast` is `redPoprSpoke`. -/
theorem redPoprSpokeFast_eq (ahub : Qarity) (redRec : Part → Bool) (p0r pr : Part) :
    redPoprSpokeFast ahub redRec p0r pr = redPoprSpoke ahub redRec p0r pr := by
  cases pr <;> simp only [redPoprSpokeFast, redPoprSpoke, redPconsFast_eq]

/-- Kernel-fast `redPoprHat` (Coq `red_popr_hat`). -/
noncomputable def redPoprHatFast (ahub : Qarity) (redRec : Part → Bool) (p0r pr : Part) :
    Bool :=
  Part.rec (motive := fun _ => Bool) true
    (fun s h p _ => redPconsFast ahub redRec p0r (Part.cons s) h p)
    (fun h f1 p _ => redPconsFast ahub redRec p0r (fun r => .cons6 r f1) h p)
    (fun h f1 f2 p _ => redPconsFast ahub redRec p0r (fun h' => .cons7 h' f1 f2) h p)
    (fun h f1 f2 f3 p _ => redPconsFast ahub redRec p0r (fun h' => .cons8 h' f1 f2 f3) h p) pr

/-- `redPoprHatFast` is `redPoprHat`. -/
theorem redPoprHatFast_eq (ahub : Qarity) (redRec : Part → Bool) (p0r pr : Part) :
    redPoprHatFast ahub redRec p0r pr = redPoprHat ahub redRec p0r pr := by
  cases pr <;> simp only [redPoprHatFast, redPoprHat, redPconsFast_eq]

/-- Kernel-fast `redPoplSpoke` (Coq `red_popl_spoke`). -/
noncomputable def redPoplSpokeFast (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    Bool :=
  Part.rec (motive := fun _ => Bool) true
    (fun s h _ _ => redPconsFast ahub redRec p0r (fun r => .cons r h) s pr)
    (fun _ _ _ _ => true) (fun _ _ _ _ _ => true) (fun _ _ _ _ _ _ => true) pl

/-- `redPoplSpokeFast` is `redPoplSpoke`. -/
theorem redPoplSpokeFast_eq (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    redPoplSpokeFast ahub redRec p0r pl pr = redPoplSpoke ahub redRec p0r pl pr := by
  cases pl <;> simp only [redPoplSpokeFast, redPoplSpoke, redPconsFast_eq]

/-- Kernel-fast `redPoplHat` (Coq `red_popl_hat`). -/
noncomputable def redPoplHatFast (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    Bool :=
  Part.rec (motive := fun _ => Bool) true
    (fun s h _ _ => redPconsFast ahub redRec p0r (fun r => .cons s r) h pr)
    (fun h f1 _ _ => redPconsFast ahub redRec p0r (fun r => .cons6 r f1) h pr)
    (fun h f1 f2 _ _ => redPconsFast ahub redRec p0r (fun r => .cons7 r f1 f2) h pr)
    (fun h f1 f2 f3 _ _ => redPconsFast ahub redRec p0r (fun r => .cons8 r f1 f2 f3) h pr) pl

/-- `redPoplHatFast` is `redPoplHat`. -/
theorem redPoplHatFast_eq (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    redPoplHatFast ahub redRec p0r pl pr = redPoplHat ahub redRec p0r pl pr := by
  cases pl <;> simp only [redPoplHatFast, redPoplHat, redPconsFast_eq]

/-- Kernel-fast `redPoplFan1l` (Coq `red_popl_fan1l`). -/
noncomputable def redPoplFan1lFast (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    Bool :=
  Part.rec (motive := fun _ => Bool) true (fun _ _ _ _ => true)
    (fun h f1 _ _ => redPconsFast ahub redRec p0r (fun r => .cons6 h r) f1 pr)
    (fun h f1 f2 _ _ => redPconsFast ahub redRec p0r (fun r => .cons7 h f1 r) f2 pr)
    (fun h f1 f2 f3 _ _ => redPconsFast ahub redRec p0r (fun r => .cons8 h f1 f2 r) f3 pr) pl

/-- `redPoplFan1lFast` is `redPoplFan1l`. -/
theorem redPoplFan1lFast_eq (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    redPoplFan1lFast ahub redRec p0r pl pr = redPoplFan1l ahub redRec p0r pl pr := by
  cases pl <;> simp only [redPoplFan1lFast, redPoplFan1l, redPconsFast_eq]

/-- Kernel-fast `redPoplFan2l` (Coq `red_popl_fan2l`). -/
noncomputable def redPoplFan2lFast (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    Bool :=
  Part.rec (motive := fun _ => Bool) true (fun _ _ _ _ => true) (fun _ _ _ _ => true)
    (fun h f1 f2 _ _ => redPconsFast ahub redRec p0r (fun r => .cons7 h r f2) f1 pr)
    (fun h f1 f2 f3 _ _ => redPconsFast ahub redRec p0r (fun r => .cons8 h f1 r f3) f2 pr) pl

/-- `redPoplFan2lFast` is `redPoplFan2l`. -/
theorem redPoplFan2lFast_eq (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    redPoplFan2lFast ahub redRec p0r pl pr = redPoplFan2l ahub redRec p0r pl pr := by
  cases pl <;> simp only [redPoplFan2lFast, redPoplFan2l, redPconsFast_eq]

/-- Kernel-fast `redPoplFan3l` (Coq `red_popl_fan3l`). -/
noncomputable def redPoplFan3lFast (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    Bool :=
  Part.rec (motive := fun _ => Bool) true (fun _ _ _ _ => true) (fun _ _ _ _ => true)
    (fun _ _ _ _ _ => true)
    (fun h f1 f2 f3 _ _ => redPconsFast ahub redRec p0r (fun r => .cons8 h r f2 f3) f1 pr) pl

/-- `redPoplFan3lFast` is `redPoplFan3l`. -/
theorem redPoplFan3lFast_eq (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    redPoplFan3lFast ahub redRec p0r pl pr = redPoplFan3l ahub redRec p0r pl pr := by
  cases pl <;> simp only [redPoplFan3lFast, redPoplFan3l, redPconsFast_eq]

/-- Kernel-fast `redPoplFan1r` (Coq `red_popl_fan1r`). -/
noncomputable def redPoplFan1rFast (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    Bool :=
  Part.rec (motive := fun _ => Bool) true (fun _ _ _ _ => true)
    (fun h f1 _ _ => redPconsFast ahub redRec p0r (fun r => .cons6 h r) f1 pr)
    (fun h f1 f2 _ _ => redPconsFast ahub redRec p0r (fun r => .cons7 h r f2) f1 pr)
    (fun h f1 f2 f3 _ _ => redPconsFast ahub redRec p0r (fun r => .cons8 h r f2 f3) f1 pr) pl

/-- `redPoplFan1rFast` is `redPoplFan1r`. -/
theorem redPoplFan1rFast_eq (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    redPoplFan1rFast ahub redRec p0r pl pr = redPoplFan1r ahub redRec p0r pl pr := by
  cases pl <;> simp only [redPoplFan1rFast, redPoplFan1r, redPconsFast_eq]

/-- Kernel-fast `redPoplFan2r` (Coq `red_popl_fan2r`). -/
noncomputable def redPoplFan2rFast (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    Bool :=
  Part.rec (motive := fun _ => Bool) true (fun _ _ _ _ => true) (fun _ _ _ _ => true)
    (fun h f1 f2 _ _ => redPconsFast ahub redRec p0r (fun r => .cons7 h f1 r) f2 pr)
    (fun h f1 f2 f3 _ _ => redPconsFast ahub redRec p0r (fun r => .cons8 h f1 r f3) f2 pr) pl

/-- `redPoplFan2rFast` is `redPoplFan2r`. -/
theorem redPoplFan2rFast_eq (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    redPoplFan2rFast ahub redRec p0r pl pr = redPoplFan2r ahub redRec p0r pl pr := by
  cases pl <;> simp only [redPoplFan2rFast, redPoplFan2r, redPconsFast_eq]

/-- Kernel-fast `redPoplFan3r` (Coq `red_popl_fan3r`). -/
noncomputable def redPoplFan3rFast (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    Bool :=
  Part.rec (motive := fun _ => Bool) true (fun _ _ _ _ => true) (fun _ _ _ _ => true)
    (fun _ _ _ _ _ => true)
    (fun h f1 f2 f3 _ _ => redPconsFast ahub redRec p0r (fun r => .cons8 h f1 f2 r) f3 pr) pl

/-- `redPoplFan3rFast` is `redPoplFan3r`. -/
theorem redPoplFan3rFast_eq (ahub : Qarity) (redRec : Part → Bool) (p0r pl pr : Part) :
    redPoplFan3rFast ahub redRec p0r pl pr = redPoplFan3r ahub redRec p0r pl pr := by
  cases pl <;> simp only [redPoplFan3rFast, redPoplFan3r, redPconsFast_eq]

/-- Kernel-fast `redPop` (Coq `red_pop`): a `ZpartLoc.rec` with closed minor premises. -/
noncomputable def redPopFast (ahub : Qarity) (redRec : Part → Bool) (p0r : Part) (zp : Zpart) :
    Bool :=
  Zpart.rec (motive := fun _ => Qarity → (Part → Bool) → Part → Bool) (fun zi pl pr ahub redRec p0r =>
    ZpartLoc.rec (motive := fun _ => Qarity → (Part → Bool) → Part → Part → Part → Bool)
      (fun _ _ _ _ _ => true)
      (fun _ _ _ _ _ => true)
      (fun ahub redRec p0r pl pr => redPoplSpokeFast ahub redRec p0r pl pr)
      (fun ahub redRec p0r _ pr => redPoprSpokeFast ahub redRec p0r pr)
      (fun ahub redRec p0r _ pr => redPoprHatFast ahub redRec p0r pr)
      (fun ahub redRec p0r pl pr => redPoplSpokeFast ahub redRec p0r pl pr)
      (fun ahub redRec p0r _ pr => redPoprSpokeFast ahub redRec p0r pr)
      (fun ahub redRec p0r _ pr => redPoprHatFast ahub redRec p0r pr)
      (fun ahub redRec p0r pl pr => redPoplFan1lFast ahub redRec p0r pl pr)
      (fun ahub redRec p0r pl pr => redPoplFan2lFast ahub redRec p0r pl pr)
      (fun ahub redRec p0r pl pr => redPoplFan3lFast ahub redRec p0r pl pr)
      (fun ahub redRec p0r pl pr => redPoplHatFast ahub redRec p0r pl pr)
      (fun ahub redRec p0r pl pr => redPoplFan1rFast ahub redRec p0r pl pr)
      (fun ahub redRec p0r pl pr => redPoplFan2rFast ahub redRec p0r pl pr)
      (fun ahub redRec p0r pl pr => redPoplFan3rFast ahub redRec p0r pl pr)
      zi ahub redRec p0r pl pr) zp ahub redRec p0r

/-- `redPopFast` is `redPop`. -/
theorem redPopFast_eq (ahub : Qarity) (redRec : Part → Bool) (p0r : Part) (zp : Zpart) :
    redPopFast ahub redRec p0r zp = redPop ahub redRec p0r zp := by
  obtain ⟨zi, pl, pr⟩ := zp
  cases zi <;> simp only [redPopFast, redPop, redPoplSpokeFast_eq, redPoprSpokeFast_eq,
    redPoprHatFast_eq, redPoplHatFast_eq, redPoplFan1lFast_eq, redPoplFan2lFast_eq,
    redPoplFan3lFast_eq, redPoplFan1rFast_eq, redPoplFan2rFast_eq, redPoplFan3rFast_eq]

/-! ### Matching questions -/

/-- Kernel-fast `fitqzp` (Coq `fitqzp`): a `Question.rec` with closed minor premises. -/
noncomputable def fitqzpFast (ahub : Qarity) (p0l p0r : Part) (zp : Zpart) (q : Question) : Bool :=
  Question.rec (motive := fun _ => Qarity → Part → Part → Zpart → Bool)
    (fun _ _ _ _ => true)
    (fun qa ahub _ _ zp => fitqaFast (zrangeFast ahub zp) qa)
    (fun qa _ ih ahub p0l p0r zp =>
      bif% (fitqaFast (zrangeFast ahub zp) qa) (ih ahub p0l p0r (zstepLtFast p0l p0r zp)) false)
    (fun qa _ ih ahub p0l p0r zp =>
      bif% (fitqaFast (zrangeFast ahub zp) qa) (ih ahub p0l p0r (zstepRtFast p0l p0r zp)) false)
    (fun qa _ _ ihl ihr ahub p0l p0r zp =>
      bif% (fitqaFast (zrangeFast ahub zp) qa)
        (bif% (ihl ahub p0l p0r (zstepLFast p0l p0r zp)) (ihr ahub p0l p0r (zstepRFast p0l p0r zp))
          false)
        false)
    (fun qa _ ih ahub p0l p0r zp =>
      bif% (fitqaFast (zrangeFast ahub (zstepLFast p0l p0r zp)) qa)
        (ih ahub p0l p0r (zstepLFast p0l p0r (zstepLFast p0l p0r zp))) false)
    (fun qa _ ih ahub p0l p0r zp =>
      bif% (fitqaFast (zrangeFast ahub (zstepRFast p0l p0r zp)) qa)
        (ih ahub p0l p0r (zstepRFast p0l p0r (zstepRFast p0l p0r zp))) false)
    q ahub p0l p0r zp

/-- `fitqzpFast` is `fitqzp`. -/
theorem fitqzpFast_eq (ahub : Qarity) (p0l p0r : Part) (zp : Zpart) (q : Question) :
    fitqzpFast ahub p0l p0r zp q = fitqzp ahub p0l p0r zp q := by
  induction q generalizing zp with
  | Qask0 => rfl
  | Qask1 qa => simp only [fitqzpFast, fitqzp, fitqaFast_eq, zrangeFast_eq]
  | QaskL qa ql ih =>
    simp only [fitqzp, ← ih, ← bool_rec_eq_ite, ← fitqaFast_eq, ← zrangeFast_eq,
      ← zstepLtFast_eq]
    rfl
  | QaskR qa qr ih =>
    simp only [fitqzp, ← ih, ← bool_rec_eq_ite, ← fitqaFast_eq, ← zrangeFast_eq,
      ← zstepRtFast_eq]
    rfl
  | QaskLR qa ql qr ihl ihr =>
    simp only [fitqzp, ← ihl, ← ihr, ← bool_rec_eq_ite, ← fitqaFast_eq, ← zrangeFast_eq,
      ← zstepLFast_eq, ← zstepRFast_eq]
    rfl
  | QaskLL qa ql ih =>
    simp only [fitqzp, ← ih, ← bool_rec_eq_ite, ← fitqaFast_eq, ← zrangeFast_eq,
      ← zstepLFast_eq]
    rfl
  | QaskRR qa qr ih =>
    simp only [fitqzp, ← ih, ← bool_rec_eq_ite, ← fitqaFast_eq, ← zrangeFast_eq,
      ← zstepRFast_eq]
    rfl

/-- Kernel-fast `redPopqzp` (Coq `red_popqzp`). -/
noncomputable def redPopqzpFast (ahub : Qarity) (redRec : Part → Bool) (p0l p0r : Part)
    (zp : Zpart) (q : Question) : Bool :=
  Question.rec (motive := fun _ => Zpart → Bool)
    (fun _ => true)
    (fun _ zp => redPopFast ahub redRec p0r zp)
    (fun _ _ ih zp => bif% (redPopFast ahub redRec p0r zp) (ih (zstepLtFast p0l p0r zp)) false)
    (fun _ _ ih zp => bif% (redPopFast ahub redRec p0r zp) (ih (zstepRtFast p0l p0r zp)) false)
    (fun _ _ _ ihl ihr zp => bif% (redPopFast ahub redRec p0r zp)
      (bif% (ihl (zstepLFast p0l p0r zp)) (ihr (zstepRFast p0l p0r zp)) false) false)
    (fun _ _ ih zp => bif% (redPopFast ahub redRec p0r (zstepLFast p0l p0r zp))
      (ih (zstepLFast p0l p0r (zstepLFast p0l p0r zp))) false)
    (fun _ _ ih zp => bif% (redPopFast ahub redRec p0r (zstepRFast p0l p0r zp))
      (ih (zstepRFast p0l p0r (zstepRFast p0l p0r zp))) false)
    q zp

/-- `redPopqzpFast` is `redPopqzp`. -/
theorem redPopqzpFast_eq (ahub : Qarity) (redRec : Part → Bool) (p0l p0r : Part) (zp : Zpart)
    (q : Question) : redPopqzpFast ahub redRec p0l p0r zp q = redPopqzp ahub redRec p0l p0r zp q := by
  induction q generalizing zp with
  | Qask0 => rfl
  | Qask1 qa => exact redPopFast_eq ahub redRec p0r zp
  | QaskL qa ql ih =>
    simp only [redPopqzp, ← ih, ← redPopFast_eq, ← zstepLtFast_eq, ← bool_rec_false_eq_and]
    rfl
  | QaskR qa qr ih =>
    simp only [redPopqzp, ← ih, ← redPopFast_eq, ← zstepRtFast_eq, ← bool_rec_false_eq_and]
    rfl
  | QaskLR qa ql qr ihl ihr =>
    simp only [redPopqzp, ← ihl, ← ihr, ← redPopFast_eq, ← zstepLFast_eq, ← zstepRFast_eq,
      ← bool_rec_false_eq_and]
    rfl
  | QaskLL qa ql ih =>
    simp only [redPopqzp, ← ih, ← redPopFast_eq, ← zstepLFast_eq, ← bool_rec_false_eq_and]
    rfl
  | QaskRR qa qr ih =>
    simp only [redPopqzp, ← ih, ← redPopFast_eq, ← zstepRFast_eq, ← bool_rec_false_eq_and]
    rfl

/-- Kernel-fast `redQztLeaf` (Coq `red_qzt_leaf`): a `QuizTree.rec` on the leaf list. -/
noncomputable def redQztLeafFast (ahub : Qarity) (redRec : Part → Bool) (p0l p0r : Part)
    (zp1 zp2 zp3 : Zpart) (t : QuizTree) : Bool :=
  QuizTree.rec (motive := fun _ => Bool) false
    (fun q1 q2 q3 _ ih =>
      bif% (fitqzpFast ahub p0l p0r zp3 q3)
        (bif% (fitqzpFast ahub p0l p0r zp2 q2)
          (bif% (fitqzpFast ahub p0l p0r zp1 q1)
            (bif% (redPopqzpFast ahub redRec p0l p0r zp1 q1)
              (bif% (redPopqzpFast ahub redRec p0l p0r zp2 q2)
                (redPopqzpFast ahub redRec p0l p0r zp3 q3) false) false)
            ih)
          ih)
        ih)
    (fun _ _ _ _ _ _ _ _ => false) (fun _ _ _ _ _ _ _ _ => false) t

/-- `redQztLeafFast` is `redQztLeaf`. -/
theorem redQztLeafFast_eq (ahub : Qarity) (redRec : Part → Bool) (p0l p0r : Part)
    (zp1 zp2 zp3 : Zpart) (t : QuizTree) :
    redQztLeafFast ahub redRec p0l p0r zp1 zp2 zp3 t =
      redQztLeaf ahub redRec p0l p0r zp1 zp2 zp3 t := by
  induction t with
  | QztNil => rfl
  | QztLeaf q1 q2 q3 t ih =>
    simp only [redQztLeaf, ← ih, ← fitqzpFast_eq, ← redPopqzpFast_eq, ← bool_rec_false_eq_and,
      ← bool_rec_eq_ite]
    rfl
  | QztNode => rfl
  | QztHubNode => rfl

/-! ### Quiz-tree lookup -/

/-- Kernel-fast `qztProper` (Coq `qzt_proper`). -/
noncomputable def qztProperFast (t : QuizTree) : Bool :=
  QuizTree.rec (motive := fun _ => Bool) false (fun _ _ _ _ _ => true)
    (fun _ _ _ _ _ _ _ _ => true) (fun _ _ _ _ _ _ _ _ => true) t

/-- `qztProperFast` is `qztProper`. -/
theorem qztProperFast_eq (t : QuizTree) : qztProperFast t = qztProper t := by
  cases t <;> rfl

/-- Kernel-fast `qztGetr` (Coq `qzt_getr`). -/
noncomputable def qztGetrFast (r : Prange) (t : QuizTree) : QuizTree :=
  QuizTree.rec (motive := fun _ => Prange → QuizTree) (fun _ => QztNil)
    (fun _ _ _ _ _ _ => QztNil)
    (fun t5 t6 t7 t8 _ _ _ _ r => Prange.rec (motive := fun _ => QuizTree)
      t5 t6 t7 t8 QztNil t6 t7 t8 QztNil t7 t8 QztNil t8 QztNil QztNil r)
    (fun _ _ _ _ _ _ _ _ _ => QztNil) t r

/-- `qztGetrFast` is `qztGetr`. -/
theorem qztGetrFast_eq (r : Prange) (t : QuizTree) : qztGetrFast r t = qztGetr r t := by
  cases t <;> try rfl
  cases r <;> rfl

/-- Kernel-fast `qztGet1` (Coq `qzt_get1`). -/
noncomputable def qztGet1Fast (qa : Qarity) (t : QuizTree) : QuizTree :=
  QuizTree.rec (motive := fun _ => Qarity → QuizTree) (fun _ => QztNil)
    (fun _ _ _ _ _ _ => QztNil)
    (fun t5 t6 t7 t8 _ _ _ _ qa => Qarity.rec (motive := fun _ => QuizTree)
      t5 t6 t7 t8 QztNil QztNil QztNil qa)
    (fun _ t9 t10 t11 ih _ _ _ qa => Qarity.rec (motive := fun _ => QuizTree)
      (ih Qa5) (ih Qa6) (ih Qa7) (ih Qa8) t9 t10 t11 qa) t qa

/-- `qztGet1Fast` is `qztGet1`. -/
theorem qztGet1Fast_eq (qa : Qarity) (t : QuizTree) : qztGet1Fast qa t = qztGet1 qa t := by
  induction t generalizing qa with
  | QztNil => cases qa <;> rfl
  | QztLeaf => cases qa <;> rfl
  | QztNode => cases qa <;> rfl
  | QztHubNode t58 t9 t10 t11 ih =>
    cases qa <;> simp only [qztGet1] <;> first | rfl | exact ih _

/-- Kernel-fast `qztTruncate` (Coq `qzt_truncate`). -/
noncomputable def qztTruncateFast (t : QuizTree) : QuizTree :=
  QuizTree.rec (motive := fun _ => QuizTree → QuizTree) (fun t => t) (fun _ _ _ _ _ t => t)
    (fun _ _ _ _ _ _ _ _ t => t)
    (fun t58 _ _ _ _ _ _ _ t => QuizTree.rec (motive := fun _ => QuizTree → QuizTree → QuizTree)
      (fun _ t => t) (fun _ _ _ _ _ _ t => t) (fun _ _ _ _ _ _ _ _ t58 _ => t58)
      (fun _ _ _ _ _ _ _ _ _ t => t) t58 t58 t) t t

/-- `qztTruncateFast` is `qztTruncate`. -/
theorem qztTruncateFast_eq (t : QuizTree) : qztTruncateFast t = qztTruncate t := by
  rcases t with _ | _ | _ | ⟨t58, _, _, _⟩ <;> try rfl
  cases t58 <;> rfl

/-! ### The search -/

/-- The loop body of `redZpartRecFast`: the `found` test of Coq `red_zpart_rec` for the
zipper part `zp = ⟨_, pl, pr⟩` and its right shift `zp' = ⟨_, pl', pr'⟩` (the argument
`sqt` is `qztGetr (getSpoke pr) (qztTruncate qt)`); the branches after the first two, which
depend on the shape of `pr`, are `redZpartFoundPrFast`. -/
noncomputable def redZpartFoundPrFast (ahub : Qarity) (redRec : Part → Bool) (p0l p0r : Part)
    (sqt : QuizTree) (pl pr pl' pr' : Part) : Bool :=
  Part.rec (motive := fun _ => Qarity → (Part → Bool) → Part → Part → QuizTree → Part → Part →
      Part → Part → Bool)
    (fun _ _ _ _ _ _ _ _ _ => false)
    (fun s h _ _ ahub redRec p0l p0r sqt pl pr pl' pr' =>
      Prange.rec (motive := fun _ => Bool)
        (bif% (redQztLeafFast ahub redRec p0l p0r ⟨Zhatr, pl', pr'⟩ ⟨Zhatl, pl, pr⟩
            ⟨Znil, pl', pr'⟩ (qztGetrFast (getHatFast pr') (qztGetrFast h sqt)))
          (bif% (redPoprHatFast ahub redRec p0r pr') (redPoprHatFast ahub redRec p0r pr) false)
          false)
        false false false false false false false false false false false false false false s)
    (fun h f1 _ _ ahub redRec p0l p0r sqt pl pr pl' pr' =>
      bif% (redQztLeafFast ahub redRec p0l p0r ⟨Zfan0l, pl', pr'⟩ ⟨Zhatl, pl, pr⟩
          ⟨Znil, pl', pr'⟩ (qztGetrFast f1 (qztGetrFast h sqt)))
        (bif% (redPoplFan1rFast ahub redRec p0r pl' pr') (redPoprHatFast ahub redRec p0r pr) false)
      (bif% (redQztLeafFast ahub redRec p0l p0r ⟨Zhatr, pl', pr'⟩ ⟨Zfan0r, pl', pr'⟩
          ⟨Znil, pl', pr'⟩ (qztGetrFast (getHatFast pr') (qztGetrFast f1 sqt)))
        (bif% (redPoprHatFast ahub redRec p0r pr') (redPoplFan1rFast ahub redRec p0r pl' pr') false)
      false))
    (fun h f1 f2 _ _ ahub redRec p0l p0r sqt pl pr pl' pr' =>
      bif% (redQztLeafFast ahub redRec p0l p0r ⟨Zfan1l, pl', pr'⟩ ⟨Zhatl, pl, pr⟩
          ⟨Znil, pl', pr'⟩ (qztGetrFast f1 (qztGetrFast h sqt)))
        (bif% (redPoplFan1rFast ahub redRec p0r pl' pr') (redPoprHatFast ahub redRec p0r pr) false)
      (bif% (redQztLeafFast ahub redRec p0l p0r ⟨Zfan0l, pl', pr'⟩ ⟨Zfan0r, pl', pr'⟩
          ⟨Znil, pl', pr'⟩ (qztGetrFast f2 (qztGetrFast f1 sqt)))
        (bif% (redPoplFan2rFast ahub redRec p0r pl' pr') (redPoplFan1rFast ahub redRec p0r pl' pr')
          false)
      (bif% (redQztLeafFast ahub redRec p0l p0r ⟨Zhatr, pl', pr'⟩ ⟨Zfan1r, pl', pr'⟩
          ⟨Znil, pl', pr'⟩ (qztGetrFast (getHatFast pr') (qztGetrFast f2 sqt)))
        (bif% (redPoprHatFast ahub redRec p0r pr') (redPoplFan2rFast ahub redRec p0r pl' pr') false)
      false)))
    (fun h f1 f2 f3 _ _ ahub redRec p0l p0r sqt pl pr pl' pr' =>
      bif% (redQztLeafFast ahub redRec p0l p0r ⟨Zfan2l, pl', pr'⟩ ⟨Zhatl, pl, pr⟩
          ⟨Znil, pl', pr'⟩ (qztGetrFast f1 (qztGetrFast h sqt)))
        (bif% (redPoplFan1rFast ahub redRec p0r pl' pr') (redPoprHatFast ahub redRec p0r pr) false)
      (bif% (redQztLeafFast ahub redRec p0l p0r ⟨Zfan1l, pl', pr'⟩ ⟨Zfan0r, pl', pr'⟩
          ⟨Znil, pl', pr'⟩ (qztGetrFast f2 (qztGetrFast f1 sqt)))
        (bif% (redPoplFan2rFast ahub redRec p0r pl' pr') (redPoplFan1rFast ahub redRec p0r pl' pr')
          false)
      (bif% (redQztLeafFast ahub redRec p0l p0r ⟨Zfan0l, pl', pr'⟩ ⟨Zfan1r, pl', pr'⟩
          ⟨Znil, pl', pr'⟩ (qztGetrFast f3 (qztGetrFast f2 sqt)))
        (bif% (redPoplFan3rFast ahub redRec p0r pl' pr') (redPoplFan2rFast ahub redRec p0r pl' pr')
          false)
      (bif% (redQztLeafFast ahub redRec p0l p0r ⟨Zhatr, pl', pr'⟩ ⟨Zfan2r, pl', pr'⟩
          ⟨Znil, pl', pr'⟩ (qztGetrFast (getHatFast pr') (qztGetrFast f3 sqt)))
        (bif% (redPoprHatFast ahub redRec p0r pr') (redPoplFan3rFast ahub redRec p0r pl' pr') false)
      false))))
    pr ahub redRec p0l p0r sqt pl pr pl' pr'

/-- The loop body of `redZpartRecFast` (see `redZpartFoundPrFast`), for the zipper part
`⟨zi, pl, pr⟩` and its right shift `⟨_, pl', pr'⟩`. -/
noncomputable def redZpartFoundFast (qt : QuizTree) (ahub : Qarity) (redRec : Part → Bool)
    (p0l p0r : Part) (zi : ZpartLoc) (pl pr pl' pr' : Part) (sqt : QuizTree) : Bool :=
  bif% (qztProperFast sqt)
    (bif% (redQztLeafFast ahub redRec p0l p0r ⟨Zhubr, pl', pr'⟩ (zshiftlPartsFast p0l p0r Zhubl pl pr)
        ⟨Zhat, pl, pr⟩
        (qztGetrFast (getSpokeFast pr) (qztGetrFast (getSpokeFast pl) (qztGet1Fast ahub qt))))
      (bif% (redPoprSpokeFast ahub redRec p0r pr) (redPoplSpokeFast ahub redRec p0r pl pr) false)
    (bif% (redQztLeafFast ahub redRec p0l p0r ⟨zfanLtFast pr, pl', pr'⟩ ⟨zi, pl, pr⟩
        ⟨zfanRtFast pl, pl, pr⟩ (qztGetrFast (getHatFast pr) (qztGetrFast (getSpokeFast pl) sqt)))
      (bif% (redPoprHatFast ahub redRec p0r pr)
        (bif% (redPoplSpokeFast ahub redRec p0r pl pr) (redPoprSpokeFast ahub redRec p0r pr) false)
        false)
      (redZpartFoundPrFast ahub redRec p0l p0r sqt pl pr pl' pr')))
    false

/-- Kernel-fast `redZpartRec` (Coq `red_zpart_rec`): `Nat.rec` on the count. -/
noncomputable def redZpartRecFast (qt : QuizTree) (ahub : Qarity) (redRec : Part → Bool)
    (p0l p0r : Part) (zp : Zpart) (d : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Zpart → Bool) (fun _ => false)
    (fun _ ih zp => Zpart.rec (motive := fun _ => Bool) (fun zi pl pr =>
      (fun zp' => Zpart.rec (motive := fun _ => Bool) (fun _ pl' pr' =>
        bif% (redZpartFoundFast qt ahub redRec p0l p0r zi pl pr pl' pr'
            (qztGetrFast (getSpokeFast pr) (qztTruncateFast qt)))
          true (ih zp')) zp')
        (zshiftrPartsFast p0l p0r Zhub pl pr)) zp)
    d zp

/-- `a && b` as an `if`. -/
private theorem and_eq_ite (a b : Bool) : (a && b) = if a = true then b else false := by
  cases a <;> rfl

/-- The loop body of the search is the one of `redZpartRec`. -/
private theorem redZpartFoundFast_eq (qt : QuizTree) (ahub : Qarity) (redRec : Part → Bool)
    (p0l p0r : Part) (zi zi' : ZpartLoc) (pl pr pl' pr' : Part) :
    redZpartFoundFast qt ahub redRec p0l p0r zi pl pr pl' pr'
        (qztGetrFast (getSpokeFast pr) (qztTruncateFast qt)) =
      (if qztProper (qztGetr (getSpoke pr) (qztTruncate qt)) = true then
          match (⟨zi', pl', pr'⟩ : Zpart) with
          | ⟨_, pl', pr'⟩ =>
          let s := getSpoke pr
          let sqt := qztGetr s (qztTruncate qt)
          let sl := getSpoke pl
          let zp : Zpart := ⟨zi, pl, pr⟩
          if redQztLeaf ahub redRec p0l p0r ⟨Zhubr, pl', pr'⟩ (zshiftl p0l p0r Zhubl zp)
              ⟨Zhat, pl, pr⟩ (qztGetr s (qztGetr sl (qztGet1 ahub qt))) then
            redPoprSpoke ahub redRec p0r pr && redPoplSpoke ahub redRec p0r pl pr
          else
          if redQztLeaf ahub redRec p0l p0r ⟨zfanLt pr, pl', pr'⟩ zp ⟨zfanRt pl, pl, pr⟩
              (qztGetr (getHat pr) (qztGetr sl sqt)) then
            redPoprHat ahub redRec p0r pr &&
              (redPoplSpoke ahub redRec p0r pl pr && redPoprSpoke ahub redRec p0r pr)
          else
          let zpnil : Zpart := ⟨Znil, pl', pr'⟩
          match pr with
          | .cons .pr55 h _ =>
            if redQztLeaf ahub redRec p0l p0r ⟨Zhatr, pl', pr'⟩ ⟨Zhatl, pl, pr⟩ zpnil
                (qztGetr (getHat pr') (qztGetr h sqt)) then
              redPoprHat ahub redRec p0r pr' && redPoprHat ahub redRec p0r pr
            else false
          | .cons6 h f1 _ =>
            if redQztLeaf ahub redRec p0l p0r ⟨Zfan0l, pl', pr'⟩ ⟨Zhatl, pl, pr⟩ zpnil
                (qztGetr f1 (qztGetr h sqt)) then
              redPoplFan1r ahub redRec p0r pl' pr' && redPoprHat ahub redRec p0r pr
            else
            if redQztLeaf ahub redRec p0l p0r ⟨Zhatr, pl', pr'⟩ ⟨Zfan0r, pl', pr'⟩ zpnil
                (qztGetr (getHat pr') (qztGetr f1 sqt)) then
              redPoprHat ahub redRec p0r pr' && redPoplFan1r ahub redRec p0r pl' pr'
            else false
          | .cons7 h f1 f2 _ =>
            if redQztLeaf ahub redRec p0l p0r ⟨Zfan1l, pl', pr'⟩ ⟨Zhatl, pl, pr⟩ zpnil
                (qztGetr f1 (qztGetr h sqt)) then
              redPoplFan1r ahub redRec p0r pl' pr' && redPoprHat ahub redRec p0r pr
            else
            if redQztLeaf ahub redRec p0l p0r ⟨Zfan0l, pl', pr'⟩ ⟨Zfan0r, pl', pr'⟩ zpnil
                (qztGetr f2 (qztGetr f1 sqt)) then
              redPoplFan2r ahub redRec p0r pl' pr' && redPoplFan1r ahub redRec p0r pl' pr'
            else
            if redQztLeaf ahub redRec p0l p0r ⟨Zhatr, pl', pr'⟩ ⟨Zfan1r, pl', pr'⟩ zpnil
                (qztGetr (getHat pr') (qztGetr f2 sqt)) then
              redPoprHat ahub redRec p0r pr' && redPoplFan2r ahub redRec p0r pl' pr'
            else false
          | .cons8 h f1 f2 f3 _ =>
            if redQztLeaf ahub redRec p0l p0r ⟨Zfan2l, pl', pr'⟩ ⟨Zhatl, pl, pr⟩ zpnil
                (qztGetr f1 (qztGetr h sqt)) then
              redPoplFan1r ahub redRec p0r pl' pr' && redPoprHat ahub redRec p0r pr
            else
            if redQztLeaf ahub redRec p0l p0r ⟨Zfan1l, pl', pr'⟩ ⟨Zfan0r, pl', pr'⟩ zpnil
                (qztGetr f2 (qztGetr f1 sqt)) then
              redPoplFan2r ahub redRec p0r pl' pr' && redPoplFan1r ahub redRec p0r pl' pr'
            else
            if redQztLeaf ahub redRec p0l p0r ⟨Zfan0l, pl', pr'⟩ ⟨Zfan1r, pl', pr'⟩ zpnil
                (qztGetr f3 (qztGetr f2 sqt)) then
              redPoplFan3r ahub redRec p0r pl' pr' && redPoplFan2r ahub redRec p0r pl' pr'
            else
            if redQztLeaf ahub redRec p0l p0r ⟨Zhatr, pl', pr'⟩ ⟨Zfan2r, pl', pr'⟩ zpnil
                (qztGetr (getHat pr') (qztGetr f3 sqt)) then
              redPoprHat ahub redRec p0r pr' && redPoplFan3r ahub redRec p0r pl' pr'
            else false
          | _ => false
        else false) := by
  have e1 := zshiftlPartsFast_eq p0l p0r Zhubl zi pl pr
  rcases pr with _ | ⟨s, h, p⟩ | ⟨h, f1, p⟩ | ⟨h, f1, f2, p⟩ | ⟨h, f1, f2, f3, p⟩
  all_goals try cases s
  all_goals simp only [redZpartFoundFast, redZpartFoundPrFast, e1, qztProperFast_eq,
    qztGetrFast_eq, getSpokeFast_eq, getHatFast_eq, qztTruncateFast_eq, qztGet1Fast_eq,
    redQztLeafFast_eq, redPoprSpokeFast_eq, redPoplSpokeFast_eq, redPoprHatFast_eq,
    redPoplFan1rFast_eq, redPoplFan2rFast_eq, redPoplFan3rFast_eq, zfanLtFast_eq, zfanRtFast_eq,
    bool_rec_eq_ite, and_eq_ite]

/-- `redZpartRecFast` is `redZpartRec`. -/
theorem redZpartRecFast_eq (qt : QuizTree) (ahub : Qarity) (redRec : Part → Bool)
    (p0l p0r : Part) (zp : Zpart) (d : ℕ) :
    redZpartRecFast qt ahub redRec p0l p0r zp d = redZpartRec qt ahub redRec p0l p0r zp d := by
  induction d generalizing zp with
  | zero => rfl
  | succ d ih =>
    obtain ⟨zi, pl, pr⟩ := zp
    have e := zshiftrPartsFast_eq p0l p0r Zhub zi pl pr
    have step : redZpartRecFast qt ahub redRec p0l p0r ⟨zi, pl, pr⟩ (d + 1) =
        Zpart.rec (motive := fun _ => Bool) (fun _ pl' pr' =>
          bif% (redZpartFoundFast qt ahub redRec p0l p0r zi pl pr pl' pr'
              (qztGetrFast (getSpokeFast pr) (qztTruncateFast qt)))
            true (redZpartRecFast qt ahub redRec p0l p0r (zshiftrPartsFast p0l p0r Zhub pl pr) d))
          (zshiftrPartsFast p0l p0r Zhub pl pr) := rfl
    rw [step, e, ih, redZpartRec]
    generalize zshiftr p0l p0r Zhub ⟨zi, pl, pr⟩ = zp'
    obtain ⟨zi', pl', pr'⟩ := zp'
    simp only [redZpartFoundFast_eq qt ahub redRec p0l p0r zi zi' pl pr pl' pr', bool_rec_eq_ite]
    rfl

/-- Kernel-fast `redZpart` (Coq `red_zpart`). -/
noncomputable def redZpartFast (qt : QuizTree) (ahub : Qarity) (redRec : Part → Bool)
    (p0l p0r : Part) : Bool :=
  redZpartRecFast qt ahub redRec p0l p0r ⟨Zhub, dropPart1Fast p0l, shiftPartFast p0l p0r⟩
    (natOfQarityFast ahub)

/-- `redZpartFast` is `redZpart`. -/
theorem redZpartFast_eq (qt : QuizTree) (ahub : Qarity) (redRec : Part → Bool) (p0l p0r : Part) :
    redZpartFast qt ahub redRec p0l p0r = redZpart qt ahub redRec p0l p0r := by
  simp only [redZpartFast, redZpart, redZpartRecFast_eq, dropPart1Fast_eq, shiftPartFast_eq,
    natOfQarityFast_eq]

/-- Kernel-fast `redpart.loop` (Coq `loop`, local to `redpart`). -/
noncomputable def redpartLoopFast (qt : QuizTree) (ahub : Qarity) (d : ℕ) : Part → Bool :=
  Nat.rec (motive := fun _ => Part → Bool) (fun _ => false)
    (fun _ ih p' => redZpartFast qt ahub ih (revPartFast p') p') d

/-- `redpartLoopFast` is `redpart.loop`. -/
theorem redpartLoopFast_eq (qt : QuizTree) (ahub : Qarity) (d : ℕ) :
    redpartLoopFast qt ahub d = redpart.loop qt ahub d := by
  induction d with
  | zero => funext p; rfl
  | succ d ih =>
    funext p
    show redZpartFast qt ahub (redpartLoopFast qt ahub d) (revPartFast p) p = _
    rw [ih, redZpartFast_eq, revPartFast_eq, redpart.loop]

/-- Kernel-fast `redpart` (Coq `redpart`): `redpartFast qt p = redpart qt p`
(`redpartFast_eq`). -/
noncomputable def redpartFast (qt : QuizTree) (p : Part) : Bool :=
  (fun nhub => (fun ahub =>
    bif% (Nat.beq nhub (natOfQarityFast ahub))
      (redpartLoopFast qt ahub (Nat.mul nhub (nat_lit 12)) p) false)
    (qarityOfNatFast nhub)) (sizePartFast p)

/-- `redpartFast` is `redpart`: the kernel-fast reducibility check of parts computes the faithful one. -/
theorem redpartFast_eq (qt : QuizTree) (p : Part) : redpartFast qt p = redpart qt p := by
  simp only [redpartFast, redpart, sizePartFast_eq, qarityOfNatFast_eq, natOfQarityFast_eq,
    redpartLoopFast_eq, bool_rec_false_eq_and]
  rfl

end FourColor
