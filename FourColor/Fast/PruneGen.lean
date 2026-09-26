/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Fast.Prune
import FourColor.Hubcap

/-!
# Computing pruning masks (native tool)

Computable functions, for native evaluation (`#eval`, `lean --run`) by the generators of the
presentation data, that compute the pruning mask (`QztMask`, `FourColor.Fast.Prune`) of a
`redpart` check or of a hubcap check: the masks keep the first fitting leaf of every
`redQztLeaf` call that the check makes on the full quiz tree, so that the check on the pruned
tree makes exactly the same calls, with the same results (see `FourColor.Fast.Prune`).

Nothing here is used in proofs: the kernel checks `redpartFast (qztPrune qt m) p` (or the
hubcap check) itself, whatever the mask `m`; a wrong mask only makes the check fail.

* `PruneGen.redpartW qt p` and `PruneGen.hubcapW qt rf p hc`: the check (`redpart qt p`,
  resp. `hubcapCover n hc && hubcapFit (redpart qt) rf p hc`) and the parts of the quiz tree it
  uses (`PruneGen.Item`): the first fitting leaves, as pairs of a leaf-list path in `qt` (the
  child indices `0..3` from the root) and the index of the leaf in its list, and the subtrees
  that the successful rotations of the search look up (the one of their spoke arity, and the
  one of the hub arity if they succeed with their first branch). These are writer-style copies
  of the faithful functions of `FourColor.RedPart` and `FourColor.Hubcap`, with the same (lazy)
  evaluation order.
* `PruneGen.maskOf qt used`: the mask keeping the leaves `used`; with `guards := true`, it also
  removes (`QztMask.nil`) the subtrees of the spoke arities 5 to 8 and of the hub arities 9 to 11
  that `used` does not keep. The check on the pruned tree then skips the rotations of its search
  that would select a removed subtree; these rotations fail on the full tree (they are not the
  successful ones), so the check still succeeds. (This was validated on all the leaves of the
  presentations, but measured no faster in the kernel, so it is off by default.)
* `PruneGen.redpartMask qt p`, `PruneGen.hubcapMask qt rf p hc`: the masks of the checks.
-/

namespace FourColor.PruneGen

/-- A used part of the quiz tree: a leaf (path of its leaf list, index of the leaf in the list),
or a guard subtree (the subtree of the spoke arity of a successful rotation, or of the hub arity
if the rotation succeeds with the first branch, the one looked up with `qztGet1 ahub`). -/
inductive Item : Type where
  | leaf (path : List ℕ) (i : ℕ)
  | guard (path : List ℕ)
  deriving DecidableEq, Repr, Inhabited

/-- The used parts of the quiz tree. -/
abbrev Used := List Item

/-- A boolean result with the leaves used to compute it. -/
abbrev W := Bool × Used

/-- A constant result. -/
def pureW (b : Bool) : W := (b, [])

/-- Lazy `&&` on `W`. -/
def andW (a : W) (b : Unit → W) : W :=
  if a.1 then let r := b (); (r.1, a.2 ++ r.2) else (false, a.2)

/-- Lazy `if` on `W`. -/
def ifW (c : W) (t e : Unit → W) : W :=
  if c.1 then let r := t (); (r.1, c.2 ++ r.2) else let r := e (); (r.1, c.2 ++ r.2)

/-! ### Popping ranges (copies of `FourColor.RedPart.Pop`) -/

/-- `redPcons`, writer-style. -/
def redPconsW (ahub : Qarity) (redRec : Part → W) (p0r : Part) (pc : Prange → Part → Part)
    (r : Prange) (pr : Part) : W :=
  let rpc (r' : Prange) := redRec (takePart (ahub : ℕ) (catPart (pc r' pr) p0r))
  match r with
  | .pr56 => rpc .pr55
  | .pr57 => rpc .pr56
  | .pr58 => rpc .pr57
  | .pr67 => rpc .pr66
  | .pr68 => rpc .pr67
  | .pr78 => rpc .pr77
  | _ => pureW true

/-- `redPoprSpoke`, writer-style. -/
def redPoprSpokeW (ahub : Qarity) (redRec : Part → W) (p0r pr : Part) : W :=
  match pr with
  | .cons s h p => redPconsW ahub redRec p0r (fun r => .cons r h) s p
  | _ => pureW true

/-- `redPoprHat`, writer-style. -/
def redPoprHatW (ahub : Qarity) (redRec : Part → W) (p0r pr : Part) : W :=
  match pr with
  | .cons s h p => redPconsW ahub redRec p0r (Part.cons s) h p
  | .cons6 h f1 p => redPconsW ahub redRec p0r (fun r => .cons6 r f1) h p
  | .cons7 h f1 f2 p => redPconsW ahub redRec p0r (fun h' => .cons7 h' f1 f2) h p
  | .cons8 h f1 f2 f3 p => redPconsW ahub redRec p0r (fun h' => .cons8 h' f1 f2 f3) h p
  | _ => pureW true

/-- `redPoplSpoke`, writer-style. -/
def redPoplSpokeW (ahub : Qarity) (redRec : Part → W) (p0r pl pr : Part) : W :=
  match pl with
  | .cons s h _ => redPconsW ahub redRec p0r (fun r => .cons r h) s pr
  | _ => pureW true

/-- `redPoplHat`, writer-style. -/
def redPoplHatW (ahub : Qarity) (redRec : Part → W) (p0r pl pr : Part) : W :=
  match pl with
  | .cons s h _ => redPconsW ahub redRec p0r (fun r => .cons s r) h pr
  | .cons6 h f1 _ => redPconsW ahub redRec p0r (fun r => .cons6 r f1) h pr
  | .cons7 h f1 f2 _ => redPconsW ahub redRec p0r (fun r => .cons7 r f1 f2) h pr
  | .cons8 h f1 f2 f3 _ => redPconsW ahub redRec p0r (fun r => .cons8 r f1 f2 f3) h pr
  | _ => pureW true

/-- `redPoplFan1l`, writer-style. -/
def redPoplFan1lW (ahub : Qarity) (redRec : Part → W) (p0r pl pr : Part) : W :=
  match pl with
  | .cons6 h f1 _ => redPconsW ahub redRec p0r (fun r => .cons6 h r) f1 pr
  | .cons7 h f1 f2 _ => redPconsW ahub redRec p0r (fun r => .cons7 h f1 r) f2 pr
  | .cons8 h f1 f2 f3 _ => redPconsW ahub redRec p0r (fun r => .cons8 h f1 f2 r) f3 pr
  | _ => pureW true

/-- `redPoplFan2l`, writer-style. -/
def redPoplFan2lW (ahub : Qarity) (redRec : Part → W) (p0r pl pr : Part) : W :=
  match pl with
  | .cons7 h f1 f2 _ => redPconsW ahub redRec p0r (fun r => .cons7 h r f2) f1 pr
  | .cons8 h f1 f2 f3 _ => redPconsW ahub redRec p0r (fun r => .cons8 h f1 r f3) f2 pr
  | _ => pureW true

/-- `redPoplFan3l`, writer-style. -/
def redPoplFan3lW (ahub : Qarity) (redRec : Part → W) (p0r pl pr : Part) : W :=
  match pl with
  | .cons8 h f1 f2 f3 _ => redPconsW ahub redRec p0r (fun r => .cons8 h r f2 f3) f1 pr
  | _ => pureW true

/-- `redPoplFan1r`, writer-style. -/
def redPoplFan1rW (ahub : Qarity) (redRec : Part → W) (p0r pl pr : Part) : W :=
  match pl with
  | .cons6 h f1 _ => redPconsW ahub redRec p0r (fun r => .cons6 h r) f1 pr
  | .cons7 h f1 f2 _ => redPconsW ahub redRec p0r (fun r => .cons7 h r f2) f1 pr
  | .cons8 h f1 f2 f3 _ => redPconsW ahub redRec p0r (fun r => .cons8 h r f2 f3) f1 pr
  | _ => pureW true

/-- `redPoplFan2r`, writer-style. -/
def redPoplFan2rW (ahub : Qarity) (redRec : Part → W) (p0r pl pr : Part) : W :=
  match pl with
  | .cons7 h f1 f2 _ => redPconsW ahub redRec p0r (fun r => .cons7 h f1 r) f2 pr
  | .cons8 h f1 f2 f3 _ => redPconsW ahub redRec p0r (fun r => .cons8 h f1 r f3) f2 pr
  | _ => pureW true

/-- `redPoplFan3r`, writer-style. -/
def redPoplFan3rW (ahub : Qarity) (redRec : Part → W) (p0r pl pr : Part) : W :=
  match pl with
  | .cons8 h f1 f2 f3 _ => redPconsW ahub redRec p0r (fun r => .cons8 h f1 f2 r) f3 pr
  | _ => pureW true

/-- `redPop`, writer-style. -/
def redPopW (ahub : Qarity) (redRec : Part → W) (p0r : Part) (zp : Zpart) : W :=
  match zp with
  | ⟨Zhubl, pl, pr⟩ => redPoplSpokeW ahub redRec p0r pl pr
  | ⟨Zhubr, _, pr⟩ => redPoprSpokeW ahub redRec p0r pr
  | ⟨Zhatl, pl, pr⟩ => redPoplSpokeW ahub redRec p0r pl pr
  | ⟨Zhat, _, pr⟩ => redPoprHatW ahub redRec p0r pr
  | ⟨Zhatr, _, pr⟩ => redPoprSpokeW ahub redRec p0r pr
  | ⟨Zfan0l, _, pr⟩ => redPoprHatW ahub redRec p0r pr
  | ⟨Zfan1l, pl, pr⟩ => redPoplFan1lW ahub redRec p0r pl pr
  | ⟨Zfan2l, pl, pr⟩ => redPoplFan2lW ahub redRec p0r pl pr
  | ⟨Zfan3l, pl, pr⟩ => redPoplFan3lW ahub redRec p0r pl pr
  | ⟨Zfan0r, pl, pr⟩ => redPoplHatW ahub redRec p0r pl pr
  | ⟨Zfan1r, pl, pr⟩ => redPoplFan1rW ahub redRec p0r pl pr
  | ⟨Zfan2r, pl, pr⟩ => redPoplFan2rW ahub redRec p0r pl pr
  | ⟨Zfan3r, pl, pr⟩ => redPoplFan3rW ahub redRec p0r pl pr
  | _ => pureW true

/-- `redPopqzp`, writer-style. -/
def redPopqzpW (ahub : Qarity) (redRec : Part → W) (p0l p0r : Part) (zp : Zpart) :
    Question → W
  | Qask0 => pureW true
  | Qask1 _ => redPopW ahub redRec p0r zp
  | QaskL _ ql => andW (redPopW ahub redRec p0r zp)
      (fun _ => redPopqzpW ahub redRec p0l p0r (zstepLt p0l p0r zp) ql)
  | QaskR _ qr => andW (redPopW ahub redRec p0r zp)
      (fun _ => redPopqzpW ahub redRec p0l p0r (zstepRt p0l p0r zp) qr)
  | QaskLR _ ql qr => andW (redPopW ahub redRec p0r zp)
      (fun _ => andW (redPopqzpW ahub redRec p0l p0r (zstepL p0l p0r zp) ql)
        (fun _ => redPopqzpW ahub redRec p0l p0r (zstepR p0l p0r zp) qr))
  | QaskLL _ ql => andW (redPopW ahub redRec p0r (zstepL p0l p0r zp))
      (fun _ => redPopqzpW ahub redRec p0l p0r (zstepL p0l p0r (zstepL p0l p0r zp)) ql)
  | QaskRR _ qr => andW (redPopW ahub redRec p0r (zstepR p0l p0r zp))
      (fun _ => redPopqzpW ahub redRec p0l p0r (zstepR p0l p0r (zstepR p0l p0r zp)) qr)

/-! ### Quiz-tree lookups with paths -/

/-- A subtree of the quiz tree with its path (the child indices from the root). -/
abbrev Sub := QuizTree × List ℕ

/-- `qztGetr` with paths. -/
def getrP (r : Prange) : Sub → Sub
  | (QztNode t5 t6 t7 t8, path) =>
    match topqa r with
    | Qa5 => (t5, path ++ [0])
    | Qa6 => (t6, path ++ [1])
    | Qa7 => (t7, path ++ [2])
    | Qa8 => (t8, path ++ [3])
    | _ => (QztNil, path)
  | (_, path) => (QztNil, path)

/-- `qztGet1` with paths. -/
def get1P (qa : Qarity) : Sub → Sub
  | (QztNode t5 t6 t7 t8, path) =>
    match qa with
    | Qa5 => (t5, path ++ [0])
    | Qa6 => (t6, path ++ [1])
    | Qa7 => (t7, path ++ [2])
    | Qa8 => (t8, path ++ [3])
    | _ => (QztNil, path)
  | (QztHubNode t58 t9 t10 t11, path) =>
    match qa with
    | Qa9 => (t9, path ++ [1])
    | Qa10 => (t10, path ++ [2])
    | Qa11 => (t11, path ++ [3])
    | _ =>
      match t58 with
      | QztNode t5 t6 t7 t8 =>
        match qa with
        | Qa5 => (t5, path ++ [0, 0])
        | Qa6 => (t6, path ++ [0, 1])
        | Qa7 => (t7, path ++ [0, 2])
        | Qa8 => (t8, path ++ [0, 3])
        | _ => (QztNil, path)
      | _ => (QztNil, path)
  | (_, path) => (QztNil, path)

/-- `qztTruncate` with paths. -/
def truncateP : Sub → Sub
  | (QztHubNode t58@(QztNode _ _ _ _) _ _ _, path) => (t58, path ++ [0])
  | s => s

/-- `redQztLeaf`, writer-style, recording the first fitting leaf of the leaf list `t` at path
`path` (the index of the head of `t` in its list is `i`). -/
def redQztLeafW (ahub : Qarity) (redRec : Part → W) (p0l p0r : Part) (zp1 zp2 zp3 : Zpart)
    (path : List ℕ) : QuizTree → ℕ → W
  | QztLeaf q1 q2 q3 t, i =>
    if fitqzp ahub p0l p0r zp3 q3 && fitqzp ahub p0l p0r zp2 q2 && fitqzp ahub p0l p0r zp1 q1 then
      let r := andW (redPopqzpW ahub redRec p0l p0r zp1 q1)
        (fun _ => andW (redPopqzpW ahub redRec p0l p0r zp2 q2)
          (fun _ => redPopqzpW ahub redRec p0l p0r zp3 q3))
      (r.1, .leaf path i :: r.2)
    else redQztLeafW ahub redRec p0l p0r zp1 zp2 zp3 path t (i + 1)
  | _, _ => pureW false

/-- `redQztLeaf` on a subtree with its path. -/
def leafW (ahub : Qarity) (redRec : Part → W) (p0l p0r : Part) (zp1 zp2 zp3 : Zpart) (s : Sub) :
    W :=
  redQztLeafW ahub redRec p0l p0r zp1 zp2 zp3 s.2 s.1 0

/-! ### The search (copies of `FourColor.RedPart.Search`) -/

/-- `redZpartRec`, writer-style. -/
def redZpartRecW (qt : QuizTree) (ahub : Qarity) (redRec : Part → W) (p0l p0r : Part) :
    Zpart → ℕ → W
  | _, 0 => pureW false
  | zp, d' + 1 =>
    let zp' := zshiftr p0l p0r Zhub zp
    match zp, zp' with
    | ⟨_, pl, pr⟩, ⟨_, pl', pr'⟩ =>
    let s := getSpoke pr
    let root : Sub := (qt, [])
    let sqt := getrP s (truncateP root)
    let sl := getSpoke pl
    let lw := leafW ahub redRec p0l p0r
    let zpnil : Zpart := ⟨Znil, pl', pr'⟩
    let leaf0 := lw ⟨Zhubr, pl', pr'⟩ (zshiftl p0l p0r Zhubl zp) ⟨Zhat, pl, pr⟩
      (getrP s (getrP sl (get1P ahub root)))
    let found : W :=
      if qztProper sqt.1 then
        ifW leaf0
          (fun _ => andW (redPoprSpokeW ahub redRec p0r pr)
            (fun _ => redPoplSpokeW ahub redRec p0r pl pr))
        fun _ => ifW (lw ⟨zfanLt pr, pl', pr'⟩ zp ⟨zfanRt pl, pl, pr⟩ (getrP (getHat pr) (getrP sl sqt)))
          (fun _ => andW (redPoprHatW ahub redRec p0r pr)
            (fun _ => andW (redPoplSpokeW ahub redRec p0r pl pr)
              (fun _ => redPoprSpokeW ahub redRec p0r pr)))
        fun _ =>
          match pr with
          | .cons .pr55 h _ =>
            ifW (lw ⟨Zhatr, pl', pr'⟩ ⟨Zhatl, pl, pr⟩ zpnil (getrP (getHat pr') (getrP h sqt)))
              (fun _ => andW (redPoprHatW ahub redRec p0r pr') (fun _ => redPoprHatW ahub redRec p0r pr))
              (fun _ => pureW false)
          | .cons6 h f1 _ =>
            ifW (lw ⟨Zfan0l, pl', pr'⟩ ⟨Zhatl, pl, pr⟩ zpnil (getrP f1 (getrP h sqt)))
              (fun _ => andW (redPoplFan1rW ahub redRec p0r pl' pr')
                (fun _ => redPoprHatW ahub redRec p0r pr))
            fun _ => ifW (lw ⟨Zhatr, pl', pr'⟩ ⟨Zfan0r, pl', pr'⟩ zpnil
                (getrP (getHat pr') (getrP f1 sqt)))
              (fun _ => andW (redPoprHatW ahub redRec p0r pr')
                (fun _ => redPoplFan1rW ahub redRec p0r pl' pr'))
              (fun _ => pureW false)
          | .cons7 h f1 f2 _ =>
            ifW (lw ⟨Zfan1l, pl', pr'⟩ ⟨Zhatl, pl, pr⟩ zpnil (getrP f1 (getrP h sqt)))
              (fun _ => andW (redPoplFan1rW ahub redRec p0r pl' pr')
                (fun _ => redPoprHatW ahub redRec p0r pr))
            fun _ => ifW (lw ⟨Zfan0l, pl', pr'⟩ ⟨Zfan0r, pl', pr'⟩ zpnil (getrP f2 (getrP f1 sqt)))
              (fun _ => andW (redPoplFan2rW ahub redRec p0r pl' pr')
                (fun _ => redPoplFan1rW ahub redRec p0r pl' pr'))
            fun _ => ifW (lw ⟨Zhatr, pl', pr'⟩ ⟨Zfan1r, pl', pr'⟩ zpnil
                (getrP (getHat pr') (getrP f2 sqt)))
              (fun _ => andW (redPoprHatW ahub redRec p0r pr')
                (fun _ => redPoplFan2rW ahub redRec p0r pl' pr'))
              (fun _ => pureW false)
          | .cons8 h f1 f2 f3 _ =>
            ifW (lw ⟨Zfan2l, pl', pr'⟩ ⟨Zhatl, pl, pr⟩ zpnil (getrP f1 (getrP h sqt)))
              (fun _ => andW (redPoplFan1rW ahub redRec p0r pl' pr')
                (fun _ => redPoprHatW ahub redRec p0r pr))
            fun _ => ifW (lw ⟨Zfan1l, pl', pr'⟩ ⟨Zfan0r, pl', pr'⟩ zpnil (getrP f2 (getrP f1 sqt)))
              (fun _ => andW (redPoplFan2rW ahub redRec p0r pl' pr')
                (fun _ => redPoplFan1rW ahub redRec p0r pl' pr'))
            fun _ => ifW (lw ⟨Zfan0l, pl', pr'⟩ ⟨Zfan1r, pl', pr'⟩ zpnil (getrP f3 (getrP f2 sqt)))
              (fun _ => andW (redPoplFan3rW ahub redRec p0r pl' pr')
                (fun _ => redPoplFan2rW ahub redRec p0r pl' pr'))
            fun _ => ifW (lw ⟨Zhatr, pl', pr'⟩ ⟨Zfan2r, pl', pr'⟩ zpnil
                (getrP (getHat pr') (getrP f3 sqt)))
              (fun _ => andW (redPoprHatW ahub redRec p0r pr')
                (fun _ => redPoplFan3rW ahub redRec p0r pl' pr'))
              (fun _ => pureW false)
          | _ => pureW false
      else pureW false
    -- a successful rotation needs its guard subtree, and the hub subtree if its first branch
    -- succeeded (then `leaf0` succeeded)
    let guards : Used :=
      .guard sqt.2 :: (if qztProper sqt.1 && leaf0.1 then [.guard (get1P ahub root).2] else [])
    if found.1 then (true, found.2 ++ guards)
    else let r := redZpartRecW qt ahub redRec p0l p0r zp' d'; (r.1, found.2 ++ r.2)

/-- `redZpart`, writer-style. -/
def redZpartW (qt : QuizTree) (ahub : Qarity) (redRec : Part → W) (p0l p0r : Part) : W :=
  redZpartRecW qt ahub redRec p0l p0r ⟨Zhub, dropPart 1 p0l, shiftPart p0l p0r⟩ ahub

/-- `redpart.loop`, writer-style. -/
def loopW (qt : QuizTree) (ahub : Qarity) : ℕ → Part → W
  | 0, _ => pureW false
  | d' + 1, p' => redZpartW qt ahub (loopW qt ahub d') (revPart p') p'

/-- `redpart qt p` and the quiz-tree leaves it uses. -/
def redpartW (qt : QuizTree) (p : Part) : W :=
  let nhub := sizePart p
  let ahub := qarityOfNat nhub
  if nhub == (ahub : ℕ) then loopW qt ahub (nhub * 12) p else pureW false

/-! ### Hubcaps (copies of `FourColor.Hubcap`) -/

/-- `checkDbound1Rec`, writer-style. -/
def checkDbound1RecW (redp : Part → W) (p : Part) (rs : Drules) (ns : ℕ) : ℕ → W
  | 0 => pureW false
  | m' + 1 =>
    match rs with
    | r :: rs' =>
      if rs'.length < ns then pureW true else
      let p' := meetPart p r
      andW (match sortDrules p' rs' with
        | ⟨dns, rs''⟩ =>
          match ns - dns with
          | ns' + 1 => checkDbound1RecW redp p' rs'' ns' m'
          | 0 => redp p')
        (fun _ => checkDbound1RecW redp p rs' ns m')
    | [] => pureW true

/-- `checkDbound1`, writer-style. -/
def checkDbound1W {nhub : ℕ} (redp : Part → W) (rf : DruleFork nhub) (p : Part) (ns : ℕ) : W :=
  checkDbound1RecW redp p rf.sourceDrules ns (rf.sourceDrules.length + 1)

/-- `checkDbound2Rec`, writer-style. -/
def checkDbound2RecW (redp : Part → W) (p : Part) (rt rs ru : Drules) (nt : ℕ) : ℕ → W
  | 0 => pureW false
  | m' + 1 =>
    match rt with
    | [] => pureW true
    | r :: rt' =>
      if rt'.length < nt then pureW true else
      let p' := meetPart p r
      andW (if checkUnfit p' ru then pureW true else
          match sortDrules p' rt', sortDrules p' rs with
          | ⟨dnt, rt''⟩, ⟨dns, rs'⟩ =>
            match dns + nt - dnt with
            | nt' + 1 => checkDbound2RecW redp p' rt'' rs' ru nt' m'
            | 0 => redp p')
        (fun _ => checkDbound2RecW redp p rt' rs (r :: ru) nt m')

/-- `checkDbound2`, writer-style. -/
def checkDbound2W {nhub : ℕ} (redp : Part → W) (rf : DruleFork nhub) (p : Part) (b : ℤ) : W :=
  match sortDrules p rf.targetDrules, sortDrules p rf.sourceDrules with
  | ⟨dnt, rt'⟩, ⟨dns, rs'⟩ =>
    match (dns : ℤ) - (dnt : ℤ) + b with
    | .ofNat nt => checkDbound2RecW redp p rt' rs' [] nt (rt'.length + 2)
    | .negSucc _ => pureW false

/-- `check2Dbound2Rec`, writer-style. -/
def check2Dbound2RecW (nhub : ℕ) (redp : Part → W) (p1 p2 : Part)
    (rt1 rs1 ru1 rt2 rs2 ru2 : Drules) (i nt : ℕ) : ℕ → W
  | 0 => pureW false
  | m' + 1 =>
    match rt1 with
    | [] =>
      match rt2 with
      | [] => pureW true
      | _ :: _ => check2Dbound2RecW nhub redp p2 p1 rt2 rs2 ru2 rt1 rs1 ru1 (nhub - i) nt m'
    | r :: rt1' =>
      if rt1'.length + rt2.length < nt then pureW true else
      let p1' := meetPart p1 r
      let p2' := rotPart i p1'
      andW (if checkUnfit p1' ru1 || checkUnfit p2' ru2 then pureW true else
          match sortDrules p1' rt1', sortDrules p1' rs1, sortDrules p2' rt2, sortDrules p2' rs2 with
          | ⟨dnt1, rt1''⟩, ⟨dns1, rs1'⟩, ⟨dnt2, rt2'⟩, ⟨dns2, rs2'⟩ =>
            match dns1 + (dns2 + nt) - (dnt1 + dnt2) with
            | nt' + 1 => check2Dbound2RecW nhub redp p1' p2' rt1'' rs1' ru1 rt2' rs2' ru2 i nt' m'
            | 0 => redp p1')
        (fun _ => check2Dbound2RecW nhub redp p1 p2 rt1' rs1 (r :: ru1) rt2 rs2 ru2 i nt m')

/-- `check2Dbound2`, writer-style. -/
def check2Dbound2W {nhub : ℕ} (redp : Part → W) (rf : DruleFork nhub) (p1 : Part) (i : ℕ)
    (b : ℤ) : W :=
  let p2 := rotPart i p1
  match sortDrules p1 rf.targetDrules, sortDrules p1 rf.sourceDrules,
      sortDrules p2 rf.targetDrules, sortDrules p2 rf.sourceDrules with
  | ⟨dnt1, rt1⟩, ⟨dns1, rs1⟩, ⟨dnt2, rt2⟩, ⟨dns2, rs2⟩ =>
    match ((dns1 + dns2 : ℕ) : ℤ) - ((dnt1 + dnt2 : ℕ) : ℤ) + b with
    | .ofNat nt =>
      check2Dbound2RecW nhub redp p1 p2 rt1 rs1 [] rt2 rs2 [] i nt (rt1.length + (rt2.length + 3))
    | .negSucc _ => pureW false

/-- `hubcapFit`, writer-style. -/
def hubcapFitW {nhub : ℕ} (redp : Part → W) (rf : DruleFork nhub) (p : Part) : Hubcap → W
  | .cons1 j b hc' =>
    andW (checkDbound2W redp rf (hubcapRot nhub j p) b) (fun _ => hubcapFitW redp rf p hc')
  | .cons2 j1 j2 b hc' =>
    andW (check2Dbound2W redp rf (hubcapRot nhub j1 p) (hubSubn nhub j2 j1) b)
      (fun _ => hubcapFitW redp rf p hc')
  | .nil => pureW true

/-- `hubcapCover nhub hc && hubcapFit (redpart qt) rf p hc` and the quiz-tree leaves it uses. -/
def hubcapW {nhub : ℕ} (qt : QuizTree) (rf : DruleFork nhub) (p : Part) (hc : Hubcap) : W :=
  if hubcapCover nhub hc then hubcapFitW (redpartW qt) rf p hc else pureW false

/-! ### Masks -/

/-- The skip counts selecting the sorted, duplicate-free indices `is` (after the index `prev`,
or from the start if `prev` is `none`). -/
def skipsOf : Option ℕ → List ℕ → List ℕ
  | _, [] => []
  | none, i :: is => i :: skipsOf (some i) is
  | some j, i :: is => (i - j - 1) :: skipsOf (some i) is

/-- The indices used in the leaf list at `path`, sorted and without duplicates. -/
def usedAt (used : Used) (path : List ℕ) : List ℕ :=
  ((used.filterMap fun
    | .leaf p i => if p == path then some i else none
    | .guard _ => none).mergeSort (· ≤ ·)).eraseDups

/-- The paths of the guard subtrees: the subtrees for the spoke arities 5 to 8 (the children of
the first subtree of the hub node) and the subtrees for the hub arities 9 to 11. -/
def guardPaths : List (List ℕ) := [[0, 0], [0, 1], [0, 2], [0, 3], [1], [2], [3]]

/-- The mask of `qt` (at path `path`) keeping the leaves `used`, and, if `guards`, removing the
guard subtrees that `used` does not keep. -/
def maskOfAt (guards : Bool) (used : Used) : QuizTree → List ℕ → QztMask
  | QztNode a b c d, path | QztHubNode a b c d, path =>
    if guards && guardPaths.contains path && !used.contains (.guard path) then .nil else
    let ma := maskOfAt guards used a (path ++ [0])
    let mb := maskOfAt guards used b (path ++ [1])
    let mc := maskOfAt guards used c (path ++ [2])
    let md := maskOfAt guards used d (path ++ [3])
    if ma == .none && mb == .none && mc == .none && md == .none then .none
    else .node ma mb mc md
  | QztLeaf .., path =>
    match usedAt used path with
    | [] => .none
    | is => .leaves (skipsOf none is)
  | QztNil, _ => .none

/-- The mask of `qt` keeping the leaves `used` (and, if `guards`, removing the guard subtrees
that `used` does not keep; this skips the failing rotations of the searches, but measured no
faster in the kernel, so it is off by default). -/
def maskOf (qt : QuizTree) (used : Used) (guards : Bool := false) : QztMask :=
  maskOfAt guards used qt []

/-- The pruning mask of the check `redpart qt p`. -/
def redpartMask (qt : QuizTree) (p : Part) (guards : Bool := false) : QztMask :=
  maskOf qt (redpartW qt p).2 guards

/-- The pruning mask of the hubcap check of `p` with `hc`. -/
def hubcapMask {nhub : ℕ} (qt : QuizTree) (rf : DruleFork nhub) (p : Part) (hc : Hubcap)
    (guards : Bool := false) : QztMask :=
  maskOf qt (hubcapW qt rf p hc).2 guards

end FourColor.PruneGen
