/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.CheckChunk

/-!
# Reducibility engine: the Kempe step on row-group chunks

Palomar's checker nanoda computes `x >>> d` as a long division by `2 ^ d`, whose cost grows like
`|x >>> d| * d`.  The Kempe step `kempeGrade` (`KempeStep.lean`) flips the ranks of a whole
grade with right shifts by up to half its size (`512 512` bits for grade 5 at ring size 14), so
nanoda spends seconds per ring-14 round on it.  This file computes the same function,
`kempeGradeB r k q = kempeGrade r k q` (`kempeGradeB_eq`), without big right shifts.

**Row groups.**  In grade `k ≥ 1` (`m = 2k` ranks, rows of `B = choose r m` bits, rows
`xp < 2 ^ (m-1)`), the `g` top bits of the row are the *chunk index*: the grade is cut into
`2 ^ g` chunks of `S = 2 ^ c * B` bits (`c = m - 1 - g` row bits inside a chunk), held in a
binary tree `KT` of height `g` (`toTree`, balanced halving).  Flipping a rank `l > c` exchanges
chunks (`i ↦ i ^^^ 2 ^ (l-1-c)`): it only walks the tree (`satT`, bits of the chunk-index xor
top first); flipping a rank `1 ≤ l ≤ c` acts inside every chunk; `chordSat`, the accumulator
`acc &&& y`, … act chunk by chunk.

**Offsets.**  For the grades of more than `2 ^ 14` bits (*offset mode*), a chunk carries an
offset `o`: the chunk is `leaf >>> o`.  A flip of rank `l` (pair distance `w`) from offset `o`
leaves the upper elements of its pairs in place and moves the lower ones up by `2 * w`, giving
offset `o + w` (`fBox`, with the masks `lo <<< o`); the saturation moves the other operand up
by the chord's shift.  So the enumeration has no right shift at all; along any perfect matching
every rank `1 … c` is flipped once, so every saturation ends at offset `S - B`, where the
accumulator lives (`alignT` would move a tree otherwise), and each chunk is shifted down once
at the end (`ofTreeAt`).  Small grades (*translation mode*, here with `g = 0`) use the ordinary
translation `xlate` inside the chunks, whose right shifts are then cheap.

**Chunking rule** (`kempeGradeB`): `g` is the number of halvings of the grade (at most `m - 1`)
until it has at most `2 ^ 16` bits (`kLevels`).  At ring size 14: grade 3 → `g = 1` (chunks of
48 048 bits), grade 4 → 3 (48 048), grade 5 → 3 (64 064), grade 6 → 2 (46 592), grades 1, 2, 7
→ 0 (grade 7, 8 192 bits, in translation mode).  The conversion `toTree` costs nanoda about
`L² / 2` bit operations per grade (`L` bits), once per round.

**Kernel style.**  Everything evaluated by the kernel is written with recursors (`Nat.rec`,
`List.rec`, `Bool.rec`, `KT.rec`, `KOp.rec`, `FBox.rec`) and the `Nat` primitives, and is
`noncomputable`.  The enumeration `kE`/`kLoop` is `ncmFold`'s, walking suffixes of the list of
rank ops (`kop`) instead of rank indices.  The first rank `a` of a loop is flipped first, and the
flip functions of a chord are built once in a box (`FBox`) so that the kernel substitutes plain
lambdas; the flip of `a` is then shared through the kernel's caches by the chords `(a, b)` of
the loop.

**Correctness** (for any chunking thresholds, `kempeGradeBT_eq`).  `getL` reads the leaves of a
tree and `testBit_ofTreeAt` the bits of the number it represents; `WinF` states how a flip
function moves the bits of a chunk between offsets (`winF_xlate`, `winF_flip`); `rowX` is the
row xor, which characterizes `chordSat` (`testBit_chordSat_rowX`) and splits into a chunk-index
xor and a row xor inside the chunk (`rowX_split`), so a chunked chord saturation is a chord
saturation (`ofTreeAt_satK`); `kE_eq` shows that `kE` folds over the matchings `ncm` in order.
Then `kempeStepB`, `roundB`, `roundsNB`, `checkStepB` are `kempeStep`, `roundC`, `roundsNC`,
`checkStepC` with the chunked Kempe step, and `checkStep_eq_checkStepB` proves the ordinary
checkpoint step through them.
-/

namespace FourColor.Engine

open FourColor

/-! ### Chunk trees -/

/-- A binary tree of chunks: a grade cut into `2 ^ h` row groups is a tree of height `h`
whose left subtree holds the lower half of the rows. -/
inductive KT : Type where
  | leaf : Nat → KT
  | node : KT → KT → KT

namespace KT

/-- The chunk of a leaf (`0` for a node). -/
noncomputable def val (t : KT) : Nat :=
  KT.rec (motive := fun _ => Nat) (fun x => x) (fun _ _ _ _ => 0) t

/-- The left subtree (`leaf 0` for a leaf). -/
noncomputable def lft (t : KT) : KT :=
  KT.rec (motive := fun _ => KT) (fun _ => leaf 0) (fun l _ _ _ => l) t

/-- The right subtree (`leaf 0` for a leaf). -/
noncomputable def rgt (t : KT) : KT :=
  KT.rec (motive := fun _ => KT) (fun _ => leaf 0) (fun _ r _ _ => r) t

end KT

/-- Balanced halving of `x` into the tree of height `h` of its chunks of `S` bits (the top
chunk is not truncated). -/
noncomputable def toTree (S : Nat) (h : Nat) : Nat → KT :=
  Nat.rec (motive := fun _ => Nat → KT)
    (fun x => KT.leaf x)
    (fun h ih x =>
      (fun d hi => KT.node (ih (Nat.xor x (Nat.shiftLeft hi d))) (ih hi))
        (Nat.mul (Nat.pow 2 h) S) (Nat.shiftRight x (Nat.mul (Nat.pow 2 h) S))) h

/-- `ofTreeAt S O h t`: the number whose chunk `i` of `S` bits is leaf `i` of the tree `t` of
height `h` read at offset `O`, i.e. `(leaf_i >>> O) &&& ones S`. -/
noncomputable def ofTreeAt (S O : Nat) (h : Nat) : KT → Nat :=
  Nat.rec (motive := fun _ => KT → Nat)
    (fun t => Nat.land (Nat.shiftRight (KT.val t) O) (ones S))
    (fun h ih t => Nat.lor (ih (KT.lft t))
      (Nat.shiftLeft (ih (KT.rgt t)) (Nat.mul (Nat.pow 2 h) S))) h

/-- The tree of height `h` all of whose leaves are `x`. -/
noncomputable def constT (x : Nat) (h : Nat) : KT :=
  Nat.rec (motive := fun _ => KT) (KT.leaf x) (fun _ ih => KT.node ih ih) h

/-- `f` on the leaves of a tree of height `h`. -/
noncomputable def mapT (f : Nat → Nat) (h : Nat) : KT → KT :=
  Nat.rec (motive := fun _ => KT → KT)
    (fun t => KT.leaf (f (KT.val t)))
    (fun _ ih t => KT.node (ih (KT.lft t)) (ih (KT.rgt t))) h

/-- Pointwise `&&&` of two trees of height `h`. -/
noncomputable def andT (h : Nat) : KT → KT → KT :=
  Nat.rec (motive := fun _ => KT → KT → KT)
    (fun t u => KT.leaf (Nat.land (KT.val t) (KT.val u)))
    (fun _ ih t u => KT.node (ih (KT.lft t) (KT.lft u)) (ih (KT.rgt t) (KT.rgt u))) h

/-- `satT G F δs t u`: the tree whose leaf `i` is `G t_i ||| F u_{i ^^^ δ}`, the bits of `δ`
given top first by `δs` (its length is the height). -/
noncomputable def satT (G F : Nat → Nat) : List Bool → KT → KT → KT :=
  List.rec (motive := fun _ => KT → KT → KT)
    (fun t u => KT.leaf (Nat.lor (G (KT.val t)) (F (KT.val u))))
    (fun b _ ih t u => Bool.rec
      (KT.node (ih (KT.lft t) (KT.lft u)) (ih (KT.rgt t) (KT.rgt u)))
      (KT.node (ih (KT.lft t) (KT.rgt u)) (ih (KT.rgt t) (KT.lft u))) b)

/-- Moving a tree of height `h` from offset `o` to offset `O`. -/
noncomputable def alignT (O o h : Nat) (y : KT) : KT :=
  Bool.rec
    (mapT (fun x => Bool.rec (Nat.shiftRight x (Nat.sub o O)) (Nat.shiftLeft x (Nat.sub O o))
      (Nat.ble o O)) h y)
    y (Nat.beq o O)

/-! ### Rank flips -/

/-- A rank flip on chunk trees: whether it acts inside the chunks, with the mask `lo` of the
lower elements of its pairs and their distance `w`, and the chunk-index bits it flips (top
bit first). -/
structure KOp where
  /-- Acts inside the chunks. -/
  inC : Bool
  /-- The mask of the lower elements of the pairs, inside a chunk. -/
  lo : Nat
  /-- The distance of the pairs. -/
  w : Nat
  /-- The chunk-index bits flipped, top first. -/
  bits : List Bool

/-- A function in a box: the kernel evaluates the box once and substitutes the lambda it
holds. -/
structure FBox where
  /-- The function. -/
  f : Nat → Nat

/-- The flip of an op on a chunk at offset `o`, boxed.  In translation mode (`om = false`,
offset `0`) it is `xlate lo w`; in offset mode it goes from offset `o` to offset `o + w`: with
`M = lo <<< o`, the upper elements of the pairs (`M <<< w`) stay in place and the lower ones
(`M`) move up by `2 * w`, so there is no right shift.  The identity for the other ops. -/
noncomputable def fBox (om : Bool) (op : KOp) (o : Nat) : FBox :=
  KOp.rec (motive := fun _ => FBox) (fun i lo w _ =>
    Bool.rec (FBox.mk fun x => x)
      (Bool.rec
        (FBox.mk fun x => Nat.lor (Nat.shiftLeft (Nat.land x lo) w)
          (Nat.land (Nat.shiftRight x w) lo))
        (FBox.mk fun x => Nat.lor (Nat.land x (Nat.shiftLeft (Nat.shiftLeft lo o) w))
          (Nat.shiftLeft (Nat.land x (Nat.shiftLeft lo o)) (Nat.add w w))) om)
      i) op

/-- The shift by `W` (the identity for `W = 0`), boxed. -/
noncomputable def gBox (W : Nat) : FBox :=
  Bool.rec (FBox.mk fun x => Nat.shiftLeft x W) (FBox.mk fun x => x) (Nat.beq W 0)

/-- The offset increment of an op (`om`: offset mode). -/
noncomputable def wOp (om : Bool) (op : KOp) : Nat :=
  KOp.rec (motive := fun _ => Nat) (fun i _ w _ => Bool.rec 0 (Bool.rec 0 w i) om) op

/-- Pointwise xor of two bit lists. -/
noncomputable def xorBits : List Bool → List Bool → List Bool :=
  List.rec (motive := fun _ => List Bool → List Bool) (fun _ => [])
    (fun a _ ih l => List.rec (motive := fun _ => List Bool) []
      (fun b l' _ => Bool.rec b (Bool.rec true false b) a :: ih l') l)

/-- The saturation under the chord `(a, b)` (ops `oa`, `ob`) of a tree at offset `o`; the
result is at offset `o + wOp om oa + wOp om ob`.  The rank `a` is flipped first: its flip is
shared (through the kernel's caches) by the chords `(a, b)` of a loop of `kE`. -/
noncomputable def satK (om : Bool) (oa ob : KOp) (o : Nat) (y : KT) : KT :=
  FBox.rec (motive := fun _ => KT) (fun Fa =>
  FBox.rec (motive := fun _ => KT) (fun Fb =>
  FBox.rec (motive := fun _ => KT) (fun G =>
    satT G (fun x => Fb (Fa x)) (xorBits (KOp.bits oa) (KOp.bits ob)) y y)
    (gBox (Nat.add (wOp om oa) (wOp om ob))))
    (fBox om ob (Nat.add o (wOp om oa))))
    (fBox om oa o)

/-- Tail of a list of ops. -/
noncomputable def tailK (l : List KOp) : List KOp :=
  List.rec (motive := fun _ => List KOp) [] (fun _ l' _ => l') l

/-- The loop of `kE` over the chords `(a, b)` of its first rank `a` (op `oa`, the ops after it
`rest`): `cnt` chords are left, `opsB` are the ops from `b` on, `i` is the number of ranks
inside the chord; `E` is the enumeration with one less fuel. -/
noncomputable def kLoop (sat : KOp → KOp → Nat → KT → KT) (wd : KOp → KOp → Nat)
    (E : List KOp → Nat → KT → Nat → KT → (KT → Nat → KT → KT) → KT)
    (oa : KOp) (rest : List KOp) (y : KT) (o : Nat) (k : KT → Nat → KT → KT) :
    Nat → List KOp → Nat → KT → KT :=
  Nat.rec (motive := fun _ => List KOp → Nat → KT → KT)
    (fun _ _ acc => acc)
    (fun cnt loop opsB i acc =>
      List.rec (motive := fun _ => KT) acc
        (fun ob opsB' _ =>
          loop (tailK opsB') (Nat.add i 2)
            (E rest i (sat oa ob o y) (Nat.add o (wd oa ob)) acc
              (fun y' o' acc' => E opsB' (Nat.add cnt cnt) y' o' acc' k)))
        opsB)

/-- Continuation-passing enumeration of the non-crossing perfect matchings of the first `n`
ranks of `ops` (for `fuel ≥ n`), in the order of `ncm`, on trees with offsets: for each
matching `M`, `acc ← k y' o' acc` where `(y', o')` is the saturation of `(y, o)` along `M`
(`sat`, offset increments `wd`).  Chord prefixes are shared between matchings. -/
noncomputable def kE (sat : KOp → KOp → Nat → KT → KT) (wd : KOp → KOp → Nat) :
    Nat → List KOp → Nat → KT → Nat → KT → (KT → Nat → KT → KT) → KT :=
  Nat.rec (motive := fun _ =>
      List KOp → Nat → KT → Nat → KT → (KT → Nat → KT → KT) → KT)
    (fun _ _ y o acc k => k y o acc)
    (fun _ ih ops n y o acc k =>
      Bool.rec
        (List.rec (motive := fun _ => KT) (k y o acc)
          (fun oa rest _ => kLoop sat wd ih oa rest y o k (Nat.div n 2) rest 0 acc) ops)
        (k y o acc)
        (Nat.beq n 0))

/-- The bits (top first) of the chunk index `2 ^ j` among `g` bits. -/
def oneHot (g j : Nat) : List Bool := (List.range g).reverse.map (· == j)

/-- The op of rank `l` in a grade with rows of `B` bits cut into chunks of `2 ^ c` rows
(`S = 2 ^ c * B` bits) and `g` chunk-index bits. -/
noncomputable def kop (B c g S l : Nat) : KOp :=
  if l = 0 then ⟨false, 0, 0, List.replicate g false⟩
  else if l ≤ c then
    ⟨true, pmask S (2 * (2 ^ (l - 1) * B)) (2 ^ (l - 1) * B), 2 ^ (l - 1) * B,
      List.replicate g false⟩
  else ⟨false, 0, 0, oneHot g (l - 1 - c)⟩

/-- The number of halvings (at most `f`) cutting `L` bits into chunks of at most `T` bits. -/
noncomputable def kLevels (T : Nat) (f : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih L => Bool.rec (Nat.succ (ih (Nat.div L 2))) 0 (Nat.ble L T)) f

/-- The chunked Kempe step of grade `k` (`k ≥ 1`): chunks of at most `T` bits, offset mode for
grades of more than `Tx` bits. -/
noncomputable def kempeGradeKT (T Tx r k q : Nat) : Nat :=
  let m := 2 * k
  let B := chooseAux r m
  let L := 2 ^ (m - 1) * B
  let g := kLevels T (m - 1) L
  let c := m - 1 - g
  let S := 2 ^ c * B
  let om := Nat.blt Tx L
  let O := Bool.rec 0 (S - B) om
  ofTreeAt S O g (kE (satK om) (fun oa ob => Nat.add (wOp om oa) (wOp om ob)) m
    ((List.range m).map (kop B c g S)) m (toTree S g q) 0 (constT (ones (O + S)) g)
    (fun y o acc => andT g acc (alignT O o g y)))

/-- The chunked Kempe step (any `T`, `Tx`). -/
noncomputable def kempeGradeBT (T Tx r k q : Nat) : Nat :=
  Bool.rec (kempeGradeKT T Tx r k q) q (Nat.beq k 0)

/-- The chunked Kempe step with the chunking rule of the certificates: chunks of at most
`2 ^ 16` bits, offset mode for the grades of more than `2 ^ 14` bits. -/
noncomputable def kempeGradeB (r k q : Nat) : Nat := kempeGradeBT 65536 16384 r k q

/-- The chunked Kempe step on all grades. -/
noncomputable def kempeStepB (r : Nat) (X : List Nat) : List Nat := mapGrades (kempeGradeB r) X

/-- `roundC` with the chunked Kempe step. -/
noncomputable def roundB (r s : Nat) (net : NetC) (X : List Nat) : List Nat :=
  permCloseKC r s net (kempeStepB r X)

/-- `roundsNC` with the chunked Kempe step. -/
noncomputable def roundsNB (r s : Nat) (net : NetC) : Nat → List Nat → List Nat
  | 0, X => X
  | n + 1, X => roundsNB r s net n (roundB r s net X)

/-- `checkStepC` with the chunked Kempe step. -/
noncomputable def checkStepB (r s : Nat) (net : NetC) (n : Nat) (H H' : List Nat) : Bool :=
  roundsNB r s net n (expand r H) == expand r H'

/-! ## Proofs -/

/-! ### Equations of the kernel-evaluated functions -/

namespace KT

@[simp] private theorem val_leaf (x : Nat) : (leaf x).val = x := rfl
@[simp] private theorem val_node (l r : KT) : (node l r).val = 0 := rfl
@[simp] private theorem lft_leaf (x : Nat) : (leaf x).lft = leaf 0 := rfl
@[simp] private theorem lft_node (l r : KT) : (node l r).lft = l := rfl
@[simp] private theorem rgt_leaf (x : Nat) : (leaf x).rgt = leaf 0 := rfl
@[simp] private theorem rgt_node (l r : KT) : (node l r).rgt = r := rfl

end KT

private theorem toTree_zero (S x : Nat) : toTree S 0 x = KT.leaf x := rfl

private theorem toTree_succ (S h x : Nat) : toTree S (h + 1) x =
    KT.node (toTree S h (x ^^^ ((x >>> (2 ^ h * S)) <<< (2 ^ h * S))))
      (toTree S h (x >>> (2 ^ h * S))) := rfl

private theorem ofTreeAt_zero (S O : Nat) (t : KT) :
    ofTreeAt S O 0 t = (t.val >>> O) &&& ones S := rfl

private theorem ofTreeAt_succ (S O h : Nat) (t : KT) : ofTreeAt S O (h + 1) t =
    ofTreeAt S O h t.lft ||| (ofTreeAt S O h t.rgt <<< (2 ^ h * S)) := rfl

private theorem constT_zero (x : Nat) : constT x 0 = KT.leaf x := rfl

private theorem constT_succ (x h : Nat) :
    constT x (h + 1) = KT.node (constT x h) (constT x h) := rfl

private theorem mapT_zero (f : Nat → Nat) (t : KT) : mapT f 0 t = KT.leaf (f t.val) := rfl

private theorem mapT_succ (f : Nat → Nat) (h : Nat) (t : KT) :
    mapT f (h + 1) t = KT.node (mapT f h t.lft) (mapT f h t.rgt) := rfl

private theorem andT_zero (t u : KT) : andT 0 t u = KT.leaf (t.val &&& u.val) := rfl

private theorem andT_succ (h : Nat) (t u : KT) :
    andT (h + 1) t u = KT.node (andT h t.lft u.lft) (andT h t.rgt u.rgt) := rfl

private theorem satT_nil (G F : Nat → Nat) (t u : KT) :
    satT G F [] t u = KT.leaf (G t.val ||| F u.val) := rfl

private theorem satT_cons_false (G F : Nat → Nat) (bs : List Bool) (t u : KT) :
    satT G F (false :: bs) t u = KT.node (satT G F bs t.lft u.lft) (satT G F bs t.rgt u.rgt) :=
  rfl

private theorem satT_cons_true (G F : Nat → Nat) (bs : List Bool) (t u : KT) :
    satT G F (true :: bs) t u = KT.node (satT G F bs t.lft u.rgt) (satT G F bs t.rgt u.lft) :=
  rfl

/-! ### Leaves of a tree -/

/-- The leaf `i` of a tree of height `h`, the bits of `i` read from the top (the left subtree
holds the leaves `i < 2 ^ (h - 1)`). -/
private noncomputable def getL : Nat → KT → Nat → Nat
  | 0, t, _ => t.val
  | h + 1, t, i => if i < 2 ^ h then getL h t.lft i else getL h t.rgt (i - 2 ^ h)

private theorem getL_zero (t : KT) (i : Nat) : getL 0 t i = t.val := rfl

private theorem getL_succ_lo {h i : Nat} (hi : i < 2 ^ h) (t : KT) :
    getL (h + 1) t i = getL h t.lft i := by
  simp [getL, hi]

private theorem getL_succ_hi (h i : Nat) (t : KT) :
    getL (h + 1) t (2 ^ h + i) = getL h t.rgt i := by
  simp [getL]

/-- The bits of `ofTreeAt`: bit `p` is bit `O + p % S` of leaf `p / S`. -/
private theorem testBit_ofTreeAt {S : Nat} (hS : 0 < S) (O : Nat) :
    ∀ (h : Nat) (t : KT) (p : Nat), (ofTreeAt S O h t).testBit p =
      (decide (p < 2 ^ h * S) && (getL h t (p / S)).testBit (O + p % S)) := by
  intro h
  induction h with
  | zero =>
    intro t p
    rw [ofTreeAt_zero, Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones, getL_zero]
    by_cases hp : p < S
    · rw [Nat.mod_eq_of_lt hp]; simp [hp, Bool.and_comm]
    · simp [hp]
  | succ h ih =>
    intro t p
    rw [ofTreeAt_succ, Nat.testBit_or, Nat.testBit_shiftLeft, ih, ih]
    have e0 : 2 ^ (h + 1) * S = 2 ^ h * S + 2 ^ h * S := by rw [Nat.pow_succ]; ring
    by_cases hp : p < 2 ^ h * S
    · have h1 : p / S < 2 ^ h := (Nat.div_lt_iff_lt_mul hS).2 hp
      have h2 : p < 2 ^ (h + 1) * S := by rw [e0]; omega
      have h3 : ¬ p ≥ 2 ^ h * S := by omega
      rw [getL_succ_lo h1]
      simp only [hp, h2, h3, decide_true, decide_false, Bool.true_and, Bool.false_and,
        Bool.or_false]
    · obtain ⟨p', rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hp)
      have e1 : (2 ^ h * S + p') / S = 2 ^ h + p' / S := by
        rw [Nat.mul_comm, Nat.mul_add_div hS]
      have e2 : (2 ^ h * S + p') % S = p' % S := by
        rw [Nat.mul_comm, Nat.mul_add_mod]
      have h3 : 2 ^ h * S + p' ≥ 2 ^ h * S := Nat.le_add_right _ _
      rw [e1, e2, getL_succ_hi, Nat.add_sub_cancel_left]
      by_cases hq : p' < 2 ^ h * S
      · have h4 : 2 ^ h * S + p' < 2 ^ (h + 1) * S := by rw [e0]; omega
        simp only [hp, h3, hq, h4, decide_true, decide_false, Bool.true_and, Bool.false_and,
          Bool.false_or]
      · have h4 : ¬ 2 ^ h * S + p' < 2 ^ (h + 1) * S := by rw [e0]; omega
        simp only [hp, h3, hq, h4, decide_true, decide_false, Bool.true_and, Bool.false_and,
          Bool.false_or]

/-! ### The operations on trees, leaf by leaf -/

private theorem getL_toTree {S : Nat} : ∀ (h x i p : Nat), i < 2 ^ h → p < S →
    (getL h (toTree S h x) i).testBit p = x.testBit (i * S + p) := by
  intro h
  induction h with
  | zero => intro x i p hi _; simp at hi; subst hi; simp [toTree_zero, getL_zero]
  | succ h ih =>
    intro x i p hi hp
    rw [toTree_succ]
    rcases Nat.lt_or_ge i (2 ^ h) with hlt | hge
    · rw [getL_succ_lo hlt, KT.lft_node, ih _ _ _ hlt hp, Nat.testBit_xor, Nat.testBit_shiftLeft]
      have : i * S + p < 2 ^ h * S := by
        have := Nat.mul_le_mul_right S (Nat.succ_le_of_lt hlt)
        rw [Nat.succ_mul] at this; omega
      simp [show ¬ (i * S + p ≥ 2 ^ h * S) by omega]
    · obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le hge
      have hi' : i' < 2 ^ h := by rw [Nat.pow_succ] at hi; omega
      rw [getL_succ_hi, KT.rgt_node, ih _ _ _ hi' hp, Nat.testBit_shiftRight]
      congr 1; rw [Nat.add_mul]; omega

private theorem getL_constT (x : Nat) : ∀ (h i : Nat), getL h (constT x h) i = x := by
  intro h
  induction h with
  | zero => intro i; rfl
  | succ h ih =>
    intro i
    rw [constT_succ]
    simp only [getL]
    split <;> simp [ih]

private theorem getL_andT : ∀ (h : Nat) (t u : KT) (i : Nat),
    getL h (andT h t u) i = getL h t i &&& getL h u i := by
  intro h
  induction h with
  | zero => intro t u i; rfl
  | succ h ih =>
    intro t u i
    rw [andT_succ]
    simp only [getL]
    split <;> simp [ih]

private theorem getL_mapT (f : Nat → Nat) : ∀ (h : Nat) (t : KT) (i : Nat),
    getL h (mapT f h t) i = f (getL h t i) := by
  intro h
  induction h with
  | zero => intro t i; rfl
  | succ h ih =>
    intro t i
    rw [mapT_succ]
    simp only [getL]
    split <;> simp [ih]

/-! ### The operations on trees, as numbers -/

private theorem ofTreeAt_toTree {S : Nat} (hS : 0 < S) (h x : Nat) :
    ofTreeAt S 0 h (toTree S h x) = x &&& ones (2 ^ h * S) := by
  apply Nat.eq_of_testBit_eq; intro p
  rw [testBit_ofTreeAt hS, Nat.testBit_and, testBit_ones]
  by_cases hp : p < 2 ^ h * S
  · have h1 : p / S < 2 ^ h := (Nat.div_lt_iff_lt_mul hS).2 hp
    rw [Nat.zero_add, getL_toTree _ _ _ _ h1 (Nat.mod_lt _ hS), Nat.div_add_mod' p S]
    simp [hp]
  · simp [hp]

private theorem ofTreeAt_constT {S : Nat} (hS : 0 < S) (O h : Nat) :
    ofTreeAt S O h (constT (ones (O + S)) h) = ones (2 ^ h * S) := by
  apply Nat.eq_of_testBit_eq; intro p
  rw [testBit_ofTreeAt hS, getL_constT, testBit_ones, testBit_ones]
  by_cases hp : p < 2 ^ h * S
  · have := Nat.mod_lt p hS
    simp [hp, this]
  · simp [hp]

private theorem ofTreeAt_andT {S : Nat} (hS : 0 < S) (O h : Nat) (t u : KT) :
    ofTreeAt S O h (andT h t u) = ofTreeAt S O h t &&& ofTreeAt S O h u := by
  apply Nat.eq_of_testBit_eq; intro p
  rw [Nat.testBit_and, testBit_ofTreeAt hS, testBit_ofTreeAt hS, testBit_ofTreeAt hS, getL_andT,
    Nat.testBit_and]
  cases decide (p < 2 ^ h * S) <;> simp

private theorem testBit_alignFn (O o x p : Nat) :
    (Bool.rec (Nat.shiftRight x (Nat.sub o O)) (Nat.shiftLeft x (Nat.sub O o)) (Nat.ble o O) :
      Nat).testBit (O + p) = x.testBit (o + p) := by
  cases h : Nat.ble o O
  · have hle : ¬ o ≤ O := fun h' => by
      rw [Nat.ble_eq_true_of_le h'] at h; exact Bool.noConfusion h
    show (x >>> (o - O)).testBit (O + p) = _
    rw [Nat.testBit_shiftRight]; congr 1; omega
  · have hle : o ≤ O := Nat.le_of_ble_eq_true h
    show (x <<< (O - o)).testBit (O + p) = _
    rw [Nat.testBit_shiftLeft]
    simp [show O + p ≥ O - o by omega, show O + p - (O - o) = o + p by omega]

private theorem ofTreeAt_alignT {S : Nat} (hS : 0 < S) (O o h : Nat) (y : KT) :
    ofTreeAt S O h (alignT O o h y) = ofTreeAt S o h y := by
  unfold alignT
  cases hb : Nat.beq o O
  · show ofTreeAt S O h (mapT _ h y) = _
    apply Nat.eq_of_testBit_eq; intro p
    rw [testBit_ofTreeAt hS, testBit_ofTreeAt hS, getL_mapT, testBit_alignFn]
  · have : o = O := Nat.eq_of_beq_eq_true hb
    subst this; rfl

/-! ### Chord saturation on trees -/

/-- The number whose bits (top first) are `bs`. -/
private def bitsN : List Bool → Nat
  | [] => 0
  | b :: bs => 2 ^ bs.length * (if b then 1 else 0) + bitsN bs

private theorem bitsN_lt : ∀ bs : List Bool, bitsN bs < 2 ^ bs.length
  | [] => by simp [bitsN]
  | b :: bs => by
    have := bitsN_lt bs
    simp only [bitsN, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

/-- Xor of numbers cut at bit `c`. -/
private theorem xor_two_pow_mul_add {c a b : Nat} (x y : Nat) (ha : a < 2 ^ c) (hb : b < 2 ^ c) :
    (2 ^ c * x + a) ^^^ (2 ^ c * y + b) = 2 ^ c * (x ^^^ y) + (a ^^^ b) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ hb,
    Nat.testBit_two_pow_mul_add _ (Nat.xor_lt_two_pow ha hb), Nat.testBit_xor, Nat.testBit_xor]
  split <;> rfl

private theorem getL_satT (G F : Nat → Nat) : ∀ (δs : List Bool) (t u : KT) (i : Nat),
    i < 2 ^ δs.length → getL δs.length (satT G F δs t u) i =
      G (getL δs.length t i) ||| F (getL δs.length u (i ^^^ bitsN δs)) := by
  intro δs
  induction δs with
  | nil =>
    intro t u i hi
    simp only [List.length_nil, Nat.pow_zero, Nat.lt_one_iff] at hi
    subst hi
    rfl
  | cons b bs ih =>
    intro t u i hi
    simp only [List.length_cons] at hi ⊢
    have hδ := bitsN_lt bs
    rcases Nat.lt_or_ge i (2 ^ bs.length) with hlt | hge
    · rw [getL_succ_lo hlt, getL_succ_lo hlt]
      cases b
      · rw [satT_cons_false, KT.lft_node, ih _ _ _ hlt]
        have hx : i ^^^ bitsN (false :: bs) = i ^^^ bitsN bs := by simp [bitsN]
        rw [hx, getL_succ_lo (Nat.xor_lt_two_pow hlt hδ)]
      · rw [satT_cons_true, KT.lft_node, ih _ _ _ hlt]
        have hx : i ^^^ bitsN (true :: bs) = 2 ^ bs.length + (i ^^^ bitsN bs) := by
          have := xor_two_pow_mul_add (c := bs.length) 0 1 hlt hδ
          simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one, Nat.zero_xor] at this
          simp only [bitsN, ite_true, Nat.mul_one]
          exact this
        rw [hx, getL_succ_hi]
    · obtain ⟨i', rfl⟩ := Nat.exists_eq_add_of_le hge
      have hi' : i' < 2 ^ bs.length := by rw [Nat.pow_succ] at hi; omega
      rw [getL_succ_hi, getL_succ_hi]
      cases b
      · rw [satT_cons_false, KT.rgt_node, ih _ _ _ hi']
        have hx : (2 ^ bs.length + i') ^^^ bitsN (false :: bs) =
            2 ^ bs.length + (i' ^^^ bitsN bs) := by
          have := xor_two_pow_mul_add (c := bs.length) 1 0 hi' hδ
          simp only [Nat.mul_one, Nat.mul_zero, Nat.zero_add, Nat.xor_zero] at this
          simp only [bitsN, Bool.false_eq_true, ite_false, Nat.mul_zero, Nat.zero_add]
          exact this
        rw [hx, getL_succ_hi]
      · rw [satT_cons_true, KT.rgt_node, ih _ _ _ hi']
        have hx : (2 ^ bs.length + i') ^^^ bitsN (true :: bs) = i' ^^^ bitsN bs := by
          have := xor_two_pow_mul_add (c := bs.length) 1 1 hi' hδ
          simp only [Nat.mul_one, Nat.xor_self, Nat.mul_zero, Nat.zero_add] at this
          simp only [bitsN, ite_true, Nat.mul_one]
          exact this
        rw [hx, getL_succ_lo (Nat.xor_lt_two_pow hi' hδ)]

/-- `F` moves a chunk from offset `o` to offset `o'`, bit `p < S` coming from bit `π p`. -/
private def WinF (S o o' : Nat) (π : Nat → Nat) (F : Nat → Nat) : Prop :=
  ∀ x p, p < S → (F x).testBit (o' + p) = x.testBit (o + π p)

/-- The bits of a chord saturation on trees. -/
private theorem testBit_ofTreeAt_satT {S o o' h : Nat} (hS : 0 < S) {π G F : Nat → Nat}
    {δs : List Bool} (hlen : δs.length = h)
    (hG : WinF S o o' id G) (hF : WinF S o o' π F) (hπ : ∀ p, p < S → π p < S) (y : KT)
    (p : Nat) :
    (ofTreeAt S o' h (satT G F δs y y)).testBit p =
      ((ofTreeAt S o h y).testBit p || (decide (p < 2 ^ h * S) &&
        (ofTreeAt S o h y).testBit ((p / S ^^^ bitsN δs) * S + π (p % S)))) := by
  subst hlen
  rw [testBit_ofTreeAt hS, testBit_ofTreeAt hS, testBit_ofTreeAt hS]
  by_cases hp : p < 2 ^ δs.length * S
  · have h1 : p / S < 2 ^ δs.length := (Nat.div_lt_iff_lt_mul hS).2 hp
    have hx := Nat.xor_lt_two_pow h1 (bitsN_lt δs)
    have hm := Nat.mod_lt p hS
    have hπ' := hπ _ hm
    have hP : (p / S ^^^ bitsN δs) * S + π (p % S) < 2 ^ δs.length * S := by
      have := Nat.mul_le_mul_right S (Nat.succ_le_of_lt hx)
      rw [Nat.succ_mul] at this; omega
    have e1 : ((p / S ^^^ bitsN δs) * S + π (p % S)) / S = p / S ^^^ bitsN δs := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hS, Nat.div_eq_of_lt hπ', Nat.zero_add]
    have e2 : ((p / S ^^^ bitsN δs) * S + π (p % S)) % S = π (p % S) := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hπ']
    rw [getL_satT _ _ _ _ _ _ h1, Nat.testBit_or, hG _ _ hm, hF _ _ hm, e1, e2]
    simp [hp, hP]
  · simp [hp]

private theorem winF_comp {S o1 o2 o3 : Nat} {π1 π2 F1 F2 : Nat → Nat}
    (h1 : WinF S o1 o2 π1 F1) (h2 : WinF S o2 o3 π2 F2) (hπ : ∀ p, p < S → π2 p < S) :
    WinF S o1 o3 (fun p => π1 (π2 p)) (fun x => F2 (F1 x)) := by
  intro x p hp
  show (F2 (F1 x)).testBit (o3 + p) = _
  rw [h2 _ _ hp, h1 _ _ (hπ p hp)]

/-- The flip inside a chunk at offset `0`. -/
private theorem winF_xlate {S w : Nat} (hw : 0 < w) (hd : 2 * w ∣ S) :
    WinF S 0 0 (xpartner w) (fun x => Nat.lor (Nat.shiftLeft (Nat.land x (pmask S (2 * w) w)) w)
      (Nat.land (Nat.shiftRight x w) (pmask S (2 * w) w))) := by
  intro x p hp
  have := testBit_xlate hw hd x p
  simp only [Nat.zero_add]
  exact this.trans (by simp [hp])

private theorem testBit_shiftLeft_add (y n j : Nat) : (y <<< n).testBit (n + j) = y.testBit j := by
  rw [Nat.testBit_shiftLeft]; simp

/-- The flip inside a chunk from offset `o` to offset `o + w` (no right shift). -/
private theorem winF_flip {S w : Nat} (o : Nat) (hw : 0 < w) (hd : 2 * w ∣ S) :
    WinF S o (o + w) (xpartner w) (fun x =>
      Nat.lor (Nat.land x (Nat.shiftLeft (Nat.shiftLeft (pmask S (2 * w) w) o) w))
        (Nat.shiftLeft (Nat.land x (Nat.shiftLeft (pmask S (2 * w) w) o)) (Nat.add w w))) := by
  intro x p hp
  have hP : 0 < 2 * w := by omega
  have hlo : ∀ j, (pmask S (2 * w) w).testBit j = (decide (j < S) && decide (j % (2 * w) < w)) :=
    fun j => testBit_pmask hP hd (by omega) j
  generalize pmask S (2 * w) w = lo at hlo
  show ((x &&& ((lo <<< o) <<< w)) ||| ((x &&& (lo <<< o)) <<< (w + w))).testBit (o + w + p) = _
  have hA : ((lo <<< o) <<< w).testBit (o + w + p) = lo.testBit p := by
    rw [show o + w + p = w + (o + p) by omega, testBit_shiftLeft_add, testBit_shiftLeft_add]
  -- decompose p modulo 2w
  obtain ⟨q, r, hpr, hr⟩ : ∃ q r, p = 2 * w * q + r ∧ r < 2 * w :=
    ⟨p / (2 * w), p % (2 * w), (Nat.div_add_mod p (2 * w)).symm, Nat.mod_lt _ hP⟩
  have hpm : p % (2 * w) = r := by rw [hpr, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]
  rw [Nat.testBit_or, Nat.testBit_and, hA, hlo p, hpm]
  unfold xpartner
  rw [hpm]
  by_cases hrw : r < w
  · -- lower element of its pair: it stays in place
    rw [ite_eq_left hrw]
    have hB : ((x &&& (lo <<< o)) <<< (w + w)).testBit (o + w + p) = false := by
      rw [Nat.testBit_shiftLeft]
      by_cases hge : o + w + p ≥ w + w
      · rw [Nat.testBit_and]
        by_cases hpw : p ≥ w
        · -- then q ≥ 1 and p - w is an upper element
          have hq : 1 ≤ q := by
            rcases Nat.eq_zero_or_pos q with h0 | h0
            · subst h0; omega
            · exact h0
          have e : o + w + p - (w + w) = o + (p - w) := by omega
          rw [e, testBit_shiftLeft_add, hlo]
          have hmod : (p - w) % (2 * w) = r + w := by
            have : p - w = 2 * w * (q - 1) + (r + w) := by
              have : 2 * w * q = 2 * w * (q - 1) + 2 * w := by
                rw [← Nat.mul_add_one]; congr 1; omega
              omega
            rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
          simp [hmod]
        · have e : o + w + p - (w + w) < o := by omega
          have : (lo <<< o).testBit (o + w + p - (w + w)) = false := by
            rw [Nat.testBit_shiftLeft]; simp [show ¬ (o + w + p - (w + w) ≥ o) by omega]
          simp [this]
      · simp [hge]
    rw [hB]
    simp [hp, hrw, show o + (p + w) = o + w + p by omega]
  · -- upper element: it comes from `p - w`
    rw [ite_eq_right hrw]
    have hpw : w ≤ p := by omega
    have e : o + w + p - (w + w) = o + (p - w) := by omega
    rw [Nat.testBit_shiftLeft, e, Nat.testBit_and, testBit_shiftLeft_add, hlo]
    have hmod : (p - w) % (2 * w) = r - w := by
      have : p - w = 2 * w * q + (r - w) := by omega
      rw [this, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
    simp [hrw, hmod, show o + w + p ≥ w + w by omega, show p - w < S by omega,
      show r - w < w by omega]

/-! ### Row xor -/

/-- The position of the trace whose row is `p / B` xor `μ`, in the same block. -/
private def rowX (B μ p : Nat) : Nat := ((p / B) ^^^ μ) * B + p % B

private theorem rowX_div {B : Nat} (hB : 0 < B) (μ p : Nat) :
    rowX B μ p / B = (p / B) ^^^ μ := by
  unfold rowX
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt (Nat.mod_lt _ hB),
    Nat.zero_add]

private theorem rowX_mod (B μ p : Nat) : rowX B μ p % B = p % B := by
  unfold rowX
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_mod]

private theorem rowX_rowX {B : Nat} (hB : 0 < B) (μ1 μ2 p : Nat) :
    rowX B μ1 (rowX B μ2 p) = rowX B (μ1 ^^^ μ2) p := by
  show ((rowX B μ2 p / B) ^^^ μ1) * B + rowX B μ2 p % B = _
  rw [rowX_div hB, rowX_mod, Nat.xor_assoc, Nat.xor_comm μ2 μ1]
  rfl

private theorem rowX_zero {B : Nat} (p : Nat) : rowX B 0 p = p := by
  unfold rowX; rw [Nat.xor_zero]; exact Nat.div_add_mod' p B

private theorem rowX_lt {B n μ p : Nat} (hB : 0 < B) (hp : p < 2 ^ n * B) (hμ : μ < 2 ^ n) :
    rowX B μ p < 2 ^ n * B := by
  have h1 : p / B < 2 ^ n := (Nat.div_lt_iff_lt_mul hB).2 hp
  have h2 := Nat.xor_lt_two_pow h1 hμ
  unfold rowX
  have := Nat.mod_lt p hB
  have h3 : ((p / B) ^^^ μ).succ * B ≤ 2 ^ n * B := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h2)
  rw [Nat.succ_mul] at h3; omega

/-- Flipping bit `e` of a number decomposed around it. -/
private theorem xor_two_pow_split' {e q b s : Nat} (hs : s < 2 ^ e) (hb : b < 2) :
    (2 ^ (e + 1) * q + (2 ^ e * b + s)) ^^^ 2 ^ e = 2 ^ (e + 1) * q + (2 ^ e * (1 - b) + s) := by
  have h1 : 2 ^ e * b + s < 2 ^ (e + 1) := by
    rw [Nat.pow_succ]; rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> omega
  have h2 : 2 ^ e * (1 - b) + s < 2 ^ (e + 1) := by
    rw [Nat.pow_succ]; rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> omega
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h2,
    Nat.testBit_two_pow]
  by_cases hi : i < e + 1
  · rw [ite_eq_left hi, ite_eq_left hi, Nat.testBit_two_pow_mul_add _ hs,
      Nat.testBit_two_pow_mul_add _ hs]
    by_cases hie : i < e
    · rw [ite_eq_left hie, ite_eq_left hie]
      have : ¬ e = i := by omega
      simp [this]
    · rw [ite_eq_right hie, ite_eq_right hie]
      have : i = e := by omega
      subst this; rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> simp
  · rw [ite_eq_right hi, ite_eq_right hi]
    have : ¬ e = i := by omega
    simp [this]

/-- The partner of a rank flip is the row xor. -/
private theorem xpartner_eq_rowX {B : Nat} (hB : 0 < B) (e p : Nat) :
    xpartner (2 ^ e * B) p = rowX B (2 ^ e) p := by
  obtain ⟨q, b, s, hxp, hb, hs⟩ : ∃ q b s,
      p / B = 2 ^ (e + 1) * q + (2 ^ e * b + s) ∧ b < 2 ∧ s < 2 ^ e := by
    refine ⟨p / B / 2 ^ (e + 1), p / B % 2 ^ (e + 1) / 2 ^ e, p / B % 2 ^ (e + 1) % 2 ^ e, ?_, ?_,
      Nat.mod_lt _ (Nat.two_pow_pos e)⟩
    · rw [Nat.div_add_mod, Nat.div_add_mod]
    · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos e), ← Nat.pow_succ']
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
  unfold xpartner rowX
  rw [hxp, xor_two_pow_split' hs hb]
  have hp : p = (2 ^ (e + 1) * q + (2 ^ e * b + s)) * B + p % B := by
    rw [← hxp]; exact (Nat.div_add_mod' p B).symm
  have hbr := Nat.mod_lt p hB
  generalize p % B = br at hp hbr ⊢
  subst hp
  rw [Nat.pow_succ]
  generalize 2 ^ e = W at *
  have hsB : s * B + br < W * B := by
    have : (s + 1) * B ≤ W * B := Nat.mul_le_mul_right _ hs
    rw [Nat.succ_mul] at this; omega
  rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl
  · have ei : (W * 2 * q + (W * 0 + s)) * B + br = 2 * (W * B) * q + (s * B + br) := by ring
    rw [ei, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega), ite_eq_left hsB]
    ring
  · have ei : (W * 2 * q + (W * 1 + s)) * B + br = 2 * (W * B) * q + (W * B + (s * B + br)) := by
      ring
    have hWB : W * B + (s * B + br) < 2 * (W * B) := by omega
    rw [ei, Nat.mul_add_mod, Nat.mod_eq_of_lt hWB, ite_eq_right (by omega)]
    have : (W * 2 * q + (W * (1 - 1) + s)) * B + br = 2 * (W * B) * q + (s * B + br) := by ring
    rw [this]; omega

/-- Row xor by a mask cut at the chunk bit `c`: the chunk index is xored with the high part,
the row inside the chunk with the low part. -/
private theorem rowX_split {B c : Nat} (hB : 0 < B) {δ μ : Nat} (hμ : μ < 2 ^ c) (p : Nat) :
    rowX B (2 ^ c * δ + μ) p =
      ((p / (2 ^ c * B)) ^^^ δ) * (2 ^ c * B) + rowX B μ (p % (2 ^ c * B)) := by
  have hS : 0 < 2 ^ c * B := Nat.mul_pos (Nat.two_pow_pos c) hB
  have hdiv : p / B = 2 ^ c * (p / (2 ^ c * B)) + p % (2 ^ c * B) / B := by
    conv_lhs => rw [← Nat.mod_add_div p (2 ^ c * B)]
    rw [show 2 ^ c * B * (p / (2 ^ c * B)) = (2 ^ c * (p / (2 ^ c * B))) * B by ring,
      Nat.add_mul_div_right _ _ hB, Nat.add_comm]
  have hlt : p % (2 ^ c * B) / B < 2 ^ c := (Nat.div_lt_iff_lt_mul hB).2 (Nat.mod_lt _ hS)
  have hmod : p % B = p % (2 ^ c * B) % B := (Nat.mod_mod_of_dvd p (Dvd.intro_left _ rfl)).symm
  unfold rowX
  rw [hdiv, xor_two_pow_mul_add _ _ hlt hμ, hmod]
  ring

/-! ### The bits of the chord saturation -/

/-- The row mask of the chord `(a, b)` (rank `0` is implicit). -/
private def chordMu (a b : Nat) : Nat := (if a = 0 then 0 else 2 ^ (a - 1)) ^^^ 2 ^ (b - 1)

private theorem testBit_flipRank_rowX {m B l : Nat} (hB : 0 < B) (hl1 : 1 ≤ l) (hl : l ≤ m - 1)
    (Y p : Nat) :
    (flipRank B (rankMasks (2 ^ (m - 1) * B) B (m - 1)) l Y).testBit p =
      (decide (p < 2 ^ (m - 1) * B) && Y.testBit (rowX B (2 ^ (l - 1)) p)) := by
  unfold flipRank
  have hmask : (rankMasks (2 ^ (m - 1) * B) B (m - 1)).getD (l - 1) 0 =
      pmask (2 ^ (m - 1) * B) (2 * (2 ^ (l - 1) * B)) (2 ^ (l - 1) * B) := by
    simp [rankMasks, List.getD_eq_getElem?_getD, List.getElem?_range (show l - 1 < m - 1 by omega)]
  have hdvd : 2 * (2 ^ (l - 1) * B) ∣ 2 ^ (m - 1) * B := by
    rw [← Nat.mul_assoc, ← Nat.pow_succ']
    exact Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 (by omega)) B
  rw [hmask, testBit_xlate (Nat.mul_pos (Nat.two_pow_pos _) hB) hdvd, xpartner_eq_rowX hB]

/-- The bits of `chordSat`: a trace is in the saturation iff it or its chord flip is in the
set. -/
private theorem testBit_chordSat_rowX {m B a b : Nat} (hB : 0 < B) (hab : a < b) (hb : b ≤ m - 1)
    (Y p : Nat) :
    (chordSat B (rankMasks (2 ^ (m - 1) * B) B (m - 1)) a b Y).testBit p =
      (Y.testBit p || (decide (p < 2 ^ (m - 1) * B) && Y.testBit (rowX B (chordMu a b) p))) := by
  unfold chordSat
  rw [Nat.testBit_or]
  congr 1
  by_cases ha : a = 0
  · subst ha
    simp only [BEq.rfl, ite_true]
    rw [testBit_flipRank_rowX hB (by omega) hb]
    simp [chordMu]
  · have ha' : (a == 0) = false := by simpa using ha
    rw [ha']
    simp only [Bool.false_eq_true, ite_false]
    rw [testBit_flipRank_rowX hB (by omega) (by omega)]
    by_cases hp : p < 2 ^ (m - 1) * B
    · have hlt : rowX B (2 ^ (a - 1)) p < 2 ^ (m - 1) * B :=
        rowX_lt hB hp (Nat.pow_lt_pow_right (by norm_num) (by omega))
      rw [testBit_flipRank_rowX hB (by omega) hb, rowX_rowX hB]
      simp [hp, hlt, chordMu, ha, Nat.xor_comm]
    · simp [hp]

/-! ### The rank ops -/

private theorem kop_zero (B c g S : Nat) :
    kop B c g S 0 = ⟨false, 0, 0, List.replicate g false⟩ := by
  simp [kop]

private theorem kop_in {B c g S l : Nat} (h1 : 1 ≤ l) (hl : l ≤ c) : kop B c g S l =
    ⟨true, pmask S (2 * (2 ^ (l - 1) * B)) (2 ^ (l - 1) * B), 2 ^ (l - 1) * B,
      List.replicate g false⟩ := by
  simp [kop, show l ≠ 0 by omega, hl]

private theorem kop_out {B c g S l : Nat} (hl : c < l) :
    kop B c g S l = ⟨false, 0, 0, oneHot g (l - 1 - c)⟩ := by
  simp [kop, show l ≠ 0 by omega, show ¬ l ≤ c by omega]

private theorem wOp_false (op : KOp) : wOp false op = 0 := rfl

private theorem wOp_out (om : Bool) (lo w : Nat) (bits : List Bool) :
    wOp om ⟨false, lo, w, bits⟩ = 0 := by
  cases om <;> rfl

private theorem bitsN_replicate_false (g : Nat) : bitsN (List.replicate g false) = 0 := by
  induction g with
  | zero => rfl
  | succ g ih => simp [List.replicate_succ, bitsN, ih]

private theorem oneHot_succ (g j : Nat) : oneHot (g + 1) j = (g == j) :: oneHot g j := by
  simp [oneHot, List.range_succ]

private theorem length_oneHot (g j : Nat) : (oneHot g j).length = g := by simp [oneHot]

private theorem bitsN_oneHot (g j : Nat) : bitsN (oneHot g j) = if j < g then 2 ^ j else 0 := by
  induction g with
  | zero => simp [oneHot, bitsN]
  | succ g ih =>
    rw [oneHot_succ, bitsN, length_oneHot, ih]
    by_cases hj : j < g
    · have : (g == j) = false := by simp; omega
      simp [this, hj, show j < g + 1 by omega]
    · by_cases hjg : j = g
      · subst hjg; simp
      · have : (g == j) = false := by simp; omega
        simp [this, hj, show ¬ j < g + 1 by omega]

/-- The part inside the chunks (`c` row bits) of the row mask of rank `l`. -/
private def muIn (c l : Nat) : Nat := if 1 ≤ l ∧ l ≤ c then 2 ^ (l - 1) else 0

/-- The chunk-index part of the row mask of rank `l`. -/
private def muHi (c l : Nat) : Nat := if c < l then 2 ^ (l - 1 - c) else 0

private theorem muIn_lt (c l : Nat) : muIn c l < 2 ^ c := by
  unfold muIn; split
  · exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  · exact Nat.two_pow_pos c

private theorem mu_split (c l : Nat) :
    (if l = 0 then 0 else 2 ^ (l - 1)) = 2 ^ c * muHi c l + muIn c l := by
  unfold muIn muHi
  by_cases h0 : l = 0
  · simp [h0]
  · by_cases hl : l ≤ c
    · simp [h0, hl, show 1 ≤ l by omega, show ¬ c < l by omega]
    · simp only [h0, ite_false, show c < l by omega, ite_true, hl, and_false, Nat.add_zero]
      rw [← Nat.pow_add]; congr 1; omega

private theorem kop_bits {B c g S l : Nat} (hl : l ≤ c + g) :
    (kop B c g S l).bits.length = g ∧ bitsN (kop B c g S l).bits = muHi c l := by
  by_cases h0 : l = 0
  · subst h0; rw [kop_zero]; simp [bitsN_replicate_false, muHi]
  · by_cases hlc : l ≤ c
    · rw [kop_in (by omega) hlc]
      simp [bitsN_replicate_false, muHi, show ¬ c < l by omega]
    · rw [kop_out (by omega)]
      simp only [length_oneHot, bitsN_oneHot, true_and]
      simp [muHi, show c < l by omega, show l - 1 - c < g by omega]

/-- The window of the flip of rank `l` inside the chunks. -/
private theorem winF_kop {B c g : Nat} (hB : 0 < B) (om : Bool) (l o : Nat)
    (ho : om = false → o = 0) :
    WinF (2 ^ c * B) o (o + wOp om (kop B c g (2 ^ c * B) l)) (rowX B (muIn c l))
      (fBox om (kop B c g (2 ^ c * B) l) o).f := by
  by_cases h0 : l = 0
  · subst h0
    rw [kop_zero, wOp_out]
    intro x p _
    simp only [muIn, show ¬ (1 ≤ 0 ∧ 0 ≤ c) by omega, ite_false, rowX_zero, Nat.add_zero]
    rfl
  · by_cases hlc : l ≤ c
    · rw [kop_in (by omega) hlc]
      have hw : 0 < 2 ^ (l - 1) * B := Nat.mul_pos (Nat.two_pow_pos _) hB
      have hd : 2 * (2 ^ (l - 1) * B) ∣ 2 ^ c * B := by
        rw [← Nat.mul_assoc, ← Nat.pow_succ']
        exact Nat.mul_dvd_mul_right (Nat.pow_dvd_pow 2 (by omega)) B
      have hmu : muIn c l = 2 ^ (l - 1) := by simp [muIn, show 1 ≤ l by omega, hlc]
      rw [hmu]
      cases om
      · have := ho rfl; subst this
        intro x p hp
        rw [← xpartner_eq_rowX hB]
        exact winF_xlate hw hd x p hp
      · intro x p hp
        rw [← xpartner_eq_rowX hB]
        exact winF_flip o hw hd x p hp
    · rw [kop_out (by omega), wOp_out]
      intro x p _
      simp only [muIn, show ¬ (1 ≤ l ∧ l ≤ c) by omega, ite_false, rowX_zero, Nat.add_zero]
      rfl

private theorem winF_gBox (S o W : Nat) : WinF S o (o + W) id (gBox W).f := by
  intro x p _
  unfold gBox
  cases h : Nat.beq W 0
  · show (x <<< W).testBit (o + W + p) = x.testBit (o + p)
    rw [show o + W + p = W + (o + p) by omega, testBit_shiftLeft_add]
  · have : W = 0 := Nat.eq_of_beq_eq_true h
    subst this
    show x.testBit (o + 0 + p) = x.testBit (o + p)
    rw [Nat.add_zero]

private theorem FBox.rec_eq {α : Sort _} (f : (Nat → Nat) → α) (b : FBox) :
    FBox.rec (motive := fun _ => α) f b = f b.f := by
  cases b; rfl

private theorem satK_eq (om : Bool) (oa ob : KOp) (o : Nat) (y : KT) :
    satK om oa ob o y = satT (gBox (wOp om oa + wOp om ob)).f
      (fun x => (fBox om ob (o + wOp om oa)).f ((fBox om oa o).f x))
      (xorBits oa.bits ob.bits) y y := by
  rfl

private theorem xorBits_cons_cons (a b : Bool) (l1 l2 : List Bool) :
    xorBits (a :: l1) (b :: l2) = (a ^^ b) :: xorBits l1 l2 := by
  cases a <;> cases b <;> rfl

private theorem xorBits_spec : ∀ (l1 l2 : List Bool), l1.length = l2.length →
    (xorBits l1 l2).length = l1.length ∧ bitsN (xorBits l1 l2) = bitsN l1 ^^^ bitsN l2
  | [], [], _ => ⟨rfl, rfl⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l1, b :: l2, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    obtain ⟨h1, h2⟩ := xorBits_spec l1 l2 h
    rw [xorBits_cons_cons]
    refine ⟨by simp [h1], ?_⟩
    simp only [bitsN, h1, h2, ← h]
    rw [xor_two_pow_mul_add _ _ (bitsN_lt l1) (by rw [h]; exact bitsN_lt l2)]
    cases a <;> cases b <;> rfl

/-- **The chunked chord saturation is the chord saturation** of the number the tree
represents (at its offset). -/
private theorem ofTreeAt_satK {B c g : Nat} (hB : 0 < B) (om : Bool) {a b : Nat} (hab : a < b)
    (hb : b ≤ c + g) (o : Nat) (ho : om = false → o = 0) (y : KT) :
    ofTreeAt (2 ^ c * B)
        (o + (wOp om (kop B c g (2 ^ c * B) a) + wOp om (kop B c g (2 ^ c * B) b))) g
        (satK om (kop B c g (2 ^ c * B) a) (kop B c g (2 ^ c * B) b) o y) =
      chordSat B (rankMasks (2 ^ (c + g + 1 - 1) * B) B (c + g + 1 - 1)) a b
        (ofTreeAt (2 ^ c * B) o g y) := by
  have hS : 0 < 2 ^ c * B := Nat.mul_pos (Nat.two_pow_pos c) hB
  obtain ⟨hla, hba⟩ := kop_bits (B := B) (S := 2 ^ c * B) (show a ≤ c + g by omega)
  obtain ⟨hlb, hbb⟩ := kop_bits (B := B) (S := 2 ^ c * B) hb
  obtain ⟨hlx, hbx⟩ := xorBits_spec (kop B c g (2 ^ c * B) a).bits
    (kop B c g (2 ^ c * B) b).bits (by rw [hla, hlb])
  have hFa := winF_kop (c := c) (g := g) hB om a o ho
  have hFb := winF_kop (c := c) (g := g) hB om b (o + wOp om (kop B c g (2 ^ c * B) a))
    (fun h => by subst h; rw [ho rfl, wOp_false])
  have hπ : ∀ p, p < 2 ^ c * B → rowX B (muIn c b) p < 2 ^ c * B :=
    fun p hp => rowX_lt hB hp (muIn_lt c b)
  have hF := winF_comp hFa hFb hπ
  rw [Nat.add_assoc] at hF
  have hG := winF_gBox (2 ^ c * B) o
    (wOp om (kop B c g (2 ^ c * B) a) + wOp om (kop B c g (2 ^ c * B) b))
  have hπ2 : ∀ p, p < 2 ^ c * B →
      (fun p => rowX B (muIn c a) (rowX B (muIn c b) p)) p < 2 ^ c * B :=
    fun p hp => rowX_lt hB (hπ p hp) (muIn_lt c a)
  rw [satK_eq]
  apply Nat.eq_of_testBit_eq; intro p
  rw [testBit_ofTreeAt_satT hS (hlx.trans hla) hG hF hπ2,
    testBit_chordSat_rowX hB hab (by omega)]
  have hL : 2 ^ g * (2 ^ c * B) = 2 ^ (c + g + 1 - 1) * B := by
    rw [show c + g + 1 - 1 = c + g by omega, Nat.pow_add]; ring
  rw [hL]
  congr 1
  by_cases hp : p < 2 ^ (c + g + 1 - 1) * B
  · simp only [hp, decide_true, Bool.true_and]
    congr 1
    rw [hbx, hba, hbb, rowX_rowX hB]
    have hmu : chordMu a b = 2 ^ c * (muHi c a ^^^ muHi c b) + (muIn c a ^^^ muIn c b) := by
      unfold chordMu
      rw [mu_split c a, show 2 ^ (b - 1) = (if b = 0 then 0 else 2 ^ (b - 1)) by
        simp [show b ≠ 0 by omega], mu_split c b,
        xor_two_pow_mul_add _ _ (muIn_lt c a) (muIn_lt c b)]
    rw [hmu, rowX_split hB (Nat.xor_lt_two_pow (muIn_lt c a) (muIn_lt c b))]
  · have hp' : ¬ p < 2 ^ (c + g) * B := by
      rwa [show c + g + 1 - 1 = c + g by omega] at hp
    simp [hp']

/-! ### The enumeration -/

/-- The saturation of `(y, o)` along the chords of `M`, the ops being read in `ops`. -/
private def satLK (sat : KOp → KOp → Nat → KT → KT) (wd : KOp → KOp → Nat)
    (ops : List KOp) (d : KOp) (M : List Chord) (s : KT × Nat) : KT × Nat :=
  M.foldl (fun s ab => (sat (ops.getD ab.1 d) (ops.getD ab.2 d) s.2 s.1,
    s.2 + wd (ops.getD ab.1 d) (ops.getD ab.2 d))) s

private theorem satLK_nil (sat : KOp → KOp → Nat → KT → KT) (wd : KOp → KOp → Nat)
    (ops : List KOp) (d : KOp) (s : KT × Nat) : satLK sat wd ops d [] s = s := rfl

private theorem satLK_cons (sat : KOp → KOp → Nat → KT → KT) (wd : KOp → KOp → Nat)
    (ops : List KOp) (d : KOp) (ab : Chord) (M : List Chord) (s : KT × Nat) :
    satLK sat wd ops d (ab :: M) s = satLK sat wd ops d M
      (sat (ops.getD ab.1 d) (ops.getD ab.2 d) s.2 s.1,
        s.2 + wd (ops.getD ab.1 d) (ops.getD ab.2 d)) := rfl

private theorem satLK_append (sat : KOp → KOp → Nat → KT → KT) (wd : KOp → KOp → Nat)
    (ops : List KOp) (d : KOp) (M1 M2 : List Chord) (s : KT × Nat) :
    satLK sat wd ops d (M1 ++ M2) s = satLK sat wd ops d M2 (satLK sat wd ops d M1 s) := by
  simp [satLK, List.foldl_append]

private theorem tailK_eq (l : List KOp) : tailK l = l.tail := by cases l <;> rfl

private theorem kLoop_succ (sat : KOp → KOp → Nat → KT → KT) (wd : KOp → KOp → Nat)
    (E : List KOp → Nat → KT → Nat → KT → (KT → Nat → KT → KT) → KT)
    (oa : KOp) (rest : List KOp) (y : KT) (o : Nat) (k : KT → Nat → KT → KT)
    (cnt : Nat) (ob : KOp) (opsB' : List KOp) (i : Nat) (acc : KT) :
    kLoop sat wd E oa rest y o k (cnt + 1) (ob :: opsB') i acc =
      kLoop sat wd E oa rest y o k cnt (tailK opsB') (i + 2)
        (E rest i (sat oa ob o y) (o + wd oa ob) acc
          (fun y' o' acc' => E opsB' (cnt + cnt) y' o' acc' k)) := rfl

private theorem kE_succ_cons (sat : KOp → KOp → Nat → KT → KT) (wd : KOp → KOp → Nat)
    (f : Nat) (oa : KOp) (rest : List KOp) {n : Nat} (hn : n ≠ 0) (y : KT) (o : Nat) (acc : KT)
    (k : KT → Nat → KT → KT) :
    kE sat wd (f + 1) (oa :: rest) n y o acc k =
      kLoop sat wd (kE sat wd f) oa rest y o k (n / 2) rest 0 acc := by
  have h : Nat.beq n 0 = false := by
    cases n with
    | zero => exact absurd rfl hn
    | succ n => rfl
  change @Bool.rec (fun _ => KT) _ _ (Nat.beq n 0) = _
  rw [h]
  rfl

/-- **`kE` enumerates the non-crossing perfect matchings in the order of `ncm`.** -/
private theorem kE_eq (sat : KOp → KOp → Nat → KT → KT) (wd : KOp → KOp → Nat)
    (ops : List KOp) (d : KOp) :
    ∀ (fuel lo n : Nat) (y : KT) (o : Nat) (acc : KT) (k : KT → Nat → KT → KT),
      n % 2 = 0 → lo + n ≤ ops.length →
      kE sat wd fuel (ops.drop lo) n y o acc k =
        (ncm fuel lo n).foldl (fun acc M =>
          k (satLK sat wd ops d M (y, o)).1 (satLK sat wd ops d M (y, o)).2 acc) acc := by
  intro fuel
  induction fuel with
  | zero => intro lo n y o acc k _ _; rfl
  | succ f ih =>
    intro lo n y o acc k hn hlen
    by_cases h0 : n = 0
    · subst h0; rfl
    · have hlo : lo < ops.length := by omega
      rw [List.drop_eq_getElem_cons hlo, kE_succ_cons _ _ _ _ _ h0]
      have hncm : ncm (f + 1) lo n = (List.range (n / 2)).flatMap fun j =>
          (ncm f (lo + 1) (2 * j)).flatMap fun mi =>
            (ncm f (lo + 2 * j + 2) (n - 2 * j - 2)).map fun mo =>
              (lo, lo + 2 * j + 1) :: (mi ++ mo) := by
        have : (n == 0) = false := by simpa using h0
        simp only [ncm, this, Bool.false_eq_true, ite_false]
      rw [hncm, List.foldl_flatMap]
      have key : ∀ cnt j acc, 2 * j + 2 * cnt = n →
          kLoop sat wd (kE sat wd f) ops[lo] (ops.drop (lo + 1)) y o k cnt
              (ops.drop (lo + 2 * j + 1)) (2 * j) acc =
            (List.range' j cnt).foldl (fun acc j =>
              ((ncm f (lo + 1) (2 * j)).flatMap fun mi =>
                (ncm f (lo + 2 * j + 2) (n - 2 * j - 2)).map fun mo =>
                  (lo, lo + 2 * j + 1) :: (mi ++ mo)).foldl (fun acc M =>
                    k (satLK sat wd ops d M (y, o)).1 (satLK sat wd ops d M (y, o)).2 acc) acc)
              acc := by
        intro cnt
        induction cnt with
        | zero => intro j acc _; rfl
        | succ cnt ihc =>
          intro j acc hj
          have hb : lo + 2 * j + 1 < ops.length := by omega
          rw [List.drop_eq_getElem_cons hb, kLoop_succ, List.range'_succ, List.foldl_cons, tailK_eq,
            List.tail_drop, show lo + 2 * j + 1 + 1 + 1 = lo + 2 * (j + 1) + 1 by ring,
            show 2 * j + 2 = 2 * (j + 1) by ring, ihc (j + 1) _ (by omega)]
          congr 1
          have e2 : cnt + cnt = n - 2 * j - 2 := by omega
          rw [e2]
          have hout : ∀ y' o' acc', kE sat wd f (ops.drop (lo + 2 * j + 1 + 1)) (n - 2 * j - 2) y'
              o' acc' k = (ncm f (lo + 2 * j + 2) (n - 2 * j - 2)).foldl (fun acc M =>
                k (satLK sat wd ops d M (y', o')).1 (satLK sat wd ops d M (y', o')).2 acc) acc' :=
            fun y' o' acc' => ih _ _ _ _ _ _ (by omega) (by omega)
          simp only [hout]
          rw [ih (lo + 1) (2 * j) _ _ _ _ (by omega) (by omega), List.foldl_flatMap]
          congr 1
          funext acc' mi
          rw [List.foldl_map]
          congr 1
          funext acc'' mo
          rw [satLK_cons, satLK_append]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlo,
            List.getElem?_eq_getElem hb, Option.getD_some]
      have := key (n / 2) 0 acc (by omega)
      simp only [Nat.mul_zero, Nat.add_zero] at this
      rw [this, List.range_eq_range']

/-! ### The chunked Kempe grade is the Kempe grade -/

private theorem kLevels_le (T : Nat) : ∀ (f L : Nat), kLevels T f L ≤ f := by
  intro f
  induction f with
  | zero => intro L; exact Nat.le_refl 0
  | succ f ih =>
    intro L
    change @Bool.rec (fun _ => Nat) (Nat.succ (kLevels T f (Nat.div L 2))) 0 (Nat.ble L T) ≤ f + 1
    cases Nat.ble L T
    · exact Nat.succ_le_succ (ih _)
    · exact Nat.zero_le _

private theorem getD_map_range {α : Type} (f : Nat → α) {n l : Nat} (hl : l < n) (d : α) :
    ((List.range n).map f).getD l d = f l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
  rfl

private theorem satList_cons (sat : Nat → Nat → Nat → Nat) (ab : Chord) (M : List Chord)
    (y : Nat) :
    satList sat (ab :: M) y = satList sat M (sat ab.1 ab.2 y) := rfl

/-- The chunked saturation along a matching of the ranks `0 … c+g`. -/
private theorem satLK_kop {B c g : Nat} (hB : 0 < B) (om : Bool) (d : KOp) :
    ∀ (M : List Chord), (∀ ab ∈ M, ab.1 < ab.2 ∧ ab.2 ≤ c + g) → ∀ (y : KT) (o : Nat),
      (om = false → o = 0) →
      ofTreeAt (2 ^ c * B) (satLK (satK om) (fun oa ob => Nat.add (wOp om oa) (wOp om ob))
          ((List.range (c + g + 1)).map (kop B c g (2 ^ c * B))) d M (y, o)).2 g
        (satLK (satK om) (fun oa ob => Nat.add (wOp om oa) (wOp om ob))
          ((List.range (c + g + 1)).map (kop B c g (2 ^ c * B))) d M (y, o)).1 =
        satList (chordSat B (rankMasks (2 ^ (c + g + 1 - 1) * B) B (c + g + 1 - 1))) M
          (ofTreeAt (2 ^ c * B) o g y) ∧
      (om = false → (satLK (satK om) (fun oa ob => Nat.add (wOp om oa) (wOp om ob))
          ((List.range (c + g + 1)).map (kop B c g (2 ^ c * B))) d M (y, o)).2 = 0) := by
  intro M
  induction M with
  | nil => intro _ y o ho; exact ⟨rfl, ho⟩
  | cons ab M ih =>
    intro hM y o ho
    have hab := hM ab List.mem_cons_self
    have hM' : ∀ ab ∈ M, ab.1 < ab.2 ∧ ab.2 ≤ c + g :=
      fun ab' h => hM ab' (List.mem_cons_of_mem _ h)
    rw [satLK_cons, getD_map_range _ (show ab.1 < c + g + 1 by omega),
      getD_map_range _ (show ab.2 < c + g + 1 by omega), satList_cons,
      ← ofTreeAt_satK hB om hab.1 hab.2 o ho y]
    exact ih hM' _ _ (fun h => by subst h; simp [ho rfl, wOp_false])

/-- The chunked fold over the matchings. -/
private theorem ofTreeAt_foldl {B c g : Nat} (hB : 0 < B) (om : Bool) (d : KOp) (O : Nat)
    (y0 : KT) :
    ∀ (Ms : List (List Chord)), (∀ M ∈ Ms, ∀ ab ∈ M, ab.1 < ab.2 ∧ ab.2 ≤ c + g) →
      ∀ (acc : KT),
      ofTreeAt (2 ^ c * B) O g (Ms.foldl (fun acc M => andT g acc (alignT O
          (satLK (satK om) (fun oa ob => Nat.add (wOp om oa) (wOp om ob))
            ((List.range (c + g + 1)).map (kop B c g (2 ^ c * B))) d M (y0, 0)).2 g
          (satLK (satK om) (fun oa ob => Nat.add (wOp om oa) (wOp om ob))
            ((List.range (c + g + 1)).map (kop B c g (2 ^ c * B))) d M (y0, 0)).1)) acc) =
        Ms.foldl (fun A M => A &&& satList
            (chordSat B (rankMasks (2 ^ (c + g + 1 - 1) * B) B (c + g + 1 - 1))) M
            (ofTreeAt (2 ^ c * B) 0 g y0))
          (ofTreeAt (2 ^ c * B) O g acc) := by
  have hS : 0 < 2 ^ c * B := Nat.mul_pos (Nat.two_pow_pos c) hB
  intro Ms
  induction Ms with
  | nil => intro _ acc; rfl
  | cons M Ms ih =>
    intro hMs acc
    rw [List.foldl_cons, List.foldl_cons, ih (fun M' h => hMs M' (List.mem_cons_of_mem _ h)),
      ofTreeAt_andT hS, ofTreeAt_alignT hS,
      (satLK_kop hB om d M (hMs M List.mem_cons_self) y0 0 (fun _ => rfl)).1]

private theorem ofTreeAt_zero_size (O : Nat) : ∀ (h : Nat) (t : KT), ofTreeAt 0 O h t = 0 := by
  intro h
  induction h with
  | zero => intro t; rw [ofTreeAt_zero]; simp [ones]
  | succ h ih => intro t; rw [ofTreeAt_succ, ih, ih]; simp

private theorem foldl_and_zero (f : List Chord → Nat) :
    ∀ (Ms : List (List Chord)), Ms.foldl (fun acc M => acc &&& f M) 0 = 0 := by
  intro Ms
  induction Ms with
  | nil => rfl
  | cons M Ms ih => rw [List.foldl_cons, Nat.zero_and, ih]

private theorem chordMu_lt {n a b : Nat} (hab : a < b) (hb : b ≤ n) : chordMu a b < 2 ^ n := by
  unfold chordMu
  have h2 : 2 ^ (b - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  split
  · simpa using h2
  · exact Nat.xor_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) (by omega)) h2

/-- The saturation along a matching only reads the bits below `L`. -/
private theorem satList_chordSat_congr {m B : Nat} (hB : 0 < B) : ∀ (M : List Chord),
    (∀ ab ∈ M, ab.1 < ab.2 ∧ ab.2 ≤ m - 1) → ∀ (Y Y' : Nat),
      (∀ p, p < 2 ^ (m - 1) * B → Y.testBit p = Y'.testBit p) → ∀ p, p < 2 ^ (m - 1) * B →
        (satList (chordSat B (rankMasks (2 ^ (m - 1) * B) B (m - 1))) M Y).testBit p =
          (satList (chordSat B (rankMasks (2 ^ (m - 1) * B) B (m - 1))) M Y').testBit p := by
  intro M
  induction M with
  | nil => intro _ Y Y' h p hp; exact h p hp
  | cons ab M ih =>
    intro hM Y Y' h p hp
    have hab := hM ab List.mem_cons_self
    rw [satList_cons, satList_cons]
    apply ih (fun ab' h' => hM ab' (List.mem_cons_of_mem _ h')) _ _ _ p hp
    intro p' hp'
    rw [testBit_chordSat_rowX hB hab.1 hab.2, testBit_chordSat_rowX hB hab.1 hab.2, h p' hp',
      h _ (rowX_lt hB hp' (chordMu_lt hab.1 (by omega)))]

private theorem foldl_and_congr (L : Nat) (f f' : List Chord → Nat) :
    ∀ (Ms : List (List Chord)),
      (∀ M ∈ Ms, ∀ p, p < L → (f M).testBit p = (f' M).testBit p) →
      ∀ A, (∀ p, L ≤ p → A.testBit p = false) →
        Ms.foldl (fun acc M => acc &&& f M) A = Ms.foldl (fun acc M => acc &&& f' M) A := by
  intro Ms
  induction Ms with
  | nil => intro _ A _; rfl
  | cons M Ms ih =>
    intro hMs A hA
    have e : A &&& f M = A &&& f' M := by
      apply Nat.eq_of_testBit_eq; intro p
      rw [Nat.testBit_and, Nat.testBit_and]
      by_cases hp : p < L
      · rw [hMs M List.mem_cons_self p hp]
      · rw [hA p (by omega)]; simp
    rw [List.foldl_cons, List.foldl_cons, e]
    apply ih (fun M' h => hMs M' (List.mem_cons_of_mem _ h))
    intro p hp
    rw [Nat.testBit_and, hA p hp, Bool.false_and]

/-- The chunked computation, with its parameters as variables. -/
private theorem kempeGrade_chunks {B c g : Nat} (hB : 0 < B) (he : (c + g + 1) % 2 = 0) (om : Bool)
    (O q : Nat) :
    ofTreeAt (2 ^ c * B) O g (kE (satK om) (fun oa ob => Nat.add (wOp om oa) (wOp om ob))
        (c + g + 1) ((List.range (c + g + 1)).map (kop B c g (2 ^ c * B))) (c + g + 1)
        (toTree (2 ^ c * B) g q) 0 (constT (ones (O + 2 ^ c * B)) g)
        (fun y o acc => andT g acc (alignT O o g y))) =
      (ncm (c + g + 1) 0 (c + g + 1)).foldl (fun A M => A &&& satList
          (chordSat B (rankMasks (2 ^ (c + g + 1 - 1) * B) B (c + g + 1 - 1))) M
          (q &&& ones (2 ^ (c + g + 1 - 1) * B)))
        (ones (2 ^ (c + g + 1 - 1) * B)) := by
  have hS : 0 < 2 ^ c * B := Nat.mul_pos (Nat.two_pow_pos c) hB
  have hL : 2 ^ g * (2 ^ c * B) = 2 ^ (c + g + 1 - 1) * B := by
    rw [show c + g + 1 - 1 = c + g by omega, Nat.pow_add]; ring
  have h := kE_eq (satK om) (fun oa ob => Nat.add (wOp om oa) (wOp om ob))
    ((List.range (c + g + 1)).map (kop B c g (2 ^ c * B))) (kop B c g (2 ^ c * B) 0)
    (c + g + 1) 0 (c + g + 1) (toTree (2 ^ c * B) g q) 0 (constT (ones (O + 2 ^ c * B)) g)
    (fun y o acc => andT g acc (alignT O o g y)) he (by simp)
  rw [List.drop_zero] at h
  rw [h, ofTreeAt_foldl hB om _ O _ _ (fun M hM ab hab => by
      have := mem_ncm_chord hM hab; omega),
    ofTreeAt_constT hS, ofTreeAt_toTree hS, hL]

/-- **The chunked Kempe step of a grade is the Kempe step.** -/
theorem kempeGradeBT_eq (T Tx r k q : Nat) : kempeGradeBT T Tx r k q = kempeGrade r k q := by
  by_cases hk : k = 0
  · subst hk; rfl
  have hk' : Nat.beq k 0 = false := by
    cases k with
    | zero => exact absurd rfl hk
    | succ k => rfl
  have hk'' : (k == 0) = false := by simpa using hk
  change @Bool.rec (fun _ => Nat) (kempeGradeKT T Tx r k q) q (Nat.beq k 0) = _
  rw [hk']
  -- the Kempe step as a fold over the matchings
  simp only [kempeGrade, hk'', Bool.false_eq_true, ite_false]
  rw [ncmFold_eq]
  unfold kempeGradeKT
  dsimp only
  have hgle := kLevels_le T (2 * k - 1) (2 ^ (2 * k - 1) * chooseAux r (2 * k))
  generalize kLevels T (2 * k - 1) (2 ^ (2 * k - 1) * chooseAux r (2 * k)) = g at hgle ⊢
  generalize chooseAux r (2 * k) = B
  generalize Nat.blt Tx (2 ^ (2 * k - 1) * B) = om
  have hm : 2 * k = (2 * k - 1 - g) + g + 1 := by omega
  generalize 2 * k - 1 - g = c at hm ⊢
  generalize (@Bool.rec (fun _ => Nat) 0 (2 ^ c * B - B) om) = O
  rw [hm]
  rcases Nat.eq_zero_or_pos B with hB | hB
  · subst hB
    simp only [Nat.mul_zero, ofTreeAt_zero_size, ones, Nat.shiftLeft_eq, Nat.one_mul,
      Nat.pow_zero, Nat.sub_self, foldl_and_zero]
  · rw [kempeGrade_chunks hB (by omega) om O q, show c + g + 1 - 1 = c + g by omega]
    symm
    apply foldl_and_congr
    · intro M hM p hp
      apply satList_chordSat_congr (m := c + g + 1) hB M (fun ab hab => by
        have := mem_ncm_chord hM hab; omega) _ _ _ p (by simpa using hp)
      intro p' hp'
      rw [Nat.testBit_and, testBit_ones]
      simp only [show c + g + 1 - 1 = c + g by omega] at hp'
      simp [hp']
    · intro p hp
      rw [testBit_ones]; simp; omega

/-- **`kempeGradeB` is `kempeGrade`.** -/
theorem kempeGradeB_eq (r k q : Nat) : kempeGradeB r k q = kempeGrade r k q :=
  kempeGradeBT_eq _ _ r k q

/-- **`kempeStepB` is `kempeStep`.** -/
theorem kempeStepB_eq (r : Nat) (X : List Nat) : kempeStepB r X = kempeStep r X := by
  unfold kempeStepB kempeStep
  congr 1
  funext k q
  exact kempeGradeB_eq r k q

/-- The round with the chunked Kempe step is the round. -/
theorem roundB_eq_roundC (r s : Nat) (net : NetC) (X : List Nat) :
    roundB r s net X = roundC r s net X := by
  unfold roundB roundC; rw [kempeStepB_eq]

/-- `n` rounds with the chunked Kempe step are `n` rounds. -/
theorem roundsNB_eq_roundsNC (r s : Nat) (net : NetC) (n : Nat) (X : List Nat) :
    roundsNB r s net n X = roundsNC r s net n X := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih => rw [roundsNB, roundsNC, roundB_eq_roundC, ih]

/-- **The checkpoint step with the chunked Kempe step is the checkpoint step**, with the
network assembled from its chunks. -/
theorem checkStep_eq_checkStepB {s : Nat} {net : NetC} (h : netCOK s net = true)
    (r n : Nat) (H H' : List Nat) :
    checkStep r (netOfChunks s net) n H H' = checkStepB r s net n H H' := by
  rw [checkStep_eq_checkStepC h, checkStepC, checkStepB, roundsNB_eq_roundsNC]

end FourColor.Engine
