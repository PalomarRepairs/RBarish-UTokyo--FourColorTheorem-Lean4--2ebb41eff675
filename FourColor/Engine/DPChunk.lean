/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.CheckChunk

/-!
# Reducibility engine: the coloring DP on base-3 chunks

The coloring DP of `ColorDP.lean` stores the trace set of a state with `ℓ` slots as one number of
`3 ^ ℓ` bits (up to `3 ^ 14`); its digit rewrites (`mv`), digit transpositions (`transp`,
`killSlot`, `sortDigits`) and final fold (`fold3`) shift it right by up to `2 * 3 ^ (ℓ - 1)` bits.
Palomar's checker nanoda computes `x >>> d` as a long division by `2 ^ d`, in time about
`|x >>> d| * d`: one ring-14 DP took ≈ 40 s
there.  This file computes the same DP on *base-3 chunks* of `3 ^ h` bits:

* a state with `ℓ` slots is a ternary tree `B3T` of height `ℓ - h` (a single chunk when `ℓ ≤ h`)
  whose leaves are the chunks (the `3 ^ h` consecutive indices with given digits `h … ℓ - 1`) and
  whose nodes branch on the digits `ℓ - 1, ℓ - 2, …, h` from the root (`B3T.val`); `z` is the
  zero tree of any height, so that the operations skip the empty parts;
* an operation on a *low* slot `s < h` acts inside every chunk (`mapT`): masks of `3 ^ h` bits,
  and shifts by at most `2 * 3 ^ (h - 1)` bits of numbers of `3 ^ h` bits;
* an operation on a *high* slot `s ≥ h` only rearranges subtrees, with no shift at all: selecting
  the digit value `v` keeps the child `v` of the nodes at depth `ℓ - 1 - s`, rewriting it from `v`
  to `v'` moves that child to position `v'` (`atT`, `mvNode`); a new top digit is a new root
  (`topB`), dropping the top digit takes the first child of the root (`truncB`), and `fold3` ors
  the three children of the root (`fold3B`);
* `selB`, `mvB`, `orsB`, `topB`, `truncB` are `sel`, `mv`, `ors`, the shifts `<<< k * 3 ^ ℓ` and
  the truncation `&&& ones (3 ^ (ℓ - 1))` of `ColorDP.lean` on trees, and `transpB`, `killSlotB`,
  `dpStepB`, `dpRunB`, `sortDigitsB`, `dpB3B` are `transp`, `killSlot`, `dpStep`, `dpRun`,
  `sortDigits`, `dpB3` written with them, operation for operation;
* the result, `3 ^ (r - 1)` bits in chunks of `3 ^ h` bits at the offsets `j * 3 ^ h`, is cut
  into the `2 ^ s`-bit chunks of the chunked conversion network (`convB`: each base-3 chunk is
  shifted left to its offset inside its first network chunk, split by `toChunksAux` with right
  shifts by `2 ^ s` bits of numbers of fewer than `3 ^ h + 2 ^ s` bits, and or-ed in place by
  `orAt`), and `dpP1B` finishes as `dpP1C` (`applyNetC`, `splitGC`).

The tree operations evaluated by the kernel are written with recursors (`B3T.rec`, `Nat.rec`,
`Bool.rec`), with `/`, `%` and `^` only on small numbers (digit positions, `3 ^ s`, chunk
offsets); an in-chunk mask (`digitMask (min ℓ h) s v`) is a closed term, evaluated once for all
the chunks.  The combinations over the digit values (`digits3.flatMap`, `ors`) are those of
`ColorDP.lean`: their cost is per operation, not per chunk.

**Correctness.**  Each tree operation computes the corresponding operation of `ColorDP.lean` on
the number that the tree represents, for well-formed trees (`TInv`: height `ℓ - h`, chunks below
`2 ^ 3 ^ min ℓ h`) and, for `mv`, entries whose digit `s` is `v` (`DigN`, the hypothesis of the
digit rewrites of `ColorDP.lean`); the proofs go through the bits of the chunks (`testBit_val`,
`leafAt`) and base-3 digit arithmetic (`setDig`).  Hence

* `dpP1B_eq_dpP1 : netCOK s cnv = true → dpP1B r s h cnv cp = dpP1 r (netOfChunks s cnv) cp`
  (`dpP1B` falls back to `dpP1C` when `h < 2` or when the program is not of ring size `r`),
* `dpP1B_eq_dpP1C`, `checkInit_eq_checkInitB`, `checkFinal_eq_checkFinalB`: the certificates can
  evaluate `checkInitB r 16 h cnvNetC<r> …` and `checkFinalB r 16 h cnvNetC<r> …` in place of
  `checkInitC`/`checkFinalC`, with the proofs `cnvNetOK<r>` they already use.

**Costs** (one ring-14 DP, `cf110`, `scripts/palomar_check.sh`, including a fixed cost of
0.3 s for nanoda): nanoda ≈ 40 s with `dpP1C`, ≈ 1.0 s with `dpP1B` for `h = 10`, ≈ 1.2 s for
`h = 11`; Lean's kernel ≈ 2.0 s with `dpP1C`, ≈ 1.0 s and ≈ 0.85 s.  Over the ring-14
configurations measured, `h = 11` is the better choice (Lean's kernel and `leanchecker` 20–30%
faster than with `h = 10`, nanoda within 10%); a ring of size at most `h` is a single chunk,
i.e. the computation of `ColorDP.lean`.
-/

namespace FourColor.Engine

open FourColor

/-! ### Ternary trees of base-3 chunks -/

/-- A ternary tree of base-3 chunks: a tree of height `k` with chunks of `3 ^ h` bits represents
a number of `3 ^ (h + k)` bits (`val`), the children of a node standing for the values `0, 1, 2`
of its top digit; `z` is the zero tree of any height. -/
inductive B3T where
  /-- The zero tree (of any height). -/
  | z : B3T
  /-- A chunk of `3 ^ h` bits (height `0`). -/
  | leaf (c : Nat) : B3T
  /-- A node (height `k + 1`): the children of height `k` for the top digit `0, 1, 2`. -/
  | node (a b c : B3T) : B3T

namespace B3T

/-- Apply `f` to every chunk (`z` stays `z`). -/
noncomputable def mapT (f : Nat → Nat) (t : B3T) : B3T :=
  B3T.rec (motive := fun _ => B3T) .z (fun c => .leaf (f c))
    (fun _ _ _ ra rb rc => .node ra rb rc) t

/-- Chunk-wise `|||` of two trees of the same height. -/
noncomputable def orT (t : B3T) : B3T → B3T :=
  B3T.rec (motive := fun _ => B3T → B3T)
    (fun u => u)
    (fun c u => B3T.rec (motive := fun _ => B3T) (.leaf c) (fun d => .leaf (Nat.lor c d))
      (fun _ _ _ _ _ _ => .leaf c) u)
    (fun a b c ra rb rc u => B3T.rec (motive := fun _ => B3T) (.node a b c) (fun _ => .node a b c)
      (fun a' b' c' _ _ _ => .node (ra a') (rb b') (rc c')) u) t

/-- The child `v` (`0`, `1`, or `2` for any `v ≥ 2`). -/
def pick (v : Nat) (a b c : B3T) : B3T :=
  Nat.rec (motive := fun _ => B3T) a
    (fun n _ => Nat.rec (motive := fun _ => B3T) b (fun _ _ => c) n) v

/-- The node whose child `v` is `x`, the other children being `z`. -/
def put (v : Nat) (x : B3T) : B3T :=
  Nat.rec (motive := fun _ => B3T) (.node x .z .z)
    (fun n _ => Nat.rec (motive := fun _ => B3T) (.node .z x .z) (fun _ _ => .node .z .z x) n) v

/-- The first child of the root. -/
noncomputable def child0 (t : B3T) : B3T :=
  B3T.rec (motive := fun _ => B3T) .z (fun _ => .z) (fun a _ _ _ _ _ => a) t

/-- The `|||` of the three children of the root. -/
noncomputable def fold3Root (t : B3T) : B3T :=
  B3T.rec (motive := fun _ => B3T) .z (fun _ => .z) (fun a b c _ _ _ => orT (orT a b) c) t

/-- Apply `g` to the children of the nodes at depth `d`. -/
noncomputable def atT (g : B3T → B3T → B3T → B3T) (d : Nat) : B3T → B3T :=
  Nat.rec (motive := fun _ => B3T → B3T)
    (fun t => B3T.rec (motive := fun _ => B3T) .z (fun c => .leaf c) (fun a b c _ _ _ => g a b c) t)
    (fun _ ih t => B3T.rec (motive := fun _ => B3T) .z (fun c => .leaf c)
      (fun a b c _ _ _ => .node (ih a) (ih b) (ih c)) t) d

/-- Keep the child `v` at position `v'`. -/
def mvNode (v v' : Nat) (a b c : B3T) : B3T := put v' (pick v a b c)

end B3T

open B3T

/-! ### The DP primitives on trees -/

/-- `sel ℓ x s v` on a tree of height `ℓ - h`. -/
noncomputable def selB (h ℓ : Nat) (t : B3T) (s v : Nat) : B3T :=
  Bool.rec (atT (mvNode v v) (ℓ - 1 - s) t)
    (mapT (fun c => Nat.land c (digitMask (min ℓ h) s v)) t) (Nat.blt s h)

/-- `mv x s v v'` on a tree of height `ℓ - h` whose entries all have the digit `s = v` (the
identity when `v = v'`, as `mv`). -/
noncomputable def mvB (h ℓ : Nat) (t : B3T) (s v v' : Nat) : B3T :=
  Bool.rec
    (Bool.rec (atT (mvNode v v') (ℓ - 1 - s) t) (mapT (fun c => mv c s v v') t) (Nat.blt s h))
    t (Nat.beq v v')

/-- `ors` on trees. -/
noncomputable def orsB (l : List B3T) : B3T := l.foldl orT .z

/-- `x <<< (k * 3 ^ ℓ)` for a new top digit `ℓ` (a tree of height `ℓ - h` becomes one of height
`ℓ + 1 - h`). -/
noncomputable def topB (h ℓ k : Nat) (t : B3T) : B3T :=
  Bool.rec (put k t) (mapT (fun c => Nat.shiftLeft c (k * 3 ^ ℓ)) t) (Nat.blt ℓ h)

/-- `x &&& ones (3 ^ (ℓ - 1))`: drop the top digit `ℓ - 1` (keeping the entries where it is
`0`). -/
noncomputable def truncB (h ℓ : Nat) (t : B3T) : B3T :=
  Bool.rec (child0 t) (mapT (fun c => Nat.land c (ones (3 ^ (ℓ - 1)))) t) (Nat.ble ℓ h)

/-- `transp` on trees. -/
noncomputable def transpB (h ℓ : Nat) (t : B3T) (a b : Nat) : B3T :=
  if a == b then t else
  orsB (digits3.flatMap fun u => digits3.map fun v =>
    let y := selB h ℓ (selB h ℓ t a u) b v
    mvB h ℓ (mvB h ℓ y a u v) b v u)

/-- The DP state on trees: as `DPState`, with the trace set as a tree of height `len - h`. -/
structure DPStateB where
  /-- The number of slots. -/
  len : Nat
  /-- The slot of each ring position, in ring order. -/
  ord : List Nat
  /-- The trace set. -/
  t : B3T

/-- `killSlot` on trees. -/
noncomputable def killSlotB (h : Nat) (st : DPStateB) (s : Nat) : DPStateB :=
  let ℓ := st.len
  let x0 := orsB (digits3.map fun v => mvB h ℓ (selB h ℓ st.t s v) s v 0)
  let top := ℓ - 1
  let x1 := transpB h ℓ x0 s top
  let ord' := st.ord.map fun t => if t == top then s else t
  ⟨ℓ - 1, ord', truncB h ℓ x1⟩

/-- `dpStep` on trees. -/
noncomputable def dpStepB (h : Nat) (st : DPStateB) (s : Cpstep) : DPStateB :=
  let ℓ := st.len
  match s, st.ord with
  | .R n, _ => { st with ord := rot n st.ord }
  | .R', _ => if st.ord.length ≤ 1 then { st with t := .z } else { st with ord := rotr 1 st.ord }
  | .Y, s0 :: rest =>
    let x' := orsB (digits3.map fun v =>
      let y := selB h ℓ st.t s0 v
      orT (topB h ℓ (p312 v) (mvB h ℓ y s0 v (p231 v)))
        (topB h ℓ (p231 v) (mvB h ℓ y s0 v (p312 v))))
    ⟨ℓ + 1, s0 :: ℓ :: rest, x'⟩
  | .H, s0 :: s1 :: _ =>
    let x' := orsB (digits3.flatMap fun v1 => digits3.map fun v2 =>
      let y := selB h ℓ (selB h ℓ st.t s0 v1) s1 v2
      if v1 == v2 then
        orT (mvB h ℓ (mvB h ℓ y s0 v1 (p231 v1)) s1 v2 (p231 v1))
          (mvB h ℓ (mvB h ℓ y s0 v1 (p312 v1)) s1 v2 (p312 v1))
      else mvB h ℓ (mvB h ℓ y s0 v1 v2) s1 v2 v1)
    { st with t := x' }
  | .U, _ =>
    let x' := orsB (digits3.map fun v => topB h (ℓ + 1) v (topB h ℓ v st.t))
    ⟨ℓ + 2, ℓ :: (ℓ + 1) :: st.ord, x'⟩
  | .K, s0 :: s1 :: rest =>
    let x' := orsB (digits3.flatMap fun v1 => digits3.map fun v2 =>
      if v1 == v2 then .z else mvB h ℓ (selB h ℓ (selB h ℓ st.t s0 v1) s1 v2) s0 v1 (addd v1 v2))
    killSlotB h ⟨ℓ, s0 :: rest, x'⟩ s1
  | .A, s0 :: s1 :: rest =>
    let x' := orsB (digits3.map fun v => selB h ℓ (selB h ℓ st.t s0 v) s1 v)
    match rest with
    | [] => { st with t := x' }
    | _ :: _ =>
      let st1 := killSlotB h ⟨ℓ, rest ++ [s0], x'⟩ s1
      match st1.ord.getLast? with
      | some s0' => killSlotB h ⟨st1.len, st1.ord.dropLast, st1.t⟩ s0'
      | none => st1
  | _, _ => { st with t := .z }

/-- The base state (`h ≥ 2`: a single chunk). -/
def dpBaseB : DPStateB := ⟨2, [0, 1], .leaf (2 ^ 0 ||| 2 ^ 4 ||| 2 ^ 8)⟩

/-- `dpRun` on trees. -/
noncomputable def dpRunB (h : Nat) (cp : Cprog) : DPStateB :=
  List.rec (motive := fun _ => DPStateB) dpBaseB (fun s _ ih => dpStepB h ih s) cp

/-- `sortDigits` on trees. -/
noncomputable def sortDigitsB (h ℓ : Nat) : Nat → Nat → List Nat → B3T → B3T
  | 0, _, _, x => x
  | fuel + 1, i, ord, x =>
    match ord with
    | [] => x
    | s :: rest =>
      sortDigitsB h ℓ fuel (i + 1) (rest.map fun t => if t == i then s else t) (transpB h ℓ x s i)

/-- `dpB3` on trees. -/
noncomputable def dpB3B (h : Nat) (cp : Cprog) : B3T :=
  let st := dpRunB h cp
  sortDigitsB h st.len st.len 0 st.ord st.t

/-- `fold3 r` on a tree of height `r - h`. -/
noncomputable def fold3B (h r : Nat) (t : B3T) : B3T :=
  Bool.rec (fold3Root t) (mapT (fold3 r) t) (Nat.ble r h)

/-- The chunks of `2 ^ s` bits of the tree `t` (height `k`, chunks of `3 ^ h` bits) placed at bit
`off`, or-ed into `acc`. -/
noncomputable def convB (s h : Nat) : Nat → B3T → Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => B3T → Nat → List Nat → List Nat)
    (fun t off acc => B3T.rec (motive := fun _ => List Nat) acc
      (fun c => orAt (off / 2 ^ s) acc
        (toChunksAux s ((off % 2 ^ s + 3 ^ h) / 2 ^ s + 1) ((off % 2 ^ s + 3 ^ h) / 2 ^ s + 1)
          (Nat.shiftLeft (Nat.land c (ones (3 ^ h))) (off % 2 ^ s)) []))
      (fun _ _ _ _ _ _ => acc) t)
    (fun k ih t off acc => B3T.rec (motive := fun _ => List Nat) acc (fun _ => acc)
      (fun a b c _ _ _ => ih c (off + 2 * 3 ^ (h + k)) (ih b (off + 3 ^ (h + k)) (ih a off acc)))
      t)

/-- `dpP1` computed on base-3 chunks of `3 ^ h` bits, converted into chunks of `2 ^ s` bits for
the chunked conversion network (for `2 ≤ h` and programs of ring size `r`; otherwise `dpP1C`). -/
noncomputable def dpP1B (r s h : Nat) (cnv : NetC) (cp : Cprog) : List Nat :=
  bif Nat.ble 2 h && Nat.beq (dpRunB h cp).len r then
    splitGC r s (applyNetC s cnv (convB s h (r - 1 - h) (fold3B h r (dpB3B h cp)) 0 []))
  else dpP1C r s cnv cp

/-- `checkInit` on base-3 chunks. -/
noncomputable def checkInitB (r s h : Nat) (cnv : NetC) (cp : Cprog) (H0 : List Nat) : Bool :=
  dpP1B r s h cnv cp == expand r H0

/-- `checkFinal` on base-3 chunks. -/
noncomputable def checkFinalB (r s h : Nat) (cnv : NetC) (cpc : Cprog) (H : List Nat) : Bool :=
  covered (dpP1B r s h cnv cpc) (expand r H)


/-! ## Proofs -/

/-! ### Facts about the operations of `ColorDP.lean`

(Copies of private lemmas of `ColorDP.lean`.) -/

/-- The base-3 digit `s` of `j`. -/
private def dig (j s : Nat) : Nat := j / 3 ^ s % 3

private theorem testBit_sel {n x s v : Nat} (hs : s < n) (hv : v ≤ 2) (j : Nat) :
    (sel n x s v).testBit j = true ↔ x.testBit j = true ∧ j < 3 ^ n ∧ dig j s = v := by
  unfold sel
  rw [Nat.testBit_land, testBit_digitMask hs hv]
  simp [dig]

private theorem testBit_mv_core (y s v v' j : Nat) :
    (mv y s v v').testBit j = true ↔ ∃ K, K + v' * 3 ^ s = j + v * 3 ^ s ∧ y.testBit K = true := by
  unfold mv
  split
  · rename_i hvv
    rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq, Nat.sub_mul]
    have : v * 3 ^ s ≤ v' * 3 ^ s := Nat.mul_le_mul_right _ hvv
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨_, by omega, h2⟩
    · rintro ⟨K, hK, h2⟩
      refine ⟨by omega, ?_⟩
      have e : j - (v' * 3 ^ s - v * 3 ^ s) = K := by omega
      rw [e]; exact h2
  · rename_i hvv
    rw [Nat.testBit_shiftRight, Nat.sub_mul]
    have : v' * 3 ^ s ≤ v * 3 ^ s := Nat.mul_le_mul_right _ (by omega)
    constructor
    · intro h; exact ⟨_, by omega, h⟩
    · rintro ⟨K, hK, h2⟩
      have e : v * 3 ^ s - v' * 3 ^ s + j = K := by omega
      rw [e]; exact h2

private theorem mem_digits3 {u : Nat} : u ∈ digits3 ↔ u ≤ 2 := by
  simp only [digits3, List.mem_cons, List.not_mem_nil, or_false]; omega

private theorem testBit_fold3 (r w k : Nat) :
    (fold3 r w).testBit k = true ↔ k < 3 ^ (r - 1) ∧ (w.testBit k = true ∨
      w.testBit (k + 1 * 3 ^ (r - 1)) = true ∨ w.testBit (k + 2 * 3 ^ (r - 1)) = true) := by
  simp only [fold3, Nat.testBit_or, Nat.testBit_land, Nat.testBit_shiftRight,
    testBit_ones, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  rw [Nat.one_mul, Nat.add_comm k, Nat.add_comm k]
  tauto

namespace B3T

/-! ### Defining equations -/

@[simp] private theorem pick_zero (a b c : B3T) : pick 0 a b c = a := rfl
@[simp] private theorem pick_one (a b c : B3T) : pick 1 a b c = b := rfl
@[simp] private theorem pick_two (a b c : B3T) : pick 2 a b c = c := rfl
@[simp] private theorem put_zero (x : B3T) : put 0 x = .node x .z .z := rfl
@[simp] private theorem put_one (x : B3T) : put 1 x = .node .z x .z := rfl
@[simp] private theorem put_two (x : B3T) : put 2 x = .node .z .z x := rfl

@[simp] private theorem mapT_z (f : Nat → Nat) : mapT f .z = .z := rfl
@[simp] private theorem mapT_leaf (f : Nat → Nat) (c : Nat) : mapT f (.leaf c) = .leaf (f c) := rfl
@[simp] private theorem mapT_node (f : Nat → Nat) (a b c : B3T) :
    mapT f (.node a b c) = .node (mapT f a) (mapT f b) (mapT f c) := rfl

@[simp] private theorem orT_z (u : B3T) : orT .z u = u := rfl
@[simp] private theorem orT_leaf_z (c : Nat) : orT (.leaf c) .z = .leaf c := rfl
@[simp] private theorem orT_leaf_leaf (c d : Nat) : orT (.leaf c) (.leaf d) = .leaf (c ||| d) := rfl
@[simp] private theorem orT_leaf_node (c : Nat) (a b d : B3T) : orT (.leaf c)
    (.node a b d) = .leaf c := rfl
@[simp] private theorem orT_node_z (a b c : B3T) : orT (.node a b c) .z = .node a b c := rfl
@[simp] private theorem orT_node_leaf (a b c : B3T) (d : Nat) : orT (.node a b c)
    (.leaf d) = .node a b c :=
  rfl
@[simp] private theorem orT_node_node (a b c a' b' c' : B3T) :
    orT (.node a b c) (.node a' b' c') = .node (orT a a') (orT b b') (orT c c') := rfl

@[simp] private theorem child0_z : child0 .z = .z := rfl
@[simp] private theorem child0_leaf (c : Nat) : child0 (.leaf c) = .z := rfl
@[simp] private theorem child0_node (a b c : B3T) : child0 (.node a b c) = a := rfl
@[simp] private theorem fold3Root_z : fold3Root .z = .z := rfl
@[simp] private theorem fold3Root_leaf (c : Nat) : fold3Root (.leaf c) = .z := rfl
@[simp] private theorem fold3Root_node (a b c : B3T) : fold3Root (.node a b c) = orT (orT a b) c
    := rfl

@[simp] private theorem atT_z (g : B3T → B3T → B3T → B3T) (d : Nat) : atT g d .z = .z := by
  cases d <;> rfl
@[simp] private theorem atT_leaf (g : B3T → B3T → B3T → B3T) (d c : Nat) : atT g d
    (.leaf c) = .leaf c := by
  cases d <;> rfl
@[simp] private theorem atT_zero_node (g : B3T → B3T → B3T → B3T) (a b c : B3T) :
    atT g 0 (.node a b c) = g a b c := rfl
@[simp] private theorem atT_succ_node (g : B3T → B3T → B3T → B3T) (d : Nat) (a b c : B3T) :
    atT g (d + 1) (.node a b c) = .node (atT g d a) (atT g d b) (atT g d c) := rfl

/-! ### Semantics -/

/-- The number represented by a tree of height `k` with chunks of `3 ^ h` bits. -/
def val (h : Nat) : Nat → B3T → Nat
  | 0, .leaf c => c
  | k + 1, .node a b c =>
    val h k a ||| (val h k b <<< (1 * 3 ^ (h + k))) ||| (val h k c <<< (2 * 3 ^ (h + k)))
  | _, _ => 0

/-- The trees of height `k` (`z` has every height). -/
private def Shp : Nat → B3T → Prop
  | _, .z => True
  | 0, .leaf _ => True
  | k + 1, .node a b c => Shp k a ∧ Shp k b ∧ Shp k c
  | _, _ => False

/-- The chunk of index `j` of a tree of height `k` (`0` in the zero subtrees). -/
private def leafAt : Nat → B3T → Nat → Nat
  | 0, .leaf c, _ => c
  | k + 1, .node a b c, j => leafAt k (pick (j / 3 ^ k) a b c) (j % 3 ^ k)
  | _, _, _ => 0

@[simp] private theorem val_z (h k : Nat) : val h k .z = 0 := by cases k <;> rfl
@[simp] private theorem val_leaf (h c : Nat) : val h 0 (.leaf c) = c := rfl
private theorem val_node (h k : Nat) (a b c : B3T) : val h (k + 1) (.node a b c) =
    val h k a ||| (val h k b <<< (1 * 3 ^ (h + k))) ||| (val h k c <<< (2 * 3 ^ (h + k))) := rfl
@[simp] private theorem leafAt_z (k j : Nat) : leafAt k .z j = 0 := by cases k <;> rfl
@[simp] private theorem leafAt_leaf (c j : Nat) : leafAt 0 (.leaf c) j = c := rfl
private theorem leafAt_node (k : Nat) (a b c : B3T) (j : Nat) :
    leafAt (k + 1) (.node a b c) j = leafAt k (pick (j / 3 ^ k) a b c) (j % 3 ^ k) := rfl
@[simp] private theorem shp_z (k : Nat) : Shp k .z := by cases k <;> trivial
@[simp] private theorem shp_leaf_iff (k c : Nat) : Shp k (.leaf c) ↔ k = 0 := by
  cases k <;> simp [Shp]
@[simp] private theorem shp_node_iff (k : Nat) (a b c : B3T) :
    Shp k (.node a b c) ↔ ∃ k', k = k' + 1 ∧ Shp k' a ∧ Shp k' b ∧ Shp k' c := by
  cases k <;> simp [Shp]

private theorem shp_pick {k v : Nat} {a b c : B3T} (ha : Shp k a) (hb : Shp k b) (hc : Shp k c) :
    Shp k (pick v a b c) := by
  match v with
  | 0 => exact ha
  | 1 => exact hb
  | n + 2 => exact hc

private theorem shp_put {k v : Nat} {x : B3T} (hx : Shp k x) : Shp (k + 1) (put v x) := by
  match v with
  | 0 => exact ⟨hx, shp_z _, shp_z _⟩
  | 1 => exact ⟨shp_z _, hx, shp_z _⟩
  | n + 2 => exact ⟨shp_z _, shp_z _, hx⟩

/-- The chunks of a tree of height `k` are below `2 ^ w`. -/
private def JF (w k : Nat) (t : B3T) : Prop := ∀ j < 3 ^ k, leafAt k t j < 2 ^ w

private theorem pow3_pos (n : Nat) : 0 < 3 ^ n := Nat.pow_pos (by norm_num)

/-- The children of a node are indexed by the top digit. -/
private theorem jf_node {w k : Nat} {a b c : B3T} (h : JF w (k + 1) (.node a b c)) :
    JF w k a ∧ JF w k b ∧ JF w k c := by
  have key : ∀ d < 3, ∀ j < 3 ^ k, leafAt k (pick d a b c) j < 2 ^ w := by
    intro d hd j hj
    have hlt : d * 3 ^ k + j < 3 ^ (k + 1) := by
      rw [Nat.pow_succ]; have : d * 3 ^ k ≤ 2 * 3 ^ k := Nat.mul_le_mul_right _ (by omega)
      omega
    have := h _ hlt
    rwa [leafAt_node, Nat.mul_comm, Nat.mul_add_div (pow3_pos k), Nat.div_eq_of_lt hj,
      Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hj] at this
  exact ⟨key 0 (by omega), key 1 (by omega), key 2 (by omega)⟩

/-- The bits of three blocks of `W` bits. -/
private theorem testBit_or3 {A B C W : Nat} (hA : A < 2 ^ W) (hB : B < 2 ^ W) (hC : C < 2 ^ W)
    {q : Nat} (hq : q < W) (d : Nat) :
    (A ||| (B <<< (1 * W)) ||| (C <<< (2 * W))).testBit (q + d * W) =
      (if d = 0 then A.testBit q else if d = 1 then B.testBit q else if d = 2 then C.testBit q
        else false) := by
  have fA : ∀ i, W ≤ i → A.testBit i = false := fun i hi =>
    Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) hi))
  have fB : ∀ i, W ≤ i → B.testBit i = false := fun i hi =>
    Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hB (Nat.pow_le_pow_right (by norm_num) hi))
  have fC : ∀ i, W ≤ i → C.testBit i = false := fun i hi =>
    Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hC (Nat.pow_le_pow_right (by norm_num) hi))
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  match d with
  | 0 =>
    rw [decide_eq_false (show ¬ (q + 0 * W ≥ 1 * W) by omega),
      decide_eq_false (show ¬ (q + 0 * W ≥ 2 * W) by omega)]
    simp
  | 1 =>
    rw [fA _ (by omega), show q + 1 * W - 1 * W = q by omega,
      decide_eq_true (show q + 1 * W ≥ 1 * W by omega),
      decide_eq_false (show ¬ (q + 1 * W ≥ 2 * W) by omega)]
    simp
  | 2 =>
    rw [fA _ (by omega), fB _ (by omega), show q + 2 * W - 2 * W = q by omega,
      decide_eq_true (show q + 2 * W ≥ 2 * W by omega)]
    simp
  | d + 3 =>
    have h3 : 3 * W ≤ (d + 3) * W := Nat.mul_le_mul_right W (by omega)
    rw [fA _ (by omega), fB _ (by omega), fC _ (by omega)]
    simp

private theorem val_lt {h : Nat} : ∀ {k : Nat} {t : B3T}, Shp k t → JF (3 ^ h) k t →
    val h k t < 2 ^ 3 ^ (h + k)
  | 0, .z, _, _ => by simp
  | 0, .leaf c, _, hj => by simpa using hj 0 (by simp)
  | k + 1, .z, _, _ => by simp
  | k + 1, .node a b c, hs, hj => by
    obtain ⟨ha, hb, hc⟩ := hs
    obtain ⟨ja, jb, jc⟩ := jf_node hj
    have hA := val_lt ha ja
    have hB := val_lt hb jb
    have hC := val_lt hc jc
    have e : 3 ^ (h + (k + 1)) = 3 ^ (h + k) + 3 ^ (h + k) + 3 ^ (h + k) := by
      rw [← Nat.add_assoc, Nat.pow_succ]; ring
    rw [val_node, e]
    generalize 3 ^ (h + k) = W at hA hB hC ⊢
    have h1 : val h k a < 2 ^ (W + W + W) :=
      Nat.lt_of_lt_of_le hA (Nat.pow_le_pow_right (by norm_num) (by omega))
    have h2 : val h k b <<< (1 * W) < 2 ^ (W + W + W) := by
      rw [Nat.shiftLeft_eq, Nat.one_mul]
      calc val h k b * 2 ^ W < 2 ^ W * 2 ^ W := Nat.mul_lt_mul_of_pos_right hB (Nat.two_pow_pos _)
        _ = 2 ^ (W + W) := (Nat.pow_add _ _ _).symm
        _ ≤ 2 ^ (W + W + W) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : val h k c <<< (2 * W) < 2 ^ (W + W + W) := by
      rw [Nat.shiftLeft_eq]
      calc val h k c * 2 ^ (2 * W) < 2 ^ W * 2 ^ (2 * W) :=
            Nat.mul_lt_mul_of_pos_right hC (Nat.two_pow_pos _)
        _ = 2 ^ (W + W + W) := by rw [← Nat.pow_add]; congr 1; omega
    exact Nat.or_lt_two_pow (Nat.or_lt_two_pow h1 h2) h3
  | 0, .node _ _ _, hs, _ => absurd hs (by simp)
  | k + 1, .leaf _, hs, _ => absurd hs (by simp)

/-- Division and remainder by `3 ^ k` of `d * 3 ^ k + j'`. -/
private theorem div_mod_pow3 {k d j' : Nat} (hj' : j' < 3 ^ k) :
    (d * 3 ^ k + j') / 3 ^ k = d ∧ (d * 3 ^ k + j') % 3 ^ k = j' := by
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div (pow3_pos k), Nat.div_eq_of_lt hj', Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj']

/-- **The bits of a tree**: bit `p + 3^h * j` (`p < 3^h`) is bit `p` of the chunk `j`. -/
private theorem testBit_val {h : Nat} : ∀ {k : Nat} {t : B3T}, Shp k t → JF (3 ^ h) k t →
    ∀ {p : Nat}, p < 3 ^ h → ∀ j : Nat,
      (val h k t).testBit (p + 3 ^ h * j) = (decide (j < 3 ^ k) && (leafAt k t j).testBit p)
  | 0, .z, _, _, p, _, j => by simp
  | 0, .leaf c, _, hj, p, hp, j => by
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · simp
    · have hc : c < 2 ^ 3 ^ h := by simpa using hj 0 (by simp)
      have h1 : 3 ^ h * 1 ≤ 3 ^ h * j := Nat.mul_le_mul_left (3 ^ h) hpos
      have : c.testBit (p + 3 ^ h * j) = false := Nat.testBit_eq_false_of_lt
        (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [this, show ¬ j < 1 by omega]
  | k + 1, .z, _, _, p, _, j => by simp
  | k + 1, .node a b c, hs, hj, p, hp, j => by
    obtain ⟨ha, hb, hc⟩ := hs
    obtain ⟨ja, jb, jc⟩ := jf_node hj
    have W3 : 3 ^ (h + k) = 3 ^ h * 3 ^ k := Nat.pow_add _ _ _
    have hA := val_lt ha ja
    have hB := val_lt hb jb
    have hC := val_lt hc jc
    rw [val_node, leafAt_node]
    obtain ⟨d, j', hj', rfl⟩ : ∃ d j', j' < 3 ^ k ∧ j = d * 3 ^ k + j' :=
      ⟨j / 3 ^ k, j % 3 ^ k, Nat.mod_lt _ (pow3_pos k),
        by rw [Nat.mul_comm]; exact (Nat.div_add_mod j _).symm⟩
    obtain ⟨hdiv, hmod⟩ := div_mod_pow3 (d := d) hj'
    rw [hdiv, hmod]
    have hidx : p + 3 ^ h * (d * 3 ^ k + j') = (p + 3 ^ h * j') + d * 3 ^ (h + k) := by
      rw [W3]; ring
    have hlo : p + 3 ^ h * j' < 3 ^ (h + k) := by
      rw [W3]
      calc p + 3 ^ h * j' < 3 ^ h + 3 ^ h * j' := by omega
        _ = 3 ^ h * (j' + 1) := by ring
        _ ≤ 3 ^ h * 3 ^ k := Nat.mul_le_mul_left _ hj'
    rw [hidx, testBit_or3 hA hB hC hlo d, testBit_val ha ja hp j', testBit_val hb jb hp j',
      testBit_val hc jc hp j']
    simp only [hj', decide_true, Bool.true_and]
    have hk3 : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    match d with
    | 0 => rw [decide_eq_true (show 0 * 3 ^ k + j' < 3 ^ (k + 1) by omega)]; simp
    | 1 => rw [decide_eq_true (show 1 * 3 ^ k + j' < 3 ^ (k + 1) by omega)]; simp
    | 2 => rw [decide_eq_true (show 2 * 3 ^ k + j' < 3 ^ (k + 1) by omega)]; simp
    | d + 3 =>
      have h3k : 3 * 3 ^ k ≤ (d + 3) * 3 ^ k := Nat.mul_le_mul_right _ (by omega)
      rw [decide_eq_false (show ¬ (d + 3) * 3 ^ k + j' < 3 ^ (k + 1) by omega)]; simp
  | 0, .node _ _ _, hs, _, _, _, _ => absurd hs (by simp)
  | k + 1, .leaf _, hs, _, _, _, _ => absurd hs (by simp)

end B3T

/-! ### Base-3 digit arithmetic -/

private theorem dig_eq (j e : Nat) : dig j e = j / 3 ^ e % 3 := rfl

private theorem dig_lt (j e : Nat) : dig j e < 3 := Nat.mod_lt _ (by norm_num)

/-- Replace the base-3 digit `e` of `j` by `v`. -/
private def setDig (j e v : Nat) : Nat := j % 3 ^ e + 3 ^ e * v + 3 ^ (e + 1) * (j / 3 ^ (e + 1))

private theorem setDig_eq (j e v : Nat) :
    setDig j e v = (j % 3 ^ e + 3 ^ e * v) + 3 ^ (e + 1) * (j / 3 ^ (e + 1)) := rfl

private theorem mod_add_mul_div {a m b : Nat} (ha : a < m) : (a + m * b) / m = b ∧
    (a + m * b) % m = a := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le a) ha
  constructor
  · rw [Nat.add_comm, Nat.mul_add_div hm, Nat.div_eq_of_lt ha, Nat.add_zero]
  · rw [Nat.add_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ha]

private theorem pow3_succ (e : Nat) : 3 ^ (e + 1) = 3 ^ e * 3 := by rw [Nat.pow_succ]

/-- The digit decomposition of `j` at `e`. -/
private theorem decomp (j e : Nat) : j = j % 3 ^ e + 3 ^ e * dig j e + 3 ^ (e + 1) * (j / 3 ^
    (e + 1)) := by
  have h1 := Nat.div_add_mod j (3 ^ e)
  have h2 := Nat.div_add_mod (j / 3 ^ e) 3
  have h3 : j / 3 ^ (e + 1) = j / 3 ^ e / 3 := by rw [pow3_succ, Nat.div_div_eq_div_mul]
  rw [dig_eq, h3, pow3_succ]
  have : 3 ^ e * (j / 3 ^ e) = 3 ^ e * (j / 3 ^ e % 3) + 3 ^ e * 3 * (j / 3 ^ e / 3) := by
    conv_lhs => rw [← h2]
    ring
  omega

private theorem lo_lt (j e v : Nat) (hv : v ≤ 2) : j % 3 ^ e + 3 ^ e * v < 3 ^ (e + 1) := by
  have := Nat.mod_lt j (pow3_pos e)
  have : 3 ^ e * v ≤ 3 ^ e * 2 := Nat.mul_le_mul_left _ hv
  rw [pow3_succ]; omega

private theorem setDig_div {j e v : Nat} (hv : v ≤ 2) : setDig j e v / 3 ^ (e + 1) = j / 3 ^
    (e + 1) :=
  (mod_add_mul_div (lo_lt j e v hv)).1

private theorem dig_setDig {j e v : Nat} (hv : v ≤ 2) : dig (setDig j e v) e = v := by
  rw [dig_eq, setDig, Nat.add_assoc, Nat.add_comm (j % 3 ^ e),
    show 3 ^ e * v + 3 ^ (e + 1) * (j / 3 ^ (e + 1)) = 3 ^ e * (v + 3 * (j / 3 ^ (e + 1))) by
      rw [pow3_succ]; ring,
    Nat.add_comm, (mod_add_mul_div (Nat.mod_lt j (pow3_pos e))).1]
  omega

private theorem setDig_self (j e : Nat) : setDig j e (dig j e) = j := (decomp j e).symm

private theorem setDig_mod_pow_self {j e v : Nat} : setDig j e v % 3 ^ e = j % 3 ^ e := by
  rw [setDig, Nat.add_assoc,
    show 3 ^ e * v + 3 ^ (e + 1) * (j / 3 ^ (e + 1)) = 3 ^ e * (v + 3 * (j / 3 ^ (e + 1))) by
      rw [pow3_succ]; ring,
    (mod_add_mul_div (Nat.mod_lt j (pow3_pos e))).2]

private theorem setDig_setDig {j e v v' : Nat} (hv : v ≤ 2) : setDig
    (setDig j e v) e v' = setDig j e v' := by
  rw [setDig_eq (setDig j e v) e v', setDig_mod_pow_self, setDig_div hv]
  rfl

/-- `setDig` changes `j` by the digit difference. -/
private theorem setDig_add {j e v : Nat} : setDig j e v + dig j e * 3 ^ e = j + v * 3 ^ e := by
  have := decomp j e
  unfold setDig
  rw [Nat.mul_comm (dig j e), Nat.mul_comm v]
  omega

private theorem pow3_sub {m e : Nat} (he : e ≤ m) : 3 ^ m = 3 ^ e * 3 ^ (m - e) := by
  rw [← Nat.pow_add]; congr 1; omega

/-- Quotient of `a + 3^m * b` by a smaller power. -/
private theorem add_mul_div_pow_le {a m b e : Nat} (he : e ≤ m) :
    (a + 3 ^ m * b) / 3 ^ e = a / 3 ^ e + 3 ^ (m - e) * b := by
  rw [pow3_sub he, Nat.mul_assoc, Nat.add_mul_div_left _ _ (pow3_pos e)]

/-- Remainder of `a + 3^m * b` by a smaller power. -/
private theorem add_mul_mod_pow_le {a m b e : Nat} (he : e ≤ m) :
    (a + 3 ^ m * b) % 3 ^ e = a % 3 ^ e := by
  rw [pow3_sub he, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- Quotient of `a + 3^m * b` (`a < 3^m`) by a larger power. -/
private theorem add_mul_div_pow_ge {a m b e : Nat} (ha : a < 3 ^ m) (he : m ≤ e) :
    (a + 3 ^ m * b) / 3 ^ e = b / 3 ^ (e - m) := by
  rw [pow3_sub he, ← Nat.div_div_eq_div_mul, (mod_add_mul_div ha).1]

/-- Remainder of `a + 3^m * b` (`a < 3^m`) by a larger power. -/
private theorem add_mul_mod_pow_ge {a m b e : Nat} (ha : a < 3 ^ m) (he : m ≤ e) :
    (a + 3 ^ m * b) % 3 ^ e = a + 3 ^ m * (b % 3 ^ (e - m)) := by
  have h1 := Nat.div_add_mod b (3 ^ (e - m))
  have key : a + 3 ^ m * b = (a + 3 ^ m * (b % 3 ^ (e - m))) + 3 ^ e * (b / 3 ^ (e - m)) := by
    rw [pow3_sub he]
    conv_lhs => rw [← h1]
    ring
  have hlt : a + 3 ^ m * (b % 3 ^ (e - m)) < 3 ^ e := by
    have h2 : b % 3 ^ (e - m) + 1 ≤ 3 ^ (e - m) := Nat.mod_lt _ (pow3_pos _)
    have h3 : 3 ^ m * (b % 3 ^ (e - m) + 1) ≤ 3 ^ m * 3 ^ (e - m) := Nat.mul_le_mul_left _ h2
    rw [pow3_sub he]; rw [Nat.mul_add, Nat.mul_one] at h3; omega
  rw [key, (mod_add_mul_div hlt).2]

/-- The digits of `a + 3^m * b` (`a < 3^m`). -/
private theorem dig_add_mul {a m b : Nat} (ha : a < 3 ^ m) (e : Nat) :
    dig (a + 3 ^ m * b) e = if e < m then dig a e else dig b (e - m) := by
  split
  · rename_i he
    rw [dig_eq, dig_eq, add_mul_div_pow_le (Nat.le_of_lt he),
      show 3 ^ (m - e) = 3 * 3 ^ (m - e - 1) by rw [← Nat.pow_succ']; congr 1; omega,
      Nat.mul_assoc, Nat.add_mul_mod_self_left]
  · rename_i he
    rw [dig_eq, dig_eq, add_mul_div_pow_ge ha (by omega)]

private theorem dig_low {j e e' : Nat} (h : e' < e) : dig j e' = dig (j % 3 ^ e) e' := by
  conv_lhs => rw [← Nat.mod_add_div j (3 ^ e)]
  rw [dig_add_mul (Nat.mod_lt _ (pow3_pos e)), ite_eq_left h]

private theorem dig_high {j e e' : Nat} (h : e ≤ e') : dig j e' = dig (j / 3 ^ e) (e' - e) := by
  conv_lhs => rw [← Nat.mod_add_div j (3 ^ e)]
  rw [dig_add_mul (Nat.mod_lt _ (pow3_pos e)), ite_eq_right (by omega)]

private theorem dig_setDig_ne {j e e' v : Nat} (hv : v ≤ 2) (hne : e' ≠ e) :
    dig (setDig j e v) e' = dig j e' := by
  rw [setDig_eq, dig_add_mul (lo_lt j e v hv)]
  split
  · rename_i h1
    have h2 : e' < e := by omega
    rw [dig_add_mul (Nat.mod_lt j (pow3_pos e)), ite_eq_left h2, ← dig_low h2]
  · rename_i h1
    rw [← dig_high (by omega)]

/-- `setDig` in the low part of `p + 3^h * j`. -/
private theorem setDig_lo {p h j s v : Nat} (hs : s < h) :
    setDig (p + 3 ^ h * j) s v = setDig p s v + 3 ^ h * j := by
  rw [setDig_eq, setDig_eq, add_mul_mod_pow_le (Nat.le_of_lt hs), add_mul_div_pow_le hs,
    Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add, show s + 1 + (h - (s + 1)) = h by omega]
  ring

/-- `setDig` in the high part of `p + 3^h * j`. -/
private theorem setDig_hi {p h j s v : Nat} (hp : p < 3 ^ h) (hs : h ≤ s) :
    setDig (p + 3 ^ h * j) s v = p + 3 ^ h * setDig j (s - h) v := by
  rw [setDig_eq, setDig_eq, add_mul_mod_pow_ge hp hs, add_mul_div_pow_ge hp (by omega),
    show s + 1 - h = s - h + 1 by omega]
  have e1 : 3 ^ s = 3 ^ h * 3 ^ (s - h) := pow3_sub hs
  have e2 : 3 ^ (s + 1) = 3 ^ h * 3 ^ (s - h + 1) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [e1, e2]; ring

private theorem setDig_lt {j n e v : Nat} (hj : j < 3 ^ n) (he : e < n) (hv : v ≤ 2)
    : setDig j e v < 3 ^ n := by
  rw [setDig_eq]
  have h1 : j / 3 ^ (e + 1) < 3 ^ (n - (e + 1)) := by
    rw [Nat.div_lt_iff_lt_mul (pow3_pos _), ← Nat.pow_add, show n - (e + 1) + (e + 1) = n by omega]
    exact hj
  have h2 := lo_lt j e v hv
  have h3 : 3 ^ (e + 1) * (j / 3 ^ (e + 1) + 1) ≤ 3 ^ (e + 1) * 3 ^ (n - (e + 1)) :=
    Nat.mul_le_mul_left _ h1
  rw [← Nat.pow_add, show e + 1 + (n - (e + 1)) = n by omega, Nat.mul_add, Nat.mul_one] at h3
  omega

/-- Moving down one level of a tree: the top digit `k` of an index below `3^(k+1)`. -/
private theorem div_pow_eq_dig {j k : Nat} (hj : j < 3 ^ (k + 1)) : j / 3 ^ k = dig j k := by
  rw [dig_eq, Nat.mod_eq_of_lt]
  rw [Nat.div_lt_iff_lt_mul (pow3_pos k)]
  have : 3 ^ (k + 1) = 3 * 3 ^ k := by rw [Nat.pow_succ]; ring
  omega

private theorem setDig_top {j k v : Nat} (hj : j < 3 ^ (k + 1)) :
    setDig j k v / 3 ^ k = v ∧ setDig j k v % 3 ^ k = j % 3 ^ k := by
  have h0 : j / 3 ^ (k + 1) = 0 := Nat.div_eq_of_lt hj
  rw [setDig_eq, h0, Nat.mul_zero, Nat.add_zero]
  exact mod_add_mul_div (Nat.mod_lt j (pow3_pos k))

private theorem setDig_below {j k e v : Nat} (he : e < k) (hv : v ≤ 2) :
    setDig j e v / 3 ^ k = j / 3 ^ k ∧ setDig j e v % 3 ^ k = setDig (j % 3 ^ k) e v := by
  constructor
  · rw [setDig_eq, add_mul_div_pow_ge (lo_lt j e v hv) (by omega), Nat.div_div_eq_div_mul,
      ← Nat.pow_add, show e + 1 + (k - (e + 1)) = k by omega]
  · rw [setDig_eq, add_mul_mod_pow_ge (lo_lt j e v hv) (by omega), setDig_eq,
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 3 (Nat.le_of_lt he))]
    congr 2
    rw [pow3_sub (show e + 1 ≤ k by omega), Nat.mod_mul_right_div_self]

private theorem dig_mod_pow {j k e : Nat} (he : e < k) : dig (j % 3 ^ k) e = dig j e :=
    (dig_low he).symm

/-! ### The chunks of the tree operations -/

namespace B3T

private theorem pick_map (F : B3T → B3T) (d : Nat) (a b c : B3T) :
    pick d (F a) (F b) (F c) = F (pick d a b c) := by
  match d with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => rfl

private theorem pick_map2 (G : B3T → B3T → B3T) (d : Nat) (a b c a' b' c' : B3T) :
    pick d (G a a') (G b b') (G c c') = G (pick d a b c) (pick d a' b' c') := by
  match d with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => rfl

private theorem shp_mapT (f : Nat → Nat) : ∀ {k : Nat} {t : B3T}, Shp k t → Shp k (mapT f t)
  | _, .z, _ => shp_z _
  | 0, .leaf _, _ => trivial
  | k + 1, .node a b c, hs => ⟨shp_mapT f hs.1, shp_mapT f hs.2.1, shp_mapT f hs.2.2⟩
  | _ + 1, .leaf _, hs => absurd hs (by simp)
  | 0, .node _ _ _, hs => absurd hs (by simp)

private theorem leafAt_mapT {f : Nat → Nat} (hf : f 0 = 0) :
    ∀ {k : Nat} {t : B3T}, Shp k t → ∀ j, leafAt k (mapT f t) j = f (leafAt k t j)
  | _, .z, _, j => by simp [hf]
  | 0, .leaf _, _, j => rfl
  | k + 1, .node a b c, hs, j => by
    rw [mapT_node, leafAt_node, leafAt_node, pick_map (mapT f)]
    exact leafAt_mapT hf (shp_pick hs.1 hs.2.1 hs.2.2) _
  | _ + 1, .leaf _, hs, _ => absurd hs (by simp)
  | 0, .node _ _ _, hs, _ => absurd hs (by simp)

private theorem shp_orT : ∀ {k : Nat} {a b : B3T}, Shp k a → Shp k b → Shp k (orT a b)
  | _, .z, _, _, hb => hb
  | 0, .leaf _, .z, _, _ => trivial
  | 0, .leaf _, .leaf _, _, _ => trivial
  | k + 1, .node _ _ _, .z, ha, _ => ha
  | k + 1, .node _ _ _, .node _ _ _, ha, hb =>
    ⟨shp_orT ha.1 hb.1, shp_orT ha.2.1 hb.2.1, shp_orT ha.2.2 hb.2.2⟩
  | 0, .leaf _, .node _ _ _, _, hb => absurd hb (by simp)
  | _ + 1, .node _ _ _, .leaf _, _, hb => absurd hb (by simp)
  | _ + 1, .leaf _, _, ha, _ => absurd ha (by simp)
  | 0, .node _ _ _, _, ha, _ => absurd ha (by simp)

private theorem leafAt_orT : ∀ {k : Nat} {a b : B3T}, Shp k a → Shp k b → ∀ j,
    leafAt k (orT a b) j = leafAt k a j ||| leafAt k b j
  | _, .z, _, _, _, j => by simp
  | 0, .leaf _, .z, _, _, j => by simp
  | 0, .leaf _, .leaf _, _, _, j => rfl
  | k + 1, .node _ _ _, .z, _, _, j => by simp
  | k + 1, .node a b c, .node a' b' c', ha, hb, j => by
    rw [orT_node_node, leafAt_node, leafAt_node, leafAt_node, pick_map2 orT]
    exact leafAt_orT (shp_pick ha.1 ha.2.1 ha.2.2) (shp_pick hb.1 hb.2.1 hb.2.2) _
  | 0, .leaf _, .node _ _ _, _, hb, _ => absurd hb (by simp)
  | _ + 1, .node _ _ _, .leaf _, _, hb, _ => absurd hb (by simp)
  | _ + 1, .leaf _, _, ha, _, _ => absurd ha (by simp)
  | 0, .node _ _ _, _, ha, _, _ => absurd ha (by simp)

private theorem leafAt_put {k v : Nat} (hv : v ≤ 2) (x : B3T) {j : Nat} (hj : j < 3 ^ (k + 1)) :
    leafAt (k + 1) (put v x) j = if dig j k = v then leafAt k x (j % 3 ^ k) else 0 := by
  have hd := dig_lt j k
  have e : put v x = .node (if v = 0 then x else .z) (if v = 1 then x else .z)
      (if v = 2 then x else .z) := by
    rcases (show v = 0 ∨ v = 1 ∨ v = 2 by omega) with rfl | rfl | rfl <;> rfl
  rw [e, leafAt_node, div_pow_eq_dig hj]
  generalize dig j k = d at hd ⊢
  rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl <;>
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 by omega) with rfl | rfl | rfl <;> simp

private theorem shp_atT_mv (v v' : Nat) : ∀ (d : Nat) {k : Nat} {t : B3T}, Shp k t → d < k →
    Shp k (atT (mvNode v v') d t)
  | _, _, .z, _, _ => by simp
  | 0, k + 1, .node a b c, hs, _ => shp_put (shp_pick hs.1 hs.2.1 hs.2.2)
  | d + 1, k + 1, .node a b c, hs, hd =>
    ⟨shp_atT_mv v v' d hs.1 (by omega), shp_atT_mv v v' d hs.2.1 (by omega),
      shp_atT_mv v v' d hs.2.2 (by omega)⟩
  | _, _ + 1, .leaf _, hs, _ => absurd hs (by simp)
  | _, 0, .node _ _ _, hs, _ => absurd hs (by simp)
  | _, 0, .leaf _, _, hd => absurd hd (by omega)

/-- The chunks after rewriting the digit `k - 1 - d` from `v` to `v'` (tree level). -/
private theorem leafAt_atT_mv {v v' : Nat} (hv : v ≤ 2) (hv' : v' ≤ 2) :
    ∀ (d : Nat) {k : Nat} {t : B3T}, Shp k t → d < k → ∀ j < 3 ^ k,
      leafAt k (atT (mvNode v v') d t) j =
        if dig j (k - 1 - d) = v' then leafAt k t (setDig j (k - 1 - d) v) else 0
  | _, _, .z, _, _, j, _ => by simp
  | 0, k + 1, .node a b c, hs, _, j, hj => by
    rw [atT_zero_node, mvNode, leafAt_put hv' _ hj, show k + 1 - 1 - 0 = k by omega]
    split
    · rw [leafAt_node, (setDig_top hj).1, (setDig_top hj).2]
    · rfl
  | d + 1, k + 1, .node a b c, hs, hd, j, hj => by
    have hk : d < k := by omega
    have hm : j % 3 ^ k < 3 ^ k := Nat.mod_lt _ (pow3_pos k)
    rw [atT_succ_node, leafAt_node, pick_map (atT (mvNode v v') d),
      leafAt_atT_mv hv hv' d (shp_pick hs.1 hs.2.1 hs.2.2) hk _ hm,
      show k + 1 - 1 - (d + 1) = k - 1 - d by omega, dig_mod_pow (by omega)]
    split
    · rw [leafAt_node, (setDig_below (by omega) hv).1, (setDig_below (by omega) hv).2]
    · rfl
  | _, _ + 1, .leaf _, hs, _, _, _ => absurd hs (by simp)
  | _, 0, .node _ _ _, hs, _, _, _ => absurd hs (by simp)
  | _, 0, .leaf _, _, hd, _, _ => absurd hd (by omega)

private theorem leafAt_child0 {k : Nat} {t : B3T} (hs : Shp (k + 1) t) {j : Nat} (hj : j < 3 ^ k) :
    leafAt k (child0 t) j = leafAt (k + 1) t j := by
  match t, hs with
  | .z, _ => simp
  | .node a b c, _ =>
    rw [child0_node, leafAt_node, Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, pick_zero]

private theorem shp_child0 {k : Nat} {t : B3T} (hs : Shp (k + 1) t) : Shp k (child0 t) := by
  match t, hs with
  | .z, _ => simp
  | .node _ _ _, hs => exact hs.1

private theorem shp_fold3Root {k : Nat} {t : B3T} (hs : Shp (k + 1) t) : Shp k (fold3Root t) := by
  match t, hs with
  | .z, _ => simp
  | .node _ _ _, hs => exact shp_orT (shp_orT hs.1 hs.2.1) hs.2.2

private theorem leafAt_fold3Root {k : Nat} {t : B3T} (hs : Shp (k + 1) t) {j : Nat} (hj
    : j < 3 ^ k) :
    leafAt k (fold3Root t) j = leafAt (k + 1) t j ||| leafAt (k + 1) t (1 * 3 ^ k + j) |||
      leafAt (k + 1) t (2 * 3 ^ k + j) := by
  match t, hs with
  | .z, _ => simp
  | .node a b c, hs =>
    rw [fold3Root_node, leafAt_orT (shp_orT hs.1 hs.2.1) hs.2.2,
      leafAt_orT hs.1 hs.2.1, leafAt_node, leafAt_node, leafAt_node,
      (div_mod_pow3 (d := 1) hj).1, (div_mod_pow3 (d := 1) hj).2,
      (div_mod_pow3 (d := 2) hj).1, (div_mod_pow3 (d := 2) hj).2,
      Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
    rfl

end B3T

/-! ### The DP primitives on trees -/

/-- The tree of a DP state with `ℓ` slots: height `ℓ - h`, chunks below `2 ^ 3 ^ min ℓ h`. -/
private def TInv (h ℓ : Nat) (t : B3T) : Prop := Shp (ℓ - h) t ∧ JF (3 ^ min ℓ h) (ℓ - h) t

/-- The number represented by the tree of a DP state with `ℓ` slots. -/
private def V (h ℓ : Nat) (t : B3T) : Nat := val h (ℓ - h) t

/-- All entries of `x` are below `3 ^ n` and have the digit `s` equal to `v`. -/
private def DigN (n s v x : Nat) : Prop := ∀ K, x.testBit K = true → K < 3 ^ n ∧ dig K s = v

private theorem pow3_min_le (ℓ h : Nat) : 3 ^ min ℓ h ≤ 3 ^ h :=
  Nat.pow_le_pow_right (by norm_num) (Nat.min_le_right _ _)

private theorem jf_mono {w w' k : Nat} {t : B3T} (hw : w ≤ w') (h : JF w k t) : JF w' k t :=
  fun j hj => Nat.lt_of_lt_of_le (h j hj) (Nat.pow_le_pow_right (by norm_num) hw)

private theorem lt_of_testBit_of_lt {x w p : Nat} (hx : x < 2 ^ w) (hb : x.testBit p = true)
    : p < w := by
  by_contra hc
  rw [Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le hx
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hc)))] at hb
  exact absurd hb (by decide)

private theorem testBit_V {h ℓ : Nat} {t : B3T} (hinv : TInv h ℓ t) {p : Nat} (hp : p < 3 ^ h) (j
    : Nat) :
    (V h ℓ t).testBit (p + 3 ^ h * j) =
      (decide (j < 3 ^ (ℓ - h)) && (leafAt (ℓ - h) t j).testBit p) :=
  testBit_val hinv.1 (jf_mono (pow3_min_le ℓ h) hinv.2) hp j

private theorem leaf_bit_lt {h ℓ : Nat} {t : B3T} (hinv : TInv h ℓ t) {j p : Nat} (hj : j < 3 ^
    (ℓ - h))
    (hb : (leafAt (ℓ - h) t j).testBit p = true) : p < 3 ^ min ℓ h :=
  lt_of_testBit_of_lt (hinv.2 j hj) hb

private theorem idx_lt {h ℓ p j : Nat} (hp : p < 3 ^ min ℓ h) (hj : j < 3 ^ (ℓ - h)) :
    p + 3 ^ h * j < 3 ^ ℓ := by
  rcases Nat.le_total h ℓ with hl | hl
  · rw [Nat.min_eq_right hl] at hp
    have h1 : 3 ^ h * (j + 1) ≤ 3 ^ h * 3 ^ (ℓ - h) := Nat.mul_le_mul_left _ hj
    rw [← pow3_sub hl, Nat.mul_add, Nat.mul_one] at h1
    omega
  · rw [Nat.min_eq_left hl] at hp
    have : ℓ - h = 0 := by omega
    rw [this, Nat.pow_zero] at hj
    have : j = 0 := by omega
    subst this; simpa using hp

private theorem eq_of_testBit_decomp {h x y : Nat}
    (H : ∀ p j, p < 3 ^ h → x.testBit (p + 3 ^ h * j) = y.testBit (p + 3 ^ h * j)) : x = y := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := H (i % 3 ^ h) (i / 3 ^ h) (Nat.mod_lt _ (pow3_pos h))
  rwa [Nat.mod_add_div] at this

/-- The digits of `p + 3^h * j`. -/
private theorem dig_lo {h p j s : Nat} (hp : p < 3 ^ h) (hs : s < h) : dig
    (p + 3 ^ h * j) s = dig p s := by
  rw [dig_add_mul hp, ite_eq_left hs]

private theorem dig_hi {h p j s : Nat} (hp : p < 3 ^ h) (hs : h ≤ s) :
    dig (p + 3 ^ h * j) s = dig j (s - h) := by
  rw [dig_add_mul hp, ite_eq_right (by omega)]

private theorem testBit_sel' {n x s v : Nat} (hs : s < n) (hv : v ≤ 2) (i : Nat) :
    (sel n x s v).testBit i = (x.testBit i && decide (i < 3 ^ n) && decide (dig i s = v)) := by
  rw [Bool.eq_iff_iff, testBit_sel hs hv]; simp [Bool.and_assoc]

/-- The bits of a digit rewrite, with the source index given by `setDig`. -/
private theorem testBit_mv_set {n y s v v' : Nat} (hy : DigN n s v y) (hv' : v' ≤ 2) (i : Nat) :
    (mv y s v v').testBit i = (decide (dig i s = v') && y.testBit (setDig i s v)) := by
  rw [Bool.eq_iff_iff, testBit_mv_core]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨K, hK, hyK⟩
    obtain ⟨-, hKs⟩ := hy K hyK
    have e1 : setDig K s v' = i := by
      have := setDig_add (j := K) (e := s) (v := v'); rw [hKs] at this; omega
    subst e1
    refine ⟨dig_setDig hv', ?_⟩
    rw [setDig_setDig hv', ← hKs, setDig_self]; exact hyK
  · rintro ⟨his, hyK⟩
    refine ⟨_, ?_, hyK⟩
    have := setDig_add (j := i) (e := s) (v := v); rw [his] at this; omega

private theorem digN_sel {n x s v : Nat} (hs : s < n) (hv : v ≤ 2) : DigN n s v (sel n x s v) := by
  intro K hK
  rw [testBit_sel hs hv] at hK
  exact ⟨hK.2.1, hK.2.2⟩

private theorem digN_sel_of {n x s v s' v' : Nat} (h : DigN n s v x) (hs' : s' < n) (hv' : v' ≤ 2) :
    DigN n s v (sel n x s' v') := by
  intro K hK
  rw [testBit_sel hs' hv'] at hK
  exact h K hK.1

private theorem digN_mv_other {n y s v v' s' w : Nat} (hy : DigN n s v y) (hy' : DigN n s' w y)
    (hs : s < n) (hv' : v' ≤ 2) (hne : s' ≠ s) : DigN n s' w (mv y s v v') := by
  intro i hi
  rw [testBit_mv_set hy hv'] at hi
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
  obtain ⟨his, hyK⟩ := hi
  have hKs := (hy _ hyK).2
  have hv : v ≤ 2 := by have := dig_lt (setDig i s v) s; omega
  obtain ⟨hK, hKs'⟩ := hy' _ hyK
  have e : setDig (setDig i s v) s v' = i := by rw [setDig_setDig hv, ← his, setDig_self]
  refine ⟨e ▸ setDig_lt hK hs hv', ?_⟩
  rw [← hKs', dig_setDig_ne hv hne]

private theorem blt_true {a b : Nat} (h : a < b) : Nat.blt a b = true := by rw [Nat.blt_eq]; exact h
private theorem blt_false {a b : Nat} (h : b ≤ a) : Nat.blt a b = false := by
  cases hb : Nat.blt a b
  · rfl
  · rw [Nat.blt_eq] at hb; omega
private theorem ble_true {a b : Nat} (h : a ≤ b) : Nat.ble a b = true := by rw [Nat.ble_eq]; exact h
private theorem ble_false {a b : Nat} (h : b < a) : Nat.ble a b = false := by
  cases hb : Nat.ble a b
  · rfl
  · rw [Nat.ble_eq] at hb; omega

private theorem selB_lo {h ℓ s v : Nat} {t : B3T} (hs : s < h) :
    selB h ℓ t s v = mapT (fun c => Nat.land c (digitMask (min ℓ h) s v)) t := by
  unfold selB; rw [blt_true hs]

private theorem selB_hi {h ℓ s v : Nat} {t : B3T} (hs : h ≤ s) :
    selB h ℓ t s v = atT (mvNode v v) (ℓ - 1 - s) t := by
  unfold selB; rw [blt_false hs]

private theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem mvB_same {h ℓ s v : Nat} {t : B3T} : mvB h ℓ t s v v = t := by
  unfold mvB; rw [Nat.beq_refl]

private theorem mvB_lo {h ℓ s v v' : Nat} {t : B3T} (hvv : v ≠ v') (hs : s < h) :
    mvB h ℓ t s v v' = mapT (fun c => mv c s v v') t := by
  unfold mvB; rw [beq_false_of_ne hvv, blt_true hs]

private theorem mvB_hi {h ℓ s v v' : Nat} {t : B3T} (hvv : v ≠ v') (hs : h ≤ s) :
    mvB h ℓ t s v v' = atT (mvNode v v') (ℓ - 1 - s) t := by
  unfold mvB; rw [beq_false_of_ne hvv, blt_false hs]

private theorem mv_same (y s v : Nat) : mv y s v v = y := by
  unfold mv; simp

private theorem mv_zero (s v v' : Nat) : mv 0 s v v' = 0 := by
  unfold mv; split <;> simp

/-- The high-digit rewrite keeps the tree invariant. -/
private theorem tinv_atT_mv {h ℓ s v v' : Nat} {t : B3T} (hinv : TInv h ℓ t) (hs : s < ℓ) (hsh
    : h ≤ s)
    (hv : v ≤ 2) (hv' : v' ≤ 2) : TInv h ℓ (atT (mvNode v v') (ℓ - 1 - s) t) := by
  have hd : ℓ - 1 - s < ℓ - h := by omega
  refine ⟨shp_atT_mv v v' _ hinv.1 hd, fun j hj => ?_⟩
  rw [leafAt_atT_mv hv hv' _ hinv.1 hd j hj]
  split
  · exact hinv.2 _ (setDig_lt hj (by omega) hv)
  · exact Nat.two_pow_pos _

/-- **`sel` on trees.** -/
private theorem selB_spec {h ℓ s v : Nat} {t : B3T} (hinv : TInv h ℓ t) (hs : s < ℓ) (hv : v ≤ 2) :
    TInv h ℓ (selB h ℓ t s v) ∧ V h ℓ (selB h ℓ t s v) = sel ℓ (V h ℓ t) s v := by
  rcases Nat.lt_or_ge s h with hsh | hsh
  · rw [selB_lo hsh]
    have hsm : s < min ℓ h := Nat.lt_min.2 ⟨hs, hsh⟩
    have hf : (fun c => Nat.land c (digitMask (min ℓ h) s v)) 0 = 0 := Nat.zero_and _
    have hinv' : TInv h ℓ (mapT (fun c => Nat.land c (digitMask (min ℓ h) s v)) t) :=
      ⟨shp_mapT _ hinv.1, fun j hj => by
        rw [leafAt_mapT hf hinv.1]; exact Nat.lt_of_le_of_lt Nat.and_le_left (hinv.2 j hj)⟩
    refine ⟨hinv', eq_of_testBit_decomp (h := h) fun p j hp => ?_⟩
    rw [testBit_sel' hs hv, testBit_V hinv' hp, testBit_V hinv hp, leafAt_mapT hf hinv.1,
      Nat.land_eq, Nat.testBit_and, testBit_digitMask hsm hv, dig_lo hp hsh, ← dig_eq]
    by_cases hj : j < 3 ^ (ℓ - h)
    · cases hb : (leafAt (ℓ - h) t j).testBit p
      · simp
      · have h1 := leaf_bit_lt hinv hj hb
        simp [hj, h1, idx_lt h1 hj]
    · simp [hj]
  · rw [selB_hi hsh]
    have hd : ℓ - 1 - s < ℓ - h := by omega
    have he : ℓ - h - 1 - (ℓ - 1 - s) = s - h := by omega
    have hinv' := tinv_atT_mv hinv hs hsh hv hv
    refine ⟨hinv', eq_of_testBit_decomp (h := h) fun p j hp => ?_⟩
    rw [testBit_sel' hs hv, testBit_V hinv' hp, testBit_V hinv hp, dig_hi hp hsh]
    by_cases hj : j < 3 ^ (ℓ - h)
    · rw [leafAt_atT_mv hv hv _ hinv.1 hd j hj, he]
      split
      · rename_i hdj
        have e : setDig j (s - h) v = j := by rw [← hdj, setDig_self]
        rw [e]
        cases hb : (leafAt (ℓ - h) t j).testBit p
        · simp
        · have h1 := leaf_bit_lt hinv hj hb
          simp [hj, idx_lt h1 hj, hdj]
      · rename_i hdj; simp [hdj]
    · simp [hj]

/-- **`mv` on trees** (all entries having the digit `s = v`). -/
private theorem mvB_spec {h ℓ s v v' : Nat} {t : B3T} (hinv : TInv h ℓ t) (hs : s < ℓ) (hv : v ≤ 2)
    (hv' : v' ≤ 2) (hd : DigN ℓ s v (V h ℓ t)) :
    TInv h ℓ (mvB h ℓ t s v v') ∧ V h ℓ (mvB h ℓ t s v v') = mv (V h ℓ t) s v v' := by
  by_cases hvv : v = v'
  · subst hvv; rw [mvB_same, mv_same]; exact ⟨hinv, rfl⟩
  rcases Nat.lt_or_ge s h with hsh | hsh
  · rw [mvB_lo hvv hsh]
    have hsm : s < min ℓ h := Nat.lt_min.2 ⟨hs, hsh⟩
    have hf : (fun c => mv c s v v') 0 = 0 := mv_zero s v v'
    -- every chunk has digit `s = v`
    have hdc : ∀ j < 3 ^ (ℓ - h), DigN (min ℓ h) s v (leafAt (ℓ - h) t j) := by
      intro j hj P hP
      have hPl := leaf_bit_lt hinv hj hP
      have hP' : P < 3 ^ h := Nat.lt_of_lt_of_le hPl (pow3_min_le ℓ h)
      have hK : (V h ℓ t).testBit (P + 3 ^ h * j) = true := by
        rw [testBit_V hinv hP']; simp [hj, hP]
      exact ⟨hPl, by rw [← dig_lo hP' hsh (j := j)]; exact (hd _ hK).2⟩
    have hinv' : TInv h ℓ (mapT (fun c => mv c s v v') t) := by
      refine ⟨shp_mapT _ hinv.1, fun j hj => ?_⟩
      rw [leafAt_mapT hf hinv.1]
      apply Nat.lt_pow_two_of_testBit
      intro p hp
      rw [testBit_mv_set (hdc j hj) hv', Bool.and_eq_false_iff]
      by_cases hps : dig p s = v'
      · right
        cases hb : (leafAt (ℓ - h) t j).testBit (setDig p s v)
        · rfl
        · have h1 := (hdc j hj _ hb).1
          have e : setDig (setDig p s v) s v' = p := by rw [setDig_setDig hv, ← hps, setDig_self]
          have := setDig_lt h1 hsm hv'
          rw [e] at this; omega
      · left; simp [hps]
    refine ⟨hinv', eq_of_testBit_decomp (h := h) fun p j hp => ?_⟩
    rw [testBit_mv_set hd hv', testBit_V hinv' hp, leafAt_mapT hf hinv.1, dig_lo hp hsh,
      setDig_lo hsh, testBit_V hinv (setDig_lt hp hsh hv)]
    by_cases hj : j < 3 ^ (ℓ - h)
    · rw [testBit_mv_set (hdc j hj) hv']; simp [hj]
    · simp [hj]
  · rw [mvB_hi hvv hsh]
    have hdd : ℓ - 1 - s < ℓ - h := by omega
    have he : ℓ - h - 1 - (ℓ - 1 - s) = s - h := by omega
    have hinv' := tinv_atT_mv hinv hs hsh hv hv'
    refine ⟨hinv', eq_of_testBit_decomp (h := h) fun p j hp => ?_⟩
    rw [testBit_mv_set hd hv', testBit_V hinv' hp, dig_hi hp hsh, setDig_hi hp hsh,
      testBit_V hinv hp]
    by_cases hj : j < 3 ^ (ℓ - h)
    · rw [leafAt_atT_mv hv hv' _ hinv.1 hdd j hj, he]
      split
      · rename_i hdj
        simp [hj, hdj, setDig_lt hj (show s - h < ℓ - h by omega) hv]
      · rename_i hdj; simp [hdj]
    · have : ¬ setDig j (s - h) v < 3 ^ (ℓ - h) ∨ dig j (s - h) ≠ v' := by
        by_cases hdj : dig j (s - h) = v'
        · left; intro hlt
          have e : setDig (setDig j (s - h) v) (s - h) v' = j := by
            rw [setDig_setDig hv, ← hdj, setDig_self]
          have := setDig_lt hlt (show s - h < ℓ - h by omega) hv'
          rw [e] at this; exact hj this
        · right; exact hdj
      rcases this with h1 | h1 <;> simp [hj, h1]

private theorem orT_spec {h ℓ : Nat} {a b : B3T} (ha : TInv h ℓ a) (hb : TInv h ℓ b) :
    TInv h ℓ (orT a b) ∧ V h ℓ (orT a b) = V h ℓ a ||| V h ℓ b := by
  have hinv' : TInv h ℓ (orT a b) := ⟨shp_orT ha.1 hb.1, fun j hj => by
    rw [leafAt_orT ha.1 hb.1]; exact Nat.or_lt_two_pow (ha.2 j hj) (hb.2 j hj)⟩
  refine ⟨hinv', eq_of_testBit_decomp (h := h) fun p j hp => ?_⟩
  rw [Nat.testBit_or, testBit_V hinv' hp, testBit_V ha hp, testBit_V hb hp,
    leafAt_orT ha.1 hb.1, Nat.testBit_or]
  cases decide (j < 3 ^ (ℓ - h)) <;> simp

private theorem tinv_z (h ℓ : Nat) : TInv h ℓ .z := ⟨shp_z _, fun j _ => by simp⟩

private theorem V_z (h ℓ : Nat) : V h ℓ .z = 0 := val_z _ _

private theorem orsB_foldl_spec {h ℓ : Nat} (l : List B3T) (hl : ∀ t ∈ l, TInv h ℓ t) :
    ∀ acc, TInv h ℓ acc → TInv h ℓ (l.foldl orT acc) ∧
      V h ℓ (l.foldl orT acc) = (l.map (V h ℓ)).foldl (· ||| ·) (V h ℓ acc) := by
  induction l with
  | nil => intro acc hacc; exact ⟨hacc, rfl⟩
  | cons t l ih =>
    intro acc hacc
    have h1 := orT_spec hacc (hl t (by simp))
    have h2 := ih (fun u hu => hl u (by simp [hu])) _ h1.1
    refine ⟨h2.1, ?_⟩
    rw [List.foldl_cons, h2.2, h1.2]; rfl

/-- **`ors` on trees.** -/
private theorem orsB_spec {h ℓ : Nat} (l : List B3T) (hl : ∀ t ∈ l, TInv h ℓ t) :
    TInv h ℓ (orsB l) ∧ V h ℓ (orsB l) = ors (l.map (V h ℓ)) := by
  have := orsB_foldl_spec l hl .z (tinv_z h ℓ)
  rw [V_z] at this
  exact this

private theorem topB_lo {h ℓ k : Nat} {t : B3T} (hl : ℓ < h) :
    topB h ℓ k t = mapT (fun c => Nat.shiftLeft c (k * 3 ^ ℓ)) t := by
  unfold topB; rw [blt_true hl]

private theorem topB_hi {h ℓ k : Nat} {t : B3T} (hl : h ≤ ℓ) : topB h ℓ k t = put k t := by
  unfold topB; rw [blt_false hl]

/-- A tree of height `0` is `z` or a chunk. -/
private theorem shp_zero {t : B3T} (hs : Shp 0 t) : t = .z ∨ ∃ c, t = .leaf c := by
  match t, hs with
  | .z, _ => exact Or.inl rfl
  | .leaf c, _ => exact Or.inr ⟨c, rfl⟩

private theorem val_put {h k v : Nat} (hv : v ≤ 2) (x : B3T) :
    val h (k + 1) (put v x) = val h k x <<< (v * 3 ^ (h + k)) := by
  rcases (show v = 0 ∨ v = 1 ∨ v = 2 by omega) with rfl | rfl | rfl <;>
    simp [put_zero, put_one, put_two, val_node]

/-- **A new top digit.** -/
private theorem topB_spec {h ℓ k : Nat} {t : B3T} (hinv : TInv h ℓ t) (hk : k ≤ 2) :
    TInv h (ℓ + 1) (topB h ℓ k t) ∧ V h (ℓ + 1) (topB h ℓ k t) = V h ℓ t <<< (k * 3 ^ ℓ) := by
  rcases Nat.lt_or_ge ℓ h with hl | hl
  · rw [topB_lo hl]
    have h0 : ℓ - h = 0 := by omega
    have h1 : ℓ + 1 - h = 0 := by omega
    have hs := hinv.1; rw [h0] at hs
    rcases shp_zero hs with rfl | ⟨c, rfl⟩
    · exact ⟨tinv_z _ _, by simp [V]⟩
    · have hc : c < 2 ^ 3 ^ ℓ := by
        have := hinv.2 0 (by simp); rw [h0, Nat.min_eq_left (Nat.le_of_lt hl)] at this
        simpa using this
      refine ⟨⟨by rw [h1]; trivial, fun j _ => ?_⟩, ?_⟩
      · rw [h1, Nat.min_eq_left (show ℓ + 1 ≤ h by omega)]
        show Nat.shiftLeft c (k * 3 ^ ℓ) < 2 ^ 3 ^ (ℓ + 1)
        rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
        calc c * 2 ^ (k * 3 ^ ℓ) < 2 ^ 3 ^ ℓ * 2 ^ (k * 3 ^ ℓ) :=
              Nat.mul_lt_mul_of_pos_right hc (Nat.two_pow_pos _)
          _ = 2 ^ (3 ^ ℓ + k * 3 ^ ℓ) := (Nat.pow_add _ _ _).symm
          _ ≤ 2 ^ 3 ^ (ℓ + 1) := Nat.pow_le_pow_right (by norm_num) (by
              rw [Nat.pow_succ]; have := Nat.mul_le_mul_right (3 ^ ℓ) hk; omega)
      · simp only [V, h0, h1, mapT_leaf, val_leaf, Nat.shiftLeft_eq']
  · rw [topB_hi hl]
    have h1 : ℓ + 1 - h = (ℓ - h) + 1 := by omega
    have hmin : min ℓ h = h := Nat.min_eq_right hl
    have hmin' : min (ℓ + 1) h = h := Nat.min_eq_right (by omega)
    refine ⟨⟨by rw [h1]; exact shp_put hinv.1, fun j hj => ?_⟩, ?_⟩
    · rw [h1] at hj ⊢
      rw [leafAt_put hk _ hj, hmin']
      split
      · have := hinv.2 _ (Nat.mod_lt j (pow3_pos (ℓ - h))); rwa [hmin] at this
      · exact Nat.two_pow_pos _
    · rw [V, V, h1, val_put hk, show h + (ℓ - h) = ℓ by omega]

private theorem truncB_lo {h ℓ : Nat} {t : B3T} (hl : ℓ ≤ h) :
    truncB h ℓ t = mapT (fun c => Nat.land c (ones (3 ^ (ℓ - 1)))) t := by
  unfold truncB; rw [ble_true hl]

private theorem truncB_hi {h ℓ : Nat} {t : B3T} (hl : h < ℓ) : truncB h ℓ t = child0 t := by
  unfold truncB; rw [ble_false hl]

private theorem ones_lt (n : Nat) : ones n < 2 ^ n := by
  rw [ones_eq]; exact Nat.sub_lt (Nat.two_pow_pos n) (by norm_num)

/-- `p + 3^h * j` is below `3^h * 3^k` iff `j` is below `3^k`. -/
private theorem idx_lt_iff {h k p j : Nat} (hp : p < 3 ^ h)
    : p + 3 ^ h * j < 3 ^ h * 3 ^ k ↔ j < 3 ^ k := by
  constructor
  · intro hlt
    by_contra hc
    have : 3 ^ h * 3 ^ k ≤ 3 ^ h * j := Nat.mul_le_mul_left _ (Nat.le_of_not_lt hc)
    omega
  · intro hj
    have : 3 ^ h * (j + 1) ≤ 3 ^ h * 3 ^ k := Nat.mul_le_mul_left _ hj
    rw [Nat.mul_add, Nat.mul_one] at this; omega

/-- **Dropping the top digit.** -/
private theorem truncB_spec {h ℓ : Nat} {t : B3T} (hinv : TInv h ℓ t) :
    TInv h (ℓ - 1) (truncB h ℓ t) ∧
      V h (ℓ - 1) (truncB h ℓ t) = V h ℓ t &&& ones (3 ^ (ℓ - 1)) := by
  rcases (Nat.lt_or_ge h ℓ).symm with hl | hl
  · rw [truncB_lo hl]
    have h0 : ℓ - h = 0 := by omega
    have h1 : ℓ - 1 - h = 0 := by omega
    have hs := hinv.1; rw [h0] at hs
    rcases shp_zero hs with rfl | ⟨c, rfl⟩
    · exact ⟨tinv_z _ _, by simp [V]⟩
    · refine ⟨⟨by rw [h1]; trivial, fun j _ => ?_⟩, ?_⟩
      · rw [h1, Nat.min_eq_left (show ℓ - 1 ≤ h by omega)]
        show Nat.land c (ones (3 ^ (ℓ - 1))) < 2 ^ 3 ^ (ℓ - 1)
        exact Nat.and_lt_two_pow _ (ones_lt _)
      · simp only [V, h0, h1, mapT_leaf, val_leaf, Nat.land_eq]
  · rw [truncB_hi hl]
    obtain ⟨k', hk'⟩ : ∃ k', ℓ - h = k' + 1 := ⟨ℓ - h - 1, by omega⟩
    have h1 : ℓ - 1 - h = k' := by omega
    have hs : Shp (k' + 1) t := hk' ▸ hinv.1
    have hmin : min ℓ h = h := Nat.min_eq_right (by omega)
    have hmin' : min (ℓ - 1) h = h := Nat.min_eq_right (by omega)
    have hinv' : TInv h (ℓ - 1) (child0 t) := by
      refine ⟨by rw [h1]; exact shp_child0 hs, fun j hj => ?_⟩
      rw [h1] at hj ⊢
      rw [leafAt_child0 hs hj, hmin']
      have := hinv.2 j (by rw [hk', Nat.pow_succ]; omega)
      rwa [hk', hmin] at this
    refine ⟨hinv', eq_of_testBit_decomp (h := h) fun p j hp => ?_⟩
    rw [testBit_V hinv' hp, Nat.testBit_and, testBit_V hinv hp, testBit_ones, h1, hk',
      show ℓ - 1 = h + k' by omega, show 3 ^ (h + k') = 3 ^ h * 3 ^ k' from Nat.pow_add _ _ _,
      show decide (p + 3 ^ h * j < 3 ^ h * 3 ^ k') = decide (j < 3 ^ k') from
        decide_eq_decide.2 (idx_lt_iff hp)]
    by_cases hj : j < 3 ^ k'
    · rw [leafAt_child0 hs hj]
      simp [hj, show j < 3 ^ (k' + 1) by rw [Nat.pow_succ]; omega]
    · simp [hj]

private theorem fold3_zero (r : Nat) : fold3 r 0 = 0 := by simp [fold3]

private theorem fold3_lt' (r x : Nat) : fold3 r x < 2 ^ 3 ^ (r - 1) := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  cases hb : (fold3 r x).testBit i
  · rfl
  · exact absurd ((testBit_fold3 r x i).1 hb).1 (by omega)

private theorem fold3B_lo {h r : Nat} {t : B3T} (hr : r ≤ h) : fold3B h r t = mapT (fold3 r) t := by
  unfold fold3B; rw [ble_true hr]

private theorem fold3B_hi {h r : Nat} {t : B3T} (hr : h < r) : fold3B h r t = fold3Root t := by
  unfold fold3B; rw [ble_false hr]

/-- **Folding the top digit.** -/
private theorem fold3B_spec {h r : Nat} {t : B3T} (hinv : TInv h r t) :
    TInv h (r - 1) (fold3B h r t) ∧ V h (r - 1) (fold3B h r t) = fold3 r (V h r t) := by
  rcases (Nat.lt_or_ge h r).symm with hl | hl
  · rw [fold3B_lo hl]
    have h0 : r - h = 0 := by omega
    have h1 : r - 1 - h = 0 := by omega
    have hs := hinv.1; rw [h0] at hs
    rcases shp_zero hs with rfl | ⟨c, rfl⟩
    · exact ⟨tinv_z _ _, by simp [V, fold3_zero]⟩
    · refine ⟨⟨by rw [h1]; trivial, fun j _ => ?_⟩, ?_⟩
      · rw [h1, Nat.min_eq_left (show r - 1 ≤ h by omega)]
        exact fold3_lt' r c
      · simp only [V, h0, h1, mapT_leaf, val_leaf]
  · rw [fold3B_hi hl]
    obtain ⟨k', hk'⟩ : ∃ k', r - h = k' + 1 := ⟨r - h - 1, by omega⟩
    have h1 : r - 1 - h = k' := by omega
    have hs : Shp (k' + 1) t := hk' ▸ hinv.1
    have hmin : min r h = h := Nat.min_eq_right (by omega)
    have hmin' : min (r - 1) h = h := Nat.min_eq_right (by omega)
    have hk3 : 3 ^ (k' + 1) = 3 * 3 ^ k' := by rw [Nat.pow_succ]; ring
    have hjf : ∀ j < 3 ^ (k' + 1), leafAt (k' + 1) t j < 2 ^ 3 ^ h := by
      intro j hj; have := hinv.2 j (by rwa [hk']); rwa [hk', hmin] at this
    have hinv' : TInv h (r - 1) (fold3Root t) := by
      refine ⟨by rw [h1]; exact shp_fold3Root hs, fun j hj => ?_⟩
      rw [h1] at hj ⊢
      rw [leafAt_fold3Root hs hj, hmin']
      exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (hjf _ (by omega)) (hjf _ (by omega)))
        (hjf _ (by omega))
    refine ⟨hinv', eq_of_testBit_decomp (h := h) fun p j hp => ?_⟩
    have hW : 3 ^ (r - 1) = 3 ^ h * 3 ^ k' := by rw [show r - 1 = h + k' by omega, Nat.pow_add]
    rw [testBit_V hinv' hp, h1, Bool.eq_iff_iff, testBit_fold3, hW, idx_lt_iff hp]
    have e1 : ∀ d, p + 3 ^ h * j + d * (3 ^ h * 3 ^ k') = p + 3 ^ h * (d * 3 ^ k' + j) := by
      intro d; ring
    rw [e1, e1, show p + 3 ^ h * j = p + 3 ^ h * (0 * 3 ^ k' + j) by simp,
      testBit_V hinv hp, testBit_V hinv hp, testBit_V hinv hp, hk']
    simp only [Nat.zero_mul, Nat.zero_add, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨hj, hb⟩
      rw [leafAt_fold3Root hs hj, Nat.testBit_or, Nat.testBit_or] at hb
      refine ⟨hj, ?_⟩
      simp only [Bool.or_eq_true] at hb
      rcases hb with (hb | hb) | hb
      · exact Or.inl ⟨by omega, hb⟩
      · exact Or.inr (Or.inl ⟨by omega, hb⟩)
      · exact Or.inr (Or.inr ⟨by omega, hb⟩)
    · rintro ⟨hj, hb⟩
      refine ⟨hj, ?_⟩
      rw [leafAt_fold3Root hs hj, Nat.testBit_or, Nat.testBit_or]
      simp only [Bool.or_eq_true]
      rcases hb with hb | hb | hb
      · exact Or.inl (Or.inl hb.2)
      · exact Or.inl (Or.inr hb.2)
      · exact Or.inr hb.2

private theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h
    : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  rw [List.flatMap_def, List.flatMap_def, List.map_congr_left h]

/-- A list of trees over the digit pairs, each computing the corresponding term: the `ors`
of their values. -/
private theorem orsB_pairs {h ℓ : Nat} {T : Nat → Nat → B3T} {U : Nat → Nat → Nat}
    (hT : ∀ u ∈ digits3, ∀ v ∈ digits3, TInv h ℓ (T u v) ∧ V h ℓ (T u v) = U u v) :
    TInv h ℓ (orsB (digits3.flatMap fun u => digits3.map fun v => T u v)) ∧
      V h ℓ (orsB (digits3.flatMap fun u => digits3.map fun v => T u v)) =
        ors (digits3.flatMap fun u => digits3.map fun v => U u v) := by
  have hl : ∀ x ∈ (digits3.flatMap fun u => digits3.map fun v => T u v), TInv h ℓ x := by
    intro x hx
    simp only [List.mem_flatMap, List.mem_map] at hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hx
    exact (hT u hu v hv).1
  obtain ⟨h1, h2⟩ := orsB_spec _ hl
  refine ⟨h1, ?_⟩
  rw [h2, List.map_flatMap]
  congr 1
  apply flatMap_congr'
  intro u hu
  rw [List.map_map]
  apply List.map_congr_left
  intro v hv
  exact (hT u hu v hv).2

/-- A list of trees over the digits, each computing the corresponding term. -/
private theorem orsB_single {h ℓ : Nat} {T : Nat → B3T} {U : Nat → Nat}
    (hT : ∀ v ∈ digits3, TInv h ℓ (T v) ∧ V h ℓ (T v) = U v) :
    TInv h ℓ (orsB (digits3.map T)) ∧ V h ℓ (orsB (digits3.map T)) = ors (digits3.map U) := by
  have hl : ∀ x ∈ digits3.map T, TInv h ℓ x := by
    intro x hx
    simp only [List.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    exact (hT v hv).1
  obtain ⟨h1, h2⟩ := orsB_spec _ hl
  refine ⟨h1, ?_⟩
  rw [h2, List.map_map]
  congr 1
  apply List.map_congr_left
  intro v hv
  exact (hT v hv).2

/-- **`transp` on trees.** -/
private theorem transpB_spec {h ℓ a b : Nat} {t : B3T} (hinv : TInv h ℓ t) (ha : a < ℓ) (hb
    : b < ℓ) :
    TInv h ℓ (transpB h ℓ t a b) ∧ V h ℓ (transpB h ℓ t a b) = transp ℓ (V h ℓ t) a b := by
  unfold transpB transp
  by_cases hab : (a == b) = true
  · simp only [hab, ite_true, and_true]; exact hinv
  · simp only [hab, Bool.false_eq_true, ite_false]
    have hne : b ≠ a := fun e => hab (by simp [e])
    apply orsB_pairs
    intro u hu v hv
    rw [mem_digits3] at hu hv
    obtain ⟨i1, e1⟩ := selB_spec hinv ha hu
    obtain ⟨i2, e2⟩ := selB_spec i1 hb hv
    rw [e1] at e2
    have d2 : DigN ℓ a u (V h ℓ (selB h ℓ (selB h ℓ t a u) b v)) := by
      rw [e2]; exact digN_sel_of (digN_sel ha hu) hb hv
    obtain ⟨i3, e3⟩ := mvB_spec i2 ha hu hv d2
    rw [e2] at e3
    have d3 : DigN ℓ b v (V h ℓ (mvB h ℓ (selB h ℓ (selB h ℓ t a u) b v) a u v)) := by
      rw [e3]; exact digN_mv_other (digN_sel_of (digN_sel ha hu) hb hv) (digN_sel hb hv) ha hv hne
    obtain ⟨i4, e4⟩ := mvB_spec i3 hb hv hu d3
    rw [e3] at e4
    exact ⟨i4, e4⟩

/-- **`killSlot` on trees.** -/
private theorem killSlotB_spec {h ℓ s : Nat} {ord : List Nat} {t : B3T} (hinv : TInv h ℓ t) (hs
    : s < ℓ) :
    (killSlotB h ⟨ℓ, ord, t⟩ s).len = (killSlot ⟨ℓ, ord, V h ℓ t⟩ s).len ∧
    (killSlotB h ⟨ℓ, ord, t⟩ s).ord = (killSlot ⟨ℓ, ord, V h ℓ t⟩ s).ord ∧
    TInv h (ℓ - 1) (killSlotB h ⟨ℓ, ord, t⟩ s).t ∧
    V h (ℓ - 1) (killSlotB h ⟨ℓ, ord, t⟩ s).t = (killSlot ⟨ℓ, ord, V h ℓ t⟩ s).x := by
  refine ⟨rfl, rfl, ?_⟩
  have h0 := orsB_single (h := h) (ℓ := ℓ) (T := fun v => mvB h ℓ (selB h ℓ t s v) s v 0)
    (U := fun v => mv (sel ℓ (V h ℓ t) s v) s v 0) (by
      intro v hv
      rw [mem_digits3] at hv
      obtain ⟨i1, e1⟩ := selB_spec hinv hs hv
      have d1 : DigN ℓ s v (V h ℓ (selB h ℓ t s v)) := by rw [e1]; exact digN_sel hs hv
      obtain ⟨i2, e2⟩ := mvB_spec (v' := 0) i1 hs hv (by omega) d1
      rw [e1] at e2
      exact ⟨i2, e2⟩)
  obtain ⟨i3, e3⟩ := transpB_spec h0.1 hs (show ℓ - 1 < ℓ by omega)
  rw [h0.2] at e3
  obtain ⟨i4, e4⟩ := truncB_spec i3
  rw [e3] at e4
  exact ⟨i4, e4⟩

/-- The tree state `stT` represents the DP state `st`. -/
private def Rel (h : Nat) (stT : DPStateB) (st : DPState) : Prop :=
  stT.len = st.len ∧ stT.ord = st.ord ∧ TInv h st.len stT.t ∧ V h st.len stT.t = st.x

private theorem p231_le' (v : Nat) : p231 v ≤ 2 := by unfold p231; split <;> omega
private theorem p312_le' (v : Nat) : p312 v ≤ 2 := by unfold p312; split <;> omega
private theorem addd_le' {v1 v2 : Nat} (h1 : v1 ≤ 2) (h2 : v2 ≤ 2) : addd v1 v2 ≤ 2 := by
  unfold addd
  rcases (show v1 = 0 ∨ v1 = 1 ∨ v1 = 2 by omega) with rfl | rfl | rfl <;>
  rcases (show v2 = 0 ∨ v2 = 1 ∨ v2 = 2 by omega) with rfl | rfl | rfl <;> decide

/-- **The DP step on trees.** -/
private theorem dpStepB_spec {h : Nat} {stT : DPStateB} {st : DPState} (hst : st.WF) (hr
    : Rel h stT st)
    (s : Cpstep) : Rel h (dpStepB h stT s) (dpStep st s) := by
  obtain ⟨ℓ, ord, x⟩ := st
  obtain ⟨ℓ', ord', t⟩ := stT
  obtain ⟨hl, ho, hinv, hx⟩ := hr
  simp only at hl ho hinv hx
  subst hl ho hx
  obtain ⟨hperm, -, hl1⟩ := hst
  simp only at hperm hl1
  have hmem : ∀ s ∈ ord', s < ℓ' := fun s hs => List.mem_range.1 (hperm.mem_iff.1 hs)
  have hnd : ord'.Nodup := hperm.nodup_iff.2 List.nodup_range
  have hlen : ord'.length = ℓ' := by rw [hperm.length_eq, List.length_range]
  unfold Rel
  cases s with
  | R n => exact ⟨rfl, rfl, hinv, rfl⟩
  | R' =>
    dsimp only [dpStep, dpStepB]
    split
    · exact ⟨rfl, rfl, tinv_z _ _, V_z _ _⟩
    · exact ⟨rfl, rfl, hinv, rfl⟩
  | Y =>
    rcases ord' with _ | ⟨s0, rest⟩
    · simp at hlen; omega
    · dsimp only [dpStep, dpStepB]
      have hs0 : s0 < ℓ' := hmem s0 (by simp)
      refine ⟨rfl, rfl, orsB_single fun v hv => ?_⟩
      rw [mem_digits3] at hv
      obtain ⟨i1, e1⟩ := selB_spec hinv hs0 hv
      have d1 : DigN ℓ' s0 v (V h ℓ' (selB h ℓ' t s0 v)) := by rw [e1]; exact digN_sel hs0 hv
      obtain ⟨i2, e2⟩ := mvB_spec (v' := p231 v) i1 hs0 hv (p231_le' v) d1
      obtain ⟨i3, e3⟩ := mvB_spec (v' := p312 v) i1 hs0 hv (p312_le' v) d1
      obtain ⟨i4, e4⟩ := topB_spec (k := p312 v) i2 (p312_le' v)
      obtain ⟨i5, e5⟩ := topB_spec (k := p231 v) i3 (p231_le' v)
      obtain ⟨i6, e6⟩ := orT_spec i4 i5
      refine ⟨i6, ?_⟩
      rw [e6, e4, e5, e2, e3, e1]
  | H =>
    rcases ord' with _ | ⟨s0, _ | ⟨s1, rest⟩⟩
    · simp at hlen; omega
    · dsimp only [dpStep, dpStepB]; exact ⟨rfl, rfl, tinv_z _ _, V_z _ _⟩
    · dsimp only [dpStep, dpStepB]
      have hs0 : s0 < ℓ' := hmem s0 (by simp)
      have hs1 : s1 < ℓ' := hmem s1 (by simp)
      have hne : s1 ≠ s0 := fun e => by
        rw [List.nodup_cons] at hnd; exact hnd.1 (by simp [e])
      refine ⟨rfl, rfl, orsB_pairs fun v1 hv1 v2 hv2 => ?_⟩
      rw [mem_digits3] at hv1 hv2
      obtain ⟨i1, e1⟩ := selB_spec hinv hs0 hv1
      obtain ⟨i2, e2⟩ := selB_spec i1 hs1 hv2
      rw [e1] at e2
      have dy0 : DigN ℓ' s0 v1 (sel ℓ' (sel ℓ' (V h ℓ' t) s0 v1) s1 v2) :=
        digN_sel_of (digN_sel hs0 hv1) hs1 hv2
      have dy1 : DigN ℓ' s1 v2 (sel ℓ' (sel ℓ' (V h ℓ' t) s0 v1) s1 v2) := digN_sel hs1 hv2
      have mv2 : ∀ w w', w ≤ 2 → w' ≤ 2 →
          TInv h ℓ' (mvB h ℓ' (mvB h ℓ' (selB h ℓ' (selB h ℓ' t s0 v1) s1 v2) s0 v1 w) s1 v2 w') ∧
          V h ℓ' (mvB h ℓ' (mvB h ℓ' (selB h ℓ' (selB h ℓ' t s0 v1) s1 v2) s0 v1 w) s1 v2 w') =
            mv (mv (sel ℓ' (sel ℓ' (V h ℓ' t) s0 v1) s1 v2) s0 v1 w) s1 v2 w' := by
        intro w w' hw hw'
        obtain ⟨i3, e3⟩ := mvB_spec (v' := w) i2 hs0 hv1 hw (by rw [e2]; exact dy0)
        rw [e2] at e3
        obtain ⟨i4, e4⟩ := mvB_spec (v' := w') i3 hs1 hv2 hw'
          (by rw [e3]; exact digN_mv_other dy0 dy1 hs0 hw hne)
        rw [e3] at e4
        exact ⟨i4, e4⟩
      by_cases hvv : (v1 == v2) = true
      · simp only [hvv, ite_true]
        obtain ⟨j1, f1⟩ := mv2 (p231 v1) (p231 v1) (p231_le' v1) (p231_le' v1)
        obtain ⟨j2, f2⟩ := mv2 (p312 v1) (p312 v1) (p312_le' v1) (p312_le' v1)
        obtain ⟨j3, f3⟩ := orT_spec j1 j2
        exact ⟨j3, by rw [f3, f1, f2]⟩
      · simp only [hvv, Bool.false_eq_true, ite_false]
        exact mv2 v2 v1 hv2 hv1
  | U =>
    dsimp only [dpStep, dpStepB]
    refine ⟨rfl, rfl, orsB_single fun v hv => ?_⟩
    rw [mem_digits3] at hv
    obtain ⟨i1, e1⟩ := topB_spec (k := v) hinv hv
    obtain ⟨i2, e2⟩ := topB_spec (k := v) i1 hv
    refine ⟨i2, ?_⟩
    rw [e2, e1, ← Nat.shiftLeft_add]
  | K =>
    rcases ord' with _ | ⟨s0, _ | ⟨s1, rest⟩⟩
    · simp at hlen; omega
    · dsimp only [dpStep, dpStepB]; exact ⟨rfl, rfl, tinv_z _ _, V_z _ _⟩
    · dsimp only [dpStep, dpStepB]
      have hs0 : s0 < ℓ' := hmem s0 (by simp)
      have hs1 : s1 < ℓ' := hmem s1 (by simp)
      have hx' := orsB_pairs (h := h) (ℓ := ℓ')
        (T := fun v1 v2 => if v1 == v2 then .z else
          mvB h ℓ' (selB h ℓ' (selB h ℓ' t s0 v1) s1 v2) s0 v1 (addd v1 v2))
        (U := fun v1 v2 => if v1 == v2 then 0 else
          mv (sel ℓ' (sel ℓ' (V h ℓ' t) s0 v1) s1 v2) s0 v1 (addd v1 v2)) (by
          intro v1 hv1 v2 hv2
          rw [mem_digits3] at hv1 hv2
          by_cases hvv : (v1 == v2) = true
          · simp only [hvv, ite_true]; exact ⟨tinv_z _ _, V_z _ _⟩
          · simp only [hvv, Bool.false_eq_true, ite_false]
            obtain ⟨i1, e1⟩ := selB_spec hinv hs0 hv1
            obtain ⟨i2, e2⟩ := selB_spec i1 hs1 hv2
            rw [e1] at e2
            obtain ⟨i3, e3⟩ := mvB_spec (v' := addd v1 v2) i2 hs0 hv1 (addd_le' hv1 hv2)
              (by rw [e2]; exact digN_sel_of (digN_sel hs0 hv1) hs1 hv2)
            rw [e2] at e3
            exact ⟨i3, e3⟩)
      have hk := killSlotB_spec (ord := s0 :: rest) hx'.1 hs1
      rw [hx'.2] at hk
      exact hk
  | A =>
    rcases ord' with _ | ⟨s0, _ | ⟨s1, rest⟩⟩
    · simp at hlen; omega
    · dsimp only [dpStep, dpStepB]; exact ⟨rfl, rfl, tinv_z _ _, V_z _ _⟩
    · dsimp only [dpStep, dpStepB]
      have hs0 : s0 < ℓ' := hmem s0 (by simp)
      have hs1 : s1 < ℓ' := hmem s1 (by simp)
      have hne : s1 ≠ s0 := fun e => by
        rw [List.nodup_cons] at hnd; exact hnd.1 (by simp [e])
      have hx' := orsB_single (h := h) (ℓ := ℓ')
        (T := fun v => selB h ℓ' (selB h ℓ' t s0 v) s1 v)
        (U := fun v => sel ℓ' (sel ℓ' (V h ℓ' t) s0 v) s1 v) (by
          intro v hv
          rw [mem_digits3] at hv
          obtain ⟨i1, e1⟩ := selB_spec hinv hs0 hv
          obtain ⟨i2, e2⟩ := selB_spec i1 hs1 hv
          rw [e1] at e2
          exact ⟨i2, e2⟩)
      rcases rest with _ | ⟨r0, rs⟩
      · exact ⟨rfl, rfl, hx'.1, hx'.2⟩
      · dsimp only
        have hk := killSlotB_spec (ord := (r0 :: rs) ++ [s0]) hx'.1 hs1
        rw [hx'.2] at hk
        obtain ⟨hk1, hk2, hk3, hk4⟩ := hk
        rw [hk2]
        cases hg : (killSlot ⟨ℓ', (r0 :: rs) ++ [s0], ors (digits3.map fun v =>
            sel ℓ' (sel ℓ' (V h ℓ' t) s0 v) s1 v)⟩ s1).ord.getLast? with
        | none => exact ⟨hk1, hk2, hk3, hk4⟩
        | some s0' =>
          dsimp only
          have hs0' : s0' < ℓ' - 1 := by
            simp only [killSlot, List.map_append, List.map_cons, List.map_nil,
              List.getLast?_append, List.getLast?_singleton, Option.some_or] at hg
            injection hg with hg
            rw [← hg]
            split
            · rename_i he
              have : s0 = ℓ' - 1 := by simpa using he
              omega
            · rename_i he
              have : s0 ≠ ℓ' - 1 := by simpa using he
              omega
          have hk' := killSlotB_spec (h := h) (ord := (killSlotB h ⟨ℓ', (r0 :: rs) ++ [s0],
            orsB (digits3.map fun v => selB h ℓ' (selB h ℓ' t s0 v) s1 v)⟩ s1).ord.dropLast)
            hk3 hs0'
          rw [hk4, hk2] at hk'
          exact hk'

/-! ### The DP, the sort and the conversion -/

private theorem dpBaseB_spec {h : Nat} (hh : 2 ≤ h) : Rel h dpBaseB dpBase := by
  refine ⟨rfl, rfl, ⟨?_, fun j _ => ?_⟩, ?_⟩
  · show Shp (2 - h) _; rw [show 2 - h = 0 by omega]; trivial
  · show leafAt (2 - h) _ j < 2 ^ 3 ^ min 2 h
    rw [show 2 - h = 0 by omega, Nat.min_eq_left hh]
    show 2 ^ 0 ||| 2 ^ 4 ||| 2 ^ 8 < 2 ^ 3 ^ 2
    decide
  · show val h (2 - h) _ = _
    rw [show 2 - h = 0 by omega]; rfl

/-- **The DP on trees computes the DP.** -/
private theorem dpRunB_spec {h : Nat} (hh : 2 ≤ h) : ∀ cp : Cprog, Rel h (dpRunB h cp) (dpRun cp)
  | [] => dpBaseB_spec hh
  | s :: cp => by
    show Rel h (dpStepB h (dpRunB h cp) s) (dpStep (dpRun cp) s)
    exact dpStepB_spec (dpRun_WF cp) (dpRunB_spec hh cp) s

/-- **`sortDigits` on trees.** -/
private theorem sortDigitsB_spec {h ℓ : Nat} : ∀ (fuel i : Nat) (ord : List Nat) (t
    : B3T), TInv h ℓ t →
    (∀ s ∈ ord, s < ℓ) → i + ord.length ≤ ℓ →
    TInv h ℓ (sortDigitsB h ℓ fuel i ord t) ∧
      V h ℓ (sortDigitsB h ℓ fuel i ord t) = sortDigits ℓ fuel i ord (V h ℓ t) := by
  intro fuel
  induction fuel with
  | zero => intro i ord t hinv _ _; exact ⟨hinv, rfl⟩
  | succ fuel ih =>
    intro i ord t hinv hord hlen
    match ord, hord, hlen with
    | [], _, _ => exact ⟨hinv, rfl⟩
    | s :: rest, hord, hlen =>
      simp only [List.length_cons] at hlen
      have hs : s < ℓ := hord s (by simp)
      obtain ⟨i1, e1⟩ := transpB_spec (a := s) (b := i) hinv hs (by omega)
      have ih' := ih (i + 1) (rest.map fun t => if t == i then s else t) _ i1 (by
        intro u hu
        simp only [List.mem_map] at hu
        obtain ⟨u', hu', rfl⟩ := hu
        split
        · exact hs
        · exact hord u' (by simp [hu'])) (by simp; omega)
      rw [e1] at ih'
      exact ih'

/-- **`dpB3` on trees.** -/
private theorem dpB3B_spec {h : Nat} (hh : 2 ≤ h) (cp : Cprog) :
    TInv h (dpRun cp).len (dpB3B h cp) ∧ V h (dpRun cp).len (dpB3B h cp) = dpB3 cp := by
  obtain ⟨hl, ho, hinv, hx⟩ := dpRunB_spec hh cp
  obtain ⟨hperm, -, -⟩ := dpRun_WF cp
  have hmem : ∀ s ∈ (dpRun cp).ord, s < (dpRun cp).len :=
    fun s hs => List.mem_range.1 (hperm.mem_iff.1 hs)
  have hlen : (dpRun cp).ord.length = (dpRun cp).len := by rw [hperm.length_eq, List.length_range]
  unfold dpB3B dpB3
  dsimp only
  rw [hl, ho]
  have := sortDigitsB_spec (h := h) (dpRun cp).len 0 (dpRun cp).ord (dpRunB h cp).t hinv hmem
    (by omega)
  rw [hx] at this
  exact this

private theorem convB_zero_z (s h off : Nat) (acc : List Nat) : convB s h 0 .z off acc = acc := rfl
private theorem convB_zero_leaf (s h c off : Nat) (acc : List Nat) :
    convB s h 0 (.leaf c) off acc = orAt (off / 2 ^ s) acc
      (toChunksAux s ((off % 2 ^ s + 3 ^ h) / 2 ^ s + 1) ((off % 2 ^ s + 3 ^ h) / 2 ^ s + 1)
        ((c &&& ones (3 ^ h)) <<< (off % 2 ^ s)) []) := rfl
private theorem convB_succ_z (s h k off : Nat) (acc : List Nat) : convB s h
    (k + 1) .z off acc = acc := rfl
private theorem convB_succ_node (s h k : Nat) (a b c : B3T) (off : Nat) (acc : List Nat) :
    convB s h (k + 1) (.node a b c) off acc =
      convB s h k c (off + 2 * 3 ^ (h + k))
        (convB s h k b (off + 3 ^ (h + k)) (convB s h k a off acc)) :=
  rfl

private theorem shiftLeft_or_distrib'' (a b w : Nat) : (a ||| b) <<< w = (a <<< w) ||| (b <<< w)
    := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  cases decide (i ≥ w) <;> simp

/-- **The conversion to chunks of `2 ^ s` bits.** -/
private theorem ofChunks_convB (s h : Nat) : ∀ (k : Nat) (t : B3T), Shp k t → JF (3 ^ h) k t →
    ∀ (off : Nat) (acc : List Nat),
      ofChunks s (convB s h k t off acc) = ofChunks s acc ||| (val h k t <<< off)
  | 0, .z, _, _, off, acc => by simp [convB_zero_z]
  | 0, .leaf c, _, hj, off, acc => by
    have hc : c < 2 ^ 3 ^ h := by simpa using hj 0 (by simp)
    have hW : 0 < 2 ^ s := Nat.two_pow_pos s
    rw [convB_zero_leaf, ofChunks_orAt]
    have hn : off % 2 ^ s + 3 ^ h < ((off % 2 ^ s + 3 ^ h) / 2 ^ s + 1) * 2 ^ s := by
      rw [Nat.add_mul, Nat.one_mul]; exact Nat.lt_div_mul_add hW
    rw [ofChunks_toChunksAux s ((off % 2 ^ s + 3 ^ h) / 2 ^ s + 1)
      ((off % 2 ^ s + 3 ^ h) / 2 ^ s + 1) _ [] (Nat.le_add_left 1 _) (Nat.le_succ _),
      ofChunks_nil, Nat.zero_shiftLeft, Nat.or_zero]
    generalize (off % 2 ^ s + 3 ^ h) / 2 ^ s + 1 = n at hn ⊢
    have hand : c &&& ones (3 ^ h) = c := by
      rw [ones_eq]; exact Nat.and_two_pow_sub_one_of_lt_two_pow hc
    rw [hand]
    have hy : c <<< (off % 2 ^ s) < 2 ^ (n * 2 ^ s) := by
      rw [Nat.shiftLeft_eq]
      calc c * 2 ^ (off % 2 ^ s) < 2 ^ 3 ^ h * 2 ^ (off % 2 ^ s) :=
            Nat.mul_lt_mul_of_pos_right hc (Nat.two_pow_pos _)
        _ = 2 ^ (3 ^ h + off % 2 ^ s) := by rw [Nat.pow_add]
        _ ≤ 2 ^ (n * 2 ^ s) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [ones_eq, Nat.and_two_pow_sub_one_of_lt_two_pow hy, ← Nat.shiftLeft_add,
      show off % 2 ^ s + off / 2 ^ s * 2 ^ s = off by
        rw [Nat.mul_comm]; exact Nat.mod_add_div off (2 ^ s)]
    rfl
  | k + 1, .z, _, _, off, acc => by simp [convB_succ_z]
  | k + 1, .node a b c, hs, hj, off, acc => by
    obtain ⟨ha, hb, hc⟩ := hs
    obtain ⟨ja, jb, jc⟩ := jf_node hj
    rw [convB_succ_node, ofChunks_convB s h k c hc jc, ofChunks_convB s h k b hb jb,
      ofChunks_convB s h k a ha ja, val_node, shiftLeft_or_distrib'', shiftLeft_or_distrib'',
      ← Nat.shiftLeft_add, ← Nat.shiftLeft_add, Nat.one_mul,
      Nat.add_comm (3 ^ (h + k)) off, Nat.add_comm (2 * 3 ^ (h + k)) off]
    simp only [Nat.or_assoc]
  | 0, .node _ _ _, hs, _, _, _ => absurd hs (by simp)
  | _ + 1, .leaf _, hs, _, _, _ => absurd hs (by simp)

/-! ### The main equalities -/

/-- **The DP on base-3 chunks computes `dpP1`** (with the conversion network assembled from its
chunks). -/
theorem dpP1B_eq_dpP1 {r s h : Nat} {cnv : NetC} (hcnv : netCOK s cnv = true) (cp : Cprog) :
    dpP1B r s h cnv cp = dpP1 r (netOfChunks s cnv) cp := by
  unfold dpP1B
  cases hg : (Nat.ble 2 h && Nat.beq (dpRunB h cp).len r)
  · rw [Bool.cond_false, dpP1_eq_dpP1C hcnv]
  · rw [Bool.cond_true]
    rw [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] at hg
    obtain ⟨hh, hlr⟩ := hg
    rw [(dpRunB_spec hh cp).1] at hlr
    obtain ⟨i1, e1⟩ := dpB3B_spec hh cp
    rw [hlr] at i1 e1
    obtain ⟨i2, e2⟩ := fold3B_spec i1
    rw [e1] at e2
    rw [splitGC_eq, ofChunks_applyNetC hcnv, ofChunks_convB s h _ _ i2.1
      (jf_mono (pow3_min_le _ h) i2.2), ofChunks_nil, Nat.zero_or, Nat.shiftLeft_zero]
    unfold dpP1
    congr 2

/-- **The DP on base-3 chunks is the DP with the chunked conversion network.** -/
theorem dpP1B_eq_dpP1C {r s h : Nat} {cnv : NetC} (hcnv : netCOK s cnv = true) (cp : Cprog) :
    dpP1B r s h cnv cp = dpP1C r s cnv cp := by
  rw [dpP1B_eq_dpP1 hcnv, dpP1_eq_dpP1C hcnv]

/-- **The initial check on base-3 chunks is the initial check.** -/
theorem checkInit_eq_checkInitB {s : Nat} {cnv : NetC} (hcnv : netCOK s cnv = true) (r h : Nat)
    (cp : Cprog) (H0 : List Nat) :
    checkInit r (netOfChunks s cnv) cp H0 = checkInitB r s h cnv cp H0 := by
  rw [checkInit, checkInitB, dpP1B_eq_dpP1 hcnv]

/-- **The final check on base-3 chunks is the final check.** -/
theorem checkFinal_eq_checkFinalB {s : Nat} {cnv : NetC} (hcnv : netCOK s cnv = true) (r h : Nat)
    (cpc : Cprog) (H : List Nat) :
    checkFinal r (netOfChunks s cnv) cpc H = checkFinalB r s h cnv cpc H := by
  rw [checkFinal, checkFinalB, dpP1B_eq_dpP1 hcnv]

end FourColor.Engine
