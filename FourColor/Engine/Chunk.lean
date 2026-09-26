/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Engine.Bits

/-!
# Reducibility engine: delta-swap networks on chunked numbers

Palomar's checker nanoda computes `x >>> d` as a long division by `2 ^ d`, whose cost grows
like `|x >>> d| * d`; a delta swap `deltaSwap x (m, d)` on the `2^21`-bit layout of ring size 14
with `d` up to `2^20` is therefore very slow there.  This file applies networks to numbers cut into
*chunks* of `W = 2 ^ s` bits (a
`List Nat`, least significant chunk first, missing chunks being `0`), with a network given by
the chunks of its masks (`NetC`, a list of `(mask chunks, distance)`):

* a layer of distance `d < W` whose mask chunks have no pair `(j, j + d)` crossing a chunk
  boundary (`m_i < 2 ^ (W - d)`) acts inside each chunk: `x_i ↦ deltaSwap x_i (m_i, d)`
  (`swapInC`); its right shifts are by less than `W` bits, on `W`-bit numbers;
* a layer of distance `d = δ * W` only combines whole chunks: `t_i = (x_{i+δ} ^^^ x_i) &&& m_i`,
  `x'_i = x_i ^^^ t_i ^^^ t_{i-δ}` (`crossC`), with no shift at all.

`layerCOK`/`netCOK` check (by kernel evaluation, once per network) that every layer is of one of
these two kinds; under this check the chunked application computes the chunks of the ordinary
one, with the masks assembled from their chunks (`netOfChunks`):

`ofChunks s (applyNetC s net xs) = applyNet (netOfChunks s net) (ofChunks s xs)`
(`ofChunks_applyNetC`).

The functions evaluated by the kernel are written with recursors (`List.rec`, `Nat.rec`) and
the `Nat` primitives, which the kernel reduces with less overhead than compiled `match`es and
type-class operators; they are `noncomputable`.
Each one has its defining equations proved by `rfl` and a chunk-wise characterisation
(`getD_*`).
-/

namespace FourColor.Engine

/-! ### Chunked numbers -/

/-- `ofChunks s cs`: the number whose chunks of `2 ^ s` bits are `cs`, least significant chunk
first; each chunk is truncated to its `2 ^ s` low bits. -/
def ofChunks (s : Nat) : List Nat → Nat
  | [] => 0
  | c :: cs => (c &&& ones (2 ^ s)) ||| (ofChunks s cs <<< 2 ^ s)

@[simp] theorem ofChunks_nil (s : Nat) : ofChunks s [] = 0 := rfl

theorem ofChunks_cons (s c : Nat) (cs : List Nat) :
    ofChunks s (c :: cs) = (c &&& ones (2 ^ s)) ||| (ofChunks s cs <<< 2 ^ s) := rfl

/-- The bits of a chunked number: bit `i` is bit `i % 2^s` of chunk `i / 2^s`. -/
theorem testBit_ofChunks (s : Nat) (cs : List Nat) (i : Nat) :
    (ofChunks s cs).testBit i = (cs.getD (i / 2 ^ s) 0).testBit (i % 2 ^ s) := by
  have hW : 0 < 2 ^ s := Nat.two_pow_pos s
  induction cs generalizing i with
  | nil => simp
  | cons c cs ih =>
    rw [ofChunks_cons, Nat.testBit_or, Nat.testBit_and, testBit_ones, Nat.testBit_shiftLeft]
    by_cases hi : i < 2 ^ s
    · rw [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
      simp [hi]
    · have e : i = (i - 2 ^ s) + 2 ^ s * 1 := by omega
      have e1 : i / 2 ^ s = (i - 2 ^ s) / 2 ^ s + 1 := by
        conv_lhs => rw [e]
        rw [Nat.add_mul_div_left _ _ hW]
      have e2 : i % 2 ^ s = (i - 2 ^ s) % 2 ^ s := by
        conv_lhs => rw [e]
        rw [Nat.add_mul_mod_self_left]
      rw [e1, e2, List.getD_cons_succ, ← ih]
      simp [hi, show 2 ^ s ≤ i by omega]

/-- The bits of a chunked number, at `2^s * c + j` with `j < 2^s`. -/
theorem testBit_ofChunks_mul_add (s : Nat) (cs : List Nat) (c : Nat) {j : Nat}
    (hj : j < 2 ^ s) : (ofChunks s cs).testBit (2 ^ s * c + j) = (cs.getD c 0).testBit j := by
  rw [testBit_ofChunks, Nat.mul_add_div (Nat.two_pow_pos s), Nat.div_eq_of_lt hj,
    Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]

/-- Every bit position is `2^s * c + j` with `j < 2^s`. -/
theorem exists_chunk_pos (s i : Nat) : ∃ c j, j < 2 ^ s ∧ i = 2 ^ s * c + j :=
  ⟨i / 2 ^ s, i % 2 ^ s, Nat.mod_lt _ (Nat.two_pow_pos s), (Nat.div_add_mod i (2 ^ s)).symm⟩

/-- Two chunk lists with the same chunks (up to the default `0`) represent the same number. -/
theorem ofChunks_congr {s : Nat} {xs ys : List Nat}
    (h : ∀ c, (xs.getD c 0) &&& ones (2 ^ s) = (ys.getD c 0) &&& ones (2 ^ s)) :
    ofChunks s xs = ofChunks s ys := by
  apply Nat.eq_of_testBit_eq
  intro i
  obtain ⟨c, j, hj, rfl⟩ := exists_chunk_pos s i
  rw [testBit_ofChunks_mul_add s xs c hj, testBit_ofChunks_mul_add s ys c hj]
  have := congrArg (fun n => n.testBit j) (h c)
  simpa [Nat.testBit_and, testBit_ones, hj] using this

/-! ### List helpers (recursor style) -/

/-- Chunk-wise `|||` of two chunk lists (missing chunks are `0`). -/
noncomputable def orC (xs : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun ys => ys)
    (fun x xs' ih ys => List.rec (motive := fun _ => List Nat) (x :: xs')
      (fun y ys' _ => Nat.lor x y :: ih ys') ys) xs

theorem orC_nil (ys : List Nat) : orC [] ys = ys := rfl
theorem orC_cons_nil (x : Nat) (xs : List Nat) : orC (x :: xs) [] = x :: xs := rfl
theorem orC_cons_cons (x y : Nat) (xs ys : List Nat) :
    orC (x :: xs) (y :: ys) = (x ||| y) :: orC xs ys := rfl

theorem getD_orC (xs ys : List Nat) (i : Nat) :
    (orC xs ys).getD i 0 = xs.getD i 0 ||| ys.getD i 0 := by
  induction xs generalizing ys i with
  | nil => simp [orC_nil]
  | cons x xs ih =>
    cases ys with
    | nil => simp [orC_cons_nil]
    | cons y ys =>
      cases i with
      | zero => simp only [orC_cons_cons, List.getD_cons_zero]
      | succ i => simp only [orC_cons_cons, List.getD_cons_succ, ih]

theorem ofChunks_orC (s : Nat) (xs ys : List Nat) :
    ofChunks s (orC xs ys) = ofChunks s xs ||| ofChunks s ys := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_or, testBit_ofChunks, testBit_ofChunks, testBit_ofChunks, getD_orC,
    Nat.testBit_or]

/-- Chunk-wise `^^^` of two chunk lists (missing chunks are `0`). -/
noncomputable def xorC (xs : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun ys => ys)
    (fun x xs' ih ys => List.rec (motive := fun _ => List Nat) (x :: xs')
      (fun y ys' _ => Nat.xor x y :: ih ys') ys) xs

theorem xorC_nil (ys : List Nat) : xorC [] ys = ys := rfl
theorem xorC_cons_nil (x : Nat) (xs : List Nat) : xorC (x :: xs) [] = x :: xs := rfl
theorem xorC_cons_cons (x y : Nat) (xs ys : List Nat) :
    xorC (x :: xs) (y :: ys) = (x ^^^ y) :: xorC xs ys := rfl

theorem getD_xorC (xs ys : List Nat) (i : Nat) :
    (xorC xs ys).getD i 0 = xs.getD i 0 ^^^ ys.getD i 0 := by
  induction xs generalizing ys i with
  | nil => simp [xorC_nil]
  | cons x xs ih =>
    cases ys with
    | nil => simp [xorC_cons_nil]
    | cons y ys =>
      cases i with
      | zero => simp only [xorC_cons_cons, List.getD_cons_zero]
      | succ i => simp only [xorC_cons_cons, List.getD_cons_succ, ih]

/-- `dropC n l`: `l` without its first `n` elements. -/
noncomputable def dropC (n : Nat) : List Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat) (fun l => l)
    (fun _ ih l => List.rec (motive := fun _ => List Nat) [] (fun _ l' _ => ih l') l) n

theorem dropC_zero (l : List Nat) : dropC 0 l = l := rfl
theorem dropC_succ_nil (n : Nat) : dropC (n + 1) [] = [] := rfl
theorem dropC_succ_cons (n a : Nat) (l : List Nat) : dropC (n + 1) (a :: l) = dropC n l := rfl

theorem getD_dropC (n : Nat) (l : List Nat) (i : Nat) :
    (dropC n l).getD i 0 = l.getD (n + i) 0 := by
  induction n generalizing l with
  | zero => simp [dropC_zero]
  | succ n ih =>
    cases l with
    | nil => simp [dropC_succ_nil]
    | cons a l => rw [dropC_succ_cons, ih, show n + 1 + i = (n + i) + 1 by omega,
        List.getD_cons_succ]

/-! ### The layers -/

/-- The layer of distance `d` acting inside each chunk: `x_i ↦ deltaSwap x_i (m_i, d)` (chunks
beyond the mask list are unchanged; `deltaSwap 0 _ = 0`). -/
noncomputable def swapInC (d : Nat) (ms : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun xs => xs)
    (fun m _ ih xs => List.rec (motive := fun _ => List Nat) []
      (fun x xs' _ =>
        (let t := Nat.land (Nat.xor (Nat.shiftRight x d) x) m
         Nat.xor (Nat.xor x t) (Nat.shiftLeft t d)) :: ih xs') xs) ms

theorem swapInC_nil (d : Nat) (xs : List Nat) : swapInC d [] xs = xs := rfl
theorem swapInC_cons_nil (d m : Nat) (ms : List Nat) : swapInC d (m :: ms) [] = [] := rfl
theorem swapInC_cons_cons (d m x : Nat) (ms xs : List Nat) :
    swapInC d (m :: ms) (x :: xs) = deltaSwap x (m, d) :: swapInC d ms xs := rfl

theorem deltaSwap_zero_left (m d : Nat) : deltaSwap 0 (m, d) = 0 := by
  simp [deltaSwap]

theorem deltaSwap_zero_mask (x d : Nat) : deltaSwap x (0, d) = x := by
  simp [deltaSwap]

theorem getD_swapInC (d : Nat) (ms xs : List Nat) (i : Nat) :
    (swapInC d ms xs).getD i 0 = deltaSwap (xs.getD i 0) (ms.getD i 0, d) := by
  induction ms generalizing xs i with
  | nil => simp [swapInC_nil, deltaSwap_zero_mask]
  | cons m ms ih =>
    cases xs with
    | nil => simp [swapInC_cons_nil, deltaSwap_zero_left]
    | cons x xs =>
      cases i with
      | zero => simp only [swapInC_cons_cons, List.getD_cons_zero]
      | succ i => simp only [swapInC_cons_cons, List.getD_cons_succ, ih]

/-- `crossTC ms xs ys`: the chunks `(y_i ^^^ x_i) &&& m_i`, for `i` below the length of `ms`
(with `ys = dropC δ xs`: the pairs of a layer of distance `δ` chunks). -/
noncomputable def crossTC (ms : List Nat) : List Nat → List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat → List Nat) (fun _ _ => [])
    (fun m _ ih xs ys =>
      List.rec (motive := fun _ => List Nat)
        (List.rec (motive := fun _ => List Nat) [] (fun y ys' _ => Nat.land y m :: ih [] ys') ys)
        (fun x xs' _ => List.rec (motive := fun _ => List Nat)
          (Nat.land x m :: ih xs' [])
          (fun y ys' _ => Nat.land (Nat.xor y x) m :: ih xs' ys') ys) xs) ms

theorem crossTC_nil (xs ys : List Nat) : crossTC [] xs ys = [] := rfl
theorem crossTC_cons_nil_nil (m : Nat) (ms : List Nat) :
    crossTC (m :: ms) [] [] = [] := rfl
theorem crossTC_cons_nil_cons (m y : Nat) (ms ys : List Nat) :
    crossTC (m :: ms) [] (y :: ys) = (y &&& m) :: crossTC ms [] ys := rfl
theorem crossTC_cons_cons_nil (m x : Nat) (ms xs : List Nat) :
    crossTC (m :: ms) (x :: xs) [] = (x &&& m) :: crossTC ms xs [] := rfl
theorem crossTC_cons_cons_cons (m x y : Nat) (ms xs ys : List Nat) :
    crossTC (m :: ms) (x :: xs) (y :: ys) = ((y ^^^ x) &&& m) :: crossTC ms xs ys := rfl

theorem getD_crossTC (ms xs ys : List Nat) (i : Nat) :
    (crossTC ms xs ys).getD i 0 = (ys.getD i 0 ^^^ xs.getD i 0) &&& ms.getD i 0 := by
  induction ms generalizing xs ys i with
  | nil => simp [crossTC_nil]
  | cons m ms ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil =>
        rw [crossTC_cons_nil_nil]
        cases i <;> simp
      | cons y ys =>
        cases i with
        | zero => simp [crossTC_cons_nil_cons]
        | succ i =>
          simp only [crossTC_cons_nil_cons, List.getD_cons_succ, ih, List.getD_nil]
    | cons x xs =>
      cases ys with
      | nil =>
        cases i with
        | zero => simp [crossTC_cons_cons_nil]
        | succ i => simp only [crossTC_cons_cons_nil, List.getD_cons_succ, ih, List.getD_nil]
      | cons y ys =>
        cases i with
        | zero => simp only [crossTC_cons_cons_cons, List.getD_cons_zero]
        | succ i => simp only [crossTC_cons_cons_cons, List.getD_cons_succ, ih]

/-- `xorAtC n ys ts`: `ys` with `ts` xored in from chunk `n` on (`ys` padded with zeros). -/
noncomputable def xorAtC (n : Nat) : List Nat → List Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat → List Nat → List Nat) (fun ys ts => xorC ys ts)
    (fun _ ih ys ts => List.rec (motive := fun _ => List Nat) (0 :: ih [] ts)
      (fun y ys' _ => y :: ih ys' ts) ys) n

theorem xorAtC_zero (ys ts : List Nat) : xorAtC 0 ys ts = xorC ys ts := rfl
theorem xorAtC_succ_nil (n : Nat) (ts : List Nat) : xorAtC (n + 1) [] ts = 0 :: xorAtC n [] ts :=
  rfl
theorem xorAtC_succ_cons (n y : Nat) (ys ts : List Nat) :
    xorAtC (n + 1) (y :: ys) ts = y :: xorAtC n ys ts := rfl

theorem getD_xorAtC (n : Nat) (ys ts : List Nat) (i : Nat) :
    (xorAtC n ys ts).getD i 0 = ys.getD i 0 ^^^ (if n ≤ i then ts.getD (i - n) 0 else 0) := by
  induction n generalizing ys i with
  | zero => rw [xorAtC_zero, getD_xorC, ite_eq_left (Nat.zero_le i), Nat.sub_zero]
  | succ n ih =>
    cases ys with
    | nil =>
      rw [xorAtC_succ_nil]
      cases i with
      | zero => simp
      | succ i =>
        rw [List.getD_cons_succ, ih]
        simp [show (n + 1 ≤ i + 1) = (n ≤ i) from propext (by omega),
          show i + 1 - (n + 1) = i - n by omega]
    | cons y ys =>
      rw [xorAtC_succ_cons]
      cases i with
      | zero => simp
      | succ i =>
        rw [List.getD_cons_succ, ih, List.getD_cons_succ]
        simp [show (n + 1 ≤ i + 1) = (n ≤ i) from propext (by omega),
          show i + 1 - (n + 1) = i - n by omega]

/-- The layer of distance `δ` chunks: `x'_i = x_i ^^^ t_i ^^^ t_{i-δ}` with
`t_i = (x_{i+δ} ^^^ x_i) &&& m_i`. -/
noncomputable def crossC (δ : Nat) (ms xs : List Nat) : List Nat :=
  let ts := crossTC ms xs (dropC δ xs)
  xorAtC δ (xorC xs ts) ts

theorem getD_crossC (δ : Nat) (ms xs : List Nat) (i : Nat) :
    (crossC δ ms xs).getD i 0 =
      xs.getD i 0 ^^^ ((xs.getD (δ + i) 0 ^^^ xs.getD i 0) &&& ms.getD i 0) ^^^
        (if δ ≤ i then
          (xs.getD (δ + (i - δ)) 0 ^^^ xs.getD (i - δ) 0) &&& ms.getD (i - δ) 0 else 0) := by
  simp only [crossC, getD_xorAtC, getD_xorC, getD_crossTC, getD_dropC]

/-- A layer of a chunked network: dispatch on `δ = d >>> s` (`δ = 0`: inside the chunks,
otherwise `δ` chunks apart). -/
noncomputable def layerCAux (xs ms : List Nat) (d : Nat) : Nat → List Nat :=
  Nat.rec (motive := fun _ => List Nat) (swapInC d ms xs) (fun δ _ => crossC (Nat.succ δ) ms xs)

/-- Apply one layer `L = (mask chunks, distance)` of a chunked network. -/
noncomputable def layerC (s : Nat) (xs : List Nat) (L : List Nat × Nat) : List Nat :=
  layerCAux xs L.1 L.2 (Nat.shiftRight L.2 s)

theorem layerCAux_zero (xs ms : List Nat) (d : Nat) :
    layerCAux xs ms d 0 = swapInC d ms xs := rfl
theorem layerCAux_succ (xs ms : List Nat) (d δ : Nat) :
    layerCAux xs ms d (δ + 1) = crossC (δ + 1) ms xs := rfl

/-- A chunked network: a list of layers `(mask chunks, distance)`. -/
abbrev NetC := List (List Nat × Nat)

/-- Apply a chunked network, first layer first. -/
noncomputable def applyNetC (s : Nat) (net : NetC) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun xs => xs)
    (fun L _ ih xs => ih (layerC s xs L)) net

theorem applyNetC_nil (s : Nat) (xs : List Nat) : applyNetC s [] xs = xs := rfl
theorem applyNetC_cons (s : Nat) (L : List Nat × Nat) (net : NetC) (xs : List Nat) :
    applyNetC s (L :: net) xs = applyNetC s net (layerC s xs L) := rfl

/-! ### Balanced assembly of the masks

The kernel keeps every intermediate number of a declaration in its cache, so the masks of the
ordinary network (evaluated only by `tauCheck`/`cnvCheck`) are assembled from their chunks by
pairwise merging (`assemble`: about `log₂ n` copies of the mask are cached) rather than by the
linear fold `ofChunks` (about `n` copies of growing size). -/

/-- `ofPieces w l`: the number whose pieces of `w` bits are `l`, least significant first (the
pieces are not truncated). -/
def ofPieces (w : Nat) : List Nat → Nat
  | [] => 0
  | a :: l => a ||| (ofPieces w l <<< w)

/-- One level of the balanced assembly: consecutive pairs of `w`-bit pieces become `2w`-bit
pieces. -/
def pairUp (w : Nat) : List Nat → List Nat
  | a :: b :: l => (a ||| (b <<< w)) :: pairUp w l
  | l => l

/-- Balanced assembly of pieces of `w` bits: `f` levels of `pairUp`, then the linear fold. -/
def assemble : Nat → Nat → List Nat → Nat
  | 0, w, l => ofPieces w l
  | f + 1, w, l =>
    match l with
    | [] => 0
    | [a] => a
    | _ :: _ :: _ => assemble f (2 * w) (pairUp w l)

private theorem shiftLeft_or_distrib' (a b w : Nat) :
    (a ||| b) <<< w = (a <<< w) ||| (b <<< w) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  cases decide (i ≥ w) <;> simp

theorem ofPieces_pairUp (w : Nat) :
    ∀ (n : Nat) (l : List Nat), l.length ≤ n →
      ofPieces (2 * w) (pairUp w l) = ofPieces w l := by
  intro n
  induction n with
  | zero => intro l hl; rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)]; rfl
  | succ n ih =>
    intro l hl
    match l with
    | [] => rfl
    | [a] => simp [pairUp, ofPieces]
    | a :: b :: l =>
      simp only [List.length_cons] at hl
      show (a ||| (b <<< w)) ||| (ofPieces (2 * w) (pairUp w l) <<< (2 * w)) =
        a ||| ((b ||| (ofPieces w l <<< w)) <<< w)
      rw [ih l (by omega), shiftLeft_or_distrib', ← Nat.shiftLeft_add, Nat.or_assoc,
        show w + w = 2 * w by omega]

theorem assemble_eq : ∀ (f w : Nat) (l : List Nat), assemble f w l = ofPieces w l := by
  intro f
  induction f with
  | zero => intro w l; rfl
  | succ f ih =>
    intro w l
    match l with
    | [] => rfl
    | [a] => simp [assemble, ofPieces]
    | a :: b :: l =>
      rw [show assemble (f + 1) w (a :: b :: l) = assemble f (2 * w) (pairUp w (a :: b :: l))
        from rfl, ih, ofPieces_pairUp w _ _ le_rfl]

theorem ofChunks_eq_ofPieces (s : Nat) (cs : List Nat) :
    ofChunks s cs = ofPieces (2 ^ s) (cs.map (· &&& ones (2 ^ s))) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [ofChunks_cons, ih]; rfl

/-- The ordinary network whose masks are assembled from their chunks (by pairwise merging,
`netOfChunks_eq`). -/
def netOfChunks (s : Nat) (net : NetC) : Net :=
  net.map fun L => (assemble L.1.length (2 ^ s) (L.1.map (· &&& ones (2 ^ s))), L.2)

/-- The masks of `netOfChunks` are the numbers represented by their chunks. -/
theorem netOfChunks_eq (s : Nat) (net : NetC) :
    netOfChunks s net = net.map fun L => (ofChunks s L.1, L.2) := by
  unfold netOfChunks
  congr 1
  funext L
  rw [assemble_eq, ← ofChunks_eq_ofPieces]

/-- The check of a layer of a chunked network: either `d < 2^s` and no pair `(j, j + d)` of a
mask chunk crosses a chunk boundary, or `d` is a multiple of `2^s`. -/
def layerCOK (s : Nat) (L : List Nat × Nat) : Bool :=
  if Nat.beq (L.2 >>> s) 0 then L.1.all fun m => Nat.blt m (1 <<< (2 ^ s - L.2))
  else Nat.beq ((L.2 >>> s) <<< s) L.2

/-- The check of a chunked network (`ofChunks_applyNetC`). -/
def netCOK (s : Nat) (net : NetC) : Bool := net.all (layerCOK s)

/-! ### Correctness -/

/-- The bits of a delta swap, without any hypothesis on the layer. -/
theorem testBit_deltaSwap_gen (x m d i : Nat) :
    (deltaSwap x (m, d)).testBit i =
      (x.testBit i ^^ ((x.testBit (d + i) ^^ x.testBit i) && m.testBit i) ^^
        (decide (d ≤ i) && ((x.testBit i ^^ x.testBit (i - d)) && m.testBit (i - d)))) := by
  simp only [deltaSwap, Nat.testBit_xor, Nat.testBit_land, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  by_cases h : d ≤ i
  · have e : d + (i - d) = i := by omega
    simp [h, e]
  · simp [h]

/-- A chunk of a list of numbers below `B` is below `B`. -/
theorem getD_lt_of_forall {l : List Nat} {B : Nat} (h : ∀ m ∈ l, m < B) (hB : 0 < B) (c : Nat) :
    l.getD c 0 < B := by
  rw [List.getD_eq_getElem?_getD]
  cases h' : l[c]? with
  | none => simpa using hB
  | some v => exact h v (List.mem_of_getElem? h')

/-- The in-chunk layer computes the chunks of the delta swap, when no pair of the mask crosses a
chunk boundary. -/
theorem ofChunks_swapInC {s d : Nat} {ms : List Nat} (hms : ∀ m ∈ ms, m < 2 ^ (2 ^ s - d))
    (hd : d < 2 ^ s) (xs : List Nat) :
    ofChunks s (swapInC d ms xs) = deltaSwap (ofChunks s xs) (ofChunks s ms, d) := by
  have hlt : ∀ c, ms.getD c 0 < 2 ^ (2 ^ s - d) := getD_lt_of_forall hms (Nat.two_pow_pos _)
  have hhi : ∀ c j, 2 ^ s - d ≤ j → (ms.getD c 0).testBit j = false :=
    fun c j hj => Nat.testBit_eq_false_of_lt (Nat.lt_of_lt_of_le (hlt c)
      (Nat.pow_le_pow_right (by norm_num) hj))
  apply Nat.eq_of_testBit_eq
  intro i
  obtain ⟨c, j, hj, rfl⟩ := exists_chunk_pos s i
  rw [testBit_ofChunks_mul_add s _ c hj, getD_swapInC, testBit_deltaSwap_gen,
    testBit_deltaSwap_gen, testBit_ofChunks_mul_add s xs c hj, testBit_ofChunks_mul_add s ms c hj]
  -- the pair `(j, j + d)`
  have hA : (((ofChunks s xs).testBit (d + (2 ^ s * c + j)) ^^ (xs.getD c 0).testBit j) &&
      (ms.getD c 0).testBit j) =
      (((xs.getD c 0).testBit (d + j) ^^ (xs.getD c 0).testBit j) && (ms.getD c 0).testBit j) := by
    cases hm : (ms.getD c 0).testBit j with
    | false => simp
    | true =>
      have hjd : j < 2 ^ s - d := by
        by_contra hc; rw [hhi c j (by omega)] at hm; exact absurd hm (by decide)
      rw [show d + (2 ^ s * c + j) = 2 ^ s * c + (d + j) by omega,
        testBit_ofChunks_mul_add s xs c (by omega)]
  -- the pair `(j - d, j)`
  have hB : (decide (d ≤ 2 ^ s * c + j) && (((xs.getD c 0).testBit j ^^
      (ofChunks s xs).testBit (2 ^ s * c + j - d)) &&
        (ofChunks s ms).testBit (2 ^ s * c + j - d))) =
      (decide (d ≤ j) && (((xs.getD c 0).testBit j ^^ (xs.getD c 0).testBit (j - d)) &&
        (ms.getD c 0).testBit (j - d))) := by
    by_cases hdj : d ≤ j
    · have e : 2 ^ s * c + j - d = 2 ^ s * c + (j - d) := by omega
      rw [e, testBit_ofChunks_mul_add s xs c (by omega),
        testBit_ofChunks_mul_add s ms c (by omega)]
      simp [hdj, show d ≤ 2 ^ s * c + j by omega]
    · rw [decide_eq_false hdj, Bool.false_and]
      by_cases hdi : d ≤ 2 ^ s * c + j
      · -- the pair comes from the previous chunk, whose mask has no bit there
        have hc : 1 ≤ c := by
          rcases Nat.eq_zero_or_pos c with h0 | h0
          · subst h0; omega
          · exact h0
        have e : 2 ^ s * c + j - d = 2 ^ s * (c - 1) + (2 ^ s + j - d) := by
          have : 2 ^ s * c = 2 ^ s * (c - 1) + 2 ^ s := by
            rw [← Nat.mul_add_one]; congr 1; omega
          omega
        rw [e, testBit_ofChunks_mul_add s ms (c - 1) (by omega), hhi (c - 1) _ (by omega)]
        simp
      · simp [hdi]
  rw [hA, hB]

/-- The cross-chunk layer computes the chunks of the delta swap of distance `δ * 2^s`. -/
theorem ofChunks_crossC (s δ : Nat) (ms xs : List Nat) :
    ofChunks s (crossC δ ms xs) = deltaSwap (ofChunks s xs) (ofChunks s ms, δ * 2 ^ s) := by
  apply Nat.eq_of_testBit_eq
  intro i
  obtain ⟨c, j, hj, rfl⟩ := exists_chunk_pos s i
  rw [testBit_ofChunks_mul_add s _ c hj, getD_crossC, testBit_deltaSwap_gen,
    testBit_ofChunks_mul_add s xs c hj, testBit_ofChunks_mul_add s ms c hj,
    show δ * 2 ^ s + (2 ^ s * c + j) = 2 ^ s * (δ + c) + j by rw [Nat.mul_add]; ring,
    testBit_ofChunks_mul_add s xs (δ + c) hj]
  simp only [Nat.testBit_xor, Nat.testBit_land]
  congr 1
  by_cases hδ : δ ≤ c
  · have e : 2 ^ s * c + j - δ * 2 ^ s = 2 ^ s * (c - δ) + j := by
      have : 2 ^ s * c = 2 ^ s * (c - δ) + δ * 2 ^ s := by
        rw [Nat.mul_comm δ, ← Nat.mul_add]; congr 1; omega
      omega
    have hle : δ * 2 ^ s ≤ 2 ^ s * c + j := by
      have := Nat.mul_le_mul_right (2 ^ s) hδ
      rw [Nat.mul_comm c] at this; omega
    rw [ite_eq_left hδ, e, testBit_ofChunks_mul_add s xs (c - δ) hj,
      testBit_ofChunks_mul_add s ms (c - δ) hj, show δ + (c - δ) = c by omega]
    simp [hle, Nat.testBit_xor]
  · have hlt : ¬ δ * 2 ^ s ≤ 2 ^ s * c + j := by
      intro h
      have : 2 ^ s * c + j < 2 ^ s * (c + 1) := by rw [Nat.mul_add_one]; omega
      have := Nat.lt_of_le_of_lt h this
      rw [Nat.mul_comm δ] at this
      have := Nat.lt_of_mul_lt_mul_left this
      omega
    rw [ite_eq_right hδ]
    simp [hlt]

/-- One checked layer computes the chunks of the ordinary delta swap. -/
theorem ofChunks_layerC {s : Nat} {L : List Nat × Nat} (h : layerCOK s L = true)
    (xs : List Nat) :
    ofChunks s (layerC s xs L) = deltaSwap (ofChunks s xs) (ofChunks s L.1, L.2) := by
  obtain ⟨ms, d⟩ := L
  simp only [layerCOK] at h
  simp only [layerC]
  cases hδ : d >>> s with
  | zero =>
    rw [hδ] at h
    simp only [show Nat.beq 0 0 = true from rfl, ite_true, List.all_eq_true, Nat.blt_eq,
      Nat.one_shiftLeft] at h
    have hd : d < 2 ^ s := by
      rw [Nat.shiftRight_eq_div_pow] at hδ
      exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos s)).1 hδ
    rw [show Nat.shiftRight d s = 0 from hδ, layerCAux_zero]
    exact ofChunks_swapInC h hd xs
  | succ δ =>
    rw [hδ] at h
    simp only [show Nat.beq (δ + 1) 0 = false from rfl, Bool.false_eq_true, ite_false,
      Nat.beq_eq, Nat.shiftLeft_eq] at h
    rw [show Nat.shiftRight d s = δ + 1 from hδ, layerCAux_succ, ofChunks_crossC, h]

/-- **The chunked application of a checked network computes the chunks of the ordinary
application**, with the masks assembled from their chunks. -/
theorem ofChunks_applyNetC {s : Nat} {net : NetC} (h : netCOK s net = true) (xs : List Nat) :
    ofChunks s (applyNetC s net xs) = applyNet (netOfChunks s net) (ofChunks s xs) := by
  rw [netOfChunks_eq]
  induction net generalizing xs with
  | nil => rfl
  | cons L net ih =>
    simp only [netCOK, List.all_cons, Bool.and_eq_true] at h
    rw [applyNetC_cons, ih h.2, ofChunks_layerC h.1]
    rfl

end FourColor.Engine
