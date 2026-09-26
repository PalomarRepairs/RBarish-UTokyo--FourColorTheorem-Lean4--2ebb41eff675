/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import Lean
import FourColor.Engine.CheckChunk
import FourColor.Engine.NetSplit
import FourColor.Engine.DPChunk
import FourColor.Engine.KempeChunk

/-!
# Reducibility engine: elaboration-time generation of big literals and certificates

The engine's kernel checks need big-number *data*: the masks of the delta-swap networks (per
ring size) and the checkpoints of the round iterations (per configuration).  They are never
elaborated as numerals (a 4 MB numeral takes minutes to elaborate) nor committed as data files:
they are computed at elaboration time and injected directly as raw literals
(`mkRawNatLit`) in ordinary definitions (`addDecl`), whose values the kernel then *checks*
through the kernel-evaluated theorems of the engine (`tauCheck`, `cnvCheck`, `checkInit`,
`checkStep`, `checkFinal`).  Nothing in this file is trusted: it is meta code, never part of a
proof, and a wrong literal only makes a kernel check fail.  Every theorem added by these
commands is checked by the kernel alone (its proof is `Eq.refl true`, or glue between such
theorems), in its own declaration (so the kernel cache is flushed between them), synchronously
(`Elab.async` is switched off for them) and without heartbeat limit.

## Commands

* `#engine_nets r` (`2 ≤ r`): computes the positions of the valid traces of ring size `r` in
  the packed layout, the permutations `τ12` (`Color1 ↔ Color2`) and base-3 prefix → packed
  layout, routes them through Beneš networks (`benesNet`, looping algorithm, empty layers
  dropped), cuts their masks into chunks of `2 ^ chunkLog = 2^16` bits (`chunkNet`; the layers
  of distance below `2^16` never pair bits of different chunks, the other ones have distances
  that are multiples of `2^16`, see `Chunk.lean`), and adds

  ```
  def FourColor.Engine.tauNetC<r> : NetC := ⟨literal⟩       -- mask chunks, ≤ 8 Kbit pieces
  def FourColor.Engine.tauNet<r> : Net := netOfChunks 16 tauNetC<r>
  theorem FourColor.Engine.tauNetOK<r> : netCOK 16 tauNetC<r> = true      -- kernel evaluation
  theorem FourColor.Engine.tauLayers<r> : tauNet<r>.all layerOK = true     -- kernel evaluation
  theorem FourColor.Engine.tauPart<r>_<p> : tauCheckAt r tauNet<r> p = true   -- p < r, kernel
  theorem FourColor.Engine.tauSpec<r> : TauSpec r tauNet<r> :=
    tauSpec_of_check _ (tauCheck_of_parts tauLayers<r> (allFrom_cons tauPart<r>_0 (…)))
  ```

  and the same for `cnv` (`cnvNetC<r>`, `cnvNet<r> := netOfChunks 16 cnvNetC<r>`,
  `cnvNetOK<r>`, `cnvLayers<r>`, `cnvPart<r>_<p>` for `p < r - 1`, `cnvSpec<r> : CnvSpec r
  cnvNet<r>`); the names do not depend on the current namespace.  The specifications are
  checked one position per declaration (`NetSplit.lean`): in one declaration the ring-14
  checks took 3.5 GB in Lean's kernel and 4.7 GB in Palomar's con-ron.  One file per ring size:
  `FourColor/Reducibility/Nets<r>.lean`.
* `#engine_certify cfNNN` (optionally `#engine_certify cfNNN (rounds := k)`): evaluates
  `contractProg cfNNN` (the constant `FourColor.contractProg` of the port of `cfcontract.v`),
  the coloring DP of the configuration and of its contract, then rounds until the contract
  traces are covered (all natively), places checkpoints every `k` rounds (`k` from the per-ring
  memory budget, see `roundsPerStep`, unless given), and adds, in the current namespace
  (`r` = ring size, `n` = number of checkpoint steps):

  ```
  def cfNNN_cpc : Cprog := ⟨literal⟩
  theorem cfNNN_ctr : contractProg cfNNN = some cfNNN_cpc        -- kernel evaluation
  theorem cfNNN_rc : cprsize cfNNN_cpc = r                        -- kernel evaluation
  def cfNNN_H0 … cfNNN_H<n> : List Nat := ⟨literal⟩                -- checkpoints (low halves)
  theorem cfNNN_init : checkInit r cnvNet<r> cfNNN.cfprog cfNNN_H0 = true
  theorem cfNNN_step<i> : checkStep r tauNet<r> k cfNNN_H<i> cfNNN_H<i+1> = true   -- i < n
  theorem cfNNN_final : checkFinal r cnvNet<r> cfNNN_cpc cfNNN_H<n> = true
  theorem cfNNN_reach : ReachN r tauNet<r> (expand r cfNNN_H0) (expand r cfNNN_H<n>)
  theorem cfNNN_reducible : CfReducible cfNNN
  ```

  The three kinds of kernel-heavy theorems are proved through chunked versions of the checks,
  which the kernel evaluates without big right shifts (Palomar's checker nanoda computes
  `x >>> d` by a long division): the networks on chunks of `2^16` bits (`CheckChunk.lean`),
  the Kempe step on row-group chunks (`KempeChunk.lean`) and the coloring DP on base-3 chunks
  of `3 ^ dpChunkDigits` bits (`DPChunk.lean`).  E.g. `cfNNN_step<i>` is
  `(checkStep_eq_checkStepB tauNetOK<r> r k H<i> H<i+1>).trans (Eq.refl true)`, the kernel
  evaluating `checkStepB r 16 tauNetC<r> k H<i> H<i+1>` (`tauNet<r>` unfolds to
  `netOfChunks 16 tauNetC<r>`); likewise `checkInit_eq_checkInitB` and
  `checkFinal_eq_checkFinalB` with `cnvNetOK<r>` and `dpChunkDigits`.

  The last theorem applies the constant `cfreducible_of_engine` (resolved in the current
  scope, else `FourColor.cfreducible_of_engine`), whose explicit and implicit arguments are
  matched **by binder name** with its statement in `CfReducible.lean` (`cf r hr hr2 tau cnv htau
  hcnv cpc hctr hrc H0 Hn hinit hreach hfinal`); its conclusion is taken from that constant.
* `#engine_def_natlist name := term`, `#engine_def_net name := term`: evaluate a term (compiled
  code, big-number operations natively through GMP) and define `name` as its literal value
  (compiled, so that later evaluations can use it);
* `#engine_load_net name "file"`: a network from a text file of lines `(0x<hex>, <dec>)` (as
  written by `scripts/engine_nets.py`; development only).

The literal definitions added by `#engine_nets` and `#engine_certify` are **not compiled**
(compiling would store every literal a second time, in the IR of the `.olean`); the generator
reads their values back from the environment (`netOfConst`, which also assembles the masks of
`netOfChunks s tauNetC<r>`).  Use `#engine_def_net` to get a compiled copy if a network is
needed in `#eval`.

Options: `engine.gen.memBudget` (MB of kernel memory per checkpoint step, default 1000),
`engine.gen.verbose` (log the native and kernel times of every step; also switched on by the
environment variable `ENGINE_GEN_VERBOSE`).

Determinism: the output (declarations and their values) depends only on the ring size and on
the configuration; the log messages contain timings only with `engine.gen.verbose`.
-/

open Lean Elab Command Meta

/-- Kernel memory budget (MB) of one checkpoint step of `#engine_certify`. -/
register_option engine.gen.memBudget : Nat := {
  defValue := 1000
  descr := "kernel memory budget (MB) of one checkpoint step of `#engine_certify`"
}

/-- Log the native and kernel times of the steps of `#engine_nets`/`#engine_certify`. -/
register_option engine.gen.verbose : Bool := {
  defValue := false
  descr := "log the native and kernel times of the steps of `#engine_nets`/`#engine_certify`"
}

namespace FourColor.Engine.Gen

open FourColor FourColor.Engine

/-! ### Literal expressions and declarations

Palomar exports the proof with `leanexport` and replays it with `leanchecker`, nanoda and
con-ron; the export (decimal) and `leanchecker`'s parser handle a `Nat` literal in time
quadratic in its size (a 2^21-bit literal takes 111 s to export), so big numbers are never
emitted as one literal: a number above
`chunkBits` bits is emitted as a balanced tree of `Nat.lor`/`Nat.shiftLeft` applications over
raw literals of at most `chunkBits` bits (`mkChunkedNat`), which the kernel reassembles (GMP
operations) the first time a declaration needs the value. -/

/-- The width (bits) of the literal chunks of big numbers. -/
def chunkBits : Nat := 8192

/-- The chunks of `n`, least significant first, `chunkBits` bits each (at least one). -/
def natChunks (n : Nat) : Array Nat := Id.run do
  let mask := (1 <<< chunkBits) - 1
  let mut out := #[n &&& mask]
  let mut m := n >>> chunkBits
  while m != 0 do
    out := out.push (m &&& mask)
    m := m >>> chunkBits
  return out

/-- A balanced `Nat.lor`/`Nat.shiftLeft` expression over the chunks `cs[lo:hi]` (`lo < hi`),
whose value is `∑ cs[i] <<< ((i - lo) * chunkBits)`; a range of zero chunks becomes the literal
`0` (`fuel` bounds the depth; `64` is plenty). -/
def chunkExprAux (cs : Array Nat) : Nat → Nat → Nat → Expr
  | 0, _, _ => mkRawNatLit 0
  | fuel + 1, lo, hi =>
    if hi ≤ lo + 1 then mkRawNatLit (cs[lo]?.getD 0)
    else if (List.range (hi - lo)).all fun i => cs[lo + i]?.getD 0 == 0 then mkRawNatLit 0
    else
      let mid := (lo + hi) / 2
      let hiE := chunkExprAux cs fuel mid hi
      let loE := chunkExprAux cs fuel lo mid
      match hiE with
      | .lit (.natVal 0) => loE
      | _ =>
        mkApp2 (mkConst ``Nat.lor) loE
          (mkApp2 (mkConst ``Nat.shiftLeft) hiE (mkRawNatLit ((mid - lo) * chunkBits)))

/-- The expression of a natural number: a raw literal if it has at most `chunkBits` bits,
otherwise a balanced tree of chunks (see above). -/
def mkChunkedNat (n : Nat) : Expr :=
  if n >>> chunkBits == 0 then mkRawNatLit n
  else
    let cs := natChunks n
    chunkExprAux cs 64 0 cs.size

/-- A `List Nat` literal expression (big numbers chunked, `mkChunkedNat`). -/
def mkNatListLit (xs : List Nat) : Expr :=
  let nat := mkConst ``Nat
  xs.foldr (fun a acc => mkApp3 (mkConst ``List.cons [0]) nat (mkChunkedNat a) acc)
    (mkApp (mkConst ``List.nil [0]) nat)

/-- A `List (Nat × Nat)` literal expression (big masks chunked, `mkChunkedNat`). -/
def mkNetLit (ps : List (Nat × Nat)) : Expr :=
  let nat := mkConst ``Nat
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) nat nat
  ps.foldr (fun (a, b) acc =>
      mkApp3 (mkConst ``List.cons [0]) pairTy
        (mkApp4 (mkConst ``Prod.mk [0, 0]) nat nat (mkChunkedNat a) (mkRawNatLit b)) acc)
    (mkApp (mkConst ``List.nil [0]) pairTy)

/-- The width exponent of the chunks of the chunked networks (`NetC`, `Chunk.lean`): chunks of
`2 ^ chunkLog = 65536` bits, each emitted as at most 8 literals of `chunkBits` bits. -/
def chunkLog : Nat := 16

/-- The coloring DP's chunks hold `3 ^ dpChunkDigits` bits (`DPChunk.lean`; measured best at 11). -/
def dpChunkDigits : Nat := 11

/-- The chunks of `2 ^ s` bits of `n`, least significant first, trailing zero chunks dropped
(`ofChunks s (natChunksW s n) = n`). -/
def natChunksW (s n : Nat) : List Nat := Id.run do
  let W := 2 ^ s
  let mask := (1 <<< W) - 1
  let mut out : Array Nat := #[]
  let mut m := n
  while m != 0 do
    out := out.push (m &&& mask)
    m := m >>> W
  return out.toList

/-- A network with its masks cut into chunks of `2 ^ s` bits (`netOfChunks s (chunkNet s net) =
net`). -/
def chunkNet (s : Nat) (net : Net) : NetC := net.map fun (m, d) => (natChunksW s m, d)

/-- A `NetC` literal expression (every chunk as `mkChunkedNat`). -/
def mkNetCLit (net : NetC) : Expr :=
  let nat := mkConst ``Nat
  let lnat := mkApp (mkConst ``List [0]) nat
  let pairTy := mkApp2 (mkConst ``Prod [0, 0]) lnat nat
  net.foldr (fun (ms, d) acc =>
      mkApp3 (mkConst ``List.cons [0]) pairTy
        (mkApp4 (mkConst ``Prod.mk [0, 0]) lnat nat
          (ms.foldr (fun m a => mkApp3 (mkConst ``List.cons [0]) nat (mkChunkedNat m) a)
            (mkApp (mkConst ``List.nil [0]) nat))
          (mkRawNatLit d)) acc)
    (mkApp (mkConst ``List.nil [0]) pairTy)

/-- A `Cpstep` literal expression. -/
def mkCpstepLit : Cpstep → Expr
  | .R n => mkApp (mkConst ``Cpstep.R) (mkNatLit n)
  | .R' => mkConst ``Cpstep.R'
  | .Y => mkConst ``Cpstep.Y
  | .H => mkConst ``Cpstep.H
  | .U => mkConst ``Cpstep.U
  | .K => mkConst ``Cpstep.K
  | .A => mkConst ``Cpstep.A

/-- A `Cprog` literal expression. -/
def mkCprogLit (cp : Cprog) : Expr :=
  let ty := mkConst ``Cpstep
  cp.foldr (fun s acc => mkApp3 (mkConst ``List.cons [0]) ty (mkCpstepLit s) acc)
    (mkApp (mkConst ``List.nil [0]) ty)

/-- The options under which the generated declarations are added: synchronous kernel checking
(so that at most one kernel cache is alive), no heartbeat limit, deep recursion allowed. -/
def kernelOpts (o : Options) : Options :=
  let o := Elab.async.set o false
  let o := maxHeartbeats.set o 0
  maxRecDepth.set o 100000

/-- Add a declaration (kernel-checked) under `kernelOpts`. -/
def addDeclK (decl : Declaration) : CoreM Unit :=
  withOptions kernelOpts (addDecl decl)

/-- Add a definition with a literal value (no elaboration of numerals), and compile it (so
that later elaboration-time evaluations can use it). -/
def addLitDef (name : Name) (type value : Expr) : CoreM Unit := do
  let decl := Declaration.defnDecl {
    name, levelParams := [], type, value, hints := .abbrev, safety := .safe }
  addDeclK decl
  compileDecl decl

/-- Add a definition with a literal value, not compiled but marked `noncomputable` (its value
is read back from the environment when needed, see `netOfConst`). -/
def addDataDef (name : Name) (type value : Expr) : CoreM Unit := do
  addDeclK <| .defnDecl { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }
  modifyEnv (addNoncomputable · name)

/-- Add a theorem, checked by the kernel alone. -/
def addThm (name : Name) (type value : Expr) : CoreM Unit :=
  addDeclK <| .thmDecl { name, levelParams := [], type, value }

/-- `@Eq Bool b true`. -/
def mkEqTrue (b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) b (mkConst ``true)

/-- `@Eq.refl Bool true`, the proof of the boolean checks (evaluated by the kernel). -/
def reflTrue : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true)

/-! ### Reading literals back from the environment -/

/-- A natural number literal (raw, or `OfNat.ofNat` of a raw literal), or a chunked number
(`Nat.lor`/`Nat.shiftLeft` applications over such literals, see `mkChunkedNat`). -/
partial def natOfExpr? (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | _ =>
    match e.consumeMData.getAppFnArgs with
    | (``Nat.lor, #[a, b]) => return (← natOfExpr? a) ||| (← natOfExpr? b)
    | (``Nat.shiftLeft, #[a, b]) => return (← natOfExpr? a) <<< (← natOfExpr? b)
    | _ => e.nat?

/-- A list literal (`List.cons`/`List.nil` applications, possibly under `mdata`). -/
partial def listOfExpr? (e : Expr) : Option (List Expr) :=
  match e.consumeMData.getAppFnArgs with
  | (``List.nil, #[_]) => some []
  | (``List.cons, #[_, a, as]) => (a :: ·) <$> listOfExpr? as
  | _ => none

/-- A network literal. -/
def netOfExpr? (e : Expr) : Option Net := do
  let ps ← listOfExpr? e
  ps.mapM fun p => do
    match p.consumeMData.getAppFnArgs with
    | (``Prod.mk, #[_, _, a, b]) => pure (← natOfExpr? a, ← natOfExpr? b)
    | _ => none

/-- A chunked network literal (see `mkNetCLit`). -/
def netCOfExpr? (e : Expr) : Option NetC := do
  let ps ← listOfExpr? e
  ps.mapM fun p => do
    match p.consumeMData.getAppFnArgs with
    | (``Prod.mk, #[_, _, a, b]) => pure (← (← listOfExpr? a).mapM natOfExpr?, ← natOfExpr? b)
    | _ => none

/-- The value of a definition. -/
def constValue (name : Name) : CoreM Expr := do
  let some ci := (← getEnv).find? name
    | throwError "unknown constant {name} (run `#engine_nets` for its ring size)"
  let some v := ci.value? (allowOpaque := true)
    | throwError "{name} is not a definition"
  return v

/-- The value of a network definition: a literal added by `#engine_def_net`, or
`netOfChunks s netC` with `netC` a chunked network literal or a constant defined as one (as
added by `#engine_nets`), whose masks are then assembled natively. -/
def netOfConst (name : Name) : CoreM Net := do
  let v ← constValue name
  if let some net := netOfExpr? v then return net
  match v.consumeMData.getAppFnArgs with
  | (``netOfChunks, #[sE, cE]) =>
    let some s := natOfExpr? sE | throwError "the value of {name} is not a network"
    let cE ← match cE.consumeMData with
      | .const c _ => constValue c
      | e => pure e
    let some netC := netCOfExpr? cE | throwError "the value of {name} is not a network"
    return netOfChunks s netC
  | _ => throwError "the value of {name} is not a network literal"

/-! ### Big numbers from bit-packed byte arrays -/

/-- Set bit `i` of a bit-packed byte array. -/
@[inline] def bset (ba : ByteArray) (i : Nat) : ByteArray :=
  let q := i / 8
  ba.set! q (ba.get! q ||| ((1 : UInt8) <<< (i % 8).toUInt8))

/-- The number whose little-endian bytes are `ba[lo : lo + len]` (divide and conquer; `fuel`
bounds the depth). -/
def natOfBytesAux (ba : ByteArray) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, lo, len =>
    if len ≤ 16 then
      (List.range len).foldr (fun i acc => acc * 256 + (ba.get! (lo + i)).toNat) 0
    else
      let h := len / 2
      natOfBytesAux ba fuel lo h ||| (natOfBytesAux ba fuel (lo + h) (len - h) <<< (8 * h))

/-- The number whose little-endian bytes are `ba`. -/
def natOfBytes (ba : ByteArray) : Nat := natOfBytesAux ba 64 0 ba.size

/-- The number of bits of `n`. -/
def bitLen (n : Nat) : Nat := if n == 0 then 0 else n.log2 + 1

/-! ### Beneš routing (looping algorithm)

A Beneš network on `N = 2^n` positions has `2n - 1` layers of delta swaps, of distances
`2^(n-1), …, 2, 1, 2, …, 2^(n-1)`.  It is routed level by level: at level `l < n - 1` the
positions form blocks of size `2h = 2^(n-l)`, in each of which the permutation `src`
(`src[j]` = the position whose bit must arrive at `j`) is split between the two halves (the
sub-networks) by following the cycles of the looping algorithm; this gives the masks of layer
`l` (distance `h`, before the sub-networks) and of layer `2n-2-l` (after them), and the
permutations of the half-blocks.  The middle layer (distance `1`) swaps what is left.  All the
blocks of a level are routed at once, in flat arrays (the code runs in the interpreter at
elaboration time).  The mask of a layer marks the lower position `i` of each swapped pair
`(i, i + d)`; `deltaSwap` then moves bit `i + d` to `i` and conversely.  The same algorithm is
implemented in `scripts/engine_nets.py`; both give the same networks. -/

/-- The inverse of the permutation `src` (positions `< j`). -/
def invAux (src : Array Nat) : Nat → Array Nat → Array Nat
  | 0, inv => inv
  | j + 1, inv => invAux src j (inv.set! src[j]! j)

/-- Follow one cycle of the looping algorithm from the input `i`: `i` goes to the lower
sub-network (`sub[i] = 1`), its partner `i ^^^ h` to the upper one (`sub = 2`); the output
paired with the output of the partner must then be fed from the lower sub-network too. -/
def loopCycle (src inv : Array Nat) (h : Nat) : Nat → Nat → ByteArray → ByteArray
  | 0, _, sub => sub
  | fuel + 1, i, sub =>
    let ip := i ^^^ h
    let sub := (sub.set! i 1).set! ip 2
    let i' := src[inv[ip]! ^^^ h]!
    if sub.get! i' == 0 then loopCycle src inv h fuel i' sub else sub

/-- Assign all the inputs `N - k … N - 1` (cycles started from the smallest unassigned input). -/
def loopAll (src inv : Array Nat) (h N : Nat) : Nat → ByteArray → ByteArray
  | 0, sub => sub
  | k + 1, sub =>
    let start := N - (k + 1)
    let sub := if sub.get! start == 0 then loopCycle src inv h N start sub else sub
    loopAll src inv h N k sub

/-- The masks of the outer layers of a level, the permutations `ns` of the half-blocks and
their inverse `ni`, for the lower positions `j0 ≥ j` of the pairs `(j0, j0 + h)` (`fuel`
bounds the number of pairs). -/
def levelAux (src : Array Nat) (sub : ByteArray) (h N : Nat) :
    Nat → Nat → ByteArray → ByteArray → Array Nat → Array Nat →
      ByteArray × ByteArray × Array Nat × Array Nat
  | 0, _, m1, m2, ns, ni => (m1, m2, ns, ni)
  | fuel + 1, j0, m1, m2, ns, ni =>
    if N ≤ j0 then (m1, m2, ns, ni) else
    let j1 := j0 + h
    let m1 := if sub.get! j0 == 2 then bset m1 j0 else m1
    let a0 := src[j0]!
    let a1 := src[j1]!
    -- the positions of the inputs `a0`, `a1` after the first layer
    let p0 := a0 - (a0 &&& h) + (if sub.get! a0 == 2 then h else 0)
    let p1 := a1 - (a1 &&& h) + (if sub.get! a1 == 2 then h else 0)
    -- the next lower position: skip the upper half of the block
    let j' := j0 + 1
    let j' := if j' &&& h == 0 then j' else j' + h
    if sub.get! a0 == 1 then
      levelAux src sub h N fuel j' m1 m2 ((ns.set! j0 p0).set! j1 p1)
        ((ni.set! p0 j0).set! p1 j1)
    else
      levelAux src sub h N fuel j' m1 (bset m2 j0) ((ns.set! j0 p1).set! j1 p0)
        ((ni.set! p1 j0).set! p0 j1)

/-- The middle layer (distance `1`): swap the pairs `(2q, 2q+1)` that are exchanged. -/
def middleAux (src : Array Nat) : Nat → ByteArray → ByteArray
  | 0, m => m
  | q + 1, m => middleAux src q (if src[2 * q]! == 2 * q + 1 then bset m (2 * q) else m)

/-- Beneš routing of a permutation `src` of `0 … 2^n - 1` (`1 ≤ n`): the masks of the
`2n - 1` layers, as bit-packed byte arrays, with their distances. -/
def benesMasks (n : Nat) (src : Array Nat) : Array (ByteArray × Nat) := Id.run do
  let N := 2 ^ n
  let empty := ByteArray.mk (Array.replicate ((N + 7) / 8) 0)
  let mut firsts : Array (ByteArray × Nat) := #[]
  let mut lasts : Array (ByteArray × Nat) := #[]
  let mut src := src
  let mut inv := invAux src N (Array.replicate N 0)
  for l in [0:n - 1] do
    let h := 2 ^ (n - 1 - l)
    let sub := loopAll src inv h N N (ByteArray.mk (Array.replicate N 0))
    let (m1, m2, ns, ni) :=
      levelAux src sub h N (N / 2) 0 empty empty (Array.replicate N 0) (Array.replicate N 0)
    firsts := firsts.push (m1, h)
    lasts := lasts.push (m2, h)
    src := ns
    inv := ni
  let mid := middleAux src (N / 2) empty
  return firsts.push (mid, 1) ++ lasts.reverse

/-- The Beneš network of a permutation `src` of `0 … 2^n - 1`, empty layers dropped. -/
def benesNet (n : Nat) (src : Array Nat) : Net :=
  (benesMasks n src).toList.filterMap fun (m, d) =>
    let m := natOfBytes m
    if m == 0 then none else some (m, d)

/-- Complete an injective partial map `pairs` (outputs `0 … pairs.size - 1`) into a permutation
of `0 … N - 1`: the free outputs get the free inputs in increasing order. -/
def completePerm (pairs : Array Nat) (N : Nat) : Array Nat := Id.run do
  let mut used := ByteArray.mk (Array.replicate N 0)
  for i in pairs do used := used.set! i 1
  let mut src := pairs
  for i in [0:N] do
    if used.get! i == 0 then src := src.push i
  return src

/-! ### The positions of the valid traces

The valid traces of ring size `r` are enumerated from the last position to the first (the
first entry is then determined by the sum), maintaining for the trace `t` and for its image
`τ12 t` the number of non-`Color1` entries, the block rank and the row code of the suffix
(`blockRank`, `xcode` are computed from the tail: a non-`Color1` entry at position `p` with
`c` non-`Color1` entries from `p` on adds `choose (r-1-p) c` to the block rank), and the
base-3 index of the prefix `t.take (r - 1)`.  Colors are encoded `Color1, Color2, Color3 ↦
1, 2, 3` (the sum of colors is the exclusive or). -/

/-- The update of (count, block rank, row code) when position `p` gets the color `c`. -/
@[inline] def posUpd (C : Array (Array Nat)) (r p c cnt br x : Nat) : Nat × Nat × Nat :=
  if c == 1 then (cnt, br, x)
  else (cnt + 1, br + C[r - 1 - p]![cnt + 1]!, 2 * x + (if c == 3 then 1 else 0))

/-- `Color1 ↔ Color2` on color codes. -/
@[inline] def tau12c (c : Nat) : Nat := if c == 1 then 2 else if c == 2 then 1 else c

/-- The enumeration: positions `p, p - 1, …, 1` still to choose (position `0` is determined);
the result `acc` holds `cpos (τ12 t)` at index `2 * cpos t` and `b3idx (t.take (r-1))` at
index `2 * cpos t + 1`. -/
def enumAux (r : Nat) (C : Array (Array Nat)) (goffs p3 : Array Nat) :
    Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Array Nat → Array Nat
  | 0, cnt, br, x, cnt', br', x', s, b3, acc =>
    if s == 0 then acc else
    let (cnt, br, x) := posUpd C r 0 s cnt br x
    let (cnt', br', x') := posUpd C r 0 (tau12c s) cnt' br' x'
    let b3 := b3 + (s - 1)
    let j := goffs[cnt / 2]! + x / 2 * C[r]![cnt]! + br
    let j' := goffs[cnt' / 2]! + x' / 2 * C[r]![cnt']! + br'
    (acc.set! (2 * j) j').set! (2 * j + 1) b3
  | p + 1, cnt, br, x, cnt', br', x', s, b3, acc =>
    let go (c : Nat) (acc : Array Nat) : Array Nat :=
      let (a, b, y) := posUpd C r (p + 1) c cnt br x
      let (a', b', y') := posUpd C r (p + 1) (tau12c c) cnt' br' x'
      let b3' := if p + 2 < r then b3 + (c - 1) * p3[p + 1]! else b3
      enumAux r C goffs p3 p a b y a' b' y' (s ^^^ c) b3' acc
    go 3 (go 2 (go 1 acc))

/-- The two permutations of ring size `r` (`2 ≤ r`), on the positions `0 … gtotal r - 1` of the
packed layout: `τ12` (`tau[cpos t] = cpos (τ12 t)`) and the conversion from the base-3 layout
of the prefixes (`cnv[cpos t] = b3idx (t.take (r - 1))`). -/
def layoutPerms (r : Nat) : Array Nat × Array Nat := Id.run do
  let C := (Array.range (r + 1)).map fun n => (Array.range (r + 2)).map fun k => chooseAux n k
  let goffs := (Array.range (ngrades r + 1)).map (goff r)
  let p3 := (Array.range r).map (3 ^ ·)
  let T := gtotal r
  let acc := enumAux r C goffs p3 (r - 1) 0 0 0 0 0 0 0 0 (Array.replicate (2 * T) 0)
  let mut tau := Array.emptyWithCapacity T
  let mut cnv := Array.emptyWithCapacity T
  for j in [0:T] do
    tau := tau.push acc[2 * j]!
    cnv := cnv.push acc[2 * j + 1]!
  return (tau, cnv)

/-- The networks `τ12` and base-3 conversion of ring size `r` (`2 ≤ r`). -/
def ringNets (r : Nat) : Net × Net :=
  let (tau, cnv) := layoutPerms r
  let T := gtotal r
  let nT := max 1 (bitLen (T - 1))
  let nC := max 1 (max (bitLen (3 ^ (r - 1) - 1)) (bitLen (T - 1)))
  (benesNet nT (completePerm tau (2 ^ nT)), benesNet nC (completePerm cnv (2 ^ nC)))

/-- The size in bytes of the masks of a network. -/
def netBytes (net : Net) : Nat := net.foldl (fun a (m, _) => a + (bitLen m + 7) / 8) 0

/-! ### `#engine_nets` -/

/-- The name `FourColor.Engine.<kind><r>` of a per-ring-size declaration. -/
def ringDeclName (kind : String) (r : Nat) : Name :=
  .str (.str (.str .anonymous "FourColor") "Engine") s!"{kind}{r}"

/-- Whether to log timings: option `engine.gen.verbose`, or the environment variable
`ENGINE_GEN_VERBOSE` (so that generated files can be measured without editing them). -/
def isVerbose (opts : Options) : IO Bool := do
  return engine.gen.verbose.get opts || (← IO.getEnv "ENGINE_GEN_VERBOSE").isSome

/-- Elapsed milliseconds since `t0` (for the verbose log). -/
def msSince (t0 : Nat) : IO Nat := return (← IO.monoMsNow) - t0

/-- `#engine_nets r`: route the networks of ring size `r`, define their chunked masks
`tauNetC<r>`, `cnvNetC<r>` and the networks `tauNet<r>`, `cnvNet<r>` assembled from them, and
prove by kernel evaluation the chunk checks `tauNetOK<r>`, `cnvNetOK<r>` and, one position per
declaration, the specifications `tauSpec<r>`, `cnvSpec<r>`. -/
elab "#engine_nets " n:num : command => do
  let r := n.getNat
  unless 2 ≤ r do throwError "#engine_nets: the ring size must be at least 2"
  let verbose ← isVerbose (← getOptions)
  let t0 ← IO.monoMsNow
  let (tau, cnv) := ringNets r
  let tauC := chunkNet chunkLog tau
  let cnvC := chunkNet chunkLog cnv
  -- force the (pure) computations here, for the timing; the chunk checks must hold
  let sz := netBytes tau + netBytes cnv
  unless netCOK chunkLog tauC && netCOK chunkLog cnvC do
    throwError "#engine_nets: a layer pairs bits of different chunks of {(2 ^ chunkLog : Nat)} bits"
  let tRoute ← msSince t0
  let sE := mkNatLit chunkLog
  let rE := mkNatLit r
  let netTy := mkConst ``Net
  let netCTy := mkConst ``NetC
  let mut times : Array String := #[]
  for (kind, netC) in [("tau", tauC), ("cnv", cnvC)] do
    let cN := ringDeclName s!"{kind}NetC" r
    let netN := ringDeclName s!"{kind}Net" r
    liftCoreM do
      addDataDef cN netCTy (mkNetCLit netC)
      addDataDef netN netTy (mkApp2 (mkConst ``netOfChunks) sE (mkConst cN))
    -- <kind>NetOK<r> : netCOK 16 <kind>NetC<r> = true
    let t ← IO.monoMsNow
    liftCoreM <| addThm (ringDeclName s!"{kind}NetOK" r)
      (mkEqTrue (mkApp2 (mkConst ``netCOK) sE (mkConst cN))) reflTrue
    times := times.push s!"{kind}NetOK{r} {← msSince t}"
  let tauN := ringDeclName "tauNet" r
  let cnvN := ringDeclName "cnvNet" r
  -- The specifications are checked in parts, one declaration per position (`NetSplit.lean`):
  -- in one declaration the ring-14 checks take 3.5 GB in Lean's kernel and 4.7 GB in con-ron.
  --   <kind>Layers<r> : <kind>Net<r>.all layerOK = true
  --   <kind>Part<r>_<p> : <kind>CheckAt r <kind>Net<r> p = true         (p < n)
  --   <kind>Spec<r> := <kind>Spec_of_check _ (<kind>Check_of_parts <kind>Layers<r>
  --                      (allFrom_cons <kind>Part<r>_0 (… (allFrom_nil _ n))))
  let natTy := mkConst ``Nat
  for (kind, netN, atN, ofPartsN, specN, specOfCheckN, minR, n) in
      [("tau", tauN, ``tauCheckAt, ``tauCheck_of_parts, ``TauSpec, ``tauSpec_of_check, 1, r),
       ("cnv", cnvN, ``cnvCheckAt, ``cnvCheck_of_parts, ``CnvSpec, ``cnvSpec_of_check, 2, r - 1)] do
    let t1 ← IO.monoMsNow
    let netE := mkConst netN
    let layersN := ringDeclName s!"{kind}Layers" r
    let allOK := mkApp3 (mkConst ``List.all [0]) (mkApp2 (mkConst ``Prod [0, 0]) natTy natTy) netE
      (mkConst ``layerOK)
    liftCoreM <| addThm layersN (mkEqTrue allOK) reflTrue
    let fE := mkApp2 (mkConst atN) rE netE
    for p in [0:n] do
      liftCoreM <| addThm (ringDeclName s!"{kind}Part{r}_" p)
        (mkEqTrue (mkApp fE (mkRawNatLit p))) reflTrue
    -- allFrom f p (n - p) from the parts p, p + 1, …
    let mut acc : Expr := mkApp2 (mkConst ``allFrom_nil) fE (mkRawNatLit n)
    for i in [0:n] do
      let p := n - 1 - i
      let partN := ringDeclName s!"{kind}Part{r}_" p
      acc := mkAppN (mkConst ``allFrom_cons)
        #[fE, mkRawNatLit p, mkRawNatLit i, mkConst partN, acc]
    let hr ← liftTermElabM do
      mkDecideProof (← mkAppM ``LE.le #[mkNatLit minR, rE])
    let check := mkAppN (mkConst ofPartsN) #[rE, netE, mkConst layersN, acc]
    liftCoreM <| addThm (ringDeclName s!"{kind}Spec" r) (mkApp2 (mkConst specN) rE netE)
      (mkApp4 (mkConst specOfCheckN) rE netE hr check)
    times := times.push s!"{kind}Spec{r} (in {n + 1} parts) {← msSince t1}"
  let nch (net : NetC) : Nat := net.foldl (fun a (ms, _) => a + ms.length) 0
  logInfo m!"ring {r}: {gtotal r} positions; tauNet{r}: {tau.length} layers, cnvNet{r}: \
    {cnv.length} layers; {sz} bytes of masks, in {nch tauC + nch cnvC} chunks of \
    {(2 ^ chunkLog : Nat)} bits"
  if verbose then
    logInfo m!"ring {r}: routing {tRoute} ms; kernel (ms): {" ".intercalate times.toList}"

/-! ### Checkpoints and their placement -/

/-- The checkpoint of a trace set: the low half (rows `xp < 2^(2k-2)`) of each grade `k ≥ 1`
(the high half is its `Color2 ↔ Color3` image, restored by `expand`). -/
def lowHalf (r : Nat) (X : List Nat) : List Nat :=
  mapGrades (fun k q => if k == 0 then q else
    q &&& (2 ^ (2 ^ (2 * k - 2) * chooseAux r (2 * k)) - 1)) X

/-- Measured kernel memory (MB) of one round in a checkpoint step, by ring size (slopes of the
peak memory of `#engine_certify` runs: ring 14 ≈ 450 MB per round, 13 ≈ 110, 12 ≈ 50; the
lower rings are extrapolated).  With the default budget of 1000 MB: 2 rounds per step at ring
14 (≈ 1.2 GB per process), 9 at ring 13 (≈ 1.1 GB), 20 at ring 12, and one step below. -/
def roundMB : Nat → Nat
  | 14 => 450
  | 13 => 110
  | 12 => 50
  | 11 => 15
  | 10 => 5
  | _ => 1

/-- The number of rounds per checkpoint step for ring size `r` and a kernel memory budget of
`budget` MB. -/
def roundsPerStep (r budget : Nat) : Nat := max 1 (budget / roundMB r)

/-- The number of rounds after which `#engine_certify` gives up. -/
def maxRounds : Nat := 1000

/-! ### `#engine_certify` -/

/-- Evaluate a closed term of type `ty` (compiled code; meta code only). -/
def evalClosed (α : Type) (ty e : Expr) : MetaM α := unsafe evalExpr α ty e

/-- Resolve an identifier to a constant (in the current scope). -/
def resolveConst? (id : Name) : CoreM (Option Name) := do
  let env ← getEnv
  if env.contains id then return some id
  return none

/-- Apply the constant `fn` to arguments given **by binder name** (implicit ones included),
the binders not in `args` being proved by `mkProof` from their (instantiated) type; returns
the application and its type. -/
def applyByName (fn : Name) (args : List (Name × Expr))
    (mkProof : Name → Expr → MetaM (Option Expr)) : MetaM (Expr × Expr) := do
  let ci ← getConstInfo fn
  unless ci.levelParams.isEmpty do throwError "{fn} has universe parameters"
  let mut ty := ci.type
  let mut val := mkConst fn
  repeat
    match ty with
    | .forallE n d b _ =>
      let a ← match args.lookup n with
        | some a => pure a
        | none =>
          match ← mkProof n d with
          | some a => pure a
          | none => throwError "#engine_certify: unexpected binder {n} : {d} of {fn}"
      val := mkApp val a
      ty := b.instantiate1 a
    | _ => break
  return (val, ty)

/-- The proofs of the small side conditions of `cfreducible_of_engine`: `hr` (an equation
checked by kernel evaluation) and `hr2` (by `decide`). -/
def sideProof (n : Name) (d : Expr) : MetaM (Option Expr) := do
  if n == `hr then
    match d.eq? with
    | some (α, _, rhs) => return some (mkApp2 (mkConst ``Eq.refl [1]) α rhs)
    | none => return none
  else if n == `hr2 then
    return some (← mkDecideProof d)
  else return none

/-- Syntax of `#engine_certify cfNNN` and `#engine_certify cfNNN (rounds := k)`. -/
syntax (name := engineCertify) "#engine_certify " ident
  (" (" &"rounds" " := " num ")")? : command

/-- `#engine_certify cfNNN`: compute and kernel-check the certificate of the configuration
`cfNNN` (see the module documentation). -/
@[command_elab engineCertify] def elabEngineCertify : CommandElab := fun stx => do
  let cfId := stx[1]
  let kOpt? : Option Nat :=
    if stx[2].getNumArgs > 0 then stx[2][3].isNatLit? else none
  let opts ← getOptions
  let verbose ← isVerbose opts
  let budget := engine.gen.memBudget.get opts
  let cfName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo cfId
  let base := cfId.getId.eraseMacroScopes.getString!
  let ns ← getCurrNamespace
  let dn (s : String) : Name := ns ++ Name.mkSimple s!"{base}_{s}"
  let some ctrName ← liftCoreM <| resolveConst? `FourColor.contractProg
    | throwError "#engine_certify: FourColor.contractProg not found (import FourColor.CfContract)"
  let cfE := mkConst cfName
  let cprogTy := mkConst ``Cprog
  let optCprogTy := mkApp (mkConst ``Option [0]) cprogTy
  -- the configuration program and the contract program (compiled code)
  let tStart ← IO.monoMsNow
  let (cp, cpc?) ← liftTermElabM do
    let cp ← evalClosed Cprog cprogTy (mkApp (mkConst ``Config.cfprog) cfE)
    let cpc? ← evalClosed (Option Cprog) optCprogTy (mkApp (mkConst ctrName) cfE)
    return (cp, cpc?)
  let some cpc := cpc? | throwError "#engine_certify: contractProg {cfName} = none"
  let r := cprsize cp
  unless 2 ≤ r do throwError "#engine_certify: ring size {r} < 2"
  unless cprsize cpc == r do
    throwError "#engine_certify: the contract program has ring size {cprsize cpc} ≠ {r}"
  let tauN := ringDeclName "tauNet" r
  let cnvN := ringDeclName "cnvNet" r
  let tauSpecN := ringDeclName "tauSpec" r
  let cnvSpecN := ringDeclName "cnvSpec" r
  let tauCN := ringDeclName "tauNetC" r
  let cnvCN := ringDeclName "cnvNetC" r
  let tauOKN := ringDeclName "tauNetOK" r
  let cnvOKN := ringDeclName "cnvNetOK" r
  for nm in [tauSpecN, cnvSpecN, tauOKN, cnvOKN] do
    unless (← getEnv).contains nm do
      throwError "#engine_certify: {nm} not found (import FourColor.Reducibility.Nets{r})"
  let tau ← liftCoreM <| netOfConst tauN
  let cnv ← liftCoreM <| netOfConst cnvN
  -- native run: coloring DP, rounds until the contract traces are covered
  let k := kOpt?.getD (roundsPerStep r budget)
  unless 0 < k do throwError "#engine_certify: rounds per step must be positive"
  let P := dpP1 r cnv cp
  let C := dpP1 r cnv cpc
  let mut X := P
  let mut n := 0
  let mut ckpts : Array (List Nat) := #[lowHalf r P]
  let mut steps : Array Nat := #[]
  let mut last := 0
  while !covered C X do
    if n ≥ maxRounds then
      throwError "#engine_certify: contract traces not covered after {maxRounds} rounds"
    X := round r tau X
    n := n + 1
    if n - last == k then
      ckpts := ckpts.push (lowHalf r X)
      steps := steps.push k
      last := n
  if n != last then
    ckpts := ckpts.push (lowHalf r X)
    steps := steps.push (n - last)
  -- sanity: the checkpoints expand to the computed sets (all of them are `τ23`-closed)
  unless expand r ckpts[0]! == P do
    throwError "#engine_certify: the coloring traces are not Color2/Color3-symmetric"
  if n > 0 then
    unless expand r ckpts.back! == X do
      throwError "#engine_certify: the last round output is not Color2/Color3-symmetric"
  let tNative ← msSince tStart
  -- declarations
  let rE := mkNatLit r
  let tauE := mkConst tauN
  let cnvE := mkConst cnvN
  let cpcN := dn "cpc"
  let cpcE := mkConst cpcN
  let natListTy := mkApp (mkConst ``List [0]) (mkConst ``Nat)
  let hN (i : Nat) : Name := dn s!"H{i}"
  let expandH (i : Nat) : Expr := mkApp2 (mkConst ``expand) rE (mkConst (hN i))
  let nsteps := steps.size
  let mut times : Array String := #[]
  liftCoreM <| addDataDef cpcN cprogTy (mkCprogLit cpc)
  -- cfNNN_ctr : contractProg cfNNN = some cfNNN_cpc
  let someCpc := mkApp2 (mkConst ``Option.some [0]) cprogTy cpcE
  let t ← IO.monoMsNow
  liftCoreM <| addThm (dn "ctr")
    (mkApp3 (mkConst ``Eq [1]) optCprogTy (mkApp (mkConst ctrName) cfE) someCpc)
    (mkApp2 (mkConst ``Eq.refl [1]) optCprogTy someCpc)
  times := times.push s!"ctr {← msSince t}"
  -- cfNNN_rc : cprsize cfNNN_cpc = r
  liftCoreM <| addThm (dn "rc")
    (mkApp3 (mkConst ``Eq [1]) (mkConst ``Nat) (mkApp (mkConst ``cprsize) cpcE) rE)
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) rE)
  -- checkpoints
  let mut ckBytes : Nat := 0
  for i in [0:ckpts.size] do
    let H := ckpts[i]!
    ckBytes := ckBytes + H.foldl (fun a h => a + (bitLen h + 7) / 8) 0
    liftCoreM <| addDataDef (hN i) natListTy (mkNatListLit H)
  -- The kernel-heavy checks are proved through their chunked versions (`CheckChunk.lean`):
  -- `(eq : lhs = rhs).trans (Eq.refl true : rhs = true)`, the kernel evaluating `rhs`.
  let sE := mkNatLit chunkLog
  let dpHE := mkNatLit dpChunkDigits
  let tauCE := mkConst tauCN
  let cnvCE := mkConst cnvCN
  let viaChunks (lhs rhs eq : Expr) : Expr :=
    mkAppN (mkConst ``Eq.trans [1]) #[mkConst ``Bool, lhs, rhs, mkConst ``true, eq, reflTrue]
  -- cfNNN_init : checkInit r cnvNet<r> cfNNN.cfprog cfNNN_H0 = true
  let cfprogE := mkApp (mkConst ``Config.cfprog) cfE
  let initLhs := mkApp4 (mkConst ``checkInit) rE cnvE cfprogE (mkConst (hN 0))
  let t ← IO.monoMsNow
  liftCoreM <| addThm (dn "init") (mkEqTrue initLhs)
    (viaChunks initLhs
      (mkAppN (mkConst ``checkInitB) #[rE, sE, dpHE, cnvCE, cfprogE, mkConst (hN 0)])
      (mkAppN (mkConst ``checkInit_eq_checkInitB)
        #[sE, cnvCE, mkConst cnvOKN, rE, dpHE, cfprogE, mkConst (hN 0)]))
  times := times.push s!"init {← msSince t}"
  -- cfNNN_step<i> : checkStep r tauNet<r> k cfNNN_H<i> cfNNN_H<i+1> = true
  for i in [0:nsteps] do
    let kE := mkNatLit steps[i]!
    let Hi := mkConst (hN i)
    let Hi' := mkConst (hN (i + 1))
    let stepLhs := mkApp5 (mkConst ``checkStep) rE tauE kE Hi Hi'
    let t ← IO.monoMsNow
    liftCoreM <| addThm (dn s!"step{i}") (mkEqTrue stepLhs)
      (viaChunks stepLhs (mkAppN (mkConst ``checkStepB) #[rE, sE, tauCE, kE, Hi, Hi'])
        (mkAppN (mkConst ``checkStep_eq_checkStepB) #[sE, tauCE, mkConst tauOKN, rE, kE, Hi, Hi']))
    times := times.push s!"step{i} {← msSince t}"
  -- cfNNN_final : checkFinal r cnvNet<r> cfNNN_cpc cfNNN_H<n> = true
  let Hn := mkConst (hN nsteps)
  let finalLhs := mkApp4 (mkConst ``checkFinal) rE cnvE cpcE Hn
  let t ← IO.monoMsNow
  liftCoreM <| addThm (dn "final") (mkEqTrue finalLhs)
    (viaChunks finalLhs (mkAppN (mkConst ``checkFinalB) #[rE, sE, dpHE, cnvCE, cpcE, Hn])
      (mkAppN (mkConst ``checkFinal_eq_checkFinalB)
        #[sE, cnvCE, mkConst cnvOKN, rE, dpHE, cpcE, Hn]))
  times := times.push s!"final {← msSince t}"
  -- cfNNN_reach : ReachN r tauNet<r> (expand r cfNNN_H0) (expand r cfNNN_H<n>)
  let reachTy (i j : Nat) : Expr := mkApp4 (mkConst ``ReachN) rE tauE (expandH i) (expandH j)
  let mut reach : Expr := mkApp3 (mkConst ``ReachN.refl) rE tauE (expandH nsteps)
  if nsteps > 0 then
    let stepPf (i : Nat) : Expr :=
      mkApp6 (mkConst ``reachN_of_checkStep) rE tauE (mkNatLit steps[i]!) (mkConst (hN i))
        (mkConst (hN (i + 1))) (mkConst (dn s!"step{i}"))
    reach := stepPf (nsteps - 1)
    for i' in [0:nsteps - 1] do
      let i := nsteps - 2 - i'
      reach := mkAppN (mkConst ``ReachN.trans)
        #[rE, tauE, expandH i, expandH (i + 1), expandH nsteps, stepPf i, reach]
  liftCoreM <| addThm (dn "reach") (reachTy 0 nsteps) reach
  -- cfNNN_reducible, if `cfreducible_of_engine` is available
  let engN? ← liftCoreM do
    match ← (observing (realizeGlobalConstNoOverload (mkIdent `cfreducible_of_engine))) with
    | .ok n => pure (some n)
    | .error _ => resolveConst? `FourColor.cfreducible_of_engine
  match engN? with
  | none =>
    logWarning m!"#engine_certify: cfreducible_of_engine not found; {dn "reducible"} not added"
  | some engN =>
    let (val, ty) ← liftTermElabM <| applyByName engN
      [(`cf, cfE), (`r, rE), (`tau, tauE), (`cnv, cnvE), (`htau, mkConst tauSpecN),
       (`hcnv, mkConst cnvSpecN), (`cpc, cpcE), (`hctr, mkConst (dn "ctr")),
       (`hrc, mkConst (dn "rc")), (`H0, mkConst (hN 0)), (`Hn, mkConst (hN nsteps)),
       (`hinit, mkConst (dn "init")), (`hreach, mkConst (dn "reach")),
       (`hfinal, mkConst (dn "final"))] sideProof
    let t ← IO.monoMsNow
    liftCoreM <| addThm (dn "reducible") ty val
    times := times.push s!"reducible {← msSince t}"
  logInfo m!"{cfName}: ring {r}, {n} rounds, {nsteps} checkpoint steps of ≤ {k} rounds, \
    {ckpts.size} checkpoints ({ckBytes} bytes)"
  if verbose then
    logInfo m!"{cfName}: native {tNative} ms; kernel (ms): {" ".intercalate times.toList}"

/-! ### Development commands -/

/-- Hex digit value. -/
def hexVal (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else c.toNat - 'A'.toNat + 10

/-- Parse hex digits `s[lo:hi]` (most significant first), divide and conquer (`fuel` bounds
the recursion depth; `64` is plenty). -/
def hexNatF (s : Array Char) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, lo, hi =>
    if hi - lo ≤ 16 then Id.run do
      let mut v := 0
      for i in [lo:hi] do v := v * 16 + hexVal s[i]!
      return v
    else
      let mid := (lo + hi) / 2
      (hexNatF s fuel lo mid <<< (4 * (hi - mid))) ||| hexNatF s fuel mid hi

/-- Parse hex digits `s[lo:hi]`. -/
def hexNat (s : Array Char) (lo hi : Nat) : Nat := hexNatF s 64 lo hi

/-- Parse all `(0x<hex>, <dec>)` pairs of a text. -/
def parsePairs (txt : String) : Array (Nat × Nat) := Id.run do
  let cs := txt.toList.toArray
  let n := cs.size
  let mut out := #[]
  let mut i := 0
  while i < n do
    if cs[i]! == '(' && i + 1 < n && cs[i+1]!.isDigit then
      let mut j := i + 1
      let mut a := 0
      if j + 1 < n && cs[j]! == '0' && cs[j+1]! == 'x' then
        let st := j + 2
        let mut e := st
        while e < n && (cs[e]!.isDigit || ('a' ≤ cs[e]! && cs[e]! ≤ 'f')) do e := e + 1
        a := hexNat cs st e
        j := e
      else
        while j < n && cs[j]!.isDigit do
          a := a * 10 + (cs[j]!.toNat - '0'.toNat); j := j + 1
      while j < n && (cs[j]! == ',' || cs[j]! == ' ') do j := j + 1
      let mut b := 0
      while j < n && cs[j]!.isDigit do
        b := b * 10 + (cs[j]!.toNat - '0'.toNat); j := j + 1
      out := out.push (a, b)
      i := j
    else
      i := i + 1
  return out

/-- `#engine_load_net name "file"`: a network from a text file (development tool). -/
elab "#engine_load_net " id:ident path:str : command => do
  let txt ← IO.FS.readFile path.getString
  let ps := parsePairs txt
  let nat := mkConst ``Nat
  let ty := mkApp (mkConst ``List [0]) (mkApp2 (mkConst ``Prod [0, 0]) nat nat)
  let name := (← getCurrNamespace) ++ id.getId
  liftCoreM <| addLitDef name ty (mkNetLit ps.toList)
  logInfo m!"defined {name}: {ps.size} layers"

/-- `#engine_def_natlist name := term`: evaluate `term : List Nat` and define `name` as its
literal value. -/
elab "#engine_def_natlist " id:ident " := " t:term : command => do
  let v ← liftTermElabM do
    let e ← Term.elabTermEnsuringType t (mkApp (mkConst ``List [0]) (mkConst ``Nat))
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    evalClosed (List Nat) (mkApp (mkConst ``List [0]) (mkConst ``Nat)) e
  let name := (← getCurrNamespace) ++ id.getId
  liftCoreM <| addLitDef name (mkApp (mkConst ``List [0]) (mkConst ``Nat)) (mkNatListLit v)
  logInfo m!"defined {name}: {v.length} numbers, {v.foldl (fun a n => a + n.log2 + 1) 0} bits"

/-- `#engine_def_net name := term`: evaluate a network and define `name` as its literal
value. -/
elab "#engine_def_net " id:ident " := " t:term : command => do
  let nat := mkConst ``Nat
  let ty := mkApp (mkConst ``List [0]) (mkApp2 (mkConst ``Prod [0, 0]) nat nat)
  let v ← liftTermElabM do
    let e ← Term.elabTermEnsuringType t ty
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    evalClosed (List (Nat × Nat)) ty e
  let name := (← getCurrNamespace) ++ id.getId
  liftCoreM <| addLitDef name ty (mkNetLit v)
  logInfo m!"defined {name}: {v.length} layers"

end FourColor.Engine.Gen
