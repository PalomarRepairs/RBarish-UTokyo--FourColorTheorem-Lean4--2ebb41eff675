/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Birkhoff

/-!
# Contract colorings of valid contracts (port of `contract.v`)

The proof that there exists a contract coloring for any valid contract. We will show in
`embed.v` that contract validity is lifted by the embedding, except for the ring condition,
which becomes moot. For `G : Hypermap D` and `cc r : List D`:

* `G.ContractRing cc r` : `r` is a proper ring (a simple R-cycle, `G.ProperRing r`) that is
  contracted to its first dart by applying the contract `cc`, i.e., the rest of `r` is in the
  edge closure `G.insertE cc` of `cc` (math-comp `contract_ring cc r`).

We show that valid contracts have no contract rings in a minimal counter-example
(`cexG : G.MinimalCounterExample`), using the Birkhoff theorem, sparsity, and triads for ring
size 5 / contract size 4:

* `sparse_contract_ring` : a contract ring of a sparse contract is nontrivial;
* `contract_ring_max`    : a contract ring has at most `cc.length + 1` darts;
* `contract3_valid`      : a sparse contract of size at most 3 has no contract ring;
* `triad_valid`          : a sparse contract of size 4 with a triad has no contract ring;
* `contract_coloring`    : a valid contract has a contract coloring (`G.CcColorable cc`), by
  induction on the size of the contract: removing the edge `{x, edge x}` of a contract dart `x`
  with two Walkup transforms (`WalkupF x`, then `WalkupF (edge x)`) yields a smaller planar
  bridgeless plain precubic map, colorable by minimality of `G`.

## Coq → Lean names

| Coq | Lean |
|---|---|
| `contract_ring` | `Hypermap.ContractRing` (a structure; fields `scycle`, `proper`, `sub`) |
| section `ContractLemmas`, hypothesis `cexG : minimal_counter_example G` | explicit argument `cexG : G.MinimalCounterExample` |
| section `Let`s `planarG`, `bridge'G`, `plainG`, `cubicG`, `pentaG`, `ccG`, `noncolG`, `minG`, `ee`, `e'id`, `nnn`, `geoG` | inlined in the proofs: `cexG.planar`, `G.bridgeless_cface cexG.bridgeless`, `cexG.plain`, `cexG.cubic`, `G.min_arity cexG`, `cexG.connected`, `cexG.noncolorable`, `cexG.minimal`, `G.plain_eq`, `G.plain_neq`, `G.cubic_eq`, `cexG.toPlanarBridgelessPlainConnected` |
| `sparse_contract_ring` | `Hypermap.sparse_contract_ring` |
| `contract_ring_max` | `Hypermap.contract_ring_max` |
| `contract3_valid` | `Hypermap.contract3_valid` |
| `triad_valid` | `Hypermap.triad_valid` |
| `contract_coloring` | `Hypermap.contract_coloring` (induction: private `contract_coloring_aux`, step: private `contract_coloring_step`) |
| math-comp `mem_next`, `next_map`, `next_cycle`, `cycle_from_next`, `next_rot`, `rot_to` (`path.v`, `seq.v`) | private helpers `mem_next`, `next_map`, `next_cycle`, `cycle_from_next`, `next_rot`, `rotate_to` (as in `FourColor.Birkhoff.Spoke`) |

## Porting notes

* `contract_ring` (math-comp `[/\ scycle rlink r, proper_ring r & {subset behead r <=
  insertE cc}]`) is a `Prop`-valued structure; `behead` is `List.tail`. `sparse`, `triad`,
  `nontrivial_ring`, `proper_ring`, `valid_contract` and `cc_colorable` are the `Prop`s
  `Sparse`, `Triad`, `NontrivialRing`, `ProperRing`, `ValidContract` and `CcColorable` of
  `FourColor.Coloring` and `FourColor.Revsnip`.
* As in Coq (`Set Implicit Arguments`), the contract, the ring and the triad dart are implicit
  when a hypothesis determines them; the ring `p` of the conclusions `∀ p, ¬ contract_ring cc p`
  is explicit.
* The proof of `contract_coloring` generalizes over the hypermap, as in Coq; its induction is
  the private `contract_coloring_aux`, over the hypermaps whose dart types live in the universe
  of `D` (the universe of `MinimalCounterExample.minimal`). The Coq bound
  `#|G0| < (0 < size cc) + #|G|` is split into `card ≤ #|G|` and `cc = [] → card < #|G|`.
* Proof-level differences: in `sparse_contract_ring` the rotation computations of the Coq proof
  (`rot_to_arc`, `arc_rot`, and `last p = node x`) are replaced by the helper `arc_props` and
  by `next p (node x) = x`, and the final sparseness argument uses `List.inj_on_of_nodup_map`
  instead of an induction on `cc`; in `contract_ring_max` the dart `odflt x (pick (df x))` of
  `cc` is `if x ∈ cc then x else edge x`; in `contract_coloring` the non-R-link of `map h p` is
  found with `next` and `cycle_from_next` (Coq: `prev`, `cycle_from_prev`), and the lifted
  coloring chooses its dart with `Classical.choose` (Coq: `pick`).
-/

namespace FourColor

open Function

universe u

/-! ### Cyclic successor, rotations and arcs (private helpers) -/

section NextPrev

variable {α β : Type*} [DecidableEq α]

/-- math-comp `next_nth` (default case): `next` fixes the points outside the sequence. -/
private theorem next_of_not_mem {p : List α} {x : α} (h : x ∉ p) : next p x = x := by
  cases p with
  | nil => rfl
  | cons y p => exact nextAt_of_not_mem h

/-- `next_at` agrees with Mathlib's `List.nextOr` on the items of the sequence. -/
private theorem nextAt_eq_nextOr {x y0 : α} :
    ∀ {y : α} {p : List α}, x ∈ y :: p → nextAt x y0 y p = List.nextOr (y :: p) x y0
  | y, [], h => by
    rw [List.mem_singleton] at h
    subst h
    simp [nextAt, List.nextOr]
  | y, z :: p, h => by
    by_cases hxy : x = y
    · subst hxy
      simp [nextAt, List.nextOr]
    · have h' : x ∈ z :: p := (List.mem_cons.1 h).resolve_left hxy
      rw [nextAt, ite_eq_right hxy, nextAt_eq_nextOr h', List.nextOr_cons_of_ne _ _ _ _ hxy]

/-- The total `next` agrees with Mathlib's `List.next` on the items of the sequence. -/
private theorem next_eq_listNext {p : List α} {x : α} (hx : x ∈ p) :
    next p x = p.next x hx := by
  cases p with
  | nil => simp at hx
  | cons y p =>
    show nextAt x y y p = _
    rw [nextAt_eq_nextOr hx]
    rfl

/-- math-comp `mem_next`. -/
private theorem mem_next {p : List α} {x : α} : next p x ∈ p ↔ x ∈ p := by
  by_cases hx : x ∈ p
  · rw [next_eq_listNext hx]
    exact ⟨fun _ => hx, fun _ => List.next_mem _ _ _⟩
  · rw [next_of_not_mem hx]

/-- Helper for math-comp `next_map`. -/
private theorem nextAt_map [DecidableEq β] {f : α → β} (hf : Injective f) (x y0 : α) :
    ∀ (y : α) (p : List α), nextAt (f x) (f y0) (f y) (p.map f) = f (nextAt x y0 y p)
  | y, [] => by
    simp only [List.map_nil, nextAt, hf.eq_iff]
    split_ifs <;> rfl
  | y, z :: p => by
    simp only [List.map_cons, nextAt, hf.eq_iff]
    split_ifs
    · rfl
    · exact nextAt_map hf x y0 z p

/-- math-comp `next_map`. -/
private theorem next_map [DecidableEq β] {f : α → β} (hf : Injective f) (p : List α)
    (x : α) : next (p.map f) (f x) = f (next p x) := by
  cases p with
  | nil => rfl
  | cons y p => exact nextAt_map hf x y y p

/-- Helper for math-comp `next_cycle`. -/
private theorem nextAt_cycle {e : α → α → Prop} {x y0 : α} :
    ∀ {y : α} {p : List α}, path e y (p ++ [y0]) → x ∈ y :: p → e x (nextAt x y0 y p)
  | y, [], hp, hx => by
    rw [List.mem_singleton] at hx
    subst hx
    rw [nextAt, ite_eq_left rfl]
    exact hp.1
  | y, z :: p, hp, hx => by
    rw [nextAt]
    by_cases hxy : x = y
    · rw [ite_eq_left hxy]
      subst hxy
      exact hp.1
    · rw [ite_eq_right hxy]
      exact nextAt_cycle hp.2 ((List.mem_cons.1 hx).resolve_left hxy)

/-- math-comp `next_cycle`. -/
private theorem next_cycle {e : α → α → Prop} {p : List α} (hp : cycle e p) {x : α}
    (hx : x ∈ p) : e x (next p x) := by
  cases p with
  | nil => simp at hx
  | cons y p => exact nextAt_cycle hp hx

/-- Helper for math-comp `cycle_from_next`. -/
private theorem path_from_nextAt {e : α → α → Prop} {y0 : α} :
    ∀ {y : α} {p : List α}, (y :: p).Nodup → (∀ x ∈ y :: p, e x (nextAt x y0 y p)) →
      path e y (p ++ [y0])
  | y, [], _, h => by
    have := h y List.mem_cons_self
    rw [nextAt, ite_eq_left rfl] at this
    exact ⟨this, trivial⟩
  | y, z :: p, hn, h => by
    have hy := h y List.mem_cons_self
    rw [nextAt, ite_eq_left rfl] at hy
    refine ⟨hy, path_from_nextAt (List.nodup_cons.1 hn).2 fun x hx => ?_⟩
    have hxy : x ≠ y := by
      rintro rfl
      exact (List.nodup_cons.1 hn).1 hx
    have := h x (List.mem_cons_of_mem _ hx)
    rwa [nextAt, ite_eq_right hxy] at this

/-- math-comp `cycle_from_next`. -/
private theorem cycle_from_next {e : α → α → Prop} {p : List α} (hp : p.Nodup)
    (h : ∀ x ∈ p, e x (next p x)) : cycle e p := by
  cases p with
  | nil => trivial
  | cons y p => exact path_from_nextAt hp h

/-- `next` is invariant under the math-comp rotations `rot` (math-comp `next_rot`). -/
private theorem next_rot {p : List α} (hp : p.Nodup) (i : ℕ) (x : α) :
    next (rot i p) x = next p x := by
  rcases le_or_gt i p.length with h | h
  · rw [rot_eq_rotate h, next_rotate hp]
  · rw [rot_oversize h.le]

omit [DecidableEq α] in
/-- Any item of a sequence can be rotated to its head (math-comp `rot_to`, for
`List.rotate`). -/
private theorem rotate_to {p : List α} {x : α} (h : x ∈ p) : ∃ i s, p.rotate i = x :: s := by
  obtain ⟨u, v, rfl⟩ := List.append_of_mem h
  exact ⟨u.length, v ++ u, by rw [List.rotate_append_length_eq, List.cons_append]⟩

/-- The arc `arc p j x` of a duplicate-free cyclic sequence `p`, from `j` to `x` (excluded),
does not contain `x`, is included in `p`, and, if the successor of `x` in `p` is not `j`, it
does not contain that successor and is shorter than `p` by at least two items. -/
private theorem arc_props {p : List α} (hp : p.Nodup) {x j : α} (hx : x ∈ p) (hj : j ∈ p)
    (hxj : x ≠ j) :
    x ∉ arc p j x ∧ (∀ y ∈ arc p j x, y ∈ p) ∧
      (next p x ≠ j → next p x ∉ arc p j x ∧ (arc p j x).length + 2 ≤ p.length) := by
  obtain ⟨i, p1, p2, -, h2, hrot⟩ := rot_to_arc hp hx hj hxj
  rw [← h2]
  have hn : (x :: p1 ++ j :: p2).Nodup := hrot ▸ nodup_rot.2 hp
  have hlen : (x :: p1 ++ j :: p2).length = p.length := by rw [← hrot, length_rot]
  have hnext : next p x = next (x :: p1 ++ j :: p2) x := by rw [← hrot, next_rot hp]
  refine ⟨?_, fun y hy => ?_, fun hne => ?_⟩
  · intro h
    rw [List.cons_append, List.nodup_cons] at hn
    exact hn.1 (List.mem_append_right _ h)
  · have : y ∈ rot i p := by rw [hrot]; exact List.mem_append_right _ hy
    exact mem_rot.1 this
  · cases p1 with
    | nil =>
      exfalso
      apply hne
      rw [hnext]
      simp [next, nextAt]
    | cons y p1 =>
      have hy : next p x = y := by
        rw [hnext]
        simp [next, nextAt]
      rw [hy]
      refine ⟨fun h => ?_, ?_⟩
      · rw [List.cons_append, List.nodup_cons, List.cons_append, List.nodup_cons] at hn
        exact hn.2.1 (List.mem_append_right _ h)
      · simp only [List.cons_append, List.length_cons, List.length_append] at hlen
        simp only [List.length_cons]
        omega

end NextPrev

namespace Hypermap

/-- math-comp `contract_ring cc r`: `r` is a proper ring (a simple R-cycle that is not an
E-path of size 2) that is contracted to its first dart by applying the contract `cc`, i.e., the
rest of `r` is in the edge closure `insertE cc` of `cc`
(`[/\ scycle rlink r, proper_ring r & {subset behead r <= insertE cc}]`). -/
structure ContractRing {D : Type u} (G : Hypermap D) (cc r : List D) : Prop where
  /-- `r` is a simple R-cycle. -/
  scycle : G.SCycle G.rlink r
  /-- `r` is a proper ring. -/
  proper : G.ProperRing r
  /-- The darts of `r` after the first are in `insertE cc`. -/
  sub : ∀ x ∈ r.tail, x ∈ G.insertE cc

/-- A proper ring has at least two darts. -/
private theorem two_le_length_of_proper {D : Type u} {G : Hypermap D} :
    ∀ {r : List D}, G.ProperRing r → 2 ≤ r.length
  | [], h => False.elim h
  | [_], h => False.elim h
  | _ :: _ :: _, _ => by simp

section ContractLemmas

variable {D : Type u} [Fintype D] [DecidableEq D] {G : Hypermap D}

/-- math-comp `sparse_contract_ring`: in a minimal counter-example, a contract ring of a
sparse contract is nontrivial. -/
theorem sparse_contract_ring (cexG : G.MinimalCounterExample) {cc : List D}
    (cc_sparse : G.Sparse (G.insertE cc)) {p : List D} (cc_p : G.ContractRing cc p) :
    G.NontrivialRing 0 p := by
  have hG := cexG.toPlanarBridgelessPlainConnected
  have hpl := cexG.plain
  have hbr := cexG.bridgeless
  have hcub := cexG.cubic
  have ee := G.plain_eq hpl
  -- `face (edge (node y)) = y`
  have enF : ∀ y, G.cface (G.edge (G.node y)) y := fun y => by
    have := fconnect1 G.face (G.edge (G.node y))
    rwa [G.nodeK] at this
  -- The main claim: the inner disk of a contract ring has a face.
  have dF_cc : ∀ n (q : List D), q.length < n → G.ContractRing cc q →
      ∃ y, y ∈ G.diskF q := by
    intro n
    induction n with
    | zero => intro q hq; omega
    | succ n IHn =>
      intro q hq cc_q
      by_contra dF0
      push Not at dF0
      obtain ⟨URq, nt_q, sub_q⟩ := cc_q
      have Uq := G.scycle_uniq URq
      obtain ⟨x, x1, q0, hqx⟩ : ∃ x x1 q0, q = x :: x1 :: q0 := by
        match q, nt_q with
        | [], h => exact False.elim h
        | [_], h => exact False.elim h
        | x :: x1 :: q0, _ => exact ⟨x, x1, q0, rfl⟩
      have q_x : x ∈ q := by rw [hqx]; exact List.mem_cons_self
      have dNx : x ∈ G.diskN q := G.mem_diskN_of_mem q q_x
      have dN_node : ∀ z, z ∈ G.diskN q → G.node z ∈ G.diskN q := fun z hz =>
        ((G.diskN_node q) z (G.node z) rfl).1 hz
      have qF_of_dN : ∀ z, z ∈ G.diskN q → z ∈ G.fband q := fun z hz => by
        by_contra h
        exact dF0 z ⟨hz, h⟩
      have dNnx := dN_node _ dNx
      have dNnnx := dN_node _ dNnx
      have qFnx := qF_of_dN _ dNnx
      have qFnnx := qF_of_dN _ dNnnx
      have tail_of : ∀ y, y ∈ q → y ≠ x → y ∈ q.tail := by
        intro y hy hyx
        rw [hqx] at hy ⊢
        exact (List.mem_cons.1 hy).resolve_left hyx
      -- A chord `c` of `q` whose chord ring is shorter than `q` and avoids `x` yields a
      -- smaller contract ring with an empty inner disk.
      have chord : ∀ c, c ∈ G.diskE q → c ∈ G.fband q → G.edge c ∈ G.fband q →
          next q (G.fproj q c) ≠ G.fproj q (G.edge c) →
          x ∉ arc q (G.fproj q (G.edge c)) (G.fproj q c) → False := by
        intro c dEc qFc qFec hne hx
        obtain ⟨q_jc, cFj⟩ := G.fprojP qFc
        obtain ⟨q_jec, ecFj⟩ := G.fprojP qFec
        have hj : G.fproj q c ≠ G.fproj q (G.edge c) := by
          intro h
          refine G.bridgeless_cface hbr c (connect_trans cFj ?_)
          rw [h]
          exact G.cfaceC.1 ecFj
        obtain ⟨-, hsub, hlen⟩ := arc_props Uq q_jc q_jec hj
        have hlen := (hlen hne).2
        have cr_def : G.chordRing q c = c :: arc q (G.fproj q (G.edge c)) (G.fproj q c) := rfl
        have cc_cr : G.ContractRing cc (G.chordRing q c) := by
          refine ⟨G.scycle_chord_ring hG URq qFc qFec, G.proper_chord_ring hG URq dEc qFc qFec,
            fun y hy => ?_⟩
          rw [cr_def, List.tail_cons] at hy
          exact sub_q y (tail_of y (hsub y hy) (fun e => hx (e ▸ hy)))
        have lt_cr : (G.chordRing q c).length < n := by
          rw [cr_def, List.length_cons]
          omega
        obtain ⟨y, hy⟩ := IHn _ lt_cr cc_cr
        rw [G.diskF_chord_ring hG URq nt_q dEc qFc qFec] at hy
        exact dF0 y hy.1
      -- `node x` is on `q`.
      have q_nx : G.node x ∈ q := by
        by_contra q'nx
        have dEnx : G.node x ∈ G.diskE q := ⟨dNnx, q'nx⟩
        have dEenx : G.edge (G.node x) ∈ G.diskE q :=
          ((G.diskE_edge hG.planar URq) _ _ rfl).1 dEnx
        have qFenx : G.edge (G.node x) ∈ G.fband q := ⟨x, q_x, enF x⟩
        have qFeenx : G.edge (G.edge (G.node x)) ∈ G.fband q := by
          rw [ee]
          exact qFnx
        have Djenx : G.fproj q (G.edge (G.node x)) = x := by
          obtain ⟨h1, h2⟩ := G.fprojP qFenx
          exact G.scycle_cface URq _ h1 _ q_x (connect_trans (G.cfaceC.1 h2) (enF x))
        obtain ⟨q_j, nxFj⟩ := G.fprojP qFnx
        have j'x : x ≠ G.fproj q (G.node x) := by
          intro h
          have h1 := nxFj
          rw [← h] at h1
          exact G.bridgeless_cface hbr (G.node x) (connect_trans h1 (G.cfaceC.1 (enF x)))
        have j'x1 : next q x ≠ G.fproj q (G.node x) := by
          have hnx : next q x = x1 := by
            rw [hqx]
            simp [next, nextAt]
          rw [hnx]
          intro h
          have h1 := nxFj
          rw [← h] at h1
          have xRx1 : G.cface (G.edge x) x1 := by
            have := URq.1
            rw [hqx] at this
            exact this.1
          have h2 : G.cface (G.edge x) (G.node x) := connect_trans xRx1 (G.cfaceC.1 h1)
          apply G.bridgeless_cface hbr (G.face (G.edge x))
          rw [← G.cface1, ← G.cubic_eq' hcub]
          exact (G.cface1r _ _).2 (by rw [G.nodeK]; exact h2)
        apply chord (G.edge (G.node x)) dEenx qFenx qFeenx
        · rw [Djenx, ee]
          exact j'x1
        · rw [Djenx, ee]
          exact (arc_props Uq q_x q_j j'x).1
      -- `next q (node x) = x`
      have next_nx : next q (G.node x) = x := by
        have h1 : G.rlink (G.node x) (next q (G.node x)) := next_cycle URq.1 q_nx
        have h2 : next q (G.node x) ∈ q := mem_next.2 q_nx
        exact G.scycle_cface URq _ h2 _ q_x (connect_trans (G.cfaceC.1 h1) (enF x))
      -- `node (node x)` is on `q`.
      have q_nnx : G.node (G.node x) ∈ q := by
        by_contra q'nnx
        have dEnnx : G.node (G.node x) ∈ G.diskE q := ⟨dNnnx, q'nnx⟩
        have dEennx : G.edge (G.node (G.node x)) ∈ G.diskE q :=
          ((G.diskE_edge hG.planar URq) _ _ rfl).1 dEnnx
        have qFennx : G.edge (G.node (G.node x)) ∈ G.fband q := ⟨G.node x, q_nx, enF _⟩
        have qFeennx : G.edge (G.edge (G.node (G.node x))) ∈ G.fband q := by
          rw [ee]
          exact qFnnx
        have Djennx : G.fproj q (G.edge (G.node (G.node x))) = G.node x := by
          obtain ⟨h1, h2⟩ := G.fprojP qFennx
          exact G.scycle_cface URq _ h1 _ q_nx (connect_trans (G.cfaceC.1 h2) (enF _))
        obtain ⟨q_j, nnxFj⟩ := G.fprojP qFnnx
        have j'x : x ≠ G.fproj q (G.node (G.node x)) := by
          intro h
          have h1 := nnxFj
          rw [← h, G.cubic_eq' hcub, ← G.cface1] at h1
          exact G.bridgeless_cface hbr x (G.cfaceC.1 h1)
        have j'nx : G.node x ≠ G.fproj q (G.node (G.node x)) := by
          intro h
          have h1 := nnxFj
          rw [← h] at h1
          exact G.bridgeless_cface hbr (G.node (G.node x))
            (connect_trans h1 (G.cfaceC.1 (enF (G.node x))))
        have hnext := (arc_props Uq q_nx q_j j'nx).2.2 (by rw [next_nx]; exact j'x)
        apply chord (G.edge (G.node (G.node x))) dEennx qFennx qFeennx
        · rw [Djennx, ee, next_nx]
          exact j'x
        · rw [Djennx, ee]
          have := hnext.1
          rwa [next_nx] at this
      -- `node x` and `node (node x)` are distinct darts of `insertE cc` in the same node.
      have x'nx : G.node x ≠ x := G.cubic_neq hcub x
      have x'nnx : G.node (G.node x) ≠ x := fun h => x'nx (by
        have := congrArg G.node h
        rw [G.cubic_eq hcub] at this
        exact this.symm)
      have cc_nx := sub_q _ (tail_of _ q_nx x'nx)
      have cc_nnx := sub_q _ (tail_of _ q_nnx x'nnx)
      have hne : G.node x ≠ G.node (G.node x) := fun h => x'nx (G.nodeI h).symm
      exact hne (List.inj_on_of_nodup_map cc_sparse cc_nx cc_nnx
        ((root_eq_iff G.cnode_sym).2 (fconnect1 G.node (G.node x))))
  have dF : ∀ q, G.ContractRing cc q → ∃ y, y ∈ G.diskF q := fun q hq =>
    dF_cc _ q (Nat.lt_succ_self _) hq
  rw [G.nontrivial0P]
  refine ⟨dF p cc_p, ?_⟩
  obtain ⟨URp, nt_p, sub_p⟩ := cc_p
  obtain ⟨x, p1, rfl⟩ : ∃ x p1, p = x :: p1 := by
    match p, nt_p with
    | [], h => exact False.elim h
    | x :: p1, _ => exact ⟨x, p1, rfl⟩
  have hrot : (x :: p1).rotate 1 = p1 ++ [x] := by simp
  have URp1 : G.SCycle G.rlink (p1 ++ [x]) := by
    rw [← hrot]
    exact (G.rot_scycle 1 G.rlink (x :: p1)).2 URp
  have nt_p1 : G.ProperRing (p1 ++ [x]) := by
    rw [← hrot]
    exact (G.proper_ring_rot hpl 1 (x :: p1)).2 nt_p
  have cc_r : G.ContractRing cc (G.revRing (p1 ++ [x])) := by
    refine ⟨G.scycle_rev_ring hG URp1, (G.proper_rev_ring hG _).2 nt_p1, fun y hy => ?_⟩
    have hy' : y ∈ (p1.map G.edge).reverse := by
      simpa [revRing] using hy
    rw [List.mem_reverse, List.mem_map] at hy'
    obtain ⟨z, hz, rfl⟩ := hy'
    have := sub_p z hz
    rw [G.mem_insertE hpl] at this ⊢
    obtain ⟨t, ht, zEt⟩ := this
    exact ⟨t, ht, (G.cedge1 z t).1 zEt⟩
  obtain ⟨y, hy⟩ := dF _ cc_r
  refine ⟨y, ?_⟩
  rw [G.diskF_rev_ring hG URp1 nt_p1] at hy
  rw [← G.diskFC_rot 1 (x :: p1), hrot]
  exact hy

/-- math-comp `contract_ring_max`: a contract ring has at most one more dart than the
contract. -/
theorem contract_ring_max (cexG : G.MinimalCounterExample) {cc p : List D}
    (cc_p : G.ContractRing cc p) : p.length ≤ cc.length + 1 := by
  obtain ⟨URp, nt_p, cc_p⟩ := cc_p
  have hG := cexG.toPlanarBridgelessPlainConnected
  have hpl := cexG.plain
  -- the dart of `cc` associated with a dart of `insertE cc` (math-comp `pick (df x)`)
  let f : D → D := fun x => if x ∈ cc then x else G.edge x
  have f_E : ∀ x, f x = x ∨ f x = G.edge x := fun x => by
    by_cases hxc : x ∈ cc
    · exact Or.inl (ite_eq_left hxc)
    · exact Or.inr (ite_eq_right hxc)
  have f_cc : ∀ x ∈ G.insertE cc, f x ∈ cc := by
    intro x hx
    obtain ⟨y, hy, xEy⟩ := (G.mem_insertE hpl cc x).1 hx
    by_cases hxc : x ∈ cc
    · have : f x = x := ite_eq_left hxc
      rw [this]
      exact hxc
    · have : f x = G.edge x := ite_eq_right hxc
      rw [this]
      have h1 := (G.plain_orbit hpl x y).1 xEy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      rcases h1 with rfl | rfl
      · exact absurd hy hxc
      · exact hy
  have Up := G.scycle_uniq URp
  have Up1 : p.tail.Nodup := Up.sublist (List.tail_sublist p)
  have hN : ∀ {u v}, u ∈ p → v ∈ p → G.edge u ≠ v := fun hu hv e =>
    G.diskN_edge_ring hG URp nt_p hu (e ▸ G.mem_diskN_of_mem p hv)
  have f_inj : ∀ x ∈ p.tail, ∀ y ∈ p.tail, f x = f y → x = y := by
    intro x hx y hy hxy
    have px := List.mem_of_mem_tail hx
    have py := List.mem_of_mem_tail hy
    rcases f_E x with hfx | hfx <;> rcases f_E y with hfy | hfy
    · rw [← hfx, hxy, hfy]
    · exact absurd (hfx.symm.trans (hxy.trans hfy)).symm (hN py px)
    · exact absurd (hfx.symm.trans (hxy.trans hfy)) (hN px py)
    · exact G.edgeI (hfx.symm.trans (hxy.trans hfy))
  have h1 : (p.tail.map f).Nodup := Up1.map_on f_inj
  have h2 : p.tail.map f ⊆ cc := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
    exact f_cc x (cc_p x hx)
  have h3 := h1.length_le_of_subset h2
  rw [List.length_map, List.length_tail] at h3
  omega

/-- math-comp `contract3_valid`: a sparse contract of size at most 3 has no contract ring. -/
theorem contract3_valid (cexG : G.MinimalCounterExample) {cc : List D}
    (cc_sparse : G.Sparse (G.insertE cc)) (cc_le3 : cc.length ≤ 3) (p : List D) :
    ¬ G.ContractRing cc p := by
  intro cc_p
  have hp := contract_ring_max cexG cc_p
  exact G.birkhoff_lt5 cexG (by omega) cc_p.scycle (sparse_contract_ring cexG cc_sparse cc_p)

/-- math-comp `triad_valid`: a sparse contract of size 4 that has a triad has no contract
ring. -/
theorem triad_valid (cexG : G.MinimalCounterExample) {cc : List D} {x0 : D}
    (cc_sparse : G.Sparse (G.insertE cc)) (cc4 : cc.length = 4)
    (triad_x0 : G.Triad (G.insertE cc) x0) (p : List D) : ¬ G.ContractRing cc p := by
  intro cc_p
  have hpl := cexG.plain
  have hbr := cexG.bridgeless
  have ee := G.plain_eq hpl
  have p_le5 : p.length ≤ 5 := by
    have := contract_ring_max cexG cc_p
    omega
  have nt0p := sparse_contract_ring cexG cc_sparse cc_p
  obtain ⟨URp, nt_p, sub_p⟩ := cc_p
  -- By the Birkhoff theorem, `p` is a 5-ring with a single face on one side.
  have sz_p : p.length = 5 := by
    by_contra h
    exact G.birkhoff_lt5 cexG (by omega) URp nt0p
  have triv1p : ¬ G.NontrivialRing 1 p := by
    have := G.birkhoff cexG p_le5 URp
    rwa [sz_p, beq_self_eq_true, Bool.toNat_true] at this
  -- There is a face `y0` all of whose neighbours are in `fband p`.
  obtain ⟨y0, sAy0Fp⟩ : ∃ y0, ∀ y, G.adj y0 y → y ∈ G.fband p := by
    by_contra no_y
    push Not at no_y
    obtain ⟨⟨y0, dFy0⟩, ⟨y1, dFCy1⟩⟩ := (G.nontrivial0P p).1 nt0p
    apply triv1p
    rw [G.nontrivial1P]
    have key : ∀ y, ∃ z, G.cface y z ∧ G.face (G.edge z) ∉ G.fband p ∧
        ¬ G.cface y (G.face (G.edge z)) := by
      intro y
      obtain ⟨t, yAt, pF't⟩ := no_y y
      obtain ⟨z, yFz, zRt⟩ := G.adjP.1 yAt
      refine ⟨z, yFz, fun h => pF't ?_, fun h => ?_⟩
      · have h1 : G.edge z ∈ G.fband p := ((G.fbandF p) _ _ rfl).2 h
        exact ((G.fbandF p).connect_iff zRt).1 h1
      · apply G.bridgeless_cface hbr z
        exact (G.cface1r _ _).2 (connect_trans (G.cfaceC.1 yFz) h)
    constructor
    · obtain ⟨z, y0Fz, hF, hF'⟩ := key y0
      refine ⟨y0, dFy0, G.face (G.edge z), ⟨?_, hF⟩, hF'⟩
      have dFz : z ∈ G.diskF p := ((G.diskF_face p).connect_iff y0Fz).1 dFy0
      exact ((G.diskN_node p) (G.face (G.edge z)) z (G.edgeK z)).2 dFz.1
    · obtain ⟨z, y1Fz, hF, hF'⟩ := key y1
      refine ⟨y1, dFCy1, G.face (G.edge z), ⟨fun h => ?_, hF⟩, hF'⟩
      have dFCz : z ∈ G.diskFC p := ((G.diskFC_face p).connect_iff y1Fz).1 dFCy1
      exact dFCz.1 (((G.diskN_node p) (G.face (G.edge z)) z (G.edgeK z)).1 h)
  -- All the faces of `p` are adjacent to `y0`, since `y0` has at least five neighbours.
  have sFpAy0 : ∀ x, x ∈ G.fband p → G.adj y0 x := by
    intro x pFx
    by_contra not_y0Ax
    have hpenta := G.min_arity cexG y0
    have e1 : G.arity y0 = fcard G.face (G.fband (G.spokeRing y0)) := by
      rw [G.scycle_fcard_fband (G.scycle_spoke_ring cexG y0), G.size_spoke_ring]
    have e2 : fcard G.face (G.fband p) = 5 := by rw [G.scycle_fcard_fband URp, sz_p]
    have hsub : G.fband (G.spokeRing y0) ⊆ G.fband p := fun z hz =>
      sAy0Fp z ((G.fband_spoke_ring y0 z).1 hz)
    have hlt : fcard G.face (G.fband (G.spokeRing y0)) < fcard G.face (G.fband p) := by
      refine Set.ncard_lt_ncard ((Set.image_mono hsub).ssubset_of_not_subset fun h => ?_)
        (Set.toFinite _)
      obtain ⟨z, hz, hzx⟩ := h ⟨x, pFx, rfl⟩
      apply not_y0Ax
      rw [← G.fband_spoke_ring]
      exact ((G.fbandF _).connect_iff ((comp_eq_iff G.cface_sym).1 hzx)).1 hz
    omega
  -- All the darts of `insertE cc` are in `fband p`, since otherwise `p` would be a contract
  -- ring for a contract of size 3.
  have p_cc : ∀ z, z ∈ G.insertE cc → z ∈ G.fband p := by
    intro z hz
    by_contra pF'z
    obtain ⟨z1, cc_z1, zEz1⟩ := (G.mem_insertE hpl cc z).1 hz
    obtain ⟨i, cc1, Dcc1⟩ := rot_to cc_z1
    have hlen : cc1.length = 3 := by
      have := congrArg List.length Dcc1
      rw [length_rot, List.length_cons] at this
      omega
    have cc_p1 : G.ContractRing cc1 p := by
      refine ⟨URp, nt_p, fun t pt => ?_⟩
      have p_t := List.mem_of_mem_tail pt
      have t_cc := sub_p t pt
      rw [G.mem_insertE hpl] at t_cc ⊢
      obtain ⟨u, cc_u, tEu⟩ := t_cc
      have cc_u' : u ∈ z1 :: cc1 := by
        rw [← Dcc1]
        exact mem_rot.2 cc_u
      rcases List.mem_cons.1 cc_u' with rfl | cc1_u
      · exfalso
        have zEt : G.cedge z t := connect_trans zEz1 (G.cedgeC.1 tEu)
        have h1 := (G.plain_orbit hpl z t).1 zEt
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
        rcases h1 with rfl | rfl
        · exact pF'z (G.ring_fband p _ p_t)
        · apply pF'z
          refine ⟨next p (G.edge z), mem_next.2 p_t, ?_⟩
          have h2 : G.cface (G.edge (G.edge z)) (next p (G.edge z)) := next_cycle URp.1 p_t
          rwa [ee] at h2
      · exact ⟨u, cc1_u, tEu⟩
    have := contract_ring_max cexG cc_p1
    omega
  -- The triad `x0` then yields a contradiction.
  obtain ⟨hcount, hnotadj⟩ := triad_x0
  by_cases x0Fy0 : G.cface x0 y0
  · exact hnotadj fun z hz => (G.adjF x0Fy0 z).2 (sFpAy0 z (p_cc z hz))
  · have hmax := fcard_adj_max cexG x0Fy0
    classical
    set fl := (G.spokeRing x0).filter (fun t => decide (t ∈ G.fband (G.insertE cc))) with hfl
    have hc : 2 < fl.length := by
      refine lt_of_lt_of_le hcount (le_of_eq ?_)
      rw [hfl, ← List.countP_eq_length_filter, spokeRing, List.countP_map, List.countP_reverse]
      apply List.countP_congr
      intro y _
      simp only [Function.comp_apply, spoke]
      constructor
      · intro h
        exact decide_eq_true (((G.fbandF _) _ _ rfl).1 (of_decide_eq_true h))
      · intro h
        exact decide_eq_true (((G.fbandF _) _ _ rfl).2 (of_decide_eq_true h))
    have fl_simple : G.Simple fl :=
      List.Nodup.sublist (List.filter_sublist.map _) (G.scycle_spoke_ring cexG x0).2
    have hsub : G.fband fl ⊆ {z | G.adj y0 z ∧ G.adj x0 z} := by
      rintro z ⟨t, ht, zFt⟩
      rw [hfl, List.mem_filter] at ht
      obtain ⟨x0r_t, tS⟩ := ht
      obtain ⟨u, ccE_u, tFu⟩ := of_decide_eq_true tS
      refine ⟨(G.adjFr (connect_trans zFt tFu) y0).2 (sFpAy0 u (p_cc u ccE_u)), ?_⟩
      exact (G.adjFr zFt x0).2 ((G.fband_spoke_ring x0 t).1 (G.ring_fband _ t x0r_t))
    have hle : fcard G.face (G.fband fl) ≤ fcard G.face {z | G.adj y0 z ∧ G.adj x0 z} :=
      Set.ncard_le_ncard (Set.image_mono hsub) (Set.toFinite _)
    rw [G.simple_fcard_fband fl_simple] at hle
    omega

/-- A four-coloring is a contract coloring for the empty contract. -/
private theorem cc_colorable_nil {D0 : Type*} (G0 : Hypermap D0) (h : G0.FourColorable) :
    G0.CcColorable [] := by
  obtain ⟨k, kE, kF⟩ := h
  exact ⟨k, fun y => ⟨fun e => absurd e (kE y), fun hy => by simp [insertE] at hy⟩, kF⟩

/-- The induction step of math-comp `contract_coloring`: the contract `x :: cc` of `G0` is
reduced to a contract of the map `G2` obtained by removing the edge `{x, edge x}` with two
Walkup transforms (`G1 = WalkupF x`, `G2 = WalkupF (edge x)`), which has two darts less. -/
private theorem contract_coloring_step {D0 : Type u} [Fintype D0] [DecidableEq D0]
    (G0 : Hypermap D0) (geoG0 : G0.PlanarBridgelessPlainPrecubic) (x : D0) (cc : List D0)
    (ring'cc : ∀ p, ¬ G0.ContractRing (x :: cc) p)
    (IH : ∀ (D2 : Type u) [Fintype D2] [DecidableEq D2] (G2 : Hypermap D2) (cc2 : List D2),
      G2.PlanarBridgelessPlainPrecubic → cc2.length ≤ cc.length →
      Fintype.card D2 < Fintype.card D0 → (∀ p, ¬ G2.ContractRing cc2 p) →
      G2.CcColorable cc2) :
    G0.CcColorable (x :: cc) := by
  have plainG0 : G0.Plain := geoG0.plain
  have ee0 := G0.plain_eq plainG0
  have bridge'G0 := G0.bridgeless_cface geoG0.bridgeless
  have D_E0 : ∀ y, G0.cedge x y ↔ y = x ∨ y = G0.edge x := fun y => by
    rw [G0.plain_orbit plainG0]
    simp
  have x'ex : G0.edge x ≠ x := G0.plain_neq plainG0 x
  -- The two Walkup transforms, and the injection `h` of their darts into `G0`.
  set G1 := G0.WalkupF x
  set uex : WDart x := ⟨G0.edge x, x'ex⟩
  set G2 := G1.WalkupF uex
  set h : WDart uex → D0 := fun w => w.1.1
  have Ih : Injective h := fun a b hab => Subtype.ext (Subtype.ext hab)
  have xE'h : ∀ w, ¬ G0.cedge x (h w) := by
    intro w hw
    rcases (D_E0 _).1 hw with e | e
    · exact w.1.2 e
    · exact w.2 (Subtype.ext e)
  have Eh : ∀ y, ¬ G0.cedge x y → ∃ w, h w = y := by
    intro y hy
    rw [D_E0, not_or] at hy
    exact ⟨⟨⟨y, hy.1⟩, fun e => hy.2 (congrArg Subtype.val e)⟩, rfl⟩
  have h_e : ∀ w, h (G2.edge w) = G0.edge (h w) := by
    intro w
    have h1 : G0.edge (h w) ≠ x := by
      intro e
      apply w.2
      apply Subtype.ext
      show h w = G0.edge x
      calc h w = G0.edge (G0.edge (h w)) := (ee0 _).symm
        _ = G0.edge x := by rw [e]
    have h2 : G1.edge w.1 ≠ uex := by
      intro e
      have e1 : (G1.edge w.1).1 = G0.edge x := congrArg Subtype.val e
      have e2 : (G1.edge w.1).1 = G0.edge (h w) := skip1_of_ne x h1
      exact w.1.2 (G0.edgeI (e2.symm.trans e1))
    calc h (G2.edge w) = (G1.edge w.1).1 := congrArg Subtype.val (skip1_of_ne uex h2)
      _ = G0.edge (h w) := skip1_of_ne x h1
  have hN : ∀ w w', G2.cnode w w' ↔ G0.cnode (h w) (h w') := fun w w' =>
    (fconnect_skip uex G1.nodeI w w').trans (fconnect_skip x G0.nodeI w.1 w'.1)
  have hE : ∀ w w', G2.cedge w w' ↔ G0.cedge (h w) (h w') := fun w w' =>
    (fconnect_skip uex G1.edgeI w w').trans (fconnect_skip x G0.edgeI w.1 w'.1)
  -- The faces of `G2`: `uex` is an edge fixpoint of `G1`, and the face of `x` and `edge x` in
  -- `G0` are merged in `G1`.
  have e_uex : G1.edge uex = uex := Subtype.ext (skip1_of_eq x (ee0 x))
  have hF0 : ∀ w w', G2.cface w w' ↔ G1.cface w.1 w'.1 := fun w w' =>
    (fconnect_congr (G1.permF.glink_fp_skip_edge uex (Or.inr (Or.inl e_uex)))).trans
      (fconnect_skip uex G1.faceI w w')
  have hcross : ¬ G0.permF.crossEdge x := bridge'G0 x
  have hF1 : ∀ w w', (G0.cface (h w) x ∨ G0.cface (h w) (G0.edge x)) →
      (G2.cface w w' ↔ (G0.cface (h w') x ∨ G0.cface (h w') (G0.edge x))) := fun w w' hw =>
    (hF0 w w').trans (G0.permF.cskip_edge_merge x (u := w.1) (v := w'.1) hcross hw)
  have hF2 : ∀ w w', ¬ (G0.cface (h w) x ∨ G0.cface (h w) (G0.edge x)) →
      (G2.cface w w' ↔ G0.cface (h w) (h w')) := fun w w' hw =>
    (hF0 w w').trans (G0.permF.same_cskip_edge x (u := w.1) (v := w'.1) hw)
  have xR_F : ∀ y y', G0.cface y y' →
      ((G0.cface y x ∨ G0.cface y (G0.edge x)) ↔
        (G0.cface y' x ∨ G0.cface y' (G0.edge x))) := by
    intro y y' hyy'
    rw [G0.same_cface hyy', G0.same_cface hyy']
  have hFh : ∀ w w', G0.cface (h w) (h w') → G2.cface w w' := by
    intro w w' hww'
    by_cases hw : G0.cface (h w) x ∨ G0.cface (h w) (G0.edge x)
    · exact (hF1 w w' hw).2 ((xR_F _ _ hww').1 hw)
    · exact (hF2 w w' hw).2 hww'
  -- `G2` is a smaller planar bridgeless plain precubic map.
  have ee2 : ∀ w, G2.edge (G2.edge w) = w := fun w => Ih (by rw [h_e, h_e, ee0])
  have plainG2 : G2.Plain := G2.plainP.2 fun w _ => ⟨ee2 w, fun e =>
    G0.plain_neq plainG0 (h w) (by rw [← h_e, e])⟩
  have precubicG2 : G2.Precubic := by
    intro w
    calc order G2.node w = (h '' {v | G2.cnode w v}).ncard :=
          (Set.ncard_image_of_injective _ Ih).symm
      _ ≤ order G0.node (h w) :=
          Set.ncard_le_ncard (by rintro _ ⟨v, hv, rfl⟩; exact (hN w v).1 hv) (Set.toFinite _)
      _ ≤ 3 := geoG0.precubic _
  have bridgelessG2 : G2.Bridgeless := by
    rintro ⟨w, wFew⟩
    by_cases hw : G0.cface (h w) x ∨ G0.cface (h w) (G0.edge x)
    · have hew : G0.cface (G0.edge (h w)) x ∨ G0.cface (G0.edge (h w)) (G0.edge x) := by
        have := (hF1 w _ hw).1 wFew
        rwa [h_e] at this
      -- `[h w, y]` would be a contract ring for `x :: cc`, with `y` in `{x, edge x}`.
      obtain ⟨y, hyx, ewFy, eyFw⟩ : ∃ y, (y = x ∨ y = G0.edge x) ∧
          G0.cface (G0.edge (h w)) y ∧ G0.cface (G0.edge y) (h w) := by
        rcases hw with wFx | wFex
        · refine ⟨G0.edge x, Or.inr rfl, ?_, by rw [ee0]; exact G0.cfaceC.1 wFx⟩
          rcases hew with ewFx | ewFex
          · exact absurd (connect_trans wFx (G0.cfaceC.1 ewFx)) (bridge'G0 (h w))
          · exact ewFex
        · refine ⟨x, Or.inl rfl, ?_, G0.cfaceC.1 wFex⟩
          rcases hew with ewFx | ewFex
          · exact ewFx
          · exact absurd (connect_trans wFex (G0.cfaceC.1 ewFex)) (bridge'G0 (h w))
      apply ring'cc [h w, y]
      refine ⟨⟨⟨ewFy, eyFw, trivial⟩, ?_⟩, ?_, ?_⟩
      · rw [G0.simple_cons]
        refine ⟨fun ⟨t, ht, wFt⟩ => ?_, List.nodup_singleton _⟩
        rw [List.mem_singleton] at ht
        rw [ht] at wFt
        exact bridge'G0 (h w) (connect_trans wFt (G0.cfaceC.1 ewFy))
      · show G0.edge (h w) ≠ y
        intro e
        apply xE'h w
        have : G0.cedge x (G0.edge (h w)) := by
          rw [e]
          exact (D_E0 y).2 hyx
        exact (G0.cedge1r x (h w)).2 this
      · intro z hz
        rw [List.tail_cons, List.mem_singleton] at hz
        rw [hz]
        rcases hyx with e | e
        · rw [e]
          exact List.mem_cons_self
        · rw [e]
          exact List.mem_cons_of_mem _ List.mem_cons_self
    · exact bridge'G0 (h w) (by have := (hF2 w _ hw).1 wFew; rwa [h_e] at this)
  have geoG2 : G2.PlanarBridgelessPlainPrecubic :=
    { planar := planar_WalkupF G1 uex (planar_WalkupF G0 x geoG0.planar)
      bridgeless := bridgelessG2
      plain := plainG2
      precubic := precubicG2 }
  -- The contract `cc2` of `G2`: the preimage of the darts of `cc` off the edge of `x`.
  set cc1 := cc.filter (fun y => y ≠ x ∧ y ≠ G0.edge x) with hcc1
  have cc1P : ∀ y, y ∈ cc1 ↔ y ∈ cc ∧ ¬ G0.cedge x y := by
    intro y
    rw [hcc1, List.mem_filter, D_E0]
    constructor
    · rintro ⟨h1, h2⟩
      have h2 := of_decide_eq_true h2
      exact ⟨h1, fun h => h.elim h2.1 h2.2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, decide_eq_true ⟨fun e => h2 (Or.inl e), fun e => h2 (Or.inr e)⟩⟩
  set cc2 := preimSeq h cc1
  have hcc2 : cc2.map h = cc1 := map_preim fun y hy => by
    obtain ⟨w, hw⟩ := Eh y ((cc1P y).1 hy).2
    exact ⟨w, hw⟩
  have Excc : ∀ y, y ∈ G0.insertE (x :: cc) ↔ G0.cedge x y ∨ y ∈ G0.insertE cc1 := by
    intro y
    have e1 : y ∈ G0.insertE (x :: cc) ↔ (y = x ∨ y = G0.edge x) ∨ y ∈ G0.insertE cc := by
      show y ∈ x :: G0.edge x :: G0.insertE cc ↔ _
      simp only [List.mem_cons, or_assoc]
    rw [e1, ← D_E0]
    by_cases xEy : G0.cedge x y
    · exact ⟨fun _ => Or.inl xEy, fun _ => Or.inl xEy⟩
    · rw [G0.mem_insertE plainG0, G0.mem_insertE plainG0]
      constructor
      · rintro (h' | ⟨z, cc_z, yEz⟩)
        · exact absurd h' xEy
        · exact Or.inr ⟨z, (cc1P z).2 ⟨cc_z, fun xEz =>
            xEy (connect_trans xEz (G0.cedgeC.1 yEz))⟩, yEz⟩
      · rintro (h' | ⟨z, cc1_z, yEz⟩)
        · exact absurd h' xEy
        · exact Or.inr ⟨z, ((cc1P z).1 cc1_z).1, yEz⟩
  have hEcc1 : ∀ w, h w ∈ G0.insertE cc1 ↔ w ∈ G2.insertE cc2 := by
    intro w
    rw [G0.mem_insertE plainG0, G2.mem_insertE plainG2, ← hcc2]
    constructor
    · rintro ⟨_, hz, hE'⟩
      obtain ⟨w', hw', rfl⟩ := List.mem_map.1 hz
      exact ⟨w', hw', (hE w w').2 hE'⟩
    · rintro ⟨w', hw', hE'⟩
      exact ⟨h w', List.mem_map.2 ⟨w', hw', rfl⟩, (hE w w').1 hE'⟩
  have le_cc2 : cc2.length ≤ cc.length := by
    have := congrArg List.length hcc2
    rw [List.length_map] at this
    rw [this, hcc1]
    exact List.length_filter_le _ _
  have card2 : Fintype.card (WDart uex) < Fintype.card D0 := by
    have c1 := card_S_Walkup x
    have c2 := card_S_Walkup uex
    omega
  -- `cc2` has no contract ring in `G2`.
  have ring'cc2 : ∀ p, ¬ G2.ContractRing cc2 p := by
    rintro p ⟨URp, nt_p, cc_p⟩
    have Up : p.Nodup := G2.scycle_uniq URp
    have hlen2 : 2 ≤ p.length := two_le_length_of_proper nt_p
    -- `map h p` is simple.
    have UhpF : G0.Simple (p.map h) := by
      show ((p.map h).map (froot G0.face)).Nodup
      rw [List.map_map]
      refine Up.map_on fun w1 hw1 w2 hw2 e => ?_
      exact G2.scycle_cface URp _ hw1 _ hw2 (hFh _ _ ((G0.froot_face_eq_iff).1 e))
    -- `h` maps the tail of `p` into `insertE cc`.
    have cc_hp : ∀ w ∈ p.tail, h w ∈ G0.insertE cc := by
      intro w hw
      have h1 := (Excc (h w)).2 (Or.inr ((hEcc1 w).2 (cc_p w hw)))
      have h2 : h w ∈ x :: G0.edge x :: G0.insertE cc := h1
      rcases List.mem_cons.1 h2 with e | h3
      · exact (xE'h w ((congrArg (G0.cedge x) e).mpr (connect_refl x))).elim
      · rcases List.mem_cons.1 h3 with e | h4
        · exact (xE'h w ((congrArg (G0.cedge x) e).mpr (fconnect1 G0.edge x))).elim
        · exact h4
    -- `map h p` is not an R-cycle, since it would be a contract ring for `x :: cc`.
    have cyc'Rhp : ¬ cycle G0.rlink (p.map h) := by
      intro cycRhp
      apply ring'cc (p.map h)
      refine ⟨⟨cycRhp, UhpF⟩, ?_, ?_⟩
      · match p, nt_p with
        | [], nt => exact False.elim nt
        | [_], nt => exact False.elim nt
        | [w0, w1], nt =>
          show G0.edge (h w0) ≠ h w1
          rw [← h_e]
          exact fun e => nt (Ih e)
        | _ :: _ :: _ :: _, _ => trivial
      · intro y hy
        rw [← List.map_tail] at hy
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (cc_hp w hw))
    -- So some R-link `w0 → w1` of `p` is not an R-link of `map h p`.
    obtain ⟨w0, pw0, hw0⟩ : ∃ w0 ∈ p, ¬ G0.rlink (h w0) (h (next p w0)) := by
      by_contra hall
      push Not at hall
      apply cyc'Rhp
      refine cycle_from_next (Up.map Ih) fun y hy => ?_
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
      rw [next_map Ih]
      exact hall w hw
    obtain ⟨i, s, hi⟩ := rotate_to pw0
    obtain ⟨w1, p1', rfl⟩ : ∃ w1 p1', s = w1 :: p1' := by
      cases s with
      | nil =>
        have := congrArg List.length hi
        rw [List.length_rotate, List.length_singleton] at this
        omega
      | cons w1 p1' => exact ⟨w1, p1', rfl⟩
    have hnext : next p w0 = w1 := by
      rw [← next_rotate Up i, hi]
      simp [next, nextAt]
    rw [hnext] at hw0
    have hrot1 : p.rotate (i + 1) = w1 :: (p1' ++ [w0]) := by
      rw [← List.rotate_rotate, hi]
      simp
    have cycRp1 : cycle G2.rlink (w1 :: (p1' ++ [w0])) := by
      rw [← hrot1]
      exact (cycle_rotate _ _).2 URp.1
    have w1Rp1 : path G2.rlink w1 (p1' ++ [w0]) := (path_concat.1 cycRp1).1
    have w0Rw1 : G2.rlink w0 w1 := by
      have := (path_concat.1 cycRp1).2
      rwa [last_concat] at this
    have Up1 : (w1 :: (p1' ++ [w0])).Nodup := by
      rw [← hrot1]
      exact List.nodup_rotate.2 Up
    have p1'w1 : w1 ∉ p1' ++ [w0] := (List.nodup_cons.1 Up1).1
    have mem_p : ∀ u, u ∈ w1 :: (p1' ++ [w0]) ↔ u ∈ p := fun u => by
      rw [← hrot1, List.mem_rotate]
    -- `edge (h w0)` and `h w1` are in the faces of `x` or `edge x`.
    have xRew0 : G0.cface (G0.edge (h w0)) x ∨ G0.cface (G0.edge (h w0)) (G0.edge x) := by
      by_contra h'
      apply hw0
      have := (hF2 (G2.edge w0) w1 (by rwa [h_e])).1 w0Rw1
      rw [h_e] at this
      exact this
    have xRw1 : G0.cface (h w1) x ∨ G0.cface (h w1) (G0.edge x) :=
      (hF1 (G2.edge w0) w1 (by rw [h_e]; exact xRew0)).1 w0Rw1
    obtain ⟨x1, hx1, w1Fx1⟩ : ∃ x1, (x1 = x ∨ x1 = G0.edge x) ∧ G0.cface (h w1) x1 := by
      rcases xRw1 with h' | h'
      · exact ⟨x, Or.inl rfl, h'⟩
      · exact ⟨G0.edge x, Or.inr rfl, h'⟩
    obtain ⟨x0, hx0, ew0Fx0⟩ : ∃ x0, (x0 = x ∨ x0 = G0.edge x) ∧
        G0.cface (G0.edge (h w0)) x0 := by
      rcases xRew0 with h' | h'
      · exact ⟨x, Or.inl rfl, h'⟩
      · exact ⟨G0.edge x, Or.inr rfl, h'⟩
    have ex0_x1 : G0.edge x0 = x1 := by
      have hne : x0 ≠ x1 := fun e => hw0 (by
        rw [e] at ew0Fx0
        exact connect_trans ew0Fx0 (G0.cfaceC.1 w1Fx1))
      rcases hx0 with e0 | e0 <;> rcases hx1 with e1 | e1
      · exact absurd (e0.trans e1.symm) hne
      · rw [e0, e1]
      · rw [e0, e1, ee0]
      · exact absurd (e0.trans e1.symm) hne
    -- No other dart of `p` is in the face of `x` or `edge x`.
    have p1R'x : ∀ u ∈ p1' ++ [w0], ¬ (G0.cface (h u) x ∨ G0.cface (h u) (G0.edge x)) := by
      intro u hu xRu
      have w1Fu : G2.cface w1 u := (hF1 w1 u xRw1).2 xRu
      have := G2.scycle_cface URp _ ((mem_p w1).1 List.mem_cons_self) _
        ((mem_p u).1 (List.mem_cons_of_mem _ hu)) w1Fu
      exact p1'w1 (by rw [this]; exact hu)
    -- Inserting `x0` between `h w0` and `h w1` yields an R-cycle of `G0`.
    have cycRq1 : cycle G0.rlink (x0 :: (w1 :: (p1' ++ [w0])).map h) := by
      show path G0.rlink x0 ((w1 :: (p1' ++ [w0])).map h ++ [x0])
      rw [List.map_cons, List.cons_append, path_cons, path_concat, last_map, last_concat]
      refine ⟨?_, ?_, ew0Fx0⟩
      · show G0.cface (G0.edge x0) (h w1)
        rw [ex0_x1]
        exact G0.cfaceC.1 w1Fx1
      · rw [path_map]
        refine path.mono_mem (fun a b _ hb hab => ?_) w1Rp1
        have := (hF2 b (G2.edge a) (p1R'x b hb)).1 (G2.cfaceC.1 hab)
        rw [h_e] at this
        exact G0.cfaceC.1 this
    have simpleq1 : G0.Simple (x0 :: (w1 :: (p1' ++ [w0])).map h) := by
      rw [G0.simple_cons]
      refine ⟨?_, ?_⟩
      · rintro ⟨y, hy, x0Fy⟩
        rw [List.map_cons, List.mem_cons] at hy
        rcases hy with e | hy
        · rw [e] at x0Fy
          apply bridge'G0 x0
          rw [ex0_x1]
          exact connect_trans x0Fy w1Fx1
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hy
          apply p1R'x u hu
          rcases hx0 with e0 | e0
          · left
            rw [← e0]
            exact G0.cfaceC.1 x0Fy
          · right
            rw [← e0]
            exact G0.cfaceC.1 x0Fy
      · have e : (w1 :: (p1' ++ [w0])).map h = (p.map h).rotate (i + 1) := by
          rw [← List.map_rotate, hrot1]
        rw [e, G0.simple_rot]
        exact UhpF
    -- Its rotation starting at the image of the head of `p` is a contract ring for `x :: cc`.
    obtain ⟨w, p0, Dp⟩ := List.exists_cons_of_ne_nil
      (List.ne_nil_of_length_pos (by omega) : p ≠ [])
    have hw_q1 : h w ∈ x0 :: (w1 :: (p1' ++ [w0])).map h :=
      List.mem_cons_of_mem _ (List.mem_map.2
        ⟨w, (mem_p w).2 (by rw [Dp]; exact List.mem_cons_self), rfl⟩)
    obtain ⟨i2, q2, Dq2⟩ := rotate_to hw_q1
    have URq2 : G0.SCycle G0.rlink (h w :: q2) := by
      rw [← Dq2, G0.rot_scycle]
      exact ⟨cycRq1, simpleq1⟩
    apply ring'cc (h w :: q2)
    refine ⟨URq2, G0.size_proper_ring ?_, ?_⟩
    · have := congrArg List.length Dq2
      have hl : (w1 :: (p1' ++ [w0])).length = p.length := by
        rw [← hrot1, List.length_rotate]
      simp only [List.length_rotate, List.length_cons, List.length_map, List.length_append]
        at this hl ⊢
      omega
    · intro y hy
      rw [List.tail_cons] at hy
      have Uq2 : (h w :: q2).Nodup := G0.scycle_uniq URq2
      have hyw : y ≠ h w := fun e => (List.nodup_cons.1 Uq2).1 (e ▸ hy)
      have hyq1 : y ∈ x0 :: (w1 :: (p1' ++ [w0])).map h := by
        rw [← List.mem_rotate (n := i2), Dq2]
        exact List.mem_cons_of_mem _ hy
      rcases List.mem_cons.1 hyq1 with e | hy'
      · rw [e]
        rcases hx0 with e0 | e0
        · rw [e0]
          exact List.mem_cons_self
        · rw [e0]
          exact List.mem_cons_of_mem _ List.mem_cons_self
      · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hy'
        have pu := (mem_p u).1 hu
        rw [Dp, List.mem_cons] at pu
        rcases pu with e | p0u
        · exact (hyw (by rw [e])).elim
        · have := cc_hp u (by rw [Dp]; exact p0u)
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ this)
  -- Lift a contract coloring `k` of `G2` to `G0`.
  obtain ⟨k, kE, kF⟩ := IH (WDart uex) G2 cc2 geoG2 le_cc2 card2 ring'cc2
  have hk : G2.CcColoring cc2 k := ⟨kE, kF⟩
  -- If no dart of `G2` is in the face of `y`, then none is in the face of `edge y`.
  have ae0 : ∀ y, (¬ ∃ w, G0.cface y (h w)) → ¬ ∃ w, G0.cface (G0.edge y) (h w) := by
    rintro y ay0 ⟨w, eyFw⟩
    have xEy : G0.cedge x y := by
      by_contra h'
      obtain ⟨w', hw'⟩ := Eh y h'
      exact ay0 ⟨w', (congrArg (G0.cface y) hw').mpr (connect_refl y)⟩
    have xEfy : G0.cedge x (G0.face y) := by
      by_contra h'
      obtain ⟨w', hw'⟩ := Eh _ h'
      exact ay0 ⟨w', (congrArg (G0.cface y) hw').mpr (fconnect1 G0.face y)⟩
    have yEfy : G0.cedge y (G0.face y) := connect_trans (G0.cedgeC.1 xEy) xEfy
    have h1 := (G0.plain_orbit plainG0 y (G0.face y)).1 yEfy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
    rcases h1 with fy_y | fy_ey
    · -- `y` is a face fixpoint.
      have ny_ey : G0.node y = G0.edge y := by
        have := G0.plain_eq' plainG0 y
        rwa [fy_y] at this
      have hle := geoG0.precubic y
      have hpos := order_pos G0.nodeI y
      have hit := iter_order G0.nodeI y
      obtain h1 | h2 | h3 : order G0.node y = 1 ∨ order G0.node y = 2 ∨
          order G0.node y = 3 := by
        omega
      · rw [h1] at hit
        exact G0.plain_neq plainG0 y (ny_ey.symm.trans hit)
      · rw [h2] at hit
        have nny : G0.node (G0.node y) = y := hit
        have fey : G0.face (G0.edge y) = G0.edge y := by
          have := G0.nodeK (G0.node y)
          rw [nny] at this
          rw [this, ny_ey]
        have hw : h w = G0.edge y := by
          obtain ⟨n, hn⟩ := fconnect_iff_iterate.1 eyFw
          rw [← hn]
          exact Function.iterate_fixed fey n
        exact xE'h w ((congrArg (G0.cedge x) hw).mpr ((G0.cedge1r x y).1 xEy))
      · rw [h3] at hit
        have nnny : G0.node (G0.node (G0.node y)) = y := hit
        have ht : G0.face (G0.edge y) = G0.node (G0.node y) := by
          have := G0.nodeK (G0.node (G0.node y))
          rwa [nnny] at this
        apply bridge'G0 (G0.face (G0.edge y))
        have e1 : G0.cface (G0.edge (G0.face (G0.edge y))) (G0.node y) := by
          rw [ht]
          have := fconnect1 G0.face (G0.edge (G0.node (G0.node y)))
          rwa [G0.nodeK] at this
        rw [ny_ey] at e1
        exact G0.cfaceC.1 (connect_trans e1 (fconnect1 G0.face (G0.edge y)))
    · exact bridge'G0 y ((congrArg (G0.cface y) fy_ey).mp (fconnect1 G0.face y))
  open Classical in
  obtain ⟨k0, hk0⟩ : ∃ k0 : D0 → Color, ∀ y, k0 y =
      if hy : ∃ w, G0.cface y (h w) then k (Classical.choose hy) else Color0 :=
    ⟨fun y => if hy : ∃ w, G0.cface y (h w) then k (Classical.choose hy) else Color0,
      fun _ => rfl⟩
  have k0_eq : ∀ y w, G0.cface y (h w) → k0 y = k w := by
    intro y w yFw
    have hy : ∃ w, G0.cface y (h w) := ⟨w, yFw⟩
    rw [hk0, dite_eq_left hy]
    exact G2.cc_coloring_cface hk
      (hFh _ _ (connect_trans (G0.cfaceC.1 (Classical.choose_spec hy)) yFw))
  have k0h : ∀ w, k0 (h w) = k w := fun w => k0_eq _ w (connect_refl _)
  have k0F : ∀ y, k0 (G0.face y) = k0 y := by
    intro y
    by_cases hy : ∃ w, G0.cface y (h w)
    · obtain ⟨w, yFw⟩ := hy
      rw [k0_eq y w yFw, k0_eq (G0.face y) w ((G0.cface1 y (h w)).1 yFw)]
    · have hfy : ¬ ∃ w, G0.cface (G0.face y) (h w) := fun ⟨w, hw⟩ =>
        hy ⟨w, (G0.cface1 y (h w)).2 hw⟩
      rw [hk0, hk0, dite_eq_right hy, dite_eq_right hfy]
  have k0ex : k0 x = k0 (G0.edge x) := by
    by_cases ax : ∃ w, G0.cface x (h w)
    · obtain ⟨w, xFw⟩ := ax
      obtain ⟨w1, exFw1⟩ : ∃ w1, G0.cface (G0.edge x) (h w1) := by
        by_contra aex0
        have := ae0 _ aex0
        rw [ee0] at this
        exact this ⟨w, xFw⟩
      rw [k0_eq x w xFw, k0_eq _ w1 exFw1]
      exact G2.cc_coloring_cface hk
        ((hF1 w w1 (Or.inl (G0.cfaceC.1 xFw))).2 (Or.inr (G0.cfaceC.1 exFw1)))
    · have aex := ae0 x ax
      rw [hk0, hk0, dite_eq_right ax, dite_eq_right aex]
  refine ⟨k0, fun y => ?_, k0F⟩
  rw [Excc]
  by_cases xEy : G0.cedge x y
  · simp only [xEy, true_or, iff_true]
    rcases (D_E0 y).1 xEy with e | e
    · rw [e]
      exact k0ex.symm
    · rw [e, ee0]
      exact k0ex
  · simp only [xEy, false_or]
    obtain ⟨w, rfl⟩ := Eh y xEy
    rw [← h_e, k0h, k0h, hEcc1]
    exact kE w

/-- The induction of math-comp `contract_coloring`, on the size `n` of the contract, for all
the planar bridgeless plain precubic maps `G0` with at most `nG` darts (fewer than `nG` darts
for the empty contract), when all the maps with fewer than `nG` darts are four-colorable. -/
private theorem contract_coloring_aux (nG : ℕ)
    (min_nG : ∀ (D' : Type u) [Fintype D'] (G' : Hypermap D'),
      G'.PlanarBridgelessPlainPrecubic → Fintype.card D' < nG → G'.FourColorable) :
    ∀ (n : ℕ) (D0 : Type u) [Fintype D0] [DecidableEq D0] (G0 : Hypermap D0) (cc : List D0),
      G0.PlanarBridgelessPlainPrecubic → cc.length ≤ n → Fintype.card D0 ≤ nG →
      (cc = [] → Fintype.card D0 < nG) → (∀ p, ¬ G0.ContractRing cc p) →
      G0.CcColorable cc := by
  intro n
  induction n with
  | zero =>
    intro D0 _ _ G0 cc geoG0 hlen _ hcard0 _
    have hcc : cc = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hlen)
    subst hcc
    exact cc_colorable_nil G0 (min_nG D0 G0 geoG0 (hcard0 rfl))
  | succ n IHn =>
    intro D0 _ _ G0 cc geoG0 hlen hcard hcard0 ring'cc
    cases cc with
    | nil => exact cc_colorable_nil G0 (min_nG D0 G0 geoG0 (hcard0 rfl))
    | cons x cc =>
      refine contract_coloring_step G0 geoG0 x cc ring'cc ?_
      intro D2 _ _ G2 cc2 geoG2 hlen2 hcard2 ring'cc2
      simp only [List.length_cons] at hlen
      exact IHn D2 G2 cc2 geoG2 (by omega) (by omega) (fun _ => by omega) ring'cc2

/-- math-comp `contract_coloring`: in a minimal counter-example, a valid contract has a
contract coloring. -/
theorem contract_coloring (cexG : G.MinimalCounterExample) {r cc : List D}
    (hcc : G.ValidContract r cc) : G.CcColorable cc := by
  have ring'cc : ∀ p, ¬ G.ContractRing cc p := by
    rcases hcc.size with h | h | h | h
    · exact contract3_valid cexG hcc.sparse (by omega)
    · exact contract3_valid cexG hcc.sparse (by omega)
    · exact contract3_valid cexG hcc.sparse (by omega)
    · obtain ⟨x0, -, hx0⟩ := hcc.triad h
      exact triad_valid cexG hcc.sparse h hx0
  have hne : cc ≠ [] := by
    rintro rfl
    rcases hcc.size with h | h | h | h <;> simp at h
  exact contract_coloring_aux (Fintype.card D) cexG.minimal cc.length D G cc
    cexG.toPlanarBridgelessPlainPrecubic le_rfl le_rfl (fun e => absurd e hne) ring'cc

end ContractLemmas

end Hypermap

end FourColor
