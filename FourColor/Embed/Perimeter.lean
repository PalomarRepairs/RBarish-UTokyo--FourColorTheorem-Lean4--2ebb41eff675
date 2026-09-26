/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Embed.HomRing

/-!
# The perimeter of an embeddable configuration (part of the port of `embed.v`)

Under the section hypotheses `E : Hypermap.EmbedHyps Gm Gc rc h`, the facts about the ring `rc`
used to extend `h` to the whole of `bc := [predC rc]`:

* `E.rcN` : the ring is node-closed (math-comp local `rcN`);
* `E.edge_perimeter` : `x ∉ rc` or `edge x ∉ rc` (the ring faces have arity at least 3);
* `Drrrc`, `E.URrrc`, `E.URerc` : `rev_ring (rev rc) = map edge rc`, and both `rev rc` and
  `erc := map edge rc` are simple R-cycles (math-comp locals `Drrrc`, `URrrc`, `URerc`);
* `E.chordless_perimeter` : an edge whose two ends are off the ring has an end in the kernel;
* `E.fcard_adj_perimeter`, `E.adj_kernel_min`, `E.adj_kernel_max` : a face `x ∉ ac` has
  exactly two darts whose edge is in `fband rc`, hence at least one and at most four whose edge
  is in the kernel.

## Porting notes

* `fclosed node rc` is `Closed (frel Gc.node) {x | x ∈ rc}`; `E.rc_node` is the one-step form.
* The cardinals `#|predI (cface x) [preim edge of A]|` are `Set.ncard`s of
  `{z | cface x z ∧ edge z ∈ A}`.
* The Coq proof of `chordless_perimeter` has the local lemmas `nt_dFerc` (by induction on the
  size of a ring) and `dFerc_ac`; the induction is the private `nt_dF_aux`, and in its first case
  the chord ring `efex :: p2` is computed from the definition of `arc` (Coq: `index z p = 1`).
-/

namespace FourColor

open Function

universe u v

namespace Hypermap

namespace EmbedHyps

variable {Dm : Type u} [Fintype Dm] {Gm : Hypermap Dm}
  {Dc : Type v} [Fintype Dc] [DecidableEq Dc] {Gc : Hypermap Dc} {rc : List Dc} {h : Dc → Dm}
  (E : EmbedHyps Gm Gc rc h)
include E

omit [DecidableEq Dc] in
/-- math-comp local `rcN`: the ring `rc` is node-closed. -/
theorem rcN : Closed (frel Gc.node) {x | x ∈ rc} := by
  apply Closed.of_forward Gc.cnode_sym
  rintro x _ rfl rcx
  exact (fconnect_cycle E.cycNrc rcx).1 (fconnect1 _ _)

omit [DecidableEq Dc] in
/-- `rcN` at one node step. -/
theorem rc_node {x : Dc} : Gc.node x ∈ rc ↔ x ∈ rc := (E.rcN x _ rfl).symm

omit [DecidableEq Dc] in
/-- math-comp `edge_perimeter`: the two ends of an edge are not both on the ring. -/
theorem edge_perimeter (x : Dc) : x ∉ rc ∨ Gc.edge x ∉ rc := by
  by_contra hne
  rw [not_or, not_not, not_not] at hne
  obtain ⟨rc_x, rc_ex⟩ := hne
  have rc_fx : Gc.face x ∈ rc := E.rc_node.1 (by rw [Gc.plain_eq' E.plainGc]; exact rc_ex)
  have fxx : Gc.face x = x :=
    Gc.scycle_cface E.UNrc _ rc_fx _ rc_x (Gc.cfaceC.1 (fconnect1 _ _))
  have ar : Gc.arity x = 1 :=
    order_cycle (show fcycle Gc.face [x] from ⟨fxx, trivial⟩) (List.nodup_singleton x)
      List.mem_cons_self
  have := (Gc.goodRingArity_iff x).1 (E.embedGc.ring x rc_x)
  omega

omit [Fintype Dc] [DecidableEq Dc] E in
/-- math-comp local `Drrrc`: `rev_ring (rev rc) = map edge rc`. -/
theorem Drrrc : Gc.revRing rc.reverse = rc.map Gc.edge := by
  simp [revRing]

omit [DecidableEq Dc] in
/-- math-comp local `URrrc`: the reverse of the ring is a simple R-cycle. -/
theorem URrrc : Gc.SCycle Gc.rlink rc.reverse := by
  refine ⟨?_, (Gc.simple_rev rc).2 E.UrcF⟩
  apply Embed.cycle_reverse.2
  exact Embed.cycle_mono (fun a b (e : Gc.node a = b) => by rw [← e]; exact cface_edge_node a)
    E.cycNrc

omit [DecidableEq Dc] in
/-- math-comp local `URerc`: `map edge rc` is a simple R-cycle. -/
theorem URerc : Gc.SCycle Gc.rlink (rc.map Gc.edge) := by
  rw [← Drrrc]
  exact Gc.scycle_rev_ring E.geoGc E.URrrc

/-- The induction of the local lemma `nt_dFerc` of math-comp `chordless_perimeter`: a proper
ring that is contracted to its head by `map edge rc` and whose disk is off the ring has a
nonempty inner face disk. -/
private theorem nt_dF_aux (n : ℕ) : ∀ q : List Dc, q.length < n → Gc.SCycle Gc.rlink q →
    Gc.ProperRing q → (∀ t ∈ q.tail, t ∈ rc.map Gc.edge) → (∀ t ∈ Gc.diskN q, t ∉ rc) →
    ∃ z, z ∈ Gc.diskF q := by
  induction n with
  | zero => intro q hq; exact absurd hq (Nat.not_lt_zero _)
  | succ n IHn =>
  intro q lepn URq q_ok q_erc dN_bc
  by_contra hdF
  have dF_0 : ∀ z, z ∉ Gc.diskF q := fun z hz => hdF ⟨z, hz⟩
  have Uq : q.Nodup := Gc.scycle_uniq URq
  obtain ⟨w, q1, rfl⟩ : ∃ w q1, q = w :: q1 := by
    rcases q with _ | ⟨w, q1⟩
    · cases q_ok
    · exact ⟨w, q1, rfl⟩
  have pw : w ∈ w :: q1 := List.mem_cons_self
  have dNw : w ∈ Gc.diskN (w :: q1) := Gc.mem_diskN_of_mem _ pw
  have bcw : w ∉ rc := dN_bc w dNw
  obtain ⟨n3w, w'nw⟩ := (Gc.cubicP.1 E.cubicGc) w bcw
  have dN_N := Gc.diskN_node (w :: q1)
  have dE_E := Gc.diskE_edge E.planarGc URq
  have nn_eq : Gc.face (Gc.edge w) = Gc.node (Gc.node w) := by
    have := Gc.nodeK (Gc.node (Gc.node w))
    rwa [n3w] at this
  have f_efex : Gc.face (Gc.edge (Gc.face (Gc.edge w))) = Gc.node w := by
    rw [nn_eq]
    exact Gc.nodeK _
  have efexFnw : Gc.cface (Gc.edge (Gc.face (Gc.edge w))) (Gc.node w) := by
    have := fconnect1 Gc.face (Gc.edge (Gc.face (Gc.edge w)))
    rwa [f_efex] at this
  have dNfew : Gc.face (Gc.edge w) ∈ Gc.diskN (w :: q1) := (dN_N _ _ (Gc.edgeK w)).2 dNw
  -- A chord `c` of `w :: q1` whose chord ring is `c :: l` with `l` shorter than `q1` and
  -- included in `q1` contradicts the induction hypothesis.
  have chord : ∀ c l, c ∈ Gc.diskE (w :: q1) → c ∈ Gc.fband (w :: q1) →
      Gc.edge c ∈ Gc.fband (w :: q1) → Gc.chordRing (w :: q1) c = c :: l →
      l.length < q1.length → (∀ t ∈ l, t ∈ q1) → False := by
    intro c l dEc qFc qFec Dcr hl lq1
    have URc : Gc.SCycle Gc.rlink (c :: l) := by
      rw [← Dcr]
      exact Gc.scycle_chord_ring E.geoGc URq qFc qFec
    have c_ok : Gc.ProperRing (c :: l) := by
      rw [← Dcr]
      exact Gc.proper_chord_ring E.geoGc URq dEc qFc qFec
    have hlen : (c :: l).length < n := by
      simp only [List.length_cons] at lepn ⊢
      omega
    obtain ⟨z, hz⟩ := IHn (c :: l) hlen URc c_ok (fun t ht => q_erc t (lq1 t ht)) (by
      intro t ht
      rw [← Dcr, Gc.diskN_chord_ring E.geoGc URq q_ok dEc qFc qFec] at ht
      exact dN_bc t ht.1)
    rw [← Dcr, Gc.diskF_chord_ring E.geoGc URq q_ok dEc qFc qFec] at hz
    exact dF_0 z hz.1
  by_cases dEefex : Gc.edge (Gc.face (Gc.edge w)) ∈ Gc.diskE (w :: q1)
  · -- The chord `efex := edge (face (edge w))`.
    have pFefex : Gc.edge (Gc.face (Gc.edge w)) ∈ Gc.fband (w :: q1) := by
      by_contra hF
      exact dF_0 _ ⟨dEefex.1, hF⟩
    have pFeefex : Gc.edge (Gc.edge (Gc.face (Gc.edge w))) ∈ Gc.fband (w :: q1) := by
      rw [E.e2c]
      exact ⟨next (w :: q1) w, Embed.mem_next.2 pw,
        (Gc.cface1 _ _).1 (Embed.next_cycle URq.1 pw)⟩
    obtain ⟨q_y', efexFy'⟩ := Gc.fprojP pFefex
    obtain ⟨y', hy'⟩ : ∃ y', y' = Gc.fproj (w :: q1) (Gc.edge (Gc.face (Gc.edge w))) :=
      ⟨_, rfl⟩
    rw [← hy'] at q_y' efexFy'
    have y'w : y' ≠ w := by
      intro e
      rw [e] at efexFy'
      exact E.bridge'Gc (Gc.node w) (connect_trans (Gc.cfaceC.1 efexFnw)
        (connect_trans efexFy' (Gc.cfaceC.1 (cface_edge_node w))))
    have q1y' : y' ∈ q1 := (List.mem_cons.1 q_y').resolve_left y'w
    obtain ⟨p2, p3, Dq1⟩ := List.append_of_mem q1y'
    obtain ⟨z1, q1', Dz1⟩ : ∃ z1 q1', q1 = z1 :: q1' := by
      rcases q1 with _ | ⟨z1, q1'⟩
      · exact absurd q1y' List.not_mem_nil
      · exact ⟨z1, q1', rfl⟩
    have wz1 : w ≠ z1 := by
      intro e
      rw [Dz1, e] at Uq
      exact (List.nodup_cons.1 Uq).1 List.mem_cons_self
    have Dz : Gc.fproj (w :: q1) (Gc.face (Gc.edge w)) = z1 := by
      apply Embed.fproj_eq Gc URq (by rw [Dz1]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      have := URq.1
      rw [Dz1] at this
      exact (Gc.cface1 _ _).1 this.1
    have hy'p2 : y' ∉ p2 := by
      intro hm
      rw [Dq1] at Uq
      exact (List.nodup_append.1 (List.nodup_cons.1 Uq).2).2.2 y' hm y' List.mem_cons_self rfl
    have Dcr : Gc.chordRing (w :: q1) (Gc.edge (Gc.face (Gc.edge w))) =
        Gc.edge (Gc.face (Gc.edge w)) :: p2 := by
      unfold chordRing
      rw [E.e2c, Dz, ← hy']
      congr 1
      have hidx : (w :: q1).idxOf z1 = 1 := by
        rw [Dz1, List.idxOf_cons_ne _ wz1, List.idxOf_cons_self]
      show (rot ((w :: q1).idxOf z1) (w :: q1)).take
        ((rot ((w :: q1).idxOf z1) (w :: q1)).idxOf y') = p2
      rw [hidx, rot1_cons, Dq1, List.append_assoc, List.idxOf_append_of_notMem hy'p2,
        List.cons_append, List.idxOf_cons_self, Nat.add_zero, List.take_left' rfl]
    exact chord _ p2 dEefex pFefex pFeefex Dcr
      (by rw [Dq1]; simp only [List.length_append, List.length_cons]; omega)
      (fun t ht => by rw [Dq1]; exact List.mem_append_left _ ht)
  · -- `face (edge w)` is on the ring: it is the dart after `w`; use the chord
    -- `enx := edge (node w)`.
    have pfex : Gc.face (Gc.edge w) ∈ w :: q1 := by
      by_contra h'
      exact dEefex ((dE_E _ _ rfl).1 ⟨dNfew, h'⟩)
    obtain ⟨fex, p2, rfl⟩ : ∃ fex p2, q1 = fex :: p2 := by
      rcases q1 with _ | ⟨fex, p2⟩
      · cases q_ok
      · exact ⟨fex, p2, rfl⟩
    have Dfex : fex = Gc.face (Gc.edge w) :=
      Gc.scycle_cface URq _ (List.mem_cons_of_mem _ List.mem_cons_self) _ pfex
        (Gc.cfaceC.1 ((Gc.cface1 _ _).1 URq.1.1))
    have efex_eq : Gc.edge fex = Gc.edge (Gc.face (Gc.edge w)) := by rw [Dfex]
    -- `node w` is inside the ring
    have nw'q : Gc.node w ∉ w :: fex :: p2 := by
      intro hm
      rcases List.mem_cons.1 hm with e | hm
      · exact w'nw e
      have rc_efex : Gc.edge (Gc.face (Gc.edge w)) ∈ rc := by
        have := q_erc fex List.mem_cons_self
        rw [Dfex] at this
        obtain ⟨r, hr, er⟩ := List.mem_map.1 this
        rw [← er, E.e2c]
        exact hr
      have nw_erc : Gc.node w ∈ rc.map Gc.edge := q_erc _ hm
      have rc_fnw : Gc.face (Gc.node w) ∈ rc := by
        obtain ⟨r, hr, er⟩ := List.mem_map.1 nw_erc
        have e1 : Gc.node (Gc.face (Gc.node w)) = r := by
          apply Gc.edgeI
          rw [Gc.faceK, er]
        exact E.rc_node.1 (by rw [e1]; exact hr)
      have fnw_eq : Gc.face (Gc.node w) = Gc.edge (Gc.face (Gc.edge w)) :=
        Gc.scycle_cface E.UNrc _ rc_fnw _ rc_efex
          (connect_trans (Gc.cfaceC.1 (fconnect1 _ _)) (Gc.cfaceC.1 efexFnw))
      have ne : Gc.edge (Gc.face (Gc.edge w)) ≠ Gc.node w := by
        intro e
        rw [e] at rc_efex
        exact bcw (E.rc_node.1 rc_efex)
      have ar2 : Gc.arity (Gc.edge (Gc.face (Gc.edge w))) = 2 :=
        order_cycle (p := [Gc.edge (Gc.face (Gc.edge w)), Gc.node w])
          ⟨f_efex, fnw_eq, trivial⟩ (by simp [ne]) List.mem_cons_self
      have := (Gc.goodRingArity_iff _).1 (E.embedGc.ring _ rc_efex)
      omega
    have dEenx : Gc.edge (Gc.node w) ∈ Gc.diskE (w :: fex :: p2) :=
      (dE_E _ _ rfl).1 ⟨(dN_N w _ rfl).1 dNw, nw'q⟩
    have pFenx : Gc.edge (Gc.node w) ∈ Gc.fband (w :: fex :: p2) := ⟨w, pw, cface_edge_node w⟩
    have fex_q : fex ∈ w :: fex :: p2 := List.mem_cons_of_mem _ List.mem_cons_self
    have pFeenx : Gc.edge (Gc.edge (Gc.node w)) ∈ Gc.fband (w :: fex :: p2) := by
      rw [E.e2c]
      refine ⟨next (w :: fex :: p2) fex, Embed.mem_next.2 fex_q, ?_⟩
      have h1 := Embed.next_cycle URq.1 fex_q
      change Gc.cface (Gc.edge fex) _ at h1
      rw [efex_eq] at h1
      rw [← f_efex]
      exact (Gc.cface1 _ _).1 h1
    have Dcr : Gc.chordRing (w :: fex :: p2) (Gc.edge (Gc.node w)) = Gc.edge (Gc.node w) :: p2 := by
      have f1 : Gc.fproj (w :: fex :: p2) (Gc.edge (Gc.node w)) = w :=
        Embed.fproj_eq Gc URq pw (cface_edge_node w)
      obtain ⟨z, p3, rfl⟩ : ∃ z p3, p2 = z :: p3 := by
        rcases p2 with _ | ⟨z, p3⟩
        · exfalso
          have h1 : Gc.cface (Gc.edge fex) w := URq.1.2.1
          rw [efex_eq, Gc.cface1, f_efex] at h1
          exact E.bridge'Gc (Gc.node w) (connect_trans h1 (Gc.cfaceC.1 (cface_edge_node w)))
        · exact ⟨z, p3, rfl⟩
      have nwFz : Gc.cface (Gc.node w) z := by
        have h1 : Gc.cface (Gc.edge fex) z := URq.1.2.1
        rw [efex_eq, Gc.cface1, f_efex] at h1
        exact h1
      have f2 : Gc.fproj (w :: fex :: z :: p3) (Gc.edge (Gc.edge (Gc.node w))) = z := by
        rw [E.e2c]
        exact Embed.fproj_eq Gc URq (by simp) nwFz
      unfold chordRing
      rw [f1, f2]
      congr 1
      exact right_arc (x := w) (p1 := [fex]) (y := z) (p2 := p3) Uq
    exact chord _ p2 dEenx pFenx pFeenx Dcr (by simp only [List.length_cons]; omega)
      (fun t ht => List.mem_cons_of_mem _ ht)

/-- math-comp `chordless_perimeter`: an edge whose two ends are off the ring has an end in the
kernel. -/
theorem chordless_perimeter {x : Dc} (bc_x : x ∉ rc) (bc_ex : Gc.edge x ∉ rc) :
    x ∈ Gc.kernel rc ∨ Gc.edge x ∈ Gc.kernel rc := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨rcFx, rcFex⟩ := hne
  have rcFx' : x ∈ Gc.fband rc := by by_contra h'; exact rcFx h'
  have rcFex' : Gc.edge x ∈ Gc.fband rc := by by_contra h'; exact rcFex h'
  have EercF : Gc.fband (rc.map Gc.edge) = Gc.fband rc := by
    rw [← Drrrc, Gc.fband_rev_ring E.geoGc E.URrrc, Gc.fband_rev]
  have erc_ok : Gc.ProperRing (rc.map Gc.edge) := by
    have hne : rc ≠ [] := by
      rintro rfl
      obtain ⟨_, h', _⟩ := rcFx'
      exact List.not_mem_nil h'
    have URerc := E.URerc
    have ep := E.edge_perimeter
    generalize rc = r at hne URerc ep ⊢
    rcases r with _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, r⟩⟩⟩
    · exact absurd rfl hne
    · exfalso
      have h1 : Gc.cface (Gc.edge (Gc.edge x1)) (Gc.edge x1) := URerc.1.1
      rw [E.e2c] at h1
      exact E.bridge'Gc x1 h1
    · show Gc.edge (Gc.edge x1) ≠ Gc.edge x2
      rw [E.e2c]
      intro e
      rcases ep x1 with h' | h'
      · exact h' List.mem_cons_self
      · apply h'
        rw [e, E.e2c]
        simp
    · exact Gc.size_proper_ring (by simp)
  have rrc_ok : Gc.ProperRing rc.reverse := by
    rw [← Gc.proper_rev_ring E.geoGc, Drrrc]
    exact erc_ok
  have dNerc_bc : ∀ t, t ∈ Gc.diskN (rc.map Gc.edge) → t ∉ rc := by
    intro t ht rct
    rw [← Drrrc, Gc.diskN_rev_ring E.geoGc E.URrrc rrc_ok] at ht
    exact ht (Gc.mem_diskN_of_mem _ (List.mem_reverse.2 rct))
  -- math-comp local `nt_dFerc`
  have nt_dFerc : ∀ y, y ∈ Gc.fband (rc.map Gc.edge) → Gc.edge y ∈ Gc.fband (rc.map Gc.edge) →
      y ∈ Gc.diskE (rc.map Gc.edge) → ∃ z, z ∈ Gc.diskF (Gc.chordRing (rc.map Gc.edge) y) := by
    intro y ercFy ercFey dEy
    refine E.nt_dF_aux _ _ (Nat.lt_succ_self _)
      (Gc.scycle_chord_ring E.geoGc E.URerc ercFy ercFey)
      (Gc.proper_chord_ring E.geoGc E.URerc dEy ercFy ercFey) ?_ ?_
    · intro t ht
      exact Embed.mem_arc ht
    · intro t ht
      rw [Gc.diskN_chord_ring E.geoGc E.URerc erc_ok dEy ercFy ercFey] at ht
      exact dNerc_bc t ht.1
  -- math-comp local `dFerc_ac`
  have dFerc_ac : ∀ y, y ∈ Gc.fband (rc.map Gc.edge) → Gc.edge y ∈ Gc.fband (rc.map Gc.edge) →
      y ∈ Gc.diskE (rc.map Gc.edge) →
      ∀ z, z ∈ Gc.diskF (Gc.chordRing (rc.map Gc.edge) y) ↔ z ∈ Gc.kernel rc := by
    intro y ercFy ercFey dEy
    have dF_ac : ∀ z, z ∈ Gc.diskF (Gc.chordRing (rc.map Gc.edge) y) → z ∈ Gc.kernel rc := by
      intro z hz
      rw [Gc.diskF_chord_ring E.geoGc E.URerc erc_ok dEy ercFy ercFey] at hz
      have := hz.1.2
      rw [EercF] at this
      exact this
    have dN_dF : ∀ t, t ∈ Gc.kernel rc → t ∈ Gc.diskN (Gc.chordRing (rc.map Gc.edge) y) →
        t ∈ Gc.diskF (Gc.chordRing (rc.map Gc.edge) y) := by
      intro t act dNt
      refine ⟨dNt, fun htF => act ?_⟩
      rw [← EercF, ← Gc.fband_chord_ring E.geoGc E.URerc ercFy ercFey]
      exact Or.inl htF
    intro z
    refine ⟨dF_ac z, fun ac_z => ?_⟩
    obtain ⟨y0, dFy0⟩ := nt_dFerc y ercFy ercFey dEy
    have ac_eey0 : Gc.edge (Gc.edge y0) ∈ Gc.kernel rc := by
      rw [E.e2c]
      exact dF_ac y0 dFy0
    obtain ⟨p, ⟨eyRp, Lp, ntp⟩, -, p_hac⟩ := E.h_spoke ac_eey0 ac_z
    have prop : ∀ (l : List Dc) (w : Dc), w ∈ Gc.diskF (Gc.chordRing (rc.map Gc.edge) y) →
        path Gc.rlink w l → (∀ t ∈ l, t ∈ Gc.kernel rc) →
        last w l ∈ Gc.diskF (Gc.chordRing (rc.map Gc.edge) y) := by
      intro l
      induction l with
      | nil => intro w hw _ _; exact hw
      | cons t l ih =>
        intro w hw hp hl
        obtain ⟨wRt, tRl⟩ := hp
        have ac_t := hl t List.mem_cons_self
        have fewFt : Gc.cface (Gc.face (Gc.edge w)) t := (Gc.cface1 _ _).1 wRt
        have hfew : Gc.face (Gc.edge w) ∈ Gc.diskF (Gc.chordRing (rc.map Gc.edge) y) :=
          dN_dF _ ((acF.connect_iff fewFt).2 ac_t)
            (((Gc.diskN_node _) _ _ (Gc.edgeK w)).2 hw.1)
        have ht : t ∈ Gc.diskF (Gc.chordRing (rc.map Gc.edge) y) :=
          ((Gc.diskF_face _).connect_iff fewFt).1 hfew
        exact ih t ht tRl (fun s hs => hl s (List.mem_cons_of_mem _ hs))
    obtain ⟨y1, p', rfl⟩ := List.exists_cons_of_ne_nil ntp
    obtain ⟨eyRy1, y1Rp⟩ := eyRp
    have y0Fy1 : Gc.cface y0 y1 := by
      have := eyRy1
      change Gc.cface (Gc.edge (Gc.edge y0)) y1 at this
      rwa [E.e2c] at this
    have dFy1 := ((Gc.diskF_face _).connect_iff y0Fy1).1 dFy0
    have hlast := prop p' y1 dFy1 y1Rp (fun t ht => (p_hac t (List.mem_cons_of_mem _ ht)).1)
    exact ((Gc.diskF_face _).connect_iff Lp).1 hlast
  -- `edge x` is strictly inside `erc`
  have dEex : Gc.edge x ∈ Gc.diskE (rc.map Gc.edge) := by
    refine ⟨?_, fun h' => bc_x ((List.mem_map_of_injective Gc.edgeI).1 h')⟩
    rw [← Drrrc, Gc.diskN_rev_ring E.geoGc E.URrrc rrc_ok]
    rintro ⟨y, rrc_y, hyx⟩
    have rc_y : y ∈ rc := List.mem_reverse.1 rrc_y
    have rc_fey : Gc.face (Gc.edge y) ∈ rc := E.rc_node.1 (by rw [Gc.edgeK]; exact rc_y)
    rcases Relation.ReflTransGen.cases_head hyx with e | ⟨c, hc, _⟩
    · rw [e] at rc_fey
      exact bc_ex rc_fey
    · exact hc.1 (List.mem_reverse.2 rc_fey)
  have ercFx : x ∈ Gc.fband (rc.map Gc.edge) := by rw [EercF]; exact rcFx'
  have ercFex : Gc.edge x ∈ Gc.fband (rc.map Gc.edge) := by rw [EercF]; exact rcFex'
  have ercFeex : Gc.edge (Gc.edge x) ∈ Gc.fband (rc.map Gc.edge) := by
    rw [E.e2c]
    exact ercFx
  obtain ⟨y, dFy⟩ := nt_dFerc _ ercFex ercFeex dEex
  have ac_y : y ∈ Gc.kernel rc := (dFerc_ac _ ercFex ercFeex dEex y).1 dFy
  have dEx : x ∈ Gc.diskE (rc.map Gc.edge) :=
    ((Gc.diskE_edge E.planarGc E.URerc) x _ rfl).2 dEex
  have hy := (dFerc_ac x ercFx ercFex dEx y).2 ac_y
  rw [Gc.diskF_chord_ring E.geoGc E.URerc erc_ok dEex ercFex ercFeex, E.e2c] at dFy
  exact dFy.2 hy

/-- math-comp `fcard_adj_perimeter`: a face `x` outside the kernel has exactly two darts whose
edge is in the face band of the ring. -/
theorem fcard_adj_perimeter {x : Dc} (hx : x ∉ Gc.kernel rc) :
    {z | Gc.cface x z ∧ Gc.edge z ∈ Gc.fband rc}.ncard = 2 := by
  have hxF : x ∈ Gc.fband rc := by by_contra h'; exact hx h'
  obtain ⟨y, rc_y, xFy⟩ := hxF
  have rc_ny : Gc.node y ∈ rc := E.rc_node.2 rc_y
  have ny_ne : Gc.edge (Gc.node y) ≠ y := by
    intro e
    rcases E.edge_perimeter (Gc.node y) with h' | h'
    · exact h' rc_ny
    · exact h' (by rw [e]; exact rc_y)
  have rcFey : Gc.edge y ∈ Gc.fband rc :=
    ⟨Gc.face (Gc.edge y), E.rc_node.1 (by rw [Gc.edgeK]; exact rc_y), fconnect1 _ _⟩
  have hset : {z | Gc.cface x z ∧ Gc.edge z ∈ Gc.fband rc} = {y, Gc.edge (Gc.node y)} := by
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨xFz, ezF⟩
      by_contra hz
      have hz1 : z ≠ y := fun e => hz (Or.inl e)
      have hz2 : z ≠ Gc.edge (Gc.node y) := fun e => hz (Or.inr e)
      have yFz : Gc.cface y z := connect_trans (Gc.cfaceC.1 xFy) xFz
      have bc_z : z ∉ rc := fun rcz => hz1 (Gc.scycle_cface E.UNrc _ rcz _ rc_y (Gc.cfaceC.1 yFz))
      have bc_ez : Gc.edge z ∉ rc := by
        intro rcez
        apply hz2
        apply Gc.scycle_cface E.URerc
        · rw [← E.e2c z]
          exact List.mem_map_of_mem rcez
        · exact List.mem_map_of_mem rc_ny
        · exact connect_trans (Gc.cfaceC.1 yFz) (Gc.cfaceC.1 (cface_edge_node y))
      rcases E.chordless_perimeter bc_z bc_ez with h' | h'
      · exact h' ⟨y, rc_y, Gc.cfaceC.1 yFz⟩
      · exact h' ezF
    · rintro (e | e)
      · rw [e]
        exact ⟨xFy, rcFey⟩
      · rw [e]
        refine ⟨connect_trans xFy (Gc.cfaceC.1 (cface_edge_node y)), ?_⟩
        rw [E.e2c]
        exact Gc.ring_fband rc _ rc_ny
  rw [hset, Set.ncard_pair (Ne.symm ny_ne)]

/-- The face of a dart `x` outside the kernel splits into the two darts whose edge is in the
face band of the ring and those whose edge is in the kernel (math-comp `cardID`). -/
private theorem arity_split {x : Dc} (hx : x ∉ Gc.kernel rc) :
    Gc.arity x = 2 + {z | Gc.cface x z ∧ Gc.edge z ∈ Gc.kernel rc}.ncard := by
  have hsplit := Set.ncard_inter_add_ncard_sdiff_eq_ncard {z | Gc.cface x z}
    {z | Gc.edge z ∈ Gc.fband rc}
  have h2 : ({z | Gc.cface x z} ∩ {z | Gc.edge z ∈ Gc.fband rc}).ncard = 2 :=
    E.fcard_adj_perimeter hx
  have e : Gc.arity x = {z | Gc.cface x z}.ncard := rfl
  have e2 : ({z | Gc.cface x z} \ {z | Gc.edge z ∈ Gc.fband rc}) =
      {z | Gc.cface x z ∧ Gc.edge z ∈ Gc.kernel rc} := rfl
  rw [e2] at hsplit
  omega

/-- math-comp `adj_kernel_min`: a face outside the kernel is adjacent to the kernel. -/
theorem adj_kernel_min {x : Dc} (hx : x ∉ Gc.kernel rc) :
    ∃ y ∈ Gc.kernel rc, Gc.cface x (Gc.edge y) := by
  have hxF : x ∈ Gc.fband rc := by by_contra h'; exact hx h'
  obtain ⟨y, rc_y, xFy⟩ := hxF
  have ar := (Gc.goodRingArity_iff y).1 (E.embedGc.ring y rc_y)
  rw [← Gc.arity_cface xFy, E.arity_split hx] at ar
  obtain ⟨z, xFz, ezA⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
    {z | Gc.cface x z ∧ Gc.edge z ∈ Gc.kernel rc}.ncard ≠ 0)
  exact ⟨Gc.edge z, ezA, by rw [E.e2c]; exact xFz⟩

/-- math-comp `adj_kernel_max`: a face outside the kernel has at most four darts whose edge is
in the kernel. -/
theorem adj_kernel_max {x : Dc} (hx : x ∉ Gc.kernel rc) :
    {z | Gc.cface x z ∧ Gc.edge z ∈ Gc.kernel rc}.ncard ≤ 4 := by
  have hxF : x ∈ Gc.fband rc := by by_contra h'; exact hx h'
  obtain ⟨y, rc_y, xFy⟩ := hxF
  have ar := (Gc.goodRingArity_iff y).1 (E.embedGc.ring y rc_y)
  rw [← Gc.arity_cface xFy, E.arity_split hx] at ar
  omega

end EmbedHyps

end Hypermap

end FourColor
