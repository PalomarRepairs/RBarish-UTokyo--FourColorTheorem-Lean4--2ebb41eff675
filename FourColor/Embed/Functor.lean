/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Embed.Basic

/-!
# The embedding functor lemma (part of the port of `embed.v`)

`E.embed_functor` (math-comp `embed_functor`): under the section hypotheses
`E : Hypermap.EmbedHyps Gm Gc rc h`, the preembedding `h` commutes with `edge` on the darts `x`
such that both `x` and `edge x` are in the kernel `ac := kernel rc`.

The Coq proof is a chain of three `suffices`; here they are the private lemmas
`functor_core` (the last one: no dart `x` outside `hc := edge_central h` starts a ring
`x :: p` with `p ⊆ hc` whose disk lies in the kernel, by induction on the size of the disk),
`functor_step` (the middle one) and the theorem itself.

## Porting notes

* The induction of `functor_core` is on a bound `n` of `(diskN (x :: p)).ncard` (Coq
  `#|diskN (x :: p)| < n`).
* In the case `node x ∈ hc`, `node (node x) ∉ hc`, the Coq proof takes the prefix
  `take (find (cface ennx) p1) p1` of `p1 := rcons p (edge (node x))`; here the list is split
  at its first dart in the face of `ennx` with `Embed.exists_first` (or is taken whole when
  there is none), and in the case `node x ∉ hc` the spoke path `q1` is split in the same way at
  its first dart in `fband p1`.
* Both cases end by showing `diskN q ⊆ diskN (x :: p)` for the new ring `q`: the Coq proof
  follows the `dlink` paths with `diskE_edge`; here `Embed.diskN_subset` reduces this to the
  darts of `q` and to the darts of `x :: p` off `q` (the only non-trivial `dlink` steps), and the
  R-path arguments use `Embed.diskN_path` and `Embed.diskN_path_rev`.
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

/-- The core of math-comp `embed_functor` (its last `suffices`): no dart `x ∉ hc` starts a
simple R-cycle `x :: p` with `p ⊆ hc` whose disk is included in the kernel; by induction on a
bound `n` of the size of the disk. -/
private theorem functor_core (n : ℕ) : ∀ (x : Dc) (p : List Dc),
    (Gc.diskN (x :: p)).ncard < n → x ∉ Gc.edgeCentral Gm h → Gc.SCycle Gc.rlink (x :: p) →
    (∀ y ∈ p, y ∈ Gc.edgeCentral Gm h) → (∀ y ∈ Gc.diskN (x :: p), y ∈ Gc.kernel rc) →
    False := by
  induction n with
  | zero => intro x p h0; exact absurd h0 (Nat.not_lt_zero _)
  | succ n IHn =>
  intro x p le_dN_n hc'x URp p_hc dN_ac
  have dNx : x ∈ Gc.diskN (x :: p) := Gc.mem_diskN_of_mem _ List.mem_cons_self
  -- The end of both cases: the induction hypothesis for a ring `w :: t` whose disk is a
  -- subset of the disk of `x :: p` that misses `x`.
  have finish : ∀ (w : Dc) (t : List Dc), w ∉ Gc.edgeCentral Gm h →
      Gc.SCycle Gc.rlink (w :: t) → (∀ z ∈ t, z ∈ Gc.edgeCentral Gm h) →
      x ∉ Gc.diskN (w :: t) → (∀ z ∈ w :: t, z ∈ Gc.diskN (x :: p)) →
      (∀ y ∈ x :: p, y ∉ w :: t → y ∈ Gc.diskN (w :: t) → False) → False := by
    intro w t hc'w URq t_hc dNq'x hstart hstep
    have dNq_dN : Gc.diskN (w :: t) ⊆ Gc.diskN (x :: p) :=
      Embed.diskN_subset Gc hstart (fun y hyq _ hq'y hy => hstep y hy hq'y hyq)
    refine IHn w t ?_ hc'w URq t_hc (fun y hy => dN_ac y (dNq_dN hy))
    have hlt : (Gc.diskN (w :: t)).ncard < (Gc.diskN (x :: p)).ncard :=
      Set.ncard_lt_ncard ((Set.ssubset_iff_subset_ne).2
        ⟨dNq_dN, fun e => dNq'x (by rw [e]; exact dNx)⟩)
    omega
  have dN_node : ∀ z, z ∈ Gc.diskN (x :: p) → Gc.node z ∈ Gc.diskN (x :: p) :=
    fun z hz => ((Gc.diskN_node _) z _ rfl).1 hz
  have dNnx := dN_node x dNx
  have dNnnx := dN_node _ dNnx
  have cycRp : path Gc.rlink x (p ++ [x]) := URp.1
  have UpF : Gc.Simple (x :: p) := URp.2
  have Up : (x :: p).Nodup := Gc.simple_uniq UpF
  have ac_x : x ∈ Gc.kernel rc := dN_ac x dNx
  obtain ⟨n3x, x'nx⟩ := (Gc.cubicP.1 E.cubicGc) x (ac_bc ac_x)
  have p_ne : p ≠ [] := by
    rintro rfl
    exact E.bridge'Gc x (Gc.cfaceC.1 cycRp.1)
  obtain ⟨enx, henx⟩ : ∃ e, e = Gc.edge (Gc.node x) := ⟨_, rfl⟩
  have enxFx : Gc.cface enx x := henx ▸ cface_edge_node x
  have eenx : Gc.edge enx = Gc.node x := by rw [henx]; exact E.e2c _
  have xRp1 : path Gc.rlink x (p ++ [enx]) := by
    rw [path_concat] at cycRp ⊢
    exact ⟨cycRp.1, (Gc.rlinkFr (Gc.cfaceC.1 enxFx) _).1 cycRp.2⟩
  have Up1 : Gc.Simple (p ++ [enx]) := by
    rw [Gc.simple_rcons]
    rw [Gc.simple_cons] at UpF
    exact ⟨fun hF => UpF.1 (((Gc.fbandF p).connect_iff enxFx).1 hF), UpF.2⟩
  have dEdE := Gc.diskE_edge E.planarGc URp
  by_cases hc_nx : Gc.node x ∈ Gc.edgeCentral Gm h
  · have ac_nx := dN_ac _ dNnx
    by_cases hc_nnx : Gc.node (Gc.node x) ∈ Gc.edgeCentral Gm h
    · -- Both `node x` and `node (node x)` are edge-central, hence so is `x`.
      apply hc'x
      show h (Gc.edge x) = Gm.edge (h x)
      have e1 := E.h_node ac_x hc_nx
      have e2 := E.h_node ac_nx hc_nnx
      have e3 := E.h_edge_node (dN_ac _ dNnnx)
      rw [n3x, e2, e1, E.n3m] at e3
      exact e3
    -- The ring `ennx :: a`, for a prefix `a` of `p ++ [enx]`.
    obtain ⟨ennx, hennx⟩ : ∃ e, e = Gc.edge (Gc.node (Gc.node x)) := ⟨_, rfl⟩
    have ennxFnx : Gc.cface ennx (Gc.node x) := hennx ▸ cface_edge_node (Gc.node x)
    have eennx : Gc.edge ennx = Gc.node (Gc.node x) := by rw [hennx]; exact E.e2c _
    have nnx_eq : Gc.face (Gc.edge x) = Gc.node (Gc.node x) := by
      have := Gc.nodeK (Gc.node (Gc.node x))
      rwa [n3x] at this
    have hc'ennx : ennx ∉ Gc.edgeCentral Gm h := by
      rw [hennx]
      exact fun hc => hc_nnx ((E.hcE _).1 hc)
    have nnx'xp : Gc.node (Gc.node x) ∉ x :: p := by
      intro hm
      rcases List.mem_cons.1 hm with e | hm
      · apply x'nx
        have := congrArg Gc.node e
        rw [n3x] at this
        exact this.symm
      · exact hc_nnx (p_hc _ hm)
    have dNennx : ennx ∈ Gc.diskN (x :: p) :=
      ((dEdE _ ennx hennx.symm).1 ⟨dNnnx, nnx'xp⟩).1
    have ennxRp1 : path Gc.rlink ennx (p ++ [enx]) := by
      obtain ⟨x0, p0, rfl⟩ := List.exists_cons_of_ne_nil p_ne
      obtain ⟨xRx0, x0R⟩ := xRp1
      refine ⟨?_, x0R⟩
      show Gc.cface (Gc.edge ennx) x0
      rw [eennx, ← nnx_eq]
      exact (Gc.cface1 _ _).1 xRx0
    -- `x` is not in the disk of the new ring.
    have dNq'x_of : ∀ a : List Dc, Gc.SCycle Gc.rlink (ennx :: a) →
        (∀ t ∈ a, t ∈ Gc.edgeCentral Gm h) → x ∉ Gc.diskN (ennx :: a) := by
      intro a URq a_hc dNq_x
      have nt_q : Gc.ProperRing (ennx :: a) := by
        rcases a with _ | ⟨x1, _ | ⟨x2, a⟩⟩
        · exact absurd (Gc.cfaceC.1 URq.1.1) (E.bridge'Gc ennx)
        · show Gc.edge ennx ≠ x1
          intro e
          apply hc_nnx
          rw [← eennx, e]
          exact a_hc x1 List.mem_cons_self
        · exact Gc.size_proper_ring (by simp)
      have hq := Gc.diskN_node (ennx :: a)
      have h1 : Gc.node x ∈ Gc.diskN (ennx :: a) := (hq x _ rfl).1 dNq_x
      have h2 : Gc.node (Gc.node x) ∈ Gc.diskN (ennx :: a) := (hq _ _ rfl).1 h1
      exact Gc.diskN_edge_ring E.geoGc URq nt_q List.mem_cons_self (by rw [eennx]; exact h2)
    have p1_hc : ∀ t ∈ p ++ [enx], t ∈ Gc.edgeCentral Gm h := by
      intro t ht
      rcases List.mem_append.1 ht with ht | ht
      · exact p_hc t ht
      · rw [List.mem_singleton.1 ht, henx]
        exact (E.hcE _).2 hc_nx
    by_cases hF1 : ∃ t ∈ p ++ [enx], Gc.cface ennx t
    · -- `a` is the prefix of `p ++ [enx]` before its first dart `b` in the face of `ennx`.
      obtain ⟨a, b, c, Dp1, a'F, ennxFb⟩ := Embed.exists_first _ _ hF1
      have b'enx : b ≠ enx := by
        intro e
        rw [e] at ennxFb
        apply E.bridge'Gc (Gc.node x)
        rw [← henx]
        exact connect_trans (Gc.cfaceC.1 ennxFnx) ennxFb
      obtain ⟨c', rfl, Dp⟩ : ∃ c', c = c' ++ [enx] ∧ p = a ++ b :: c' := by
        rcases List.eq_nil_or_concat c with hc0 | ⟨c', e', hc0⟩
        · subst hc0
          exfalso
          have := (List.append_inj' Dp1 rfl).2
          exact b'enx (List.singleton_inj.1 this).symm
        · rw [List.concat_eq_append] at hc0
          subst hc0
          have e1 : a ++ b :: (c' ++ [e']) = (a ++ b :: c') ++ [e'] := by simp
          have := List.append_inj' (Dp1.trans e1) rfl
          refine ⟨c', ?_, this.1⟩
          rw [List.singleton_inj.1 this.2]
      have a_p : ∀ t ∈ a, t ∈ p := fun t ht => by rw [Dp]; exact List.mem_append_left _ ht
      have a_hc : ∀ t ∈ a, t ∈ Gc.edgeCentral Gm h := fun t ht => p_hc t (a_p t ht)
      have URq : Gc.SCycle Gc.rlink (ennx :: a) := by
        refine ⟨?_, ?_⟩
        · show path Gc.rlink ennx (a ++ [ennx])
          rw [Dp1, path_append] at ennxRp1
          rw [path_concat]
          exact ⟨ennxRp1.1, (Gc.rlinkFr (Gc.cfaceC.1 ennxFb) _).1 ennxRp1.2.1⟩
        · rw [Gc.simple_cons]
          refine ⟨fun ⟨t, ht, e⟩ => a'F t ht e, ?_⟩
          rw [Dp1, Gc.simple_cat] at Up1
          exact Up1.1
      refine finish ennx a hc'ennx URq a_hc (dNq'x_of a URq a_hc) ?_ ?_
      · intro z hz
        rcases List.mem_cons.1 hz with hz | hz
        · rw [hz]; exact dNennx
        · exact Gc.mem_diskN_of_mem _ (List.mem_cons_of_mem _ (a_p z hz))
      · intro y xpy q'y dNq_y
        rcases List.mem_cons.1 xpy with hy | py
        · rw [hy] at dNq_y
          exact dNq'x_of a URq a_hc dNq_y
        rw [Dp] at py
        rcases List.mem_append.1 py with ya | ybc
        · exact q'y (List.mem_cons_of_mem _ ya)
        -- `y` is after `b` on the ring: follow the ring from `y` back to `x`.
        obtain ⟨r0, r1, Dbc⟩ := List.append_of_mem ybc
        have Dp_full : p = a ++ (r0 ++ y :: r1) := by rw [Dp, Dbc]
        have yRr : path Gc.rlink y (r1 ++ [x]) := by
          have e1 : p ++ [x] = (a ++ r0) ++ y :: (r1 ++ [x]) := by rw [Dp_full]; simp
          have := cycRp
          rw [e1] at this
          exact path.of_append_cons this
        have Uxp := Up
        rw [Dp_full] at Uxp
        have hbc : (b :: c').Nodup := by
          have := Up
          rw [Dp] at this
          exact (List.nodup_append.1 (List.nodup_cons.1 this).2).2.1
        have r1_c' : ∀ t ∈ r1, t ∈ c' := by
          intro t ht
          rcases r0 with _ | ⟨b0, r0⟩
          · simp only [List.nil_append, List.cons.injEq] at Dbc
            rw [Dbc.2]
            exact ht
          · simp only [List.cons_append, List.cons.injEq] at Dbc
            rw [Dbc.2]
            exact List.mem_append_right _ (List.mem_cons_of_mem _ ht)
        have hl : ∀ t ∈ r1 ++ [x], t ∉ Gc.fband (ennx :: a) := by
          rintro t ht ⟨s, hs, tFs⟩
          obtain ⟨s', hs', tFs'⟩ : ∃ s' ∈ a ++ [b], Gc.cface t s' := by
            rcases List.mem_cons.1 hs with hs | hs
            · rw [hs] at tFs
              exact ⟨b, List.mem_append_right _ List.mem_cons_self, connect_trans tFs ennxFb⟩
            · exact ⟨s, List.mem_append_left _ hs, tFs⟩
          have s'p : s' ∈ p := by
            rw [Dp]
            rcases List.mem_append.1 hs' with h' | h'
            · exact List.mem_append_left _ h'
            · rw [List.mem_singleton.1 h']
              exact List.mem_append_right _ List.mem_cons_self
          have t_xp : t ∈ x :: p := by
            rcases List.mem_append.1 ht with h' | h'
            · rw [Dp_full]
              exact List.mem_cons_of_mem _
                (List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_of_mem _ h')))
            · rw [List.mem_singleton.1 h']
              exact List.mem_cons_self
          have e := Gc.scycle_cface URp t t_xp s' (List.mem_cons_of_mem _ s'p) tFs'
          rw [← e] at hs' s'p
          rcases List.mem_append.1 ht with ht1 | ht1
          · rcases List.mem_append.1 hs' with ha | hb
            · exact (List.nodup_append.1 (List.nodup_cons.1 Uxp).2).2.2 t ha t
                (List.mem_append_right _ (List.mem_cons_of_mem _ ht1)) rfl
            · rw [List.mem_singleton.1 hb] at ht1
              exact (List.nodup_cons.1 hbc).1 (r1_c' b ht1)
          · rw [List.mem_singleton.1 ht1] at s'p
            exact (List.nodup_cons.1 Up).1 s'p
        exact dNq'x_of a URq a_hc
          (Embed.diskN_path Gc dNq_y yRr hl x (List.mem_append_right _ List.mem_cons_self))
    · -- No dart of `p ++ [enx]` is in the face of `ennx`: the new ring is
      -- `ennx :: p ++ [enx]`.
      have F'p1 : ∀ t ∈ p ++ [enx], ¬ Gc.cface ennx t := fun t ht e => hF1 ⟨t, ht, e⟩
      have URq : Gc.SCycle Gc.rlink (ennx :: (p ++ [enx])) := by
        refine ⟨?_, ?_⟩
        · show path Gc.rlink ennx ((p ++ [enx]) ++ [ennx])
          rw [path_concat, last_concat]
          refine ⟨ennxRp1, ?_⟩
          show Gc.cface (Gc.edge enx) ennx
          rw [eenx]
          exact Gc.cfaceC.1 ennxFnx
        · rw [Gc.simple_cons]
          exact ⟨fun ⟨t, ht, e⟩ => F'p1 t ht e, Up1⟩
      refine finish ennx (p ++ [enx]) hc'ennx URq p1_hc (dNq'x_of _ URq p1_hc) ?_ ?_
      · intro z hz
        rcases List.mem_cons.1 hz with hz | hz
        · rw [hz]; exact dNennx
        rcases List.mem_append.1 hz with hz | hz
        · exact Gc.mem_diskN_of_mem _ (List.mem_cons_of_mem _ hz)
        · rw [List.mem_singleton.1 hz]
          have nx'xp : Gc.node x ∉ x :: p := by
            intro hm
            rcases List.mem_cons.1 hm with e | hm
            · exact x'nx e
            · exact F'p1 (Gc.node x) (List.mem_append_left _ hm) ennxFnx
          exact ((dEdE _ enx henx.symm).1 ⟨dNnx, nx'xp⟩).1
      · intro y xpy q'y dNq_y
        rcases List.mem_cons.1 xpy with hy | py
        · rw [hy] at dNq_y
          exact dNq'x_of _ URq p1_hc dNq_y
        · exact q'y (List.mem_cons_of_mem _ (List.mem_append_left _ py))
  · -- `node x` is not edge-central: follow the spoke path from `enx`.
    have nx'xp : Gc.node x ∉ x :: p := by
      intro hm
      rcases List.mem_cons.1 hm with e | hm
      · exact x'nx e
      · exact hc_nx (p_hc _ hm)
    have dNenx : enx ∈ Gc.diskN (x :: p) := ((dEdE _ enx henx.symm).1 ⟨dNnx, nx'xp⟩).1
    have ac_eenx : Gc.edge enx ∈ Gc.kernel rc := by
      rw [eenx]
      exact dN_ac _ dNnx
    obtain ⟨q1, ⟨enxRq1, Lq1, ntq1⟩, Uq1, q1_ac⟩ := E.h_spoke ac_eenx (dN_ac _ dNenx)
    have p1Fq1 : ∃ t ∈ q1, t ∈ Gc.fband (p ++ [enx]) :=
      ⟨last enx q1, last_mem_of_ne_nil _ ntq1, enx,
        List.mem_append_right _ List.mem_cons_self, Lq1⟩
    obtain ⟨q2, y1, q1', Dq1, q2'F, y1F⟩ := Embed.exists_first _ _ p1Fq1
    obtain ⟨y, p1y, y1Fy⟩ := y1F
    have Upq2 : ∀ t ∈ p ++ [enx], t ∉ Gc.fband q2 := by
      rintro t ht ⟨s, hs, tFs⟩
      exact q2'F s hs ⟨t, ht, Gc.cfaceC.1 tFs⟩
    obtain ⟨p2, p3, Dp⟩ := List.append_of_mem p1y
    have Lp3 : last y p3 = enx := by
      have e : x :: (p ++ [enx]) = (x :: p2) ++ y :: p3 := by rw [Dp]; rfl
      have := last_eq_of_cons_eq_append e
      rw [last_concat] at this
      exact this.symm
    have Dp' : p = p2 ++ belast y p3 := by
      have e := lastI y p3
      rw [Lp3] at e
      have Dp2 := Dp
      rw [e, ← List.append_assoc] at Dp2
      exact List.append_cancel_right Dp2
    have Dq3 : (q2 ++ belast y p3) ++ [enx] = q2 ++ y :: p3 := by
      rw [List.append_assoc, ← Lp3, ← lastI]
    have URq : Gc.SCycle Gc.rlink (enx :: (q2 ++ belast y p3)) := by
      refine ⟨?_, ?_⟩
      · show path Gc.rlink enx ((q2 ++ belast y p3) ++ [enx])
        rw [Dq3, path_append]
        rw [Dq1, path_append] at enxRq1
        refine ⟨enxRq1.1, (Gc.rlinkFr y1Fy _).1 enxRq1.2.1, ?_⟩
        have := xRp1
        rw [Dp] at this
        exact path.of_append_cons this
      · refine (Gc.simple_rot 1 _).1 ?_
        have e : (enx :: (q2 ++ belast y p3)).rotate 1 = q2 ++ y :: p3 := by
          rw [List.rotate_cons_succ, List.rotate_zero, Dq3]
        rw [e, Gc.simple_cat]
        rw [Dq1, Gc.simple_cat] at Uq1
        have Up1' := Up1
        rw [Dp, Gc.simple_cat] at Up1'
        refine ⟨Uq1.1, ?_, Up1'.2.2⟩
        rintro ⟨t, ht, tF⟩
        exact Upq2 t (by rw [Dp]; exact List.mem_append_right _ ht) tF
    have q3_hc : ∀ t ∈ q2 ++ belast y p3, t ∈ Gc.edgeCentral Gm h := by
      intro t ht
      rcases List.mem_append.1 ht with ht | ht
      · exact (q1_ac t (by rw [Dq1]; exact List.mem_append_left _ ht)).2
      · exact p_hc t (by rw [Dp']; exact List.mem_append_right _ ht)
    have dNq'x : x ∉ Gc.diskN (enx :: (q2 ++ belast y p3)) := by
      intro dNq_x
      have nt_q : Gc.ProperRing (enx :: (q2 ++ belast y p3)) := by
        generalize q2 ++ belast y p3 = q3 at URq q3_hc ⊢
        rcases q3 with _ | ⟨x1, _ | ⟨x2, q3⟩⟩
        · exact absurd (Gc.cfaceC.1 URq.1.1) (E.bridge'Gc enx)
        · show Gc.edge enx ≠ x1
          intro e
          apply hc_nx
          rw [← eenx, e]
          exact q3_hc x1 List.mem_cons_self
        · exact Gc.size_proper_ring (by simp)
      have h1 : Gc.node x ∈ Gc.diskN (enx :: (q2 ++ belast y p3)) :=
        ((Gc.diskN_node _) x _ rfl).1 dNq_x
      exact Gc.diskN_edge_ring E.geoGc URq nt_q List.mem_cons_self (by rw [eenx]; exact h1)
    have hxpF : ∀ t, t ∈ Gc.fband (x :: p) → t ∈ Gc.fband (p ++ [enx]) := by
      rintro t ⟨s, hs, tFs⟩
      rcases List.mem_cons.1 hs with hs | hs
      · rw [hs] at tFs
        exact ⟨enx, List.mem_append_right _ List.mem_cons_self,
          connect_trans tFs (Gc.cfaceC.1 enxFx)⟩
      · exact ⟨s, List.mem_append_left _ hs, tFs⟩
    have hc'enx : enx ∉ Gc.edgeCentral Gm h := by
      rw [henx]
      exact fun hc => hc_nx ((E.hcE _).1 hc)
    refine finish enx (q2 ++ belast y p3) hc'enx URq q3_hc dNq'x ?_ ?_
    · intro z hz
      rcases List.mem_cons.1 hz with hz | hz
      · rw [hz]; exact dNenx
      rcases List.mem_append.1 hz with hz | hz
      · have enxRq2 : path Gc.rlink enx q2 := by
          have := enxRq1
          rw [Dq1, path_append] at this
          exact this.1
        exact Embed.diskN_path Gc dNenx enxRq2 (fun t ht htF => q2'F t ht (hxpF t htF)) z hz
      · exact Gc.mem_diskN_of_mem _
          (List.mem_cons_of_mem _ (by rw [Dp']; exact List.mem_append_right _ hz))
    · intro y' xpy' q'y' dNq_y'
      have hy' : y' ∈ x :: p2 ∨ y' ∈ belast y p3 := by
        rw [Dp'] at xpy'
        rcases List.mem_cons.1 xpy' with e | h'
        · rw [e]
          exact Or.inl List.mem_cons_self
        · rcases List.mem_append.1 h' with h'' | h''
          · exact Or.inl (List.mem_cons_of_mem _ h'')
          · exact Or.inr h''
      rcases hy' with xp2y' | hy'
      · obtain ⟨p4, p5, Dp2, Lp4⟩ := splitPl xp2y'
        have xRp4 : path Gc.rlink x p4 := by
          have := xRp1
          rw [Dp, Dp2, List.append_assoc] at this
          exact (path_append.1 this).1
        have Uqp2 : ∀ t ∈ p2, t ∉ Gc.fband (enx :: (q2 ++ belast y p3)) := by
          rintro t ht ⟨u, hu, tFu⟩
          have hu' : u ∈ q2 ++ y :: p3 := by
            rw [← Dq3]
            rcases List.mem_cons.1 hu with hu | hu
            · rw [hu]
              exact List.mem_append_right _ List.mem_cons_self
            · exact List.mem_append_left _ hu
          rcases List.mem_append.1 hu' with hu' | hu'
          · exact Upq2 t (by rw [Dp]; exact List.mem_append_left _ ht) ⟨u, hu', tFu⟩
          · have Up1' := Up1
            rw [Dp, Gc.simple_cat] at Up1'
            exact Up1'.2.1 ⟨u, hu', t, ht, Gc.cfaceC.1 tFu⟩
        exact dNq'x (Embed.diskN_path_rev Gc xRp4
          (fun t ht => Uqp2 t (by rw [Dp2]; exact List.mem_append_left _ ht))
          (by rw [Lp4]; exact dNq_y'))
      · exact q'y' (List.mem_cons_of_mem _ (List.mem_append_right _ hy'))

/-- The middle `suffices` of math-comp `embed_functor`: no dart `x ∈ ac` outside `hc` starts a
simple R-cycle `x :: p` with `p ⊆ ac ∩ hc`. -/
private theorem functor_step : ¬ ∃ x, x ∈ Gc.kernel rc ∧ x ∉ Gc.edgeCentral Gm h ∧
    ∃ p, Gc.SCycle Gc.rlink (x :: p) ∧
      ∀ y ∈ p, y ∈ Gc.kernel rc ∧ y ∈ Gc.edgeCentral Gm h := by
  rintro ⟨x, ac_x, hc'x, p, URp, hac_p⟩
  have ac_xp : ∀ y ∈ x :: p, y ∈ Gc.kernel rc := by
    intro y hy
    rcases List.mem_cons.1 hy with hy | hy
    · rw [hy]; exact ac_x
    · exact (hac_p y hy).1
  by_cases dFrc : ∃ z ∈ rc, z ∈ Gc.diskF (x :: p)
  · -- The disk of `x :: p` meets the ring: use the reverse ring `edge x :: revRing p`.
    obtain ⟨z0, rcz0, dFz0⟩ := dFrc
    have nt_xp : Gc.ProperRing (x :: p) := by
      rcases p with _ | ⟨x2, _ | ⟨x3, p⟩⟩
      · exact absurd (Gc.cfaceC.1 URp.1.1) (E.bridge'Gc x)
      · show Gc.edge x ≠ x2
        intro e
        apply hc'x
        rw [← E.hcE, e]
        exact (hac_p x2 List.mem_cons_self).2
      · exact Gc.size_proper_ring (by simp)
    have hrot : (x :: p).rotate 1 = p ++ [x] := by
      rw [List.rotate_cons_succ, List.rotate_zero]
    have URp1 : Gc.SCycle Gc.rlink (p ++ [x]) := by
      rw [← hrot]
      exact (Gc.rot_scycle 1 _ _).2 URp
    have nt_p1 : Gc.ProperRing (p ++ [x]) := by
      rw [← hrot]
      exact (Gc.proper_ring_rot E.plainGc 1 _).2 nt_xp
    have rr : Gc.revRing (p ++ [x]) = Gc.edge x :: Gc.revRing p := by
      simp [revRing]
    have URq := Gc.scycle_rev_ring E.geoGc URp1
    rw [rr] at URq
    refine functor_core E _ (Gc.edge x) (Gc.revRing p) (Nat.lt_succ_self _)
      (fun hc => hc'x ((E.hcE x).1 hc)) URq ?_ ?_
    · intro y hy
      exact (E.hcE y).1 (hac_p _ ((Gc.mem_rev_ring E.geoGc).1 hy)).2
    · intro y dNy
      rw [← rr, Gc.diskN_rev_ring E.geoGc URp1 nt_p1, ← hrot, Gc.diskN_rot] at dNy
      rintro ⟨z, rcz, yFz⟩
      have z_dF : z ∈ Gc.diskF (x :: p) := by
        refine ⟨?_, ?_⟩
        · have hz0z : Gc.cnode z0 z := (fconnect_cycle E.cycNrc rcz0).2 rcz
          exact ((Gc.diskN_node _).connect_iff hz0z).1 dFz0.1
        · rintro ⟨t, xpt, zFt⟩
          exact ac_xp t xpt ⟨z, rcz, Gc.cfaceC.1 zFt⟩
      exact dNy (((Gc.diskF_face _).connect_iff yFz).2 z_dF).1
  · -- The disk of `x :: p` misses the ring: it is included in the kernel.
    refine functor_core E _ x p (Nat.lt_succ_self _) hc'x URp (fun y hy => (hac_p y hy).2) ?_
    intro y dNy
    by_cases xpFy : y ∈ Gc.fband (x :: p)
    · obtain ⟨z, pz, yFz⟩ := xpFy
      exact (acF.connect_iff yFz).2 (ac_xp z pz)
    · rintro ⟨z, rcz, yFz⟩
      exact dFrc ⟨z, rcz, ((Gc.diskF_face _).connect_iff yFz).1 ⟨dNy, xpFy⟩⟩

/-- math-comp `embed_functor`: `h` commutes with `edge` at the darts `x` such that `x` and
`edge x` are in the kernel. -/
theorem embed_functor {x : Dc} (hx : x ∈ Gc.kernel rc) (hex : Gc.edge x ∈ Gc.kernel rc) :
    h (Gc.edge x) = Gm.edge (h x) := by
  by_contra hc'x
  obtain ⟨p, ⟨xRp, Lp, ntp⟩, Up, p_ac⟩ := E.h_spoke hex hx
  obtain ⟨p', y, rfl⟩ : ∃ p' y, p = p' ++ [y] := by
    rcases List.eq_nil_or_concat p with h0 | ⟨p', y, h0⟩
    · exact absurd h0 ntp
    · exact ⟨p', y, by rw [h0, List.concat_eq_append]⟩
  rw [last_concat] at Lp
  apply E.functor_step
  refine ⟨x, hx, hc'x, p', ⟨?_, ?_⟩, fun z hz => p_ac z (List.mem_append_left _ hz)⟩
  · show path Gc.rlink x (p' ++ [x])
    rw [path_concat] at xRp ⊢
    exact ⟨xRp.1, (Gc.rlinkFr Lp _).1 xRp.2⟩
  · rw [Gc.simple_rcons] at Up
    rw [Gc.simple_cons]
    exact ⟨fun hF => Up.1 (((Gc.fbandF p').connect_iff Lp).2 hF), Up.2⟩

end EmbedHyps

end Hypermap

end FourColor
