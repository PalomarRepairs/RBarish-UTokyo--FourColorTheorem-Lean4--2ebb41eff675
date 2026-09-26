/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Embed.Functor

/-!
# Face morphisms and pre-homomorphic rings (part of the port of `embed.v`)

Under the section hypotheses `E : Hypermap.EmbedHyps Gm Gc rc h`:

* `E.cface_ac_h`, `E.cface_h_ac` : on the kernel `ac`, `h` maps faces onto faces (math-comp
  section `Let`s `cface_ac_h`, `cface_h_ac`);
* `E.cface_inj_embed` : `h` is injective on each face of the kernel;
* `Gm.PreHomRing Gc rc h x p` : `x :: p` is an R-path in the kernel whose image by `h` is a
  simple R-cycle (math-comp `pre_hom_ring`), and `E.intro_pre_hom_ring`;
* `E.trivial_hom_ring` : if the image of a pre-homomorphic ring `x :: p` has an empty inner disk
  (`fcard face (diskF (map h (x :: p))) ≤ 0`), then `x :: p` is itself an R-cycle.

## Porting notes

* `pre_hom_ring x p` (math-comp `[/\ path rlink x p, {subset x :: p <= ac} &
  scycle rlink (map h (x :: p))]`) is the structure `PreHomRing` with fields `rpath`, `sub_ac`,
  `scycle_map`; it depends on the section variables `Gm Gc rc h`, not on the hypotheses.
* `E.rlink_h` (an R-link between kernel darts is mapped to an R-link) is the induction step of
  `intro_pre_hom_ring`, stated separately because `trivial_hom_ring` uses it too.
* The Coq proof of `trivial_hom_ring` is by induction on `size p`, with the hypothesis
  `fcard face (diskF ...) <= 0`; the private `trivial_hom_ring_aux` does the induction with the
  equivalent hypothesis that `diskF (map h (x :: p))` is empty. The chord rings
  `chord_ring (map h xp) (h eny)`, `chord_ring (map h xp) (h enny)` are computed with
  `arc_of_rotate` (Coq: `arc_rot`, `right_arc`, `left_arc`), and the simplicity contradictions
  with `Embed.simple_split`.
-/

namespace FourColor

open Function

universe u v

namespace Hypermap

/-- math-comp `pre_hom_ring x p`: `x :: p` is an R-path included in the kernel `ac` of `rc`,
whose image by `h` is a simple R-cycle
(`[/\ path rlink x p, {subset x :: p <= ac} & scycle rlink (map h (x :: p))]`). -/
structure PreHomRing {Dm : Type u} {Dc : Type v} (Gm : Hypermap Dm) (Gc : Hypermap Dc)
    (rc : List Dc) (h : Dc → Dm) (x : Dc) (p : List Dc) : Prop where
  /-- `x :: p` is an R-path of `Gc`. -/
  rpath : path Gc.rlink x p
  /-- `x :: p` is included in the kernel. -/
  sub_ac : ∀ y ∈ x :: p, y ∈ Gc.kernel rc
  /-- The image of `x :: p` is a simple R-cycle of `Gm`. -/
  scycle_map : Gm.SCycle Gm.rlink ((x :: p).map h)

namespace EmbedHyps

variable {Dm : Type u} [Fintype Dm] {Gm : Hypermap Dm}
  {Dc : Type v} [Fintype Dc] [DecidableEq Dc] {Gc : Hypermap Dc} {rc : List Dc} {h : Dc → Dm}
  (E : EmbedHyps Gm Gc rc h)
include E

omit [DecidableEq Dc] in
/-- math-comp local `cface_ac_h`: on the kernel, `h` maps faces into faces. -/
theorem cface_ac_h {x y : Dc} (hx : x ∈ Gc.kernel rc) (hxy : Gc.cface x y) :
    Gm.cface (h x) (h y) := by
  induction hxy with
  | refl => exact connect_refl _
  | @tail b c hab hbc ih =>
    have hb : b ∈ Gc.kernel rc := (acF.connect_iff hab).1 hx
    obtain rfl : Gc.face b = c := hbc
    rw [E.hF hb]
    exact connect_trans ih (fconnect1 _ _)

omit [DecidableEq Dc] in
/-- math-comp local `cface_h_ac`: on the kernel, `h` maps faces onto faces. -/
theorem cface_h_ac {x : Dc} {u : Dm} (hx : x ∈ Gc.kernel rc) (hxu : Gm.cface (h x) u) :
    ∃ y, Gc.cface x y ∧ h y = u := by
  induction hxu with
  | refl => exact ⟨x, connect_refl _, rfl⟩
  | @tail b c _ hbc ih =>
    obtain ⟨y, xFy, rfl⟩ := ih
    have hy : y ∈ Gc.kernel rc := (acF.connect_iff xFy).1 hx
    refine ⟨Gc.face y, connect_trans xFy (fconnect1 _ _), ?_⟩
    rw [E.hF hy]
    exact hbc

omit [DecidableEq Dc] in
/-- math-comp `cface_inj_embed`: `h` is injective on the faces of the kernel. -/
theorem cface_inj_embed {x y : Dc} (hx : x ∈ Gc.kernel rc) (hxy : Gc.cface x y)
    (hh : h x = h y) : x = y := by
  have iter_hF : ∀ n z, z ∈ Gc.kernel rc → h (Gc.face^[n] z) = Gm.face^[n] (h z) := by
    intro n
    induction n with
    | zero => intro z _; rfl
    | succ n ih =>
      intro z hz
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← E.hF hz]
      exact ih _ ((acF z _ rfl).1 hz)
  obtain ⟨n, hn⟩ := fconnect_iff_iterate.1 hxy
  have hper : Function.IsPeriodicPt Gc.face (Gc.arity x) x := Gc.iter_face_arity x
  have hm : Gc.face^[n % Gc.arity x] x = y := by rw [hper.iterate_mod_apply, hn]
  have hlt : n % Gc.arity x < Gc.arity x := Nat.mod_lt _ (order_pos Gc.faceI x)
  have e : Gm.face^[n % Gc.arity x] (h x) = h x := by rw [← iter_hF _ x hx, hm, hh]
  have h0 : n % Gc.arity x = 0 := by
    apply Function.IsPeriodicPt.eq_zero_of_lt_minimalPeriod (show
      Function.IsPeriodicPt Gm.face (n % Gc.arity x) (h x) from e)
    rw [← order_eq_minimalPeriod Gm.faceI]
    have : Gm.arity (h x) = Gc.arity x := E.hFn hx
    unfold arity at this
    rw [this]
    exact hlt
  rw [← hm, h0]
  rfl

/-- An R-link between two darts of the kernel is mapped by `h` to an R-link (the induction step
of math-comp `intro_pre_hom_ring`). -/
theorem rlink_h {x y : Dc} (hx : x ∈ Gc.kernel rc) (hy : y ∈ Gc.kernel rc)
    (xRy : Gc.rlink x y) : Gm.rlink (h x) (h y) := by
  have ac_ex : Gc.edge x ∈ Gc.kernel rc := (acF.connect_iff xRy).2 hy
  show Gm.cface (Gm.edge (h x)) (h y)
  rw [← E.embed_functor hx ac_ex]
  exact E.cface_ac_h ac_ex xRy

/-- math-comp `intro_pre_hom_ring`. -/
theorem intro_pre_hom_ring {x : Dc} {p : List Dc} (xRp : path Gc.rlink x p)
    (Lhp : Gm.rlink (h (last x p)) (h x)) (p_ac : ∀ y ∈ x :: p, y ∈ Gc.kernel rc)
    (Uhp : Gm.Simple ((x :: p).map h)) : Gm.PreHomRing Gc rc h x p := by
  refine ⟨xRp, p_ac, ?_, Uhp⟩
  show path Gm.rlink (h x) (p.map h ++ [h x])
  rw [path_concat, last_map]
  refine ⟨?_, Lhp⟩
  clear Lhp Uhp
  induction p generalizing x with
  | nil => trivial
  | cons y p ih =>
    obtain ⟨xRy, yRp⟩ := xRp
    have ac_x := p_ac x List.mem_cons_self
    have ac_y := p_ac y (List.mem_cons_of_mem _ List.mem_cons_self)
    exact ⟨E.rlink_h ac_x ac_y xRy, ih yRp (fun z hz => p_ac z (List.mem_cons_of_mem _ hz))⟩

/-- The induction of math-comp `trivial_hom_ring`, on a bound `n` of `size p`, with the
hypothesis that the inner disk of the image ring is empty. -/
private theorem trivial_hom_ring_aux [DecidableEq Dm] (n : ℕ) : ∀ (x : Dc) (p : List Dc),
    p.length < n → (∀ u, u ∉ Gm.diskF ((x :: p).map h)) → Gm.PreHomRing Gc rc h x p →
    Gc.rlink (last x p) x := by
  induction n with
  | zero => intro x p hp; exact absurd hp (Nat.not_lt_zero _)
  | succ n IHn =>
  intro x p le_p_n pF_0 xHRp
  obtain ⟨xRp, p_ac, URhp⟩ := xHRp
  obtain ⟨y, hy⟩ : ∃ y, y = last x p := ⟨_, rfl⟩
  rw [← hy]
  have xp_y : y ∈ x :: p := hy ▸ mem_last x p
  have xp_hy : h y ∈ (x :: p).map h := List.mem_map_of_mem xp_y
  have ac_y := p_ac y xp_y
  have ac_x := p_ac x List.mem_cons_self
  have bc_y : y ∉ rc := ac_bc ac_y
  have Uhxp : ((x :: p).map h).Nodup := Gm.simple_uniq URhp.2
  have hyRx : Gm.rlink (h y) (h x) := by
    have := URhp.1
    change path Gm.rlink (h x) (p.map h ++ [h x]) at this
    rw [path_concat, last_map, ← hy] at this
    exact this.2
  have dN_hxp : ∀ w, w ∈ (x :: p).map h → w ∈ Gm.diskN ((x :: p).map h) :=
    fun w hw => Gm.mem_diskN_of_mem _ hw
  have dNnode : ∀ w, w ∈ Gm.diskN ((x :: p).map h) → Gm.node w ∈ Gm.diskN ((x :: p).map h) :=
    fun w hw => ((Gm.diskN_node _) w _ rfl).1 hw
  have fband_of_dN : ∀ w, w ∈ Gm.diskN ((x :: p).map h) → w ∈ Gm.fband ((x :: p).map h) := by
    intro w hw
    by_contra hF
    exact pF_0 w ⟨hw, hF⟩
  -- the face predecessor, and `node (node w) = face (edge w)`, in `Gm`
  have enFm : ∀ w : Dm, Gm.cface (Gm.edge (Gm.node w)) w := fun w => by
    have := fconnect1 Gm.face (Gm.edge (Gm.node w))
    rwa [Gm.nodeK] at this
  have nn_eq_m : ∀ w : Dm, Gm.face (Gm.edge w) = Gm.node (Gm.node w) := fun w => by
    have := Gm.nodeK (Gm.node (Gm.node w))
    rwa [E.n3m] at this
  -- `node (h y)` is in the face of the image of some dart `z` of `x :: p`
  obtain ⟨w, hw, nhyFw⟩ := fband_of_dN _ (dNnode _ (dN_hxp _ xp_hy))
  obtain ⟨z, xpz, rfl⟩ := List.mem_map.1 hw
  have zFnhy : Gm.cface (h z) (Gm.node (h y)) := Gm.cfaceC.1 nhyFw
  have ac_z := p_ac z xpz
  obtain ⟨p1, p2, Dp, Lp1⟩ := splitPl xpz
  rcases List.eq_nil_or_concat p2 with hp2 | ⟨p2', y1, hp2⟩
  · -- `z = y`: impossible, `Gm` is bridgeless.
    subst hp2
    rw [List.append_nil] at Dp
    have zy : z = y := by rw [hy, Dp, Lp1]
    rw [zy] at zFnhy
    exact absurd (Gm.cfaceC.1 (connect_trans (enFm _) zFnhy)) (E.bridge'Gm (Gm.node (h y)))
  rw [List.concat_eq_append] at hp2
  subst hp2
  have Dy1 : y1 = y := by rw [hy, Dp, last_append, last_concat]
  rw [Dy1] at Dp
  rcases List.eq_nil_or_concat p1 with hp1 | ⟨p1', z1, hp1⟩
  · -- `z = x`: impossible, `Gm` is bridgeless.
    subst hp1
    have zx : z = x := by rw [← Lp1]; rfl
    rw [zx] at zFnhy
    exfalso
    apply E.bridge'Gm (Gm.node (Gm.node (h y)))
    have h1 : Gm.cface (Gm.edge (h y)) (Gm.node (Gm.node (h y))) := by
      rw [← nn_eq_m]
      exact fconnect1 _ _
    exact connect_trans (Gm.cfaceC.1 h1)
      (connect_trans hyRx (connect_trans zFnhy (Gm.cfaceC.1 (enFm _))))
  rw [List.concat_eq_append] at hp1
  subst hp1
  have z1z : z1 = z := by rw [← Lp1, last_concat]
  rw [z1z] at Dp
  -- `p = p1' ++ [z] ++ p2' ++ [y]`
  have e_map : (x :: p).map h = (h x :: p1'.map h) ++ h z :: (p2'.map h ++ [h y]) := by
    rw [Dp]
    simp
  have nt_r : Gm.ProperRing ((x :: p).map h) := by
    apply Gm.size_proper_ring
    rw [e_map]
    simp only [List.length_append, List.length_cons, List.length_map, List.length_nil]
    omega
  have hlen : p.length = p1'.length + p2'.length + 2 := by
    rw [Dp]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  -- `eny := edge (node y)`
  obtain ⟨eny, heny⟩ : ∃ e, e = Gc.edge (Gc.node y) := ⟨_, rfl⟩
  have ac_eny : eny ∈ Gc.kernel rc := heny ▸ ac_edge_node ac_y
  have h_eny : h eny = Gm.edge (Gm.node (h y)) := heny ▸ E.h_edge_node ac_y
  have enyFy : Gc.cface eny y := heny ▸ cface_edge_node y
  have eeny : Gc.edge eny = Gc.node y := by rw [heny]; exact E.e2c _
  have henyFy : Gm.cface (h eny) (h y) := by rw [h_eny]; exact enFm _
  have enyRz : Gc.rlink eny z := by
    by_cases p_hny : Gm.node (h y) ∈ (x :: p).map h
    · obtain ⟨t, xpt, Dht⟩ := List.mem_map.1 p_hny
      obtain ⟨p3, p4, Dp3, Lp3⟩ := splitPl xpt
      have Dp4 : p4 = [y] := by
        rcases p4 with _ | ⟨t1, _ | ⟨t2, p4⟩⟩
        · exfalso
          rw [List.append_nil] at Dp3
          have ty : t = y := by rw [hy, Dp3, Lp3]
          rw [ty] at Dht
          apply E.bridge'Gm (h y)
          have := enFm (h y)
          rw [← Dht] at this
          exact Gm.cfaceC.1 this
        · have : t1 = y := by rw [hy, Dp3, last_append]; rfl
          rw [this]
        · exfalso
          have ac_t := p_ac t xpt
          have ac_t1 := p_ac t1 (by
            rw [Dp3]
            exact List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
          have tRt1 : Gc.rlink t t1 := by
            have := xRp
            rw [Dp3, path_append, Lp3] at this
            exact this.2.1
          have htRt1 := E.rlink_h ac_t ac_t1 tRt1
          change Gm.cface (Gm.edge (h t)) (h t1) at htRt1
          rw [Dht] at htRt1
          have t1Fy : Gm.cface (h t1) (h y) := connect_trans (Gm.cfaceC.1 htRt1) (enFm _)
          have y_mem : h y ∈ (t2 :: p4).map h := by
            have : y = last t2 p4 := by rw [hy, Dp3, last_append, Lp3]; rfl
            rw [this]
            exact List.mem_map_of_mem (mem_last _ _)
          exact Embed.simple_split Gm URhp.2 (A := (x :: p3).map h)
            (by rw [Dp3]; simp) y_mem t1Fy
      rw [Dp4] at Dp3
      have ac_t := p_ac t xpt
      have tRy : Gc.rlink t y := by
        have := xRp
        rw [Dp3, path_concat, Lp3] at this
        exact this.2
      have ac_et : Gc.edge t ∈ Gc.kernel rc := (acF.connect_iff tRy).2 ac_y
      have Dt : t = Gc.node y := by
        apply Gc.edgeI
        rw [← heny]
        apply E.cface_inj_embed ac_et (connect_trans tRy (Gc.cfaceC.1 enyFy))
        rw [E.embed_functor ac_t ac_et, Dht, h_eny]
      have Dp3' : p3 = (p1' ++ [z]) ++ p2' := by
        have := Dp3.symm.trans Dp
        rw [← List.append_assoc] at this
        exact List.append_cancel_right this
      rcases List.eq_nil_or_concat p2' with hp2' | ⟨p2'', t', hp2'⟩
      · rw [hp2', List.append_nil] at Dp3'
        have tz : t = z := by rw [← Lp3, Dp3', last_concat]
        show Gc.cface (Gc.edge eny) z
        rw [eeny, ← Dt, tz]
      · exfalso
        rw [List.concat_eq_append] at hp2'
        have tt' : t = t' := by rw [← Lp3, Dp3', hp2', ← List.append_assoc, last_concat]
        have t_mem : h t ∈ p2'.map h ++ [h y] := by
          rw [hp2', tt']
          simp
        exact Embed.simple_split Gm URhp.2 e_map t_mem (by rw [Dht]; exact zFnhy)
    · -- The chord `h eny` of the image ring cuts off the smaller ring `z :: p2' ++ [eny]`.
      have zRp2 : path Gc.rlink z (p2' ++ [y]) := by
        have := xRp
        rw [Dp, path_append, last_concat] at this
        exact this.2
      have zRq : path Gc.rlink z (p2' ++ [eny]) := by
        rw [path_concat] at zRp2 ⊢
        exact ⟨zRp2.1, (Gc.rlinkFr (Gc.cfaceC.1 enyFy) _).1 zRp2.2⟩
      have zHRq : Gm.PreHomRing Gc rc h z (p2' ++ [eny]) := by
        refine E.intro_pre_hom_ring zRq ?_ ?_ ?_
        · rw [last_concat]
          show Gm.cface (Gm.edge (h eny)) (h z)
          rw [h_eny, E.e2m]
          exact Gm.cfaceC.1 zFnhy
        · intro t ht
          rcases List.mem_cons.1 ht with ht | ht
          · rw [ht]; exact ac_z
          rcases List.mem_append.1 ht with ht | ht
          · exact p_ac t (by rw [Dp]; simp [ht])
          · rw [List.mem_singleton.1 ht]; exact ac_eny
        · have hS := URhp.2
          rw [e_map, Gm.simple_cat] at hS
          have hS2 := hS.2.2
          rw [← List.cons_append, Gm.simple_rcons] at hS2
          rw [show (z :: (p2' ++ [eny])).map h = (h z :: p2'.map h) ++ [h eny] by simp,
            Gm.simple_rcons]
          exact ⟨fun hF => hS2.1 (((Gm.fbandF _).connect_iff henyFy).1 hF), hS2.2⟩
      have hlq : (p2' ++ [eny]).length < n := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have := IHn z (p2' ++ [eny]) hlq ?_ zHRq
      · rw [last_concat] at this
        exact this
      intro u hu
      have hxpFeny : h eny ∈ Gm.fband ((x :: p).map h) := ⟨h y, xp_hy, henyFy⟩
      have xpFenhy : Gm.edge (h eny) ∈ Gm.fband ((x :: p).map h) := by
        rw [h_eny, E.e2m]
        exact ⟨h z, List.mem_map_of_mem xpz, Gm.cfaceC.1 zFnhy⟩
      have dEeny : h eny ∈ Gm.diskE ((x :: p).map h) := by
        rw [h_eny]
        exact ((Gm.diskE_edge E.planarGm URhp) _ _ rfl).1
          ⟨dNnode _ (dN_hxp _ xp_hy), p_hny⟩
      have Ech : Gm.chordRing ((x :: p).map h) (h eny) = h eny :: h z :: p2'.map h := by
        have f1 : Gm.fproj ((x :: p).map h) (h eny) = h y :=
          Embed.fproj_eq Gm URhp xp_hy henyFy
        have f2 : Gm.fproj ((x :: p).map h) (Gm.edge (h eny)) = h z := by
          rw [h_eny, E.e2m]
          exact Embed.fproj_eq Gm URhp (List.mem_map_of_mem xpz) (Gm.cfaceC.1 zFnhy)
        unfold chordRing
        rw [f1, f2]
        congr 1
        have e2 : (x :: p).map h = ((h x :: p1'.map h) ++ h z :: p2'.map h) ++ [h y] := by
          rw [e_map]
          simp
        have hrot : ((x :: p).map h).rotate ((h x :: p1'.map h) ++ h z :: p2'.map h).length =
            h y :: (h x :: p1'.map h) ++ h z :: p2'.map h := by
          rw [e2, List.rotate_append_length_eq]
          simp
        exact (arc_of_rotate Uhxp hrot).2
      have hmap : (z :: (p2' ++ [eny])).map h = (h eny :: h z :: p2'.map h).rotate 1 := by
        rw [List.rotate_cons_succ, List.rotate_zero]
        simp
      rw [hmap, Gm.diskF_rot, ← Ech,
        Gm.diskF_chord_ring E.geoGm URhp nt_r dEeny hxpFeny xpFenhy] at hu
      exact pF_0 u hu.1
  -- `node y` is in the kernel and `h` commutes with `node` there.
  have ac_ny : Gc.node y ∈ Gc.kernel rc := by
    rw [← eeny]
    exact (acF.connect_iff enyRz).2 ac_z
  have h_ny : h (Gc.node y) = Gm.node (h y) := by
    apply Gm.edgeI
    rw [← E.embed_functor ac_ny (ac_edge_node ac_y), ← heny, h_eny]
  -- `enny := edge (node (node y))`
  obtain ⟨enny, henny⟩ : ∃ e, e = Gc.edge (Gc.node (Gc.node y)) := ⟨_, rfl⟩
  have ac_enny : enny ∈ Gc.kernel rc := henny ▸ ac_edge_node ac_ny
  have h_enny : h enny = Gm.edge (Gm.node (Gm.node (h y))) := by
    rw [henny, E.h_edge_node ac_ny, h_ny]
  have ennyFny : Gc.cface enny (Gc.node y) := henny ▸ cface_edge_node (Gc.node y)
  have eenny : Gc.edge enny = Gc.node (Gc.node y) := by rw [henny]; exact E.e2c _
  have hennyFnhy : Gm.cface (h enny) (Gm.node (h y)) := by rw [h_enny]; exact enFm _
  have ennyFz : Gc.cface enny z := by
    have : Gc.cface (Gc.node y) z := by
      have := enyRz
      change Gc.cface (Gc.edge eny) z at this
      rwa [eeny] at this
    exact connect_trans ennyFny this
  have ennyRx : Gc.rlink enny x := by
    by_cases p'nnhy : Gm.node (Gm.node (h y)) ∈ (x :: p).map h
    · obtain ⟨t, xpt, Dht⟩ := List.mem_map.1 p'nnhy
      have htFhx : Gm.cface (h t) (h x) := by
        rw [Dht, ← nn_eq_m]
        exact (Gm.cface1 _ _).1 hyRx
      have tx : t = x := by
        rcases List.mem_cons.1 xpt with e | tp
        · exact e
        · exfalso
          exact Embed.simple_split Gm URhp.2 (A := []) (by simp) (List.mem_map_of_mem tp)
            (Gm.cfaceC.1 htFhx)
      rw [tx] at Dht
      have hp1' : p1' = [] := by
        rcases p1' with _ | ⟨x1, p1''⟩
        · rfl
        · exfalso
          have ac_x1 := p_ac x1 (by rw [Dp]; simp)
          have xRx1 : Gc.rlink x x1 := by
            have := xRp
            rw [Dp] at this
            exact this.1
          have hxRx1 := E.rlink_h ac_x ac_x1 xRx1
          change Gm.cface (Gm.edge (h x)) (h x1) at hxRx1
          rw [Dht] at hxRx1
          have nhyFx1 : Gm.cface (Gm.node (h y)) (h x1) :=
            connect_trans (Gm.cfaceC.1 (enFm _)) hxRx1
          have x1Fz : Gm.cface (h x1) (h z) := Gm.cfaceC.1 (connect_trans zFnhy nhyFx1)
          exact Embed.simple_split Gm URhp.2 (A := [h x])
            (B := p1''.map h ++ h z :: (p2'.map h ++ [h y])) (by rw [e_map]; simp) (by simp)
            x1Fz
      rw [hp1'] at Dp
      have xRz : Gc.rlink x z := by
        have := xRp
        rw [Dp] at this
        exact this.1
      have ac_ex : Gc.edge x ∈ Gc.kernel rc := (acF.connect_iff xRz).2 ac_z
      have Dx : Gc.edge x = enny := by
        apply E.cface_inj_embed ac_ex (connect_trans xRz (Gc.cfaceC.1 ennyFz))
        rw [E.embed_functor ac_x ac_ex, Dht, h_enny]
      show Gc.cface (Gc.edge enny) x
      rw [← Dx, E.e2c]
    · -- The chord `h enny` of the image ring cuts off the smaller ring `x :: p1' ++ [enny]`.
      have xRp1z : path Gc.rlink x (p1' ++ [z]) := by
        have := xRp
        rw [Dp, path_append] at this
        exact this.1
      have xRq : path Gc.rlink x (p1' ++ [enny]) := by
        rw [path_concat] at xRp1z ⊢
        exact ⟨xRp1z.1, (Gc.rlinkFr (Gc.cfaceC.1 ennyFz) _).1 xRp1z.2⟩
      have hennyFz : Gm.cface (h enny) (h z) := connect_trans hennyFnhy (Gm.cfaceC.1 zFnhy)
      have xHRq : Gm.PreHomRing Gc rc h x (p1' ++ [enny]) := by
        refine E.intro_pre_hom_ring xRq ?_ ?_ ?_
        · rw [last_concat]
          show Gm.cface (Gm.edge (h enny)) (h x)
          rw [h_enny, E.e2m, ← nn_eq_m]
          exact (Gm.cface1 _ _).1 hyRx
        · intro t ht
          rcases List.mem_cons.1 ht with ht | ht
          · rw [ht]; exact ac_x
          rcases List.mem_append.1 ht with ht | ht
          · exact p_ac t (by rw [Dp]; simp [ht])
          · rw [List.mem_singleton.1 ht]; exact ac_enny
        · have hS := URhp.2
          rw [e_map, Gm.simple_cat] at hS
          rw [show (x :: (p1' ++ [enny])).map h = (h x :: p1'.map h) ++ [h enny] by simp,
            Gm.simple_rcons]
          exact ⟨fun hF => hS.2.1 ⟨h z, List.mem_cons_self,
            ((Gm.fbandF _).connect_iff hennyFz).1 hF⟩, hS.1⟩
      have hlq : (p1' ++ [enny]).length < n := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have := IHn x (p1' ++ [enny]) hlq ?_ xHRq
      · rw [last_concat] at this
        exact this
      intro u hu
      have hxpFenny : h enny ∈ Gm.fband ((x :: p).map h) :=
        ⟨h z, List.mem_map_of_mem xpz, hennyFz⟩
      have hxpFeenny : Gm.edge (h enny) ∈ Gm.fband ((x :: p).map h) := by
        rw [h_enny, E.e2m, ← nn_eq_m]
        exact ⟨h x, List.mem_map_of_mem List.mem_cons_self, (Gm.cface1 _ _).1 hyRx⟩
      have dEenny : h enny ∈ Gm.diskE ((x :: p).map h) := by
        rw [h_enny]
        exact ((Gm.diskE_edge E.planarGm URhp) _ _ rfl).1
          ⟨dNnode _ (dNnode _ (dN_hxp _ xp_hy)), p'nnhy⟩
      have Ech : Gm.chordRing ((x :: p).map h) (h enny) = h enny :: h x :: p1'.map h := by
        have f1 : Gm.fproj ((x :: p).map h) (h enny) = h z :=
          Embed.fproj_eq Gm URhp (List.mem_map_of_mem xpz) hennyFz
        have f2 : Gm.fproj ((x :: p).map h) (Gm.edge (h enny)) = h x := by
          rw [h_enny, E.e2m, ← nn_eq_m]
          exact Embed.fproj_eq Gm URhp (List.mem_map_of_mem List.mem_cons_self)
            ((Gm.cface1 _ _).1 hyRx)
        unfold chordRing
        rw [f1, f2]
        congr 1
        have hrot : ((x :: p).map h).rotate 0 =
            h x :: p1'.map h ++ h z :: (p2'.map h ++ [h y]) := by
          rw [List.rotate_zero, e_map]
        exact (arc_of_rotate Uhxp hrot).1
      have hmap : (x :: (p1' ++ [enny])).map h = (h enny :: h x :: p1'.map h).rotate 1 := by
        rw [List.rotate_cons_succ, List.rotate_zero]
        simp
      rw [hmap, Gm.diskF_rot, ← Ech,
        Gm.diskF_chord_ring E.geoGm URhp nt_r dEenny hxpFenny hxpFeenny] at hu
      exact pF_0 u hu.1
  -- Conclusion: `rlink y x`, since `node (node y) = face (edge y)`.
  show Gc.cface (Gc.edge y) x
  have e1 : Gc.face (Gc.edge y) = Gc.node (Gc.node y) := by
    have := Gc.nodeK (Gc.node (Gc.node y))
    rwa [E.n3c bc_y] at this
  have : Gc.cface (Gc.node (Gc.node y)) x := by
    have := ennyRx
    change Gc.cface (Gc.edge enny) x at this
    rwa [eenny] at this
  rw [← e1] at this
  exact (Gc.cface1 _ _).2 this

/-- math-comp `trivial_hom_ring`: a pre-homomorphic ring whose image has an empty inner disk is
an R-cycle. -/
theorem trivial_hom_ring [DecidableEq Dm] {x : Dc} {p : List Dc}
    (xHRp : Gm.PreHomRing Gc rc h x p) (pF_0 : fcard Gm.face (Gm.diskF ((x :: p).map h)) ≤ 0) :
    Gc.rlink (last x p) x := by
  refine E.trivial_hom_ring_aux _ x p (Nat.lt_succ_self _) ?_ xHRp
  intro u hu
  have := (Gm.fcard0P (Gm.diskF_face _)).2 ⟨u, hu⟩
  omega

end EmbedHyps

end Hypermap

end FourColor
