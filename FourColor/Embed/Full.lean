/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Embed.Perimeter

/-!
# The preembedding is full (part of the port of `embed.v`)

`E.embed_full` (math-comp `embed_full`): under the section hypotheses
`E : Hypermap.EmbedHyps Gm Gc rc h`, if `x1` and `x2` are in the kernel and `edge (h x1) = h x2`
then `edge x1 = x2`.

The Coq proof is a chain of three `suffices`; here they are the private lemmas

* `full_step4`: there is no pre-homomorphic ring `x :: p` (`PreHomRing`) that is not an
  R-cycle, and whose image has at most `size (x :: p) == 5` inner faces (for size 5 with one
  inner face, the image is the spoke ring of that face, and the kernel would have five darts
  adjacent to the face of `node x`, contradicting `adj_kernel_max`);
* `full_step3`: nor one with `size p ≤ 4` (by the Birkhoff theorem, applied to the image ring,
  one of `x :: p` and of its reverse ring satisfies the hypothesis of `full_step4`);
* `full_shorten` and `full_step2`: there is no R-path `x0 :: p` in the kernel, of size at most
  `5`, with `last x0 p ≠ x0` and `edge (h (last x0 p)) = h (edge x0)` (`full_shorten` makes the
  image of such a path simple, by the induction on `p` of the Coq proof);

and the theorem itself follows by joining `x1` and `x2` through the center of the kernel, which
has radius 2.

## Porting notes

* `nat_of_bool (size (x :: p) == 5)` is `((x :: p).length == 5).toNat`, as in
  `Hypermap.birkhoff`.
* In `full_step4` the Coq proof compares the numbers of face roots of `fband (spoke_ring u)` and
  `fband (map h (x :: p))`; here the private lemma `closed_subset_eq` concludes from the
  inclusion of face-closed sets and the equality of their face counts (`fcard`).
* In `full_step3` the reverse ring is `rx :: rp` with `rx := edge (last x p1)` and
  `rp := rev (map edge (belast x p1)) ++ [ry]`, and its image is the rotation
  `(rev_ring (map h (x :: p))).rotate 1` (Coq: `rot 1`).
-/

namespace FourColor

open Function

universe u v

/-- Face counts are monotone. -/
private theorem nComp_mono {α : Type*} [Finite α] {e : α → α → Prop} {A B : Set α}
    (h : A ⊆ B) : nComp e A ≤ nComp e B :=
  Set.ncard_le_ncard (Set.image_mono h) (Set.toFinite _)

/-- A closed set `A` included in a set `B` with no more components is equal to `B`
(the counting argument `subset_cardP` of the Coq proof of `embed_full`). -/
private theorem closed_subset_eq {α : Type*} [Finite α] {e : α → α → Prop} (hs : ConnectSym e)
    {A B : Set α} (hA : Closed e A) (hAB : A ⊆ B) (hc : nComp e B ≤ nComp e A) : B ⊆ A := by
  intro v hv
  have himg : comp e '' A = comp e '' B :=
    Set.eq_of_subset_of_ncard_le (Set.image_mono hAB) hc (Set.toFinite _)
  have hv' : comp e v ∈ comp e '' A := by
    rw [himg]
    exact ⟨v, hv, rfl⟩
  obtain ⟨a, ha, hav⟩ := hv'
  exact (hA.connect_iff ((comp_eq_iff hs).1 hav)).1 ha

namespace Hypermap

namespace EmbedHyps

variable {Dm : Type u} [Fintype Dm] [DecidableEq Dm] {Gm : Hypermap Dm}
  {Dc : Type v} [Fintype Dc] [DecidableEq Dc] {Gc : Hypermap Dc} {rc : List Dc} {h : Dc → Dm}
  (E : EmbedHyps Gm Gc rc h)
include E

/-- The innermost `suffices` of math-comp `embed_full`: a pre-homomorphic ring whose image has
at most `size (x :: p) == 5` inner faces is an R-cycle. -/
private theorem full_step4 {x : Dc} {p : List Dc} (xHRp : Gm.PreHomRing Gc rc h x p)
    (Lp : ¬ Gc.rlink (last x p) x)
    (triv_dF : fcard Gm.face (Gm.diskF ((x :: p).map h)) ≤ ((x :: p).length == 5).toNat) :
    False := by
  apply Lp
  apply E.trivial_hom_ring xHRp
  by_cases sz : (x :: p).length = 5
  swap
  · have : ((x :: p).length == 5).toNat = 0 := by rw [beq_false_of_ne sz]; rfl
    omega
  by_contra hpos
  have hpos' : 0 < fcard Gm.face (Gm.diskF ((x :: p).map h)) := by omega
  obtain ⟨u, dFu⟩ := (Gm.fcard0P (Gm.diskF_face _)).1 hpos'
  have le1 : fcard Gm.face (Gm.diskF ((x :: p).map h)) ≤ 1 := by
    have : ((x :: p).length == 5).toNat = 1 := by rw [beq_iff_eq.2 sz]; rfl
    omega
  obtain ⟨xRp, p_ac, URhxp⟩ := xHRp
  have hlen : ((x :: p).map h).length = 5 := by rw [List.length_map]; exact sz
  have Uhxp : ((x :: p).map h).Nodup := Gm.simple_uniq URhxp.2
  have enFm : ∀ w : Dm, Gm.cface (Gm.edge (Gm.node w)) w := fun w => by
    have := fconnect1 Gm.face (Gm.edge (Gm.node w))
    rwa [Gm.nodeK] at this
  -- The inner face disk of the image ring is the face of `u`.
  have DdF : ∀ v, v ∈ Gm.diskF ((x :: p).map h) ↔ Gm.cface u v := by
    intro v
    constructor
    · intro dFv
      by_contra uv
      have := (Gm.fcard1P (Gm.diskF_face _)).2 ⟨u, dFu, v, dFv, uv⟩
      omega
    · intro uv
      exact ((Gm.diskF_face _).connect_iff uv).1 dFu
  -- The image ring and the spoke ring of `u` have the same face band.
  have URu := Gm.scycle_spoke_ring E.cexGm u
  have ruF_xpF : Gm.fband (Gm.spokeRing u) ⊆ Gm.fband ((x :: p).map h) := by
    rintro v1 ⟨v, ru_v, v1Fv⟩
    have uFnv := Gm.mem_spoke_ring.1 ru_v
    have dNnv : Gm.node v ∈ Gm.diskN ((x :: p).map h) := ((DdF _).2 uFnv).1
    have dNv : v ∈ Gm.diskN ((x :: p).map h) := ((Gm.diskN_node _) v _ rfl).2 dNnv
    have dF'v : v ∉ Gm.diskF ((x :: p).map h) := by
      intro dFv
      apply E.bridge'Gm (Gm.node v)
      exact connect_trans (connect_trans (Gm.cfaceC.1 uFnv) ((DdF v).1 dFv))
        (Gm.cfaceC.1 (enFm v))
    have xpFv : v ∈ Gm.fband ((x :: p).map h) := by
      by_contra h'
      exact dF'v ⟨dNv, h'⟩
    exact ((Gm.fbandF _).connect_iff v1Fv).2 xpFv
  have EpFr : fcard Gm.face (Gm.fband ((x :: p).map h)) ≤
      fcard Gm.face (Gm.fband (Gm.spokeRing u)) := by
    rw [Gm.scycle_fcard_fband URhxp, Gm.scycle_fcard_fband URu, Gm.size_spoke_ring, hlen]
    have := E.pentaGm u
    omega
  have DxpF : Gm.fband ((x :: p).map h) ⊆ Gm.fband (Gm.spokeRing u) :=
    closed_subset_eq Gm.cface_sym (Gm.fbandF _) ruF_xpF EpFr
  -- The image ring is included in the spoke ring of `u`.
  have nt_hxp : Gm.ProperRing ((x :: p).map h) := Gm.size_proper_ring (by rw [hlen]; omega)
  have hxp_ru : ∀ v ∈ (x :: p).map h, v ∈ Gm.spokeRing u := by
    intro v hv
    have uAv : Gm.adj u v := (Gm.fband_spoke_ring u v).1 (DxpF (Gm.ring_fband _ v hv))
    have uAev : Gm.adj u (Gm.edge v) := by
      have h1 : Gm.rlink v (next ((x :: p).map h) v) := Embed.next_cycle URhxp.1 hv
      rw [Gm.adjFr h1]
      exact (Gm.fband_spoke_ring u _).1 (DxpF (Gm.ring_fband _ _ (Embed.mem_next.2 hv)))
    rcases Gm.adj11_edge E.cexGm uAv uAev with h' | h'
    · exact h'
    · exfalso
      have dNnev := ((DdF _).2 (Gm.mem_spoke_ring.1 h')).1
      have dNev := ((Gm.diskN_node _) _ _ rfl).2 dNnev
      exact Gm.diskN_edge_ring E.geoGm URhxp nt_hxp hv dNev
  -- Hence the image ring is a cycle of `face ∘ face ∘ edge`.
  have cycFFE : fcycle (fun w => Gm.face (Gm.face (Gm.edge w))) ((x :: p).map h) := by
    apply Embed.cycle_from_next Uhxp
    intro v hv
    show Gm.face (Gm.face (Gm.edge v)) = next ((x :: p).map h) v
    have ru_v := hxp_ru v hv
    have e : next (Gm.spokeRing u) v = Gm.face (Gm.face (Gm.edge v)) :=
      Gm.next_spoke_ring E.cexGm ru_v
    apply Gm.scycle_cface URu
    · rw [← e]
      exact Embed.mem_next.2 ru_v
    · exact hxp_ru _ (Embed.mem_next.2 hv)
    · have h1 : Gm.rlink v (next ((x :: p).map h) v) := Embed.next_cycle URhxp.1 hv
      exact (Gm.cface1 _ _).1 ((Gm.cface1 _ _).1 h1)
  have hcyc : path (frel (fun w => Gm.face (Gm.face (Gm.edge w)))) (h x) (p.map h ++ [h x]) :=
    cycFFE
  rw [path_concat, last_map] at hcyc
  obtain ⟨hxFFEhp, Lhp⟩ := hcyc
  change Gm.face (Gm.face (Gm.edge (h (last x p)))) = h x at Lhp
  -- The nodes of the darts of `x :: p` are all in the face of `node x`.
  have step : ∀ x1 x2, x1 ∈ Gc.kernel rc → x2 ∈ Gc.kernel rc → Gc.rlink x1 x2 →
      h x2 = Gm.face (Gm.face (Gm.edge (h x1))) → Gc.cface (Gc.node x1) (Gc.node x2) := by
    intro x1 x2 ac_x1 ac_x2 x1Rx2 Dhx2
    have ac_ex1 : Gc.edge x1 ∈ Gc.kernel rc := (acF.connect_iff x1Rx2).2 ac_x2
    have ac_fex1 : Gc.face (Gc.edge x1) ∈ Gc.kernel rc := (acF _ _ rfl).1 ac_ex1
    rw [← E.embed_functor ac_x1 ac_ex1, ← E.hF ac_ex1, ← E.hF ac_fex1] at Dhx2
    have x2Fffe : Gc.cface x2 (Gc.face (Gc.face (Gc.edge x1))) :=
      (Gc.cface1r _ _).1 ((Gc.cface1r _ _).1 (Gc.cfaceC.1 x1Rx2))
    have e := E.cface_inj_embed ac_x2 x2Fffe Dhx2
    rw [e, Gc.plain_eq' E.plainGc]
    have nn : Gc.face (Gc.edge x1) = Gc.node (Gc.node x1) := by
      have := Gc.nodeK (Gc.node (Gc.node x1))
      rwa [E.n3c (ac_bc ac_x1)] at this
    have e2 : Gc.face (Gc.edge (Gc.face (Gc.edge x1))) = Gc.node x1 := by
      rw [nn]
      exact Gc.nodeK _
    have h1 := fconnect1 Gc.face (Gc.edge (Gc.face (Gc.edge x1)))
    rw [e2] at h1
    exact Gc.cfaceC.1 h1
  have nxp_nxF : ∀ z ∈ x :: p, Gc.cface (Gc.node x) (Gc.node z) := by
    have key : ∀ (l : List Dc) (w : Dc), path Gc.rlink w l →
        (∀ z ∈ w :: l, z ∈ Gc.kernel rc) →
        fpath (fun w => Gm.face (Gm.face (Gm.edge w))) (h w) (l.map h) →
        ∀ z ∈ w :: l, Gc.cface (Gc.node w) (Gc.node z) := by
      intro l
      induction l with
      | nil =>
        intro w _ _ _ z hz
        obtain rfl := List.mem_singleton.1 hz
        exact connect_refl _
      | cons w2 l ih =>
        intro w wR hac hF z hz
        obtain ⟨wRw2, w2R⟩ := wR
        obtain ⟨Dhw2, hF'⟩ := hF
        have e := step w w2 (hac w List.mem_cons_self)
          (hac w2 (List.mem_cons_of_mem _ List.mem_cons_self)) wRw2 Dhw2.symm
        rcases List.mem_cons.1 hz with hz | hz
        · rw [hz]
        · exact connect_trans e
            (ih w2 w2R (fun t ht => hac t (List.mem_cons_of_mem _ ht)) hF' z hz)
    exact key p x xRp p_ac hxFFEhp
  -- `node x` is not in the kernel.
  have ac'nx : Gc.node x ∉ Gc.kernel rc := by
    intro ac_nx
    apply Lp
    obtain ⟨y, hy⟩ : ∃ y, y = last x p := ⟨_, rfl⟩
    rw [← hy] at Lhp ⊢
    have xp_y : y ∈ x :: p := hy ▸ mem_last x p
    have ac_x := p_ac x List.mem_cons_self
    have ac_y := p_ac y xp_y
    have nxFny := nxp_nxF y xp_y
    have ac_ny : Gc.node y ∈ Gc.kernel rc := (acF.connect_iff nxFny).1 ac_nx
    have h_nx : h (Gc.node x) = Gm.node (h x) := by
      apply Gm.edgeI
      rw [← E.embed_functor ac_nx (ac_edge_node ac_x), E.h_edge_node ac_x]
    have h_ny : h (Gc.node y) = Gm.node (h y) := by
      apply Gm.edgeI
      rw [← E.embed_functor ac_ny (ac_edge_node ac_y), E.h_edge_node ac_y]
    have nn_hy : Gm.face (Gm.edge (h y)) = Gm.node (Gm.node (h y)) := by
      have := Gm.nodeK (Gm.node (Gm.node (h y)))
      rwa [E.n3m] at this
    have hny : h (Gc.node y) = h (Gc.face (Gc.node x)) := by
      rw [E.hF ac_nx, h_nx, h_ny, ← Lhp, Gm.plain_eq' E.plainGm, nn_hy, Gm.nodeK]
    have nyFfnx : Gc.cface (Gc.node y) (Gc.face (Gc.node x)) :=
      connect_trans (Gc.cfaceC.1 nxFny) (fconnect1 _ _)
    have e := E.cface_inj_embed ac_ny nyFfnx hny
    show Gc.cface (Gc.edge y) x
    have nny : Gc.face (Gc.edge y) = Gc.node (Gc.node y) := by
      have := Gc.nodeK (Gc.node (Gc.node y))
      rwa [E.n3c (ac_bc ac_y)] at this
    rw [Gc.cface1, nny, e, Gc.plain_eq' E.plainGc]
    exact cface_edge_node x
  -- Five distinct darts of the face of `node x` have their edge in the kernel.
  have nxp_ace : ∀ w ∈ (x :: p).map Gc.node,
      w ∈ {z | Gc.cface (Gc.node x) z ∧ Gc.edge z ∈ Gc.kernel rc} := by
    intro w hw
    obtain ⟨z, xpz, rfl⟩ := List.mem_map.1 hw
    exact ⟨nxp_nxF z xpz, ac_edge_node (p_ac z xpz)⟩
  have Unxp : ((x :: p).map Gc.node).Nodup := (List.Nodup.of_map h Uhxp).map Gc.nodeI
  have hc1 := ncard_mem_of_nodup Unxp
  have hc2 := Set.ncard_le_ncard (s := {w | w ∈ (x :: p).map Gc.node}) nxp_ace
  have hc3 := E.adj_kernel_max ac'nx
  rw [hc1, List.length_map, sz] at hc2
  omega

/-- The middle `suffices` of math-comp `embed_full`: a pre-homomorphic ring `x :: p` with
`size p ≤ 4` is an R-cycle. -/
private theorem full_step3 {x : Dc} {p : List Dc} (xHRp : Gm.PreHomRing Gc rc h x p)
    (Lp : ¬ Gc.rlink (last x p) x) (hp4 : p.length ≤ 4) : False := by
  by_cases triv : fcard Gm.face (Gm.diskF ((x :: p).map h)) ≤ ((x :: p).length == 5).toNat
  · exact E.full_step4 xHRp Lp triv
  rw [not_le] at triv
  obtain ⟨xRp, p_ac, URhp⟩ := xHRp
  have ac_x := p_ac x List.mem_cons_self
  have hp_ok : Gm.ProperRing ((x :: p).map h) := by
    rcases p with _ | ⟨y, _ | ⟨y1, p1⟩⟩
    · exact absurd (Gm.cfaceC.1 URhp.1.1) (E.bridge'Gm (h x))
    · show Gm.edge (h x) ≠ h y
      intro ehx
      apply Lp
      have ac_y := p_ac y (List.mem_cons_of_mem _ List.mem_cons_self)
      have xRy : Gc.rlink x y := xRp.1
      have ac_ex : Gc.edge x ∈ Gc.kernel rc := (acF.connect_iff xRy).2 ac_y
      have e : Gc.edge x = y :=
        E.cface_inj_embed ac_ex xRy (by rw [E.embed_functor ac_x ac_ex, ehx])
      show Gc.cface (Gc.edge y) x
      rw [← e, E.e2c]
    · exact Gm.size_proper_ring (by simp)
  have hxFehp : Gm.cface (h x) (Gm.edge (h (last x p))) := by
    have := URhp.1
    change path Gm.rlink (h x) (p.map h ++ [h x]) at this
    rw [path_concat, last_map] at this
    exact Gm.cfaceC.1 this.2
  obtain ⟨p1, y, rfl⟩ : ∃ p1 y, p = p1 ++ [y] := by
    rcases List.eq_nil_or_concat p with h0 | ⟨p1, y, h0⟩
    · subst h0
      exact absurd hxFehp (E.bridge'Gm (h x))
    · exact ⟨p1, y, by rw [h0, List.concat_eq_append]⟩
  rw [last_concat] at hxFehp
  have ac_y := p_ac y (List.mem_cons_of_mem _ (List.mem_append_right _ List.mem_cons_self))
  obtain ⟨ry, xFry, hry⟩ := E.cface_h_ac ac_x hxFehp
  have ac_ry : ry ∈ Gc.kernel rc := (acF.connect_iff xFry).1 ac_x
  -- `h` commutes with `edge` on the darts of `x :: p1`.
  have hEac : ∀ z ∈ x :: p1, Gc.edge z ∈ Gc.kernel rc ∧ h (Gc.edge z) = Gm.edge (h z) := by
    intro z hz
    obtain ⟨z', hz', zRz'⟩ := Embed.path_belast xRp z (by rw [belast_concat]; exact hz)
    have ac_z := p_ac z (by
      rcases List.mem_cons.1 hz with e | hz
      · rw [e]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hz))
    have ac_z' := p_ac z' (List.mem_cons_of_mem _ hz')
    have ac_ez : Gc.edge z ∈ Gc.kernel rc := (acF.connect_iff zRz').2 ac_z'
    exact ⟨ac_ez, E.embed_functor ac_z ac_ez⟩
  have hlastE := hEac (last x p1) (mem_last x p1)
  -- the reverse ring `rx :: rp` and its image
  have Ehrp : (Gc.edge (last x p1) :: (((belast x p1).map Gc.edge).reverse ++ [ry])).map h =
      (Gm.revRing ((x :: (p1 ++ [y])).map h)).rotate 1 := by
    have e1 : x :: (p1 ++ [y]) = (belast x p1 ++ [last x p1]) ++ [y] := by
      rw [← lastI]
      rfl
    have hmapE : (belast x p1).map (fun z => h (Gc.edge z)) =
        (belast x p1).map (fun z => Gm.edge (h z)) :=
      List.map_congr_left (fun z hz => (hEac z (mem_belast hz)).2)
    rw [e1]
    simp only [revRing, List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.map_reverse, List.map_map, hry, hlastE.2]
    rw [List.rotate_cons_succ, List.rotate_zero]
    simp only [Function.comp_def, hmapE, List.cons_append]
  have hlen : (Gc.edge (last x p1) :: (((belast x p1).map Gc.edge).reverse ++ [ry])).length =
      (x :: (p1 ++ [y])).length := by
    simp [length_belast]
  refine E.full_step4 (x := Gc.edge (last x p1))
    (p := ((belast x p1).map Gc.edge).reverse ++ [ry]) ⟨?_, ?_, ?_⟩ ?_ ?_
  · -- the reverse ring is an R-path
    have xRp1 : path Gc.rlink x p1 := (path_concat.1 xRp).1
    have hrev : path (fun a b => Gc.rlink (Gc.edge a) (Gc.edge b)) (last x p1)
        (belast x p1).reverse := by
      apply path_reverse.2
      refine path.mono (fun a b (hab : Gc.cface (Gc.edge a) b) => ?_) xRp1
      show Gc.cface (Gc.edge (Gc.edge b)) (Gc.edge a)
      rw [E.e2c]
      exact Gc.cfaceC.1 hab
    rw [path_concat]
    refine ⟨?_, ?_⟩
    · rw [← List.map_reverse]
      exact path_map.2 hrev
    · rw [← List.map_reverse, last_map, last_last_belast_reverse]
      show Gc.cface (Gc.edge (Gc.edge x)) ry
      rw [E.e2c]
      exact xFry
  · intro z hz
    rcases List.mem_cons.1 hz with hz | hz
    · rw [hz]
      exact hlastE.1
    rcases List.mem_append.1 hz with hz | hz
    · rw [List.mem_reverse] at hz
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hz
      exact (hEac t (mem_belast ht)).1
    · rw [List.mem_singleton.1 hz]
      exact ac_ry
  · rw [Ehrp]
    exact (Gm.rot_scycle 1 _ _).2 (Gm.scycle_rev_ring E.geoGm URhp)
  · rw [last_concat]
    intro ryRrx
    apply Lp
    rw [last_concat]
    have p1Ry : Gc.rlink (last x p1) y := (path_concat.1 xRp).2
    have ryRy : Gc.cface (Gc.edge ry) y := connect_trans ryRrx p1Ry
    have ac_ery : Gc.edge ry ∈ Gc.kernel rc := (acF.connect_iff ryRy).2 ac_y
    have Dhy : h (Gc.edge ry) = h y := by rw [E.embed_functor ac_ry ac_ery, hry, E.e2m]
    have e := E.cface_inj_embed ac_ery ryRy Dhy
    show Gc.cface (Gc.edge y) x
    rw [← e, E.e2c]
    exact Gc.cfaceC.1 xFry
  · rw [Ehrp, Gm.diskF_rot, Gm.diskF_rev_ring E.geoGm URhp hp_ok, hlen]
    by_contra hgt
    rw [not_le] at hgt
    apply Gm.birkhoff E.cexGm (r := (x :: (p1 ++ [y])).map h)
      (by simp only [List.length_map, List.length_cons, List.length_append,
        List.length_nil] at hp4 ⊢; omega) URhp
    rw [List.length_map]
    exact ⟨triv, hgt⟩

/-- The induction of the Coq proof of the first `suffices` of math-comp `embed_full`: an
R-path `x0 :: p` in the kernel can be shortened to one whose image is simple, with the same
last dart. -/
private theorem full_shorten : ∀ (p : List Dc) (x0 : Dc), path Gc.rlink x0 p →
    (∀ z ∈ p, z ∈ Gc.kernel rc) → p.length ≤ 5 →
    ∃ q, (path Gc.rlink x0 q ∧ last x0 q = last x0 p ∧ ∀ z ∈ q, z ∈ Gc.kernel rc) ∧
      Gm.Simple (q.map h) ∧ q.length ≤ p.length := by
  intro p
  induction p with
  | nil =>
    intro x0 _ _ _
    exact ⟨[], ⟨trivial, rfl, fun z hz => absurd hz List.not_mem_nil⟩,
      (Gm.simple_recI []).2 trivial, le_refl _⟩
  | cons x1 p IHp =>
    intro x0 x0Rp p_ac ple5
    obtain ⟨x0Rx1, x1Rp⟩ := x0Rp
    have ac_x1 := p_ac x1 List.mem_cons_self
    obtain ⟨q, ⟨x1Rq, Lq, q_ac⟩, Uq, leqp⟩ := IHp x1 x1Rp
      (fun z hz => p_ac z (List.mem_cons_of_mem _ hz))
      (by simp only [List.length_cons] at ple5; omega)
    by_cases qFx1 : h x1 ∈ Gm.fband (q.map h)
    swap
    · refine ⟨x1 :: q, ⟨⟨x0Rx1, x1Rq⟩, Lq, ?_⟩, ?_, by simp only [List.length_cons]; omega⟩
      · intro z hz
        rcases List.mem_cons.1 hz with hz | hz
        · rw [hz]
          exact ac_x1
        · exact q_ac z hz
      · rw [List.map_cons, Gm.simple_cons]
        exact ⟨qFx1, Uq⟩
    obtain ⟨w, hw, hx1Fw⟩ := qFx1
    obtain ⟨x2, q_x2, rfl⟩ := List.mem_map.1 hw
    have hx2Fx1 : Gm.cface (h x2) (h x1) := Gm.cfaceC.1 hx1Fw
    have ac_x2 := q_ac x2 q_x2
    obtain ⟨x3, x2Fx3, eq_hx13⟩ := E.cface_h_ac ac_x2 hx2Fx1
    have ac_x3 : x3 ∈ Gc.kernel rc := (acF.connect_iff x2Fx3).1 ac_x2
    obtain ⟨q1, q2, Dq⟩ := List.append_of_mem q_x2
    have x2Rq2 : path Gc.rlink x2 q2 := by
      rw [Dq] at x1Rq
      exact path.of_append_cons x1Rq
    have Lq2 : last x2 q2 = last x1 p := by
      rw [← Lq, Dq, last_append]
      rfl
    by_cases eq_x13 : x1 = x3
    · refine ⟨x2 :: q2, ⟨⟨?_, x2Rq2⟩, Lq2, ?_⟩, ?_, ?_⟩
      · show Gc.cface (Gc.edge x0) x2
        have := x0Rx1
        change Gc.cface (Gc.edge x0) x1 at this
        rw [eq_x13] at this
        exact connect_trans this (Gc.cfaceC.1 x2Fx3)
      · intro z hz
        exact q_ac z (by rw [Dq]; exact List.mem_append_right _ hz)
      · have := Uq
        rw [Dq, List.map_append, Gm.simple_cat] at this
        exact this.2.2
      · have := leqp
        rw [Dq] at this
        simp only [List.length_append, List.length_cons] at this ⊢
        omega
    rcases q1 with _ | ⟨x, q1'⟩
    · exfalso
      have x1Rx2 : Gc.rlink x1 x2 := by
        rw [Dq] at x1Rq
        exact x1Rq.1
      have hR := E.rlink_h ac_x1 ac_x2 x1Rx2
      exact E.bridge'Gm (h x1) (Gm.cfaceC.1 (connect_trans hR hx2Fx1))
    exfalso
    have ac_x : x ∈ Gc.kernel rc := q_ac x (by rw [Dq]; exact List.mem_cons_self)
    have x1Rx : Gc.rlink x1 x := by
      rw [Dq] at x1Rq
      exact x1Rq.1
    have xRq : path Gc.rlink x (q1' ++ [x3]) := by
      have := x1Rq
      rw [Dq] at this
      have h2 : path Gc.rlink x (q1' ++ [x2]) := by
        have h3 : path Gc.rlink x (q1' ++ x2 :: q2) := this.2
        rw [show q1' ++ x2 :: q2 = (q1' ++ [x2]) ++ q2 by simp] at h3
        exact path.take_of_append h3
      rw [path_concat] at h2 ⊢
      exact ⟨h2.1, (Gc.rlinkFr x2Fx3 _).1 h2.2⟩
    apply E.full_step3 (x := x) (p := q1' ++ [x3]) ?_ ?_ ?_
    · refine E.intro_pre_hom_ring xRq ?_ ?_ ?_
      · rw [last_concat, eq_hx13]
        exact E.rlink_h ac_x1 ac_x x1Rx
      · intro z hz
        rcases List.mem_cons.1 hz with hz | hz
        · rw [hz]
          exact ac_x
        rcases List.mem_append.1 hz with hz | hz
        · exact q_ac z (by rw [Dq]; exact List.mem_cons_of_mem _ (List.mem_append_left _ hz))
        · rw [List.mem_singleton.1 hz]
          exact ac_x3
      · have hU := Uq
        rw [Dq, List.map_append, Gm.simple_cat] at hU
        rw [show (x :: (q1' ++ [x3])).map h = (x :: q1').map h ++ [h x3] by simp,
          Gm.simple_rcons]
        refine ⟨fun hF => hU.2.1 ⟨h x2, List.mem_cons_self, ?_⟩, hU.1⟩
        rw [eq_hx13] at hF
        exact ((Gm.fbandF _).connect_iff hx2Fx1).2 hF
    · rw [last_concat]
      intro x3Rx
      have ac_ex1 : Gc.edge x1 ∈ Gc.kernel rc := (acF.connect_iff x1Rx).2 ac_x
      have ex1Fex3 : Gc.cface (Gc.edge x1) (Gc.edge x3) :=
        connect_trans x1Rx (Gc.cfaceC.1 x3Rx)
      have ac_ex3 : Gc.edge x3 ∈ Gc.kernel rc := (acF.connect_iff ex1Fex3).1 ac_ex1
      apply eq_x13
      apply Gc.edgeI
      apply E.cface_inj_embed ac_ex1 ex1Fex3
      rw [E.embed_functor ac_x1 ac_ex1, E.embed_functor ac_x3 ac_ex3, eq_hx13]
    · have := leqp
      rw [Dq] at this
      simp only [List.length_append, List.length_cons, List.length_nil] at this ple5 ⊢
      omega

/-- The first `suffices` of math-comp `embed_full`: there is no R-path `x0 :: p` in the kernel,
with `size p ≤ 5`, `last x0 p ≠ x0` and `edge (h (last x0 p)) = h (edge x0)`. -/
private theorem full_step2 {x0 : Dc} {p : List Dc} (x0Rp : path Gc.rlink x0 p)
    (Lp : last x0 p ≠ x0) (p_ac : ∀ z ∈ p, z ∈ Gc.kernel rc)
    (Lhp : Gm.edge (h (last x0 p)) = h (Gc.edge x0)) (ple5 : p.length ≤ 5) : False := by
  obtain ⟨q, ⟨x0Rq, Lq, q_ac⟩, Uq, leqp⟩ := E.full_shorten p x0 x0Rp p_ac ple5
  rcases q with _ | ⟨x, q⟩
  · exact Lp Lq.symm
  obtain ⟨x0Rx, xRq⟩ := x0Rq
  have ac_x := q_ac x List.mem_cons_self
  have Lq' : last x q = last x0 p := Lq
  have ac_ex0 : Gc.edge x0 ∈ Gc.kernel rc := (acF.connect_iff x0Rx).2 ac_x
  apply E.full_step3 (x := x) (p := q) ?_ ?_
    (by simp only [List.length_cons] at leqp; omega)
  · refine E.intro_pre_hom_ring xRq ?_ q_ac Uq
    show Gm.cface (Gm.edge (h (last x q))) (h x)
    rw [Lq', Lhp]
    exact E.cface_ac_h ac_ex0 x0Rx
  · intro qRx
    rw [Lq'] at qRx
    apply Lp
    have ac_L : last x0 p ∈ Gc.kernel rc := by
      rw [← Lq']
      exact q_ac _ (mem_last x q)
    have ac_eL : Gc.edge (last x0 p) ∈ Gc.kernel rc := (acF.connect_iff qRx).2 ac_x
    apply Gc.edgeI
    apply E.cface_inj_embed ac_eL (connect_trans qRx (Gc.cfaceC.1 x0Rx))
    rw [E.embed_functor ac_L ac_eL, Lhp]

/-- math-comp `embed_full`: `{in ac &, forall x1 x2, edge (h x1) = h x2 -> edge x1 = x2}`. -/
theorem embed_full {x1 x2 : Dc} (hx1 : x1 ∈ Gc.kernel rc) (hx2 : x2 ∈ Gc.kernel rc)
    (ehx : Gm.edge (h x1) = h x2) : Gc.edge x1 = x2 := by
  by_contra x2'ex1
  obtain ⟨x0, ac_x0, ac_x0rad2⟩ := E.embedGc.kernel
  obtain ⟨x01, x10, ⟨x0Fx01, x1Fx10⟩, ac_ex01, ex01Fex10⟩ :=
    (Gc.at_radius2P acF).1 (ac_x0rad2 x1 hx1)
  obtain ⟨x02, x20, ⟨x0Fx02, x2Fx20⟩, ac_ex02, ex02Fex20⟩ :=
    (Gc.at_radius2P acF).1 (ac_x0rad2 x2 hx2)
  apply E.full_step2 (x0 := Gc.edge x1) (p := [x10, Gc.edge x01, x02, Gc.edge x20, x2])
  · refine ⟨?_, ?_, ?_, ?_, ?_, trivial⟩
    · show Gc.cface (Gc.edge (Gc.edge x1)) x10
      rw [E.e2c]
      exact x1Fx10
    · show Gc.cface (Gc.edge x10) (Gc.edge x01)
      exact Gc.cfaceC.1 ex01Fex10
    · show Gc.cface (Gc.edge (Gc.edge x01)) x02
      rw [E.e2c]
      exact connect_trans (Gc.cfaceC.1 x0Fx01) x0Fx02
    · show Gc.cface (Gc.edge x02) (Gc.edge x20)
      exact ex02Fex20
    · show Gc.cface (Gc.edge (Gc.edge x20)) x2
      rw [E.e2c]
      exact Gc.cfaceC.1 x2Fx20
  · show x2 ≠ Gc.edge x1
    exact fun e => x2'ex1 e.symm
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with hz | hz | hz | hz | hz <;> rw [hz]
    · exact (acF.connect_iff x1Fx10).1 hx1
    · exact ac_ex01
    · exact (acF.connect_iff x0Fx02).1 ac_x0
    · exact (acF.connect_iff ex02Fex20).1 ac_ex02
    · exact hx2
  · show Gm.edge (h x2) = h (Gc.edge (Gc.edge x1))
    rw [E.e2c, ← ehx, E.e2m]
  · simp

end EmbedHyps

end Hypermap

end FourColor
