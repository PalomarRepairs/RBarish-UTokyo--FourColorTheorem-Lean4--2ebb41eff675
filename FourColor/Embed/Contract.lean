/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Embed.Rem

/-!
# The embedded contract and the main result (part of the port of `embed.v`)

Under the section hypotheses `E : Hypermap.EmbedHyps Gm Gc rc h` and a C-reducible contract
`Cred_cc : Gc.CReducible rc cc`:

* `E.embed_sparse`, `E.embed_valid_contract` : the image `ccr := map embed cc` of the contract
  is a valid contract of `Gm` (for the empty ring);
* `E.embedCotrace`, `E.embed_closure` : the ring traces of the remainder map on
  `rotr 1 embr_ring` form a Kempe-closed set (math-comp `embed_cotrace`, `embed_closure`);
* `E.embed_contract` : some trace is both a contract ring trace of `cc` on `rev rc` in `Gc` and
  an `embed_cotrace`;
* `E.not_embed_reducible`, `Hypermap.not_embed_reducible` : hence the configuration is not
  C-reducible, as the coclosure property of `Cred_cc` would make `Gm` four-colorable
  (math-comp `not_embed_reducible`).

## Porting notes

* The section `Let`s `mapEh1`, `ccE`, `cface_ac_h1`, `cface_h1`, `adj_ac_h1`, `orbitF_h1` are
  theorems. `cface_h1` moves the ends of a face path off the ring with the private lemma
  `embed_face_rc` (the `wlog` of the Coq proof).
* `Drc` (math-comp's last `suffices` of `not_embed_reducible`,
  `rc = map face (rot 1 (map edge rc))`) is a separate lemma, with its consequence
  `rc_map_rot` for the face-invariant functions, also used in `embed_contract`.
* `not_embed_reducible` is stated twice: `Hypermap.EmbedHyps.not_embed_reducible` under the
  bundled hypotheses, and `Hypermap.not_embed_reducible`, with the four hypotheses of the Coq
  section as explicit arguments (the form used by `present.v`).
-/

namespace FourColor

open Function

universe u v

namespace Embed

/-- A list whose image by `g` is duplicate-free has a duplicate-free image by `f` if equal
`f`-images have equal `g`-images. -/
theorem nodup_map_of_imp {α β γ : Type*} {f : α → β} {g : α → γ} :
    ∀ {l : List α}, (l.map g).Nodup → (∀ a ∈ l, ∀ b ∈ l, f a = f b → g a = g b) →
      (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hg, h => by
    rw [List.map_cons, List.nodup_cons] at hg ⊢
    refine ⟨fun hm => ?_, nodup_map_of_imp hg.2 (fun x hx y hy =>
      h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))⟩
    obtain ⟨b, hb, e⟩ := List.mem_map.1 hm
    exact hg.1 (List.mem_map.2
      ⟨b, hb, (h a List.mem_cons_self b (List.mem_cons_of_mem _ hb) e.symm).symm⟩)

end Embed

namespace Hypermap

namespace EmbedHyps

variable {Dm : Type u} [Fintype Dm] [DecidableEq Dm] {Gm : Hypermap Dm}
  {Dc : Type v} [Fintype Dc] [DecidableEq Dc] {Gc : Hypermap Dc} {rc : List Dc} {h : Dc → Dm}
  (E : EmbedHyps Gm Gc rc h)
include E

omit [DecidableEq Dm] in
/-- math-comp local `mapEh1`: `insertE (map h1 p) = map h1 (insertE p)`. -/
theorem mapEh1 (p : List Dc) :
    Gm.insertE (p.map (Gm.embed Gc rc h)) = (Gc.insertE p).map (Gm.embed Gc rc h) := by
  induction p with
  | nil => rfl
  | cons x p ih => simp only [List.map_cons, insertE, ih, E.embedE]

omit [DecidableEq Dm] [DecidableEq Dc] in
/-- math-comp local `ccE`: `insertE cc` is edge-closed. -/
theorem ccE {cc : List Dc} {x : Dc} (hx : x ∈ Gc.insertE cc) : Gc.edge x ∈ Gc.insertE cc := by
  rw [Gc.mem_insertE E.plainGc] at hx ⊢
  obtain ⟨y, hy, xEy⟩ := hx
  exact ⟨y, hy, (Gc.cedge1 x y).1 xEy⟩

omit [DecidableEq Dm] in
/-- `h1` commutes with the iterates of `node` on `bc`. -/
theorem embed_node_iter {x : Dc} (bc_x : x ∉ rc) (n : ℕ) :
    Gc.node^[n] x ∉ rc ∧ Gm.embed Gc rc h (Gc.node^[n] x) = Gm.node^[n] (Gm.embed Gc rc h x) := by
  induction n with
  | zero => exact ⟨bc_x, rfl⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', E.embedN h1, h2]
    exact ⟨fun h' => h1 (E.rc_node.1 h'), rfl⟩

/-- math-comp `embed_sparse`: the edge closure of the image of the contract is sparse. -/
theorem embed_sparse {cc : List Dc} (Cred_cc : Gc.CReducible rc cc) :
    Gm.Sparse (Gm.insertE (cc.map (Gm.embed Gc rc h))) := by
  have rc'cc : ∀ x ∈ Gc.insertE cc, x ∉ rc := fun x hx hrc => Cred_cc.off_ring hrc hx
  unfold Sparse
  rw [E.mapEh1, List.map_map]
  apply Embed.nodup_map_of_imp Cred_cc.sparse
  intro a ha b hb e
  have hab : Gm.cnode (Gm.embed Gc rc h a) (Gm.embed Gc rc h b) := (root_eq_iff Gm.cnode_sym).1 e
  obtain ⟨n, hn⟩ := fconnect_iff_iterate.1 hab
  obtain ⟨bc_n, hn'⟩ := E.embed_node_iter (rc'cc a ha) n
  rw [← hn'] at hn
  have e2 := E.embed_inj bc_n (rc'cc b hb) hn
  exact (root_eq_iff Gc.cnode_sym).2 (by rw [← e2]; exact fconnect_iterate _ _ _)

omit [DecidableEq Dm] in
/-- A dart `y` of the ring is in the face of `face y`, which is off the ring, and so are their
images by `h1` (the `wlog` of math-comp `cface_ac_h1` and `cface_h1`). -/
private theorem embed_face_rc {y : Dc} (rc_y : y ∈ rc) :
    Gc.face y ∉ rc ∧ Gm.cface (Gm.embed Gc rc h y) (Gm.embed Gc rc h (Gc.face y)) := by
  have bc_ey : Gc.edge y ∉ rc := (E.edge_perimeter y).resolve_left (not_not.2 rc_y)
  have bc_fy : Gc.face y ∉ rc := fun h' => bc_ey (by
    rw [← Gc.plain_eq' E.plainGc]
    exact E.rc_node.2 h')
  refine ⟨bc_fy, ?_⟩
  have e : Gm.embed Gc rc h y = Gm.edge (Gm.node (Gm.embed Gc rc h (Gc.face y))) := by
    conv_lhs => rw [← Gc.faceK y]
    rw [E.embedE, E.embedN bc_fy]
  rw [e]
  have := fconnect1 Gm.face (Gm.edge (Gm.node (Gm.embed Gc rc h (Gc.face y))))
  rwa [Gm.nodeK] at this

omit [DecidableEq Dm] in
/-- Any dart is in the face of a dart off the ring, with the same property for the images. -/
private theorem embed_off_ring (z : Dc) : ∃ z', z' ∉ rc ∧ Gc.cface z z' ∧
    Gm.cface (Gm.embed Gc rc h z) (Gm.embed Gc rc h z') := by
  by_cases hz : z ∈ rc
  · obtain ⟨h1, h2⟩ := E.embed_face_rc hz
    exact ⟨Gc.face z, h1, fconnect1 _ _, h2⟩
  · exact ⟨z, hz, connect_refl _, connect_refl _⟩

/-- math-comp local `cface_h1`: `{homo h1 : x y / cface x y}`. -/
theorem cface_h1 {x y : Dc} (hxy : Gc.cface x y) :
    Gm.cface (Gm.embed Gc rc h x) (Gm.embed Gc rc h y) := by
  obtain ⟨x', bc_x', xFx', hx'⟩ := E.embed_off_ring x
  obtain ⟨y', bc_y', yFy', hy'⟩ := E.embed_off_ring y
  have x'Fy' : Gc.cface x' y' := connect_trans (Gc.cfaceC.1 xFx') (connect_trans hxy yFy')
  have hd : E.embedDisk.cface ⟨x', bc_x'⟩ ⟨y', bc_y'⟩ :=
    (E.cface_embd ⟨x', bc_x'⟩ ⟨y', bc_y'⟩).1 x'Fy'
  have hm : Gm.cface (Gm.embed Gc rc h x') (Gm.embed Gc rc h y') :=
    E.embed_patch.patch_face_d' hd
  exact connect_trans hx' (connect_trans hm (Gm.cfaceC.1 hy'))

/-- math-comp local `cface_ac_h1`: `{in ac, {mono h1 : x y / cface x y}}`. -/
theorem cface_ac_h1 {x : Dc} (hx : x ∈ Gc.kernel rc) (y : Dc) :
    Gm.cface (Gm.embed Gc rc h x) (Gm.embed Gc rc h y) ↔ Gc.cface x y := by
  refine ⟨fun hF => ?_, E.cface_h1⟩
  obtain ⟨y', bc_y', yFy', hy'⟩ := E.embed_off_ring y
  suffices hxy' : Gc.cface x y' from connect_trans hxy' (Gc.cfaceC.1 yFy')
  have bc_x : x ∉ rc := ac_bc hx
  have hout : Gm.embdd Gc rc h ⟨x, bc_x⟩ ∉ Gm.outer (Gm.embr Gc rc h) := by
    rintro ⟨z, ⟨w, rfl⟩, hxz⟩
    have hxz' : Gm.cface (h x) (Gm.embr Gc rc h w) := by
      have e : Gm.embed Gc rc h x = h x := embed_of_mem hx
      rw [← e]
      exact hxz
    obtain ⟨x1, xFx1, Dx1⟩ := E.cface_h_ac hx hxz'
    have ac_x1 : x1 ∈ Gc.kernel rc := (acF.connect_iff xFx1).1 hx
    apply w.2
    refine ⟨⟨x1, ac_bc ac_x1⟩, ?_, ?_⟩
    · intro hm0
      have hm := E.mem_embd_ring.1 hm0
      obtain ⟨r, hr, er⟩ := List.mem_map.1 hm
      have er' : Gc.edge r = x1 := er
      have rc_fx1 : Gc.face x1 ∈ rc :=
        E.rc_node.1 (by rw [Gc.plain_eq' E.plainGc, ← er', E.e2c]; exact hr)
      exact ac_bc ((acF _ _ rfl).1 ac_x1) rc_fx1
    · show Gm.embed Gc rc h x1 = w.1
      rw [embed_of_mem ac_x1, Dx1]
      rfl
  have hm : Gm.cface (Gm.embdd Gc rc h ⟨x, bc_x⟩) (Gm.embdd Gc rc h ⟨y', bc_y'⟩) :=
    connect_trans hF hy'
  exact (E.cface_embd ⟨x, bc_x⟩ ⟨y', bc_y'⟩).2 ((E.embed_patch.patch_face_d hout).2 hm)

/-- math-comp local `adj_ac_h1`: `{in ac &, {mono h1 : x y / adj x y}}`. -/
theorem adj_ac_h1 {x y : Dc} (hx : x ∈ Gc.kernel rc) (hy : y ∈ Gc.kernel rc) :
    Gm.adj (Gm.embed Gc rc h x) (Gm.embed Gc rc h y) ↔ Gc.adj x y := by
  rw [embed_of_mem hx, embed_of_mem hy, Gm.adjP, Gc.adjP]
  constructor
  · rintro ⟨z', hxz', z'Ry⟩
    obtain ⟨z, xFz, rfl⟩ := E.cface_h_ac hx hxz'
    have ac_z := (acF.connect_iff xFz).1 hx
    obtain ⟨t, yFt, Dt⟩ := E.cface_h_ac hy (Gm.cfaceC.1 z'Ry)
    have ac_t := (acF.connect_iff yFt).1 hy
    have Dez : Gc.edge z = t := E.embed_full ac_z ac_t Dt.symm
    refine ⟨z, xFz, ?_⟩
    show Gc.cface (Gc.edge z) y
    rw [Dez]
    exact Gc.cfaceC.1 yFt
  · rintro ⟨z, xFz, zRy⟩
    have ac_z := (acF.connect_iff xFz).1 hx
    exact ⟨h z, E.cface_ac_h hx xFz, E.rlink_h ac_z hy zRy⟩

omit [DecidableEq Dm] [DecidableEq Dc] in
/-- math-comp local `orbitF_h1`: on the kernel, `h1` maps face orbits onto face orbits. -/
theorem orbitF_h1 {x : Dc} (hx : x ∈ Gc.kernel rc) :
    orbit Gm.face (Gm.embed Gc rc h x) = (orbit Gc.face x).map (Gm.embed Gc rc h) := by
  unfold orbit
  have har : order Gm.face (Gm.embed Gc rc h x) = order Gc.face x := by
    rw [embed_of_mem hx]
    exact E.hFn hx
  rw [har]
  clear har
  generalize order Gc.face x = n
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have hfx : Gc.face x ∈ Gc.kernel rc := (acF _ _ rfl).1 hx
    show Gm.embed Gc rc h x :: List.iterate Gm.face (Gm.face (Gm.embed Gc rc h x)) n =
      Gm.embed Gc rc h x :: (List.iterate Gc.face (Gc.face x) n).map (Gm.embed Gc rc h)
    rw [← ih hfx, embed_of_mem hx, embed_of_mem hfx, E.hF hx]

/-- math-comp `embed_valid_contract`: the image of the contract is a valid contract of `Gm`, for
the empty ring. -/
theorem embed_valid_contract {cc : List Dc} (Cred_cc : Gc.CReducible rc cc) :
    Gm.ValidContract [] (cc.map (Gm.embed Gc rc h)) where
  off_ring := fun _ h' _ => absurd h' List.not_mem_nil
  sparse := E.embed_sparse Cred_cc
  size := by
    rw [List.length_map]
    exact Cred_cc.size
  triad := by
    intro h4
    rw [List.length_map] at h4
    obtain ⟨x, ac_x, adj3x, xA'cc⟩ := Cred_cc.triad h4
    refine ⟨Gm.embed Gc rc h x, fun ⟨_, h', _⟩ => absurd h' List.not_mem_nil, ?_, ?_⟩
    · rw [E.orbitF_h1 ac_x, List.countP_map, E.mapEh1]
      refine lt_of_lt_of_le adj3x (List.countP_mono_left ?_)
      intro y _ hyF
      simp only [decide_eq_true_eq, Function.comp] at hyF ⊢
      obtain ⟨z, hz, eyFz⟩ := hyF
      rw [← E.embedE]
      exact ⟨Gm.embed Gc rc h z, List.mem_map_of_mem hz, E.cface_h1 eyFz⟩
    · intro ccAx
      apply xA'cc
      intro y cc_y
      have cc_ey := E.ccE cc_y
      have bc_y : y ∉ rc := fun h' => Cred_cc.off_ring h' cc_y
      have bc_ey : Gc.edge y ∉ rc := fun h' => Cred_cc.off_ring h' cc_ey
      have hA : ∀ z ∈ Gc.insertE cc, Gm.adj (Gm.embed Gc rc h x) (Gm.embed Gc rc h z) := by
        intro z hz
        apply ccAx
        rw [E.mapEh1]
        exact List.mem_map_of_mem hz
      have hA2 := hA _ cc_ey
      rw [E.embedE] at hA2
      rcases Gm.adj11_edge E.cexGm (hA y cc_y) hA2 with h' | h'
      · rw [Gm.mem_spoke_ring, ← E.embedN bc_y, E.cface_ac_h1 ac_x] at h'
        exact Gc.adjP.2 ⟨Gc.node y, h', cface_edge_node y⟩
      · rw [Gm.mem_spoke_ring, ← E.embedE, ← E.embedN bc_ey, E.cface_ac_h1 ac_x] at h'
        have ffy : Gc.face y = Gc.node (Gc.node (Gc.edge y)) := by
          have := Gc.nodeK (Gc.node (Gc.node (Gc.edge y)))
          rw [E.n3c bc_ey, E.e2c] at this
          exact this
        have e1 : Gc.face (Gc.edge (Gc.face y)) = Gc.node (Gc.edge y) := by
          rw [ffy]
          exact Gc.nodeK _
        refine Gc.adjP.2 ⟨Gc.edge (Gc.face y), ?_, ?_⟩
        · have h2 := fconnect1 Gc.face (Gc.edge (Gc.face y))
          rw [e1] at h2
          exact connect_trans h' (Gc.cfaceC.1 h2)
        · show Gc.cface (Gc.edge (Gc.edge (Gc.face y))) y
          rw [E.e2c]
          exact Gc.cfaceC.1 (fconnect1 _ _)

/-- math-comp `embed_cotrace`: the ring traces of the remainder map on `rotr 1 embr_ring`. -/
def embedCotrace (et : Colseq) : Prop :=
  E.embedRem.RingTrace (rotr 1 (Gm.embrRing Gc rc h)) et

/-- math-comp `embed_closure`: the traces of the remainder map are Kempe-closed. -/
theorem embed_closure : KempeClosed E.embedCotrace := by
  have hU := E.ucycle_embr_ring
  apply kempe_map E.embedRem (rotr 1 (Gm.embrRing Gc rc h))
  refine { plain := E.plain_embr, quasicubic := ?_, ucycle := ?_, planar := E.planar_embr }
  · intro w hw
    exact E.cubic_embr (fun h' => hw (mem_rotr.2 h'))
  · refine ⟨?_, nodup_rotr.2 hU.2⟩
    have e : rotr 1 (Gm.embrRing Gc rc h) =
        (Gm.embrRing Gc rc h).rotate ((Gm.embrRing Gc rc h).length - 1) := by
      unfold rotr
      exact rot_eq_rotate (Nat.sub_le _ _)
    rw [e, cycle_rotate]
    exact hU.1

omit [DecidableEq Dm] [DecidableEq Dc] in
/-- The last `suffices` of math-comp `not_embed_reducible`: `rc = map face (rot 1 erc)`. -/
theorem Drc : rc = (rot 1 (rc.map Gc.edge)).map Gc.face := by
  have hcyc := E.cycNrc
  generalize rc = r at hcyc ⊢
  rcases r with _ | ⟨x, p⟩
  · rfl
  rw [List.map_cons, rot1_cons, List.map_append, List.map_singleton]
  have key : ∀ (p : List Dc) (y : Dc), fpath Gc.node y (p ++ [x]) →
      y :: p = (p.map Gc.edge).map Gc.face ++ [Gc.face (Gc.edge x)] := by
    intro p
    induction p with
    | nil =>
      intro y hy
      have e : Gc.node y = x := hy.1
      rw [← e, Gc.nodeK]
      rfl
    | cons z p ih =>
      intro y hy
      obtain ⟨e, hz⟩ := hy
      have hfz : Gc.face (Gc.edge z) = y := by
        rw [← (e : Gc.node y = z)]
        exact Gc.nodeK y
      simp only [List.map_cons, List.cons_append]
      rw [hfz, ← ih z hz]
  exact key p x hcyc

omit [DecidableEq Dm] [DecidableEq Dc] in
/-- A face-invariant function takes the same values on `rc` and on `rot 1 (map edge rc)`. -/
theorem rc_map_rot {α : Type*} (g : Dc → α) (hg : ∀ z, g (Gc.face z) = g z) :
    rc.map g = rot 1 ((rc.map Gc.edge).map g) := by
  conv_lhs => rw [E.Drc]
  rw [List.map_map, map_rot]
  congr 1
  exact List.map_congr_left (fun z _ => hg z)

/-- math-comp `embed_contract`: some trace is both a contract ring trace of `cc` on `rev rc` in
`Gc` and a ring trace of the remainder map. -/
theorem embed_contract {cc : List Dc} (Cred_cc : Gc.CReducible rc cc) :
    ∃ et, Gc.CcRingTrace cc rc.reverse et ∧ E.embedCotrace et := by
  have rc'cc : ∀ x ∈ Gc.insertE cc, x ∉ rc := fun x hx hrc => Cred_cc.off_ring hrc hx
  obtain ⟨k, kE, kF⟩ := contract_coloring E.cexGm (E.embed_valid_contract Cred_cc)
  have kFF : ∀ a b, Gm.cface a b → k a = k b := fun a b hab =>
    (Embed.fconnect_invariant kF hab).symm
  have k1F : ∀ z, k (Gm.embed Gc rc h (Gc.face z)) = k (Gm.embed Gc rc h z) :=
    fun z => (kFF _ _ (E.cface_h1 (fconnect1 _ z))).symm
  refine ⟨trace (rc.reverse.map (k ∘ Gm.embed Gc rc h)),
    ⟨k ∘ Gm.embed Gc rc h, ⟨?_, fun z => k1F z⟩, rfl⟩, ?_⟩
  · have k1Ebc : ∀ x, x ∉ rc →
        (k (Gm.embed Gc rc h (Gc.edge x)) = k (Gm.embed Gc rc h x) ↔ x ∈ Gc.insertE cc) := by
      intro x bc_x
      rw [E.embedE, kE, E.mapEh1]
      constructor
      · intro hm
        obtain ⟨z, hz, e⟩ := List.mem_map.1 hm
        rw [← E.embed_inj (rc'cc z hz) bc_x e]
        exact hz
      · intro hx
        exact List.mem_map_of_mem hx
    intro x
    show k (Gm.embed Gc rc h (Gc.edge x)) = k (Gm.embed Gc rc h x) ↔ x ∈ Gc.insertE cc
    rcases E.edge_perimeter x with bc_x | bc_ex
    · exact k1Ebc x bc_x
    · have := k1Ebc _ bc_ex
      rw [E.e2c] at this
      rw [eq_comm, this]
      constructor
      · intro h'
        have := E.ccE h'
        rwa [E.e2c] at this
      · exact E.ccE
  · refine ⟨k ∘ Gm.embr Gc rc h, ⟨?_, ?_⟩, ?_⟩
    · intro w
      show k (Gm.edge w.1) ≠ k w.1
      rw [ne_eq, kE, E.mapEh1]
      intro hm
      obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
      apply w.2
      refine ⟨⟨x, rc'cc x hx⟩, ?_, e⟩
      intro hm0
      have hm' := E.mem_embd_ring.1 hm0
      obtain ⟨r, hr, er⟩ := List.mem_map.1 hm'
      have er' : Gc.edge r = x := er
      apply rc'cc _ (E.ccE hx)
      rw [← er', E.e2c]
      exact hr
    · intro w
      show k (Gm.embr Gc rc h (E.embedRem.face w)) = k (Gm.embr Gc rc h w)
      exact (kFF _ _ ((E.embed_patch.patch_face_r w (E.embedRem.face w)).1
        (fconnect1 _ _))).symm
    · have hX : ((Gc.embdRing rc).map (Gm.embdd Gc rc h)).map k =
          (rc.map Gc.edge).map (k ∘ Gm.embed Gc rc h) := by
        have e1 : (Gc.embdRing rc).map (Gm.embdd Gc rc h) =
            ((Gc.embdRing rc).map (embd rc)).map (Gm.embed Gc rc h) := by
          rw [List.map_map]
          rfl
        rw [e1, E.map_embd_ring, List.map_map]
      have e1 : (Gm.embrRing Gc rc h).map (k ∘ Gm.embr Gc rc h) =
          (((Gc.embdRing rc).map (Gm.embdd Gc rc h)).map k).reverse := by
        rw [← List.map_map, E.map_embr_ring, List.map_reverse]
      have e2 : (rotr 1 (Gm.embrRing Gc rc h)).map (k ∘ Gm.embr Gc rc h) =
          (rot 1 ((rc.map Gc.edge).map (k ∘ Gm.embed Gc rc h))).reverse := by
        rw [map_rotr, e1, hX, ← rev_rot]
      congr 1
      rw [e2, List.map_reverse, ← E.rc_map_rot (k ∘ Gm.embed Gc rc h) k1F]

/-- math-comp `not_embed_reducible`, under the bundled section hypotheses. -/
theorem not_embed_reducible {cc : List Dc} (Cred_cc : Gc.CReducible rc cc) : False := by
  obtain ⟨et, etGc, etGr⟩ := E.embed_contract Cred_cc
  obtain ⟨et', ⟨kc, kc_col, Detc⟩, ⟨kr, kr_col, Detr⟩⟩ :=
    Cred_cc.coclosure et etGc E.embedCotrace E.embed_closure etGr
  apply E.cexGm.noncolorable
  refine E.embed_patch.colorable_patch.2 ⟨et'.reverse, ⟨kc ∘ embd rc, ⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro u
    show kc (Gc.embdEdge rc u.1) ≠ kc u.1
    unfold embdEdge
    split_ifs with h1
    · rw [← kc_col.2 (Gc.edge (Gc.node (Gc.edge u.1))), Gc.nodeK]
      exact kc_col.1 u.1
    · exact kc_col.1 u.1
  · intro u
    exact (Gc.coloring_cface kc_col
      ((E.cface_embd u (E.embedDisk.face u)).2 (fconnect1 _ _))).symm
  · rw [← List.map_map, E.map_embd_ring, Detc, List.map_reverse, trace_rev, rev_rot,
      List.reverse_reverse, E.rc_map_rot kc kc_col.2, trace_rot, rotK]
  · rw [List.reverse_reverse]
    refine ⟨kr, kr_col, ?_⟩
    rw [Detr, map_rotr, ← trace_rot, rotrK]

end EmbedHyps

/-- math-comp `not_embed_reducible`: a C-reducible configuration `Gc` with an embeddable ring
`rc` does not occur in a minimal counter-example `Gm`, that is, there is no preembedding `h`
of its kernel into `Gm`. -/
theorem not_embed_reducible {Dm : Type u} [Fintype Dm] [DecidableEq Dm] {Gm : Hypermap Dm}
    {Dc : Type v} [Fintype Dc] [DecidableEq Dc] {Gc : Hypermap Dc} {rc cc : List Dc}
    {h : Dc → Dm} (cexGm : Gm.MinimalCounterExample) (embedGc : Gc.Embeddable rc)
    (embed_h : Gc.Preembedding Gm (Gc.kernel rc) h) (Cred_cc : Gc.CReducible rc cc) : False :=
  EmbedHyps.not_embed_reducible ⟨cexGm, embedGc, embed_h⟩ Cred_cc

end Hypermap

end FourColor
