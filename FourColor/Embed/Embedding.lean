/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Embed.Full

/-!
# The embedding (part of the port of `embed.v`)

* `E.pre_embed_inj` : the preembedding `h` is injective on the kernel;
* `Gm.embed Gc rc h` : the extension of `h` from the kernel `ac` to `bc := [predC rc]`
  (math-comp `embed`, notation `h1`);
* `E.embed_cases`, `E.embedE`, `E.embedN`, `E.embed_inj` : every dart has a kernel dart within
  one edge or node step; `embed` commutes with `edge` everywhere, with `node` on `bc`, and is
  injective on `bc`.

## Porting notes

* `embed` is a classical `if` cascade on membership in the kernel (the kernel is a `Set`); the
  equations `embed_of_mem`, `embed_of_edge`, `embed_of_node` and `embed_of_else` unfold it.
* The `wlog` of the Coq proofs of `embedE` and `embed_inj` are explicit case splits.
-/

namespace FourColor

open Function

universe u v

namespace Hypermap

section EmbedDef

variable {Dm : Type u} {Dc : Type v}

open Classical in
/-- math-comp `embed` (notation `h1`): an extension of `h` from `ac := kernel rc` to an
embedding of `bc := [predC rc]`:
`if x \in ac then h x else if edge x \in ac then edge (h (edge x)) else
 if node x \in ac then face (edge (h (node x))) else edge (node (node (h (node (edge x)))))`. -/
noncomputable def embed (Gm : Hypermap Dm) (Gc : Hypermap Dc) (rc : List Dc) (h : Dc → Dm)
    (x : Dc) : Dm :=
  if x ∈ Gc.kernel rc then h x
  else if Gc.edge x ∈ Gc.kernel rc then Gm.edge (h (Gc.edge x))
  else if Gc.node x ∈ Gc.kernel rc then Gm.face (Gm.edge (h (Gc.node x)))
  else Gm.edge (Gm.node (Gm.node (h (Gc.node (Gc.edge x)))))

variable {Gm : Hypermap Dm} {Gc : Hypermap Dc} {rc : List Dc} {h : Dc → Dm}

/-- `embed` on the kernel. -/
theorem embed_of_mem {x : Dc} (hx : x ∈ Gc.kernel rc) : Gm.embed Gc rc h x = h x := by
  unfold embed
  rw [ite_eq_left hx]

/-- `embed` at the darts whose edge is in the kernel. -/
theorem embed_of_edge {x : Dc} (hx : x ∉ Gc.kernel rc) (hex : Gc.edge x ∈ Gc.kernel rc) :
    Gm.embed Gc rc h x = Gm.edge (h (Gc.edge x)) := by
  unfold embed
  rw [ite_eq_right hx, ite_eq_left hex]

/-- `embed` at the darts whose node is in the kernel. -/
theorem embed_of_node {x : Dc} (hx : x ∉ Gc.kernel rc) (hex : Gc.edge x ∉ Gc.kernel rc)
    (hnx : Gc.node x ∈ Gc.kernel rc) :
    Gm.embed Gc rc h x = Gm.face (Gm.edge (h (Gc.node x))) := by
  unfold embed
  rw [ite_eq_right hx, ite_eq_right hex, ite_eq_left hnx]

/-- `embed` at the other darts. -/
theorem embed_of_else {x : Dc} (hx : x ∉ Gc.kernel rc) (hex : Gc.edge x ∉ Gc.kernel rc)
    (hnx : Gc.node x ∉ Gc.kernel rc) :
    Gm.embed Gc rc h x = Gm.edge (Gm.node (Gm.node (h (Gc.node (Gc.edge x))))) := by
  unfold embed
  rw [ite_eq_right hx, ite_eq_right hex, ite_eq_right hnx]

end EmbedDef

namespace EmbedHyps

variable {Dm : Type u} [Fintype Dm] {Gm : Hypermap Dm}
  {Dc : Type v} [Fintype Dc] [DecidableEq Dc] {Gc : Hypermap Dc} {rc : List Dc} {h : Dc → Dm}
  (E : EmbedHyps Gm Gc rc h)
include E

/-- math-comp `pre_embed_inj`: `h` is injective on the kernel. -/
theorem pre_embed_inj [DecidableEq Dm] {x y : Dc} (hx : x ∈ Gc.kernel rc) (hy : y ∈ Gc.kernel rc)
    (Dhx : h x = h y) : x = y := by
  have ac_eex : Gc.edge (Gc.edge x) ∈ Gc.kernel rc := by rw [E.e2c]; exact hx
  obtain ⟨p, ⟨exRp, Lp, ntp⟩, -, p_ac⟩ := E.h_spoke ac_eex hy
  rcases p with _ | ⟨z1, _ | ⟨z2, p⟩⟩
  · exact absurd rfl ntp
  · have xFz1 : Gc.cface x z1 := by
      have := exRp.1
      change Gc.cface (Gc.edge (Gc.edge x)) z1 at this
      rwa [E.e2c] at this
    exact E.cface_inj_embed hx (connect_trans xFz1 Lp) Dhx
  · obtain ⟨exRz1, z1Rz2, -⟩ := exRp
    have xFz1 : Gc.cface x z1 := by
      change Gc.cface (Gc.edge (Gc.edge x)) z1 at exRz1
      rwa [E.e2c] at exRz1
    obtain ⟨ac_z1, hez1⟩ := p_ac z1 List.mem_cons_self
    have ac_z2 := (p_ac z2 (List.mem_cons_of_mem _ List.mem_cons_self)).1
    have hxFhz1 := E.cface_ac_h hx xFz1
    rw [Dhx] at hxFhz1
    obtain ⟨t, yFt, Dht⟩ := E.cface_h_ac hy hxFhz1
    have ac_t : t ∈ Gc.kernel rc := (acF.connect_iff yFt).1 hy
    have ac_ez1 : Gc.edge z1 ∈ Gc.kernel rc := (acF.connect_iff z1Rz2).2 ac_z2
    have e := E.embed_full ac_t ac_ez1
      (by rw [Dht]; exact (hez1 : h (Gc.edge z1) = Gm.edge (h z1)).symm)
    have tz1 : t = z1 := Gc.edgeI e
    apply E.cface_inj_embed hx _ Dhx
    rw [tz1] at yFt
    exact connect_trans xFz1 (Gc.cfaceC.1 yFt)

/-- math-comp `embed_cases`: every dart is within one edge or node step of the kernel. -/
theorem embed_cases (x : Dc) :
    (x ∈ Gc.kernel rc ∨ Gc.edge x ∈ Gc.kernel rc) ∨
      Gc.node x ∈ Gc.kernel rc ∨ Gc.node (Gc.edge x) ∈ Gc.kernel rc := by
  have in_bc : ∀ x, x ∉ rc →
      (x ∈ Gc.kernel rc ∨ Gc.edge x ∈ Gc.kernel rc) ∨ Gc.node x ∈ Gc.kernel rc := by
    intro x bc_x
    by_cases rc_ex : Gc.edge x ∈ rc
    swap
    · exact Or.inl (E.chordless_perimeter bc_x rc_ex)
    by_cases rc_enx : Gc.edge (Gc.node x) ∈ rc
    swap
    · have bc_nx : Gc.node x ∉ rc := fun h' => bc_x (E.rc_node.1 h')
      rcases E.chordless_perimeter bc_nx rc_enx with h' | h'
      · exact Or.inr h'
      · exact Or.inl (Or.inl ((acF _ _ (Gc.nodeK x)).1 h'))
    exfalso
    have rc_fx : Gc.face x ∈ rc := E.rc_node.1 (by rw [Gc.plain_eq' E.plainGc]; exact rc_ex)
    have Dfx : Gc.face x = Gc.edge (Gc.node x) :=
      Gc.scycle_cface E.UNrc _ rc_fx _ rc_enx
        (connect_trans (Gc.cfaceC.1 (fconnect1 _ _)) (Gc.cfaceC.1 (cface_edge_node x)))
    have ffx : Gc.face (Gc.face x) = x := by rw [Dfx]; exact Gc.nodeK x
    have fx'x : Gc.face x ≠ x := fun e => bc_x (e ▸ rc_fx)
    have ar : Gc.arity (Gc.face x) = 2 :=
      order_cycle (p := [Gc.face x, x]) ⟨ffx, rfl, trivial⟩
        (List.nodup_cons.2 ⟨by simpa using fx'x, List.nodup_singleton x⟩) List.mem_cons_self
    have := (Gc.goodRingArity_iff _).1 (E.embedGc.ring _ rc_fx)
    omega
  rcases E.edge_perimeter x with bc_x | bc_ex
  · rcases in_bc x bc_x with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · rcases in_bc (Gc.edge x) bc_ex with (h' | h') | h'
    · exact Or.inl (Or.inr h')
    · rw [E.e2c] at h'
      exact Or.inl (Or.inl h')
    · exact Or.inr (Or.inr h')

omit [DecidableEq Dc] in
/-- In the cubic map `Gm`, `node (node w) = face (edge w)`. -/
private theorem nn_m (w : Dm) : Gm.node (Gm.node w) = Gm.face (Gm.edge w) := by
  have := Gm.nodeK (Gm.node (Gm.node w))
  rw [E.n3m] at this
  exact this.symm

/-- A dart off the ring outside the kernel, whose edge is outside the kernel, has its node in
the kernel (math-comp local `bc_acN` of `embed_inj`). -/
theorem bc_acN {z : Dc} (bc_z : z ∉ rc) (ac'z : z ∉ Gc.kernel rc)
    (ac'ez : Gc.edge z ∉ Gc.kernel rc) : Gc.node z ∈ Gc.kernel rc := by
  rcases E.embed_cases z with (h' | h') | h' | h'
  · exact absurd h' ac'z
  · exact absurd h' ac'ez
  · exact h'
  · exfalso
    have bc_ez : Gc.edge z ∉ rc := fun h'' => ac_bc h' (E.rc_node.2 h'')
    rcases E.chordless_perimeter bc_z bc_ez with h'' | h''
    · exact ac'z h''
    · exact ac'ez h''

/-- math-comp `embedE`: `{morph h1 : x / edge x}`. -/
theorem embedE (x : Dc) : Gm.embed Gc rc h (Gc.edge x) = Gm.edge (Gm.embed Gc rc h x) := by
  suffices H : ∀ x, x ∉ rc → Gm.embed Gc rc h (Gc.edge x) = Gm.edge (Gm.embed Gc rc h x) by
    rcases E.edge_perimeter x with bc_x | bc_ex
    · exact H x bc_x
    · have := H (Gc.edge x) bc_ex
      rw [E.e2c] at this
      rw [this, E.e2m]
  intro x bc_x
  by_cases hex : Gc.edge x ∈ Gc.kernel rc <;> by_cases hx : x ∈ Gc.kernel rc
  · rw [embed_of_mem hex, embed_of_mem hx]
    exact E.embed_functor hx hex
  · rw [embed_of_mem hex, embed_of_edge hx hex, E.e2m]
  · rw [embed_of_edge hex (by rw [E.e2c]; exact hx), embed_of_mem hx, E.e2c]
  · by_cases hnex : Gc.node (Gc.edge x) ∈ Gc.kernel rc
    · exfalso
      have bc_ex : Gc.edge x ∉ rc := fun h' => ac_bc hnex (E.rc_node.2 h')
      rcases E.chordless_perimeter bc_x bc_ex with h' | h'
      · exact hx h'
      · exact hex h'
    have hnx := E.bc_acN bc_x hx hex
    rw [embed_of_else hex (by rw [E.e2c]; exact hx) hnex, embed_of_node hx hex hnx, E.e2c,
      E.nn_m]

/-- math-comp `embedN`: `{in bc, {morph h1 : x / node x}}`. -/
theorem embedN {x : Dc} (bc_x : x ∉ rc) :
    Gm.embed Gc rc h (Gc.node x) = Gm.node (Gm.embed Gc rc h x) := by
  have hen : Gc.edge (Gc.node x) ∈ Gc.kernel rc ↔ x ∈ Gc.kernel rc := acF _ _ (Gc.nodeK x)
  have nn : Gc.face (Gc.edge x) = Gc.node (Gc.node x) := by
    have := Gc.nodeK (Gc.node (Gc.node x))
    rwa [E.n3c bc_x] at this
  have hnn : Gc.node (Gc.node x) ∈ Gc.kernel rc ↔ Gc.edge x ∈ Gc.kernel rc := by
    rw [← nn]
    exact (acF _ _ rfl).symm
  by_cases hx : x ∈ Gc.kernel rc
  · have ac_enx := hen.2 hx
    rw [embed_of_mem hx]
    apply Gm.edgeI
    rw [← E.h_edge_node hx]
    by_cases hnx : Gc.node x ∈ Gc.kernel rc
    · rw [embed_of_mem hnx, E.embed_functor hnx ac_enx]
    · rw [embed_of_edge hnx ac_enx, E.e2m]
  by_cases hex : Gc.edge x ∈ Gc.kernel rc
  · rw [embed_of_edge hx hex]
    have ac_nnx := hnn.2 hex
    have ac_fex : Gc.face (Gc.edge x) ∈ Gc.kernel rc := (acF _ _ rfl).1 hex
    -- `edge (h (edge x)) = node (h (node (node x)))`
    have e1 : Gm.edge (h (Gc.edge x)) = Gm.node (h (Gc.node (Gc.node x))) := by
      rw [← nn, E.hF hex, Gm.plain_eq' E.plainGm]
    rw [e1]
    by_cases hnx : Gc.node x ∈ Gc.kernel rc
    · rw [embed_of_mem hnx]
      have ac_ennx : Gc.edge (Gc.node (Gc.node x)) ∈ Gc.kernel rc := ac_edge_node hnx
      have e2 : h (Gc.node (Gc.node x)) = Gm.node (h (Gc.node x)) := by
        apply Gm.edgeI
        rw [← E.embed_functor ac_nnx ac_ennx, E.h_edge_node hnx]
      rw [e2, E.n3m]
    · rw [embed_of_node hnx (fun h' => hx (hen.1 h')) ac_nnx, E.nn_m]
  have ac'nnx : Gc.node (Gc.node x) ∉ Gc.kernel rc := fun h' => hex (hnn.1 h')
  by_cases hnx : Gc.node x ∈ Gc.kernel rc
  · rw [embed_of_mem hnx, embed_of_node hx hex hnx, Gm.edgeK]
  · exfalso
    rcases E.embed_cases x with (h' | h') | h' | h'
    · exact hx h'
    · exact hex h'
    · exact hnx h'
    · have bc_ex : Gc.edge x ∉ rc := fun h'' => ac_bc h' (E.rc_node.2 h'')
      rcases E.chordless_perimeter bc_x bc_ex with h'' | h''
      · exact hx h''
      · exact hex h''

/-- math-comp `embed_inj`: `{in bc &, injective h1}`. -/
theorem embed_inj [DecidableEq Dm] {x y : Dc} (bc_x : x ∉ rc) (bc_y : y ∉ rc)
    (e : Gm.embed Gc rc h x = Gm.embed Gc rc h y) : x = y := by
  have main : ∀ x y, x ∈ Gc.kernel rc → y ∉ rc →
      Gm.embed Gc rc h x = Gm.embed Gc rc h y → x = y := by
    intro x y ac_x bc_y e
    rw [embed_of_mem ac_x] at e
    by_cases ac_y : y ∈ Gc.kernel rc
    · rw [embed_of_mem ac_y] at e
      exact E.pre_embed_inj ac_x ac_y e
    by_cases ac_ey : Gc.edge y ∈ Gc.kernel rc
    · rw [embed_of_edge ac_y ac_ey] at e
      have := E.embed_full ac_ey ac_x e.symm
      rw [E.e2c] at this
      exact this.symm
    · have ac_ny := E.bc_acN bc_y ac_y ac_ey
      rw [embed_of_node ac_y ac_ey ac_ny] at e
      have ac_enx := ac_edge_node ac_x
      have e2 : h x = Gm.face (h (Gc.edge (Gc.node x))) := by
        rw [← E.hF ac_enx, Gc.nodeK]
      rw [e2] at e
      have e3 := Gm.faceI e
      have := E.embed_full ac_ny ac_enx e3.symm
      exact (Gc.nodeI (Gc.edgeI this)).symm
  by_cases ac_x : x ∈ Gc.kernel rc
  · exact main x y ac_x bc_y e
  by_cases ac_y : y ∈ Gc.kernel rc
  · exact (main y x ac_y bc_x e.symm).symm
  by_cases ac_nx : Gc.node x ∈ Gc.kernel rc
  · apply Gc.nodeI
    apply main _ _ ac_nx (fun h' => bc_y (E.rc_node.1 h'))
    rw [E.embedN bc_x, E.embedN bc_y, e]
  by_cases ac_ny : Gc.node y ∈ Gc.kernel rc
  · apply Gc.nodeI
    symm
    apply main _ _ ac_ny (fun h' => bc_x (E.rc_node.1 h'))
    rw [E.embedN bc_x, E.embedN bc_y, e]
  have ac_ex : Gc.edge x ∈ Gc.kernel rc := by
    by_contra h'
    exact ac_nx (E.bc_acN bc_x ac_x h')
  have ac_ey : Gc.edge y ∈ Gc.kernel rc := by
    by_contra h'
    exact ac_ny (E.bc_acN bc_y ac_y h')
  apply Gc.edgeI
  apply main _ _ ac_ex (ac_bc ac_ey)
  rw [E.embedE, E.embedE, e]

end EmbedHyps

end Hypermap

end FourColor
