/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Embed.Embedding

/-!
# The disk map of the embedding (part of the port of `embed.v`)

The disk hypermap `E.embedDisk` delimited by `rev_ring rc` in `Gc`, constructed explicitly on
the darts `EmbdDart rc` of `bc := [predC rc]` (math-comp `embed_disk`), with its border
`Gc.embdRing rc` (math-comp `embd_ring`), its injection `embd rc` into `Gc` (math-comp `embd`),
and its injection `Gm.embdd Gc rc h` into `Gm` through `embed` (math-comp `embdd`):

* `E.map_embd_ring` : the border is mapped onto `map edge rc`;
* `E.cface_embd` : `embd` preserves and reflects faces;
* `E.scycle_embd_ring` : the border is a simple E-cycle of the disk map;
* `E.embdd_inj`, `E.embddE`, `E.embddN` : `embdd` is injective, commutes with `edge` off the
  border and with `node`.

## Porting notes

* The dart type `EmbdDart rc = {x : Dc // x ∉ rc}` does not depend on the hypotheses, and
  neither do `embdEdge`, `embdFace`, `embd`, `embdRing` and `embdd`; the permutations of the
  disk map need `E` (for their subproofs), as in `FourColor.Snip`.
* math-comp's `preim_seq` is `preimSeq` (from `FourColor.Snip`).
* In `cface_embd` the Coq induction on the length of a face path of `Gc` is an induction on the
  number of `face` steps.
-/

namespace FourColor

open Function

universe u v

namespace Hypermap

section EmbedDiskDef

variable {Dm : Type u} {Dc : Type v}

/-- The darts of the disk map `embed_disk`: the darts of `Gc` off the ring (math-comp
`Local Notation ddart := {x | x \in bc}`). -/
def EmbdDart (rc : List Dc) : Type v := {x : Dc // x ∉ rc}

/-- The (classical) finite type structure of the disk darts. -/
noncomputable instance (rc : List Dc) [Fintype Dc] : Fintype (EmbdDart rc) := by
  classical exact (inferInstance : Fintype {x : Dc // x ∉ rc})

/-- The disk darts form a finite type. -/
instance (rc : List Dc) [Finite Dc] : Finite (EmbdDart rc) :=
  inferInstanceAs (Finite {x : Dc // x ∉ rc})

/-- The disk darts have decidable equality. -/
instance (rc : List Dc) [DecidableEq Dc] : DecidableEq (EmbdDart rc) :=
  inferInstanceAs (DecidableEq {x : Dc // x ∉ rc})

/-- math-comp `embd`: the injection of the disk darts into `Gc`. -/
def embd (rc : List Dc) (u : EmbdDart rc) : Dc := u.1

/-- math-comp `embd_inj`. -/
theorem embd_inj (rc : List Dc) : Injective (embd rc) := fun _ _ e => Subtype.ext e

/-- math-comp `codom_embd`. -/
theorem codom_embd (rc : List Dc) (x : Dc) : x ∈ Set.range (embd rc) ↔ x ∉ rc :=
  ⟨by rintro ⟨u, rfl⟩; exact u.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

/-- math-comp `embd_ring`: the border of the disk map, the preimage of `map edge rc`. -/
noncomputable def embdRing (Gc : Hypermap Dc) (rc : List Dc) : List (EmbdDart rc) :=
  preimSeq (embd rc) (rc.map Gc.edge)

/-- math-comp `embdd`: the injection of the disk darts into `Gm`, through `embed`. -/
noncomputable def embdd (Gm : Hypermap Dm) (Gc : Hypermap Dc) (rc : List Dc) (h : Dc → Dm)
    (u : EmbdDart rc) : Dm :=
  Gm.embed Gc rc h u.1

variable [DecidableEq Dc] (Gc : Hypermap Dc)

/-- math-comp `embd_edge`: the edge function of the disk map, which skips the ring. -/
def embdEdge (rc : List Dc) (x : Dc) : Dc :=
  if Gc.edge x ∉ rc then Gc.edge x else Gc.edge (Gc.node (Gc.edge x))

/-- math-comp `embd_face`: the face function of the disk map, which skips the ring. -/
def embdFace (rc : List Dc) (x : Dc) : Dc :=
  if Gc.face x ∉ rc then Gc.face x else Gc.face (Gc.face x)

end EmbedDiskDef

namespace EmbedHyps

variable {Dm : Type u} [Fintype Dm] {Gm : Hypermap Dm}
  {Dc : Type v} [Fintype Dc] [DecidableEq Dc] {Gc : Hypermap Dc} {rc : List Dc} {h : Dc → Dm}
  (E : EmbedHyps Gm Gc rc h)
include E

/-- math-comp `embd_edge_subproof`. -/
theorem embd_edge_subproof (u : EmbdDart rc) : Gc.embdEdge rc u.1 ∉ rc := by
  unfold embdEdge
  split_ifs with h1
  · exact (E.edge_perimeter (Gc.node (Gc.edge u.1))).resolve_left
      (not_not.2 (E.rc_node.2 h1))
  · exact h1

omit [DecidableEq Dc] in
/-- math-comp `embd_node_subproof`. -/
theorem embd_node_subproof (u : EmbdDart rc) : Gc.node u.1 ∉ rc :=
  fun h' => u.2 (E.rc_node.1 h')

/-- math-comp `embd_face_subproof`. -/
theorem embd_face_subproof (u : EmbdDart rc) : Gc.embdFace rc u.1 ∉ rc := by
  unfold embdFace
  split_ifs with h1
  · have bc_efu : Gc.edge (Gc.face u.1) ∉ rc := (E.edge_perimeter _).resolve_left (not_not.2 h1)
    intro h2
    apply bc_efu
    rw [← Gc.plain_eq' E.plainGc]
    exact E.rc_node.2 h2
  · exact h1

/-- The edge permutation of `embed_disk` (math-comp section `Let dedge`). -/
def embedDiskEdge (u : EmbdDart rc) : EmbdDart rc := ⟨Gc.embdEdge rc u.1, E.embd_edge_subproof u⟩

/-- The node permutation of `embed_disk` (math-comp section `Let dnode`). -/
def embedDiskNode (u : EmbdDart rc) : EmbdDart rc := ⟨Gc.node u.1, E.embd_node_subproof u⟩

/-- The face permutation of `embed_disk` (math-comp section `Let dface`). -/
def embedDiskFace (u : EmbdDart rc) : EmbdDart rc := ⟨Gc.embdFace rc u.1, E.embd_face_subproof u⟩

/-- math-comp `embed_disk_subproof`: `cancel3 dedge dnode dface`. -/
theorem embed_disk_subproof (u : EmbdDart rc) :
    E.embedDiskNode (E.embedDiskFace (E.embedDiskEdge u)) = u := by
  apply Subtype.ext
  show Gc.node (Gc.embdFace rc (Gc.embdEdge rc u.1)) = u.1
  by_cases bc_eu : Gc.edge u.1 ∉ rc
  · have bc_feu : Gc.face (Gc.edge u.1) ∉ rc := fun h' => u.2 (by
      rw [← Gc.edgeK u.1]
      exact E.rc_node.2 h')
    rw [embdEdge, ite_eq_left bc_eu, embdFace, ite_eq_left bc_feu, Gc.edgeK]
  · rw [embdEdge, ite_eq_right bc_eu, embdFace, Gc.nodeK, ite_eq_right bc_eu, Gc.edgeK]

/-- math-comp `embed_disk`: the disk hypermap delimited by `rev_ring rc` in `Gc`, with the
darts of `bc`. -/
def embedDisk : Hypermap (EmbdDart rc) where
  edge := E.embedDiskEdge
  node := E.embedDiskNode
  face := E.embedDiskFace
  edgeK := E.embed_disk_subproof

omit [DecidableEq Dc] in
/-- math-comp `map_embd_ring`. -/
theorem map_embd_ring : (Gc.embdRing rc).map (embd rc) = rc.map Gc.edge := by
  apply map_preim
  intro y hy
  obtain ⟨x, rc_x, rfl⟩ := List.mem_map.1 hy
  exact (codom_embd rc _).2 ((E.edge_perimeter x).resolve_left (not_not.2 rc_x))

omit [DecidableEq Dc] in
/-- The darts of the border of the disk map are those projected on `map edge rc`. -/
theorem mem_embd_ring {u : EmbdDart rc} : u ∈ Gc.embdRing rc ↔ embd rc u ∈ rc.map Gc.edge := by
  rw [← List.mem_map_of_injective (embd_inj rc), E.map_embd_ring]

/-- math-comp `cface_embd`: `{mono embd : u v / cface u v}`. -/
theorem cface_embd (u v : EmbdDart rc) :
    Gc.cface (embd rc u) (embd rc v) ↔ E.embedDisk.cface u v := by
  constructor
  · intro huv
    obtain ⟨n, hn⟩ := fconnect_iff_iterate.1 huv
    clear huv
    induction n using Nat.strong_induction_on generalizing u with
    | _ n IH =>
      rcases n with _ | n
      · have : u = v := Subtype.ext hn
        rw [this]
      rw [Function.iterate_succ_apply] at hn
      by_cases bc_fu : Gc.face u.1 ∉ rc
      · have hf : embd rc (E.embedDisk.face u) = Gc.face (embd rc u) := by
          show Gc.embdFace rc u.1 = _
          unfold embdFace
          rw [ite_eq_left bc_fu]
          rfl
        exact connect_trans (fconnect1 _ _)
          (IH n (Nat.lt_succ_self n) (E.embedDisk.face u) (by rw [hf]; exact hn))
      rcases n with _ | n
      · exfalso
        apply v.2
        have hn' : Gc.face u.1 = v.1 := hn
        rw [← hn']
        exact not_not.1 bc_fu
      rw [Function.iterate_succ_apply] at hn
      have hf : embd rc (E.embedDisk.face u) = Gc.face (Gc.face (embd rc u)) := by
        show Gc.embdFace rc u.1 = _
        unfold embdFace
        rw [ite_eq_right bc_fu]
        rfl
      exact connect_trans (fconnect1 _ _)
        (IH n (by omega) (E.embedDisk.face u) (by rw [hf]; exact hn))
  · intro huv
    induction huv with
    | refl => exact connect_refl _
    | @tail b c _ hbc ih =>
      refine connect_trans ih ?_
      obtain rfl : E.embedDisk.face b = c := hbc
      show Gc.cface b.1 (Gc.embdFace rc b.1)
      unfold embdFace
      split_ifs
      · exact connect_trans (fconnect1 _ _) (fconnect1 _ _)
      · exact fconnect1 _ _

/-- math-comp `scycle_embd_ring`: the border of the disk map is a simple E-cycle. -/
theorem scycle_embd_ring : E.embedDisk.SFCycle E.embedDisk.edge (Gc.embdRing rc) := by
  have hsimple : E.embedDisk.Simple (Gc.embdRing rc) := by
    have := simple_map (G := E.embedDisk) (G' := Gc) (h := embd rc)
      (fun u v => E.cface_embd u v) (Gc.embdRing rc)
    rw [E.map_embd_ring] at this
    exact this.1 E.URerc.2
  refine ⟨?_, hsimple⟩
  apply Embed.cycle_from_next (E.embedDisk.simple_uniq hsimple)
  intro u hu
  show E.embedDisk.edge u = next (Gc.embdRing rc) u
  apply embd_inj rc
  obtain ⟨x, rc_x, hx⟩ := List.mem_map.1 (E.mem_embd_ring.1 hu)
  rw [← Embed.next_map (embd_inj rc), E.map_embd_ring]
  show Gc.embdEdge rc (embd rc u) = _
  rw [← hx, Embed.next_map Gc.edgeI]
  have nx : next rc x = Gc.node x := (Embed.next_cycle E.cycNrc rc_x).symm
  rw [nx]
  unfold embdEdge
  rw [E.e2c, ite_eq_right (not_not.2 rc_x)]

/-- math-comp local `bGdE`: the border of the disk map is edge-closed. -/
theorem bGdE : Closed (frel E.embedDisk.edge) {u | u ∈ Gc.embdRing rc} := by
  apply Closed.of_forward E.embedDisk.cedge_sym
  rintro u _ rfl hu
  exact (fconnect_cycle E.scycle_embd_ring.1 hu).1 (fconnect1 _ _)

/-- math-comp local `bGd'E`: the darts of the disk map off its border form an edge-closed
set. -/
theorem bGd'E : Closed (frel E.embedDisk.edge) {u | u ∉ Gc.embdRing rc} := E.bGdE.compl

/-- math-comp `embdd_inj`. -/
theorem embdd_inj [DecidableEq Dm] : Injective (Gm.embdd Gc rc h) :=
  fun u v e => Subtype.ext (E.embed_inj u.2 v.2 e)

/-- math-comp `embddE`: `{in [predC embd_ring], {morph embdd : u / edge u}}`. -/
theorem embddE {u : EmbdDart rc} (hu : u ∉ Gc.embdRing rc) :
    Gm.embdd Gc rc h (E.embedDisk.edge u) = Gm.edge (Gm.embdd Gc rc h u) := by
  have bc_eu : Gc.edge u.1 ∉ rc := by
    intro h'
    apply hu
    rw [E.mem_embd_ring]
    show u.1 ∈ rc.map Gc.edge
    rw [← E.e2c u.1]
    exact List.mem_map_of_mem h'
  show Gm.embed Gc rc h (Gc.embdEdge rc u.1) = Gm.edge (Gm.embed Gc rc h u.1)
  unfold embdEdge
  rw [ite_eq_left bc_eu, E.embedE]

/-- math-comp `embddN`: `{morph embdd : u / node u}`. -/
theorem embddN (u : EmbdDart rc) :
    Gm.embdd Gc rc h (E.embedDisk.node u) = Gm.node (Gm.embdd Gc rc h u) :=
  E.embedN u.2

end EmbedHyps

end Hypermap

end FourColor
