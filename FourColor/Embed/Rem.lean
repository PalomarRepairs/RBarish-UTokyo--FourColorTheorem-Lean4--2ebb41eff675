/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Embed.Disk

/-!
# The remainder map of the embedding (part of the port of `embed.v`)

The remainder hypermap `E.embedRem`, whose darts `EmbrDart Gm Gc rc h` are the darts of `Gm`
outside the image by `embdd` of the disk darts off the border (math-comp `embed_rem`, with
`rdom' := image embdd [predC embd_ring]`), with its border `Gm.embrRing Gc rc h` (math-comp
`embr_ring`) and its injection `embr` into `Gm` (math-comp `embr`):

* `E.embed_patch` : `Gm` is the patch of the disk map `E.embedDisk` and the remainder map
  `E.embedRem` along their borders (math-comp `embed_patch`);
* `E.planar_embr`, `E.plain_embr`, `E.cubic_embr` : the remainder map is planar, plain and
  quasicubic.

## Porting notes

* `rdom'` is the set `Gm.embrDom Gc rc h`; the dart type `EmbrDart Gm Gc rc h` and the
  functions `embrNode`, `embrFace` do not depend on the hypotheses. math-comp's
  `oapp f x (pick (bGd_proj y))` is a classical `dite` on `∃ u, u ∈ embd_ring ∧ y = embdd u`
  choosing `u` with `Classical.choose` (unique, as `embdd` is injective: `embrNode_of_ring`,
  `embrFace_of_ring`), and `embdd \o node \o face`, `embdd \o edge` are written through the
  functions `embdFace`, `embdEdge` of the disk map.
* `planar_embr` is proved with `planar_patch` (Coq: `genus_patch`).
-/

namespace FourColor

open Function

universe u v

namespace Hypermap

section EmbedRemDef

variable {Dm : Type u} {Dc : Type v} (Gm : Hypermap Dm) (Gc : Hypermap Dc) (rc : List Dc)
  (h : Dc → Dm)

/-- math-comp `rdom'`: the image by `embdd` of the disk darts off the border of the disk
map (`image embdd [predC embd_ring]`). -/
def embrDom : Set Dm := {x | ∃ u, u ∉ Gc.embdRing rc ∧ Gm.embdd Gc rc h u = x}

/-- The darts of the remainder map `embed_rem`: the darts of `Gm` outside `rdom'` (math-comp
`Local Notation rdart := {x | x \notin rdom'}`). -/
def EmbrDart : Type u := {x : Dm // x ∉ Gm.embrDom Gc rc h}

/-- The (classical) finite type structure of the remainder darts. -/
noncomputable instance [Fintype Dm] : Fintype (Gm.EmbrDart Gc rc h) := by
  classical exact (inferInstance : Fintype {x : Dm // x ∉ Gm.embrDom Gc rc h})

/-- The remainder darts form a finite type. -/
instance [Finite Dm] : Finite (Gm.EmbrDart Gc rc h) :=
  inferInstanceAs (Finite {x : Dm // x ∉ Gm.embrDom Gc rc h})

/-- The remainder darts have decidable equality. -/
instance [DecidableEq Dm] : DecidableEq (Gm.EmbrDart Gc rc h) :=
  inferInstanceAs (DecidableEq {x : Dm // x ∉ Gm.embrDom Gc rc h})

/-- math-comp `embr`: the injection of the remainder darts into `Gm`. -/
def embr (w : Gm.EmbrDart Gc rc h) : Dm := w.1

/-- math-comp `embr_inj`. -/
theorem embr_inj : Injective (Gm.embr Gc rc h) := fun _ _ e => Subtype.ext e

/-- math-comp `codom_embr`. -/
theorem codom_embr (x : Dm) : x ∈ Set.range (Gm.embr Gc rc h) ↔ x ∉ Gm.embrDom Gc rc h :=
  ⟨by rintro ⟨w, rfl⟩; exact w.2, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩

/-- math-comp `embr_ring`: the border of the remainder map, the preimage of
`rev (map embdd embd_ring)`. -/
noncomputable def embrRing : List (Gm.EmbrDart Gc rc h) :=
  preimSeq (Gm.embr Gc rc h) ((Gc.embdRing rc).map (Gm.embdd Gc rc h)).reverse

variable [DecidableEq Dc]

open Classical in
/-- math-comp `embr_node`: `oapp (embdd \o node \o face) (node x) (pick (bGd_proj x))`. -/
noncomputable def embrNode (x : Dm) : Dm :=
  if hx : ∃ u, u ∈ Gc.embdRing rc ∧ x = Gm.embdd Gc rc h u then
    Gm.embed Gc rc h (Gc.node (Gc.embdFace rc (Classical.choose hx).1))
  else Gm.node x

open Classical in
/-- math-comp `embr_face`: `oapp (embdd \o edge) (face x) (pick (bGd_proj (edge x)))`. -/
noncomputable def embrFace (x : Dm) : Dm :=
  if hx : ∃ u, u ∈ Gc.embdRing rc ∧ Gm.edge x = Gm.embdd Gc rc h u then
    Gm.embed Gc rc h (Gc.embdEdge rc (Classical.choose hx).1)
  else Gm.face x

variable {Gm Gc rc h} in
/-- `embr_node` off the image of the border. -/
theorem embrNode_of_not {x : Dm} (hx : ¬ ∃ u, u ∈ Gc.embdRing rc ∧ x = Gm.embdd Gc rc h u) :
    Gm.embrNode Gc rc h x = Gm.node x := by
  unfold embrNode
  rw [dite_eq_right hx]

variable {Gm Gc rc h} in
/-- `embr_face` at the darts whose edge is not the image of a border dart. -/
theorem embrFace_of_not {x : Dm}
    (hx : ¬ ∃ u, u ∈ Gc.embdRing rc ∧ Gm.edge x = Gm.embdd Gc rc h u) :
    Gm.embrFace Gc rc h x = Gm.face x := by
  unfold embrFace
  rw [dite_eq_right hx]

end EmbedRemDef

namespace EmbedHyps

variable {Dm : Type u} [Fintype Dm] [DecidableEq Dm] {Gm : Hypermap Dm}
  {Dc : Type v} [Fintype Dc] [DecidableEq Dc] {Gc : Hypermap Dc} {rc : List Dc} {h : Dc → Dm}
  (E : EmbedHyps Gm Gc rc h)
include E

/-- The image of a disk dart is in `rdom'` iff the dart is off the border (math-comp
`mem_image embdd_inj`). -/
theorem mem_embrDom (u : EmbdDart rc) :
    Gm.embdd Gc rc h u ∈ Gm.embrDom Gc rc h ↔ u ∉ Gc.embdRing rc := by
  constructor
  · rintro ⟨u', hu', e⟩
    rwa [E.embdd_inj e] at hu'
  · intro hu
    exact ⟨u, hu, rfl⟩

/-- `embr_node` at the image of a border dart. -/
theorem embrNode_of_ring {u : EmbdDart rc} (hu : u ∈ Gc.embdRing rc) :
    Gm.embrNode Gc rc h (Gm.embdd Gc rc h u) =
      Gm.embdd Gc rc h (E.embedDisk.node (E.embedDisk.face u)) := by
  have hx : ∃ u', u' ∈ Gc.embdRing rc ∧ Gm.embdd Gc rc h u = Gm.embdd Gc rc h u' := ⟨u, hu, rfl⟩
  unfold embrNode
  rw [dite_eq_left hx]
  have e : Classical.choose hx = u := (E.embdd_inj (Classical.choose_spec hx).2).symm
  rw [e]
  rfl

/-- `embr_face` at a dart whose edge is the image of a border dart. -/
theorem embrFace_of_ring {x : Dm} {u : EmbdDart rc} (hu : u ∈ Gc.embdRing rc)
    (Dx : Gm.edge x = Gm.embdd Gc rc h u) :
    Gm.embrFace Gc rc h x = Gm.embdd Gc rc h (E.embedDisk.edge u) := by
  have hx : ∃ u', u' ∈ Gc.embdRing rc ∧ Gm.edge x = Gm.embdd Gc rc h u' := ⟨u, hu, Dx⟩
  unfold embrFace
  rw [dite_eq_left hx]
  have e : Classical.choose hx = u :=
    E.embdd_inj ((Classical.choose_spec hx).2.symm.trans Dx)
  rw [e]
  rfl

omit [DecidableEq Dm] in
/-- math-comp `embr_edge_subproof`. -/
theorem embr_edge_subproof (w : Gm.EmbrDart Gc rc h) : Gm.edge w.1 ∉ Gm.embrDom Gc rc h := by
  rintro ⟨u, hu, e⟩
  apply w.2
  refine ⟨E.embedDisk.edge u, (E.bGd'E u _ rfl).1 hu, ?_⟩
  rw [E.embddE hu, e, E.e2m]

/-- math-comp `embr_node_subproof`. -/
theorem embr_node_subproof (w : Gm.EmbrDart Gc rc h) :
    Gm.embrNode Gc rc h w.1 ∉ Gm.embrDom Gc rc h := by
  by_cases hx : ∃ u, u ∈ Gc.embdRing rc ∧ w.1 = Gm.embdd Gc rc h u
  · obtain ⟨u, hu, Dw⟩ := hx
    rw [Dw, E.embrNode_of_ring hu, E.mem_embrDom, not_not]
    exact (E.bGdE _ _ rfl).2 (by rw [E.embedDisk.faceK]; exact hu)
  · rw [embrNode_of_not hx]
    rintro ⟨u, hu, e⟩
    have Dw : w.1 = Gm.embdd Gc rc h (E.embedDisk.node (E.embedDisk.node u)) := by
      rw [E.embddN, E.embddN, e, E.n3m]
    have hnn : E.embedDisk.node (E.embedDisk.node u) ∉ Gc.embdRing rc :=
      fun h' => hx ⟨_, h', Dw⟩
    exact w.2 ⟨_, hnn, Dw.symm⟩

/-- math-comp `embr_face_subproof`. -/
theorem embr_face_subproof (w : Gm.EmbrDart Gc rc h) :
    Gm.embrFace Gc rc h w.1 ∉ Gm.embrDom Gc rc h := by
  by_cases hx : ∃ u, u ∈ Gc.embdRing rc ∧ Gm.edge w.1 = Gm.embdd Gc rc h u
  · obtain ⟨u, hu, Dew⟩ := hx
    rw [E.embrFace_of_ring hu Dew, E.mem_embrDom, not_not]
    exact (E.bGdE u _ rfl).1 hu
  · rw [embrFace_of_not hx]
    rintro ⟨u, hu, e⟩
    have Dew : Gm.edge w.1 = Gm.embdd Gc rc h (E.embedDisk.node u) := by
      rw [E.embddN, e, Gm.plain_eq' E.plainGm]
    have hn : E.embedDisk.node u ∉ Gc.embdRing rc := fun h' => hx ⟨_, h', Dew⟩
    exact E.embr_edge_subproof w ⟨_, hn, Dew.symm⟩

/-- The edge permutation of `embed_rem` (math-comp section `Let redge`). -/
def embedRemEdge (w : Gm.EmbrDart Gc rc h) : Gm.EmbrDart Gc rc h :=
  ⟨Gm.edge w.1, E.embr_edge_subproof w⟩

/-- The node permutation of `embed_rem` (math-comp section `Let rnode`). -/
noncomputable def embedRemNode (w : Gm.EmbrDart Gc rc h) : Gm.EmbrDart Gc rc h :=
  ⟨Gm.embrNode Gc rc h w.1, E.embr_node_subproof w⟩

/-- The face permutation of `embed_rem` (math-comp section `Let rface`). -/
noncomputable def embedRemFace (w : Gm.EmbrDart Gc rc h) : Gm.EmbrDart Gc rc h :=
  ⟨Gm.embrFace Gc rc h w.1, E.embr_face_subproof w⟩

/-- math-comp `embed_rem_subproof`: `cancel3 redge rnode rface`. -/
theorem embed_rem_subproof (w : Gm.EmbrDart Gc rc h) :
    E.embedRemNode (E.embedRemFace (E.embedRemEdge w)) = w := by
  apply Subtype.ext
  show Gm.embrNode Gc rc h (Gm.embrFace Gc rc h (Gm.edge w.1)) = w.1
  by_cases hw : ∃ u, u ∈ Gc.embdRing rc ∧ w.1 = Gm.embdd Gc rc h u
  · obtain ⟨u, hu, Dw⟩ := hw
    rw [E.embrFace_of_ring hu (by rw [E.e2m]; exact Dw),
      E.embrNode_of_ring ((E.bGdE u _ rfl).1 hu), E.embedDisk.edgeK, Dw]
  · have hw' : ¬ ∃ u, u ∈ Gc.embdRing rc ∧ Gm.edge (Gm.edge w.1) = Gm.embdd Gc rc h u := by
      rw [E.e2m]
      exact hw
    rw [embrFace_of_not hw']
    by_cases hf : ∃ u, u ∈ Gc.embdRing rc ∧ Gm.face (Gm.edge w.1) = Gm.embdd Gc rc h u
    · exfalso
      obtain ⟨u, hu, Dfew⟩ := hf
      have Dw : w.1 = Gm.embdd Gc rc h (E.embedDisk.node u) := by
        rw [E.embddN, ← Dfew, Gm.edgeK]
      by_cases hnu : E.embedDisk.node u ∈ Gc.embdRing rc
      · exact hw ⟨_, hnu, Dw⟩
      · exact w.2 ⟨_, hnu, Dw.symm⟩
    · rw [embrNode_of_not hf, Gm.edgeK]

/-- math-comp `embed_rem`: the remainder hypermap, on the darts of `Gm` outside `rdom'`. -/
noncomputable def embedRem : Hypermap (Gm.EmbrDart Gc rc h) where
  edge := E.embedRemEdge
  node := E.embedRemNode
  face := E.embedRemFace
  edgeK := E.embed_rem_subproof

/-- math-comp `map_embr_ring`. -/
theorem map_embr_ring :
    (Gm.embrRing Gc rc h).map (Gm.embr Gc rc h) =
      ((Gc.embdRing rc).map (Gm.embdd Gc rc h)).reverse := by
  apply map_preim
  intro x hx
  obtain ⟨u, hu, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hx)
  rw [codom_embr, E.mem_embrDom, not_not]
  exact hu

/-- math-comp `ucycle_embr_ring`: the border of the remainder map is a duplicate-free
N-cycle. -/
theorem ucycle_embr_ring : UCycle (frel E.embedRem.node) (Gm.embrRing Gc rc h) := by
  have cycEbGd := E.scycle_embd_ring.1
  have UbGd := E.embedDisk.simple_uniq E.scycle_embd_ring.2
  have UbGm : ((Gc.embdRing rc).map (Gm.embdd Gc rc h)).Nodup := UbGd.map E.embdd_inj
  have UbGr : (Gm.embrRing Gc rc h).Nodup := by
    have : ((Gm.embrRing Gc rc h).map (Gm.embr Gc rc h)).Nodup := by
      rw [E.map_embr_ring]
      exact List.nodup_reverse.2 UbGm
    exact this.of_map _
  refine ⟨?_, UbGr⟩
  apply Embed.cycle_from_next UbGr
  intro w hw
  show E.embedRem.node w = next (Gm.embrRing Gc rc h) w
  apply embr_inj
  rw [← Embed.next_map (embr_inj Gm Gc rc h), E.map_embr_ring, Embed.next_rev UbGm]
  have hw' : Gm.embr Gc rc h w ∈ ((Gc.embdRing rc).map (Gm.embdd Gc rc h)).reverse := by
    rw [← E.map_embr_ring]
    exact List.mem_map_of_mem hw
  obtain ⟨u, hu, Dw⟩ := List.mem_map.1 (List.mem_reverse.1 hw')
  rw [← Dw, Embed.prev_map E.embdd_inj UbGd]
  show Gm.embrNode Gc rc h (Gm.embr Gc rc h w) = _
  rw [← Dw, E.embrNode_of_ring hu]
  congr 1
  have e1 : E.embedDisk.edge (prev (Gc.embdRing rc) u) = u := Embed.prev_cycle cycEbGd hu
  calc E.embedDisk.node (E.embedDisk.face u)
      = E.embedDisk.node (E.embedDisk.face (E.embedDisk.edge (prev (Gc.embdRing rc) u))) := by
        rw [e1]
    _ = prev (Gc.embdRing rc) u := E.embedDisk.edgeK _

/-- math-comp `embed_patch`: `Gm` is the patch of the disk map and the remainder map. -/
theorem embed_patch :
    Gm.Patch E.embedDisk E.embedRem (Gm.embdd Gc rc h) (Gm.embr Gc rc h) (Gc.embdRing rc)
      (Gm.embrRing Gc rc h) where
  injd := E.embdd_inj
  injr := embr_inj Gm Gc rc h
  cycle_d := E.scycle_embd_ring
  cycle_r := E.ucycle_embr_ring
  map_ring_r := E.map_embr_ring
  codom_r := by
    intro x
    rw [codom_embr]
    constructor
    · intro hx
      by_cases hd : x ∈ Set.range (Gm.embdd Gc rc h)
      · obtain ⟨u, rfl⟩ := hd
        right
        refine List.mem_map_of_mem ?_
        by_contra hu
        exact hx ⟨u, hu, rfl⟩
      · exact Or.inl hd
    · rintro (hd | hb) ⟨u, hu, rfl⟩
      · exact hd ⟨u, rfl⟩
      · rw [List.mem_map_of_injective E.embdd_inj] at hb
        exact hu hb
  edge_d := fun _ hu => E.embddE hu
  node_d := E.embddN
  edge_r := fun _ => rfl
  node_r := by
    intro w hw
    show Gm.embrNode Gc rc h w.1 = Gm.node w.1
    apply embrNode_of_not
    rintro ⟨u, hu, Dw⟩
    apply hw
    rw [← List.mem_map_of_injective (embr_inj Gm Gc rc h), E.map_embr_ring, List.mem_reverse]
    show w.1 ∈ _
    rw [Dw]
    exact List.mem_map_of_mem hu

/-- math-comp `planar_embr`. -/
theorem planar_embr : E.embedRem.Planar := (E.embed_patch.planar_patch.1 E.planarGm).2

/-- math-comp `plain_embr`. -/
theorem plain_embr : E.embedRem.Plain := (E.embed_patch.plain_patch.1 E.plainGm).2

/-- math-comp `cubic_embr`. -/
theorem cubic_embr : E.embedRem.Quasicubic (Gm.embrRing Gc rc h) :=
  (E.embed_patch.cubic_patch.1 E.cexGm.cubic).2

end EmbedHyps

end Hypermap

end FourColor
