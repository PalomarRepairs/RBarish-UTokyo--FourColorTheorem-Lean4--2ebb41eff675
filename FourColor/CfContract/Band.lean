/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfContract.Enum

/-!
# Configuration contracts (port of `cfcontract.v`, `ctrband_correct`)

`ctrband_correct`: the face mask `ctrband cm cp` is proper, and selects exactly the faces
incident to the edges selected by the contract mask `cm`.

The proof is by induction on `cp`, one lemma per construction step (`bandCorrect_R`,
`bandCorrect_Y0`, `bandCorrect_Y`, `bandCorrect_H`).
-/

namespace FourColor

open Function CfMap EcpDart Hypermap

namespace CfContract

variable {D D' : Type*}

/-- The face band of a masked list. -/
theorem mem_fband_mask_cons (G : Hypermap D) (b : Bool) (m : List Bool) (x : D) (s : List D)
    (u : D) : u ∈ G.fband (mask (b :: m) (x :: s)) ↔
      (b = true ∧ G.cface u x) ∨ u ∈ G.fband (mask m s) := by
  cases b <;> simp [Hypermap.fband_cons]

/-- The face band of the edge closure of a masked list. -/
theorem mem_fband_insertE_mask_cons (G : Hypermap D) (b : Bool) (m : List Bool) (x : D)
    (s : List D) (u : D) : u ∈ G.fband (G.insertE (mask (b :: m) (x :: s))) ↔
      (b = true ∧ (G.cface u x ∨ G.cface u (G.edge x))) ∨
        u ∈ G.fband (G.insertE (mask m s)) := by
  cases b <;> simp [insertE, Hypermap.fband_cons, or_assoc]

/-- The face band of an image, for an injection that preserves and reflects faces. -/
theorem mem_fband_map (G : Hypermap D) (M : Hypermap D') (i : D → D')
    (hcf : ∀ x y, M.cface (i x) (i y) ↔ G.cface x y) (x : D) (L : List D) :
    i x ∈ M.fband (L.map i) ↔ x ∈ G.fband L := by
  simp only [Hypermap.mem_fband, List.mem_map]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩
    exact ⟨y, hy, (hcf x y).1 h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨i y, ⟨y, hy, rfl⟩, (hcf x y).2 h⟩

/-- A new face is not in the face band of an image. -/
theorem not_mem_fband_map (M : Hypermap D') (i : D → D') {X u : D'}
    (hXi : ∀ y, ¬ M.cface X (i y)) (hu : M.cface X u) (L : List D) :
    u ∉ M.fband (L.map i) := by
  rintro ⟨_, hv, h⟩
  obtain ⟨y, -, rfl⟩ := List.mem_map.1 hv
  exact hXi y (connect_trans hu h)

variable [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D']

/-- The statement of `ctrband_correct` for the program `cp` (for the induction). -/
def BandCorrect (cp : Cprog) : Prop :=
  ∀ cm : List Bool, cm.length = ctrmsize cp → configProg cp →
    ProperCpmask cp (ctrband cm cp) ∧
      ∀ x, x ∈ (cpmap cp).pointee.fband ((cpmap cp).pointee.insertE (mask cm (ctrenum cp))) ↔
        x ∈ (cpmap cp).pointee.fband (cpmask (ctrband cm cp) cp)

/-- `ctrband_correct` for an `R n` step. -/
theorem bandCorrect_R (n : ℕ) {cp : Cprog} (ih : BandCorrect cp) : BandCorrect (.R n :: cp) := by
  intro cm hcm hcp
  set G := (cpmap cp).pointee with hG
  set x0 := (cpmap cp).pointer with hx0
  have hcm' : cm.length = ctrmsize cp := hcm
  have hcp' : configProg cp := hcp
  obtain ⟨⟨h1, h2⟩, IH⟩ := ih cm hcm' hcp'
  generalize hq : ctrband cm cp = cmq at h1 h2 IH
  obtain ⟨mr, mk⟩ := cmq
  have hband : ctrband cm (.R n :: cp) = ⟨CfMap.rot n mr, mk⟩ := by simp only [ctrband, hq]
  rw [hband]
  refine ⟨⟨?_, h2⟩, ?_⟩
  · show (CfMap.rot n mr).length = cprsize cp
    rw [CfMap.length_rot]; exact h1
  · show ∀ u : (cpmap cp).D, u ∈ G.fband (G.insertE (mask cm (ctrenum cp))) ↔
      u ∈ G.fband (mask (CfMap.rot n mr) ((G.ecpR n x0).pointee.cpring (G.ecpR n x0).pointer) ++
        mask mk (cpker cp))
    intro u
    refine (IH u).trans ?_
    rw [cpring_ecpR]
    have hlen : mr.length = (G.cpring x0).length := by rw [size_ring_cpmap]; exact h1
    show u ∈ G.fband (mask mr (G.cpring x0) ++ mask mk (cpker cp)) ↔ _
    simp only [Hypermap.mem_fband, List.mem_append, mem_mask_rot hlen n]

/-- `ctrband_correct` for the initial `Y` step. -/
theorem bandCorrect_Y0 : BandCorrect [.Y] := by
  intro cm hcm _
  have hcm' : cm.length = 0 := hcm
  rw [List.length_eq_zero_iff] at hcm'
  subst hcm'
  refine ⟨⟨rfl, rfl⟩, fun u => ?_⟩
  show u ∈ _ ↔ u ∈ (cpmap [.Y]).pointee.fband
    (mask [false, false, false] ((cpmap [.Y]).pointee.cpring (cpmap [.Y]).pointer) ++
      mask [] (cpker [.Y]))
  rw [show [false, false, false] = List.replicate 3 false from rfl, mask_false]
  simp [insertE, Hypermap.mem_fband]

/-- `ctrband_correct` for a non-initial `Y` step. -/
theorem bandCorrect_Y {s : Cpstep} {cp : Cprog} (ih : BandCorrect (s :: cp)) :
    BandCorrect (.Y :: s :: cp) := by
  intro cm hcm hcp
  set G := (cpmap (s :: cp)).pointee with hG
  set x0 := (cpmap (s :: cp)).pointer with hx0
  have hcp' : configProg (s :: cp) := hcp
  have hp : G.ProperCpring x0 := cpmap_proper (config_prog_cubic hcp')
  rcases cm with _ | ⟨b1, cm⟩
  · simp [ctrmsize] at hcm
  have hcm' : cm.length = ctrmsize (s :: cp) := by
    simp only [ctrmsize, List.length_cons] at hcm ⊢; omega
  obtain ⟨⟨h1, h2⟩, IH⟩ := ih cm hcm' hcp'
  generalize hq : ctrband cm (s :: cp) = cmq at h1 h2 IH
  obtain ⟨mr0, mk⟩ := cmq
  have hlr : (G.cpring x0).length = cprsize (s :: cp) := size_ring_cpmap _
  have h2r := (G.size_proper_cpring x0).1 hp
  have h1' : mr0.length = cprsize (s :: cp) := h1
  rcases mr0 with _ | ⟨a0, _ | ⟨a1, mr⟩⟩
  · simp only [List.length_nil] at h1'; omega
  · simp only [List.length_cons, List.length_nil] at h1'; omega
  have hband : ctrband (b1 :: cm) (.Y :: s :: cp) =
      ⟨(b1 || a0) :: false :: (b1 || a1) :: mr, mk⟩ := by
    simp only [ctrband, hq]
  rw [hband]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show mr.length + 3 = cprsize (s :: cp) + 1
    simp only [List.length_cons] at h1'; omega
  · show mk.length = (Cpstep.Y :: s :: cp).countP isCpH
    rw [List.countP_cons]; exact h2
  set M := (G.ecpY x0).pointee with hM
  set i := G.icpY x0 with hi
  show ∀ u : (G.ecpY x0).D,
    u ∈ M.fband (M.insertE (mask (b1 :: cm) ((G.node x0 :: ctrenum (s :: cp)).map i))) ↔
      u ∈ M.fband (mask ((b1 || a0) :: false :: (b1 || a1) :: mr)
        (M.cpring (G.ecpY x0).pointer) ++ mask mk ((cpker (s :: cp)).map i))
  intro u
  have hr : G.cpring x0 = G.node x0 :: x0 :: (G.cpring x0).drop 2 := G.head_proper_cpring x0 hp
  rw [cpring_ecpY, node_ecpY, ecpY_pointer, ← map_mask, G.insertE_icpY, ← map_mask]
  rw [show (G.cpring x0).tail = x0 :: (G.cpring x0).drop 2 by rw [hr]; rfl, List.map_cons]
  have hcf := G.cface_icpY x0
  have hXi : ∀ y, ¬ M.cface IcpX (i y) := fun y h => by
    have := (G.cface_ecpY x0 _).1 h
    rw [face_ecpY] at this
    simp [hi, icpY_eq] at this
  have hnX : M.cface (Icp IcpXe) (i (G.node x0)) := by
    have := G.cface_node_ecpY x0
    rwa [node_ecpY] at this
  have hex : G.cface (G.edge (G.node x0)) x0 := by
    have := fconnect1 G.face (G.edge (G.node x0))
    rwa [G.nodeK] at this
  have IHu := fun x => IH x
  simp only [cpmask] at IHu
  rw [hr] at IHu
  rcases G.fband_icpY x0 u with ⟨x, hux⟩ | hXu
  · rw [(M.fbandF _).connect_iff hux, (M.fbandF _).connect_iff hux]
    have hnXx : M.cface (i x) (Icp IcpXe) ↔ G.cface x (G.node x0) :=
      (M.cface_sym.same_r hnX (i x)).trans (hcf _ _)
    have hex' : G.cface x (G.edge (G.node x0)) ↔ G.cface x x0 := G.cface_sym.same_r hex x
    rw [mem_fband_map G M i hcf, mem_fband_insertE_mask_cons, IHu x, M.fband_cat,
      mem_fband_mask_cons, mem_fband_mask_cons, mem_fband_mask_cons, ← map_mask,
      mem_fband_map G M i hcf, mem_fband_map G M i hcf, G.fband_cat, mem_fband_mask_cons,
      mem_fband_mask_cons, hnXx, hcf, hex']
    simp only [Bool.or_eq_true, Bool.false_eq_true, false_and, false_or, or_and_right,
      and_or_left, or_assoc]
    simp only [or_assoc, or_comm, or_left_comm]
  · have hnXu : ¬ M.cface u (Icp IcpXe) := fun h =>
      hXi _ (connect_trans (connect_trans hXu h) hnX)
    have hx0u : ¬ M.cface u (G.icpY x0 x0) := fun h => hXi _ (connect_trans hXu h)
    refine iff_of_false (not_mem_fband_map M i hXi hXu _) (fun hmem => ?_)
    rw [M.fband_cat, mem_fband_mask_cons, mem_fband_mask_cons, mem_fband_mask_cons,
      ← map_mask] at hmem
    rcases hmem with (⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩ | h) | h
    · exact hnXu h
    · cases h
    · exact hx0u h
    · exact not_mem_fband_map M (G.icpY x0) hXi hXu _ h
    · exact not_mem_fband_map M (G.icpY x0) hXi hXu _ h

/-- `ctrband_correct` for an `H` step. -/
theorem bandCorrect_H {cp : Cprog} (ih : BandCorrect cp) : BandCorrect (.H :: cp) := by
  intro cm hcm hcp
  set G := (cpmap cp).pointee with hG
  set x0 := (cpmap cp).pointer with hx0
  have hcp' : configProg cp := hcp
  have hp : G.ProperCpring x0 := cpmap_proper (config_prog_cubic hcp')
  have hl : G.LongCpring x0 := cfmap_long hcp'
  rcases cm with _ | ⟨b1, _ | ⟨b0, _ | ⟨b2, cm⟩⟩⟩
  · simp [ctrmsize] at hcm
  · simp [ctrmsize] at hcm
  · simp [ctrmsize] at hcm
  have hcm' : cm.length = ctrmsize cp := by
    simp only [ctrmsize, List.length_cons] at hcm ⊢; omega
  obtain ⟨⟨h1, h2⟩, IH⟩ := ih cm hcm' hcp'
  generalize hq : ctrband cm cp = cmq at h1 h2 IH
  obtain ⟨mr0, mk⟩ := cmq
  have hlr : (G.cpring x0).length = cprsize cp := size_ring_cpmap _
  have h3r := (G.size_long_cpring x0).1 hl
  have h1' : mr0.length = cprsize cp := h1
  rcases mr0 with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, mr⟩⟩⟩
  · simp only [List.length_nil] at h1'; omega
  · simp only [List.length_cons, List.length_nil] at h1'; omega
  · simp only [List.length_cons, List.length_nil] at h1'; omega
  have hband : ctrband (b1 :: b0 :: b2 :: cm) (.H :: cp) =
      ⟨(b0 || a0) :: b1 :: (b2 || a2) :: mr, (b0 || (b1 || (b2 || a1))) :: mk⟩ := by
    simp only [ctrband, hq]
  rw [hband]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show mr.length + 3 = cprsize cp
    simp only [List.length_cons] at h1'; omega
  · show mk.length + 1 = (Cpstep.H :: cp).countP isCpH
    rw [List.countP_cons]
    have : mk.length = cpksize cp := h2
    simp [isCpH, this, cpksize]
  simp only [cpmask]
  rw [cpker_H hp]
  set M := (G.ecpH x0).pointee with hM
  set i := G.icpH x0 with hi
  show ∀ u : (G.ecpH x0).D,
    u ∈ M.fband (M.insertE (mask (b1 :: b0 :: b2 :: cm) (M.face (G.ecpH x0).pointer ::
      (G.node x0 :: x0 :: ctrenum cp).map i))) ↔
      u ∈ M.fband (mask ((b0 || a0) :: b1 :: (b2 || a2) :: mr) (M.cpring (G.ecpH x0).pointer) ++
        mask ((b0 || (b1 || (b2 || a1))) :: mk) ((x0 :: cpker cp).map i))
  intro u
  have hr : G.cpring x0 = G.node x0 :: x0 :: G.face (G.edge x0) :: (G.cpring x0).drop 3 :=
    G.head_long_cpring x0 hl
  rw [G.cpring_ecpH x0 hp, CfContract.node_ecpH G x0 hp, ecpH_pointer, face_ecpH]
  change u ∈ M.fband (M.insertE (mask (b1 :: b0 :: b2 :: cm) (Icp IcpX ::
      (G.node x0 :: x0 :: ctrenum cp).map i))) ↔
    u ∈ M.fband (mask ((b0 || a0) :: b1 :: (b2 || a2) :: mr)
      (Icp (Icp IcpXe) :: IcpX :: ((G.cpring x0).drop 2).map i) ++
        mask ((b0 || (b1 || (b2 || a1))) :: mk) ((x0 :: cpker cp).map i))
  rw [show (G.cpring x0).drop 2 = G.face (G.edge x0) :: (G.cpring x0).drop 3 by rw [hr]; rfl]
  have hcf := G.cface_icpH x0
  have hXf : ∀ v, M.cface IcpX v ↔ v ∈ [IcpX, Icp IcpX, Icp (Icp IcpX)] := fun v => by
    have := G.cface_ecpH x0 hp v
    rwa [G.face_face_ecpH x0 hp, face_ecpH] at this
  have hXi : ∀ y, ¬ M.cface IcpX (i y) := fun y h => by
    have := (hXf _).1 h
    simp [hi, icpH_eq] at this
  have hnX : M.cface (Icp (Icp IcpXe)) (i (G.node x0)) := by
    have := G.cface_node_ecpH x0 hp
    rwa [CfContract.node_ecpH G x0 hp] at this
  have hefX : M.cface (M.edge (Icp IcpX)) (i x0) := by
    have h := CfContract.face_edge_face_ecpH G x0 hp
    rw [face_ecpH, ← hM, ← hi] at h
    rw [← h]; exact fconnect1 _ _
  have hex : G.cface (G.edge (G.node x0)) x0 := by
    have := fconnect1 G.face (G.edge (G.node x0))
    rwa [G.nodeK] at this
  have hex0 : G.cface (G.edge x0) (G.face (G.edge x0)) := fconnect1 _ _
  have IHu := fun x => IH x
  simp only [cpmask] at IHu
  rw [hr] at IHu
  rcases G.fband_icpH x0 u with ⟨x, hux⟩ | hXu
  · rw [(M.fbandF _).connect_iff hux, (M.fbandF _).connect_iff hux]
    rw [mem_fband_insertE_mask_cons, ← map_mask i (b0 :: b2 :: cm), G.insertE_icpH, M.fband_cat,
      ← map_mask i ((b0 || (b1 || (b2 || a1))) :: mk)]
    rw [mem_fband_mask_cons, mem_fband_mask_cons, List.map_cons, mem_fband_mask_cons,
      ← map_mask i mr]
    have hnXx : M.cface (i x) (Icp (Icp IcpXe)) ↔ G.cface x (G.node x0) :=
      (M.cface_sym.same_r hnX (i x)).trans (hcf _ _)
    have hefXx : M.cface (i x) (M.edge (Icp IcpX)) ↔ G.cface x x0 :=
      (M.cface_sym.same_r hefX (i x)).trans (hcf _ _)
    have hXx : ¬ M.cface (G.icpH x0 x) IcpX := fun h => hXi x (M.cfaceC.1 h)
    have hfXx : ¬ M.cface (G.icpH x0 x) (Icp IcpX) := fun h =>
      hXi x (connect_trans (fconnect1 M.face IcpX) (M.cfaceC.1 h))
    have hex' : G.cface x (G.edge (G.node x0)) ↔ G.cface x x0 := G.cface_sym.same_r hex x
    have hex0' : G.cface x (G.edge x0) ↔ G.cface x (G.face (G.edge x0)) :=
      G.cface_sym.same_r hex0 x
    rw [mem_fband_map G M i hcf, mem_fband_insertE_mask_cons, mem_fband_insertE_mask_cons,
      IHu x, mem_fband_map G M i hcf, mem_fband_map G M i hcf, G.fband_cat,
      mem_fband_mask_cons, mem_fband_mask_cons, mem_fband_mask_cons, mem_fband_mask_cons, hnXx,
      hefXx, hex', hex0']
    have hff : M.cface (G.icpH x0 x) (i (G.face (G.edge x0))) ↔ G.cface x (G.face (G.edge x0)) :=
      hcf _ _
    simp only [Bool.or_eq_true, hXx, hfXx, and_false, false_or, hff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ |
        (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h) | h)
      · exact Or.inr (Or.inl ⟨Or.inr (Or.inl h1), h2⟩)
      · exact Or.inl (Or.inl ⟨Or.inl h1, h2⟩)
      · exact Or.inr (Or.inl ⟨Or.inl h1, h2⟩)
      · exact Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inl h1)), h2⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨Or.inl h1, h2⟩))
      · exact Or.inl (Or.inl ⟨Or.inr h1, h2⟩)
      · exact Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inr h1)), h2⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨Or.inr h1, h2⟩))
      · exact Or.inl (Or.inr (Or.inr h))
      · exact Or.inr (Or.inr h)
    · rintro ((⟨h1 | h1, h2⟩ | ⟨h1 | h1, h2⟩ | h) | ⟨h1 | h1 | h1 | h1, h2⟩ | h)
      · exact Or.inr (Or.inl ⟨h1, Or.inl h2⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨h1, h2⟩))))
      · exact Or.inr (Or.inr (Or.inl ⟨h1, Or.inr h2⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr (Or.inr h))))))
      · exact Or.inr (Or.inl ⟨h1, Or.inr h2⟩)
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inr (Or.inl ⟨h1, Or.inl h2⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl ⟨h1, h2⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · rw [mem_fband_insertE_mask_cons, ← map_mask i (b0 :: b2 :: cm), G.insertE_icpH, M.fband_cat,
      ← map_mask i ((b0 || (b1 || (b2 || a1))) :: mk)]
    rw [mem_fband_mask_cons, mem_fband_mask_cons, List.map_cons, mem_fband_mask_cons,
      ← map_mask i mr]
    have hXu' : M.cface IcpX u := hXu
    have hnXu : ¬ M.cface u (Icp (Icp IcpXe)) := fun h =>
      hXi _ (connect_trans (connect_trans hXu' h) hnX)
    have hfXu : M.cface u (Icp IcpX) := connect_trans (M.cfaceC.1 hXu') (fconnect1 _ _)
    have hXu'' : M.cface u IcpX := M.cfaceC.1 hXu'
    have hiu : ∀ y, ¬ M.cface u (i y) := fun y h => hXi y (connect_trans hXu' h)
    simp only [hfXu, hXu'', hnXu, hiu, true_or, and_true, and_false, false_or, or_false,
      not_mem_fband_map M (G.icpH x0) hXi hXu' _, not_mem_fband_map M i hXi hXu' _]

end CfContract

/-- math-comp `ctrband_correct`. -/
theorem ctrband_correct {cm : List Bool} {cp : Cprog} (hcm : cm.length = ctrmsize cp)
    (h : configProg cp) :
    ProperCpmask cp (ctrband cm cp) ∧
      ∀ x, x ∈ (cpmap cp).pointee.fband ((cpmap cp).pointee.insertE (mask cm (ctrenum cp))) ↔
        x ∈ (cpmap cp).pointee.fband (cpmask (ctrband cm cp) cp) := by
  suffices hall : ∀ cp, CfContract.BandCorrect cp from hall cp cm hcm h
  intro cp
  induction cp with
  | nil => intro cm _ h; simp [configProg] at h
  | cons s cp ih =>
    cases s with
    | R n => exact CfContract.bandCorrect_R n ih
    | Y =>
      cases cp with
      | nil => exact CfContract.bandCorrect_Y0
      | cons s' cp' => exact CfContract.bandCorrect_Y ih
    | H => exact CfContract.bandCorrect_H ih
    | _ => intro cm _ h; simp [configProg] at h

end FourColor
