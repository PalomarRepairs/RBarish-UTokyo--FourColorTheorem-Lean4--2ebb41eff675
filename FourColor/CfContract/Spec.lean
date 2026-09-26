/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfContract.Correct
import FourColor.CfContract.Sparse
import FourColor.CfContract.Band

/-!
# Configuration contracts (port of `cfcontract.v`, `contract_ctreeP`)

`contractProg_spec` replaces math-comp's `contract_ctreeP`: if
`contractProg cf = some cpc`, then the contract `cfcontract cf` is valid for the ring
`cfring cf`, and every contract ring trace of `cfmap cf` (on `rev (cfring cf)`) is a ring
trace of `cpmap cpc`.  This is the proof of `contract_ctreeP` up to its last line (where
math-comp concludes `ctree_mem (cpcolor cpc) (etrace (behead et))` by `ctree_mem_cpcolor`).

The triad of a contract of size 4 is found by `cptriad`: `cptriad_spec` extracts the index of
the kernel face it found, and `triad_of_cptriad` shows that this face is a triad (math-comp
proves the contrapositive).
-/

namespace FourColor

open Function CfMap EcpDart Hypermap

namespace CfContract

variable {α : Type*}

/-- math-comp `mask_subseq`. -/
theorem mask_sublist (m : List Bool) (s : List α) : (mask m s).Sublist s := by
  induction s generalizing m with
  | nil => simp
  | cons x s ih =>
    cases m with
    | nil => simp
    | cons b m =>
      cases b
      · exact (ih m).cons x
      · exact (ih m).cons_cons x

/-- The number of `true` bits of `mt` selected by `mc`, as the size of a mask. -/
theorem countP_mask_mask {mc mt : List Bool} {q : List α} (h1 : mc.length = q.length)
    (h2 : mt.length = q.length) :
    (mask mc mt).countP id = (mask (List.zipWith (· && ·) mc mt) q).length := by
  induction q generalizing mc mt with
  | nil =>
    rw [List.length_eq_zero_iff.1 h1, List.length_eq_zero_iff.1 h2]
    simp
  | cons y q ih =>
    match mc, mt, h1, h2 with
    | b1 :: m1, b2 :: m2, h1, h2 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
      cases b1 <;> cases b2 <;> simp [ih h1 h2]

/-- The items selected by both `mc` and `mt`. -/
theorem mem_mask_zipWith {mc mt : List Bool} {q : List α} {z : α}
    (h : z ∈ mask (List.zipWith (· && ·) mc mt) q) : z ∈ mask mc q ∧ z ∈ mask mt q := by
  induction q generalizing mc mt with
  | nil => simp at h
  | cons y q ih =>
    match mc, mt, h with
    | [], _, h => simp at h
    | _ :: _, [], h => simp at h
    | b1 :: m1, b2 :: m2, h =>
      rw [List.zipWith_cons_cons, mem_mask_cons] at h
      rw [mem_mask_cons, mem_mask_cons]
      rcases h with ⟨hb, rfl⟩ | h
      · rw [Bool.and_eq_true] at hb
        exact ⟨Or.inl ⟨hb.1, rfl⟩, Or.inl ⟨hb.2, rfl⟩⟩
      · have := ih h
        exact ⟨Or.inr this.1, Or.inr this.2⟩

variable {D : Type*} [Fintype D] [DecidableEq D] (G : Hypermap D)

omit [Fintype D] [DecidableEq D] in
/-- A sub-list of a simple list is simple. -/
theorem simple_sublist {p q : List D} (h : p.Sublist q) (hq : G.Simple q) : G.Simple p :=
  (h.map _).nodup hq

omit [DecidableEq D] in
/-- A bit of the band `mc` that is not in `mt` gives a dart of the band of `mc` outside the
face band of `mt` (for a simple list `q`). -/
theorem exists_mask_not {mc mt : List Bool} {q : List D} (h1 : mc.length = q.length)
    (h2 : mt.length = q.length) (hq : G.Simple q) (h : (mask mc mt).any (fun b => !b) = true) :
    ∃ z ∈ mask mc q, z ∉ G.fband (mask mt q) := by
  induction q generalizing mc mt with
  | nil =>
    rw [List.length_eq_zero_iff.1 h1] at h
    simp at h
  | cons y q ih =>
    match mc, mt, h1, h2 with
    | b1 :: m1, b2 :: m2, h1, h2 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h1 h2
      rw [G.simple_cons] at hq
      have hy : ∀ m : List Bool, y ∉ G.fband (mask m q) := fun m hm =>
        hq.1 (let ⟨w, hw, hyw⟩ := hm; ⟨w, mem_of_mem_mask hw, hyw⟩)
      by_cases hb : b1 = true ∧ b2 = false
      · obtain ⟨rfl, rfl⟩ := hb
        exact ⟨y, by simp, by rw [mask_false_cons]; exact hy m2⟩
      · have h' : (mask m1 m2).any (fun b => !b) = true := by
          cases b1 <;> cases b2 <;> simp_all
        obtain ⟨z, hz, hzn⟩ := ih h1 h2 hq.2 h'
        refine ⟨z, mem_mask_cons.2 (Or.inr hz), fun hm => ?_⟩
        rw [mem_fband_mask_cons] at hm
        rcases hm with ⟨-, hzy⟩ | hm
        · exact hq.1 ⟨z, mem_of_mem_mask hz, G.cfaceC.1 hzy⟩
        · exact hzn hm

omit [DecidableEq D] in
/-- Counting the darts of a face whose edges reach given faces: `S` is a simple list of faces
that are each reached by the `edge` of some dart of `L` satisfying `p`. -/
theorem length_le_countP {L S : List D} (hS : G.Simple S) (p : D → Bool)
    (hS' : ∀ z ∈ S, ∃ y ∈ L, G.cface (G.edge y) z ∧ p y = true) :
    S.length ≤ L.countP p := by
  classical
  let f : D → D := fun z =>
    if h : ∃ y ∈ L, G.cface (G.edge y) z ∧ p y = true then h.choose else z
  have hf : ∀ z ∈ S, f z ∈ L ∧ G.cface (G.edge (f z)) z ∧ p (f z) = true := by
    intro z hz
    have h := hS' z hz
    simp only [f, dite_eq_left h]
    exact ⟨h.choose_spec.1, h.choose_spec.2⟩
  have hinj : ∀ z1 ∈ S, ∀ z2 ∈ S, f z1 = f z2 → z1 = z2 := by
    intro z1 h1 z2 h2 e
    have c1 := (hf z1 h1).2.1
    have c2 := (hf z2 h2).2.1
    rw [e] at c1
    exact G.simple_cface hS z1 h1 z2 h2 (connect_trans (G.cfaceC.1 c1) c2)
  have hnd : (S.map f).Nodup := List.Nodup.map_on hinj (G.simple_uniq hS)
  have hsub : S.map f ⊆ L.filter p := fun y hy => by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    exact List.mem_filter.2 ⟨(hf z hz).1, (hf z hz).2.2⟩
  rw [List.countP_eq_length_filter, ← List.length_map (f := f)]
  exact (hnd.subperm hsub).length_le

/-- The step of `cptriad`. -/
theorem cptriad_succ (ccm : Cfmask) (cp : Cprog) (i : ℕ) :
    cptriad ccm cp (i + 1) =
      if (mask ccm.mr (cpadj (cfmask1 cp i) cp).mr ++
            mask ccm.mk (cpadj (cfmask1 cp i) cp).mk).any (fun b => !b) &&
          decide (2 < (mask ccm.mr (cpadj (cfmask1 cp i) cp).mr ++
            mask ccm.mk (cpadj (cfmask1 cp i) cp).mk).countP id)
      then true else cptriad ccm cp i := by
  rw [cptriad]
  obtain ⟨mrt, mkt⟩ := cpadj (cfmask1 cp i) cp
  obtain ⟨mrc, mkc⟩ := ccm
  rfl

/-- `cptriad` finds a kernel face with index `< n`. -/
theorem cptriad_spec {ccm : Cfmask} {cp : Cprog} {n : ℕ} (h : cptriad ccm cp n = true) :
    ∃ i < n, (mask ccm.mr (cpadj (cfmask1 cp i) cp).mr ++
        mask ccm.mk (cpadj (cfmask1 cp i) cp).mk).any (fun b => !b) = true ∧
      2 < (mask ccm.mr (cpadj (cfmask1 cp i) cp).mr ++
        mask ccm.mk (cpadj (cfmask1 cp i) cp).mk).countP id := by
  induction n with
  | zero => simp [cptriad] at h
  | succ n ih =>
    rw [cptriad_succ] at h
    split_ifs at h with hc
    · rw [Bool.and_eq_true, decide_eq_true_iff] at hc
      exact ⟨n, Nat.lt_succ_self n, hc⟩
    · obtain ⟨i, hi, hc'⟩ := ih h
      exact ⟨i, Nat.lt_succ_of_lt hi, hc'⟩

end CfContract

/-- **The contract of a configuration** (replaces math-comp `contract_ctreeP`). -/
theorem contractProg_spec {cf : Config} {cpc : Cprog} (h : contractProg cf = some cpc) :
    (cfmap cf).pointee.ValidContract (cfring cf) (cfcontract cf) ∧
    ∀ et, (cfmap cf).pointee.CcRingTrace (cfcontract cf) (cfring cf).reverse et →
      (cpmap cpc).pointee.RingTrace ((cpmap cpc).pointee.cpring (cpmap cpc).pointer) et := by
  simp only [contractProg] at h
  set cp := cf.cfprog with hcpdef
  set G := (cpmap cp).pointee with hG
  set x0 := (cpmap cp).pointer with hx0
  set cm := cfcontractMask cf with hcmdef
  set r := G.cpring x0 with hr
  set e := ctrenum cp with he
  have hcm : cm.length = ctrmsize cp := size_ctrmask _ _
  have hmr0 : (List.replicate (cprsize cp) false).length = cprsize cp := List.length_replicate
  show G.ValidContract r.reverse (mask cm e) ∧
    ∀ et, G.CcRingTrace (mask cm e) r.reverse.reverse et →
      (cpmap cpc).pointee.RingTrace ((cpmap cpc).pointee.cpring (cpmap cpc).pointer) et
  set cc := mask cm e with hcc
  generalize hc : cfctr (List.replicate (cprsize cp) false) cm cp = oc at h
  cases oc with
  | none => cases h
  | some cpc0 =>
  simp only at h
  by_cases hv : validCtrm cm cp = true
  swap
  · rw [ite_eq_right hv] at h; cases h
  rw [ite_eq_left hv] at h
  cases h
  have hcp : configProg cp := cfctr_config_prog hc
  have hplain : G.Plain := cpmap_plain (config_prog_cubic hcp)
  have hsp := sparse_cfctr hmr0 hcm hc
  rw [mask_false, List.map_nil, List.nil_append, G.sparse_cons] at hsp
  have hlcc : cc.length = cm.countP id := CfContract.length_mask (hcm.trans (size_ctrenum cp).symm)
  refine ⟨⟨?_, hsp.2, ?_, ?_⟩, ?_⟩
  · -- the contract is off the ring
    intro x hx1 hx2
    have hu := uniq_ctrenum hcp
    rw [G.insertE_cat, List.nodup_append] at hu
    have h1 : x ∈ G.insertE r :=
      (CfContract.mem_insertE_iff G _ _).2 ⟨x, List.mem_reverse.1 hx1, Or.inl rfl⟩
    have h2 : x ∈ G.insertE e := by
      obtain ⟨y, hy, hxy⟩ := (CfContract.mem_insertE_iff G _ _).1 hx2
      exact (CfContract.mem_insertE_iff G _ _).2 ⟨y, mem_of_mem_mask hy, hxy⟩
    exact hu.2.2 x h1 x h2 rfl
  · -- the size of the contract
    rw [hlcc]
    simp only [validCtrm] at hv
    split_ifs at hv with h4
    · exact Or.inr (Or.inr (Or.inr (by simpa using h4)))
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
      omega
  · -- the triad of a contract of size 4
    intro h4
    rw [hlcc] at h4
    simp only [validCtrm, h4, beq_self_eq_true, ite_true] at hv
    obtain ⟨i, hi, hany, hcount⟩ := CfContract.cptriad_spec hv
    obtain ⟨⟨hlr, hlk⟩, hband⟩ := ctrband_correct hcm hcp
    have hpm := proper_cpmask1 cp i
    have hmtp := cpadj_proper cp _ hpm
    set ccm := ctrband cm cp with hccm
    set mt := cpadj (cfmask1 cp i) cp with hmt
    have hadj : ∀ u, u ∈ G.fband (cpmask mt cp) ↔ G.adj u ((cpker cp).getD i x0) := by
      intro u
      rw [cpmask_adj hcp hpm u, cpmask1 hi hcp]
      exact ⟨fun ⟨y, hy, h⟩ => (List.mem_singleton.1 hy) ▸ h,
        fun h => ⟨_, List.mem_singleton_self _, h⟩⟩
    set x := (cpker cp).getD i x0 with hx
    set q := r ++ cpker cp with hq
    have hqs : G.Simple q := cpmap_simple hcp
    have hlr' : ccm.mr.length = r.length := by rw [size_ring_cpmap]; exact hlr
    have hlt' : mt.mr.length = r.length := by rw [size_ring_cpmap]; exact hmtp.1
    have hlk' : ccm.mk.length = (cpker cp).length := by rw [size_cpker hcp]; exact hlk
    have hlkt : mt.mk.length = (cpker cp).length := by rw [size_cpker hcp]; exact hmtp.2
    have hc1 : cpmask ccm cp = mask (ccm.mr ++ ccm.mk) q := (mask_cat hlr').symm
    have hc2 : cpmask mt cp = mask (mt.mr ++ mt.mk) q := (mask_cat hlt').symm
    have hc3 : mask ccm.mr mt.mr ++ mask ccm.mk mt.mk =
        mask (ccm.mr ++ ccm.mk) (mt.mr ++ mt.mk) := (mask_cat (hlr'.trans hlt'.symm)).symm
    rw [hc3] at hany hcount
    have hLc : (ccm.mr ++ ccm.mk).length = q.length := by simp [q, hlr', hlk']
    have hLt : (mt.mr ++ mt.mk).length = q.length := by simp [q, hlt', hlkt]
    have hxk : x ∈ cpker cp := by
      have hi' : i < (cpker cp).length := by rw [size_cpker hcp]; exact hi
      rw [hx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
      exact List.getElem_mem hi'
    refine ⟨x, ?_, ?_, ?_⟩
    · -- a kernel face
      show x ∉ G.fband r.reverse
      rw [G.fband_rev]
      intro hxr
      exact ((G.simple_cat _ _).1 hqs).2.1 ⟨x, hxk, hxr⟩
    · -- adjacent to at least three faces of the contract
      rw [CfContract.countP_mask_mask hLc hLt] at hcount
      have hSs := CfContract.simple_sublist G (CfContract.mask_sublist
        (List.zipWith (· && ·) (ccm.mr ++ ccm.mk) (mt.mr ++ mt.mk)) q) hqs
      refine lt_of_lt_of_le hcount (CfContract.length_le_countP G hSs _ fun z hz => ?_)
      obtain ⟨hz1, hz2⟩ := CfContract.mem_mask_zipWith hz
      have hzx : G.adj x z := (G.adjC hplain _ _).1 ((hadj z).1 (hc2 ▸ G.ring_fband _ z hz2))
      obtain ⟨y, hy, hyz⟩ := hzx
      refine ⟨y, hy, hyz, ?_⟩
      have hzP : z ∈ G.fband (G.insertE cc) := (hband z).2 (hc1 ▸ G.ring_fband _ z hz1)
      simp only [decide_eq_true_eq]
      exact ((G.fbandF _).connect_iff hyz).2 hzP
    · -- but not adjacent to all of them
      intro hall
      obtain ⟨z, hz1, hz2⟩ := CfContract.exists_mask_not G hLc hLt hqs hany
      obtain ⟨y, hy, hzy⟩ := (hband z).2 (hc1 ▸ G.ring_fband _ z hz1)
      apply hz2
      rw [← hc2]
      exact (hadj z).2 ((G.adjF hzy _).2 ((G.adjC hplain _ _).1 (hall y hy)))
  · -- the contract ring traces
    rintro et ⟨k, hk, het⟩
    have hk' : G.CcColoring (mask (List.replicate (cprsize cp) false) r ++ mask cm e) k := by
      rw [mask_false, List.nil_append]; exact hk
    obtain ⟨k', hk'c, hEk'⟩ := cfctr_correct hmr0 hcm hk' hc
    refine ⟨k', hk'c, ?_⟩
    rw [het, hEk', List.reverse_reverse, List.map_replicate, Bool.not_false,
      mask_true (le_of_eq (size_ring_cpmap cp))]

end FourColor
