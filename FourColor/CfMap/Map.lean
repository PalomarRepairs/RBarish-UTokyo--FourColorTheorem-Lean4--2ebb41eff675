/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.CfMap.CompExt

/-!
# Configuration maps (port of `cfmap.v`, final part)

* `cpmap0`      : the base map, a single edge on the darts `Bool` (math-comp `cpmap0`).
* `cpmap cp`    : the pointed map obtained by running `cp : Cprog` right-to-left
  (math-comp `cpmap`).
* `cfmap cf`    : the pointed map of `cf : Config` (`cpmap (cfprog cf)`, math-comp `cfmap`).
* `cfring cf`   : the ring of `cf : Config` (`rev (cpring (cfmap cf))`, math-comp `cfring`).
* `cpker cp`    : a sequence of darts transversal of the kernel of `cpmap cp`, with one dart for
  each face NOT incident to the ring of `cpmap cp`; thus `cpring (cpmap cp) ++ cpker cp` is a
  transversal of the faces of `cpmap cp` (math-comp `cpker`).
* `injcp cp1 cp2` : the injection from `cpmap cp2` to `cpmap (catrev cp1 cp2)` (math-comp
  `injcp`); math-comp's `catrev cp1 cp2` is `List.reverseAux cp1 cp2` (`= cp1.reverse ++ cp2`),
  whose defining equations make the dependent type of `injcp` compute.
* `cpmask cm cp` : the subsequence of `cpring (cpmap cp) ++ cpker cp` selected by `cm : Cfmask`
  (math-comp `cpmask`).

The program-level functions `cprsize`, `cpksize`, `cfmask1`, `cpadj` are defined in
`FourColor/CfMap/Prog.lean`; their specifications (`size_ring_cpmap`, `size_cpker`, `cpmask1`,
`cpmask_adj`) are proved here.
-/

namespace FourColor

open Function CfMap EcpDart Hypermap

/-! ### The base map -/

/-- math-comp `cpmap0_subproof`. -/
theorem cpmap0_subproof (b : Bool) : (!(id (!b))) = b := by cases b <;> rfl

/-- math-comp `cpmap0`: the base map, a single edge, with darts `Bool`
(`edge = node = negb`, `face = id`). -/
def cpmap0 : Hypermap Bool := ⟨not, not, id, cpmap0_subproof⟩

/-- math-comp `cpring0`. -/
theorem cpring0 (b : Bool) : cpmap0.cpring b = [!b, b] := by
  apply cpmap0.cpring_def
  · rfl
  · refine ⟨?_, ?_⟩
    · show (!b) = (!b) ∧ (!(!b)) = b ∧ True
      cases b <;> exact ⟨rfl, rfl, trivial⟩
    · cases b <;> decide

/-! ### The configuration maps -/

/-- math-comp `cpmap cp`: the pointed map obtained by running the program `cp` right-to-left,
starting from the base map `cpmap0` (pointed at `true`). -/
noncomputable def cpmap : Cprog → PointedMap.{0}
  | [] => ⟨Bool, cpmap0, true⟩
  | .R n :: cp => (cpmap cp).pointee.ecpR n (cpmap cp).pointer
  | .R' :: cp => (cpmap cp).pointee.ecpR' (cpmap cp).pointer
  | .Y :: cp => (cpmap cp).pointee.ecpY (cpmap cp).pointer
  | .H :: cp => (cpmap cp).pointee.ecpH (cpmap cp).pointer
  | .U :: cp => (cpmap cp).pointee.ecpU (cpmap cp).pointer
  | .K :: cp => (cpmap cp).pointee.ecpK (cpmap cp).pointer
  | .A :: cp => (cpmap cp).pointee.ecpA (cpmap cp).pointer

/-- `cpmap []` is the base map `cpmap0`, pointed at `true`. -/
theorem cpmap_nil : cpmap [] = ⟨Bool, cpmap0, true⟩ := rfl
/-- `cpmap` of an `R n` step (by definition). -/
theorem cpmap_R (n : ℕ) (cp : Cprog) :
    cpmap (.R n :: cp) = (cpmap cp).pointee.ecpR n (cpmap cp).pointer := rfl
/-- `cpmap` of an `R'` step (by definition). -/
theorem cpmap_R' (cp : Cprog) :
    cpmap (.R' :: cp) = (cpmap cp).pointee.ecpR' (cpmap cp).pointer := rfl
/-- `cpmap` of a `Y` step (by definition). -/
theorem cpmap_Y (cp : Cprog) : cpmap (.Y :: cp) = (cpmap cp).pointee.ecpY (cpmap cp).pointer := rfl
/-- `cpmap` of an `H` step (by definition). -/
theorem cpmap_H (cp : Cprog) : cpmap (.H :: cp) = (cpmap cp).pointee.ecpH (cpmap cp).pointer := rfl
/-- `cpmap` of a `U` step (by definition). -/
theorem cpmap_U (cp : Cprog) : cpmap (.U :: cp) = (cpmap cp).pointee.ecpU (cpmap cp).pointer := rfl
/-- `cpmap` of a `K` step (by definition). -/
theorem cpmap_K (cp : Cprog) : cpmap (.K :: cp) = (cpmap cp).pointee.ecpK (cpmap cp).pointer := rfl
/-- `cpmap` of an `A` step (by definition). -/
theorem cpmap_A (cp : Cprog) : cpmap (.A :: cp) = (cpmap cp).pointee.ecpA (cpmap cp).pointer := rfl

/-- math-comp `cfmap cf`: the pointed map of the configuration `cf`. -/
noncomputable abbrev cfmap (cf : Config) : PointedMap.{0} := cpmap cf.cfprog

/-- math-comp `cfring cf`: the ring of the configuration `cf` (a node cycle). -/
noncomputable def cfring (cf : Config) : List (cfmap cf).D :=
  ((cfmap cf).pointee.cpring (cfmap cf).pointer).reverse

/-- math-comp `cpmap_proper`. -/
theorem cpmap_proper {cp : Cprog} (h : cubicProg cp) :
    (cpmap cp).pointee.ProperCpring (cpmap cp).pointer := by
  rw [size_proper_cpring]
  induction cp with
  | nil => show 1 < (cpmap0.cpring true).length; rw [cpring0]; decide
  | cons s cp ih =>
    cases s with
    | R n => rw [cpmap_R, size_cpring_ecpR]; exact ih h
    | Y => rw [cpmap_Y, size_cpring_ecpY]; have := ih h; omega
    | H => rw [cpmap_H, size_cpring_ecpH]; exact ih h
    | U => rw [cpmap_U, size_cpring_ecpU]; have := ih h; omega
    | _ => simp [cubicProg] at h

/-- math-comp `cfmap_long`. -/
theorem cfmap_long {cp : Cprog} (h : configProg cp) :
    (cpmap cp).pointee.LongCpring (cpmap cp).pointer := by
  rw [size_long_cpring]
  induction cp with
  | nil => simp [configProg] at h
  | cons s cp ih =>
    cases s with
    | R n => rw [cpmap_R, size_cpring_ecpR]; exact ih h
    | H => rw [cpmap_H, size_cpring_ecpH]; exact ih h
    | Y =>
      rw [cpmap_Y, size_cpring_ecpY]
      cases cp with
      | nil => show 2 < (cpmap0.cpring true).length + 1; rw [cpring0]; decide
      | cons s' cp' => have := ih h; omega
    | _ => simp [configProg] at h

/-- math-comp `cpmap_plain`. -/
theorem cpmap_plain {cp : Cprog} (h : cubicProg cp) : (cpmap cp).pointee.Plain := by
  induction cp with
  | nil =>
    show cpmap0.Plain
    unfold Plain
    rw [plainP]
    intro b _
    cases b <;> exact ⟨rfl, by decide⟩
  | cons s cp ih =>
    cases s with
    | R n => exact ih h
    | Y => exact (cpmap cp).pointee.plain_ecpY _ (ih h)
    | H => exact (cpmap cp).pointee.plain_ecpH _ (ih h)
    | U => exact (cpmap cp).pointee.plain_ecpU _ (ih h)
    | _ => simp [cubicProg] at h

/-- math-comp `cpmap_cubic`. -/
theorem cpmap_cubic {cp : Cprog} (h : cubicProg cp) :
    (cpmap cp).pointee.Quasicubic ((cpmap cp).pointee.cpring (cpmap cp).pointer).reverse := by
  induction cp with
  | nil =>
    show cpmap0.Quasicubic (cpmap0.cpring true).reverse
    rw [cpring0]
    intro b hb
    simp only [Set.mem_ofPred_eq] at hb
    cases b <;> simp at hb
  | cons s cp ih =>
    cases s with
    | R n => exact (cpmap cp).pointee.cubic_ecpR _ _ (ih h)
    | Y => exact (cpmap cp).pointee.cubic_ecpY _ (ih h)
    | H => exact (cpmap cp).pointee.cubic_ecpH _ (ih h)
    | U => exact (cpmap cp).pointee.cubic_ecpU _ (ih h)
    | _ => simp [cubicProg] at h

/-- math-comp `cpmap_connected`. -/
theorem cpmap_connected {cp : Cprog} (h : cubicProg cp) : (cpmap cp).pointee.Connected := by
  induction cp with
  | nil =>
    show cpmap0.Connected
    apply nComp_univ_eq_one cpmap0.glinkC true
    intro b
    cases b
    · exact connect_of_rel (cpmap0.glinkE true)
    · exact connect_refl _
  | cons s cp ih =>
    cases s with
    | R n => exact ih h
    | Y => exact (cpmap cp).pointee.connected_ecpY _ (ih h)
    | H => exact (cpmap cp).pointee.connected_ecpH _ (ih h)
    | U => exact (cpmap cp).pointee.connected_ecpU _ (ih h)
    | _ => simp [cubicProg] at h

/-- In `cpmap0`, faces are singletons. -/
theorem cface_cpmap0 (a b : Bool) : cpmap0.cface a b ↔ a = b := by
  have hc : fcycle cpmap0.face [a] := ⟨rfl, trivial⟩
  exact (fconnect_cycle hc List.mem_cons_self).trans (List.mem_singleton.trans eq_comm)

/-- math-comp `cpmap_bridgeless`. -/
theorem cpmap_bridgeless {cp : Cprog} (h : cubicProg cp) : (cpmap cp).pointee.Bridgeless := by
  induction cp with
  | nil =>
    show cpmap0.Bridgeless
    rintro ⟨b, hb⟩
    rw [cface_cpmap0] at hb
    cases b <;> exact absurd hb (by decide)
  | cons s cp ih =>
    cases s with
    | R n => exact ih h
    | Y => exact (cpmap cp).pointee.bridgeless_ecpY _ (ih h)
    | H => exact (cpmap cp).pointee.bridgeless_ecpH _ (ih h) (cpmap_proper h)
    | U => exact (cpmap cp).pointee.bridgeless_ecpU _ (ih h)
    | _ => simp [cubicProg] at h

/-- math-comp `cpmap_planar`. -/
theorem cpmap_planar {cp : Cprog} (h : cubicProg cp) : (cpmap cp).pointee.Planar := by
  induction cp with
  | nil =>
    have geoG : cpmap0.UCyclePlainQuasicubicConnected (cpmap0.cpring true).reverse :=
      ⟨⟨⟨cpmap_plain (cp := []) rfl, cpmap_cubic (cp := []) rfl⟩, cpmap0.ucycle_rev_cpring _⟩,
        cpmap_connected (cp := []) rfl⟩
    show cpmap0.Planar
    rw [cpmap0.quasicubic_euler geoG, cpring0]
    have hf : fcard cpmap0.face Set.univ * 1 = (Set.univ : Set Bool).ncard :=
      fcard_order_set cpmap0.faceI (fun b _ => (order_eq_one_iff cpmap0.faceI).2 rfl)
        (fun _ _ _ => Iff.rfl)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_bool, Nat.mul_one] at hf
    rw [hf, Fintype.card_bool]
    rfl
  | cons s cp ih =>
    have hs := h
    cases s with
    | R n => exact ih h
    | Y =>
      exact (cpmap cp).pointee.planar_ecpY _ (ih h) (cpmap_plain (cp := cp) h)
        (cpmap_cubic (cp := cp) h) (cpmap_connected (cp := cp) h)
    | H =>
      exact (cpmap cp).pointee.planar_ecpH _ (ih h) (cpmap_plain (cp := cp) h)
        (cpmap_cubic (cp := cp) h) (cpmap_connected (cp := cp) h)
    | U =>
      exact (cpmap cp).pointee.planar_ecpU _ (ih h) (cpmap_plain (cp := cp) h)
        (cpmap_cubic (cp := cp) h) (cpmap_connected (cp := cp) h)
    | _ => simp [cubicProg] at h

/-! ### Kernel transversals -/

/-- math-comp `cpker cp`: a sequence of darts transversal of the kernel of `cpmap cp`, with one
dart for each face NOT incident to the ring of `cpmap cp`. -/
noncomputable def cpker : (cp : Cprog) → List (cpmap cp).D
  | .R _ :: cp => cpker cp
  | .Y :: cp => (cpker cp).map ((cpmap cp).pointee.icpY (cpmap cp).pointer)
  | .H :: cp =>
    match (cpmap cp).pointee.cpring (cpmap cp).pointer with
    | _ :: x :: _ => (x :: cpker cp).map ((cpmap cp).pointee.icpH (cpmap cp).pointer)
    | _ => []
  | _ => []

/-- `cpker` of the empty program (by definition). -/
theorem cpker_nil : cpker [] = [] := rfl
/-- `cpker` of an `R n` step (by definition). -/
theorem cpker_R (n : ℕ) (cp : Cprog) : cpker (.R n :: cp) = cpker cp := rfl
/-- `cpker` of a `Y` step (by definition). -/
theorem cpker_Y (cp : Cprog) :
    cpker (.Y :: cp) = (cpker cp).map ((cpmap cp).pointee.icpY (cpmap cp).pointer) := rfl

/-- `cpker` for an `H` step on a proper ring. -/
theorem cpker_H {cp : Cprog} (h : (cpmap cp).pointee.ProperCpring (cpmap cp).pointer) :
    cpker (.H :: cp) =
      ((cpmap cp).pointer :: cpker cp).map ((cpmap cp).pointee.icpH (cpmap cp).pointer) := by
  show (match (cpmap cp).pointee.cpring (cpmap cp).pointer with
    | _ :: x :: _ => (x :: cpker cp).map ((cpmap cp).pointee.icpH (cpmap cp).pointer)
    | _ => []) = _
  rw [(cpmap cp).pointee.head_proper_cpring _ h]

namespace Hypermap

variable {D : Type*} [Finite D] (G : Hypermap D)

omit [Finite D] in
/-- Face-simplicity is invariant under permutation (math-comp `simple_catCA` and friends). -/
private theorem simple_perm {p q : List D} (h : p.Perm q) : G.Simple p ↔ G.Simple q :=
  (h.map _).nodup_iff

/-- Face-simplicity only depends on the faces of the darts. -/
private theorem simple_cons_cface {a b : D} (h : G.cface a b) (p : List D) :
    G.Simple (a :: p) ↔ G.Simple (b :: p) := by
  rw [simple_cons, simple_cons, (G.fbandF p).connect_iff h]

end Hypermap

/-- The rotation of the ring does not change the darts it contains. -/
private theorem perm_rot_append {α : Type*} (n : ℕ) (c k : List α) :
    (rot n c ++ k).Perm (c ++ k) := by
  refine List.Perm.append_right _ ?_
  rw [rot]
  exact List.perm_append_comm.trans (by rw [List.take_append_drop])

/-- math-comp `cpmap_simple`. -/
theorem cpmap_simple {cp : Cprog} (h : configProg cp) :
    (cpmap cp).pointee.Simple ((cpmap cp).pointee.cpring (cpmap cp).pointer ++ cpker cp) := by
  induction cp with
  | nil => simp [configProg] at h
  | cons s cp ih =>
    cases s with
    | R n =>
      show ((cpmap cp).pointee.ecpR n (cpmap cp).pointer).pointee.Simple
        (((cpmap cp).pointee.ecpR n (cpmap cp).pointer).pointee.cpring
          ((cpmap cp).pointee.ecpR n (cpmap cp).pointer).pointer ++ cpker cp)
      rw [cpring_ecpR]
      exact ((cpmap cp).pointee.simple_perm (perm_rot_append n _ _)).2 (ih h)
    | Y =>
      set G := (cpmap cp).pointee with hG
      set x0 := (cpmap cp).pointer with hx0
      set M := (G.ecpY x0).pointee with hM
      -- the simplicity of the ring and kernel of `G`
      have hGs : G.Simple (G.cpring x0 ++ cpker cp) := by
        cases cp with
        | nil =>
          rw [cpker_nil, List.append_nil]
          show cpmap0.Simple (cpmap0.cpring true)
          rw [cpring0, simple_recI]
          refine ⟨?_, fun h => ?_, trivial⟩
          · rintro ⟨y, hy, hxy⟩
            rw [List.mem_singleton] at hy
            subst hy
            exact absurd ((cface_cpmap0 _ _).1 hxy) (by decide)
          · obtain ⟨y, hy, -⟩ := h
            simp at hy
        | cons s' cp' => exact ih h
      show M.Simple (M.cpring (G.ecpY x0).pointer ++ (cpker cp).map (G.icpY x0))
      rw [cpring_ecpY]
      show M.Simple (M.node (G.ecpY x0).pointer :: (G.ecpY x0).pointer ::
        ((G.cpring x0).tail.map (G.icpY x0) ++ (cpker cp).map (G.icpY x0)))
      rw [M.simple_cons_cface (G.cface_node_ecpY x0)]
      rw [M.simple_perm (List.Perm.swap _ _ _), ← List.map_append, ← List.map_cons,
        ← List.cons_append, ← G.head_cpring x0, M.simple_cons]
      refine ⟨?_, (simple_map (G.cface_icpY x0) _).2 hGs⟩
      rintro ⟨w, hw, hXw⟩
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hw
      have := (G.cface_ecpY x0 _).1 hXw
      rw [face_ecpY] at this
      simp at this
    | H =>
      have h' : configProg cp := h
      have hp := cpmap_proper (config_prog_cubic h')
      set G := (cpmap cp).pointee with hG
      set x0 := (cpmap cp).pointer with hx0
      set M := (G.ecpH x0).pointee with hM
      have hc := G.head_proper_cpring x0 hp
      rw [cpker_H hp]
      show M.Simple (M.cpring (G.ecpH x0).pointer ++ (x0 :: cpker cp).map (G.icpH x0))
      rw [G.cpring_ecpH x0 hp]
      show M.Simple (M.node (G.ecpH x0).pointer :: (G.ecpH x0).pointer ::
        (((G.cpring x0).drop 2).map (G.icpH x0) ++ (x0 :: cpker cp).map (G.icpH x0)))
      rw [M.simple_cons_cface (G.cface_node_ecpH x0 hp)]
      have hperm : (G.icpH x0 (G.node x0) :: (G.ecpH x0).pointer ::
          (((G.cpring x0).drop 2).map (G.icpH x0) ++ (x0 :: cpker cp).map (G.icpH x0))).Perm
          ((G.ecpH x0).pointer :: (G.cpring x0 ++ cpker cp).map (G.icpH x0)) := by
        rw [hc]
        simp only [List.drop_succ_cons, List.drop_zero, List.map_cons, List.cons_append,
          List.map_append]
        refine (List.Perm.swap _ _ _).trans (List.Perm.cons _ (List.Perm.cons _ ?_))
        exact List.perm_middle
      rw [M.simple_perm hperm, M.simple_cons]
      refine ⟨?_, (simple_map (G.cface_icpH x0) _).2 (ih h')⟩
      rintro ⟨w, hw, hXw⟩
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hw
      have := (G.cface_ecpH x0 hp _).1 hXw
      rw [G.face_face_ecpH x0 hp, face_ecpH] at this
      simp at this
    | _ => simp [configProg] at h

/-- math-comp `cpmap_cover`: the ring and the kernel sequence of `cpmap cp` meet every face. -/
theorem cpmap_cover {cp : Cprog} (h : configProg cp) (u : (cpmap cp).D) :
    u ∈ (cpmap cp).pointee.fband ((cpmap cp).pointee.cpring (cpmap cp).pointer ++ cpker cp) := by
  induction cp with
  | nil => simp [configProg] at h
  | cons s cp ih =>
    cases s with
    | R n =>
      show u ∈ ((cpmap cp).pointee.ecpR n (cpmap cp).pointer).pointee.fband
        (((cpmap cp).pointee.ecpR n (cpmap cp).pointer).pointee.cpring
          ((cpmap cp).pointee.ecpR n (cpmap cp).pointer).pointer ++ cpker cp)
      rw [cpring_ecpR]
      obtain ⟨w, hw, huw⟩ := ih h u
      exact ⟨w, (perm_rot_append n _ _).mem_iff.2 hw, huw⟩
    | Y =>
      set G := (cpmap cp).pointee with hG
      set x0 := (cpmap cp).pointer with hx0
      set M := (G.ecpY x0).pointee with hM
      have hGc : ∀ x, x ∈ G.fband (G.cpring x0 ++ cpker cp) := by
        cases cp with
        | nil =>
          intro x
          rw [cpker_nil, List.append_nil]
          show x ∈ cpmap0.fband (cpmap0.cpring true)
          rw [cpring0]
          exact ⟨x, by cases x <;> simp, connect_refl _⟩
        | cons s' cp' => exact ih h
      show u ∈ M.fband (M.cpring (G.ecpY x0).pointer ++ (cpker cp).map (G.icpY x0))
      rw [cpring_ecpY]
      rcases G.fband_icpY x0 u with ⟨x, hx⟩ | hX
      · obtain ⟨w, hw, hxw⟩ := hGc x
        have huw : M.cface u (G.icpY x0 w) := connect_trans hx ((G.cface_icpY x0 x w).2 hxw)
        rw [List.mem_append, G.head_cpring x0, List.mem_cons] at hw
        rcases hw with (rfl | hw) | hw
        · exact ⟨_, List.mem_cons_self,
            connect_trans huw (M.cfaceC.1 (G.cface_node_ecpY x0))⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_map_of_mem hw))), huw⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_map_of_mem hw))), huw⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, M.cfaceC.1 hX⟩
    | H =>
      have h' : configProg cp := h
      have hp := cpmap_proper (config_prog_cubic h')
      set G := (cpmap cp).pointee with hG
      set x0 := (cpmap cp).pointer with hx0
      set M := (G.ecpH x0).pointee with hM
      rw [cpker_H hp]
      show u ∈ M.fband (M.cpring (G.ecpH x0).pointer ++ (x0 :: cpker cp).map (G.icpH x0))
      rw [G.cpring_ecpH x0 hp]
      rcases G.fband_icpH x0 u with ⟨x, hx⟩ | hX
      · obtain ⟨w, hw, hxw⟩ := ih h' x
        have huw : M.cface u (G.icpH x0 w) := connect_trans hx ((G.cface_icpH x0 x w).2 hxw)
        rw [List.mem_append, G.head_proper_cpring x0 hp, List.mem_cons, List.mem_cons] at hw
        rcases hw with (rfl | rfl | hw) | hw
        · exact ⟨_, List.mem_cons_self,
            connect_trans huw (M.cfaceC.1 (G.cface_node_ecpH x0 hp))⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_map_of_mem List.mem_cons_self))), huw⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_left _ (List.mem_map_of_mem hw))), huw⟩
        · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_append_right _ (List.mem_map_of_mem (List.mem_cons_of_mem _ hw)))), huw⟩
      · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, M.cfaceC.1 hX⟩
    | _ => simp [configProg] at h

/-! ### Injections between configuration maps -/

/-- The injection of a single construction step `s` (the inner `match` of math-comp `injcp`). -/
noncomputable def icpStep : (s : Cpstep) → (cp : Cprog) → (cpmap cp).D → (cpmap (s :: cp)).D
  | .R _, _, x => x
  | .R', _, x => x
  | .Y, cp, x => (cpmap cp).pointee.icpY (cpmap cp).pointer x
  | .H, cp, x => (cpmap cp).pointee.icpH (cpmap cp).pointer x
  | .U, cp, x => (cpmap cp).pointee.icpU (cpmap cp).pointer x
  | .K, cp, x => (cpmap cp).pointee.icpK (cpmap cp).pointer x
  | .A, _, x => x

/-- math-comp `injcp cp1 cp2`: the injection from `cpmap cp2` to `cpmap (catrev cp1 cp2)`
(math-comp's `catrev cp1 cp2` is `List.reverseAux cp1 cp2 = cp1.reverse ++ cp2`). -/
noncomputable def injcp : (cp1 cp2 : Cprog) → (cpmap cp2).D → (cpmap (cp1.reverseAux cp2)).D
  | [], _, x => x
  | s :: cp1, cp2, x => injcp cp1 (s :: cp2) (icpStep s cp2 x)

/-- `injcp` of the empty program is the identity (by definition). -/
theorem injcp_nil (cp2 : Cprog) (x : (cpmap cp2).D) : injcp [] cp2 x = x := rfl

/-- `injcp` of a nonempty program (by definition). -/
theorem injcp_cons (s : Cpstep) (cp1 cp2 : Cprog) (x : (cpmap cp2).D) :
    injcp (s :: cp1) cp2 x = injcp cp1 (s :: cp2) (icpStep s cp2 x) := rfl

/-- Each construction step injects the darts. -/
theorem icpStep_inj (s : Cpstep) (cp : Cprog) : Injective (icpStep s cp) := by
  cases s with
  | Y => exact (cpmap cp).pointee.icpY_inj _
  | H => exact (cpmap cp).pointee.icpH_inj _
  | U => exact (cpmap cp).pointee.icpU_inj _
  | K => exact (cpmap cp).pointee.icpK_inj _
  | _ => exact injective_id

/-- math-comp `injcp_inj`. -/
theorem injcp_inj (cp1 cp2 : Cprog) : Injective (injcp cp1 cp2) := by
  induction cp1 generalizing cp2 with
  | nil => exact injective_id
  | cons s cp1 ih => exact (ih _).comp (icpStep_inj s cp2)

/-- math-comp `sub_cface_injcp`. -/
theorem sub_cface_injcp (cp1 cp2 : Cprog) {x y : (cpmap cp2).D}
    (h : (cpmap cp2).pointee.cface x y) :
    (cpmap (cp1.reverseAux cp2)).pointee.cface (injcp cp1 cp2 x) (injcp cp1 cp2 y) := by
  induction cp1 generalizing cp2 with
  | nil => exact h
  | cons s cp1 ih =>
    apply ih
    cases s with
    | R n => exact h
    | R' => exact h
    | Y => exact ((cpmap cp2).pointee.cface_icpY _ _ _).2 h
    | H => exact ((cpmap cp2).pointee.cface_icpH _ _ _).2 h
    | U => exact ((cpmap cp2).pointee.cface_icpU _ _ _).2 h
    | K => exact ((cpmap cp2).pointee.cface_icpK _ _ _).2 h
    | A => exact (cpmap cp2).pointee.sub_cface_icpA _ h

/-- math-comp `sub_adj_injcp`. -/
theorem sub_adj_injcp (cp1 cp2 : Cprog) {x y : (cpmap cp2).D}
    (h : (cpmap cp2).pointee.adj x y) :
    (cpmap (cp1.reverseAux cp2)).pointee.adj (injcp cp1 cp2 x) (injcp cp1 cp2 y) := by
  induction cp1 generalizing cp2 with
  | nil => exact h
  | cons s cp1 ih =>
    apply ih
    cases s with
    | R n => exact h
    | R' => exact h
    | Y => exact ((cpmap cp2).pointee.adj_icpY _ _ _).2 h
    | H => exact ((cpmap cp2).pointee.adj_icpH _ _ _).2 h
    | U => exact ((cpmap cp2).pointee.adj_icpU _ _ _).2 h
    | K => exact (cpmap cp2).pointee.sub_adj_icpK _ h
    | A => exact (cpmap cp2).pointee.sub_adj_icpA _ h

/-- math-comp `cface_injcp`. -/
theorem cface_injcp {cp1 : Cprog} (hcp : cubicProg cp1) (cp2 : Cprog) (x y : (cpmap cp2).D) :
    (cpmap (cp1.reverseAux cp2)).pointee.cface (injcp cp1 cp2 x) (injcp cp1 cp2 y) ↔
      (cpmap cp2).pointee.cface x y := by
  induction cp1 generalizing cp2 with
  | nil => exact Iff.rfl
  | cons s cp1 ih =>
    refine (ih ?_ (s :: cp2) _ _).trans ?_
    · cases s <;> first | exact hcp | simp [cubicProg] at hcp
    cases s with
    | R n => exact Iff.rfl
    | Y => exact (cpmap cp2).pointee.cface_icpY _ _ _
    | H => exact (cpmap cp2).pointee.cface_icpH _ _ _
    | U => exact (cpmap cp2).pointee.cface_icpU _ _ _
    | _ => simp [cubicProg] at hcp

/-- math-comp `edge_injcp`. -/
theorem edge_injcp {cp1 : Cprog} (hcp : cubicProg cp1) (cp2 : Cprog) (x : (cpmap cp2).D) :
    injcp cp1 cp2 ((cpmap cp2).pointee.edge x) =
      (cpmap (cp1.reverseAux cp2)).pointee.edge (injcp cp1 cp2 x) := by
  induction cp1 generalizing cp2 with
  | nil => rfl
  | cons s cp1 ih =>
    have hcp' : cubicProg cp1 := by cases s <;> first | exact hcp | simp [cubicProg] at hcp
    show injcp cp1 (s :: cp2) (icpStep s cp2 ((cpmap cp2).pointee.edge x)) =
      (cpmap (cp1.reverseAux (s :: cp2))).pointee.edge (injcp cp1 (s :: cp2) (icpStep s cp2 x))
    rw [← ih hcp' (s :: cp2)]
    congr 1
    cases s with
    | R n => rfl
    | Y => rfl
    | H => rfl
    | U => rfl
    | _ => simp [cubicProg] at hcp

/-- math-comp `adj_injcp`. -/
theorem adj_injcp {cp1 : Cprog} (hcp : cubicProg cp1) (cp2 : Cprog) (x y : (cpmap cp2).D) :
    (cpmap (cp1.reverseAux cp2)).pointee.adj (injcp cp1 cp2 x) (injcp cp1 cp2 y) ↔
      (cpmap cp2).pointee.adj x y := by
  induction cp1 generalizing cp2 with
  | nil => exact Iff.rfl
  | cons s cp1 ih =>
    refine (ih ?_ (s :: cp2) _ _).trans ?_
    · cases s <;> first | exact hcp | simp [cubicProg] at hcp
    cases s with
    | R n => exact Iff.rfl
    | Y => exact (cpmap cp2).pointee.adj_icpY _ _ _
    | H => exact (cpmap cp2).pointee.adj_icpH _ _ _
    | U => exact (cpmap cp2).pointee.adj_icpU _ _ _
    | _ => simp [cubicProg] at hcp

namespace Hypermap

variable {D : Type*} [Fintype D] [DecidableEq D] (G : Hypermap D) (x0 : D)

/-- The old darts on the ring of `ecpN x0` were on the ring of `x0`. -/
theorem mem_cpring_ecpN_Icp {v : D}
    (h : Icp v ∈ (G.ecpN x0).pointee.cpring (G.ecpN x0).pointer) : v ∈ G.cpring x0 := by
  rw [cpring_ecpN] at h
  split_ifs at h with hl
  · simp only [List.mem_cons, List.mem_map, Icp.injEq, reduceCtorEq, false_or] at h
    rcases h with rfl | ⟨w, hw, rfl⟩
    · rw [G.head_cpring x0]; exact List.mem_cons_self
    · exact List.mem_of_mem_drop hw
  · simp at h

/-- The old darts on the ring of `ecpU x0` were on the ring of `x0`. -/
theorem mem_cpring_ecpU_Icp {v : D}
    (h : Icp v ∈ (G.ecpU x0).pointee.cpring (G.ecpU x0).pointer) : v ∈ G.cpring x0 := by
  rw [cpring_ecpU] at h
  simp only [List.mem_cons, List.mem_map, Icp.injEq, reduceCtorEq, false_or] at h
  rcases h with h | ⟨w, hw, rfl⟩
  · exact absurd h (by simp [ecpUNode])
  · exact hw

/-- The old darts on the ring of `ecpY x0` were on the ring of `x0`. -/
theorem mem_cpring_ecpY_icpY {v : D}
    (h : G.icpY x0 v ∈ (G.ecpY x0).pointee.cpring (G.ecpY x0).pointer) : v ∈ G.cpring x0 :=
  G.mem_cpring_ecpU_Icp x0 ((G.ecpU x0).pointee.mem_cpring_ecpN_Icp _ h)

/-- The old darts on the ring of `ecpH x0` were on the ring of `x0`. -/
theorem mem_cpring_ecpH_icpH {v : D}
    (h : G.icpH x0 v ∈ (G.ecpH x0).pointee.cpring (G.ecpH x0).pointer) : v ∈ G.cpring x0 :=
  G.mem_cpring_ecpY_icpY x0 ((G.ecpY x0).pointee.mem_cpring_ecpN_Icp _ h)

end Hypermap

/-- math-comp `node_injcp`: `injcp` commutes with `node` off the ring. -/
theorem node_injcp {cp1 : Cprog} (hcp : cubicProg cp1) (cp2 : Cprog) (x : (cpmap cp2).D)
    (hx : x ∉ (cpmap cp2).pointee.cpring (cpmap cp2).pointer) :
    injcp cp1 cp2 ((cpmap cp2).pointee.node x) =
      (cpmap (cp1.reverseAux cp2)).pointee.node (injcp cp1 cp2 x) := by
  induction cp1 generalizing cp2 with
  | nil => rfl
  | cons s cp1 ih =>
    have hcp' : cubicProg cp1 := by cases s <;> first | exact hcp | simp [cubicProg] at hcp
    set G := (cpmap cp2).pointee with hG
    set x0 := (cpmap cp2).pointer with hx0
    have hxc : ¬ G.cnode x0 x := fun h => hx ((G.mem_cpring x0).2 h)
    have hx1 : x ≠ G.node x0 := fun h => hxc (h ▸ fconnect1 _ _)
    have hx2 : x ≠ x0 := fun h => hxc (h ▸ connect_refl _)
    cases s with
    | R n =>
      refine ih hcp' (.R n :: cp2) x ?_
      show x ∉ (G.ecpR n x0).pointee.cpring (G.ecpR n x0).pointer
      rw [cpring_ecpR, mem_rot]
      exact hx
    | Y =>
      show injcp cp1 (.Y :: cp2) (G.icpY x0 (G.node x)) =
        (cpmap (cp1.reverseAux (.Y :: cp2))).pointee.node (injcp cp1 (.Y :: cp2) (G.icpY x0 x))
      rw [G.icpY_node x0 x (by simp [hx1, hx2])]
      exact ih hcp' (.Y :: cp2) (G.icpY x0 x) (fun h => hx (G.mem_cpring_ecpY_icpY x0 h))
    | H =>
      have hx3 : x ≠ G.face (G.edge x0) := fun h =>
        hxc (G.cnodeC.1 (connect_of_rel (show G.node x = x0 by rw [h, G.edgeK])))
      show injcp cp1 (.H :: cp2) (G.icpH x0 (G.node x)) =
        (cpmap (cp1.reverseAux (.H :: cp2))).pointee.node (injcp cp1 (.H :: cp2) (G.icpH x0 x))
      rw [G.icpH_node x0 x (by simp [hx1, hx2, hx3])]
      exact ih hcp' (.H :: cp2) (G.icpH x0 x) (fun h => hx (G.mem_cpring_ecpH_icpH x0 h))
    | U =>
      show injcp cp1 (.U :: cp2) (G.icpU x0 (G.node x)) =
        (cpmap (cp1.reverseAux (.U :: cp2))).pointee.node (injcp cp1 (.U :: cp2) (G.icpU x0 x))
      rw [G.icpU_node x0 x (by simp [hx1])]
      exact ih hcp' (.U :: cp2) (G.icpU x0 x) (fun h => hx (G.mem_cpring_ecpU_Icp x0 h))
    | _ => simp [cubicProg] at hcp

/-- math-comp `cnode_injcp`: `injcp` preserves the node orbits off the ring. -/
theorem cnode_injcp {cp1 : Cprog} (hcp : cubicProg cp1) (cp2 : Cprog) (x : (cpmap cp2).D)
    (hx : x ∉ (cpmap cp2).pointee.cpring (cpmap cp2).pointer) (y : (cpmap cp2).D) :
    (cpmap (cp1.reverseAux cp2)).pointee.cnode (injcp cp1 cp2 x) (injcp cp1 cp2 y) ↔
      (cpmap cp2).pointee.cnode x y := by
  set G := (cpmap cp2).pointee with hG
  set H := (cpmap (cp1.reverseAux cp2)).pointee with hH
  have hoff : ∀ n, G.node^[n] x ∉ G.cpring (cpmap cp2).pointer := by
    intro n hn
    apply hx
    rw [G.mem_cpring] at hn ⊢
    exact connect_trans hn (G.cnodeC.1 (fconnect_iterate _ _ n))
  have key : ∀ n, injcp cp1 cp2 (G.node^[n] x) = H.node^[n] (injcp cp1 cp2 x) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iterate_succ_apply', iterate_succ_apply', node_injcp hcp cp2 _ (hoff n), ih]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := fconnect_iff_iterate.1 h
    rw [← key] at hn
    rw [← injcp_inj cp1 cp2 hn]
    exact fconnect_iterate _ _ n
  · intro h
    obtain ⟨n, rfl⟩ := fconnect_iff_iterate.1 h
    rw [key]
    exact fconnect_iterate _ _ n

/-! ### Ring and kernel sizes -/

/-- math-comp `size_ring_cpmap`. -/
theorem size_ring_cpmap (cp : Cprog) :
    ((cpmap cp).pointee.cpring (cpmap cp).pointer).length = cprsize cp := by
  induction cp with
  | nil => show (cpmap0.cpring true).length = 2; rw [cpring0]; rfl
  | cons s cp ih =>
    cases s with
    | R n => rw [cpmap_R, size_cpring_ecpR, ih]; rfl
    | R' => rw [cpmap_R', size_cpring_ecpR, ih]; rfl
    | Y => rw [cpmap_Y, size_cpring_ecpY, ih]; rfl
    | H => rw [cpmap_H, size_cpring_ecpH, ih]; rfl
    | U => rw [cpmap_U, size_cpring_ecpU, ih]; rfl
    | K => rw [cpmap_K, size_cpring_ecpK, ih]; rfl
    | A => rw [cpmap_A, size_cpring_ecpA, ih]; rfl

/-- math-comp `size_cpker`. -/
theorem size_cpker {cp : Cprog} (h : configProg cp) : (cpker cp).length = cpksize cp := by
  induction cp with
  | nil => simp [configProg] at h
  | cons s cp ih =>
    cases s with
    | R n =>
      show (cpker cp).length = _
      rw [ih h]
      simp [cpksize, isCpH]
    | Y =>
      show ((cpker cp).map ((cpmap cp).pointee.icpY (cpmap cp).pointer)).length = _
      rw [List.length_map]
      cases cp with
      | nil => rfl
      | cons s' cp' => rw [ih h]; simp [cpksize, isCpH, List.countP_cons]
    | H =>
      have h' : configProg cp := h
      rw [cpker_H (cpmap_proper (config_prog_cubic h'))]
      show (((cpmap cp).pointer :: cpker cp).map ((cpmap cp).pointee.icpH (cpmap cp).pointer)).length
        = _
      rw [List.length_map, List.length_cons, ih h']
      simp [cpksize, isCpH, List.countP_cons]
    | _ => simp [configProg] at h

/-! ### Face masks -/

/-- math-comp `cpmask cm cp`: the subsequence of `cpring (cpmap cp) ++ cpker cp` selected by
the face mask `cm`. -/
noncomputable def cpmask (cm : Cfmask) (cp : Cprog) : List (cpmap cp).D :=
  mask cm.mr ((cpmap cp).pointee.cpring (cpmap cp).pointer) ++ mask cm.mk (cpker cp)

/-- math-comp `cpmask1`: `cfmask1 cp i` selects the `i`-th dart of `cpker cp`. -/
theorem cpmask1 {cp : Cprog} {i : ℕ} (hi : i < cpksize cp) (h : configProg cp) :
    cpmask (cfmask1 cp i) cp = [(cpker cp).getD i (cpmap cp).pointer] := by
  unfold cpmask cfmask1
  simp only
  rw [mask_false, List.nil_append, ← size_cpker h]
  rw [← size_cpker h] at hi
  have := mask_range'_beq (s := 0) (i := i) (cpker cp) hi (cpmap cp).pointer
  rw [Nat.zero_add] at this
  exact this

/-- In `cpmap0`, adjacent faces are the ends of edges. -/
theorem adj_cpmap0 (a b : Bool) : cpmap0.adj a b ↔ b = !a := by
  rw [cpmap0.adjP]
  constructor
  · rintro ⟨z, hz, hzb⟩
    rw [cface_cpmap0] at hz
    subst hz
    exact ((cface_cpmap0 _ _).1 hzb).symm
  · rintro rfl
    exact ⟨a, connect_refl _, (cface_cpmap0 _ _).2 rfl⟩

/-! ### Adjacency masks -/

namespace Hypermap

variable {D : Type*} [Fintype D] [DecidableEq D] (G : Hypermap D) (x0 : D)

/-- The propositional core of the `Y` step of math-comp `cpmask_adj`. -/
private theorem cpmask_adj_prop_Y {a0 a2 b0 b1 b2 c1 c2 C K e1 e2 F Ka : Prop}
    (IH : ((a0 ∧ c1 ∨ a2 ∧ c2 ∨ C) ∨ K) ↔ ((b0 ∧ e1 ∨ b2 ∧ e2 ∨ F) ∨ Ka)) :
    (((a0 ∨ b1) ∧ c1 ∨ (a2 ∨ b1) ∧ c2 ∨ C) ∨ K) ↔
      ((b0 ∧ e1 ∨ b1 ∧ (c1 ∨ c2) ∨ b2 ∧ e2 ∨ F) ∨ Ka) := by
  have hL : (((a0 ∨ b1) ∧ c1 ∨ (a2 ∨ b1) ∧ c2 ∨ C) ∨ K) ↔
      ((a0 ∧ c1 ∨ a2 ∧ c2 ∨ C) ∨ K) ∨ b1 ∧ (c1 ∨ c2) := by
    constructor
    · rintro ((⟨h1 | h1, h2⟩ | ⟨h1 | h1, h2⟩ | h3) | h4)
      · exact Or.inl (Or.inl (Or.inl ⟨h1, h2⟩))
      · exact Or.inr ⟨h1, Or.inl h2⟩
      · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨h1, h2⟩)))
      · exact Or.inr ⟨h1, Or.inr h2⟩
      · exact Or.inl (Or.inl (Or.inr (Or.inr h3)))
      · exact Or.inl (Or.inr h4)
    · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩ | h3) | h4) | ⟨h1, h2 | h2⟩)
      · exact Or.inl (Or.inl ⟨Or.inl h1, h2⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨Or.inl h1, h2⟩))
      · exact Or.inl (Or.inr (Or.inr h3))
      · exact Or.inr h4
      · exact Or.inl (Or.inl ⟨Or.inr h1, h2⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨Or.inr h1, h2⟩))
  have hR : ∀ B : Prop, ((b0 ∧ e1 ∨ B ∨ b2 ∧ e2 ∨ F) ∨ Ka) ↔
      ((b0 ∧ e1 ∨ b2 ∧ e2 ∨ F) ∨ Ka) ∨ B := by
    intro B
    constructor
    · rintro ((h | h | h | h) | h)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
      · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
      · exact Or.inl (Or.inl (Or.inr (Or.inr h)))
      · exact Or.inl (Or.inr h)
    · rintro (((h | h | h) | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
      · exact Or.inr h
      · exact Or.inl (Or.inr (Or.inl h))
  rw [hL, hR, IH]

/-- The `Y` step of math-comp `cpmask_adj`, for an arbitrary hypermap. -/
private theorem cpmask_adj_ecpY (plainG : G.Plain) (hp : G.ProperCpring x0) (k : List D)
    (hs : G.Simple (G.cpring x0 ++ k)) {b0 b1 b2 a0 a2 : Bool} {mr₀ mk mr' mk' : List Bool}
    (IH : ∀ x, x ∈ G.fband (mask (a0 :: a2 :: mr') (G.cpring x0) ++ mask mk' k) ↔
      ∃ y ∈ mask (b0 :: b2 :: mr₀) (G.cpring x0) ++ mask mk k, G.adj x y)
    (u : (G.ecpY x0).D) :
    u ∈ (G.ecpY x0).pointee.fband (mask ((a0 || b1) :: (b0 || b2) :: (a2 || b1) :: mr')
        ((G.ecpY x0).pointee.cpring (G.ecpY x0).pointer) ++ mask mk' (k.map (G.icpY x0))) ↔
      ∃ y ∈ mask (b0 :: b1 :: b2 :: mr₀) ((G.ecpY x0).pointee.cpring (G.ecpY x0).pointer) ++
        mask mk (k.map (G.icpY x0)), (G.ecpY x0).pointee.adj u y := by
  set M := (G.ecpY x0).pointee with hM
  set X := (G.ecpY x0).pointer with hX
  have hnX : M.cface (M.node X) (G.icpY x0 (G.node x0)) := G.cface_node_ecpY x0
  have hplainM : M.Plain := G.plain_ecpY x0 plainG
  have hXold : ∀ w, ¬ M.cface X (G.icpY x0 w) := by
    intro w h
    have := (G.cface_ecpY x0 _).1 h
    rw [face_ecpY] at this
    simp at this
  have hc := G.head_proper_cpring x0 hp
  rw [hc] at hs IH
  generalize (G.cpring x0).drop 2 = c₂ at hc hs IH
  rw [G.cpring_ecpY x0, hc, List.tail_cons, List.map_cons]
  -- simplicity of the ring and kernel of `G`
  rw [List.cons_append, List.cons_append, G.simple_cons, G.simple_cons] at hs
  have hs1 : ∀ w ∈ c₂ ++ k, ¬ G.cface w (G.node x0) := fun w hw h =>
    hs.1 ((G.fband_cons _ _ _).2 (Or.inr ⟨w, hw, G.cfaceC.1 h⟩))
  have hs2 : ∀ w ∈ c₂ ++ k, ¬ G.cface w x0 := fun w hw h => hs.2.1 ⟨w, hw, G.cfaceC.1 h⟩
  simp only [Hypermap.mem_fband, exists_mem_append', exists_mem_mask_cons,
    exists_mem_mask_map] at IH ⊢
  rcases G.fband_icpY x0 u with ⟨x, hux⟩ | hXu
  · have hsame : ∀ w, M.cface u w ↔ M.cface (G.icpY x0 x) w := fun w => M.same_cface hux w
    have f1 : M.cface u (((G.ecpUMap x0).ecpNMap IcpX).node IcpX) ↔ G.cface x (G.node x0) :=
      (hsame _).trans ((M.cface_sym.same_r hnX _).trans (G.cface_icpY x0 x _))
    have f2 : M.cface u IcpX ↔ False :=
      ⟨fun h => hXold x (M.cfaceC.1 ((hsame X).1 h)), False.elim⟩
    have f3 : ∀ w, M.cface u (G.icpY x0 w) ↔ G.cface x w := fun w =>
      (hsame _).trans (G.cface_icpY x0 x w)
    have g1 : M.adj u (((G.ecpUMap x0).ecpNMap IcpX).node IcpX) ↔ G.adj x (G.node x0) :=
      (M.adjF hux _).trans ((M.adjFr hnX _).trans (G.adj_icpY x0 x _))
    have g2 : M.adj u IcpX ↔ G.cface x (G.node x0) ∨ G.cface x x0 := by
      show M.adj u X ↔ _
      rw [M.adjF hux, M.adjC hplainM, G.adj_ecpY x0 hp, Hypermap.mem_fband]
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        exists_eq_or_imp, exists_eq_left, G.cface_icpY]
    have g3 : ∀ w, M.adj u (G.icpY x0 w) ↔ G.adj x w := fun w =>
      (M.adjF hux _).trans (G.adj_icpY x0 x w)
    have IHx := IH x
    simp only [f1, f2, f3, g1, g2, g3, Bool.or_eq_true, and_false, false_or]
    exact cpmask_adj_prop_Y IHx
  · have hsame : ∀ w, M.cface u w ↔ M.cface X w := fun w => M.same_cface (M.cfaceC.1 hXu) w
    have f1 : M.cface u (((G.ecpUMap x0).ecpNMap IcpX).node IcpX) ↔ False :=
      ⟨fun h => hXold _ (connect_trans ((hsame _).1 h) hnX), False.elim⟩
    have f2 : M.cface u IcpX ↔ True := ⟨fun _ => trivial, fun _ => M.cfaceC.1 hXu⟩
    have f3 : ∀ w, M.cface u (G.icpY x0 w) ↔ False := fun w =>
      ⟨fun h => hXold w ((hsame _).1 h), False.elim⟩
    have hadj : ∀ y, M.adj u y ↔ y ∈ M.fband ([G.node x0, x0].map (G.icpY x0)) := fun y =>
      (M.adjF (M.cfaceC.1 hXu) y).trans (G.adj_ecpY x0 hp y)
    have g1 : M.adj u (((G.ecpUMap x0).ecpNMap IcpX).node IcpX) ↔ True :=
      ⟨fun _ => trivial, fun _ => (hadj _).2 ⟨_, List.mem_cons_self, hnX⟩⟩
    have g2 : M.adj u IcpX ↔ False := by
      refine ⟨fun h => ?_, False.elim⟩
      obtain ⟨w, hw, hXw⟩ := (hadj _).1 h
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> exact hXold _ hXw
    have g3 : M.adj u (G.icpY x0 x0) ↔ True :=
      ⟨fun _ => trivial, fun _ => (hadj _).2 ⟨_, by simp, connect_refl _⟩⟩
    have g4 : ∀ w ∈ c₂ ++ k, ¬ M.adj u (G.icpY x0 w) := by
      intro w hw h
      obtain ⟨v, hv, hwv⟩ := (hadj _).1 h
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact hs1 w hw ((G.cface_icpY x0 _ _).1 hwv)
      · exact hs2 w hw ((G.cface_icpY x0 _ _).1 hwv)
    have e1 : (∃ y ∈ mask mr₀ c₂, M.adj u (G.icpY x0 y)) ↔ False :=
      ⟨fun ⟨y, hy, h⟩ => g4 y (List.mem_append_left _ (mem_of_mem_mask hy)) h, False.elim⟩
    have e2 : (∃ y ∈ mask mk k, M.adj u (G.icpY x0 y)) ↔ False :=
      ⟨fun ⟨y, hy, h⟩ => g4 y (List.mem_append_right _ (mem_of_mem_mask hy)) h, False.elim⟩
    simp only [f1, f2, f3, g1, g2, g3, e1, e2, Bool.or_eq_true, and_false, and_true, false_or,
      or_false]
    simp

/-- The propositional core of the `H` step of math-comp `cpmask_adj`. -/
private theorem cpmask_adj_prop_H {a0 a1 a2 b0 b1 b1' b2 c0 cx cf C K e0 ex ef F Ka : Prop}
    (IH : ((a0 ∧ c0 ∨ a1 ∧ cx ∨ a2 ∧ cf ∨ C) ∨ K) ↔ ((b0 ∧ e0 ∨ b1' ∧ ex ∨ b2 ∧ ef ∨ F) ∨ Ka)) :
    (((a0 ∨ b1) ∧ c0 ∨ (a2 ∨ b1) ∧ cf ∨ C) ∨ (a1 ∨ b1) ∧ cx ∨ K) ↔
      ((b0 ∧ e0 ∨ b1 ∧ (c0 ∨ cx ∨ cf) ∨ b2 ∧ ef ∨ F) ∨ b1' ∧ ex ∨ Ka) := by
  have hL : (((a0 ∨ b1) ∧ c0 ∨ (a2 ∨ b1) ∧ cf ∨ C) ∨ (a1 ∨ b1) ∧ cx ∨ K) ↔
      ((a0 ∧ c0 ∨ a1 ∧ cx ∨ a2 ∧ cf ∨ C) ∨ K) ∨ b1 ∧ (c0 ∨ cx ∨ cf) := by
    constructor
    · rintro ((⟨h1 | h1, h2⟩ | ⟨h1 | h1, h2⟩ | h3) | ⟨h1 | h1, h2⟩ | h4)
      · exact Or.inl (Or.inl (Or.inl ⟨h1, h2⟩))
      · exact Or.inr ⟨h1, Or.inl h2⟩
      · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))))
      · exact Or.inr ⟨h1, Or.inr (Or.inr h2)⟩
      · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h3))))
      · exact Or.inl (Or.inl (Or.inr (Or.inl ⟨h1, h2⟩)))
      · exact Or.inr ⟨h1, Or.inr (Or.inl h2)⟩
      · exact Or.inl (Or.inr h4)
    · rintro (((⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | h3) | h4) | ⟨h1, h2 | h2 | h2⟩)
      · exact Or.inl (Or.inl ⟨Or.inl h1, h2⟩)
      · exact Or.inr (Or.inl ⟨Or.inl h1, h2⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨Or.inl h1, h2⟩))
      · exact Or.inl (Or.inr (Or.inr h3))
      · exact Or.inr (Or.inr h4)
      · exact Or.inl (Or.inl ⟨Or.inr h1, h2⟩)
      · exact Or.inr (Or.inl ⟨Or.inr h1, h2⟩)
      · exact Or.inl (Or.inr (Or.inl ⟨Or.inr h1, h2⟩))
  have hR : ∀ B : Prop, ((b0 ∧ e0 ∨ B ∨ b2 ∧ ef ∨ F) ∨ b1' ∧ ex ∨ Ka) ↔
      ((b0 ∧ e0 ∨ b1' ∧ ex ∨ b2 ∧ ef ∨ F) ∨ Ka) ∨ B := by
    intro B
    constructor
    · rintro ((h | h | h | h) | h | h)
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
      · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr h))))
      · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
      · exact Or.inl (Or.inr h)
    · rintro (((h | h | h | h) | h) | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr h)))
      · exact Or.inr (Or.inr h)
      · exact Or.inl (Or.inr (Or.inl h))
  rw [hL, hR, IH]

/-- The `H` step of math-comp `cpmask_adj`, for an arbitrary hypermap. -/
private theorem cpmask_adj_ecpH (plainG : G.Plain) (hp : G.ProperCpring x0)
    (hl : G.LongCpring x0) (k : List D) (hs : G.Simple (G.cpring x0 ++ k))
    {b0 b1 b2 b1' a0 a1 a2 : Bool} {mr₀ mk₀ mr' mk' : List Bool}
    (IH : ∀ x, x ∈ G.fband (mask (a0 :: a1 :: a2 :: mr') (G.cpring x0) ++ mask mk' k) ↔
      ∃ y ∈ mask (b0 :: b1' :: b2 :: mr₀) (G.cpring x0) ++ mask mk₀ k, G.adj x y)
    (u : (G.ecpH x0).D) :
    u ∈ (G.ecpH x0).pointee.fband (mask ((a0 || b1) :: (b0 || (b1' || b2)) :: (a2 || b1) :: mr')
        ((G.ecpH x0).pointee.cpring (G.ecpH x0).pointer) ++
          mask ((a1 || b1) :: mk') ((x0 :: k).map (G.icpH x0))) ↔
      ∃ y ∈ mask (b0 :: b1 :: b2 :: mr₀) ((G.ecpH x0).pointee.cpring (G.ecpH x0).pointer) ++
        mask (b1' :: mk₀) ((x0 :: k).map (G.icpH x0)), (G.ecpH x0).pointee.adj u y := by
  set M := (G.ecpH x0).pointee with hM
  set X := (G.ecpH x0).pointer with hX
  have hnX : M.cface (M.node X) (G.icpH x0 (G.node x0)) := G.cface_node_ecpH x0 hp
  have hplainM : M.Plain := G.plain_ecpH x0 plainG
  have hXold : ∀ w, ¬ M.cface X (G.icpH x0 w) := by
    intro w h
    have := (G.cface_ecpH x0 hp _).1 h
    rw [G.face_face_ecpH x0 hp, face_ecpH] at this
    simp at this
  have hc := G.head_long_cpring x0 hl
  rw [hc] at hs IH
  generalize (G.cpring x0).drop 3 = c₃ at hc hs IH
  rw [G.cpring_ecpH x0 hp, hc]
  simp only [List.drop_succ_cons, List.drop_zero, List.map_cons]
  rw [List.cons_append, List.cons_append, List.cons_append, G.simple_cons, G.simple_cons,
    G.simple_cons] at hs
  have hs1 : ∀ w ∈ c₃ ++ k, ¬ G.cface w (G.node x0) := fun w hw h =>
    hs.1 ((G.fband_cons _ _ _).2 (Or.inr ((G.fband_cons _ _ _).2 (Or.inr ⟨w, hw, G.cfaceC.1 h⟩))))
  have hs2 : ∀ w ∈ c₃ ++ k, ¬ G.cface w x0 := fun w hw h =>
    hs.2.1 ((G.fband_cons _ _ _).2 (Or.inr ⟨w, hw, G.cfaceC.1 h⟩))
  have hs3 : ∀ w ∈ c₃ ++ k, ¬ G.cface w (G.face (G.edge x0)) := fun w hw h =>
    hs.2.2.1 ⟨w, hw, G.cfaceC.1 h⟩
  simp only [Hypermap.mem_fband, exists_mem_append', exists_mem_mask_cons,
    exists_mem_mask_map] at IH ⊢
  rcases G.fband_icpH x0 u with ⟨x, hux⟩ | hXu
  · have hsame : ∀ w, M.cface u w ↔ M.cface (G.icpH x0 x) w := fun w => M.same_cface hux w
    have f1 : M.cface u ((((G.ecpUMap x0).ecpNMap IcpX).ecpNMap IcpX).node IcpX) ↔
        G.cface x (G.node x0) :=
      (hsame _).trans ((M.cface_sym.same_r hnX _).trans (G.cface_icpH x0 x _))
    have f2 : M.cface u IcpX ↔ False :=
      ⟨fun h => hXold x (M.cfaceC.1 ((hsame X).1 h)), False.elim⟩
    have f3 : ∀ w, M.cface u (G.icpH x0 w) ↔ G.cface x w := fun w =>
      (hsame _).trans (G.cface_icpH x0 x w)
    have g1 : M.adj u ((((G.ecpUMap x0).ecpNMap IcpX).ecpNMap IcpX).node IcpX) ↔
        G.adj x (G.node x0) :=
      (M.adjF hux _).trans ((M.adjFr hnX _).trans (G.adj_icpH x0 x _))
    have g2 : M.adj u IcpX ↔
        G.cface x (G.node x0) ∨ G.cface x x0 ∨ G.cface x (G.face (G.edge x0)) := by
      show M.adj u X ↔ _
      rw [M.adjF hux, M.adjC hplainM, G.adj_ecpH x0 hp, Hypermap.mem_fband]
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false,
        exists_eq_or_imp, exists_eq_left, G.cface_icpH]
    have g3 : ∀ w, M.adj u (G.icpH x0 w) ↔ G.adj x w := fun w =>
      (M.adjF hux _).trans (G.adj_icpH x0 x w)
    have IHx := IH x
    simp only [f1, f2, f3, g1, g2, g3, Bool.or_eq_true, and_false, false_or]
    exact cpmask_adj_prop_H IHx
  · have hsame : ∀ w, M.cface u w ↔ M.cface X w := fun w => M.same_cface (M.cfaceC.1 hXu) w
    have f1 : M.cface u ((((G.ecpUMap x0).ecpNMap IcpX).ecpNMap IcpX).node IcpX) ↔ False :=
      ⟨fun h => hXold _ (connect_trans ((hsame _).1 h) hnX), False.elim⟩
    have f2 : M.cface u IcpX ↔ True := ⟨fun _ => trivial, fun _ => M.cfaceC.1 hXu⟩
    have f3 : ∀ w, M.cface u (G.icpH x0 w) ↔ False := fun w =>
      ⟨fun h => hXold w ((hsame _).1 h), False.elim⟩
    have hadj : ∀ y, M.adj u y ↔
        y ∈ M.fband ([G.node x0, x0, G.face (G.edge x0)].map (G.icpH x0)) := fun y =>
      (M.adjF (M.cfaceC.1 hXu) y).trans (G.adj_ecpH x0 hp y)
    have g1 : M.adj u ((((G.ecpUMap x0).ecpNMap IcpX).ecpNMap IcpX).node IcpX) ↔ True :=
      ⟨fun _ => trivial, fun _ => (hadj _).2 ⟨_, List.mem_cons_self, hnX⟩⟩
    have g2 : M.adj u IcpX ↔ False := by
      refine ⟨fun h => ?_, False.elim⟩
      obtain ⟨w, hw, hXw⟩ := (hadj _).1 h
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl <;> exact hXold _ hXw
    have g3 : M.adj u (G.icpH x0 x0) ↔ True :=
      ⟨fun _ => trivial, fun _ => (hadj _).2 ⟨_, by simp, connect_refl _⟩⟩
    have g4 : M.adj u (G.icpH x0 (G.face (G.edge x0))) ↔ True :=
      ⟨fun _ => trivial, fun _ => (hadj _).2 ⟨_, by simp, connect_refl _⟩⟩
    have g5 : ∀ w ∈ c₃ ++ k, ¬ M.adj u (G.icpH x0 w) := by
      intro w hw h
      obtain ⟨v, hv, hwv⟩ := (hadj _).1 h
      simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact hs1 w hw ((G.cface_icpH x0 _ _).1 hwv)
      · exact hs2 w hw ((G.cface_icpH x0 _ _).1 hwv)
      · exact hs3 w hw ((G.cface_icpH x0 _ _).1 hwv)
    have e1 : (∃ y ∈ mask mr₀ c₃, M.adj u (G.icpH x0 y)) ↔ False :=
      ⟨fun ⟨y, hy, h⟩ => g5 y (List.mem_append_left _ (mem_of_mem_mask hy)) h, False.elim⟩
    have e2 : (∃ y ∈ mask mk₀ k, M.adj u (G.icpH x0 y)) ↔ False :=
      ⟨fun ⟨y, hy, h⟩ => g5 y (List.mem_append_right _ (mem_of_mem_mask hy)) h, False.elim⟩
    simp only [f1, f2, f3, g1, g2, g3, g4, e1, e2, Bool.or_eq_true, and_false, and_true,
      false_or, or_false]
    simp only [exists_false, or_false]
    cases b0 <;> cases b1' <;> cases b2 <;> simp

end Hypermap

/-- The ring of the base map is face-simple. -/
private theorem cpmap_simple_nil :
    (cpmap []).pointee.Simple ((cpmap []).pointee.cpring (cpmap []).pointer ++ cpker []) := by
  rw [cpker_nil, List.append_nil]
  show cpmap0.Simple (cpmap0.cpring true)
  rw [cpring0, simple_recI]
  refine ⟨?_, fun h => ?_, trivial⟩
  · rintro ⟨y, hy, hxy⟩
    rw [List.mem_singleton] at hy
    subst hy
    exact absurd ((cface_cpmap0 _ _).1 hxy) (by decide)
  · obtain ⟨y, hy, -⟩ := h
    simp at hy

/-- `cpmap_simple`, extended to the empty program. -/
private theorem cpmap_simple' {cp : Cprog} (h : cp = [] ∨ configProg cp) :
    (cpmap cp).pointee.Simple ((cpmap cp).pointee.cpring (cpmap cp).pointer ++ cpker cp) := by
  rcases h with rfl | h
  · exact cpmap_simple_nil
  · exact cpmap_simple h

/-- math-comp `cpmask_adj`: for a configuration program `cp` and a proper face mask `cm`,
`cpadj cm cp` selects exactly the faces adjacent to the faces selected by `cm`. -/
theorem cpmask_adj {cp : Cprog} (h : configProg cp) {cm : Cfmask} (hm : ProperCpmask cp cm)
    (u : (cpmap cp).D) :
    u ∈ (cpmap cp).pointee.fband (cpmask (cpadj cm cp) cp) ↔
      ∃ y ∈ cpmask cm cp, (cpmap cp).pointee.adj u y := by
  suffices key : ∀ cp : Cprog, (cp = [] ∨ configProg cp) → ∀ cm : Cfmask, ProperCpmask cp cm →
      ∀ u : (cpmap cp).D, u ∈ (cpmap cp).pointee.fband (cpmask (cpadj cm cp) cp) ↔
        ∃ y ∈ cpmask cm cp, (cpmap cp).pointee.adj u y from key cp (Or.inr h) cm hm u
  intro cp
  induction cp with
  | nil =>
    rintro - ⟨mr, mk⟩ ⟨hr, hk⟩ u
    simp only [cprsize, cpksize, List.countP_nil] at hr hk
    match mr, mk, hr, hk with
    | [b0, b1], [], _, _ =>
      revert u
      show ∀ u : Bool,
        u ∈ cpmap0.fband (mask [b1, b0] (cpmap0.cpring true) ++ mask [] ([] : List Bool)) ↔
          ∃ y ∈ mask [b0, b1] (cpmap0.cpring true) ++ mask [] ([] : List Bool), cpmap0.adj u y
      intro u
      rw [cpring0]
      simp only [Hypermap.mem_fband, cface_cpmap0, adj_cpmap0]
      cases b0 <;> cases b1 <;> cases u <;> simp
  | cons s cp ih =>
    rintro hcp ⟨mr, mk⟩ ⟨hr, hk⟩
    have hcp' : configProg (s :: cp) := hcp.resolve_left (List.cons_ne_nil _ _)
    set G := (cpmap cp).pointee with hG
    set x0 := (cpmap cp).pointer with hx0
    cases s with
    | R n =>
      have h1 : cp = [] ∨ configProg cp := Or.inr hcp'
      have hm1 : ProperCpmask cp ⟨rotr n mr, mk⟩ :=
        ⟨by simpa [cprsize] using hr, by simpa [cpksize, isCpH] using hk⟩
      have hp1 := cpadj_proper cp _ hm1
      have ihu := ih h1 _ hm1
      generalize hq : cpadj ⟨rotr n mr, mk⟩ cp = cm1 at hp1 ihu
      obtain ⟨mr', mk'⟩ := cm1
      have hadj : cpadj ⟨mr, mk⟩ (.R n :: cp) = ⟨rot n mr', mk'⟩ := by
        simp only [cpadj, hq]
      rw [hadj]
      unfold cpmask at ihu ⊢
      show ∀ u : (cpmap cp).D,
        u ∈ G.fband (mask (rot n mr') ((G.ecpR n x0).pointee.cpring (G.ecpR n x0).pointer) ++
          mask mk' (cpker cp)) ↔
        ∃ y ∈ mask mr ((G.ecpR n x0).pointee.cpring (G.ecpR n x0).pointer) ++ mask mk (cpker cp),
          G.adj u y
      intro u
      rw [cpring_ecpR]
      have hc : mr'.length = (G.cpring x0).length := by rw [size_ring_cpmap]; exact hp1.1
      have hc' : (rotr n mr).length = (G.cpring x0).length := by
        rw [length_rotr, size_ring_cpmap]; exact hr
      have e1 : ∀ w, w ∈ mask (rot n mr') (rot n (G.cpring x0)) ++ mask mk' (cpker cp) ↔
          w ∈ mask mr' (G.cpring x0) ++ mask mk' (cpker cp) := by
        intro w
        rw [List.mem_append, List.mem_append, mem_mask_rot hc]
      have e2 : ∀ w, w ∈ mask mr (rot n (G.cpring x0)) ++ mask mk (cpker cp) ↔
          w ∈ mask (rotr n mr) (G.cpring x0) ++ mask mk (cpker cp) := by
        intro w
        rw [show mask mr (rot n (G.cpring x0)) = mask (rot n (rotr n mr)) (rot n (G.cpring x0)) by
          rw [rot_rotr], List.mem_append, List.mem_append, mem_mask_rot hc']
      have ihu' := ihu u
      simp only [Hypermap.mem_fband] at ihu' ⊢
      simp only [e1, e2]
      exact ihu'
    | Y =>
      have h1 : cp = [] ∨ configProg cp := by
        cases cp with
        | nil => left; rfl
        | cons s' cp' => right; exact hcp'
      have hcub : cubicProg cp := by
        rcases h1 with rfl | h1
        · rfl
        · exact config_prog_cubic h1
      have hp := cpmap_proper hcub
      have hplain := cpmap_plain hcub
      have hs := cpmap_simple' h1
      have hlen : mr.length = (G.cpring x0).length + 1 := by rw [size_ring_cpmap]; exact hr
      have h2 := (G.size_proper_cpring x0).1 hp
      rcases mr with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, mr₀⟩⟩⟩
      · simp only [List.length_nil] at hlen; omega
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      have hm1 : ProperCpmask cp ⟨b0 :: b2 :: mr₀, mk⟩ :=
        ⟨by simp only [cprsize, List.length_cons] at hr ⊢; omega,
          by simpa [cpksize, isCpH] using hk⟩
      have hp1 := cpadj_proper cp _ hm1
      have IH := fun x => ih h1 _ hm1 x
      generalize hq : cpadj ⟨b0 :: b2 :: mr₀, mk⟩ cp = cm1 at hp1 IH
      obtain ⟨mr', mk'⟩ := cm1
      have hlen' : mr'.length = (G.cpring x0).length := by rw [size_ring_cpmap]; exact hp1.1
      rcases mr' with _ | ⟨a0, _ | ⟨a2, mr'⟩⟩
      · simp only [List.length_nil] at hlen'; omega
      · simp only [List.length_cons, List.length_nil] at hlen'; omega
      have hadj : cpadj ⟨b0 :: b1 :: b2 :: mr₀, mk⟩ (.Y :: cp) =
          ⟨(a0 || b1) :: (b0 || b2) :: (a2 || b1) :: mr', mk'⟩ := by
        simp only [cpadj, hq]
      rw [hadj]
      unfold cpmask at IH ⊢
      exact G.cpmask_adj_ecpY x0 hplain hp (cpker cp) hs IH
    | H =>
      have h1 : configProg cp := hcp'
      have hcub := config_prog_cubic h1
      have hp := cpmap_proper hcub
      have hl := cfmap_long h1
      have hplain := cpmap_plain hcub
      have hs := cpmap_simple h1
      have hlen : mr.length = (G.cpring x0).length := by rw [size_ring_cpmap]; exact hr
      have h3 := (G.size_long_cpring x0).1 hl
      have hklen : mk.length = (cpker cp).length + 1 := by
        rw [size_cpker h1]
        simpa [cpksize, isCpH, List.countP_cons] using hk
      rcases mk with _ | ⟨b1', mk₀⟩
      · simp only [List.length_nil] at hklen; omega
      rcases mr with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, mr₀⟩⟩⟩
      · simp only [List.length_nil] at hlen; omega
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      have hm1 : ProperCpmask cp ⟨b0 :: b1' :: b2 :: mr₀, mk₀⟩ :=
        ⟨by simpa [cprsize] using hr,
          by simp only [List.length_cons] at hklen ⊢; rw [← size_cpker h1]; omega⟩
      have hp1 := cpadj_proper cp _ hm1
      have IH := fun x => ih (Or.inr h1) _ hm1 x
      generalize hq : cpadj ⟨b0 :: b1' :: b2 :: mr₀, mk₀⟩ cp = cm1 at hp1 IH
      obtain ⟨mr', mk'⟩ := cm1
      have hlen' : mr'.length = (G.cpring x0).length := by rw [size_ring_cpmap]; exact hp1.1
      rcases mr' with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, mr'⟩⟩⟩
      · simp only [List.length_nil] at hlen'; omega
      · simp only [List.length_cons, List.length_nil] at hlen'; omega
      · simp only [List.length_cons, List.length_nil] at hlen'; omega
      have hadj : cpadj ⟨b0 :: b1 :: b2 :: mr₀, b1' :: mk₀⟩ (.H :: cp) =
          ⟨(a0 || b1) :: (b0 || (b1' || b2)) :: (a2 || b1) :: mr', (a1 || b1) :: mk'⟩ := by
        simp only [cpadj, hq, List.headD]
      rw [hadj]
      unfold cpmask at IH ⊢
      rw [cpker_H hp]
      exact G.cpmask_adj_ecpH x0 hplain hp hl (cpker cp) hs IH
    | _ => simp [configProg] at hcp'

end FourColor
