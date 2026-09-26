/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Birkhoff.Check
import FourColor.Revsnip
import FourColor.Engine.SuccSpec

/-!
# The Birkhoff theorem (port of `birkhoff.v`, section `Birkhoff`, subsection `BirkhoffValid`,
and the theorem `Birkhoff`)

For a minimal counter-example `G` (`cexG : G.MinimalCounterExample`):

* `G.birkhoff_basis_trace` : for a nontrivial ring `r` of size `n + 1` (when the rings of size
  at most `n` are trivial), every basis program `cp` accepted by `birkhoffCheck1 n m` has a ring
  trace (in the orientation of `cpring`) that is also a ring trace of the disk map of `r`: the
  map obtained by sewing the disk of `r` to `cpmap cp` is smaller than `G`, hence colorable
  (math-comp local `chkbP` of `Birkhoff_valid`).
* `G.birkhoff_valid` : a successful Birkhoff check excludes `m`-nontrivial rings of size
  `n + 1` (math-comp `Birkhoff_valid`).
* `G.birkhoff` : a minimal counter-example has no nontrivial rings of size at most `5`, except
  rings of size `5` with a single face on one side (math-comp `Birkhoff`).

## Porting notes

* `Birkhoff_valid` is re-proved from the soundness of the engine's Birkhoff game,
  `Engine.bk2_false` (see `Engine/Birkhoff.lean`): the two sides of the game are the disk maps of
  `r`
  and of `revRing r`, `Pi t` says that `t` is not a ring trace of side `i`, `hR` is
  `ring_disk_closed`, `hglue` is `colorable_from_ring`, and `hb` is `chkbP`
  (`birkhoff_basis_trace`).  The `kempetree` bookkeeping of the Coq proof (`Kempe_valid_init`,
  `Kempe_valid_restrict`, `Kempe_tree_closure_correct`, `Kempe_validP`) is subsumed by the
  `SoundFor` invariant of `bk2_false`.
* In `chkbP`, the border of the remainder map `cpmap cp` is `rev (cpring Gr)` rather than Coq's
  `rotr 1 (rev (cpring Gr))`: with this choice the ring trace of the disk given by
  `colorable_patch` is exactly a ring trace of `cpring Gr` (the orientation in which the
  engine's coloring DP computes the basis coloring sets, `Engine.den_dpP1`), with no rotation.
* `nontrivial_ring m r = false` becomes `¬ G.NontrivialRing m r`; math-comp's
  `nat_of_bool (size r == 5)` is `(r.length == 5).toNat`.
-/

namespace FourColor

open Engine

universe u

/-! ### Component counts (helpers) -/

section NCompHelpers

variable {α : Type*} {e : α → α → Prop}

/-- `nComp` is monotone. -/
private theorem nComp_mono_set [Finite α] {a b : Set α} (h : a ⊆ b) : nComp e a ≤ nComp e b :=
  Set.ncard_le_ncard (Set.image_mono h) (Set.toFinite _)

/-- `nComp` is additive on a closed set and a disjoint set. -/
private theorem nComp_union_closed [Finite α] {a b : Set α} (ha : Closed e a)
    (hab : Disjoint a b) : nComp e (a ∪ b) = nComp e a + nComp e b := by
  rw [nComp, nComp, nComp, Set.image_union, Set.ncard_union_eq]
  rw [Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
  have hyx : connect e y x := by
    have : x ∈ comp e y := by rw [hxy]; exact connect_refl x
    exact this
  exact Set.disjoint_left.1 hab ((ha.connect_iff hyx).2 hx) hy

end NCompHelpers

namespace Hypermap

section BirkhoffValid

variable {D : Type u} [Fintype D] [DecidableEq D] {G : Hypermap D}

/-- math-comp local `chkbP` of `Birkhoff_valid`: if the rings of size at most `n` are trivial,
then for an `m`-nontrivial ring `r` of size `n + 1` and a basis program `cp` accepted by
`Birkhoff_check1`, some ring trace of `cpmap cp` (in the orientation of `cpring`) is a ring
trace of the disk map of `r`. -/
theorem birkhoff_basis_trace (cexG : G.MinimalCounterExample) {n : ℕ}
    (leq_n_trivial : ∀ r : List D, G.SCycle G.rlink r → r.length ≤ n → ¬ G.NontrivialRing 0 r)
    {m : ℕ} {r : List D} (hr : G.SCycle G.rlink r) (sz_r : r.length = n + 1)
    (nt_r : G.NontrivialRing m r) {cp : Cprog} (hcp : birkhoffCheck1 n m cp = true) :
    ∃ et, (G.snipDisk cexG.planar hr).RingTrace (G.snipdRing r) et ∧ RingTraces cp et := by
  simp only [birkhoffCheck1, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcp
  obtain ⟨cpQ, ltn_cp, szr_cp⟩ := hcp
  have hG := cexG.toPlanarBridgelessPlainConnected
  have hGp : G.Planar := cexG.planar
  -- the disk map of `r` and the remainder map
  have ppGd := G.snip_patch hGp hr
  have cycEbGd := G.scycle_snipd_ring hGp hr
  -- the configuration map, with the border `rev (cpring Gr)`
  set Gr := (cpmap cp).pointee with hGr
  set bGr := (Gr.cpring (cpmap cp).pointer).reverse with hbGr
  have cycNbGr : UCycle (frel Gr.node) bGr := Gr.ucycle_rev_cpring _
  have sz_bGd : (G.snipdRing r).length = r.length := by
    rw [← List.length_map (f := G.snipd r), G.map_snipd_ring]
  have sz_bG : (G.snipdRing r).length = bGr.length := by
    rw [sz_bGd, hbGr, List.length_reverse, size_ring_cpmap, szr_cp, sz_r]
  have ppG2 := sew_map_patch cycEbGd cycNbGr sz_bG
  obtain ⟨plainGd, plainGrr⟩ := ppGd.plain_patch.1 cexG.plain
  obtain ⟨cubicGd, cubicGrr⟩ := ppGd.cubic_patch.1 cexG.cubic
  have planarG2 : (sewMap cycEbGd cycNbGr sz_bG).Planar :=
    ppG2.planar_patch.2 ⟨G.planar_snipd hGp hr, cpmap_planar cpQ⟩
  have plainG2 : (sewMap cycEbGd cycNbGr sz_bG).Plain :=
    ppG2.plain_patch.2 ⟨plainGd, cpmap_plain cpQ⟩
  have cubicG2 : (sewMap cycEbGd cycNbGr sz_bG).Cubic :=
    ppG2.cubic_patch.2 ⟨cubicGd, cpmap_cubic cpQ⟩
  have bridge'G2 : (sewMap cycEbGd cycNbGr sz_bG).Bridgeless := by
    have bridge'Gd := (ppGd.patch_bridgeless cexG.bridgeless).1
    refine ppG2.bridgeless_patch bridge'Gd (cpmap_bridgeless cpQ) ?_
    by_contra chord_bGd
    obtain ⟨r1, Ur1, nt_r1, lt_r1r⟩ := G.ring_disk_chord hG hGp hr nt_r chord_bGd
    exact leq_n_trivial r1 Ur1 (by omega) nt_r1
  -- the size of the sewn map
  have ltG2 : Fintype.card (SewDart (G.SnipdDart r) bGr) < Fintype.card D := by
    have c1 := ppGd.card_patch
    have c2 := ppG2.card_patch
    simp only [List.length_map] at c1 c2
    have cGr : Fintype.card (cpmap cp).D = cpcard cp := card_cpmap cp
    -- the Euler formula for the remainder map of `r`
    have sz_bGrr : (G.sniprRing r).length = n + 1 := by
      rw [← List.length_map (f := G.snipr r), G.map_snipr_ring, List.length_reverse, sz_r]
    obtain ⟨x0, r0, rfl⟩ : ∃ x0 r0, r = x0 :: r0 := List.exists_cons_of_length_eq_add_one sz_r
    have geoGrr : (G.snipRem hGp hr).UCyclePlainQuasicubicConnected (G.sniprRing (x0 :: r0)) :=
      { plain := plainGrr
        quasicubic := cubicGrr
        ucycle := G.ucycle_snipr_ring hGp hr
        connected := ppGd.patch_connected_r cexG.connected
          ⟨x0, fun h => h.2 List.mem_cons_self⟩ }
    have hE := ((G.snipRem hGp hr).quasicubic_euler geoGrr).1 (G.planar_snipr hGp hr)
    have hne : G.sniprRing (x0 :: r0) ≠ [] := fun h => by
      rw [h] at sz_bGrr
      simp at sz_bGrr
    simp only [hne, ↓reduceIte] at hE
    rw [ppGd.patch_fcard_face_r, sz_bGrr] at hE
    -- the faces of the remainder map: the faces of the ring and those outside the ring
    have hF : (x0 :: r0).length + fcard G.face (G.diskFC (x0 :: r0)) ≤
        fcard G.face (G.outer (G.snipr (x0 :: r0))) := by
      rw [← G.scycle_fcard_fband hr, ← nComp_union_closed (G.fbandF _)]
      · apply nComp_mono_set
        rintro x (⟨y, ry, xFy⟩ | ⟨dN'x, _⟩)
        · exact ⟨y, (G.codom_snipr _ y).2 fun h => h.2 ry, xFy⟩
        · exact ⟨x, (G.codom_snipr _ x).2 fun h => dN'x h.1, connect_refl x⟩
      · rw [Set.disjoint_left]
        exact fun x hx hx' => hx'.2 hx
    have ntFC := nt_r.2
    simp only [List.length_cons] at hF sz_r
    omega
  -- the sewn map is colorable
  have colG2 : (sewMap cycEbGd cycNbGr sz_bG).FourColorable :=
    cexG.minimal _ _ ⟨⟨⟨planarG2, bridge'G2⟩, plainG2⟩, cubic_precubic _ cubicG2⟩ ltG2
  obtain ⟨et, Det_d, k, hk, Det_r⟩ := ppG2.colorable_patch.1 colG2
  refine ⟨et, Det_d, k, hk, ?_⟩
  rw [hbGr, List.map_reverse, trace_rev] at Det_r
  have := congrArg List.reverse (rot_inj 1 Det_r)
  rwa [List.reverse_reverse, List.reverse_reverse] at this

/-- The basis coloring sets of a successful check meet the ring traces of the disk map of a
nontrivial ring (the hypothesis `hb` of `Engine.bk2_false`, from `chkbP`). -/
theorem birkhoff_basis_den (cexG : G.MinimalCounterExample) {n : ℕ}
    (leq_n_trivial : ∀ r : List D, G.SCycle G.rlink r → r.length ≤ n → ¬ G.NontrivialRing 0 r)
    {m : ℕ} {r : List D} (hr : G.SCycle G.rlink r) (sz_r : r.length = n + 1)
    (nt_r : G.NontrivialRing m r) (hn : 1 ≤ n) {cnv : Net} (hcnv : CnvSpec (n + 1) cnv)
    {cps : List Cprog} (hcps : cps.all (birkhoffCheck1 n m) = true) :
    ∀ B ∈ cps.map (dpP1 (n + 1) cnv), ∃ t, den (n + 1) B t ∧
      (G.snipDisk cexG.planar hr).RingTrace (G.snipdRing r) t := by
  intro B hB
  obtain ⟨cp, hcp, rfl⟩ := List.mem_map.1 hB
  have hcp1 := List.all_eq_true.1 hcps cp hcp
  obtain ⟨et, het, hcpet⟩ := G.birkhoff_basis_trace cexG leq_n_trivial hr sz_r nt_r hcp1
  have szr_cp : cprsize cp = n + 1 := by
    simp only [birkhoffCheck1, Bool.and_eq_true, beq_iff_eq] at hcp1
    exact hcp1.2.2
  have reach := (ringTraces_iff_cpReach cp et).1 hcpet
  obtain ⟨hl, h0, hs⟩ := cpReach_valid reach
  refine ⟨et, (den_dpP1 hcnv szr_cp (by omega)).2 ⟨⟨by rw [hl, szr_cp], h0, hs⟩, reach⟩, het⟩

/-- math-comp `Birkhoff_valid`: if all the rings of size at most `n` are trivial, a successful
Birkhoff check `BirkhoffCheck n m` excludes the `m`-nontrivial rings of size `n + 1` in a minimal
counter-example. -/
theorem birkhoff_valid (cexG : G.MinimalCounterExample) {n : ℕ}
    (leq_n_trivial : ∀ r : List D, G.SCycle G.rlink r → r.length ≤ n → ¬ G.NontrivialRing 0 r)
    {m : ℕ} {r : List D} (hbk : BirkhoffCheck n m) (hr : G.SCycle G.rlink r)
    (sz_r : r.length = n + 1) : ¬ G.NontrivialRing m r := by
  intro nt_r
  have hG := cexG.toPlanarBridgelessPlainConnected
  have hGp : G.Planar := cexG.planar
  obtain ⟨niter, fuel, cps, tau, cnv, rv, htau, hcnv, hrv, hcps, hbk⟩ := hbk
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · -- a ring of size 1 would be a bridge
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 sz_r
    exact G.bridgeless_cface hG.bridgeless x (G.cfaceC.1 hr.1.1)
  -- the two sides: the disk maps of `r` and of `revRing r`
  have hr2 := G.scycle_rev_ring hG hr
  have nt_r2 := G.nontrivial_rev_ring hG hr nt_r
  have sz_r2 : (G.revRing r).length = n + 1 := by
    rw [revRing, List.length_reverse, List.length_map, sz_r]
  let P1 : Colseq → Prop := fun t => ¬ (G.snipDisk hGp hr).RingTrace (G.snipdRing r) t
  let P2 : Colseq → Prop := fun t =>
    ¬ (G.snipDisk hGp hr2).RingTrace (G.snipdRing (G.revRing r)) t
  have hR1 : KempeClosed fun t => ¬ P1 t := by
    simpa only [P1, not_not] using G.ring_disk_closed hG hGp hr nt_r cexG.cubic
  have hR2 : KempeClosed fun t => ¬ P2 t := by
    simpa only [P2, not_not] using G.ring_disk_closed hG hGp hr2 nt_r2 cexG.cubic
  have hglue : ∀ t, ValidTrace (n + 1) t → P1 t ∨ P2 t.reverse := by
    intro t _
    by_cases h1 : (G.snipDisk hGp hr).RingTrace (G.snipdRing r) t
    · exact Or.inr fun h2 => cexG.noncolorable (G.colorable_from_ring hG hGp hr nt_r h1 h2)
    · exact Or.inl h1
  have hb1 : ∀ B ∈ cps.map (dpP1 (n + 1) cnv), ∃ t, den (n + 1) B t ∧ ¬ P1 t := by
    intro B hB
    obtain ⟨t, ht, htr⟩ :=
      G.birkhoff_basis_den cexG leq_n_trivial hr sz_r nt_r hn hcnv hcps B hB
    exact ⟨t, ht, not_not.2 htr⟩
  have hb2 : ∀ B ∈ cps.map (dpP1 (n + 1) cnv), ∃ t, den (n + 1) B t ∧ ¬ P2 t := by
    intro B hB
    obtain ⟨t, ht, htr⟩ :=
      G.birkhoff_basis_den cexG leq_n_trivial hr2 sz_r2 nt_r2 hn hcnv hcps B hB
    exact ⟨t, ht, not_not.2 htr⟩
  have hfalse := bk2_false (fuel := fuel) htau hrv (fun _ ht => validTrace_reverse ht)
    (fun t _ => List.reverse_reverse t) P1 P2 hR1 hR2 hglue hb1 hb2 niter
    (emptySet (n + 1)) (emptySet (n + 1)) (soundFor_emptySet _ _) (soundFor_emptySet _ _)
  rw [birkhoffCheck, hfalse] at hbk
  exact Bool.false_ne_true hbk

open BirkhoffCheckLemmas in
/-- math-comp `Birkhoff`: a minimal counter-example has no nontrivial rings of size at most
`5`, except rings of size `5` with a single face on one side (math-comp's
`nontrivial_ring (size r == 5) r = false`). -/
theorem birkhoff (cexG : G.MinimalCounterExample) {r : List D} (hr5 : r.length ≤ 5)
    (hr : G.SCycle G.rlink r) : ¬ G.NontrivialRing (r.length == 5).toNat r := by
  have hG := cexG.toPlanarBridgelessPlainConnected
  suffices h : ∀ n, n ≤ 5 → ∀ r : List D, r.length ≤ n → G.SCycle G.rlink r →
      ¬ G.NontrivialRing (r.length == 5).toNat r from h 5 le_rfl r hr5 hr
  intro n
  induction n with
  | zero =>
    intro _ r hr0 _ nt_r
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hr0)] at nt_r
    have h0 : G.diskF [] = ∅ := by
      ext y
      simp [diskF, diskN]
    have := nt_r.1
    simp [h0] at this
  | succ n IHn =>
    intro n_lt5 r sz_r Ur
    rcases Nat.lt_or_eq_of_le sz_r with sz_r | sz_r
    · exact IHn (by omega) r (by omega) Ur
    have leq_n_trivial : ∀ r : List D, G.SCycle G.rlink r → r.length ≤ n →
        ¬ G.NontrivialRing 0 r := by
      intro r' Ur' r'_le_n
      have h := IHn (by omega) r' r'_le_n Ur'
      rwa [show (r'.length == 5).toNat = 0 by
        rw [show (r'.length == 5) = false by simp only [beq_eq_false_iff_ne]; omega]; rfl] at h
    rw [sz_r]
    rcases n with _ | _ | _ | _ | _ | n
    · intro nt_r
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 sz_r
      exact G.bridgeless_cface hG.bridgeless x (G.cfaceC.1 Ur.1.1)
    · exact G.birkhoff_valid cexG leq_n_trivial birkhoff2 Ur sz_r
    · exact G.birkhoff_valid cexG leq_n_trivial birkhoff3 Ur sz_r
    · exact G.birkhoff_valid cexG leq_n_trivial birkhoff4 Ur sz_r
    · exact G.birkhoff_valid cexG leq_n_trivial birkhoff5 Ur sz_r
    · omega

end BirkhoffValid

end Hypermap

end FourColor
