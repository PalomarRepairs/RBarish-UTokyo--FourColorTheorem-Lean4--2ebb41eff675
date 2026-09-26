/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.RealPlane
import FourColor.Approx
import Mathlib.Logic.Encodable.Basic
import Mathlib.Data.Fintype.Card

/-!
# Compactness extension  (port of `finitize.v`)

We use a special case of the compactness theorem for predicate logic to extend the Four Color
Theorem from finite to arbitrary maps. We can dispense with the full axiom of choice as maps
have only countably many regions because of the local compactness of the plane (in Lean we use
`Classical` freely anyway).

Given a natural integer `nc` such that all finite maps are `nc`-colorable and a (possibly
infinite) simple plane map `m0`, we construct an `nc`-coloring of `m0` by defining:

* `EqMap m1 m2`        : maps `m1` and `m2` coincide (relate the same points) (Coq `eq_map`).
* `stdPoint i`         : the `i`-th scaled grid point, in a standard fixed enumeration
  (Coq `std_point i`, notation `'z_i`).
* `finColorMap n g`    : the (plain) map whose (at most) `n` regions are the preimages by
  `g : Point → ℝ` of the integers `i`, `0 ≤ i < n` (Coq `fin_color_map`).
* `inPmap m0 n`        : the union of the regions of `m0` containing one of the first `n` scaled
  grid points (Coq `in_pmap n`).
* `pmap m0 n k`        : the restriction of the map `k` to `inPmap m0 n` (Coq `pmap n k`).
* `EqPmap m0 n k1 k2`  : maps `k1` and `k2` coincide on `inPmap m0 n` (Coq `eq_pmap`).
* `SubColoring nc m0 k` : `k` is an `nc`-coloring consistent with `m0`, i.e. `k` does not relate
  points in adjacent regions of `m0` (Coq `subcoloring`).
* `PColoring nc m0 n k` : `k` is a subcoloring covering at least `inPmap m0 n`
  (Coq `pcoloring`).
* `Extensible nc m0 n k` : the coloring of `inPmap m0 n` induced by `k` extends to
  `nc`-colorings of `inPmap m0 n'` for any `n'` (Coq `extensible`).
* `Minimal nc m0 n k`  : the lexicographic minimality property of a prefix coloring
  (Coq section `Let minimal`; public here so that `PrefixColoring` unfolds in other files).
* `PrefixColoring nc m0 n k` : `k` is an extensible, minimal coloring of `pmap m0 n m0`
  (Coq `prefix_coloring`).
* `IsPrefix nc m0 k`   : `k` is a prefix coloring for some `n` (Coq `is_prefix`).
* `limitColoring nc m0` : the union of the inclusion chain of prefix colorings, which we show is
  an `nc`-coloring of `m0` (Coq `limit_coloring`).

## Translation notes

* Coq's section variables `nc`, `m0` become explicit arguments of the definitions and implicit
  arguments of the lemmas; the hypotheses `fin_colorable` and `m0P` are explicit arguments of
  the lemmas that use them.
* Coq's classical helpers `Rclassic`, `RcontraR`, `Rwlog` are Lean's `Classical` logic
  (`by_contra`, `by_cases`).
* Coq's `[map z1 z2 | E]` is `fun z1 z2 => E`; `implies A B` is `A → B`; `exists2 x, P & Q`
  is `∃ x, P ∧ Q`; `[/\ A, B & C]` is `A ∧ B ∧ C`; `maxn` is `max`; `std_point` uses
  Mathlib's
  `Encodable` enumeration of `ℕ × GPoint` instead of math-comp's `unpickle` (only its
  surjectivity, `Encodable.encodek`, is used).
* `fin_color_map` uses `g z = g t ∧ g t = i` for Coq's setoid `g z == g t == i%:R`.
* Several proofs are restructured (direct constructions instead of inductions for
  `at_most_regionsP` and `size_pmap`, `Nat.find` instead of the downward induction on `j0` in
  `prefix_coloring_exists`, and a pigeonhole on `Fin` in `size_limit_coloring`); the statements
  are the Coq ones.
* The final statement `compactness_extension` is specialised to `nc = 4`, the case that
  `fourcolor.v` uses; the Coq statement for an arbitrary `nc` is `compactness_extension_with`.
-/

namespace FourColor.RealPlane

open Classical

/-! ### Derived map transitivity and equivalence lemmas -/

namespace PlainMap

variable {m : Map}

/-- Coq `map_transl`. -/
theorem map_transl (mP : PlainMap m) {z1 z2 : Point} (h : m z1 z2) (z : Point) :
    m z1 z ↔ m z2 z :=
  ⟨fun h1 => mP.map_trans (mP.map_sym h) z h1, fun h2 => mP.map_trans h z h2⟩

/-- Coq `map_transr`. -/
theorem map_transr (mP : PlainMap m) {z1 z2 : Point} (h : m z1 z2) (z : Point) :
    m z z1 ↔ m z z2 :=
  ⟨fun h1 => mP.map_sym ((mP.map_transl h z).1 (mP.map_sym h1)),
   fun h2 => mP.map_sym ((mP.map_transl h z).2 (mP.map_sym h2))⟩

/-- Coq `map_cover`. -/
theorem map_cover (mP : PlainMap m) {z1 z2 : Point} (h : m z1 z2) :
    cover m z1 ∧ cover m z2 :=
  ⟨(mP.map_transr h z1).2 h, (mP.map_transl h z2).1 h⟩

/-- Transitivity of a plain map, in the usual order (a consequence of Coq `map_trans`). -/
theorem trans' (mP : PlainMap m) {z1 z2 z3 : Point} (h12 : m z1 z2) (h23 : m z2 z3) :
    m z1 z3 :=
  mP.map_trans h12 z3 h23

end PlainMap

/-! ### A canonical enumeration of grid points -/

/-- Coq `std_point i` (notation `'z_i`): the `i`-th scaled grid point, in the `Encodable`
enumeration of `ℕ × GPoint`. -/
noncomputable def stdPoint (i : ℕ) : Point :=
  let sp : ℕ × GPoint := (Encodable.decode (α := ℕ × GPoint) i).getD (0, ⟨0, 0⟩)
  scalePoint sp.1 sp.2

/-- The enumeration `stdPoint` reaches every scaled grid point (Coq `pickleK` step). -/
theorem stdPoint_encode (s : ℕ) (p : GPoint) :
    stdPoint (Encodable.encode (s, p)) = scalePoint s p := by
  simp [stdPoint, Encodable.encodek]

/-! ### Finite maps as color maps -/

/-- Coq `eq_map`: the maps `m1` and `m2` relate the same points. -/
def EqMap (m1 m2 : Map) : Prop :=
  ∀ z t : Point, m1 z t ↔ m2 z t

/-- Coq `fin_color_map n g`: the map whose regions are the preimages by `g` of the integers
`i < n`. -/
def finColorMap (n : ℕ) (g : Point → ℝ) : Map :=
  fun z t => ∃ i : ℕ, i < n ∧ g z = g t ∧ g t = (i : ℝ)

/-- Coq `at_most_regionsP`: an alternative characterization of `AtMostRegions` (not used in the
rest of the proof). -/
theorem at_most_regionsP (n : ℕ) (m : Map) :
    PlainMap m ∧ AtMostRegions n m ↔ ∃ g : Point → ℝ, EqMap m (finColorMap n g) := by
  constructor
  · rintro ⟨mP, f, fP⟩
    let P : Point → ℕ → Prop := fun z i => i < n ∧ m (f i) z
    let g : Point → ℝ := fun z =>
      if h : cover m z then (Nat.find (p := P z) (by
        obtain ⟨i, hi, hfi⟩ := fP z h; exact ⟨i, hi, hfi⟩) : ℝ) else (n : ℝ)
    refine ⟨g, fun z t => ⟨fun mzt => ?_, ?_⟩⟩
    · obtain ⟨cz, ct⟩ := mP.map_cover mzt
      have hPzt : ∀ i, P z i ↔ P t i := fun i =>
        and_congr Iff.rfl (mP.map_transr mzt (f i))
      have hz : ∃ i, P z i := by obtain ⟨i, hi, hfi⟩ := fP z cz; exact ⟨i, hi, hfi⟩
      have ht : ∃ i, P t i := by obtain ⟨i, hi, hfi⟩ := fP t ct; exact ⟨i, hi, hfi⟩
      have eq : Nat.find hz = Nat.find ht :=
        le_antisymm (Nat.find_min' hz ((hPzt _).2 (Nat.find_spec ht)))
          (Nat.find_min' ht ((hPzt _).1 (Nat.find_spec hz)))
      refine ⟨Nat.find ht, (Nat.find_spec ht).1, ?_, ?_⟩
      · simp only [g, cz, ct, eq, ↓reduceDIte]
      · simp only [g, ct, ↓reduceDIte]
    · rintro ⟨i, hi, hzt, hti⟩
      have cov : ∀ w, g w = (i : ℝ) → ∃ h : cover m w, True := by
        intro w hw
        by_cases h : cover m w
        · exact ⟨h, trivial⟩
        · simp only [g, h, Nat.cast_inj, ↓reduceDIte] at hw
          omega
      obtain ⟨ct, -⟩ := cov t hti
      obtain ⟨cz, -⟩ := cov z (hzt.trans hti)
      have ht : ∃ i, P t i := by obtain ⟨i, hi, hfi⟩ := fP t ct; exact ⟨i, hi, hfi⟩
      have hz : ∃ i, P z i := by obtain ⟨i, hi, hfi⟩ := fP z cz; exact ⟨i, hi, hfi⟩
      have gt : g t = (Nat.find ht : ℝ) := by simp only [g, ct, ↓reduceDIte]
      have gz : g z = (Nat.find hz : ℝ) := by simp only [g, cz, ↓reduceDIte]
      have eq : Nat.find hz = Nat.find ht := by
        rw [gz, gt] at hzt; exact_mod_cast hzt
      have h1 := (Nat.find_spec hz).2
      have h2 := (Nat.find_spec ht).2
      rw [eq] at h1
      exact mP.map_trans (mP.map_sym h1) t h2
  · rintro ⟨g, gP⟩
    have mP : PlainMap m := by
      constructor
      · intro z1 z2 h
        obtain ⟨i, hi, h12, h2i⟩ := (gP z1 z2).1 h
        exact (gP z2 z1).2 ⟨i, hi, h12.symm, h12.trans h2i⟩
      · intro z1 z2 h12 z h2
        obtain ⟨i, hi, e12, -⟩ := (gP z1 z2).1 h12
        obtain ⟨j, hj, e2, ej⟩ := (gP z2 z).1 h2
        exact (gP z1 z).2 ⟨j, hj, e12.trans e2, ej⟩
    refine ⟨mP, fun i => if h : ∃ z, g z = (i : ℝ) then Classical.choose h else stdPoint 0,
      fun z hz => ?_⟩
    obtain ⟨i, hi, -, hzi⟩ := (gP z z).1 hz
    have h : ∃ z, g z = (i : ℝ) := ⟨z, hzi⟩
    refine ⟨i, hi, ?_⟩
    simp only [h, ↓reduceDIte]
    exact (gP _ z).2 ⟨i, hi, (Classical.choose_spec h).trans hzi.symm, hzi⟩

/-! ### The limit construction -/

section FinitizeMap

variable (nc : ℕ) (m0 : Map)

/-- Coq `in_pmap n`: the union of the regions of `m0` containing one of the first `n` scaled
grid points. -/
def inPmap (n : ℕ) : Region :=
  fun z => ∃ i, i < n ∧ m0 z (stdPoint i)

/-- Coq `pmap n m`: the restriction of the map `m` to `inPmap m0 n`. -/
def pmap (n : ℕ) (m : Map) : Map :=
  fun z1 z2 => inPmap m0 n z1 ∧ inPmap m0 n z2 ∧ m z1 z2

/-- Coq `eq_pmap n k k'`: the maps `k` and `k'` coincide on `inPmap m0 n`. -/
def EqPmap (n : ℕ) (k k' : Map) : Prop :=
  ∀ z1 z2, inPmap m0 n z1 → inPmap m0 n z2 → (k z1 z2 ↔ k' z1 z2)

/-- Coq `subcoloring k`: `k` is an `nc`-coloring consistent with `m0`. -/
structure SubColoring (k : Map) : Prop extends PlainMap k where
  /-- Coq `subcoloring_adj`. -/
  subcoloring_adj : ∀ z1 z2, Adjacent m0 z1 z2 → ¬ k z1 z2
  /-- Coq `subcoloring_size`. -/
  subcoloring_size : AtMostRegions nc k

/-- Coq `pcoloring n k`: `k` is a subcoloring covering at least `inPmap m0 n`. -/
def PColoring (n : ℕ) (k : Map) : Prop :=
  SubColoring nc m0 k ∧ Submap (pmap m0 n m0) k

/-- Coq `extensible n0 k0`: the coloring of `inPmap m0 n0` induced by `k0` extends to
`nc`-colorings of `inPmap m0 n` for any `n`. -/
def Extensible (n0 : ℕ) (k0 : Map) : Prop :=
  ∀ n, ∃ k, PColoring nc m0 n k ∧ EqPmap m0 n0 k0 k

/-- Coq section `Let minimal n k0`: the lexicographic minimality property of a prefix
coloring. -/
def Minimal (n : ℕ) (k0 : Map) : Prop :=
  ∀ i j k, i < n → EqPmap m0 i k0 k → pmap m0 (i + 1) k (stdPoint j) (stdPoint i) →
    Extensible nc m0 (i + 1) k → ∃ j0, j0 ≤ j ∧ k0 (stdPoint j0) (stdPoint i)

/-- Coq `prefix_coloring n k`: `k` is an extensible coloring of `pmap m0 n m0` that assigns a
lexicographically minimal sequence of colors to the first `n` scaled grid points. -/
def PrefixColoring (n : ℕ) (k : Map) : Prop :=
  Submap k (pmap m0 n k) ∧ Extensible nc m0 n k ∧ Minimal nc m0 n k

/-- Coq `is_prefix k`: `k` is a prefix coloring for some `n`. -/
def IsPrefix (k : Map) : Prop :=
  ∃ n, PrefixColoring nc m0 n k

/-- Coq `limit_coloring`: the union of the inclusion chain of prefix colorings. -/
def limitColoring : Map :=
  fun z1 z2 => ∃ k, IsPrefix nc m0 k ∧ k z1 z2

variable {nc m0}

/-! #### Standard point properties -/

/-- Coq `has_std_point`. -/
theorem has_std_point (m0P : SimpleMap m0) {z : Point} (m0z : cover m0 z) :
    ∃ i, m0 z (stdPoint i) := by
  obtain ⟨rr, rrz, m0rr⟩ := m0P.simple_map_open z z m0z
  obtain ⟨b, ⟨p, hp, pin⟩, rr_b⟩ := approx_rect rrz
  refine ⟨Encodable.encode (b.1, p), ?_⟩
  rw [stdPoint_encode]
  exact m0rr _ (rr_b _ ((mem_approx_scale b.1 _ p).2 (insetW b.2 p pin)))

/-- Coq `pmap_std`. -/
theorem pmap_std (m0P : SimpleMap m0) {n1 n2 i : ℕ} (lt_i_n1 : i < n1)
    (h : inPmap m0 n2 (stdPoint i)) : inPmap m0 n1 (stdPoint i) := by
  obtain ⟨_, _, m0zi⟩ := h
  exact ⟨i, lt_i_n1, (m0P.map_cover m0zi).1⟩

/-! #### Partial map cover properties -/

/-- Coq `in_pmap_le`. -/
theorem in_pmap_le {n1 n2 : ℕ} (le_n12 : n1 ≤ n2) : Subregion (inPmap m0 n1) (inPmap m0 n2) :=
  fun _ ⟨i, hi, hz⟩ => ⟨i, lt_of_lt_of_le hi le_n12, hz⟩

/-- Coq `in_pmap_trans`. -/
theorem in_pmap_trans (m0P : SimpleMap m0) {n : ℕ} {z : Point} (h : inPmap m0 n z) :
    Subregion (m0 z) (inPmap m0 n) := by
  obtain ⟨i, ltin, m0zi⟩ := h
  exact fun t m0zt => ⟨i, ltin, (m0P.map_transl m0zt _).1 m0zi⟩

/-- Coq `cover_pmap`. -/
theorem cover_pmap (m0P : SimpleMap m0) (n : ℕ) (z : Point) :
    cover (pmap m0 n m0) z ↔ inPmap m0 n z := by
  refine ⟨fun h => h.1, fun n_z => ⟨n_z, n_z, ?_⟩⟩
  obtain ⟨_, _, m0zi⟩ := n_z
  exact (m0P.map_cover m0zi).1

/-- Coq `in_pmapP`. -/
theorem in_pmapP (m0P : SimpleMap m0) {n : ℕ} {z : Point} (n_z : inPmap m0 n z) :
    ∃ i, i < n ∧ pmap m0 n m0 z (stdPoint i) := by
  obtain ⟨i, lt_i_n, m0zi⟩ := n_z
  exact ⟨i, lt_i_n, ⟨i, lt_i_n, m0zi⟩, in_pmap_trans m0P ⟨i, lt_i_n, m0zi⟩ _ m0zi, m0zi⟩

/-! #### Partial map equality -/

/-- Coq `eq_pmap_sym`. -/
theorem eq_pmap_sym {n : ℕ} {k k' : Map} (h : EqPmap m0 n k k') : EqPmap m0 n k' k :=
  fun z1 z2 h1 h2 => (h z1 z2 h1 h2).symm

/-- Coq `eq_pmap_trans`. -/
theorem eq_pmap_trans {n : ℕ} {k1 k2 k3 : Map} (h12 : EqPmap m0 n k1 k2)
    (h23 : EqPmap m0 n k2 k3) : EqPmap m0 n k1 k3 :=
  fun z1 z2 h1 h2 => (h12 z1 z2 h1 h2).trans (h23 z1 z2 h1 h2)

/-- Coq `eq_map_pmap`. -/
theorem eq_map_pmap (n : ℕ) (k : Map) : EqPmap m0 n k (pmap m0 n k) :=
  fun _ _ h1 h2 => ⟨fun h => ⟨h1, h2, h⟩, fun h => h.2.2⟩

/-- Coq `sub_pmap_pmap`. -/
theorem sub_pmap_pmap (n : ℕ) (k : Map) : Submap (pmap m0 n k) (pmap m0 n (pmap m0 n k)) :=
  fun _ _ h => ⟨h.1, h.2.1, h⟩

/-- Coq `eq_pmap_le`. -/
theorem eq_pmap_le {n1 n2 : ℕ} {k k' : Map} (le_n12 : n1 ≤ n2) (h : EqPmap m0 n2 k k') :
    EqPmap m0 n1 k k' :=
  fun z1 z2 h1 h2 => h z1 z2 (in_pmap_le le_n12 _ h1) (in_pmap_le le_n12 _ h2)

/-! #### Partial map properties -/

/-- Coq `pmap_sub`. -/
theorem pmap_sub (n : ℕ) (m : Map) : Submap (pmap m0 n m) m :=
  fun _ _ h => h.2.2

/-- Coq `pmap_le`. -/
theorem pmap_le {n1 n2 : ℕ} (le_n12 : n1 ≤ n2) (m : Map) :
    Submap (pmap m0 n1 m) (pmap m0 n2 m) :=
  fun _ _ h => ⟨in_pmap_le le_n12 _ h.1, in_pmap_le le_n12 _ h.2.1, h.2.2⟩

/-- Coq `pmap_plain`. -/
theorem pmap_plain (n : ℕ) {m : Map} (mP : PlainMap m) : PlainMap (pmap m0 n m) :=
  ⟨fun h => ⟨h.2.1, h.1, mP.map_sym h.2.2⟩,
   fun h12 _ h2 => ⟨h12.1, h2.2.1, mP.map_trans h12.2.2 _ h2.2.2⟩⟩

/-- Coq `pmap_finite`. -/
theorem pmap_finite (m0P : SimpleMap m0) (n : ℕ) : FiniteSimpleMap (pmap m0 n m0) where
  toPlainMap := pmap_plain n m0P.toPlainMap
  simple_map_open z := by
    rintro t ⟨n_z, -, m0zt⟩
    obtain ⟨r, r_t, m0_r⟩ := m0P.simple_map_open z t m0zt
    exact ⟨r, r_t, fun w rw => ⟨n_z, in_pmap_trans m0P n_z w (m0_r w rw), m0_r w rw⟩⟩
  simple_map_connected z := by
    rintro u v uP vP sub ⟨z1, u_z1, n_z, -, m0zz1⟩ ⟨z2, v_z2, -, -, m0zz2⟩
    refine m0P.simple_map_connected z u v uP vP (fun t m0zt => ?_) ⟨z1, u_z1, m0zz1⟩
      ⟨z2, v_z2, m0zz2⟩
    exact sub t ⟨n_z, in_pmap_trans m0P n_z t m0zt, m0zt⟩
  finite_simple_map_finite := by
    refine ⟨n, stdPoint, fun z ⟨n_z, _, _⟩ => ?_⟩
    obtain ⟨i, lt_i_n, m0zi⟩ := n_z
    exact ⟨i, lt_i_n, in_pmap_trans m0P ⟨i, lt_i_n, m0zi⟩ _ m0zi, ⟨i, lt_i_n, m0zi⟩,
      m0P.map_sym m0zi⟩

/-- Coq `size_pmap`. -/
theorem size_pmap (n : ℕ) {k : Map} (kP : PlainMap k) (h : AtMostRegions nc k) :
    AtMostRegions nc (pmap m0 n k) := by
  obtain ⟨f, f_k⟩ := h
  refine ⟨fun i => if h : ∃ t, k (f i) t ∧ inPmap m0 n t then Classical.choose h else f i,
    fun z ⟨n_z, _, kz⟩ => ?_⟩
  obtain ⟨i, lt_i_nc, kiz⟩ := f_k z kz
  have h : ∃ t, k (f i) t ∧ inPmap m0 n t := ⟨z, kiz, n_z⟩
  refine ⟨i, lt_i_nc, ?_⟩
  simp only [h, ↓reduceDIte]
  obtain ⟨kit, n_t⟩ := Classical.choose_spec h
  exact ⟨n_t, n_z, (kP.map_transl kit z).1 kiz⟩

/-! #### Partial map coloring -/

/-- Coq `pmap_subcoloring`. -/
theorem pmap_subcoloring (n : ℕ) {k : Map} (h : SubColoring nc m0 k) :
    SubColoring nc m0 (pmap m0 n k) where
  toPlainMap := pmap_plain n h.toPlainMap
  subcoloring_adj z1 z2 adj kz := h.subcoloring_adj z1 z2 adj kz.2.2
  subcoloring_size := size_pmap n h.toPlainMap h.subcoloring_size

/-- Coq `pcoloring_exists`. -/
theorem pcoloring_exists (fin_colorable : ∀ m, FiniteSimpleMap m → ColorableWith nc m)
    (m0P : SimpleMap m0) (n : ℕ) : ∃ k, PColoring nc m0 n k := by
  obtain ⟨k, kc, nc_k⟩ := fin_colorable _ (pmap_finite m0P n)
  have clos_n : ∀ z t, inPmap m0 n z → closure (m0 z) t → closure (pmap m0 n m0 z) t := by
    intro z t n_z m0zt r rP r_t
    obtain ⟨u, m0zu, r_u⟩ := m0zt r rP r_t
    exact ⟨u, ⟨n_z, in_pmap_trans m0P n_z u m0zu, m0zu⟩, r_u⟩
  refine ⟨k, ⟨kc.toPlainMap, ?_, nc_k⟩, kc.coloring_consistent⟩
  rintro z1 z2 ⟨m0'z12, z, ⟨f, fP⟩, cl1, cl2⟩ kz12
  have n_z1 := (kc.coloring_cover z1 (kc.map_cover kz12).1).1
  have n_z2 := (kc.coloring_cover z2 (kc.map_cover kz12).2).1
  refine kc.coloring_adjacent ⟨fun h => m0'z12 h.2.2, z, ⟨f, ?_⟩,
    clos_n _ _ n_z1 cl1, clos_n _ _ n_z2 cl2⟩ kz12
  rintro t ⟨⟨n_t, -, m0t⟩, m0tz⟩
  have ct : cover (cornerMap m0 z) t := by
    refine ⟨m0t, fun r rP r_z => ?_⟩
    obtain ⟨u, pu, r_u⟩ := m0tz r rP r_z
    exact ⟨u, pu.2.2, r_u⟩
  obtain ⟨i, lti2, m0it, m0iz⟩ := fP t ct
  have n_i : inPmap m0 n (f i) := in_pmap_trans m0P n_t _ (m0P.map_sym m0it)
  exact ⟨i, lti2, ⟨n_i, n_t, m0it⟩, clos_n _ _ n_i m0iz⟩

/-- Coq `pcoloring_le`. -/
theorem pcoloring_le {n1 n2 : ℕ} {k : Map} (le_n12 : n1 ≤ n2) (h : PColoring nc m0 n2 k) :
    PColoring nc m0 n1 k :=
  ⟨h.1, fun z1 z2 h12 => h.2 z1 z2 (pmap_le le_n12 m0 z1 z2 h12)⟩

/-- Coq `pmap_extensible`. -/
theorem pmap_extensible {n1 n2 : ℕ} {k : Map} (le_n12 : n1 ≤ n2)
    (ext_k : Extensible nc m0 n2 k) : Extensible nc m0 n1 (pmap m0 n1 k) := by
  intro n
  obtain ⟨k', k'P, Ekk'⟩ := ext_k n
  exact ⟨k', k'P, eq_pmap_trans (eq_pmap_sym (eq_map_pmap n1 k)) (eq_pmap_le le_n12 Ekk')⟩

/-! #### Properties of limit coloring prefixes -/

/-- Coq `prefix_pcoloring`. -/
theorem prefix_pcoloring {n : ℕ} {k : Map} (h : PrefixColoring nc m0 n k) :
    PColoring nc m0 n k := by
  obtain ⟨n_k, ext_k, -⟩ := h
  obtain ⟨k', ⟨k'S, k'nm0⟩, Ekk'⟩ := ext_k n
  have k'_k : Submap k k' := fun z1 z2 kz12 => by
    obtain ⟨nz1, nz2, -⟩ := n_k z1 z2 kz12
    exact (Ekk' z1 z2 nz1 nz2).1 kz12
  have kP : PlainMap k := by
    constructor
    · intro z1 z2 kz12
      obtain ⟨nz1, nz2, -⟩ := n_k z1 z2 kz12
      exact (Ekk' z2 z1 nz2 nz1).2 (k'S.map_sym (k'_k z1 z2 kz12))
    · intro z1 z2 kz12 z3 kz23
      obtain ⟨nz1, -, -⟩ := n_k z1 z2 kz12
      obtain ⟨-, nz3, -⟩ := n_k z2 z3 kz23
      exact (Ekk' z1 z3 nz1 nz3).2 (k'S.map_trans (k'_k z1 z2 kz12) z3 (k'_k z2 z3 kz23))
  refine ⟨⟨kP, fun z1 z2 adj kz => k'S.subcoloring_adj z1 z2 adj (k'_k z1 z2 kz), ?_⟩,
    fun z1 z2 h12 => (Ekk' z1 z2 h12.1 h12.2.1).2 (k'nm0 z1 z2 h12)⟩
  obtain ⟨f, k'f⟩ := size_pmap (m0 := m0) n k'S.toPlainMap k'S.subcoloring_size
  refine ⟨f, fun z kz => ?_⟩
  obtain ⟨nz, -, -⟩ := n_k z z kz
  obtain ⟨i, lt_i_nc, nfi, -, k'fiz⟩ := k'f z ⟨nz, nz, k'_k z z kz⟩
  exact ⟨i, lt_i_nc, (Ekk' _ z nfi nz).2 k'fiz⟩

/-- Coq `prefix_coloring_exists`. -/
theorem prefix_coloring_exists (fin_colorable : ∀ m, FiniteSimpleMap m → ColorableWith nc m)
    (m0P : SimpleMap m0) (n : ℕ) : ∃ k, PrefixColoring nc m0 n k := by
  induction n with
  | zero =>
    refine ⟨fun _ _ => False, fun _ _ h => h.elim, fun n => ?_,
      fun i _ _ hi => absurd hi (Nat.not_lt_zero i)⟩
    obtain ⟨k, kP⟩ := pcoloring_exists fin_colorable m0P n
    exact ⟨k, kP, fun _ _ ⟨i, hi, _⟩ _ => absurd hi (Nat.not_lt_zero i)⟩
  | succ n IH =>
    obtain ⟨k0, n_k0, ext_k0, min_k0⟩ := IH
    have le_nn1 : n ≤ n + 1 := Nat.le_succ n
    by_cases n1_n : inPmap m0 (n + 1) (stdPoint n)
    swap
    · have En1n : ∀ z, inPmap m0 (n + 1) z → inPmap m0 n z := by
        intro z hz
        obtain ⟨i, hi, pz⟩ := in_pmapP m0P hz
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · exact ⟨i, hi, pz.2.2⟩
        · exact absurd (hi ▸ pz.2.1) n1_n
      refine ⟨k0, fun z1 z2 h => pmap_le le_nn1 k0 z1 z2 (n_k0 z1 z2 h), fun i => ?_, ?_⟩
      · obtain ⟨k, kP, Ek0k⟩ := ext_k0 i
        exact ⟨k, kP, fun z1 z2 h1 h2 => Ek0k z1 z2 (En1n z1 h1) (En1n z2 h2)⟩
      · intro i j k hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · exact min_k0 i j k hi
        · intro _ h; exact absurd (hi ▸ h.2.1) n1_n
    -- The main case: the `n`-th grid point is in `inPmap m0 (n + 1)`.
    let Ext : ℕ → ℕ → Map → Prop := fun n0 j k =>
      PColoring nc m0 n0 k ∧ EqPmap m0 n k0 k ∧ pmap m0 (n + 1) k (stdPoint j) (stdPoint n)
    let LimitMin : ℕ → Prop := fun j0 => ∃ n0, n < n0 ∧ ∀ j k, Ext n0 j k → j0 ≤ j
    have not_lim : ¬ LimitMin (n + 1) := by
      rintro ⟨n0, lt_nn0, min_n0⟩
      obtain ⟨k, ⟨kS, k_n0⟩, eq_k0k⟩ := ext_k0 n0
      have n0_n : inPmap m0 n0 (stdPoint n) := pmap_std m0P lt_nn0 n1_n
      have := min_n0 n k
        ⟨⟨kS, k_n0⟩, eq_k0k, n1_n, n1_n, k_n0 _ _ ((cover_pmap m0P n0 _).2 n0_n)⟩
      omega
    have hex : ∃ j, ¬ LimitMin (j + 1) := ⟨n, not_lim⟩
    obtain ⟨j0, min'j1, hmin⟩ :
        ∃ j0, ¬ LimitMin (j0 + 1) ∧ ∀ j, j < j0 → LimitMin (j + 1) :=
      ⟨Nat.find hex, Nat.find_spec hex, fun j hj => not_not.1 (Nat.find_min hex hj)⟩
    have le_j0n : j0 ≤ n := by
      by_contra h
      exact not_lim (hmin n (by omega))
    have lim_j0 : LimitMin j0 := by
      cases j0 with
      | zero => exact ⟨n + 1, Nat.lt_succ_self n, fun _ _ _ => Nat.zero_le _⟩
      | succ j' => exact hmin j' (Nat.lt_succ_self j')
    obtain ⟨n0, lt_nn0, min_j0⟩ := lim_j0
    have ext0P : ∀ n', n0 ≤ n' → ∃ k, PColoring nc m0 n' k ∧ Ext n0 j0 k := by
      intro n' le_n0n'
      by_contra ext'n'
      apply min'j1
      refine ⟨n', lt_of_lt_of_le lt_nn0 le_n0n', fun j k ⟨kP, Ek0k, k_jn⟩ => ?_⟩
      have kPn0 : PColoring nc m0 n0 k := pcoloring_le le_n0n' kP
      rcases Nat.lt_or_eq_of_le (min_j0 j k ⟨kPn0, Ek0k, k_jn⟩) with h | h
      · exact h
      · subst h; exact absurd ⟨k, kP, kPn0, Ek0k, k_jn⟩ ext'n'
    obtain ⟨k1, -, Dk1⟩ := ext0P n0 le_rfl
    have Ek12 : EqPmap m0 (n + 1) k1 (pmap m0 (n + 1) k1) := eq_map_pmap _ _
    have m1P : ∀ z, inPmap m0 (n + 1) z → ∃ j, j ≤ n ∧ pmap m0 n0 m0 z (stdPoint j) := by
      intro z hz
      obtain ⟨j, hj, h⟩ := in_pmapP m0P hz
      exact ⟨j, Nat.lt_succ_iff.1 hj, pmap_le lt_nn0 m0 _ _ h⟩
    have n1j0 : inPmap m0 (n + 1) (stdPoint j0) := Dk1.2.2.1
    refine ⟨pmap m0 (n + 1) k1, sub_pmap_pmap _ _, ?ext, ?min⟩
    case min =>
      obtain ⟨-, Ek01, k2_j0n⟩ := Dk1
      intro i j k lt_i_n1 Ek2k i1k_ji ext_k
      have Ek02 : EqPmap m0 n k0 (pmap m0 (n + 1) k1) :=
        eq_pmap_trans Ek01 (eq_pmap_le le_nn1 Ek12)
      have Ek0k : EqPmap m0 i k0 k :=
        eq_pmap_trans (eq_pmap_le (Nat.lt_succ_iff.1 lt_i_n1) Ek02) Ek2k
      rcases Nat.lt_succ_iff_lt_or_eq.1 lt_i_n1 with lt_i_n | Di
      · obtain ⟨j1, le_j1j, k0j1i⟩ := min_k0 i j k lt_i_n Ek0k i1k_ji ext_k
        obtain ⟨nj1, ni, -⟩ := n_k0 _ _ k0j1i
        exact ⟨j1, le_j1j, (Ek02 _ _ nj1 ni).1 k0j1i⟩
      · subst Di
        refine ⟨j0, ?_, k2_j0n⟩
        obtain ⟨k', k'P, Ekk'⟩ := ext_k n0
        obtain ⟨n1j, n1i, k_ji⟩ := i1k_ji
        exact min_j0 j k' ⟨k'P, eq_pmap_trans Ek0k (eq_pmap_le le_nn1 Ekk'), n1j, n1i,
          (Ekk' _ _ n1j n1i).1 k_ji⟩
    case ext =>
      have key : ∀ ka kb, Ext n0 j0 ka → Ext n0 j0 kb → ∀ z1 z2, inPmap m0 (n + 1) z1 →
          inPmap m0 (n + 1) z2 → ka z1 z2 → kb z1 z2 := by
        rintro ka kb ⟨⟨kaS, ka_n0⟩, Ek0a, ka_j0n⟩ ⟨⟨kbS, kb_n0⟩, Ek0b, kb_j0n⟩
          z1 z2 hz1 hz2 kaz12
        obtain ⟨i1, le_i1n, p1⟩ := m1P z1 hz1
        obtain ⟨i2, le_i2n, p2⟩ := m1P z2 hz2
        have kaP := kaS.toPlainMap
        have kbP := kbS.toPlainMap
        have n0i1 : inPmap m0 n0 (stdPoint i1) := p1.2.1
        have n0i2 : inPmap m0 n0 (stdPoint i2) := p2.2.1
        suffices h : ka (stdPoint i1) (stdPoint i2) → kb (stdPoint i1) (stdPoint i2) by
          have a1 := ka_n0 _ _ p1
          have a2 := ka_n0 _ _ p2
          have b1 := kb_n0 _ _ p1
          have b2 := kb_n0 _ _ p2
          have := h ((kaP.map_transr a2 _).1 ((kaP.map_transl a1 _).1 kaz12))
          exact (kbP.map_transl b1 _).2 ((kbP.map_transr b2 _).2 this)
        have Eab : EqPmap m0 n ka kb := eq_pmap_trans (eq_pmap_sym Ek0a) Ek0b
        have main : ∀ i1 i2, i1 < i2 → i2 ≤ n → inPmap m0 n0 (stdPoint i1) →
            inPmap m0 n0 (stdPoint i2) → ka (stdPoint i1) (stdPoint i2) →
            kb (stdPoint i1) (stdPoint i2) := by
          intro i1 i2 lt12 le2n n0i1 n0i2 kai
          have lt_i1n : i1 < n := lt_of_lt_of_le lt12 le2n
          have n_i1 : inPmap m0 n (stdPoint i1) := pmap_std m0P lt_i1n n0i1
          rcases Nat.lt_or_eq_of_le le2n with lt2n | h2n
          · exact (Eab _ _ n_i1 (pmap_std m0P lt2n n0i2)).1 kai
          rw [h2n] at kai ⊢
          have n1i1 : inPmap m0 (n + 1) (stdPoint i1) := in_pmap_le le_nn1 _ n_i1
          have le_j0i1 : j0 ≤ i1 :=
            min_j0 i1 ka ⟨⟨kaS, ka_n0⟩, Ek0a, n1i1, n1_n, kai⟩
          have n_j0 : inPmap m0 n (stdPoint j0) :=
            pmap_std m0P (lt_of_le_of_lt le_j0i1 lt_i1n) n1j0
          have ka_i1j0 : ka (stdPoint i1) (stdPoint j0) := (kaP.map_transr ka_j0n.2.2 _).2 kai
          exact kbP.trans' ((Eab _ _ n_i1 n_j0).1 ka_i1j0) kb_j0n.2.2
        rcases lt_trichotomy i1 i2 with h | h | h
        · exact main i1 i2 h le_i2n n0i1 n0i2
        · intro _
          subst h
          exact kb_n0 _ _ ((cover_pmap m0P n0 _).2 n0i1)
        · intro kai
          exact kbP.map_sym (main i2 i1 h le_i1n n0i2 n0i1 (kaP.map_sym kai))
      intro n'
      obtain ⟨k3, k3P, Dk3⟩ := ext0P (max n0 n') (le_max_left _ _)
      refine ⟨k3, pcoloring_le (le_max_right _ _) k3P, ?_⟩
      have Ek13 : EqPmap m0 (n + 1) k1 k3 := fun z1 z2 h1 h2 =>
        ⟨key k1 k3 Dk1 Dk3 z1 z2 h1 h2, key k3 k1 Dk3 Dk1 z1 z2 h1 h2⟩
      exact eq_pmap_trans (eq_pmap_sym Ek12) Ek13

/-- Coq `prefix_coloring_le`: prefix colorings form an inclusion chain. -/
theorem prefix_coloring_le (m0P : SimpleMap m0) {n1 n2 : ℕ} {k1 k2 : Map} (le_n12 : n1 ≤ n2)
    (k1pre : PrefixColoring nc m0 n1 k1) (k2pre : PrefixColoring nc m0 n2 k2) :
    Submap k1 k2 := by
  -- Reduce to the case `n2 = n1`, replacing `k2` by `pmap m0 n1 k2`.
  suffices H : ∀ k2, PrefixColoring nc m0 n1 k2 → Submap k1 k2 by
    have k2P := (prefix_pcoloring k2pre).1.toPlainMap
    obtain ⟨n2k2, k2_ext, k2_min⟩ := k2pre
    refine fun z1 z2 h => pmap_sub n1 k2 z1 z2
      (H (pmap m0 n1 k2) ⟨sub_pmap_pmap _ _, pmap_extensible le_n12 k2_ext, ?_⟩ z1 z2 h)
    intro i j k lt_i_n1 Ek2k i1k_ji k_ext
    obtain ⟨j0, le_j0j, k2j0i⟩ := k2_min i j k (lt_of_lt_of_le lt_i_n1 le_n12)
      (eq_pmap_trans (eq_pmap_le (Nat.le_of_lt lt_i_n1) (eq_map_pmap n1 k2)) Ek2k) i1k_ji k_ext
    have n1i : inPmap m0 n1 (stdPoint i) := pmap_std m0P lt_i_n1 i1k_ji.2.1
    obtain ⟨n2j0, -, -⟩ := n2k2 _ _ k2j0i
    have k2i : cover k2 (stdPoint i) := (k2P.map_cover k2j0i).2
    by_cases le_i_j : i ≤ j
    · exact ⟨i, le_i_j, n1i, n1i, k2i⟩
    · exact ⟨j0, le_j0j, pmap_std m0P (by omega) n2j0, n1i, k2j0i⟩
  intro k2 k2pre
  have n1k1 := k1pre.1
  suffices Ek12 : EqPmap m0 n1 k1 k2 by
    intro z1 z2 h
    obtain ⟨nz1, nz2, -⟩ := n1k1 z1 z2 h
    exact (Ek12 z1 z2 nz1 nz2).1 h
  -- One direction of the induction step, for any two prefix colorings `ka` and `kb`.
  have step : ∀ n, n + 1 ≤ n1 → ∀ ka kb, PrefixColoring nc m0 n1 ka →
      PrefixColoring nc m0 n1 kb → EqPmap m0 n ka kb → ∀ z1 z2, inPmap m0 (n + 1) z1 →
      inPmap m0 (n + 1) z2 → ka z1 z2 → kb z1 z2 := by
    intro n lt_nn1 ka kb kapre kbpre IHn z1 z2 hz1 hz2 kaz12
    have m1P : ∀ z, inPmap m0 (n + 1) z → ∃ i, i ≤ n ∧ pmap m0 n1 m0 z (stdPoint i) := by
      intro z hz
      obtain ⟨i, hi, h⟩ := in_pmapP m0P hz
      exact ⟨i, Nat.lt_succ_iff.1 hi, pmap_le lt_nn1 m0 _ _ h⟩
    obtain ⟨i1, le_i1n, p1⟩ := m1P z1 hz1
    obtain ⟨i2, le_i2n, p2⟩ := m1P z2 hz2
    obtain ⟨kaS, ka_n1⟩ := prefix_pcoloring kapre
    obtain ⟨kbS, kb_n1⟩ := prefix_pcoloring kbpre
    have kaP := kaS.toPlainMap
    have kbP := kbS.toPlainMap
    have n1i1 : inPmap m0 n1 (stdPoint i1) := p1.2.1
    have n1i2 : inPmap m0 n1 (stdPoint i2) := p2.2.1
    suffices h : ka (stdPoint i1) (stdPoint i2) → kb (stdPoint i1) (stdPoint i2) by
      have a1 := ka_n1 _ _ p1
      have a2 := ka_n1 _ _ p2
      have b1 := kb_n1 _ _ p1
      have b2 := kb_n1 _ _ p2
      have := h ((kaP.map_transr a2 _).1 ((kaP.map_transl a1 _).1 kaz12))
      exact (kbP.map_transl b1 _).2 ((kbP.map_transr b2 _).2 this)
    obtain ⟨n1ka, kaext, kamin⟩ := kapre
    obtain ⟨n1kb, kbext, kbmin⟩ := kbpre
    have main : ∀ i1 i2, i1 < i2 → i2 ≤ n → inPmap m0 n1 (stdPoint i1) →
        inPmap m0 n1 (stdPoint i2) → ka (stdPoint i1) (stdPoint i2) →
        kb (stdPoint i1) (stdPoint i2) := by
      intro i1 i2 lt12 le2n n1i1 n1i2 kai
      have lt_i1n : i1 < n := lt_of_lt_of_le lt12 le2n
      rcases Nat.lt_or_eq_of_le le2n with lt2n | h2n
      · exact (IHn _ _ (pmap_std m0P lt_i1n n1i1) (pmap_std m0P lt2n n1i2)).1 kai
      rw [h2n] at kai n1i2 ⊢
      have n'_n : inPmap m0 (n + 1) (stdPoint n) := pmap_std m0P (Nat.lt_succ_self n) n1i2
      -- Strong induction on `i1` (Coq's inner `elim` on `n3`).
      have H : ∀ i1, i1 < n → inPmap m0 n1 (stdPoint i1) → ka (stdPoint i1) (stdPoint n) →
          kb (stdPoint i1) (stdPoint n) := by
        intro i1
        induction i1 using Nat.strong_induction_on with
        | _ i1 IH =>
        intro lt_i1n n1i1 kai
        have n'_i1 : inPmap m0 (n + 1) (stdPoint i1) := pmap_std m0P (by omega) n1i1
        obtain ⟨i3, le_i3i1, kbi3n⟩ := kbmin n i1 (pmap m0 (n + 1) ka) (by omega)
          (eq_pmap_trans (eq_pmap_sym IHn) (eq_pmap_le (Nat.le_succ n) (eq_map_pmap (n + 1) ka)))
          ⟨n'_i1, n'_n, n'_i1, n'_n, kai⟩ (pmap_extensible lt_nn1 kaext)
        rcases Nat.lt_or_eq_of_le le_i3i1 with lt_i31 | h31
        swap
        · rw [← h31]; exact kbi3n
        obtain ⟨n1i3, -, -⟩ := n1kb _ _ kbi3n
        have n'i3 : inPmap m0 (n + 1) (stdPoint i3) := pmap_std m0P (by omega) n1i3
        obtain ⟨i4, le_i43, kai4n⟩ := kamin n i3 (pmap m0 (n + 1) kb) (by omega)
          (eq_pmap_trans IHn (eq_pmap_le (Nat.le_succ n) (eq_map_pmap (n + 1) kb)))
          ⟨n'i3, n'_n, n'i3, n'_n, kbi3n⟩ (pmap_extensible lt_nn1 kbext)
        have lt_i4n : i4 < n := by omega
        obtain ⟨n1i4, -, -⟩ := n1ka _ _ kai4n
        have kbi4n : kb (stdPoint i4) (stdPoint n) := IH i4 (by omega) lt_i4n n1i4 kai4n
        have kai14 : ka (stdPoint i1) (stdPoint i4) := (kaP.map_transr kai4n _).2 kai
        have kbi14 :=
          (IHn _ _ (pmap_std m0P lt_i1n n1i1) (pmap_std m0P lt_i4n n1i4)).1 kai14
        exact kbP.trans' kbi14 kbi4n
      exact H i1 lt_i1n n1i1 kai
    rcases lt_trichotomy i1 i2 with h | h | h
    · exact main i1 i2 h le_i2n n1i1 n1i2
    · intro _
      subst h
      exact kb_n1 _ _ ((cover_pmap m0P n1 _).2 n1i1)
    · intro kai
      exact kbP.map_sym (main i2 i1 h le_i1n n1i2 n1i1 (kaP.map_sym kai))
  have H : ∀ n, n ≤ n1 → EqPmap m0 n k1 k2 := by
    intro n
    induction n with
    | zero => intro _ z1 _ ⟨i, hi, _⟩; exact absurd hi (Nat.not_lt_zero _)
    | succ n IHn =>
      intro lt
      have IH := IHn (by omega)
      exact fun z1 z2 h1 h2 => ⟨step n lt k1 k2 k1pre k2pre IH z1 z2 h1 h2,
        step n lt k2 k1 k2pre k1pre (eq_pmap_sym IH) z1 z2 h1 h2⟩
  exact H n1 le_rfl

/-! #### The constructed limit is an `nc`-coloring of `m0` -/

/-- Coq `limit_coloring_coloring`. -/
theorem limit_coloring_coloring (fin_colorable : ∀ m, FiniteSimpleMap m → ColorableWith nc m)
    (m0P : SimpleMap m0) : Coloring m0 (limitColoring nc m0) := by
  have lP : PlainMap (limitColoring nc m0) := by
    constructor
    · rintro z1 z2 ⟨k, ⟨n, kpre⟩, kz⟩
      exact ⟨k, ⟨n, kpre⟩, (prefix_pcoloring kpre).1.toPlainMap.map_sym kz⟩
    · rintro z1 z2 ⟨k1, ⟨n1, k1pre⟩, k1z⟩ z3 ⟨k3, ⟨n3, k3pre⟩, k3z⟩
      rcases le_total n1 n3 with h | h
      · exact ⟨k3, ⟨n3, k3pre⟩, (prefix_pcoloring k3pre).1.toPlainMap.trans'
          (prefix_coloring_le m0P h k1pre k3pre _ _ k1z) k3z⟩
      · exact ⟨k1, ⟨n1, k1pre⟩, (prefix_pcoloring k1pre).1.toPlainMap.trans' k1z
          (prefix_coloring_le m0P h k3pre k1pre _ _ k3z)⟩
  refine ⟨lP, ?_, ?_, ?_⟩
  · rintro z ⟨k, ⟨n, n_k, -, -⟩, kz⟩
    obtain ⟨⟨i, _, m0zi⟩, -, -⟩ := n_k z z kz
    exact (m0P.map_cover m0zi).1
  · intro z1 z2 m0z12
    obtain ⟨i1, h1⟩ := has_std_point m0P (m0P.map_cover m0z12).1
    obtain ⟨i2, h2⟩ := has_std_point m0P (m0P.map_cover m0z12).2
    obtain ⟨k, kpre⟩ := prefix_coloring_exists fin_colorable m0P (max i1 i2 + 1)
    exact ⟨k, ⟨_, kpre⟩, (prefix_pcoloring kpre).2 z1 z2
      ⟨⟨i1, by omega, h1⟩, ⟨i2, by omega, h2⟩, m0z12⟩⟩
  · rintro z1 z2 adj ⟨k, ⟨n, kpre⟩, kz⟩
    exact (prefix_pcoloring kpre).1.subcoloring_adj z1 z2 adj kz

/-- Coq `size_limit_coloring`. -/
theorem size_limit_coloring (fin_colorable : ∀ m, FiniteSimpleMap m → ColorableWith nc m)
    (m0P : SimpleMap m0) : AtMostRegions nc (limitColoring nc m0) := by
  -- A map with more than `n` regions has `n + 1` covered, pairwise unrelated points.
  have minsize : ∀ (n : ℕ) (k : Map), ¬ AtMostRegions n k → ∃ f : ℕ → Point,
      (∀ i, i < n + 1 → cover k (f i)) ∧
        (∀ i j, i < j → j < n + 1 → ¬ k (f i) (f j)) := by
    intro n k
    induction n with
    | zero =>
      intro h
      by_cases hz : ∃ z, cover k z
      · obtain ⟨z, kz⟩ := hz
        exact ⟨fun _ => z, fun _ _ => kz, fun i j hij hj => by omega⟩
      · exact absurd ⟨stdPoint, fun z kz => absurd ⟨z, kz⟩ hz⟩ h
    | succ n IHn =>
      intro nonmin
      have : ¬ AtMostRegions n k := fun ⟨f, hf⟩ => nonmin ⟨f, fun z kz => by
        obtain ⟨i, hi, h⟩ := hf z kz; exact ⟨i, by omega, h⟩⟩
      obtain ⟨f, k_f, inj_f⟩ := IHn this
      have : ∃ z, cover k z ∧ ∀ i, i < n + 1 → ¬ k (f i) z := by
        by_contra hcon
        refine nonmin ⟨f, fun z kz => ?_⟩
        by_contra hz
        exact hcon ⟨z, kz, fun i hi kiz => hz ⟨i, hi, kiz⟩⟩
      obtain ⟨z, kz, hz⟩ := this
      refine ⟨fun i => if i < n + 1 then f i else z, fun i _ => ?_, fun i j hij hj => ?_⟩
      · by_cases hi : i < n + 1
        · simp only [hi, ↓reduceIte]; exact k_f i hi
        · simp only [hi, ↓reduceIte]; exact kz
      · have hi : i < n + 1 := by omega
        by_cases hjn : j < n + 1
        · simp only [hi, hjn, ↓reduceIte]; exact inj_f i j hij hjn
        · simp only [hi, hjn, ↓reduceIte]; exact hz i hi
  by_contra hnot
  obtain ⟨f, lim_f, inj_limf⟩ := minsize nc _ hnot
  -- A single prefix coloring covers all the points `f i`.
  have hN : ∀ n, n ≤ nc + 1 → ∃ N, ∀ i, i < n →
      ∃ ni ki, ni ≤ N ∧ PrefixColoring nc m0 ni ki ∧ ki (f i) (f i) := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨0, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ n IH =>
      intro hn
      obtain ⟨N, hN⟩ := IH (by omega)
      obtain ⟨k, ⟨ni, kpre⟩, kf⟩ := lim_f n (by omega)
      refine ⟨max N ni, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
      · obtain ⟨nj, kj, h1, h2, h3⟩ := hN i hi
        exact ⟨nj, kj, le_trans h1 (le_max_left _ _), h2, h3⟩
      · subst hi
        exact ⟨ni, k, le_max_right _ _, kpre, kf⟩
  obtain ⟨N, hN⟩ := hN (nc + 1) le_rfl
  obtain ⟨k, kpre⟩ := prefix_coloring_exists fin_colorable m0P N
  have k_f : ∀ i, i < nc + 1 → cover k (f i) := fun i hi => by
    obtain ⟨ni, ki, le, kipre, kif⟩ := hN i hi
    exact prefix_coloring_le m0P le kipre kpre _ _ kif
  obtain ⟨⟨kP, -, fk, fk_k⟩, -⟩ := prefix_pcoloring kpre
  have hs : ∀ i : Fin (nc + 1), ∃ j : Fin nc, k (fk j) (f i) := fun i => by
    obtain ⟨j, hj, h⟩ := fk_k _ (k_f i i.2)
    exact ⟨⟨j, hj⟩, h⟩
  choose s hs using hs
  have key : ∀ a b : Fin (nc + 1), a < b → s a = s b → False := by
    intro a b hab e
    have h1 := hs a
    have h2 := hs b
    rw [e] at h1
    exact inj_limf a b hab b.2 ⟨k, ⟨N, kpre⟩, kP.trans' (kP.map_sym h1) h2⟩
  have inj : Function.Injective s := by
    intro a b e
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact key _ _ h e
    · exact key _ _ h e.symm
  have := Fintype.card_le_of_injective s inj
  simp at this

end FinitizeMap

/-- Coq `compactness_extension`, for an arbitrary number of colors `nc`: if every finite simple
map is `nc`-colorable, then so is every simple map. -/
theorem compactness_extension_with {nc : ℕ}
    (fin_colorable : ∀ m, FiniteSimpleMap m → ColorableWith nc m)
    (m0 : Map) (m0P : SimpleMap m0) : ColorableWith nc m0 :=
  ⟨limitColoring nc m0, limit_coloring_coloring fin_colorable m0P,
    size_limit_coloring fin_colorable m0P⟩

/-- Coq `compactness_extension` (with `nc = 4`): the Four Color Theorem for finite simple maps
extends to all simple maps. -/
theorem compactness_extension :
    (∀ m, FiniteSimpleMap m → ColorableWith 4 m) → ∀ m, SimpleMap m → ColorableWith 4 m :=
  fun h m hm => compactness_extension_with h m hm

end FourColor.RealPlane
