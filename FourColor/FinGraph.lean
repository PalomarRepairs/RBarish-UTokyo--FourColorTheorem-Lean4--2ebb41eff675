/-
Copyright (c) 2026. Lean 4 port of the planarity part of the Coq/Rocq formal proof
of the Four Color Theorem by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import Mathlib.Data.Set.Card
import Mathlib.Logic.Relation
import Mathlib.GroupTheory.Perm.Cycle.Basic
import FourColor.Seq

/-!
# Finite graphs

The fragment of math-comp's `fingraph.v` used by the hypermap development:

* `connect e`   : reflexive-transitive closure of a relation (math-comp `connect`)
* `frel f`, `fconnect f`, `fpath f`, `fcycle f` : the same notions for the graph of a function
* `ConnectSym e` : `connect e` is symmetric (math-comp `connect_sym`)
* `Closed e a`  : `a` is closed under `e`-links (math-comp `closed`)
* `closure e a` : the points connected to `a` (math-comp `closure`)
* `nComp e a`   : the number of connected components meeting `a` (math-comp `n_comp`)
* `fcard f a`   : the number of `f`-orbits meeting `a` (math-comp `fcard`)
* `order f x`   : the size of the `f`-orbit of `x` (math-comp `order`)

math-comp counts components by counting canonical roots (`root e x == x`) inside `a`; here
`nComp e a` counts the distinct components `{y | connect e x y}` for `x ∈ a`.  The two agree
whenever `connect e` is symmetric and `a` is `e`-closed.  This is the case in every use in this
development: all relations counted (`glink`, `clink`, and the graphs of injective functions on
finite types) are connect-symmetric, and all sets counted are closed.  A later port that counts
components of a non-closed set, or of a non-symmetric relation, cannot use `nComp` as a drop-in
replacement for math-comp's `n_comp`.

The "adjunction" machinery of math-comp (`rel_adjunction`, `strict_adjunction`,
`adjunction_n_comp`) is packaged as `connect_iff_of_base` and `nComp_adjunction`.
-/

namespace FourColor

open Function Relation

variable {α β : Type*}

/-! ### Connectivity -/

/-- math-comp `connect e`: the reflexive-transitive closure of `e`. -/
abbrev connect (e : α → α → Prop) : α → α → Prop := ReflTransGen e

/-- math-comp `frel f`: the graph of a function, as a relation. -/
abbrev frel (f : α → α) : α → α → Prop := fun x y => f x = y

/-- math-comp `fconnect f`: `y` is in the forward orbit of `x`. -/
abbrev fconnect (f : α → α) : α → α → Prop := connect (frel f)

/-- math-comp `fpath f`. -/
abbrev fpath (f : α → α) : α → List α → Prop := path (frel f)

/-- math-comp `fcycle f`. -/
abbrev fcycle (f : α → α) : List α → Prop := cycle (frel f)

/-- math-comp `connect_sym e`. -/
def ConnectSym (e : α → α → Prop) : Prop := ∀ x y, connect e x y → connect e y x

variable {e e' : α → α → Prop}

/-- math-comp `connect0`. -/
theorem connect_refl (x : α) : connect e x x := ReflTransGen.refl

/-- math-comp `connect1`. -/
theorem connect_of_rel {x y : α} (h : e x y) : connect e x y := ReflTransGen.single h

/-- math-comp `connect_trans`. -/
theorem connect_trans {x y z : α} (h₁ : connect e x y) (h₂ : connect e y z) :
    connect e x z := ReflTransGen.trans h₁ h₂

/-- math-comp `connectP`. -/
theorem connect_iff_path {x y : α} : connect e x y ↔ ∃ p, path e x p ∧ last x p = y := by
  constructor
  · intro h
    induction h using ReflTransGen.head_induction_on with
    | refl => exact ⟨[], trivial, rfl⟩
    | head hxc _ ih =>
      obtain ⟨p, hp, hl⟩ := ih
      exact ⟨_ :: p, ⟨hxc, hp⟩, hl⟩
  · rintro ⟨p, hp, rfl⟩
    induction p generalizing x with
    | nil => exact connect_refl x
    | cons y p ih => exact ReflTransGen.head hp.1 (ih hp.2)

/-- math-comp `path_connect`. -/
theorem path_connect {x : α} {p : List α} (hp : path e x p) {y : α} (hy : y ∈ x :: p) :
    connect e x y := by
  induction p generalizing x with
  | nil =>
    rw [List.mem_singleton] at hy
    subst hy
    exact connect_refl _
  | cons z p ih =>
    rcases List.mem_cons.1 hy with rfl | hy
    · exact connect_refl _
    · exact ReflTransGen.head hp.1 (ih hp.2 hy)

theorem connect_mono (h : ∀ a b, e a b → e' a b) {x y : α} (hxy : connect e x y) :
    connect e' x y := by
  induction hxy with
  | refl => exact connect_refl _
  | tail _ hbc ih => exact ReflTransGen.tail ih (h _ _ hbc)

/-- math-comp `connect_sub`: a relation included in `connect e'` has its closure included too. -/
theorem connect_sub (h : ∀ a b, e a b → connect e' a b) {x y : α} (hxy : connect e x y) :
    connect e' x y := by
  induction hxy with
  | refl => exact connect_refl _
  | tail _ hbc ih => exact connect_trans ih (h _ _ hbc)

/-- math-comp `eq_connect`. -/
theorem connect_congr (h : ∀ a b, e a b ↔ e' a b) {x y : α} :
    connect e x y ↔ connect e' x y :=
  ⟨connect_mono fun a b => (h a b).1, connect_mono fun a b => (h a b).2⟩

theorem ConnectSym.iff (hs : ConnectSym e) {x y : α} : connect e x y ↔ connect e y x :=
  ⟨hs x y, hs y x⟩

/-- A relation whose links can each be reversed by a path is connect-symmetric. -/
theorem connectSym_of_rev (h : ∀ x y, e x y → connect e y x) : ConnectSym e := by
  intro x y hxy
  induction hxy with
  | refl => exact connect_refl _
  | tail _ hbc ih => exact connect_trans (h _ _ hbc) ih

/-- A connected pair lies in the same `connect`-class (math-comp `same_connect`). -/
theorem ConnectSym.same (hs : ConnectSym e) {x y : α} (hxy : connect e x y) (z : α) :
    connect e x z ↔ connect e y z :=
  ⟨fun h => connect_trans (hs _ _ hxy) h, fun h => connect_trans hxy h⟩

/-- math-comp `same_connect_r`. -/
theorem ConnectSym.same_r (hs : ConnectSym e) {x y : α} (hxy : connect e x y) (z : α) :
    connect e z x ↔ connect e z y :=
  ⟨fun h => connect_trans h hxy, fun h => connect_trans h (hs _ _ hxy)⟩

/-- math-comp `same_connect_rev`: connectivity for the converse relation. -/
theorem connect_flip_iff (hs : ConnectSym e) {x y : α} :
    connect (fun a b => e b a) x y ↔ connect e x y := by
  have key : ∀ {x y : α}, connect (fun a b => e b a) x y → connect e y x := by
    intro x y h
    induction h with
    | refl => exact connect_refl _
    | tail _ hbc ih => exact connect_trans (connect_of_rel hbc) ih
  have key' : ∀ {x y : α}, connect e x y → connect (fun a b => e b a) y x := by
    intro x y h
    induction h with
    | refl => exact connect_refl _
    | tail _ hbc ih => exact connect_trans (connect_of_rel hbc) ih
  exact ⟨fun h => hs _ _ (key h), fun h => key' (hs _ _ h)⟩

/-! ### Function orbits -/

theorem fconnect_iff_iterate {f : α → α} {x y : α} : fconnect f x y ↔ ∃ n, f^[n] x = y := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, rfl⟩
    | tail _ hbc ih =>
      obtain ⟨n, rfl⟩ := ih
      exact ⟨n + 1, by rw [iterate_succ_apply']; exact hbc⟩
  · rintro ⟨n, rfl⟩
    induction n with
    | zero => exact connect_refl _
    | succ n ih => rw [iterate_succ_apply']; exact ReflTransGen.tail ih rfl

theorem fconnect_iterate (f : α → α) (x : α) (n : ℕ) : fconnect f x (f^[n] x) :=
  fconnect_iff_iterate.2 ⟨n, rfl⟩

/-- math-comp `fconnect1`. -/
theorem fconnect1 (f : α → α) (x : α) : fconnect f x (f x) := connect_of_rel rfl

theorem exists_iterate_eq_self [Finite α] {f : α → α} (hf : Injective f) (x : α) :
    ∃ n, 0 < n ∧ f^[n] x = x := by
  let σ : Equiv.Perm α := Equiv.ofBijective f hf.bijective_of_finite
  refine ⟨orderOf σ, orderOf_pos σ, ?_⟩
  have h1 : (σ ^ orderOf σ) x = x := by rw [pow_orderOf_eq_one]; rfl
  rw [Equiv.Perm.coe_pow] at h1
  exact h1

/-- math-comp `fconnect_sym`. -/
theorem fconnect_sym [Finite α] {f : α → α} (hf : Injective f) : ConnectSym (frel f) := by
  apply connectSym_of_rev
  rintro x _ rfl
  obtain ⟨n, hn, hx⟩ := exists_iterate_eq_self hf x
  refine fconnect_iff_iterate.2 ⟨n - 1, ?_⟩
  rw [← iterate_succ_apply, Nat.succ_eq_add_one, Nat.sub_add_cancel hn, hx]

theorem fconnect_comm [Finite α] {f : α → α} (hf : Injective f) {x y : α} :
    fconnect f x y ↔ fconnect f y x :=
  (fconnect_sym hf).iff

/-- math-comp `same_fconnect1`. -/
theorem same_fconnect1 [Finite α] {f : α → α} (hf : Injective f) (x y : α) :
    fconnect f x y ↔ fconnect f (f x) y :=
  (fconnect_sym hf).same (fconnect1 f x) y

/-- math-comp `same_fconnect1_r`. -/
theorem same_fconnect1_r [Finite α] {f : α → α} (hf : Injective f) (x y : α) :
    fconnect f x y ↔ fconnect f x (f y) :=
  (fconnect_sym hf).same_r (fconnect1 f y) x

/-- math-comp `same_fconnect_finv`: an inverse of `f` has the same orbits as `f`. -/
theorem fconnect_inverse [Finite α] {f g : α → α} (hgf : LeftInverse g f)
    (hfg : RightInverse g f) {x y : α} : fconnect g x y ↔ fconnect f x y := by
  have hf : Injective f := hgf.injective
  have hg : Injective g := hfg.injective
  have key : ∀ {h k : α → α}, LeftInverse k h → ∀ {x y : α}, fconnect h x y → fconnect k y x := by
    intro h k hkh x y hxy
    induction hxy with
    | refl => exact connect_refl _
    | tail _ hbc ih =>
      subst hbc
      exact connect_trans (connect_of_rel (hkh _)) ih
  exact ⟨fun h => (fconnect_sym hf) _ _ (key hfg h), fun h => (fconnect_sym hg) _ _ (key hgf h)⟩

/-- math-comp `eq_fconnect`. -/
theorem fconnect_congr {f g : α → α} (h : ∀ x, f x = g x) {x y : α} :
    fconnect f x y ↔ fconnect g x y :=
  connect_congr fun a b => by show f a = b ↔ g a = b; rw [h]

theorem last_eq_last {a b : α} {p : List α} (hp : p ≠ []) : last a p = last b p := by
  cases p with
  | nil => exact absurd rfl hp
  | cons x p => rfl

/-- math-comp `fconnect_cycle`: in an `f`-cycle, the orbit of an item is the cycle. -/
theorem fconnect_cycle {f : α → α} {p : List α} (hp : fcycle f p) {x : α} (hx : x ∈ p)
    {y : α} : fconnect f x y ↔ y ∈ p := by
  constructor
  · intro h
    induction h with
    | refl => exact hx
    | tail _ hbc ih =>
      obtain ⟨v, hv, huv⟩ := hp.exists_succ ih
      exact hbc ▸ huv ▸ hv
  · intro hy
    have hne : p ≠ [] := List.ne_nil_of_mem hx
    have hpath : path (frel f) (last x p) p := (cycle_iff_path x p).1 hp
    have hpp : path (frel f) (last x p) (p ++ p) := by
      rw [path_append]
      refine ⟨hpath, ?_⟩
      rw [last_eq_last hne (a := last x p) (b := x)]
      exact hpath
    obtain ⟨p₁, p₂, rfl⟩ := List.append_of_mem hx
    have h2 : path (frel f) x (p₂ ++ (p₁ ++ x :: p₂)) := by
      rw [List.append_assoc] at hpp
      exact path.of_append_cons hpp
    exact path_connect h2 (List.mem_cons_of_mem _ (List.mem_append_right _ hy))

/-! ### Closed sets and closures -/

/-- math-comp `closed e a`: `a` is closed under `e`-links, in both directions. -/
def Closed (e : α → α → Prop) (a : Set α) : Prop := ∀ x y, e x y → (x ∈ a ↔ y ∈ a)

/-- math-comp `closed_connect`. -/
theorem Closed.connect_iff {a : Set α} (ha : Closed e a) {x y : α} (h : connect e x y) :
    x ∈ a ↔ y ∈ a := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ hbc ih => exact ih.trans (ha _ _ hbc)

/-- math-comp `predC_closed`. -/
theorem Closed.compl {a : Set α} (ha : Closed e a) : Closed e aᶜ :=
  fun x y h => not_congr (ha x y h)

/-- math-comp `intro_closed`. -/
theorem Closed.of_forward (hs : ConnectSym e) {a : Set α}
    (h : ∀ x y, e x y → x ∈ a → y ∈ a) : Closed e a := by
  intro x y hxy
  refine ⟨h x y hxy, fun hy => ?_⟩
  have hyx := hs _ _ (connect_of_rel hxy)
  clear hxy
  induction hyx with
  | refl => exact hy
  | tail _ hbc ih => exact h _ _ hbc ih

/-- Forward closure of a set along `connect`. -/
theorem mem_of_connect_of_forward {a : Set α} (h : ∀ x y, e x y → x ∈ a → y ∈ a) {x y : α}
    (hxy : connect e x y) (hx : x ∈ a) : y ∈ a := by
  induction hxy with
  | refl => exact hx
  | tail _ hbc ih => exact h _ _ hbc ih

/-- The connected component of `x`, as a set. -/
def comp (e : α → α → Prop) (x : α) : Set α := {y | connect e x y}

@[simp] theorem mem_comp {x y : α} : y ∈ comp e x ↔ connect e x y := Iff.rfl

/-- math-comp `connect_closed`. -/
theorem closed_comp (hs : ConnectSym e) (x : α) : Closed e (comp e x) :=
  Closed.of_forward hs fun _ _ h hy => connect_trans hy (connect_of_rel h)

/-- math-comp `closure e a`: the points connected to some point of `a`. -/
def closure (e : α → α → Prop) (a : Set α) : Set α := {x | ∃ y ∈ a, connect e x y}

/-- math-comp `fclosure f a`. -/
abbrev fclosure (f : α → α) (a : Set α) : Set α := closure (frel f) a

theorem closure_closed (hs : ConnectSym e) (a : Set α) : Closed e (closure e a) := by
  apply Closed.of_forward hs
  rintro x y hxy ⟨z, hz, hxz⟩
  exact ⟨z, hz, connect_trans (hs _ _ (connect_of_rel hxy)) hxz⟩

theorem subset_closure (a : Set α) : a ⊆ closure e a := fun x hx => ⟨x, hx, connect_refl x⟩

/-! ### Counting components -/

/-- Port of math-comp `n_comp e a`: the number of `connect e`-components meeting `a`.  It agrees
with math-comp's count of component roots lying in `a` when `connect e` is symmetric and `a` is
`e`-closed (see the module docstring). -/
noncomputable def nComp (e : α → α → Prop) (a : Set α) : ℕ := (comp e '' a).ncard

/-- math-comp `fcard f a`: the number of `f`-orbits meeting `a`. -/
noncomputable abbrev fcard (f : α → α) (a : Set α) : ℕ := nComp (frel f) a

theorem comp_eq_iff (hs : ConnectSym e) {x y : α} : comp e x = comp e y ↔ connect e x y := by
  constructor
  · intro h
    have : y ∈ comp e y := connect_refl y
    rw [← h] at this
    exact this
  · intro h
    ext z
    exact hs.same h z

/-- math-comp `eq_n_comp`. -/
theorem nComp_congr (h : ∀ x y, connect e x y ↔ connect e' x y) (a : Set α) :
    nComp e a = nComp e' a := by
  have : comp e = comp e' := by
    funext x
    ext y
    exact h x y
  rw [nComp, nComp, this]

/-- math-comp `eq_n_comp_r`. -/
theorem nComp_congr_set {a b : Set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : nComp e a = nComp e b := by
  rw [Set.ext h]

@[simp] theorem nComp_empty : nComp e (∅ : Set α) = 0 := by simp [nComp]

/-- math-comp `n_comp_connect`. -/
theorem nComp_comp (hs : ConnectSym e) (x : α) : nComp e (comp e x) = 1 := by
  rw [nComp, Set.ncard_eq_one]
  refine ⟨comp e x, ?_⟩
  ext c
  simp only [Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ((comp_eq_iff hs).2 hy).symm
  · rintro rfl
    exact ⟨x, connect_refl x, rfl⟩

theorem nComp_eq_zero [Finite α] {a : Set α} : nComp e a = 0 ↔ a = ∅ := by
  rw [nComp, Set.ncard_eq_zero, Set.image_eq_empty]

theorem nComp_pos [Finite α] {a : Set α} : 0 < nComp e a ↔ a.Nonempty := by
  rw [nComp, Set.ncard_pos, Set.image_nonempty]

/-- math-comp `n_compC`: splitting the component count along an `e`-closed set. -/
theorem nComp_compl [Finite α] {a : Set α} (ha : Closed e a) :
    nComp e Set.univ = nComp e a + nComp e aᶜ := by
  rw [nComp, nComp, nComp, ← Set.ncard_union_eq]
  · rw [← Set.image_union, Set.union_compl_self]
  · rw [Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have : connect e y x := by
      have : x ∈ comp e y := by rw [hxy]; exact connect_refl x
      exact this
    exact hy ((ha.connect_iff this).2 hx)

theorem comp_image_closure2 (hs : ConnectSym e) (x y : α) :
    comp e '' closure e {x, y} = {comp e x, comp e y} := by
  ext c
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨z, ⟨w, hw, hzw⟩, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact Or.inl ((comp_eq_iff hs).2 hzw)
    · exact Or.inr ((comp_eq_iff hs).2 hzw)
  · rintro (rfl | rfl)
    · exact ⟨x, subset_closure _ (by simp), rfl⟩
    · exact ⟨y, subset_closure _ (by simp), rfl⟩

/-- math-comp `n_comp_closure2`, connected case. -/
theorem nComp_closure2_of_connect (hs : ConnectSym e) {x y : α} (h : connect e x y) :
    nComp e (closure e {x, y}) = 1 := by
  rw [nComp, comp_image_closure2 hs, (comp_eq_iff hs).2 h, Set.pair_eq_singleton,
    Set.ncard_singleton]

/-- math-comp `n_comp_closure2`, disconnected case. -/
theorem nComp_closure2_of_not_connect (hs : ConnectSym e) {x y : α} (h : ¬ connect e x y) :
    nComp e (closure e {x, y}) = 2 := by
  rw [nComp, comp_image_closure2 hs, Set.ncard_pair]
  exact fun h' => h ((comp_eq_iff hs).1 h')

/-- math-comp `n_comp_closure2`, as an upper bound. -/
theorem nComp_closure2_le (hs : ConnectSym e) (x y : α) : nComp e (closure e {x, y}) ≤ 2 := by
  by_cases h : connect e x y
  · rw [nComp_closure2_of_connect hs h]; omega
  · rw [nComp_closure2_of_not_connect hs h]

/-- A single component: any two points are connected. -/
theorem connect_of_nComp_eq_one (hs : ConnectSym e) {a : Set α} (h : nComp e a = 1) {x y : α}
    (hx : x ∈ a) (hy : y ∈ a) : connect e x y := by
  rw [nComp, Set.ncard_eq_one] at h
  obtain ⟨c, hc⟩ := h
  have hxc : comp e x = c := by
    have : comp e x ∈ comp e '' a := ⟨x, hx, rfl⟩
    rw [hc] at this; exact this
  have hyc : comp e y = c := by
    have : comp e y ∈ comp e '' a := ⟨y, hy, rfl⟩
    rw [hc] at this; exact this
  exact (comp_eq_iff hs).1 (hxc.trans hyc.symm)

/-- Two points in different components give at least two components. -/
theorem one_lt_nComp [Finite α] (hs : ConnectSym e) {a : Set α} {x y : α} (hx : x ∈ a) (hy : y ∈ a)
    (hxy : ¬ connect e x y) : 1 < nComp e a := by
  rw [nComp]
  have hsub : {comp e x, comp e y} ⊆ comp e '' a := by
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact ⟨x, hx, rfl⟩
    · exact ⟨y, hy, rfl⟩
  have h2 : ({comp e x, comp e y} : Set (Set α)).ncard = 2 :=
    Set.ncard_pair fun h => hxy ((comp_eq_iff hs).1 h)
  have := Set.ncard_le_ncard hsub
  omega

/-- Counting components through a "kernel": if `f` and `g` identify the same points of `s`,
then `f '' s` and `g '' s` have the same size. -/
theorem ncard_image_eq_of_ker {γ δ : Type*} {s : Set α} (f : α → γ) (g : α → δ)
    (h : ∀ x ∈ s, ∀ y ∈ s, f x = f y ↔ g x = g y) : (f '' s).ncard = (g '' s).ncard := by
  classical
  refine Set.ncard_congr (fun c hc => g (Classical.choose hc)) ?_ ?_ ?_
  · intro c hc
    exact ⟨_, (Classical.choose_spec hc).1, rfl⟩
  · intro c d hc hd hcd
    have hc' := Classical.choose_spec hc
    have hd' := Classical.choose_spec hd
    rw [← hc'.2, ← hd'.2]
    exact (h _ hc'.1 _ hd'.1).2 hcd
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
    have hc' := Classical.choose_spec (⟨x, hx, rfl⟩ : f x ∈ f '' s)
    exact (h _ hc'.1 _ hx).1 hc'.2

/-- math-comp `adjunction_n_comp`: components meeting `a` correspond to components of `e'`
meeting the preimage of `a`, when `h` identifies the two connectivity relations there. -/
theorem nComp_adjunction {e' : β → β → Prop} (hs : ConnectSym e) (hs' : ConnectSym e')
    (h : β → α) {a : Set α} (hcod : a ⊆ Set.range h)
    (hfun : ∀ x' y', h x' ∈ a → h y' ∈ a → (connect e' x' y' ↔ connect e (h x') (h y'))) :
    nComp e a = nComp e' (h ⁻¹' a) := by
  have himg : comp e '' a = (comp e ∘ h) '' (h ⁻¹' a) := by
    rw [Set.image_comp, Set.image_preimage_eq_of_subset hcod]
  rw [nComp, nComp, himg]
  apply ncard_image_eq_of_ker
  intro x hx y hy
  simp only [comp_apply]
  rw [comp_eq_iff hs, comp_eq_iff hs', hfun x y hx hy]

/-- math-comp `strict_adjunction`: an injection that matches single links on an `e`-closed
region contained in its range matches `connect` on that region. -/
theorem connect_iff_of_base {e' : β → β → Prop} {h : β → α} (hinj : Injective h)
    {a : Set α} (ha : ∀ x y, e x y → x ∈ a → y ∈ a) (hcod : a ⊆ Set.range h)
    (hbase : ∀ x' y', h x' ∈ a → (e (h x') (h y') ↔ e' x' y')) {x' y' : β} (hx : h x' ∈ a) :
    connect e' x' y' ↔ connect e (h x') (h y') := by
  constructor
  · intro hxy
    have key : ∀ z', connect e' x' z' → h z' ∈ a ∧ connect e (h x') (h z') := by
      intro z' hz
      induction hz with
      | refl => exact ⟨hx, connect_refl _⟩
      | tail _ hbc ih =>
        have hstep := (hbase _ _ ih.1).2 hbc
        exact ⟨ha _ _ hstep ih.1, connect_trans ih.2 (connect_of_rel hstep)⟩
    exact (key y' hxy).2
  · intro hxy
    have key : ∀ v, connect e (h x') v → ∀ w', h w' = v → connect e' x' w' := by
      intro v hv
      induction hv with
      | refl =>
        intro w' hw
        obtain rfl := hinj hw
        exact connect_refl _
      | tail hab hbc ih =>
        rename_i u v
        intro w' hw
        have hu : u ∈ a := mem_of_connect_of_forward ha hab hx
        obtain ⟨u', rfl⟩ := hcod hu
        have := ih u' rfl
        subst hw
        exact connect_trans this (connect_of_rel ((hbase _ _ hu).1 hbc))
    exact key _ hxy y' rfl

/-! ### Orbit size -/

/-- math-comp `order f x`: the number of points in the `f`-orbit of `x`. -/
noncomputable def order (f : α → α) (x : α) : ℕ := {y | fconnect f x y}.ncard

end FourColor
