/-
Copyright (c) 2026. Lean 4 port of the planarity part of the Coq/Rocq formal proof
of the Four Color Theorem by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Infix
import Mathlib.Data.List.Perm.Basic

/-!
# Sequence and path utilities

This file provides the small fragment of math-comp's `seq.v` and `path.v` libraries that the
hypermap / Walkup / Jordan development relies on.  The definitions follow the math-comp ones
literally, so that the ported proofs can use the same decompositions:

* `last x p`   : the last item of `x :: p`                       (math-comp `last`)
* `belast x p` : `x :: p` without its last item                  (math-comp `belast`)
* `path e x p` : `e` holds between consecutive items of `x :: p` (math-comp `path`)
* `cycle e p`  : `path e` closed back to the head of `p`         (math-comp `cycle`)
* `mem2 s x y` : `y` occurs in `s` at or after an occurrence of `x` (math-comp `mem2`)

Membership-closed "uniq" (`List.Nodup`), `subseq` (`List.Sublist`) and `has` (`∃ x ∈ s, _`)
are taken from core/Mathlib.
-/

namespace FourColor

variable {α β : Type*}

/-! ### `last` and `belast` -/

/-- `last x p` is the last item of the sequence `x :: p` (math-comp `last`). -/
def last : α → List α → α
  | x, [] => x
  | _, y :: p => last y p

@[simp] theorem last_nil (x : α) : last x [] = x := rfl

@[simp] theorem last_cons (x y : α) (p : List α) : last x (y :: p) = last y p := rfl

theorem last_append (x : α) (p q : List α) : last x (p ++ q) = last (last x p) q := by
  induction p generalizing x with
  | nil => rfl
  | cons y p ih => exact ih y

@[simp] theorem last_concat (x y : α) (p : List α) : last x (p ++ [y]) = y := by
  rw [last_append]; rfl

theorem last_map (f : α → β) (x : α) (p : List α) : last (f x) (p.map f) = f (last x p) := by
  induction p generalizing x with
  | nil => rfl
  | cons y p ih => exact ih y

theorem mem_last (x : α) (p : List α) : last x p ∈ x :: p := by
  induction p generalizing x with
  | nil => simp
  | cons y p ih => exact List.mem_cons_of_mem _ (ih y)

theorem last_mem_of_ne_nil (x : α) {p : List α} (hp : p ≠ []) : last x p ∈ p := by
  cases p with
  | nil => exact absurd rfl hp
  | cons y p => exact mem_last y p

/-- `belast x p` is `x :: p` with its last item removed (math-comp `belast`). -/
def belast : α → List α → List α
  | _, [] => []
  | x, y :: p => x :: belast y p

@[simp] theorem belast_nil (x : α) : belast x [] = [] := rfl

@[simp] theorem belast_cons (x y : α) (p : List α) : belast x (y :: p) = x :: belast y p := rfl

/-- math-comp `lastI`. -/
theorem lastI (x : α) (p : List α) : x :: p = belast x p ++ [last x p] := by
  induction p generalizing x with
  | nil => rfl
  | cons y p ih => rw [belast_cons, last_cons, List.cons_append, ← ih y]

theorem belast_append (x : α) (p q : List α) :
    belast x (p ++ q) = belast x p ++ belast (last x p) q := by
  induction p generalizing x with
  | nil => rfl
  | cons y p ih => simp only [List.cons_append, belast_cons, last_cons, ih y]

@[simp] theorem belast_concat (x y : α) (p : List α) : belast x (p ++ [y]) = x :: p := by
  induction p generalizing x with
  | nil => rfl
  | cons z p ih => simp only [List.cons_append, belast_cons, ih z]

theorem mem_belast {x y : α} {p : List α} (h : y ∈ belast x p) : y ∈ x :: p := by
  induction p generalizing x with
  | nil => simp at h
  | cons z p ih =>
    simp only [belast_cons, List.mem_cons] at h
    rcases h with h | h
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem belast_map (f : α → β) (x : α) (p : List α) :
    belast (f x) (p.map f) = (belast x p).map f := by
  induction p generalizing x with
  | nil => rfl
  | cons y p ih => simp only [List.map_cons, belast_cons, ih y]

theorem length_belast (x : α) (p : List α) : (belast x p).length = p.length := by
  induction p generalizing x with
  | nil => rfl
  | cons y p ih => simp only [belast_cons, List.length_cons, ih y]

theorem mem_of_mem_belast_ne {x y : α} {p : List α} (h : y ∈ belast x p) (hx : y ≠ x) :
    y ∈ p := by
  have := mem_belast h
  simp only [List.mem_cons] at this
  exact this.resolve_left hx

/-- math-comp `splitPl`: split `p` after an occurrence of `y` in `x :: p`. -/
theorem splitPl {x y : α} {p : List α} (h : y ∈ x :: p) :
    ∃ p₁ p₂, p = p₁ ++ p₂ ∧ last x p₁ = y := by
  induction p generalizing x with
  | nil =>
    simp only [List.mem_singleton] at h
    exact ⟨[], [], rfl, h.symm⟩
  | cons z p ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨[], z :: p, rfl, rfl⟩
    · obtain ⟨p₁, p₂, rfl, hl⟩ := ih (List.mem_cons.2 h)
      exact ⟨z :: p₁, p₂, rfl, hl⟩

/-- math-comp `splitPr` (core `List.append_of_mem`). -/
theorem splitPr {y : α} {p : List α} (h : y ∈ p) : ∃ p₁ p₂, p = p₁ ++ y :: p₂ :=
  List.append_of_mem h

/-! ### Paths -/

/-- `path e x p` : `e` relates each item of `x :: p` to the next one (math-comp `path`). -/
def path (e : α → α → Prop) : α → List α → Prop
  | _, [] => True
  | x, y :: p => e x y ∧ path e y p

variable {e e' : α → α → Prop}

@[simp] theorem path_nil (e : α → α → Prop) (x : α) : path e x [] ↔ True := Iff.rfl

@[simp] theorem path_cons (e : α → α → Prop) (x y : α) (p : List α) :
    path e x (y :: p) ↔ e x y ∧ path e y p := Iff.rfl

/-- math-comp `cat_path`. -/
theorem path_append {x : α} {p q : List α} :
    path e x (p ++ q) ↔ path e x p ∧ path e (last x p) q := by
  induction p generalizing x with
  | nil => simp
  | cons y p ih => simp only [List.cons_append, path_cons, ih, last_cons, and_assoc]

/-- math-comp `rcons_path`. -/
theorem path_concat {x y : α} {p : List α} :
    path e x (p ++ [y]) ↔ path e x p ∧ e (last x p) y := by
  simp [path_append]

theorem path_map {f : β → α} {x : β} {p : List β} :
    path e (f x) (p.map f) ↔ path (fun a b => e (f a) (f b)) x p := by
  induction p generalizing x with
  | nil => simp
  | cons y p ih => simp only [List.map_cons, path_cons, ih]

/-- math-comp `sub_path`. -/
theorem path.mono (h : ∀ a b, e a b → e' a b) {x : α} {p : List α} (hp : path e x p) :
    path e' x p := by
  induction p generalizing x with
  | nil => trivial
  | cons y p ih => exact ⟨h _ _ hp.1, ih hp.2⟩

/-- math-comp `eq_path`. -/
theorem path_congr (h : ∀ a b, e a b ↔ e' a b) {x : α} {p : List α} :
    path e x p ↔ path e' x p :=
  ⟨path.mono fun a b => (h a b).1, path.mono fun a b => (h a b).2⟩

/-- A `path` version of `sub_path` restricted to the items actually visited. -/
theorem path.mono_mem {x : α} {p : List α}
    (h : ∀ a b, a ∈ x :: p → b ∈ p → e a b → e' a b) (hp : path e x p) : path e' x p := by
  induction p generalizing x with
  | nil => trivial
  | cons y p ih =>
    refine ⟨h _ _ List.mem_cons_self List.mem_cons_self hp.1, ih ?_ hp.2⟩
    intro a b ha hb
    exact h a b (List.mem_cons_of_mem _ ha) (List.mem_cons_of_mem _ hb)

/-- math-comp `map_path`, specialised to a "base" hypothesis: `e` on the image of `h`
coincides with `e'` except at the points of `b`, which must not be left by the path. -/
theorem path_map_base {h : β → α} {e' : β → β → Prop} {b : α → Prop}
    (hb : ∀ x y, ¬ b (h x) → (e (h x) (h y) ↔ e' x y)) {x : β} {p : List β}
    (hp : ∀ y ∈ belast x p, ¬ b (h y)) : path e (h x) (p.map h) ↔ path e' x p := by
  induction p generalizing x with
  | nil => simp
  | cons y p ih =>
    simp only [belast_cons, List.mem_cons, forall_eq_or_imp] at hp
    simp only [List.map_cons, path_cons, hb x y hp.1, ih hp.2]

/-- Split a path at an intermediate point. -/
theorem path.of_append_cons {x y : α} {p q : List α} (h : path e x (p ++ y :: q)) :
    path e y q := by
  rw [path_append] at h
  exact h.2.2

/-- If `x₀ :: l = r₁ ++ y :: r₂` and `path e x₀ l`, then `path e y r₂`. -/
theorem path.of_cons_eq_append {x₀ y : α} {l r₁ r₂ : List α} (hl : path e x₀ l)
    (h : x₀ :: l = r₁ ++ y :: r₂) : path e y r₂ := by
  cases r₁ with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hl
  | cons a r₁ =>
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact path.of_append_cons hl

theorem last_last_belast_reverse (y : α) (p : List α) :
    last (last y p) (belast y p).reverse = y := by
  cases p with
  | nil => rfl
  | cons z p => simp

/-- math-comp `rev_path`. -/
theorem path_reverse {x : α} {p : List α} :
    path e (last x p) (belast x p).reverse ↔ path (fun a b => e b a) x p := by
  induction p generalizing x with
  | nil => simp
  | cons y p ih =>
    simp only [last_cons, belast_cons, List.reverse_cons, path_concat, path_cons, ih,
      last_last_belast_reverse]
    exact and_comm

/-- Sub-path extraction. -/
theorem path.take_of_append {x : α} {p q : List α} (h : path e x (p ++ q)) : path e x p :=
  (path_append.1 h).1

/-- math-comp `path_connect`-style membership lemma for relation-closed predicates:
every item of a path starting in `a` stays in `a` if `e` preserves `a`. -/
theorem path.mem_of_closed {a : α → Prop} (ha : ∀ u v, e u v → a u → a v) {x : α}
    {p : List α} (hp : path e x p) (hx : a x) : ∀ y ∈ p, a y := by
  induction p generalizing x with
  | nil => simp
  | cons y p ih =>
    intro w hw
    have hy : a y := ha _ _ hp.1 hx
    simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · exact hy
    · exact ih hp.2 hy w hw

theorem last_eq_of_cons_eq_append {x₀ x : α} {s s₁ s₂ : List α}
    (h : x₀ :: s = s₁ ++ x :: s₂) : last x₀ s = last x s₂ := by
  induction s₁ generalizing x₀ s with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | cons a s₁ ih =>
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases s₁ with
    | nil => rfl
    | cons b s₁ => rw [List.cons_append, last_cons]; exact ih rfl

/-! ### Cycles -/

/-- `cycle e p` : `e` relates each item of `p` to the next one, cyclically
(math-comp `cycle`). -/
def cycle (e : α → α → Prop) : List α → Prop
  | [] => True
  | x :: p => path e x (p ++ [x])

@[simp] theorem cycle_nil (e : α → α → Prop) : cycle e [] ↔ True := Iff.rfl

theorem cycle_cons (e : α → α → Prop) (x : α) (p : List α) :
    cycle e (x :: p) ↔ path e x (p ++ [x]) := Iff.rfl

/-- math-comp `cycle_path`. -/
theorem cycle_iff_path (x₀ : α) (p : List α) : cycle e p ↔ path e (last x₀ p) p := by
  cases p with
  | nil => simp
  | cons x p =>
    rw [cycle_cons, path_concat, last_cons, path_cons]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩

/-- In an `e`-cycle, every item has an `e`-successor in the cycle. -/
theorem cycle.exists_succ {p : List α} (hp : cycle e p) {x : α} (hx : x ∈ p) :
    ∃ y ∈ p, e x y := by
  cases p with
  | nil => simp at hx
  | cons x₀ p =>
    rw [cycle_cons] at hp
    have key : ∀ (a : α) (l : List α), path e a (l ++ [x₀]) → ∀ u ∈ a :: l,
        ∃ v ∈ l ++ [x₀], e u v := by
      intro a l
      induction l generalizing a with
      | nil =>
        intro h u hu
        simp only [List.mem_singleton] at hu
        subst hu
        exact ⟨x₀, by simp, h.1⟩
      | cons b l ih =>
        intro h u hu
        simp only [List.mem_cons] at hu
        rcases hu with rfl | hu
        · exact ⟨b, by simp, h.1⟩
        · obtain ⟨v, hv, huv⟩ := ih b h.2 u (List.mem_cons.2 hu)
          exact ⟨v, by simp only [List.cons_append, List.mem_cons]; right; exact hv, huv⟩
    obtain ⟨v, hv, huv⟩ := key x₀ p hp x hx
    refine ⟨v, ?_, huv⟩
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · exact List.mem_cons_of_mem _ hv
    · exact List.mem_cons_self

/-! ### `mem2` -/

/-- `mem2 s x y` : `y` occurs in `s` at or after the first occurrence of `x`
(math-comp `mem2`; the disjunctive definition is equivalent to math-comp's
`y \in drop (index x s) s`). -/
def mem2 : List α → α → α → Prop
  | [], _, _ => False
  | a :: s, x, y => (a = x ∧ y ∈ a :: s) ∨ mem2 s x y

@[simp] theorem mem2_nil (x y : α) : mem2 [] x y ↔ False := Iff.rfl

theorem mem2_cons {a x y : α} {s : List α} :
    mem2 (a :: s) x y ↔ (a = x ∧ y ∈ a :: s) ∨ mem2 s x y := Iff.rfl

theorem mem2l {s : List α} {x y : α} (h : mem2 s x y) : x ∈ s := by
  induction s with
  | nil => exact h.elim
  | cons a s ih =>
    rcases h with ⟨rfl, _⟩ | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

theorem mem2r {s : List α} {x y : α} (h : mem2 s x y) : y ∈ s := by
  induction s with
  | nil => exact h.elim
  | cons a s ih =>
    rcases h with ⟨_, h⟩ | h
    · exact h
    · exact List.mem_cons_of_mem _ (ih h)

theorem mem2_cons_self {a y : α} {s : List α} : mem2 (a :: s) a y ↔ y ∈ a :: s :=
  ⟨fun h => mem2r h, fun h => Or.inl ⟨rfl, h⟩⟩

theorem mem2_cons_of_ne {a x y : α} {s : List α} (h : a ≠ x) :
    mem2 (a :: s) x y ↔ mem2 s x y := by
  rw [mem2_cons]; simp [h]

/-- math-comp `splitP2r`, as a characterization of `mem2`. -/
theorem mem2_iff {s : List α} {x y : α} :
    mem2 s x y ↔ ∃ s₁ s₂, s = s₁ ++ x :: s₂ ∧ y ∈ x :: s₂ := by
  constructor
  · intro h
    induction s with
    | nil => exact h.elim
    | cons a s ih =>
      rcases h with ⟨rfl, hy⟩ | h
      · exact ⟨[], s, rfl, hy⟩
      · obtain ⟨s₁, s₂, rfl, hy⟩ := ih h
        exact ⟨a :: s₁, s₂, rfl, hy⟩
  · rintro ⟨s₁, s₂, rfl, hy⟩
    induction s₁ with
    | nil => exact Or.inl ⟨rfl, hy⟩
    | cons a s₁ ih => exact Or.inr ih

theorem mem2_append {s₁ s₂ : List α} {x y : α} :
    mem2 (s₁ ++ s₂) x y ↔ mem2 s₁ x y ∨ (x ∈ s₁ ∧ y ∈ s₂) ∨ mem2 s₂ x y := by
  induction s₁ with
  | nil => simp
  | cons a s₁ ih =>
    rw [List.cons_append, mem2_cons, ih, mem2_cons]
    simp only [List.mem_cons, List.mem_append]
    constructor
    · rintro (⟨rfl, h | h | h⟩ | h | ⟨hx, hy⟩ | h)
      · exact Or.inl (Or.inl ⟨rfl, Or.inl h⟩)
      · exact Or.inl (Or.inl ⟨rfl, Or.inr h⟩)
      · exact Or.inr (Or.inl ⟨Or.inl rfl, h⟩)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (Or.inl ⟨Or.inr hx, hy⟩)
      · exact Or.inr (Or.inr h)
    · rintro ((⟨rfl, h | h⟩ | h) | ⟨rfl | hx, hy⟩ | h)
      · exact Or.inl ⟨rfl, Or.inl h⟩
      · exact Or.inl ⟨rfl, Or.inr (Or.inl h)⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inl ⟨rfl, Or.inr (Or.inr hy)⟩
      · exact Or.inr (Or.inr (Or.inl ⟨hx, hy⟩))
      · exact Or.inr (Or.inr (Or.inr h))

theorem mem2_singleton {a x y : α} : mem2 [a] x y ↔ x = a ∧ y = a := by
  simp only [mem2_cons, List.mem_singleton, mem2_nil, or_false]
  constructor
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩

/-- math-comp `mem2_last`. -/
theorem mem2_last {x₀ x : α} {s : List α} : mem2 (x₀ :: s) x (last x₀ s) ↔ x ∈ x₀ :: s := by
  refine ⟨mem2l, fun hx => ?_⟩
  obtain ⟨s₁, s₂, h⟩ := List.append_of_mem hx
  rw [mem2_iff]
  exact ⟨s₁, s₂, h, by rw [last_eq_of_cons_eq_append h]; exact mem_last x s₂⟩

/-- math-comp `mem2l_cat`. -/
theorem mem2l_append {s₁ s₂ : List α} {x y : α} (hx : x ∉ s₁) :
    mem2 (s₁ ++ s₂) x y ↔ mem2 s₂ x y := by
  rw [mem2_append]
  constructor
  · rintro (h | ⟨h, _⟩ | h)
    · exact absurd (mem2l h) hx
    · exact absurd h hx
    · exact h
  · exact fun h => Or.inr (Or.inr h)

/-- math-comp `mem2r_cat`. -/
theorem mem2r_append {s₁ s₂ : List α} {x y : α} (hy : y ∉ s₂) :
    mem2 (s₁ ++ s₂) x y ↔ mem2 s₁ x y := by
  rw [mem2_append]
  constructor
  · rintro (h | ⟨_, h⟩ | h)
    · exact h
    · exact absurd h hy
    · exact absurd (mem2r h) hy
  · exact fun h => Or.inl h

/-- math-comp `mem2lr_splice`. -/
theorem mem2lr_splice {s₁ s₂ s₃ : List α} {x y : α} (hx : x ∉ s₂) (hy : y ∉ s₂) :
    mem2 (s₁ ++ s₂ ++ s₃) x y ↔ mem2 (s₁ ++ s₃) x y := by
  rw [List.append_assoc, mem2_append, mem2l_append hx, mem2_append (s₁ := s₁)]
  simp only [List.mem_append, hy, false_or]

/-- math-comp `mem2_splice`. -/
theorem mem2_splice {s₁ s₂ s₃ : List α} {x y : α} (h : mem2 (s₁ ++ s₃) x y) :
    mem2 (s₁ ++ s₂ ++ s₃) x y := by
  rw [List.append_assoc, mem2_append, mem2_append]
  rw [mem2_append] at h
  simp only [List.mem_append]
  rcases h with h | ⟨hx, hy⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨hx, Or.inr hy⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

/-- math-comp `mem2_splice1`. -/
theorem mem2_splice1 {s₁ s₃ : List α} {x y z : α} (h : mem2 (s₁ ++ s₃) x y) :
    mem2 (s₁ ++ z :: s₃) x y := by
  have := mem2_splice (s₂ := [z]) h
  simpa using this

theorem mem2_map {f : α → β} (hf : Function.Injective f) {s : List α} {x y : α} :
    mem2 (s.map f) (f x) (f y) ↔ mem2 s x y := by
  induction s with
  | nil => simp
  | cons a s ih =>
    simp only [List.map_cons, mem2_cons, ih, hf.eq_iff]
    rw [← List.map_cons, List.mem_map_of_injective hf]

/-- The concatenation `s₁ ++ s₂` is `mem2`-related from the head of `s₁`... -/
theorem mem2_append_of_mem {s₁ s₂ : List α} {x y : α} (hx : x ∈ s₁) (hy : y ∈ s₂) :
    mem2 (s₁ ++ s₂) x y :=
  mem2_append.2 (Or.inr (Or.inl ⟨hx, hy⟩))

/-! ### Shortening paths -/

/-- math-comp `shortenP`: any path can be shortened to a duplicate-free path with the
same endpoints, visiting only items of the original path. -/
theorem shortenP {x : α} {p : List α} (hp : path e x p) :
    ∃ p', path e x p' ∧ (x :: p').Nodup ∧ (∀ y ∈ p', y ∈ p) ∧ last x p' = last x p := by
  induction p generalizing x with
  | nil => exact ⟨[], trivial, List.nodup_singleton x, by simp, rfl⟩
  | cons y q ih =>
    obtain ⟨q', hq'p, hq'u, hq'sub, hq'l⟩ := ih hp.2
    by_cases hx : x ∈ y :: q'
    · obtain ⟨r₁, r₂, hr⟩ := List.append_of_mem hx
      refine ⟨r₂, ?_, ?_, ?_, ?_⟩
      · exact path.of_cons_eq_append hq'p hr
      · rw [hr] at hq'u
        exact hq'u.sublist (List.sublist_append_right _ _)
      · intro w hw
        have : w ∈ y :: q' := by rw [hr]; simp [hw]
        simp only [List.mem_cons] at this ⊢
        rcases this with h | h
        · exact Or.inl h
        · exact Or.inr (hq'sub w h)
      · rw [last_cons, ← hq'l, last_eq_of_cons_eq_append hr]
    · refine ⟨y :: q', ⟨hp.1, hq'p⟩, List.nodup_cons.2 ⟨hx, hq'u⟩, ?_, hq'l⟩
      intro w hw
      simp only [List.mem_cons] at hw ⊢
      rcases hw with h | h
      · exact Or.inl h
      · exact Or.inr (hq'sub w h)

end FourColor
