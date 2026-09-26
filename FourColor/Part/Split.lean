/-
Copyright (c) 2026. Lean 4 port of the Coq/Rocq formal proof of the Four Color Theorem
by Georges Gonthier (math-comp/fourcolor).
Original Coq development: (c) 2006-2018 Microsoft Corporation and Inria, CeCILL-B.
-/
import FourColor.Part.Fit

/-!
# Parts: refinement  (port of `part.v`, section `FitSplitPart`)

In a pentagonal map:

* `fitp_pcons_`, `exact_fitp_pcons_`: every dart `x` fits `pcons_ n`, and exactly fits
  `pcons_ (arity x)`.
* `G.fitc i j k x` (Coq `fitc`): `k` is smaller than the arity of `i.move G (face^j x)`, which
  corresponds to sublocation `i` of subpart `j`.
* `fitp_split`: if `goodSplit i j k p`, then `x` fits `splitPart i j k lo p` iff it fits `p`
  and `lo` xor `fitc i j k x` holds.
-/

namespace FourColor

universe u

variable {D : Type u}

namespace Hypermap

variable (G : Hypermap D)

/-- Coq `fitp_pcons_`. -/
theorem fitp_pcons_ (hG : G.Pentagonal) (x : D) (n : ℕ) : G.fitp x (pcons_ n) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pcons_, Function.iterate_succ_apply']
    simp only [fitp, memRange, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hG _, hG _, ih _⟩

/-- The size of `pcons_ n`. -/
private theorem size_pcons_ (n : ℕ) : sizePart (pcons_ n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pcons_, Function.iterate_succ_apply']
    simp only [sizePart]
    rw [← pcons_, ih]

/-- Coq `exact_fitp_pcons_`. -/
theorem exact_fitp_pcons_ (hG : G.Pentagonal) (x : D) : G.exactFitp x (pcons_ (G.arity x)) := by
  simp only [exactFitp, size_pcons_, beq_self_eq_true, Bool.true_and]
  exact G.fitp_pcons_ hG x _

/-- Coq `fitc i j k x`: `k` is smaller than the arity of `i.move G (face^[j] x)`, which
corresponds to sublocation `i` of subpart `j`. -/
noncomputable def fitc (i : SubpartLoc) (j k : ℕ) (x : D) : Bool :=
  decide (k < G.arity (i.move G (G.face^[j] x)))

/-- Coq `fitp_split`. -/
theorem fitp_split (hG : G.Pentagonal) (i : SubpartLoc) (j k : ℕ) (p : Part)
    (hp : goodSplit i j k p) (lo : Bool) (x : D) :
    G.exactFitp x (splitPart i j k lo p) = ((lo ^^ G.fitc i j k x) && G.exactFitp x p) := by
  simp only [exactFitp, size_split_part]
  suffices H : G.fitp x (splitPart i j k lo p) = ((lo ^^ G.fitc i j k x) && G.fitp x p) by
    rw [H]
    cases (G.arity x == sizePart p) <;> cases (lo ^^ G.fitc i j k x) <;> rfl
  unfold fitc
  have key : ∀ (pc : Prange → Part → Part), PartUpdate.{u} pc i → ∀ (q : Part) (r : Prange),
      sizePart (dropPart j p) = sizePart (pc r q) →
      (∀ y, G.fitp y (dropPart j p) = G.fitp y (pc r q)) → goodRsplit k r →
      G.fitp x (catPart (takePart j p) (pc (splitRange k lo r) q)) =
        ((lo ^^ decide (k < G.arity (i.move G (G.face^[j] x)))) && G.fitp x p) := by
    intro pc hpc q r hsz hfit hkr
    obtain ⟨hs1, hf1⟩ := hpc r q
    obtain ⟨-, hf2⟩ := hpc (splitRange k lo r) q
    have htake : sizePart (takePart j p) = j := by
      have h1 : sizePart (takePart j p) + sizePart (dropPart j p) = sizePart p := by
        conv_rhs => rw [← cat_take_drop_part j p]
        rw [size_cat_part]
      have h2 := size_drop_part j p
      omega
    conv_rhs => rw [← cat_take_drop_part j p]
    rw [fitp_cat, fitp_cat, htake, hfit]
    have hsplit : G.fitp (G.face^[j] x) (pc (splitRange k lo r) q) =
        ((lo ^^ decide (k < G.arity (i.move G (G.face^[j] x)))) &&
          G.fitp (G.face^[j] x) (pc r q)) := by
      apply Bool.eq_iff_iff.2
      rw [Bool.and_eq_true]
      constructor
      · intro h
        obtain ⟨hr', hall⟩ := hf2 D G _ h
        rw [fit_split_range k r hkr, Bool.and_eq_true] at hr'
        exact ⟨hr'.1, hall r hr'.2⟩
      · rintro ⟨hlo, h⟩
        obtain ⟨hr, hall⟩ := hf1 D G _ h
        refine hall _ ?_
        rw [fit_split_range k r hkr, hlo, hr]
        rfl
    rw [hsplit]
    cases G.fitp x (takePart j p) <;> cases (lo ^^ decide (k < G.arity (i.move G (G.face^[j] x))))
      <;> rfl
  -- the Pcons Pr66/Pr77/Pr88 forms are refined to their fan forms
  have p59 : ∀ y, memRange .pr59 (G.arity y) = true := fun y => decide_eq_true (hG y)
  have h66 : ∀ h p' y, G.fitp y (.cons .pr66 h p') = G.fitp y (.cons6 h .pr59 p') := by
    intro h p' y
    simp only [fitp, p59, Bool.true_and]
  have h77 : ∀ h p' y, G.fitp y (.cons .pr77 h p') = G.fitp y (.cons7 h .pr59 .pr59 p') := by
    intro h p' y
    simp only [fitp, p59, Bool.true_and]
  have h88 : ∀ h p' y,
      G.fitp y (.cons .pr88 h p') = G.fitp y (.cons8 h .pr59 .pr59 .pr59 p') := by
    intro h p' y
    simp only [fitp, p59, Bool.true_and]
  unfold goodSplit at hp
  unfold splitPart
  rcases hd : dropPart j p with _ | ⟨s, h, p'⟩ | ⟨h, f1, p'⟩ | ⟨h, f1, f2, p'⟩ |
      ⟨h, f1, f2, f3, p'⟩ <;> rw [hd] at hp <;> cases i <;> simp only at hp ⊢
  all_goals try exact absurd hp Bool.false_ne_true
  · exact key _ (updatePs h) p' s (by rw [hd]) (by rw [hd]; exact fun _ => rfl) hp
  · exact key _ (updatePh s) p' h (by rw [hd]) (by rw [hd]; exact fun _ => rfl) hp
  · cases s <;> simp only at hp ⊢ <;> try exact absurd hp Bool.false_ne_true
    · exact key _ (updateP6f1 h) p' .pr59 (by rw [hd]; rfl) (by rw [hd]; exact h66 h p') hp
    · exact key _ (updateP7f1 h .pr59) p' .pr59 (by rw [hd]; rfl) (by rw [hd]; exact h77 h p')
        hp
    · exact key _ (updateP8f1 h .pr59 .pr59) p' .pr59 (by rw [hd]; rfl)
        (by rw [hd]; exact h88 h p') hp
  · cases s <;> simp only at hp ⊢ <;> try exact absurd hp Bool.false_ne_true
    · exact key _ (updateP7f2 h .pr59) p' .pr59 (by rw [hd]; rfl) (by rw [hd]; exact h77 h p')
        hp
    · exact key _ (updateP8f2 h .pr59 .pr59) p' .pr59 (by rw [hd]; rfl)
        (by rw [hd]; exact h88 h p') hp
  · cases s <;> simp only at hp ⊢ <;> try exact absurd hp Bool.false_ne_true
    · exact key _ (updateP8f3 h .pr59 .pr59) p' .pr59 (by rw [hd]; rfl)
        (by rw [hd]; exact h88 h p') hp
  · exact key _ (updateP6h f1) p' h (by rw [hd]) (by rw [hd]; exact fun _ => rfl) hp
  · exact key _ (updateP6f1 h) p' f1 (by rw [hd]) (by rw [hd]; exact fun _ => rfl) hp
  · exact key _ (updateP7h f1 f2) p' h (by rw [hd]) (by rw [hd]; exact fun _ => rfl) hp
  · exact key _ (updateP7f1 h f2) p' f1 (by rw [hd]) (by rw [hd]; exact fun _ => rfl) hp
  · exact key _ (updateP7f2 h f1) p' f2 (by rw [hd]) (by rw [hd]; exact fun _ => rfl) hp
  · exact key _ (updateP8h f1 f2 f3) p' h (by rw [hd]) (by rw [hd]; exact fun _ => rfl)
      hp
  · exact key _ (updateP8f1 h f2 f3) p' f1 (by rw [hd]) (by rw [hd]; exact fun _ => rfl)
      hp
  · exact key _ (updateP8f2 h f1 f3) p' f2 (by rw [hd]) (by rw [hd]; exact fun _ => rfl)
      hp
  · exact key _ (updateP8f3 h f1 f2) p' f3 (by rw [hd]) (by rw [hd]; exact fun _ => rfl)
      hp

end Hypermap

end FourColor
