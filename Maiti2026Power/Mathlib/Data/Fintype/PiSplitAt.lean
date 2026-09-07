/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Sums and cardinalities over dependent products, split at one coordinate

Using `Equiv.piSplitAt`, a sum over `∀ j, β j` is written as a double sum over the `i`-th
coordinate and the remaining ones (`Fintype.sum_pi_piSplitAt`), the cardinality factors
accordingly (`Fintype.card_pi_eq_mul_card_pi_subtype`), and `∑ κ, [κ i = k]` is the number of
choices of the other coordinates (`Fintype.sum_ite_apply_eq`). Summing over all the values of
one coordinate multiplies the total sum by the cardinality of that coordinate
(`Fintype.sum_sum_update`).
-/

@[expose] public section

variable {ι : Type*} [DecidableEq ι] {β : ι → Type*}

lemma Equiv.piSplitAt_symm_apply_self (i : ι) (a : β i) (r : ∀ j : {j // j ≠ i}, β j) :
    (Equiv.piSplitAt i β).symm (a, r) i = a := by
  simp

lemma Equiv.piSplitAt_symm_apply_of_ne (i : ι) (a : β i) (r : ∀ j : {j // j ≠ i}, β j) {j : ι}
    (hj : j ≠ i) :
    (Equiv.piSplitAt i β).symm (a, r) j = r ⟨j, hj⟩ := by
  simp [hj]

variable [Fintype ι] [∀ i, Fintype (β i)]

/-- Splitting a sum over `∀ j, β j` according to the `i`-th coordinate. -/
lemma Fintype.sum_pi_piSplitAt {M : Type*} [AddCommMonoid M] (i : ι) (F : (∀ j, β j) → M) :
    ∑ κ, F κ = ∑ a : β i, ∑ r : ∀ j : {j // j ≠ i}, β j, F ((Equiv.piSplitAt i β).symm (a, r)) := by
  rw [← Equiv.sum_comp (Equiv.piSplitAt i β).symm, Fintype.sum_prod_type]

/-- Summing a function of a dependent product over all values of its `i`-th coordinate multiplies
the total sum by the cardinality of `β i`: the map `(κ, a) ↦ (update κ i a, κ i)` is an
involution of `(∀ j, β j) × β i`. -/
lemma Fintype.sum_sum_update {R : Type*} [NonAssocSemiring R] (i : ι) (F : (∀ j, β j) → R) :
    ∑ κ : ∀ j, β j, ∑ a : β i, F (Function.update κ i a) =
      Fintype.card (β i) * ∑ κ : ∀ j, β j, F κ := by
  have hΦ : Function.Involutive
      (fun p : (∀ j, β j) × β i ↦ (Function.update p.1 i p.2, p.1 i)) := by
    rintro ⟨κ, a⟩
    simp [Function.update_idem, Function.update_eq_self]
  calc ∑ κ : ∀ j, β j, ∑ a : β i, F (Function.update κ i a)
      = ∑ p : (∀ j, β j) × β i, F (Function.update p.1 i p.2) :=
        (Fintype.sum_prod_type fun p : (∀ j, β j) × β i ↦ F (Function.update p.1 i p.2)).symm
    _ = ∑ p : (∀ j, β j) × β i, F p.1 :=
        Fintype.sum_bijective _ hΦ.bijective _ _ fun _ ↦ rfl
    _ = Fintype.card (β i) * ∑ κ : ∀ j, β j, F κ := by
        rw [Fintype.sum_prod_type, Finset.mul_sum]
        refine Finset.sum_congr rfl fun κ _ ↦ ?_
        change ∑ _y : β i, F κ = _
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

lemma Fintype.card_pi_eq_mul_card_pi_subtype (i : ι) :
    Fintype.card (∀ j, β j) = Fintype.card (β i) * Fintype.card (∀ j : {j // j ≠ i}, β j) := by
  rw [Fintype.card_congr (Equiv.piSplitAt i β), Fintype.card_prod]

/-- `∑ κ, [κ i = k] = |∀ j ≠ i, β j|`. -/
lemma Fintype.sum_ite_apply_eq {R : Type*} [Semiring R] (i : ι) [DecidableEq (β i)] (k : β i) :
    (∑ κ : ∀ j, β j, if k = κ i then (1 : R) else 0) =
      Fintype.card (∀ j : {j // j ≠ i}, β j) := by
  rw [Fintype.sum_pi_piSplitAt i]
  simp only [Equiv.piSplitAt_symm_apply_self, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_ite, mul_one, mul_zero]
  simp
