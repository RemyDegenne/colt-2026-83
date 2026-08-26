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
choices of the other coordinates (`Fintype.sum_ite_apply_eq`).
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
