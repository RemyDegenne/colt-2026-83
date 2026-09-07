/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.Mathlib.Matrix.HermitianCFC

/-!
# Trace of the inverse: AM–HM

For a positive definite real matrix `A` with eigenvalues `λ i`, the trace of `A⁻¹` is
`∑ i, (λ i)⁻¹` (`Matrix.PosDef.trace_inv_eq_sum_inv_eigenvalues`), and the arithmetic–harmonic
mean inequality (a special case of Cauchy–Schwarz) between the eigenvalues gives

* `Matrix.PosDef.card_sq_le_trace_mul_trace_inv`: `(card n) ^ 2 ≤ tr A * tr A⁻¹`;
* `Matrix.PosDef.card_sq_div_trace_le_trace_inv`: `(card n) ^ 2 / tr A ≤ tr A⁻¹`.
-/

@[expose] public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℝ}

/-- The trace of the inverse of a positive definite real matrix is the sum of the inverses of its
eigenvalues. -/
lemma PosDef.trace_inv_eq_sum_inv_eigenvalues (hA : A.PosDef) :
    A⁻¹.trace = ∑ i, (hA.1.eigenvalues i)⁻¹ := by
  simpa using hA.1.trace_inv_sub_smul_one fun x hx ↦ (hA.pos_of_mem_spectrum hx).ne'

/-- **AM–HM for the trace**: `(card n)² ≤ tr A · tr A⁻¹` for a positive definite real matrix. -/
lemma PosDef.card_sq_le_trace_mul_trace_inv (hA : A.PosDef) :
    (Fintype.card n : ℝ) ^ 2 ≤ A.trace * A⁻¹.trace := by
  rw [hA.trace_inv_eq_sum_inv_eigenvalues, hA.1.trace_eq_sum_eigenvalues]
  simpa using Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ (r := fun _ ↦ (1 : ℝ))
    (f := hA.1.eigenvalues) (g := fun i ↦ (hA.1.eigenvalues i)⁻¹)
    (fun i _ ↦ (hA.eigenvalues_pos i).le) (fun i _ ↦ (inv_pos.2 (hA.eigenvalues_pos i)).le)
    fun i _ ↦ by simp [(hA.eigenvalues_pos i).ne']

/-- `tr A⁻¹ ≥ (card n)² / tr A` for a positive definite real matrix (with `0 / 0 = 0` when `n`
is empty). -/
lemma PosDef.card_sq_div_trace_le_trace_inv (hA : A.PosDef) :
    (Fintype.card n : ℝ) ^ 2 / A.trace ≤ A⁻¹.trace := by
  rw [hA.trace_inv_eq_sum_inv_eigenvalues, hA.1.trace_eq_sum_eigenvalues]
  simpa using Finset.sq_sum_div_le_sum_sq_div Finset.univ (fun _ ↦ (1 : ℝ))
    fun i _ ↦ hA.eigenvalues_pos i

end Matrix
