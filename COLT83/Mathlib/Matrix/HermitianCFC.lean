/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Traces, inverses and positivity of functions of a Hermitian matrix

For a Hermitian matrix `A` with eigenvalues `λ i`, the continuous functional calculus gives
`cfc f A = U diag(f (λ i)) U*`. We record:

* `Matrix.IsHermitian.trace_cfc`: `tr (cfc f A) = ∑ i, f (λ i)`;
* for a real symmetric matrix `B` and `l : ℝ`: `B - l • 1 = cfc (· - l) B`
  (`Matrix.IsHermitian.sub_smul_one_eq_cfc`), its inverse is `cfc (· - l)⁻¹ B` when `l` is not in
  the spectrum (`Matrix.IsHermitian.inv_sub_smul_one_eq_cfc`), the traces of that inverse and of
  its square are the sums `∑ i, (λ i - l)⁻¹` and `∑ i, (λ i - l)⁻¹ ^ 2`
  (`Matrix.IsHermitian.trace_inv_sub_smul_one`, `Matrix.IsHermitian.trace_inv_sub_smul_one_sq`);
* `B - l • 1` is positive semidefinite iff `l ≤ x` on the spectrum, and positive definite iff
  `l < x` on the spectrum (`Matrix.IsHermitian.posSemidef_sub_smul_one_iff`,
  `Matrix.IsHermitian.posDef_sub_smul_one_iff`); in Loewner terms, `l • 1 ≤ B` iff `l ≤ x` on the
  spectrum (`Matrix.IsHermitian.smul_one_le_iff`).

Together these express "the smallest eigenvalue of `B` is larger than `l`" as the spectral
condition `∀ x ∈ spectrum ℝ B, l < x`, without choosing an ordering of the eigenvalues.
-/

@[expose] public section

open scoped MatrixOrder ComplexOrder

namespace Matrix

section RCLike

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

/-- The trace of `cfc f A` is the sum of `f` over the eigenvalues of the Hermitian matrix `A`. -/
lemma IsHermitian.trace_cfc (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, (f (hA.eigenvalues i) : 𝕜) := by
  rw [hA.cfc_eq, IsHermitian.cfc, Unitary.conjStarAlgAut_apply, trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, trace_diagonal]
  rfl

/-- Every real function is continuous on the (finite) spectrum of a matrix. -/
lemma continuousOn_spectrum_real (A : Matrix n n 𝕜) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ A) :=
  A.finite_real_spectrum.continuousOn f

/-- A positive definite matrix has positive real spectrum. -/
lemma PosDef.pos_of_mem_spectrum (hA : A.PosDef) {x : ℝ} (hx : x ∈ spectrum ℝ A) : 0 < x := by
  rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact hA.eigenvalues_pos i

end RCLike

section real

variable {n : Type*} [Fintype n] [DecidableEq n] {B : Matrix n n ℝ} {l : ℝ}

/-- The trace of `cfc f B` is the sum of `f` over the eigenvalues of the symmetric matrix `B`. -/
lemma IsHermitian.trace_cfc_real (hB : B.IsHermitian) (f : ℝ → ℝ) :
    (cfc f B).trace = ∑ i, f (hB.eigenvalues i) := by
  simpa using hB.trace_cfc f

/-- `B - l • 1 = cfc (· - l) B` for a symmetric matrix `B`. -/
lemma IsHermitian.sub_smul_one_eq_cfc (hB : B.IsHermitian) (l : ℝ) :
    B - l • 1 = cfc (fun x ↦ x - l) B := by
  rw [cfc_sub _ _ B (continuousOn_spectrum_real _ _) (continuousOn_spectrum_real _ _), cfc_id' ℝ B,
    cfc_const l B, Algebra.algebraMap_eq_smul_one]

/-- `(B - l • 1)⁻¹ = cfc (· - l)⁻¹ B` for a symmetric matrix `B` and `l` outside its
spectrum. -/
lemma IsHermitian.inv_sub_smul_one_eq_cfc (hB : B.IsHermitian) (hl : ∀ x ∈ spectrum ℝ B, x ≠ l) :
    (B - l • 1)⁻¹ = cfc (fun x ↦ (x - l)⁻¹) B := by
  rw [hB.sub_smul_one_eq_cfc, nonsing_inv_eq_ringInverse,
    ← cfc_inv (a := B) (f := fun x ↦ x - l) (fun x hx ↦ sub_ne_zero.2 (hl x hx))
      (continuousOn_spectrum_real _ _) hB.isSelfAdjoint]

/-- `tr (B - l • 1)⁻¹ = ∑ i, (λ i - l)⁻¹` for a symmetric matrix `B` with eigenvalues `λ i` and
`l` outside its spectrum. -/
lemma IsHermitian.trace_inv_sub_smul_one (hB : B.IsHermitian)
    (hl : ∀ x ∈ spectrum ℝ B, x ≠ l) :
    (B - l • 1)⁻¹.trace = ∑ i, (hB.eigenvalues i - l)⁻¹ := by
  rw [hB.inv_sub_smul_one_eq_cfc hl, hB.trace_cfc_real]

/-- `tr ((B - l • 1)⁻¹ * (B - l • 1)⁻¹) = ∑ i, (λ i - l)⁻¹ ^ 2` for a symmetric matrix `B` with
eigenvalues `λ i` and `l` outside its spectrum. -/
lemma IsHermitian.trace_inv_sub_smul_one_sq (hB : B.IsHermitian)
    (hl : ∀ x ∈ spectrum ℝ B, x ≠ l) :
    ((B - l • 1)⁻¹ * (B - l • 1)⁻¹).trace = ∑ i, (hB.eigenvalues i - l)⁻¹ ^ 2 := by
  rw [hB.inv_sub_smul_one_eq_cfc hl, ← cfc_mul _ _ B (continuousOn_spectrum_real _ _)
    (continuousOn_spectrum_real _ _), hB.trace_cfc_real]
  simp_rw [sq]

/-- `B - l • 1` is positive semidefinite iff `l ≤ x` for every `x` in the spectrum of the
symmetric matrix `B`. -/
lemma IsHermitian.posSemidef_sub_smul_one_iff (hB : B.IsHermitian) :
    (B - l • 1).PosSemidef ↔ ∀ x ∈ spectrum ℝ B, l ≤ x := by
  rw [← nonneg_iff_posSemidef, hB.sub_smul_one_eq_cfc, ← cfc_zero ℝ B,
    cfc_le_iff _ _ B (continuousOn_spectrum_real _ _) (continuousOn_spectrum_real _ _)]
  simp

/-- `l • 1 ≤ B` (Loewner order) iff `l ≤ x` for every `x` in the spectrum of the symmetric
matrix `B`. -/
lemma IsHermitian.smul_one_le_iff (hB : B.IsHermitian) :
    l • 1 ≤ B ↔ ∀ x ∈ spectrum ℝ B, l ≤ x := by
  rw [le_iff, hB.posSemidef_sub_smul_one_iff]

/-- `B - l • 1` is positive definite iff `l < x` for every `x` in the spectrum of the symmetric
matrix `B`. -/
lemma IsHermitian.posDef_sub_smul_one_iff (hB : B.IsHermitian) :
    (B - l • 1).PosDef ↔ ∀ x ∈ spectrum ℝ B, l < x := by
  constructor
  · intro h x hx
    have hx' : x - l ∈ spectrum ℝ (B - l • 1) := by
      rw [hB.sub_smul_one_eq_cfc, cfc_map_spectrum _ B hB.isSelfAdjoint
        (continuousOn_spectrum_real _ _)]
      exact ⟨x, hx, rfl⟩
    exact sub_pos.1 (h.pos_of_mem_spectrum hx')
  · intro h
    refine (hB.posSemidef_sub_smul_one_iff.2 fun x hx ↦ (h x hx).le).posDef_iff_isUnit.2 ?_
    rw [hB.sub_smul_one_eq_cfc, isUnit_cfc_iff _ B (continuousOn_spectrum_real _ _)]
    exact fun x hx ↦ sub_ne_zero.2 (h x hx).ne'

end real

end Matrix
