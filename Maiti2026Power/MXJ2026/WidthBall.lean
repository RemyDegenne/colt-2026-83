/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.MXJ2026.UnitBall
public import Maiti2026Power.MXJ2026.WidthBounds
public import Maiti2026Power.Mathlib.Probability.GaussianAbsMoment

/-!
# The Gaussian width of the unit ball

For a positive definite matrix `A`, the width of the unit ball for `A` is `E‖Y‖` with
`Y ~ N(0, A⁻¹)` (`gwMat_unitBall`), and it is at least `√(2/π) d / √(tr A)`
(`le_gwMat_unitBall`): with the weights `cᵢ = √(Aᵢᵢ / tr A)`, `E‖Y‖ ≥ √(2/π) ∑ᵢ cᵢ √((A⁻¹)ᵢᵢ)`
(`sum_mul_sqrt_diag_le_integral_norm_multivariateGaussian`) and `Aᵢᵢ (A⁻¹)ᵢᵢ ≥ 1`
(`one_le_sqrt_diag_mul_sqrt_diag_inv`, Cauchy–Schwarz for `⟪A^{1/2} eᵢ, A^{-1/2} eᵢ⟫ = 1`).
Since the design matrices of the unit ball have trace at most `1`, the Gaussian width term of
the unit ball is at least `√(2/π) d ≥ d / √3` (`le_gw_unitBall`, `div_sqrt_three_le_gw_unitBall`,
blueprint `prop:width_ball`), and at most `d` (`gw_unitBall_le_card`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace Maiti2026Power

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}

/-- The width of the unit ball for `A` is `E‖Y‖` with `Y ~ N(0, A⁻¹)`. -/
lemma gwMat_unitBall (A : Matrix ι ι ℝ) :
    gwMat (unitBall ι) A = ∫ x, ‖x‖ ∂multivariateGaussian 0 A⁻¹ := by
  simp only [gwMat, gaussianWidth, supportFn_unitBall]

/-- `√(Aᵢᵢ) √((A⁻¹)ᵢᵢ) ≥ 1` for a positive definite matrix `A`: Cauchy–Schwarz for
`⟪A^{1/2} eᵢ, A^{-1/2} eᵢ⟫ = 1`. -/
lemma one_le_sqrt_diag_mul_sqrt_diag_inv (hA : A.PosDef) (i : ι) :
    1 ≤ √(A i i) * √(A⁻¹ i i) := by
  set e : EuclideanSpace ℝ ι := EuclideanSpace.single i 1 with he
  have h := inner_toEuclideanCLM_sqrt_sqrt_inv hA e e
  have h1 := norm_toEuclideanCLM_sqrt_sq hA.posSemidef e
  have h2 := norm_toEuclideanCLM_sqrt_inv_sq hA e
  have hee : ⟪e, e⟫ = 1 := by simp [he]
  have hq1 : WithLp.ofLp e ⬝ᵥ A *ᵥ WithLp.ofLp e = A i i := by
    simp [he]
  have hq2 : WithLp.ofLp e ⬝ᵥ A⁻¹ *ᵥ WithLp.ofLp e = A⁻¹ i i := by
    simp [he]
  rw [hq1] at h1
  rw [hq2] at h2
  calc (1 : ℝ) = ⟪toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) e,
        toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A⁻¹) e⟫ := by rw [h, hee]
    _ ≤ ‖toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A) e‖ *
        ‖toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A⁻¹) e‖ := real_inner_le_norm _ _
    _ = √(A i i) * √(A⁻¹ i i) := by
        rw [← Real.sqrt_sq (norm_nonneg _), h1, ← Real.sqrt_sq (norm_nonneg _), h2]

/-- **Width of the unit ball for a matrix**: `gwMat (unitBall) A ≥ √(2/π) d / √(tr A)` for
`A` positive definite. -/
lemma le_gwMat_unitBall (hA : A.PosDef) :
    √(2 / π) * Fintype.card ι / √A.trace ≤ gwMat (unitBall ι) A := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [gwMat_of_isEmpty]
  have htr : 0 < A.trace := hA.trace_pos
  rw [gwMat_unitBall]
  set c : ι → ℝ := fun i ↦ √(A i i) / √A.trace with hc
  have hc0 : ∀ i, 0 ≤ c i := fun i ↦ by positivity
  have hcsum : ∑ i, c i ^ 2 ≤ 1 := by
    have : ∑ i, c i ^ 2 = 1 := by
      simp only [hc, div_pow, Real.sq_sqrt hA.posSemidef.diag_nonneg, Real.sq_sqrt htr.le,
        ← Finset.sum_div]
      exact div_self htr.ne'
    exact this.le
  refine le_trans ?_
    (sum_mul_sqrt_diag_le_integral_norm_multivariateGaussian hA.inv.posSemidef hc0 hcsum)
  rw [mul_div_assoc]
  gcongr
  calc (Fintype.card ι : ℝ) / √A.trace = ∑ _i : ι, 1 / √A.trace := by
        simp [Finset.sum_const, div_eq_mul_inv]
    _ ≤ ∑ i, c i * √(A⁻¹ i i) := Finset.sum_le_sum fun i _ ↦ by
        rw [hc, div_mul_eq_mul_div]
        gcongr
        exact one_le_sqrt_diag_mul_sqrt_diag_inv hA i

/-- **Width of the unit ball** (blueprint `prop:width_ball`, lower bound):
`gw (unitBall) ≥ √(2/π) d`. -/
lemma le_gw_unitBall : √(2 / π) * Fintype.card ι ≤ gw (unitBall ι) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [gw_of_isEmpty]
  refine le_gw (exists_posDef_mem_designSet span_unitBall) fun A hA hA' ↦ ?_
  have htr : A.trace ≤ 1 := by
    simpa using trace_le_of_mem_designSet (R := 1) (fun x hx ↦ norm_le_one_of_mem_unitBall hx) hA
  have htr0 : 0 < A.trace := hA'.trace_pos
  refine le_trans ?_ (le_gwMat_unitBall hA')
  rw [le_div_iff₀ (Real.sqrt_pos.2 htr0)]
  have hs : √A.trace ≤ 1 := Real.sqrt_le_one.2 htr
  calc √(2 / π) * Fintype.card ι = √(2 / π) * Fintype.card ι * 1 := (mul_one _).symm
    _ ≥ √(2 / π) * Fintype.card ι * √A.trace := by gcongr

/-- **Width of the unit ball** (blueprint `prop:width_ball`): `gw (unitBall) ≥ d / √3`. -/
lemma div_sqrt_three_le_gw_unitBall : (Fintype.card ι : ℝ) / √3 ≤ gw (unitBall ι) := by
  refine le_trans ?_ le_gw_unitBall
  rw [div_eq_mul_inv, mul_comm, ← Real.sqrt_inv]
  gcongr
  rw [le_div_iff₀ Real.pi_pos]
  have := Real.pi_le_four
  linarith

/-- **Width of the unit ball** (blueprint `prop:width_ball`, upper bound): `gw (unitBall) ≤ d`. -/
lemma gw_unitBall_le_card : gw (unitBall ι) ≤ Fintype.card ι :=
  gw_le_card _ isCompact_unitBall unitBall_nonempty span_unitBall

end Maiti2026Power
