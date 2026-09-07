/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.Mathlib.Probability.SteinExpGrowth

/-!
# Gaussian posterior identities

For the Gaussian prior `π = N(0, σ² I)` on `ℝ^ι` and the exponential tilt
`gaussTilt b S θ = exp (⟪b, θ⟫ - ⟪θ, S θ⟫ / 2)` (`S` positive semidefinite), the tilted measure
`π.withDensity (gaussTilt b S)` is, up to normalization, the Gaussian `N(m, V)` with
`V = (σ⁻² I + S)⁻¹` (`postCov`) and `m = V b` (`postMean`). We only need two consequences,
which we prove by Stein's identity (Gaussian integration by parts, in its exponential-growth
form `integral_inner_mul_multivariateGaussian_of_le_exp`) rather than by completing the square:

* `integral_inner_sub_postMean_mul_gaussTilt`: `∫ ⟪c, θ - m⟫ ℓ(θ) dπ = 0` for every `c`
  (posterior mean identity);
* `integral_norm_sq_sub_postMean_mul_gaussTilt`: `∫ ‖θ - m‖² ℓ(θ) dπ = tr V ∫ ℓ dπ`
  (posterior second moment), and `integral_norm_sq_mul_gaussTilt`:
  `∫ ‖θ‖² ℓ dπ = (tr V + ‖m‖²) ∫ ℓ dπ`.

Blueprint: `lem:gaussian_complete_square`, `lem:pb_complete_square_identity`,
`lem:pb_gaussian_integrals` (the Lean proofs replace the change of variables by Stein's
identity).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Matrix
open scoped RealInnerProductSpace MatrixOrder

namespace ProbabilityTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section defs

variable (σ : ℝ) (b : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)

/-- The exponential tilt `θ ↦ exp (⟪b, θ⟫ - ⟪θ, S θ⟫ / 2)`. -/
noncomputable def gaussTilt (θ : EuclideanSpace ℝ ι) : ℝ :=
  rexp (⟪b, θ⟫ - 2⁻¹ * ⟪θ, toEuclideanCLM (𝕜 := ℝ) S θ⟫)

/-- The posterior precision matrix `σ⁻² I + S`. -/
noncomputable def postPrec : Matrix ι ι ℝ := σ⁻¹ ^ 2 • 1 + S

/-- The posterior covariance matrix `(σ⁻² I + S)⁻¹`. -/
noncomputable def postCov : Matrix ι ι ℝ := (postPrec σ S)⁻¹

/-- The posterior mean `(σ⁻² I + S)⁻¹ b`. -/
noncomputable def postMean : EuclideanSpace ℝ ι := toEuclideanCLM (𝕜 := ℝ) (postCov σ S) b

end defs

variable {σ : ℝ} {b : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}

section matrix

omit [Fintype ι] in
lemma posDef_postPrec (hS : S.PosSemidef) (hσ : σ ≠ 0) : (postPrec σ S).PosDef :=
  (Matrix.PosDef.one.smul (by positivity)).add_posSemidef hS

lemma posDef_postCov (hS : S.PosSemidef) (hσ : σ ≠ 0) : (postCov σ S).PosDef :=
  (posDef_postPrec hS hσ).inv

lemma toEuclideanCLM_postPrec_apply (x : EuclideanSpace ℝ ι) :
    toEuclideanCLM (𝕜 := ℝ) (postPrec σ S) x = σ⁻¹ ^ 2 • x + toEuclideanCLM (𝕜 := ℝ) S x := by
  simp [postPrec, map_add, map_smul]

lemma toEuclideanCLM_postCov_postPrec (hS : S.PosSemidef) (hσ : σ ≠ 0) (x : EuclideanSpace ℝ ι) :
    toEuclideanCLM (𝕜 := ℝ) (postCov σ S) (toEuclideanCLM (𝕜 := ℝ) (postPrec σ S) x) = x := by
  have h : toEuclideanCLM (𝕜 := ℝ) (postCov σ S) * toEuclideanCLM (𝕜 := ℝ) (postPrec σ S) = 1 := by
    rw [← map_mul, postCov, Matrix.nonsing_inv_mul _ (posDef_postPrec hS hσ).det_pos.ne'.isUnit,
      map_one]
  calc toEuclideanCLM (𝕜 := ℝ) (postCov σ S) (toEuclideanCLM (𝕜 := ℝ) (postPrec σ S) x)
      = (toEuclideanCLM (𝕜 := ℝ) (postCov σ S) * toEuclideanCLM (𝕜 := ℝ) (postPrec σ S)) x := rfl
    _ = x := by rw [h]; rfl

lemma toEuclideanCLM_postPrec_postCov (hS : S.PosSemidef) (hσ : σ ≠ 0) (x : EuclideanSpace ℝ ι) :
    toEuclideanCLM (𝕜 := ℝ) (postPrec σ S) (toEuclideanCLM (𝕜 := ℝ) (postCov σ S) x) = x := by
  have h : toEuclideanCLM (𝕜 := ℝ) (postPrec σ S) * toEuclideanCLM (𝕜 := ℝ) (postCov σ S) = 1 := by
    rw [← map_mul, postCov, Matrix.mul_nonsing_inv _ (posDef_postPrec hS hσ).det_pos.ne'.isUnit,
      map_one]
  calc toEuclideanCLM (𝕜 := ℝ) (postPrec σ S) (toEuclideanCLM (𝕜 := ℝ) (postCov σ S) x)
      = (toEuclideanCLM (𝕜 := ℝ) (postPrec σ S) * toEuclideanCLM (𝕜 := ℝ) (postCov σ S)) x := rfl
    _ = x := by rw [h]; rfl

/-- `(σ⁻² I + S) m = b`. -/
lemma toEuclideanCLM_postPrec_postMean (hS : S.PosSemidef) (hσ : σ ≠ 0) :
    toEuclideanCLM (𝕜 := ℝ) (postPrec σ S) (postMean σ b S) = b :=
  toEuclideanCLM_postPrec_postCov hS hσ b

/-- `b - S m = σ⁻² m`. -/
lemma sub_toEuclideanCLM_postMean (hS : S.PosSemidef) (hσ : σ ≠ 0) :
    b - toEuclideanCLM (𝕜 := ℝ) S (postMean σ b S) = σ⁻¹ ^ 2 • postMean σ b S := by
  have h := toEuclideanCLM_postPrec_postMean (b := b) hS hσ
  rw [toEuclideanCLM_postPrec_apply] at h
  calc b - toEuclideanCLM (𝕜 := ℝ) S (postMean σ b S)
      = (σ⁻¹ ^ 2 • postMean σ b S + toEuclideanCLM (𝕜 := ℝ) S (postMean σ b S)) -
          toEuclideanCLM (𝕜 := ℝ) S (postMean σ b S) := by rw [h]
    _ = σ⁻¹ ^ 2 • postMean σ b S := by abel

/-- The linear map of a symmetric matrix is self-adjoint. -/
lemma inner_toEuclideanCLM_symm (hS : S.IsHermitian) (x y : EuclideanSpace ℝ ι) :
    ⟪toEuclideanCLM (𝕜 := ℝ) S x, y⟫ = ⟪x, toEuclideanCLM (𝕜 := ℝ) S y⟫ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, Matrix.adjoint_toEuclideanCLM,
    ← conjTranspose_eq_transpose_of_trivial, hS.eq]

lemma inner_toEuclideanCLM_nonneg (hS : S.PosSemidef) (θ : EuclideanSpace ℝ ι) :
    0 ≤ ⟪θ, toEuclideanCLM (𝕜 := ℝ) S θ⟫ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, ofLp_toEuclideanCLM, star_trivial,
    dotProduct_comm]
  simpa using hS.dotProduct_mulVec_nonneg (WithLp.ofLp θ)

end matrix

section tilt

lemma gaussTilt_pos (θ : EuclideanSpace ℝ ι) : 0 < gaussTilt b S θ := exp_pos _

lemma gaussTilt_le (hS : S.PosSemidef) (θ : EuclideanSpace ℝ ι) :
    gaussTilt b S θ ≤ rexp (‖b‖ * ‖θ‖) := by
  unfold gaussTilt
  gcongr
  have := inner_toEuclideanCLM_nonneg hS θ
  have := real_inner_le_norm b θ
  linarith

lemma hasFDerivAt_gaussTilt (hS : S.IsHermitian) (θ : EuclideanSpace ℝ ι) :
    HasFDerivAt (gaussTilt b S)
      (gaussTilt b S θ • innerSL ℝ (b - toEuclideanCLM (𝕜 := ℝ) S θ)) θ := by
  have h1 : HasFDerivAt (fun θ : EuclideanSpace ℝ ι ↦ ⟪b, θ⟫) (innerSL ℝ b) θ :=
    (innerSL ℝ b).hasFDerivAt
  have h2 : HasFDerivAt (fun θ : EuclideanSpace ℝ ι ↦ ⟪θ, toEuclideanCLM (𝕜 := ℝ) S θ⟫)
      ((2 : ℝ) • innerSL ℝ (toEuclideanCLM (𝕜 := ℝ) S θ)) θ := by
    refine ((hasFDerivAt_id θ).inner ℝ (toEuclideanCLM (𝕜 := ℝ) S).hasFDerivAt).congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_id', id_eq, fderivInnerCLM_apply, _root_.smul_apply,
      innerSL_apply_apply, smul_eq_mul]
    rw [(inner_toEuclideanCLM_symm hS θ v).symm, real_inner_comm (toEuclideanCLM (𝕜 := ℝ) S θ) v]
    ring
  have h3 : HasFDerivAt
      (fun θ : EuclideanSpace ℝ ι ↦ ⟪b, θ⟫ - 2⁻¹ * ⟪θ, toEuclideanCLM (𝕜 := ℝ) S θ⟫)
      (innerSL ℝ (b - toEuclideanCLM (𝕜 := ℝ) S θ)) θ := by
    refine (h1.sub (h2.const_mul 2⁻¹)).congr_fderiv ?_
    ext v
    simp only [_root_.sub_apply, innerSL_apply_apply, _root_.smul_apply, smul_eq_mul,
      inner_sub_left]
    ring
  exact h3.exp

lemma contDiff_gaussTilt : ContDiff ℝ 1 (gaussTilt b S) := by
  unfold gaussTilt
  refine Real.contDiff_exp.comp ((contDiff_const.inner ℝ contDiff_id).sub ?_)
  exact contDiff_const.mul (contDiff_id.inner ℝ (toEuclideanCLM (𝕜 := ℝ) S).contDiff)

/-- The affine tilt `θ ↦ (⟪c, θ⟫ + r) ℓ(θ)`. -/
lemma hasFDerivAt_affine_mul_gaussTilt (hS : S.IsHermitian) (c : EuclideanSpace ℝ ι) (r : ℝ)
    (θ : EuclideanSpace ℝ ι) :
    HasFDerivAt (fun θ ↦ (⟪c, θ⟫ + r) * gaussTilt b S θ)
      ((⟪c, θ⟫ + r) • (gaussTilt b S θ • innerSL ℝ (b - toEuclideanCLM (𝕜 := ℝ) S θ)) +
        gaussTilt b S θ • innerSL ℝ c) θ :=
  ((innerSL ℝ c).hasFDerivAt.add_const r).mul (hasFDerivAt_gaussTilt hS θ)

lemma contDiff_affine_mul_gaussTilt (c : EuclideanSpace ℝ ι) (r : ℝ) :
    ContDiff ℝ 1 fun θ ↦ (⟪c, θ⟫ + r) * gaussTilt b S θ :=
  ((contDiff_const.inner ℝ contDiff_id).add contDiff_const).mul contDiff_gaussTilt

omit [DecidableEq ι] in
lemma one_le_exp_norm (θ : EuclideanSpace ℝ ι) : 1 ≤ rexp ‖θ‖ :=
  Real.one_le_exp (norm_nonneg θ)

/-- Growth of the affine tilt: `|(⟪c, θ⟫ + r) ℓ(θ)| ≤ (‖c‖ + |r|) exp ((‖b‖ + 1) ‖θ‖)`. -/
lemma abs_affine_mul_gaussTilt_le (hS : S.PosSemidef) (c : EuclideanSpace ℝ ι) (r : ℝ)
    (θ : EuclideanSpace ℝ ι) :
    |(⟪c, θ⟫ + r) * gaussTilt b S θ| ≤ (‖c‖ + |r|) * rexp ((‖b‖ + 1) * ‖θ‖) := by
  have h1 : |⟪c, θ⟫ + r| ≤ (‖c‖ + |r|) * rexp ‖θ‖ := by
    calc |⟪c, θ⟫ + r| ≤ |⟪c, θ⟫| + |r| := abs_add_le _ _
      _ ≤ ‖c‖ * ‖θ‖ + |r| := by gcongr; exact abs_real_inner_le_norm _ _
      _ ≤ ‖c‖ * rexp ‖θ‖ + |r| * rexp ‖θ‖ := by
          have := Real.le_exp_self ‖θ‖
          have := one_le_exp_norm θ
          nlinarith [norm_nonneg c, abs_nonneg r]
      _ = (‖c‖ + |r|) * rexp ‖θ‖ := by ring
  have hexp : rexp ((‖b‖ + 1) * ‖θ‖) = rexp (‖b‖ * ‖θ‖) * rexp ‖θ‖ := by
    rw [← Real.exp_add]
    ring_nf
  rw [abs_mul, abs_of_pos (gaussTilt_pos θ), hexp]
  calc |⟪c, θ⟫ + r| * gaussTilt b S θ ≤ (‖c‖ + |r|) * rexp ‖θ‖ * rexp (‖b‖ * ‖θ‖) :=
        mul_le_mul h1 (gaussTilt_le hS θ) (gaussTilt_pos θ).le (by positivity)
    _ = (‖c‖ + |r|) * (rexp (‖b‖ * ‖θ‖) * rexp ‖θ‖) := by ring

/-- Growth of the derivative of the affine tilt. -/
lemma norm_fderiv_affine_mul_gaussTilt_le (hS : S.PosSemidef) (c : EuclideanSpace ℝ ι) (r : ℝ)
    (θ : EuclideanSpace ℝ ι) :
    ‖fderiv ℝ (fun θ ↦ (⟪c, θ⟫ + r) * gaussTilt b S θ) θ‖ ≤
      ((‖c‖ + |r|) * (‖b‖ + ‖toEuclideanCLM (𝕜 := ℝ) S‖) + ‖c‖) * rexp ((‖b‖ + 2) * ‖θ‖) := by
  rw [(hasFDerivAt_affine_mul_gaussTilt hS.1 c r θ).fderiv]
  set L := toEuclideanCLM (𝕜 := ℝ) S
  have hℓ := gaussTilt_pos (b := b) (S := S) θ
  have hbS : ‖b - L θ‖ ≤ (‖b‖ + ‖L‖) * rexp ‖θ‖ := by
    calc ‖b - L θ‖ ≤ ‖b‖ + ‖L θ‖ := norm_sub_le _ _
      _ ≤ ‖b‖ + ‖L‖ * ‖θ‖ := by gcongr; exact L.le_opNorm θ
      _ ≤ ‖b‖ * rexp ‖θ‖ + ‖L‖ * rexp ‖θ‖ := by
          have := Real.le_exp_self ‖θ‖
          have := one_le_exp_norm θ
          nlinarith [norm_nonneg b, norm_nonneg L]
      _ = (‖b‖ + ‖L‖) * rexp ‖θ‖ := by ring
  have hexp1 : rexp ((‖b‖ + 1) * ‖θ‖) * rexp ‖θ‖ = rexp ((‖b‖ + 2) * ‖θ‖) := by
    rw [← Real.exp_add]; ring_nf
  have hexp2 : rexp (‖b‖ * ‖θ‖) ≤ rexp ((‖b‖ + 2) * ‖θ‖) := by
    gcongr
    nlinarith [norm_nonneg θ]
  calc ‖(⟪c, θ⟫ + r) • (gaussTilt b S θ • innerSL ℝ (b - L θ)) + gaussTilt b S θ • innerSL ℝ c‖
      ≤ ‖(⟪c, θ⟫ + r) • (gaussTilt b S θ • innerSL ℝ (b - L θ))‖ +
          ‖gaussTilt b S θ • innerSL ℝ c‖ := norm_add_le _ _
    _ = |(⟪c, θ⟫ + r) * gaussTilt b S θ| * ‖b - L θ‖ + gaussTilt b S θ * ‖c‖ := by
        rw [norm_smul, norm_smul, norm_smul, innerSL_apply_norm, innerSL_apply_norm,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hℓ, abs_mul, abs_of_pos hℓ]
        ring
    _ ≤ (‖c‖ + |r|) * rexp ((‖b‖ + 1) * ‖θ‖) * ((‖b‖ + ‖L‖) * rexp ‖θ‖) +
          rexp (‖b‖ * ‖θ‖) * ‖c‖ :=
        add_le_add (mul_le_mul (abs_affine_mul_gaussTilt_le (b := b) hS c r θ) hbS (norm_nonneg _)
          (by positivity)) (mul_le_mul_of_nonneg_right (gaussTilt_le hS θ) (norm_nonneg c))
    _ = (‖c‖ + |r|) * (‖b‖ + ‖L‖) * (rexp ((‖b‖ + 1) * ‖θ‖) * rexp ‖θ‖) +
          rexp (‖b‖ * ‖θ‖) * ‖c‖ := by ring
    _ ≤ (‖c‖ + |r|) * (‖b‖ + ‖L‖) * rexp ((‖b‖ + 2) * ‖θ‖) +
          rexp ((‖b‖ + 2) * ‖θ‖) * ‖c‖ := by
        rw [hexp1]
        gcongr
    _ = _ := by ring

end tilt

section stein

/-- The Gaussian prior `N(0, σ² I)`. -/
noncomputable abbrev gaussPrior (σ : ℝ) : Measure (EuclideanSpace ℝ ι) :=
  multivariateGaussian 0 (σ ^ 2 • (1 : Matrix ι ι ℝ))

omit [Fintype ι] in
lemma posSemidef_sq_smul_one (σ : ℝ) : (σ ^ 2 • (1 : Matrix ι ι ℝ)).PosSemidef :=
  Matrix.PosSemidef.one.smul (sq_nonneg σ)

/-- Integrability of functions of exponential growth under the prior. -/
lemma integrable_gaussPrior_of_abs_le {F : EuclideanSpace ℝ ι → ℝ}
    (hF : AEStronglyMeasurable F (gaussPrior σ)) {A B : ℝ}
    (hb : ∀ θ, |F θ| ≤ A * rexp (B * ‖θ‖)) : Integrable F (gaussPrior σ) :=
  IsGaussian.integrable_of_abs_le_mul_exp hF hb

/-- **Stein's identity for the affine tilt**:
`∫ ⟪a, θ⟫ (⟪c, θ⟫ + r) ℓ(θ) dπ = σ² ∫ (⟪c, a⟫ + (⟪c, θ⟫ + r) ⟪b - S θ, a⟫) ℓ(θ) dπ`. -/
lemma integral_inner_mul_affine_mul_gaussTilt (hS : S.PosSemidef) (c : EuclideanSpace ℝ ι)
    (r : ℝ) (a : EuclideanSpace ℝ ι) :
    ∫ θ, ⟪a, θ⟫ * ((⟪c, θ⟫ + r) * gaussTilt b S θ) ∂gaussPrior σ =
      σ ^ 2 * ∫ θ, (⟪c, a⟫ + (⟪c, θ⟫ + r) * ⟪b - toEuclideanCLM (𝕜 := ℝ) S θ, a⟫) *
        gaussTilt b S θ ∂gaussPrior σ := by
  set L := toEuclideanCLM (𝕜 := ℝ) S
  set A : ℝ := (‖c‖ + |r|) * (‖b‖ + ‖L‖ + 1) + ‖c‖ with hA
  set B : ℝ := ‖b‖ + 2 with hB
  have hFb : ∀ θ, |(⟪c, θ⟫ + r) * gaussTilt b S θ| ≤ A * rexp (B * ‖θ‖) := fun θ ↦ by
    refine (abs_affine_mul_gaussTilt_le hS c r θ).trans ?_
    have h1 : rexp ((‖b‖ + 1) * ‖θ‖) ≤ rexp (B * ‖θ‖) := by
      gcongr
      rw [hB]
      nlinarith [norm_nonneg θ]
    have h2 : ‖c‖ + |r| ≤ A := by
      rw [hA]
      nlinarith [norm_nonneg c, abs_nonneg r, norm_nonneg b, norm_nonneg L]
    exact mul_le_mul h2 h1 (exp_pos _).le (by rw [hA]; positivity)
  have hL : ∀ θ, ‖fderiv ℝ (fun θ ↦ (⟪c, θ⟫ + r) * gaussTilt b S θ) θ‖ ≤ A * rexp (B * ‖θ‖) :=
    fun θ ↦ by
      refine (norm_fderiv_affine_mul_gaussTilt_le hS c r θ).trans ?_
      gcongr
      rw [hA]
      nlinarith [norm_nonneg c, abs_nonneg r, norm_nonneg b, norm_nonneg L]
  rw [integral_inner_mul_multivariateGaussian_of_le_exp (posSemidef_sq_smul_one σ)
    (contDiff_affine_mul_gaussTilt c r) hFb hL a, ← integral_const_mul]
  congr 1
  funext θ
  rw [(hasFDerivAt_affine_mul_gaussTilt hS.1 c r θ).fderiv]
  simp only [map_smul, map_one, _root_.smul_apply, one_apply_eq_self, _root_.add_apply,
    innerSL_apply_apply, smul_eq_mul]
  ring

/-- Integrability of `(⟪a, θ⟫ + r) (⟪c, θ⟫ + s) ℓ(θ)` under the prior. -/
lemma integrable_affine_mul_affine_mul_gaussTilt (hS : S.PosSemidef) (a c : EuclideanSpace ℝ ι)
    (r s : ℝ) :
    Integrable (fun θ ↦ (⟪a, θ⟫ + r) * ((⟪c, θ⟫ + s) * gaussTilt b S θ)) (gaussPrior σ) := by
  refine integrable_gaussPrior_of_abs_le (A := (‖a‖ + |r|) * (‖c‖ + |s|)) (B := ‖b‖ + 2)
    (((continuous_const.inner continuous_id).add continuous_const).mul
      (contDiff_affine_mul_gaussTilt c s).continuous).aestronglyMeasurable fun θ ↦ ?_
  have h1 : |⟪a, θ⟫ + r| ≤ (‖a‖ + |r|) * rexp ‖θ‖ := by
    calc |⟪a, θ⟫ + r| ≤ |⟪a, θ⟫| + |r| := abs_add_le _ _
      _ ≤ ‖a‖ * ‖θ‖ + |r| := by gcongr; exact abs_real_inner_le_norm _ _
      _ ≤ ‖a‖ * rexp ‖θ‖ + |r| * rexp ‖θ‖ := by
          have := Real.le_exp_self ‖θ‖
          have := one_le_exp_norm θ
          nlinarith [norm_nonneg a, abs_nonneg r]
      _ = (‖a‖ + |r|) * rexp ‖θ‖ := by ring
  have h2 := abs_affine_mul_gaussTilt_le (b := b) hS c s θ
  have hexp : rexp ‖θ‖ * rexp ((‖b‖ + 1) * ‖θ‖) = rexp ((‖b‖ + 2) * ‖θ‖) := by
    rw [← Real.exp_add]
    ring_nf
  rw [abs_mul]
  calc |⟪a, θ⟫ + r| * |(⟪c, θ⟫ + s) * gaussTilt b S θ|
      ≤ (‖a‖ + |r|) * rexp ‖θ‖ * ((‖c‖ + |s|) * rexp ((‖b‖ + 1) * ‖θ‖)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = (‖a‖ + |r|) * (‖c‖ + |s|) * (rexp ‖θ‖ * rexp ((‖b‖ + 1) * ‖θ‖)) := by ring
    _ = _ := by rw [hexp]

lemma integrable_affine_mul_gaussTilt (hS : S.PosSemidef) (c : EuclideanSpace ℝ ι) (s : ℝ) :
    Integrable (fun θ ↦ (⟪c, θ⟫ + s) * gaussTilt b S θ) (gaussPrior σ) := by
  have := integrable_affine_mul_affine_mul_gaussTilt (σ := σ) (b := b) hS 0 c 1 s
  simpa using this

lemma integrable_gaussTilt (hS : S.PosSemidef) : Integrable (gaussTilt b S) (gaussPrior σ) := by
  have := integrable_affine_mul_gaussTilt (σ := σ) (b := b) hS 0 1
  simpa using this

/-- Integrability of `ℓ(θ) • θ` under the prior. -/
lemma integrable_gaussTilt_smul (hS : S.PosSemidef) :
    Integrable (fun θ ↦ gaussTilt b S θ • θ) (gaussPrior σ) := by
  have hint : Integrable (fun θ : EuclideanSpace ℝ ι ↦ ‖θ‖ * rexp (‖b‖ * ‖θ‖)) (gaussPrior σ) :=
    IsGaussian.integrable_norm_mul_of_abs_le_mul_exp (A := 1) (B := ‖b‖) (by fun_prop)
      fun θ ↦ by rw [abs_of_pos (exp_pos _), one_mul]
  refine hint.mono' (contDiff_gaussTilt.continuous.smul continuous_id).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ ↦ ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (gaussTilt_pos θ), mul_comm]
  exact mul_le_mul_of_nonneg_left (gaussTilt_le hS θ) (norm_nonneg θ)

/-- `∫ ⟪a, θ⟫ ℓ(θ) dπ = ⟪a, ∫ ℓ(θ) • θ dπ⟫`. -/
lemma integral_inner_mul_gaussTilt (hS : S.PosSemidef) (a : EuclideanSpace ℝ ι) :
    ∫ θ, ⟪a, θ⟫ * gaussTilt b S θ ∂gaussPrior σ =
      ⟪a, ∫ θ, gaussTilt b S θ • θ ∂gaussPrior σ⟫ := by
  have h := (innerSL ℝ a).integral_comp_comm (integrable_gaussTilt_smul (σ := σ) (b := b) hS)
  simp only [innerSL_apply_apply, inner_smul_right] at h
  rw [← h]
  congr 1
  funext θ
  ring

/-- The normalizing constant `Z = ∫ ℓ dπ` is positive. -/
lemma integral_gaussTilt_pos (hS : S.PosSemidef) : 0 < ∫ θ, gaussTilt b S θ ∂gaussPrior σ :=
  integral_exp_pos (integrable_gaussTilt (σ := σ) (b := b) hS)

/-- **Posterior mean identity, vector form**: `∫ ℓ(θ) • θ dπ = Z • m`. -/
lemma integral_gaussTilt_smul_eq (hS : S.PosSemidef) (hσ : 0 < σ) :
    ∫ θ, gaussTilt b S θ • θ ∂gaussPrior σ =
      (∫ θ, gaussTilt b S θ ∂gaussPrior σ) • postMean σ b S := by
  set L := toEuclideanCLM (𝕜 := ℝ) S with hL
  set Z := ∫ θ, gaussTilt b S θ ∂gaussPrior σ with hZ
  set u := ∫ θ, gaussTilt b S θ • θ ∂gaussPrior σ with hu
  have hint1 := integrable_gaussTilt (σ := σ) (b := b) hS
  have key : ∀ a, ⟪a, u⟫ = σ ^ 2 * (⟪b, a⟫ * Z - ⟪a, L u⟫) := by
    intro a
    have h := integral_inner_mul_affine_mul_gaussTilt (σ := σ) (b := b) hS 0 1 a
    simp only [inner_zero_left, zero_add, one_mul] at h
    have h1 : ∫ θ, ⟪a, θ⟫ * gaussTilt b S θ ∂gaussPrior σ = ⟪a, u⟫ :=
      integral_inner_mul_gaussTilt hS a
    have h2 : ∫ θ, ⟪b - L θ, a⟫ * gaussTilt b S θ ∂gaussPrior σ = ⟪b, a⟫ * Z - ⟪a, L u⟫ := by
      have h3 : ∫ θ, ⟪L a, θ⟫ * gaussTilt b S θ ∂gaussPrior σ = ⟪L a, u⟫ :=
        integral_inner_mul_gaussTilt hS (L a)
      rw [inner_toEuclideanCLM_symm hS.1] at h3
      rw [← h3, ← integral_const_mul, ← integral_sub (hint1.const_mul _) ?_]
      · congr 1
        funext θ
        rw [inner_sub_left, inner_toEuclideanCLM_symm hS.1, real_inner_comm θ]
        ring
      · have := integrable_affine_mul_gaussTilt (σ := σ) (b := b) hS (L a) 0
        simpa using this
    rw [h1, h2] at h
    exact h
  -- `σ⁻² u + L u = Z b`
  have h4 : toEuclideanCLM (𝕜 := ℝ) (postPrec σ S) u = Z • b := by
    rw [toEuclideanCLM_postPrec_apply]
    refine ext_inner_left ℝ fun a ↦ ?_
    have := key a
    rw [inner_add_right, inner_smul_right, inner_smul_right, real_inner_comm b a]
    have hσ2 : σ ^ 2 ≠ 0 := by positivity
    field_simp
    linear_combination this
  have h5 := congrArg (toEuclideanCLM (𝕜 := ℝ) (postCov σ S)) h4
  rw [toEuclideanCLM_postCov_postPrec hS hσ.ne', map_smul] at h5
  exact h5

/-- **Posterior mean identity** (blueprint `lem:gaussian_complete_square`):
`∫ ⟪c, θ - m⟫ ℓ(θ) dπ = 0`. -/
lemma integral_inner_sub_postMean_mul_gaussTilt (hS : S.PosSemidef) (hσ : 0 < σ)
    (c : EuclideanSpace ℝ ι) :
    ∫ θ, ⟪c, θ - postMean σ b S⟫ * gaussTilt b S θ ∂gaussPrior σ = 0 := by
  have hint1 := integrable_gaussTilt (σ := σ) (b := b) hS
  have h1 : ∫ θ, ⟪c, θ - postMean σ b S⟫ * gaussTilt b S θ ∂gaussPrior σ =
      ∫ θ, ⟪c, θ⟫ * gaussTilt b S θ ∂gaussPrior σ -
        ⟪c, postMean σ b S⟫ * ∫ θ, gaussTilt b S θ ∂gaussPrior σ := by
    rw [← integral_const_mul, ← integral_sub ?_ (hint1.const_mul _)]
    · congr 1
      funext θ
      rw [inner_sub_right]
      ring
    · have := integrable_affine_mul_gaussTilt (σ := σ) (b := b) hS c 0
      simpa using this
  rw [h1, integral_inner_mul_gaussTilt hS, integral_gaussTilt_smul_eq hS hσ, inner_smul_right]
  ring

section secondMoment

variable (hS : S.PosSemidef) (hσ : 0 < σ)
include hS

lemma integrable_inner_sub_mul_inner_sub_mul_gaussTilt (a c : EuclideanSpace ℝ ι) :
    Integrable (fun θ ↦ ⟪a, θ - postMean σ b S⟫ * ⟪c, θ - postMean σ b S⟫ * gaussTilt b S θ)
      (gaussPrior σ) := by
  refine (integrable_affine_mul_affine_mul_gaussTilt (σ := σ) (b := b) hS a c
    (-⟪a, postMean σ b S⟫) (-⟪c, postMean σ b S⟫)).congr (ae_of_all _ fun θ ↦ ?_)
  simp only [inner_sub_right]
  ring

lemma integrable_inner_sub_mul_gaussTilt (c : EuclideanSpace ℝ ι) :
    Integrable (fun θ ↦ ⟪c, θ - postMean σ b S⟫ * gaussTilt b S θ) (gaussPrior σ) := by
  refine (integrable_affine_mul_gaussTilt (σ := σ) (b := b) hS c (-⟪c, postMean σ b S⟫)).congr
    (ae_of_all _ fun θ ↦ ?_)
  simp only [inner_sub_right]
  ring

include hσ

/-- **Stein's identity for the centered affine tilt**, rearranged: with
`Φ(a, c) := ∫ ⟪a, θ - m⟫ ⟪c, θ - m⟫ ℓ(θ) dπ`, `Φ(a, c) + σ² Φ(S a, c) = σ² ⟪c, a⟫ Z`. -/
lemma integral_inner_sub_mul_inner_sub_mul_gaussTilt_add (a c : EuclideanSpace ℝ ι) :
    ∫ θ, ⟪a, θ - postMean σ b S⟫ * ⟪c, θ - postMean σ b S⟫ * gaussTilt b S θ ∂gaussPrior σ +
      σ ^ 2 * ∫ θ, ⟪toEuclideanCLM (𝕜 := ℝ) S a, θ - postMean σ b S⟫ *
        ⟪c, θ - postMean σ b S⟫ * gaussTilt b S θ ∂gaussPrior σ =
      σ ^ 2 * ⟪c, a⟫ * ∫ θ, gaussTilt b S θ ∂gaussPrior σ := by
  have hstein := integral_inner_mul_affine_mul_gaussTilt (σ := σ) (b := b) hS c
    (-⟪c, postMean σ b S⟫) a
  have hmean := integral_inner_sub_postMean_mul_gaussTilt (b := b) hS hσ c
  have hbm : b - toEuclideanCLM (𝕜 := ℝ) S (postMean σ b S) = σ⁻¹ ^ 2 • postMean σ b S :=
    sub_toEuclideanCLM_postMean hS hσ.ne'
  have hI1 := integrable_inner_sub_mul_inner_sub_mul_gaussTilt (σ := σ) (b := b) hS a c
  have hI2 := integrable_inner_sub_mul_gaussTilt (σ := σ) (b := b) hS c
  have hI3 := integrable_inner_sub_mul_inner_sub_mul_gaussTilt (σ := σ) (b := b) hS
    (toEuclideanCLM (𝕜 := ℝ) S a) c
  have hI4 := integrable_gaussTilt (σ := σ) (b := b) hS
  set m := postMean σ b S with hm
  set L := toEuclideanCLM (𝕜 := ℝ) S with hL
  have hI5 : Integrable (fun θ ↦ ⟪c, a⟫ * gaussTilt b S θ +
      σ⁻¹ ^ 2 * ⟪m, a⟫ * (⟪c, θ - m⟫ * gaussTilt b S θ)) (gaussPrior σ) :=
    (hI4.const_mul _).add (hI2.const_mul _)
  have hI6 : Integrable (fun θ ↦ ⟪c, a⟫ * gaussTilt b S θ) (gaussPrior σ) := hI4.const_mul _
  have hI7 : Integrable (fun θ ↦ σ⁻¹ ^ 2 * ⟪m, a⟫ * (⟪c, θ - m⟫ * gaussTilt b S θ))
      (gaussPrior σ) := hI2.const_mul _
  have hI8 : Integrable (fun θ ↦ ⟪a, m⟫ * (⟪c, θ - m⟫ * gaussTilt b S θ)) (gaussPrior σ) :=
    hI2.const_mul _
  have e1 : (fun θ ↦ ⟪a, θ⟫ * ((⟪c, θ⟫ + -⟪c, m⟫) * gaussTilt b S θ)) =
      fun θ ↦ ⟪a, θ - m⟫ * ⟪c, θ - m⟫ * gaussTilt b S θ +
        ⟪a, m⟫ * (⟪c, θ - m⟫ * gaussTilt b S θ) := by
    funext θ
    simp only [inner_sub_right]
    ring
  have e2 : (fun θ ↦ (⟪c, a⟫ + (⟪c, θ⟫ + -⟪c, m⟫) * ⟪b - L θ, a⟫) * gaussTilt b S θ) =
      fun θ ↦ ⟪c, a⟫ * gaussTilt b S θ +
        (σ⁻¹ ^ 2 * ⟪m, a⟫) * (⟪c, θ - m⟫ * gaussTilt b S θ) -
          ⟪L a, θ - m⟫ * ⟪c, θ - m⟫ * gaussTilt b S θ := by
    funext θ
    have h3 : b - L θ = σ⁻¹ ^ 2 • m - L (θ - m) := by
      rw [map_sub, ← hbm]
      abel
    rw [h3, inner_sub_left, real_inner_smul_left, inner_toEuclideanCLM_symm hS.1,
      real_inner_comm (L a)]
    simp only [inner_sub_right]
    ring
  rw [e1, e2, integral_add hI1 hI8, integral_const_mul, hmean, integral_sub hI5 hI3,
    integral_add hI6 hI7, integral_const_mul, integral_const_mul, hmean] at hstein
  linear_combination hstein

/-- `Φ(eᵢ, c) = ⟪c, V eᵢ⟫ Z`. -/
lemma integral_inner_single_sub_mul_inner_sub_mul_gaussTilt (i : ι) (c : EuclideanSpace ℝ ι) :
    ∫ θ, ⟪EuclideanSpace.single i 1, θ - postMean σ b S⟫ * ⟪c, θ - postMean σ b S⟫ *
        gaussTilt b S θ ∂gaussPrior σ =
      ⟪c, toEuclideanCLM (𝕜 := ℝ) (postCov σ S) (EuclideanSpace.single i 1)⟫ *
        ∫ θ, gaussTilt b S θ ∂gaussPrior σ := by
  set m := postMean σ b S with hm
  set L := toEuclideanCLM (𝕜 := ℝ) S with hL
  set e : EuclideanSpace ℝ ι := EuclideanSpace.single i 1 with he
  set a : EuclideanSpace ℝ ι := σ⁻¹ ^ 2 • toEuclideanCLM (𝕜 := ℝ) (postCov σ S) e with ha
  have hσ2 : σ ^ 2 * σ⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hσ.ne', one_pow]
  have hae : e = a + σ ^ 2 • L a := by
    have h1 : toEuclideanCLM (𝕜 := ℝ) (postPrec σ S) a = σ⁻¹ ^ 2 • e := by
      rw [ha, map_smul, toEuclideanCLM_postPrec_postCov hS hσ.ne']
    rw [toEuclideanCLM_postPrec_apply] at h1
    calc e = σ ^ 2 • (σ⁻¹ ^ 2 • e) := by rw [smul_smul, hσ2, one_smul]
      _ = σ ^ 2 • (σ⁻¹ ^ 2 • a + L a) := by rw [h1]
      _ = a + σ ^ 2 • L a := by rw [smul_add, smul_smul, hσ2, one_smul]
  have hkey := integral_inner_sub_mul_inner_sub_mul_gaussTilt_add (b := b) hS hσ a c
  have hI1 := integrable_inner_sub_mul_inner_sub_mul_gaussTilt (σ := σ) (b := b) hS a c
  have hI3 := integrable_inner_sub_mul_inner_sub_mul_gaussTilt (σ := σ) (b := b) hS (L a) c
  have e1 : (fun θ ↦ ⟪e, θ - m⟫ * ⟪c, θ - m⟫ * gaussTilt b S θ) =
      fun θ ↦ ⟪a, θ - m⟫ * ⟪c, θ - m⟫ * gaussTilt b S θ +
        σ ^ 2 * (⟪L a, θ - m⟫ * ⟪c, θ - m⟫ * gaussTilt b S θ) := by
    funext θ
    rw [hae, inner_add_left, real_inner_smul_left _ _ (σ ^ 2)]
    ring
  rw [e1, integral_add hI1 (hI3.const_mul _), integral_const_mul, hkey, ha,
    real_inner_smul_right, ← mul_assoc (σ ^ 2), hσ2, one_mul]

/-- **Posterior second moment** (blueprint `lem:gaussian_complete_square`):
`∫ ‖θ - m‖² ℓ(θ) dπ = tr V ∫ ℓ dπ`. -/
lemma integral_norm_sq_sub_postMean_mul_gaussTilt :
    ∫ θ, ‖θ - postMean σ b S‖ ^ 2 * gaussTilt b S θ ∂gaussPrior σ =
      (postCov σ S).trace * ∫ θ, gaussTilt b S θ ∂gaussPrior σ := by
  set m := postMean σ b S with hm
  have h1 : ∀ θ : EuclideanSpace ℝ ι, ‖θ - m‖ ^ 2 * gaussTilt b S θ =
      ∑ i, ⟪EuclideanSpace.single i 1, θ - m⟫ * ⟪EuclideanSpace.single i 1, θ - m⟫ *
        gaussTilt b S θ := by
    intro θ
    rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
    simp [EuclideanSpace.inner_single_left, sq]
  simp_rw [h1]
  rw [integral_finsetSum _ fun i _ ↦
    integrable_inner_sub_mul_inner_sub_mul_gaussTilt (σ := σ) (b := b) hS _ _, Matrix.trace,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_inner_single_sub_mul_inner_sub_mul_gaussTilt (b := b) hS hσ i]
  congr 1
  simp [EuclideanSpace.inner_single_left, ofLp_toEuclideanCLM]

/-- `∫ ‖θ‖² ℓ(θ) dπ = (tr V + ‖m‖²) ∫ ℓ dπ`. -/
lemma integral_norm_sq_mul_gaussTilt :
    ∫ θ, ‖θ‖ ^ 2 * gaussTilt b S θ ∂gaussPrior σ =
      ((postCov σ S).trace + ‖postMean σ b S‖ ^ 2) * ∫ θ, gaussTilt b S θ ∂gaussPrior σ := by
  have hmean := integral_inner_sub_postMean_mul_gaussTilt (b := b) hS hσ (postMean σ b S)
  have hsq := integral_norm_sq_sub_postMean_mul_gaussTilt (b := b) hS hσ
  have hI2 := integrable_inner_sub_mul_gaussTilt (σ := σ) (b := b) hS (postMean σ b S)
  have hI4 := integrable_gaussTilt (σ := σ) (b := b) hS
  have hI1 : Integrable (fun θ ↦ ‖θ - postMean σ b S‖ ^ 2 * gaussTilt b S θ) (gaussPrior σ) := by
    have h1 : ∀ θ : EuclideanSpace ℝ ι, ‖θ - postMean σ b S‖ ^ 2 * gaussTilt b S θ =
        ∑ i, ⟪EuclideanSpace.single i 1, θ - postMean σ b S⟫ *
          ⟪EuclideanSpace.single i 1, θ - postMean σ b S⟫ * gaussTilt b S θ := by
      intro θ
      rw [EuclideanSpace.real_norm_sq_eq, Finset.sum_mul]
      simp [EuclideanSpace.inner_single_left, sq]
    simp_rw [h1]
    exact integrable_finsetSum _ fun i _ ↦
      integrable_inner_sub_mul_inner_sub_mul_gaussTilt (σ := σ) (b := b) hS _ _
  set m := postMean σ b S with hm
  have hI5 : Integrable (fun θ ↦ ‖θ - m‖ ^ 2 * gaussTilt b S θ +
      2 * (⟪m, θ - m⟫ * gaussTilt b S θ)) (gaussPrior σ) := hI1.add (hI2.const_mul _)
  have hI6 : Integrable (fun θ ↦ 2 * (⟪m, θ - m⟫ * gaussTilt b S θ)) (gaussPrior σ) :=
    hI2.const_mul _
  have hI7 : Integrable (fun θ ↦ ‖m‖ ^ 2 * gaussTilt b S θ) (gaussPrior σ) := hI4.const_mul _
  have e : (fun θ : EuclideanSpace ℝ ι ↦ ‖θ‖ ^ 2 * gaussTilt b S θ) =
      fun θ ↦ ‖θ - m‖ ^ 2 * gaussTilt b S θ + 2 * (⟪m, θ - m⟫ * gaussTilt b S θ) +
        ‖m‖ ^ 2 * gaussTilt b S θ := by
    funext θ
    have h2 : ‖θ‖ ^ 2 = ‖θ - m‖ ^ 2 + 2 * ⟪m, θ - m⟫ + ‖m‖ ^ 2 := by
      rw [← sub_add_cancel θ m, norm_add_sq_real, real_inner_comm, add_sub_cancel_right]
    rw [h2]
    ring
  rw [e, integral_add hI5 hI7, integral_add hI1 hI6, integral_const_mul, integral_const_mul,
    hmean, hsq]
  ring

end secondMoment

end stein

end ProbabilityTheory
