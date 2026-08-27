/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.FixedDesignRun
public import COLT83.MXJ2026.Rounding
public import COLT83.Mathlib.Probability.MultivariateGaussian

/-!
# The least-squares estimator of a fixed design

For a fixed design `x : Fin T → ℝ^d` with design matrix `Σ = ∑ t, x t x tᵀ` and observations
`y : Fin T → ℝ`, the least-squares estimator is `leastSquares x y = Σ⁻¹ ∑ t, y t • x t`
(blueprint `def:least_squares`). If `y t = ⟪x t, θ⟫ + η t` then
`leastSquares x y = θ + Σ⁻¹ Xᵀ η` (`leastSquares_inner_add`), and under the fixed-design run in
the linear Gaussian environment with reward vector `θ` the estimator has the law `N(θ, Σ⁻¹)`
(`hasLaw_leastSquares_of_fixedDesign`, blueprint `lem:least_squares_law`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset Learning Learning.LinearBandit Matrix
open scoped RealInnerProductSpace

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℕ}

omit [Fintype ι] [DecidableEq ι] in
/-- The matrix `X ∈ ℝ^{T × d}` whose rows are the points of the design `x`. -/
def designRows (x : Fin T → EuclideanSpace ℝ ι) : Matrix (Fin T) ι ℝ := Matrix.of fun t i ↦ x t i

omit [Fintype ι] [DecidableEq ι] in
/-- `Xᵀ X = ∑ t, x t x tᵀ`. -/
lemma transpose_designRows_mul_designRows (x : Fin T → EuclideanSpace ℝ ι) :
    (designRows x)ᵀ * designRows x = ∑ t, outerSelf (x t) := by
  ext i j
  simp [Matrix.mul_apply, designRows, outerSelf, Matrix.sum_apply, Matrix.vecMulVec_apply]

omit [Fintype ι] [DecidableEq ι] in
/-- `Xᵀ y = ∑ t, y t • x t`. -/
lemma transpose_designRows_mulVec (x : Fin T → EuclideanSpace ℝ ι) (y : Fin T → ℝ) :
    (designRows x)ᵀ *ᵥ y = WithLp.ofLp (∑ t, y t • x t) := by
  ext i
  simp [Matrix.mulVec, dotProduct, designRows, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, mul_comm]

/-- The least-squares estimator `Σ⁻¹ ∑ t, y t • x t` of the fixed design `x` with observations
`y` (blueprint `def:least_squares`). -/
noncomputable def leastSquares (x : Fin T → EuclideanSpace ℝ ι) (y : Fin T → ℝ) :
    EuclideanSpace ℝ ι :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ t, outerSelf (x t))⁻¹ (∑ t, y t • x t)

/-- The matrix `Σ⁻¹ Xᵀ` mapping the observations to the least-squares estimate. -/
noncomputable def lsMatrix (x : Fin T → EuclideanSpace ℝ ι) : Matrix ι (Fin T) ℝ :=
  (∑ t, outerSelf (x t))⁻¹ * (designRows x)ᵀ

lemma leastSquares_eq_toEuclideanLin (x : Fin T → EuclideanSpace ℝ ι) (y : Fin T → ℝ) :
    leastSquares x y = Matrix.toEuclideanLin (lsMatrix x) (WithLp.toLp 2 y) := by
  apply WithLp.ofLp_injective
  rw [leastSquares, Matrix.ofLp_toEuclideanCLM, ofLp_toEuclideanLin, lsMatrix,
    ← Matrix.mulVec_mulVec, WithLp.ofLp_toLp, transpose_designRows_mulVec]

/-- If the observations are `y t = ⟪x t, θ⟫ + η t`, the least-squares estimate is
`θ + Σ⁻¹ Xᵀ η`. -/
lemma leastSquares_inner_add (x : Fin T → EuclideanSpace ℝ ι)
    (hS : (∑ t, outerSelf (x t)).PosDef) (θ : EuclideanSpace ℝ ι) (η : Fin T → ℝ) :
    leastSquares x (fun t ↦ ⟪x t, θ⟫ + η t) =
      θ + Matrix.toEuclideanLin (lsMatrix x) (WithLp.toLp 2 η) := by
  rw [← leastSquares_eq_toEuclideanLin, leastSquares, leastSquares]
  simp_rw [add_smul, Finset.sum_add_distrib, map_add, ← toEuclideanCLM_sum_outerSelf_apply,
    Matrix.toEuclideanCLM_inv_apply_toEuclideanCLM hS]

/-- `(Σ⁻¹ Xᵀ) (Σ⁻¹ Xᵀ)ᵀ = Σ⁻¹`. -/
lemma lsMatrix_mul_transpose (x : Fin T → EuclideanSpace ℝ ι)
    (hS : (∑ t, outerSelf (x t)).PosDef) :
    lsMatrix x * (lsMatrix x)ᵀ = (∑ t, outerSelf (x t))⁻¹ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hS.isUnit
  rw [lsMatrix, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_nonsing_inv,
    transpose_sum_outerSelf]
  calc (∑ t, outerSelf (x t))⁻¹ * (designRows x)ᵀ * (designRows x * (∑ t, outerSelf (x t))⁻¹)
      = (∑ t, outerSelf (x t))⁻¹ * ((designRows x)ᵀ * designRows x) *
          (∑ t, outerSelf (x t))⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (∑ t, outerSelf (x t))⁻¹ := by
        rw [transpose_designRows_mul_designRows, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]

/-- The least-squares estimator is continuous in the observations. -/
lemma continuous_leastSquares (x : Fin T → EuclideanSpace ℝ ι) : Continuous (leastSquares x) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) _).continuous.comp
    (continuous_finsetSum _ fun t _ ↦ (continuous_apply t).smul continuous_const)

/-- **Law of the least-squares estimator** for the observations `⟪x t, θ⟫ + η t` of the fixed
design `x` with an i.i.d. `N(0, 1)` noise vector `η`: if the design matrix `Σ = ∑ t < T, x t x tᵀ`
is positive definite then the least-squares estimator has the law `N(θ, Σ⁻¹)`. -/
lemma hasLaw_leastSquares_add_pi (x : Fin T → EuclideanSpace ℝ ι) (θ : EuclideanSpace ℝ ι)
    (hS : (∑ t, outerSelf (x t)).PosDef) :
    HasLaw (fun η : Fin T → ℝ ↦ leastSquares x fun t ↦ ⟪x t, θ⟫ + η t)
      (multivariateGaussian θ (∑ t, outerSelf (x t))⁻¹) (Measure.pi fun _ ↦ gaussianReal 0 1) := by
  have hη : HasLaw (fun η : Fin T → ℝ ↦ WithLp.toLp 2 η) (stdGaussian (EuclideanSpace ℝ (Fin T)))
      (Measure.pi fun _ ↦ gaussianReal 0 1) := by
    rw [← map_pi_eq_stdGaussian]
    exact ⟨(WithLp.measurable_toLp 2 _).aemeasurable, rfl⟩
  have h1 : HasLaw (fun η : Fin T → ℝ ↦ Matrix.toEuclideanLin (lsMatrix x) (WithLp.toLp 2 η))
      (multivariateGaussian 0 (∑ t, outerSelf (x t))⁻¹) (Measure.pi fun _ ↦ gaussianReal 0 1) := by
    have h2 := (⟨(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
      (lsMatrix x))).continuous.measurable.aemeasurable, rfl⟩ :
      HasLaw (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (lsMatrix x))) _ _).comp hη
    rw [← multivariateGaussian_zero_one, multivariateGaussian_zero_map_toEuclideanLin
      Matrix.PosDef.one.posSemidef (lsMatrix x), Matrix.mul_one, lsMatrix_mul_transpose x hS]
      at h2
    exact h2
  have h2 := (⟨(measurable_const_add θ).aemeasurable, rfl⟩ :
    HasLaw (fun v : EuclideanSpace ℝ ι ↦ θ + v) _ _).comp h1
  rw [multivariateGaussian_zero_map_const_add] at h2
  refine h2.congr (Filter.Eventually.of_forall fun η ↦ ?_)
  exact leastSquares_inner_add x hS θ η

/-- **Law of the least-squares estimator** (blueprint `lem:least_squares_law`): under the
fixed-design run of `x` in the linear Gaussian environment with reward vector `θ`, if the design
matrix `Σ = ∑ t < T, x t x tᵀ` is positive definite then the least-squares estimator of the first
`T` observations has the law `N(θ, Σ⁻¹)`. -/
lemma hasLaw_leastSquares_of_fixedDesign {𝒳 : Set (EuclideanSpace ℝ ι)}
    {θ : EuclideanSpace ℝ ι} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → ℝ} {x : ℕ → 𝒳}
    (h : IsAlgEnvSeq X Y (fixedDesignAlg x) (linearGaussianEnv 𝒳 θ) P) (T : ℕ)
    (hS : (∑ t : Fin T, outerSelf (x t : EuclideanSpace ℝ ι)).PosDef) :
    HasLaw (fun ω ↦ leastSquares (fun t : Fin T ↦ (x t : EuclideanSpace ℝ ι)) (fun t ↦ Y t ω))
      (multivariateGaussian θ (∑ t : Fin T, outerSelf (x t : EuclideanSpace ℝ ι))⁻¹) P := by
  refine ((hasLaw_leastSquares_add_pi _ θ hS).comp (h.hasLaw_noise_finVec T)).congr ?_
  filter_upwards [h.ae_feedback_eq_of_fixedDesign] with ω hω
  simp only [Function.comp_apply]
  congr 1
  funext t
  exact hω t

end COLT83
