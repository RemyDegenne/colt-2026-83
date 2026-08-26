/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.FixedDesignLaw
public import COLT83.MXJ2026.LeastSquares
public import COLT83.MXJ2026.DifferenceProcess
public import COLT83.MXJ2026.Width
public import COLT83.Mathlib.Probability.StdGaussianProd
public import COLT83.Mathlib.Probability.Kernel.PriorAverage
public import COLT83.Mathlib.Probability.IndepIntegral

/-!
# The Bayesian model of the non-adaptive lower bound

Fix a design `x : Fin T → ℝ^d` with positive definite design matrix `Σ = ∑ t, x t x tᵀ` and
`τ > 0`. The Bayesian model (blueprint `def:bayes_prior`) is built on a standard Gaussian pair
`(g, η) ~ N(0, I_d) ⊗ N(0, I_T)`: the reward vector is `θ = bayesParam x τ g = τ Σ^{-1/2} g`
(so that `θ ~ N(0, τ² Σ⁻¹)`), the observations are `y t = ⟪x t, θ⟫ + η t` (`bayesObs`), and the
recommendation of a fixed-budget algorithm `A` is drawn from `A.output T` applied to the history
`(x t, y t)_t`; the joint law of `((g, η), rec)` is `bayesJoint A x hx τ`.

* `map_bayesParam_stdGaussian`: `θ ~ N(0, τ² Σ⁻¹)`;
* `integral_supportFn_bayesParam`: `E[sup_{z ∈ 𝒳} ⟪z, θ⟫] = τ w_T`, `w_T = gwMat 𝒳 Σ`;
* `integral_supportFn_toEuclideanLin_lsMatrix`: `E[sup_{z ∈ 𝒳} ⟪z, Σ⁻¹ Xᵀ η⟫] = w_T`;
* `integral_diffSup_bayesParam`: `E[Z(θ)] = 2 τ w_T` for the diameter `Z`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Learning Learning.LinearBandit
open scoped RealInnerProductSpace MatrixOrder

universe u

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒳 : Set (EuclideanSpace ℝ ι)} {T : ℕ} {R : ℝ}

section param

variable (x : Fin T → EuclideanSpace ℝ ι) (τ : ℝ)

/-- The linear map `Σ^{-1/2}` of the design matrix `Σ = ∑ t, x t x tᵀ`, as a continuous linear
map. -/
noncomputable def sqrtInvDesign : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  LinearMap.toContinuousLinearMap (toEuclideanLin (CFC.sqrt (∑ t, outerSelf (x t))⁻¹))

/-- The reward vector of the Bayesian model: `θ = τ Σ^{-1/2} g`. -/
noncomputable def bayesParam (g : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  τ • sqrtInvDesign x g

/-- The observation vector of the Bayesian model: `y t = ⟪x t, θ⟫ + η t` with
`θ = bayesParam x τ g`. -/
noncomputable def bayesObs (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) : Fin T → ℝ :=
  fun t ↦ ⟪x t, bayesParam x τ p.1⟫ + p.2 t

lemma bayesObs_eq (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) :
    bayesObs x τ p = fun t ↦ ⟪x t, bayesParam x τ p.1⟫ + WithLp.ofLp p.2 t := rfl

/-- `Σ^{-1/2} g ~ N(0, Σ⁻¹)` for `g ~ N(0, I)`. -/
lemma map_sqrtInvDesign_stdGaussian (hS : (∑ t, outerSelf (x t)).PosDef) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (sqrtInvDesign x) =
      multivariateGaussian 0 (∑ t, outerSelf (x t))⁻¹ := by
  rw [sqrtInvDesign, ← multivariateGaussian_zero_one,
    multivariateGaussian_zero_map_toEuclideanLin PosSemidef.one, Matrix.mul_one, transpose_sqrt,
    hS.inv.posSemidef.sqrt_mul_sqrt]

/-- The reward vector of the Bayesian model has law `N(0, τ² Σ⁻¹)`. -/
lemma map_bayesParam_stdGaussian (hS : (∑ t, outerSelf (x t)).PosDef) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (bayesParam x τ) =
      multivariateGaussian 0 (τ ^ 2 • (∑ t, outerSelf (x t))⁻¹) := by
  have : bayesParam x τ = (fun v ↦ τ • v) ∘ sqrtInvDesign x := rfl
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), map_sqrtInvDesign_stdGaussian x hS,
    multivariateGaussian_zero_map_smul hS.inv.posSemidef]

/-- `E[sup_{z ∈ 𝒳} ⟪z, θ⟫] = τ w_T` where `w_T = gwMat 𝒳 Σ` is the width of the design. -/
lemma integral_supportFn_bayesParam (hne : 𝒳.Nonempty) (hR : ∀ z ∈ 𝒳, ‖z‖ ≤ R)
    (hS : (∑ t, outerSelf (x t)).PosDef) (hτ : 0 ≤ τ) :
    ∫ g, supportFn 𝒳 (bayesParam x τ g) ∂stdGaussian (EuclideanSpace ℝ ι) =
      τ * gwMat 𝒳 (∑ t, outerSelf (x t)) := by
  simp_rw [bayesParam, supportFn_smul 𝒳 hτ]
  rw [integral_const_mul, gwMat, gaussianWidth, ← map_sqrtInvDesign_stdGaussian x hS,
    integral_map (by fun_prop) (continuous_supportFn hne hR).aestronglyMeasurable]

/-- `Σ⁻¹ Xᵀ η ~ N(0, Σ⁻¹)` for `η ~ N(0, I_T)`. -/
lemma map_toEuclideanLin_lsMatrix_stdGaussian (hS : (∑ t, outerSelf (x t)).PosDef) :
    (stdGaussian (EuclideanSpace ℝ (Fin T))).map
        (LinearMap.toContinuousLinearMap (toEuclideanLin (lsMatrix x))) =
      multivariateGaussian 0 (∑ t, outerSelf (x t))⁻¹ := by
  rw [← multivariateGaussian_zero_one, multivariateGaussian_zero_map_toEuclideanLin PosSemidef.one,
    Matrix.mul_one, lsMatrix_mul_transpose x hS]

/-- `E[sup_{z ∈ 𝒳} ⟪z, Σ⁻¹ Xᵀ η⟫] = w_T`. -/
lemma integral_supportFn_toEuclideanLin_lsMatrix (hne : 𝒳.Nonempty) (hR : ∀ z ∈ 𝒳, ‖z‖ ≤ R)
    (hS : (∑ t, outerSelf (x t)).PosDef) :
    ∫ η, supportFn 𝒳 (toEuclideanLin (lsMatrix x) η) ∂stdGaussian (EuclideanSpace ℝ (Fin T)) =
      gwMat 𝒳 (∑ t, outerSelf (x t)) := by
  rw [gwMat, gaussianWidth, ← map_toEuclideanLin_lsMatrix_stdGaussian x hS,
    integral_map (by fun_prop) (continuous_supportFn hne hR).aestronglyMeasurable]
  rfl

/-- `E[Z(θ)] = 2 τ w_T` for the diameter `Z(θ) = sup_{z ∈ 𝒳} ⟪z, θ⟫ + sup_{z ∈ 𝒳} ⟪z, -θ⟫`. -/
lemma integral_diffSup_bayesParam (hne : 𝒳.Nonempty) (hR : ∀ z ∈ 𝒳, ‖z‖ ≤ R)
    (hS : (∑ t, outerSelf (x t)).PosDef) (hτ : 0 ≤ τ) :
    ∫ g, diffSup 𝒳 (bayesParam x τ g) ∂stdGaussian (EuclideanSpace ℝ ι) =
      2 * τ * gwMat 𝒳 (∑ t, outerSelf (x t)) := by
  simp_rw [diffSup, bayesParam, ← smul_neg, supportFn_smul 𝒳 hτ, ← mul_add]
  rw [integral_const_mul, show ∫ g, supportFn 𝒳 (sqrtInvDesign x g) +
      supportFn 𝒳 (-sqrtInvDesign x g) ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∫ v, supportFn 𝒳 v + supportFn 𝒳 (-v)
        ∂(stdGaussian (EuclideanSpace ℝ ι)).map (sqrtInvDesign x) from
      (integral_map (by fun_prop) ((continuous_supportFn hne hR).add
        ((continuous_supportFn hne hR).comp continuous_neg) |>.aestronglyMeasurable)).symm,
    map_sqrtInvDesign_stdGaussian x hS]
  have := integral_diffSup_multivariateGaussian hne hR hS.inv.posSemidef
  simp only [diffSup] at this
  rw [this, gwMat]
  ring

/-- `(X v) t = ⟪x t, v⟫` for the design matrix `X` with rows `x t`. -/
lemma toEuclideanLin_designRows_apply (v : EuclideanSpace ℝ ι) (t : Fin T) :
    toEuclideanLin (designRows x) v t = ⟪x t, v⟫ := by
  rw [show toEuclideanLin (designRows x) v t = (designRows x *ᵥ WithLp.ofLp v) t from rfl,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  simp [mulVec, dotProduct, designRows, mul_comm]

end param

section linear

/-! ### The linear maps of the orthogonal decomposition

With `c = τ² / (1 + τ²)`, `W := θ - c Σ⁻¹ Xᵀ y = (1 - c) θ - c Σ⁻¹ Xᵀ η` and
`y = X θ + η`, both `W` and `y` are linear in the standard Gaussian pair `(g, η)`:
`W = bayesW₁ g + bayesW₂ η`, `y = bayesY₁ g + η`, with matrices `(1 - c) τ Σ^{-1/2}`,
`-c Σ⁻¹ Xᵀ` and `τ X Σ^{-1/2}`. -/

variable (x : Fin T → EuclideanSpace ℝ ι) (τ : ℝ)

/-- The continuous linear map of a (rectangular) matrix between Euclidean spaces. -/
noncomputable abbrev euclideanClm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    (M : Matrix m n ℝ) : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
  LinearMap.toContinuousLinearMap (toEuclideanLin M)

lemma euclideanClm_comp {m n k : Type*} [Fintype m] [Fintype n] [Fintype k] [DecidableEq n]
    [DecidableEq k] (M : Matrix m n ℝ) (N : Matrix n k ℝ) :
    euclideanClm M ∘L euclideanClm N = euclideanClm (M * N) := by
  ext v i
  simp [euclideanClm, mulVec_mulVec]

lemma adjoint_euclideanClm {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (M : Matrix m n ℝ) :
    ContinuousLinearMap.adjoint (euclideanClm M) = euclideanClm Mᵀ := by
  rw [euclideanClm, euclideanClm, ← LinearMap.adjoint_toContinuousLinearMap,
    ← toEuclideanLin_conjTranspose_eq_adjoint, conjTranspose_eq_transpose_of_trivial]

/-- The constant `c = τ² / (1 + τ²)` of the orthogonal decomposition. -/
noncomputable def bayesC : ℝ := τ ^ 2 / (1 + τ ^ 2)

lemma one_sub_bayesC_mul_sq : (1 - bayesC τ) * τ ^ 2 = bayesC τ := by
  rw [bayesC]
  field_simp
  ring

/-- The `g`-part of `W`: the matrix `(1 - c) τ Σ^{-1/2}`. -/
noncomputable def bayesW₁ : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι :=
  euclideanClm (((1 - bayesC τ) * τ) • CFC.sqrt (∑ t, outerSelf (x t))⁻¹)

/-- The `η`-part of `W`: the matrix `-c Σ⁻¹ Xᵀ`. -/
noncomputable def bayesW₂ : EuclideanSpace ℝ (Fin T) →L[ℝ] EuclideanSpace ℝ ι :=
  euclideanClm ((-bayesC τ) • lsMatrix x)

/-- The `g`-part of `y`: the matrix `τ X Σ^{-1/2}`. -/
noncomputable def bayesY₁ : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ (Fin T) :=
  euclideanClm (τ • (designRows x * CFC.sqrt (∑ t, outerSelf (x t))⁻¹))

lemma bayesW₁_apply (g : EuclideanSpace ℝ ι) :
    bayesW₁ x τ g = (1 - bayesC τ) • bayesParam x τ g := by
  simp [bayesW₁, euclideanClm, bayesParam, sqrtInvDesign, mul_smul]

lemma bayesW₂_apply (η : EuclideanSpace ℝ (Fin T)) :
    bayesW₂ x τ η = -(bayesC τ • toEuclideanLin (lsMatrix x) η) := by
  simp [bayesW₂, euclideanClm, neg_smul]

lemma bayesY₁_apply (g : EuclideanSpace ℝ ι) :
    bayesY₁ x τ g = WithLp.toLp 2 fun t ↦ ⟪x t, bayesParam x τ g⟫ := by
  ext t
  simp only [bayesY₁, euclideanClm, LinearMap.coe_toContinuousLinearMap']
  rw [show toEuclideanLin (τ • (designRows x * CFC.sqrt (∑ t, outerSelf (x t))⁻¹)) g =
      τ • toEuclideanLin (designRows x) (toEuclideanLin (CFC.sqrt (∑ t, outerSelf (x t))⁻¹) g) by
      apply WithLp.ofLp_injective; simp [mulVec_mulVec],
    PiLp.smul_apply, smul_eq_mul, toEuclideanLin_designRows_apply, bayesParam, sqrtInvDesign,
    real_inner_smul_right]
  rfl

/-- The observation vector is `y = bayesY₁ g + η`. -/
lemma toLp_bayesObs (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) :
    WithLp.toLp 2 (bayesObs x τ p) = bayesY₁ x τ p.1 + p.2 := by
  ext t
  simp [bayesObs, bayesY₁_apply]

/-- The orthogonal decomposition `θ - c Σ⁻¹ Xᵀ y = bayesW₁ g + bayesW₂ η` (blueprint
`lem:posterior_decomposition`). -/
lemma bayesParam_sub_smul_leastSquares (hS : (∑ t, outerSelf (x t)).PosDef)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) :
    bayesParam x τ p.1 - bayesC τ • leastSquares x (bayesObs x τ p) =
      bayesW₁ x τ p.1 + bayesW₂ x τ p.2 := by
  rw [bayesObs_eq, leastSquares_inner_add x hS, bayesW₁_apply, bayesW₂_apply, WithLp.toLp_ofLp,
    smul_add, sub_smul, one_smul]
  abel

/-- The cross-covariance of `W` and `y` vanishes: `W₁ Y₁ᵀ + W₂ = 0` (blueprint
`lem:posterior_decomposition`). -/
lemma bayesW₁_comp_adjoint_bayesY₁_add (hS : (∑ t, outerSelf (x t)).PosDef) :
    bayesW₁ x τ ∘L ContinuousLinearMap.adjoint (bayesY₁ x τ) +
      bayesW₂ x τ ∘L ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℝ _) = 0 := by
  rw [ContinuousLinearMap.adjoint_id, ContinuousLinearMap.comp_id, bayesW₁, bayesY₁, bayesW₂,
    adjoint_euclideanClm, euclideanClm_comp]
  have hM : CFC.sqrt (∑ t, outerSelf (x t))⁻¹ * (CFC.sqrt (∑ t, outerSelf (x t))⁻¹)ᵀ =
      (∑ t, outerSelf (x t))⁻¹ := by
    rw [transpose_sqrt, hS.inv.posSemidef.sqrt_mul_sqrt]
  have hmat : ((1 - bayesC τ) * τ) • CFC.sqrt (∑ t, outerSelf (x t))⁻¹ *
      (τ • (designRows x * CFC.sqrt (∑ t, outerSelf (x t))⁻¹))ᵀ + (-bayesC τ) • lsMatrix x = 0 := by
    rw [transpose_smul, transpose_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      ← Matrix.mul_assoc, hM, lsMatrix, ← add_smul,
      show (1 - bayesC τ) * τ * τ + -bayesC τ = 0 by
        rw [mul_assoc, ← sq, one_sub_bayesC_mul_sq, add_neg_cancel], zero_smul]
  rw [show euclideanClm (((1 - bayesC τ) * τ) • CFC.sqrt (∑ t, outerSelf (x t))⁻¹ *
      (τ • (designRows x * CFC.sqrt (∑ t, outerSelf (x t))⁻¹))ᵀ) +
      euclideanClm ((-bayesC τ) • lsMatrix x) = euclideanClm (((1 - bayesC τ) * τ) •
      CFC.sqrt (∑ t, outerSelf (x t))⁻¹ *
        (τ • (designRows x * CFC.sqrt (∑ t, outerSelf (x t))⁻¹))ᵀ +
      (-bayesC τ) • lsMatrix x) by simp [euclideanClm, map_add], hmat]
  simp [euclideanClm]

/-- The reward vector as a continuous linear map of the standard Gaussian pair. -/
noncomputable def bayesParamClm :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T) →L[ℝ] EuclideanSpace ℝ ι :=
  (τ • sqrtInvDesign x) ∘L ContinuousLinearMap.fst ℝ _ _

lemma bayesParamClm_apply (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) :
    bayesParamClm x τ p = bayesParam x τ p.1 := rfl

/-- The least-squares estimator `Σ⁻¹ Xᵀ y = θ + Σ⁻¹ Xᵀ η` as a continuous linear map of the
standard Gaussian pair. -/
noncomputable def bayesLSclm :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T) →L[ℝ] EuclideanSpace ℝ ι :=
  bayesParamClm x τ + euclideanClm (lsMatrix x) ∘L ContinuousLinearMap.snd ℝ _ _

lemma bayesLSclm_apply (hS : (∑ t, outerSelf (x t)).PosDef)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) :
    bayesLSclm x τ p = leastSquares x (bayesObs x τ p) := by
  rw [bayesObs_eq, leastSquares_inner_add x hS, WithLp.toLp_ofLp]
  rfl

end linear

section joint

/-! ### The joint law of the Bayesian model -/

variable {Ω₀ O : Type*} {mΩ₀ : MeasurableSpace Ω₀} {mO : MeasurableSpace O}

omit [Fintype ι] [DecidableEq ι] in
/-- A function of the first coordinate is integrable under `μ ⊗ₘ κ` when it is integrable
under `μ` (`κ` Markov). -/
lemma integrable_fst_compProd {μ : Measure Ω₀} [SFinite μ] {κ : Kernel Ω₀ O} [IsMarkovKernel κ]
    {f : Ω₀ → ℝ} (hf : Integrable f μ) : Integrable (fun q ↦ f q.1) (μ ⊗ₘ κ) := by
  have h : (μ ⊗ₘ κ).map Prod.fst = μ := Measure.fst_compProd μ κ
  rw [← h] at hf
  exact (integrable_map_measure hf.1 measurable_fst.aemeasurable).1 hf

omit [Fintype ι] [DecidableEq ι] in
/-- The integral of a function of the first coordinate under `μ ⊗ₘ κ` (`κ` Markov). -/
lemma integral_fst_compProd {μ : Measure Ω₀} [SFinite μ] {κ : Kernel Ω₀ O} [IsMarkovKernel κ]
    {f : Ω₀ → ℝ} (hf : Integrable f μ) : ∫ q, f q.1 ∂(μ ⊗ₘ κ) = ∫ ω, f ω ∂μ := by
  have h : (μ ⊗ₘ κ).map Prod.fst = μ := Measure.fst_compProd μ κ
  rw [← integral_map measurable_fst.aemeasurable (by rw [h]; exact hf.1), h]

omit [Fintype ι] [DecidableEq ι] in
/-- The integral of a function of the second coordinate under a product of probability
measures. -/
lemma integral_snd_prod {Ω₁ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {μ : Measure Ω₁}
    [IsProbabilityMeasure μ] {ν : Measure Ω₀} [SFinite ν] {f : Ω₀ → ℝ} (hf : Integrable f ν) :
    ∫ p, f p.2 ∂(μ.prod ν) = ∫ ω, f ω ∂ν := by
  have h : (μ.prod ν).map Prod.snd = ν := by rw [Measure.map_snd_prod, measure_univ, one_smul]
  rw [← integral_map measurable_snd.aemeasurable (by rw [h]; exact hf.1), h]

omit [Fintype ι] [DecidableEq ι] in
/-- The integral of a function of the first coordinate under a product of probability
measures. -/
lemma integral_fst_prod {Ω₁ : Type*} {mΩ₁ : MeasurableSpace Ω₁} {μ : Measure Ω₀}
    {ν : Measure Ω₁} [IsProbabilityMeasure ν] {f : Ω₀ → ℝ} (hf : Integrable f μ) :
    ∫ p, f p.1 ∂(μ.prod ν) = ∫ ω, f ω ∂μ := by
  have h : (μ.prod ν).map Prod.fst = μ := by rw [Measure.map_fst_prod, measure_univ, one_smul]
  rw [← integral_map (f := f) measurable_fst.aemeasurable (by rw [h]; exact hf.1), h]

variable (A : IdentAlg 𝒳 ℝ 𝒳) (x : Fin T → EuclideanSpace ℝ ι) (hx : ∀ t, x t ∈ 𝒳) (τ : ℝ)

/-- The history of the design `x` seen by the algorithm in the Bayesian model, as a function of
the standard Gaussian pair `(g, η)`. -/
noncomputable def bayesHist (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) :
    Fin T → 𝒳 × ℝ :=
  fixedDesignHist (fun t ↦ ⟨x t, hx t⟩) (bayesParam x τ p.1) (WithLp.ofLp p.2)

lemma bayesHist_eq (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) :
    bayesHist x hx τ p = fun t ↦ (⟨x t, hx t⟩, bayesObs x τ p t) := rfl

lemma continuous_bayesObs : Continuous fun p ↦ bayesObs x τ p := by
  refine continuous_pi fun t ↦ ?_
  exact (continuous_const.inner ((continuous_const_smul τ).comp
    ((sqrtInvDesign x).continuous.comp continuous_fst))).add
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin T ↦ ℝ) t).continuous.comp continuous_snd)

lemma measurable_bayesHist : Measurable (bayesHist x hx τ) := by
  refine measurable_pi_lambda _ fun t ↦ measurable_const.prodMk ?_
  exact ((continuous_apply t).comp (continuous_bayesObs x τ)).measurable

/-- The recommendation kernel of the Bayesian model: `(g, η) ↦ A.output T (history)`. -/
noncomputable def bayesKernel : Kernel (EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) 𝒳 :=
  (A.output T).comap (bayesHist x hx τ) (measurable_bayesHist x hx τ)

instance [IsMarkovKernel (A.output T)] : IsMarkovKernel (bayesKernel A x hx τ) := by
  unfold bayesKernel
  infer_instance

/-- The joint law of `((g, η), rec)` in the Bayesian model (blueprint `def:bayes_prior`). -/
noncomputable def bayesJoint : Measure ((EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) × 𝒳) :=
  ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ (Fin T)))) ⊗ₘ
    bayesKernel A x hx τ

instance [IsMarkovKernel (A.output T)] : IsProbabilityMeasure (bayesJoint A x hx τ) := by
  unfold bayesJoint
  infer_instance

/-- The mean recommendation `∫ rec ∂A.output T h` as a function of the history `h`. -/
noncomputable def meanOutput (h : Fin T → 𝒳 × ℝ) : EuclideanSpace ℝ ι :=
  ∫ z, (z : EuclideanSpace ℝ ι) ∂(A.output T h)

omit [DecidableEq ι] in
lemma measurable_meanOutput : Measurable (meanOutput A (T := T)) := by
  have : StronglyMeasurable fun q : (Fin T → 𝒳 × ℝ) × 𝒳 ↦ (q.2 : EuclideanSpace ℝ ι) :=
    (continuous_subtype_val.comp continuous_snd).measurable.stronglyMeasurable
  exact this.integral_kernel_prod_right'.measurable

omit [DecidableEq ι] in
lemma norm_meanOutput_le [IsMarkovKernel (A.output T)] (hR : ∀ z ∈ 𝒳, ‖z‖ ≤ R)
    (h : Fin T → 𝒳 × ℝ) : ‖meanOutput A h‖ ≤ R := by
  have hae : ∀ᵐ z : 𝒳 ∂(A.output T h), ‖Subtype.val z‖ ≤ R := ae_of_all _ fun z ↦ hR z z.2
  refine (norm_integral_le_of_norm_le_const hae).trans ?_
  simp

end joint

section identity

/-! ### The Bayes identity `E⟪rec, θ⟫ = c E⟪rec, Σ⁻¹ Xᵀ y⟫` -/

variable (A : IdentAlg 𝒳 ℝ 𝒳) (x : Fin T → EuclideanSpace ℝ ι) (hx : ∀ t, x t ∈ 𝒳) (τ : ℝ)
  [IsMarkovKernel (A.output T)]

/-- `W = (1 - c) θ - c Σ⁻¹ Xᵀ η` and `y = X θ + η` are independent (blueprint
`lem:posterior_decomposition`). -/
lemma indepFun_bayesW_bayesY (hS : (∑ t, outerSelf (x t)).PosDef) :
    IndepFun (fun p ↦ bayesW₁ x τ p.1 + bayesW₂ x τ p.2) (fun p ↦ bayesY₁ x τ p.1 + p.2)
      ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ (Fin T)))) := by
  have := indepFun_add_prod_stdGaussian_of_comp_adjoint_eq_zero
    (bayesW₁_comp_adjoint_bayesY₁_add x τ hS)
  simpa using this

/-- The linear map `(g, η) ↦ W`. -/
noncomputable def bayesWclm :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T) →L[ℝ] EuclideanSpace ℝ ι :=
  bayesW₁ x τ ∘L ContinuousLinearMap.fst ℝ _ _ + bayesW₂ x τ ∘L ContinuousLinearMap.snd ℝ _ _

lemma bayesWclm_apply (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) :
    bayesWclm x τ p = bayesW₁ x τ p.1 + bayesW₂ x τ p.2 := rfl

/-- The orthogonal decomposition in terms of the linear maps: `θ = W + c (Σ⁻¹ Xᵀ y)`. -/
lemma bayesParamClm_eq_add (hS : (∑ t, outerSelf (x t)).PosDef)
    (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) :
    bayesParamClm x τ p = bayesWclm x τ p + bayesC τ • bayesLSclm x τ p := by
  rw [bayesLSclm_apply x τ hS, bayesParamClm_apply, bayesWclm_apply,
    ← bayesParam_sub_smul_leastSquares x τ hS]
  abel

/-- The linear map `(g, η) ↦ y`. -/
noncomputable def bayesYclm :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T) →L[ℝ] EuclideanSpace ℝ (Fin T) :=
  bayesY₁ x τ ∘L ContinuousLinearMap.fst ℝ _ _ + ContinuousLinearMap.snd ℝ _ _

lemma bayesYclm_apply (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) :
    bayesYclm x τ p = bayesY₁ x τ p.1 + p.2 := rfl

/-- The history is a (measurable) function of the observation vector `y`. -/
lemma bayesHist_eq_comp (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) :
    bayesHist x hx τ p = (fun y : EuclideanSpace ℝ (Fin T) ↦ fun t ↦ (⟨x t, hx t⟩, y t))
      (bayesYclm x τ p) := by
  rw [bayesHist_eq, bayesYclm_apply, ← toLp_bayesObs]

/-- Integrability of `⟪rec, L (g, η)⟫` under the joint law for a linear `L`. -/
lemma integrable_inner_clm_bayesJoint (hR : ∀ z ∈ 𝒳, ‖z‖ ≤ R)
    (L : EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T) →L[ℝ] EuclideanSpace ℝ ι) :
    Integrable (fun q ↦ ⟪(q.2 : EuclideanSpace ℝ ι), L q.1⟫) (bayesJoint A x hx τ) := by
  have hL : Integrable (fun p ↦ ‖L p‖)
      ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ (Fin T)))) :=
    (L.integrable_comp IsGaussian.integrable_id).norm
  refine ((integrable_fst_compProd hL).const_mul R).mono' ?_ (ae_of_all _ fun q ↦ ?_)
  · exact ((continuous_subtype_val.comp continuous_snd).inner
      (L.continuous.comp continuous_fst)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hR _ q.2.2) (norm_nonneg _))

/-- `E⟪rec, W⟫ = 0`: the recommendation depends on `(g, η)` only through `y`, which is
independent of the centered vector `W` (blueprint `lem:bayes_regret_identity`,
`lem:indep_integral_zero`). -/
lemma integral_inner_bayesW_bayesJoint (hR : ∀ z ∈ 𝒳, ‖z‖ ≤ R)
    (hS : (∑ t, outerSelf (x t)).PosDef) :
    ∫ q, ⟪(q.2 : EuclideanSpace ℝ ι), bayesWclm x τ q.1⟫ ∂bayesJoint A x hx τ = 0 := by
  set μ₀ := (stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ (Fin T)))
    with hμ₀
  set G : EuclideanSpace ℝ (Fin T) → EuclideanSpace ℝ ι :=
    fun y ↦ meanOutput A (fun t ↦ (⟨x t, hx t⟩, y t)) with hG
  have hGm : Measurable G := by
    refine (measurable_meanOutput A).comp (measurable_pi_lambda _ fun t ↦ ?_)
    exact measurable_const.prodMk
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin T ↦ ℝ) t).continuous.measurable
  have hGb : ∀ y, ‖G y‖ ≤ R := fun y ↦ norm_meanOutput_le A hR _
  -- integrate out the recommendation: `E[⟪rec, W⟫ | g, η] = ⟪G y, W⟫`
  have h1 : ∫ q, ⟪(q.2 : EuclideanSpace ℝ ι), bayesWclm x τ q.1⟫ ∂bayesJoint A x hx τ =
      ∫ p, ⟪G (bayesYclm x τ p), bayesWclm x τ p⟫ ∂μ₀ := by
    rw [bayesJoint, Measure.integral_compProd (integrable_inner_clm_bayesJoint A x hx τ hR _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
    have hker : Integrable (fun b : 𝒳 ↦ (b : EuclideanSpace ℝ ι))
        (bayesKernel A x hx τ p) :=
      Integrable.of_bound continuous_subtype_val.aestronglyMeasurable R
        (Filter.Eventually.of_forall fun z ↦ hR z z.2)
    have hswap : ∀ b : 𝒳, ⟪(b : EuclideanSpace ℝ ι), bayesWclm x τ p⟫ =
        ⟪bayesWclm x τ p, (b : EuclideanSpace ℝ ι)⟫ := fun b ↦ real_inner_comm _ _
    simp_rw [hswap]
    rw [integral_inner (𝕜 := ℝ) hker, real_inner_comm]
    congr 1
    rw [bayesKernel, Kernel.comap_apply, hG]
    exact congrArg (meanOutput A) (bayesHist_eq_comp x hx τ p)
  rw [h1]
  -- `W` is centered and independent of `y`
  exact ((indepFun_bayesW_bayesY x τ hS).symm.integral_inner_comp_eq_zero
    (bayesYclm x τ).continuous.measurable.aemeasurable hGm hGb
    ((bayesWclm x τ).integrable_comp IsGaussian.integrable_id) integral_add_prod_stdGaussian)

/-- **Bayes identity** (blueprint `lem:bayes_regret_identity`):
`E⟪rec, θ⟫ = c E⟪rec, Σ⁻¹ Xᵀ y⟫` with `c = τ² / (1 + τ²)`. -/
lemma integral_inner_bayesParamClm_bayesJoint (hR : ∀ z ∈ 𝒳, ‖z‖ ≤ R)
    (hS : (∑ t, outerSelf (x t)).PosDef) :
    ∫ q, ⟪(q.2 : EuclideanSpace ℝ ι), bayesParamClm x τ q.1⟫ ∂bayesJoint A x hx τ =
      bayesC τ * ∫ q, ⟪(q.2 : EuclideanSpace ℝ ι), bayesLSclm x τ q.1⟫ ∂bayesJoint A x hx τ := by
  have hdec : ∀ q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) × 𝒳,
      ⟪(q.2 : EuclideanSpace ℝ ι), bayesParamClm x τ q.1⟫ =
        ⟪(q.2 : EuclideanSpace ℝ ι), bayesWclm x τ q.1⟫ +
          bayesC τ * ⟪(q.2 : EuclideanSpace ℝ ι), bayesLSclm x τ q.1⟫ := by
    intro q
    rw [bayesParamClm_eq_add x τ hS, inner_add_right, real_inner_smul_right]
  rw [integral_congr_ae (Filter.Eventually.of_forall hdec),
    integral_add (integrable_inner_clm_bayesJoint A x hx τ hR _)
      ((integrable_inner_clm_bayesJoint A x hx τ hR _).const_mul _),
    integral_inner_bayesW_bayesJoint A x hx τ hR hS, zero_add, integral_const_mul]

end identity

section regret

/-! ### The Bayesian lower bound on the expected simple regret -/

variable (A : IdentAlg 𝒳 ℝ 𝒳) (x : Fin T → EuclideanSpace ℝ ι) (hx : ∀ t, x t ∈ 𝒳) (τ : ℝ)
  [IsMarkovKernel (A.output T)]

/-- The integral of a function of `g` under the joint law is its integral under `N(0, I_d)`. -/
lemma integral_comp_fst_fst_bayesJoint {f : EuclideanSpace ℝ ι → ℝ}
    (hf : Integrable f (stdGaussian (EuclideanSpace ℝ ι))) :
    ∫ q, f q.1.1 ∂bayesJoint A x hx τ = ∫ g, f g ∂stdGaussian (EuclideanSpace ℝ ι) := by
  rw [bayesJoint, integral_fst_compProd (hf.comp_fst _), integral_fst_prod hf]

/-- The integral of a function of `η` under the joint law is its integral under `N(0, I_T)`. -/
lemma integral_comp_snd_fst_bayesJoint {f : EuclideanSpace ℝ (Fin T) → ℝ}
    (hf : Integrable f (stdGaussian (EuclideanSpace ℝ (Fin T)))) :
    ∫ q, f q.1.2 ∂bayesJoint A x hx τ = ∫ η, f η ∂stdGaussian (EuclideanSpace ℝ (Fin T)) := by
  rw [bayesJoint, integral_fst_compProd (hf.comp_snd _), integral_snd_prod hf]

omit [DecidableEq ι] in
/-- The support function of a Gaussian linear image is integrable. -/
lemma integrable_supportFn_comp {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {μ : Measure F} [IsGaussian μ]
    (hne : 𝒳.Nonempty) (hR : ∀ z ∈ 𝒳, ‖z‖ ≤ R) (L : F →L[ℝ] EuclideanSpace ℝ ι) :
    Integrable (fun v ↦ supportFn 𝒳 (L v)) μ := by
  refine IsGaussian.integrable_of_abs_le_add_mul_norm (A := 0) (B := R * ‖L‖)
    ((continuous_supportFn hne hR).comp L.continuous).aestronglyMeasurable fun v ↦ ?_
  rw [zero_add, mul_assoc]
  refine (abs_supportFn_le hne hR _).trans ?_
  gcongr
  · exact nonneg_of_norm_le hne hR
  · exact L.le_opNorm v

/-- `E⟪rec, Σ⁻¹ Xᵀ y⟫ ≤ τ w_T + w_T`: the recommendation is in `𝒳`, so its value is at most the
support function, and `Σ⁻¹ Xᵀ y = θ + Σ⁻¹ Xᵀ η`. -/
lemma integral_inner_bayesLSclm_le (hne : 𝒳.Nonempty) (hR : ∀ z ∈ 𝒳, ‖z‖ ≤ R)
    (hS : (∑ t, outerSelf (x t)).PosDef) (hτ : 0 ≤ τ) :
    ∫ q, ⟪(q.2 : EuclideanSpace ℝ ι), bayesLSclm x τ q.1⟫ ∂bayesJoint A x hx τ ≤
      τ * gwMat 𝒳 (∑ t, outerSelf (x t)) + gwMat 𝒳 (∑ t, outerSelf (x t)) := by
  have hsupp : Integrable (fun g ↦ supportFn 𝒳 (bayesParam x τ g))
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    integrable_supportFn_comp hne hR (τ • sqrtInvDesign x)
  have hsupp' : Integrable (fun η ↦ supportFn 𝒳 (toEuclideanLin (lsMatrix x) η))
      (stdGaussian (EuclideanSpace ℝ (Fin T))) :=
    integrable_supportFn_comp hne hR (euclideanClm (lsMatrix x))
  have hle : ∀ q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) × 𝒳,
      ⟪(q.2 : EuclideanSpace ℝ ι), bayesLSclm x τ q.1⟫ ≤
        supportFn 𝒳 (bayesParam x τ q.1.1) + supportFn 𝒳 (toEuclideanLin (lsMatrix x) q.1.2) := by
    intro q
    have h1 : bayesLSclm x τ q.1 =
        bayesParam x τ q.1.1 + toEuclideanLin (lsMatrix x) q.1.2 := rfl
    rw [h1, inner_add_right]
    gcongr
    · exact inner_le_supportFn hR q.2.2 _
    · exact inner_le_supportFn hR q.2.2 _
  have hint1 : Integrable (fun q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) × 𝒳 ↦
      supportFn 𝒳 (bayesParam x τ q.1.1)) (bayesJoint A x hx τ) :=
    integrable_fst_compProd (hsupp.comp_fst _)
  have hint2 : Integrable (fun q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) × 𝒳 ↦
      supportFn 𝒳 (toEuclideanLin (lsMatrix x) q.1.2)) (bayesJoint A x hx τ) :=
    integrable_fst_compProd (hsupp'.comp_snd _)
  calc ∫ q, ⟪(q.2 : EuclideanSpace ℝ ι), bayesLSclm x τ q.1⟫ ∂bayesJoint A x hx τ
      ≤ ∫ q, (supportFn 𝒳 (bayesParam x τ q.1.1) +
          supportFn 𝒳 (toEuclideanLin (lsMatrix x) q.1.2)) ∂bayesJoint A x hx τ :=
        integral_mono (integrable_inner_clm_bayesJoint A x hx τ hR _) (hint1.add hint2) hle
    _ = (∫ q, supportFn 𝒳 (bayesParam x τ q.1.1) ∂bayesJoint A x hx τ) +
          ∫ q, supportFn 𝒳 (toEuclideanLin (lsMatrix x) q.1.2) ∂bayesJoint A x hx τ :=
        integral_add hint1 hint2
    _ = τ * gwMat 𝒳 (∑ t, outerSelf (x t)) + gwMat 𝒳 (∑ t, outerSelf (x t)) := by
        rw [integral_comp_fst_fst_bayesJoint A x hx τ hsupp,
          integral_comp_snd_fst_bayesJoint A x hx τ hsupp',
          integral_supportFn_bayesParam x τ hne hR hS hτ,
          integral_supportFn_toEuclideanLin_lsMatrix x hne hR hS]

/-- **Bayesian lower bound on the expected simple regret** (blueprint `lem:bayes_regret_lower`):
`E[r(rec, θ)] ≥ τ w_T - c (τ w_T + w_T)` with `c = τ²/(1 + τ²)`. -/
lemma le_integral_simpleRegret_bayesJoint (hne : 𝒳.Nonempty) (hR : ∀ z ∈ 𝒳, ‖z‖ ≤ R)
    (hS : (∑ t, outerSelf (x t)).PosDef) (hτ : 0 ≤ τ) :
    τ * gwMat 𝒳 (∑ t, outerSelf (x t)) -
        bayesC τ * (τ * gwMat 𝒳 (∑ t, outerSelf (x t)) + gwMat 𝒳 (∑ t, outerSelf (x t))) ≤
      ∫ q, simpleRegret 𝒳 (bayesParam x τ q.1.1) (q.2 : EuclideanSpace ℝ ι)
        ∂bayesJoint A x hx τ := by
  have hsupp : Integrable (fun g ↦ supportFn 𝒳 (bayesParam x τ g))
      (stdGaussian (EuclideanSpace ℝ ι)) :=
    integrable_supportFn_comp hne hR (τ • sqrtInvDesign x)
  have hint1 : Integrable (fun q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) × 𝒳 ↦
      supportFn 𝒳 (bayesParam x τ q.1.1)) (bayesJoint A x hx τ) :=
    integrable_fst_compProd (hsupp.comp_fst _)
  have hdec : ∀ q : (EuclideanSpace ℝ ι × EuclideanSpace ℝ (Fin T)) × 𝒳,
      simpleRegret 𝒳 (bayesParam x τ q.1.1) (q.2 : EuclideanSpace ℝ ι) =
        supportFn 𝒳 (bayesParam x τ q.1.1) -
          ⟪(q.2 : EuclideanSpace ℝ ι), bayesParamClm x τ q.1⟫ := fun q ↦ by
    rw [simpleRegret_eq_supportFn_sub, bayesParamClm_apply, real_inner_comm]
  rw [integral_congr_ae (Filter.Eventually.of_forall hdec),
    integral_sub hint1 (integrable_inner_clm_bayesJoint A x hx τ hR _),
    integral_comp_fst_fst_bayesJoint A x hx τ hsupp,
    integral_supportFn_bayesParam x τ hne hR hS hτ,
    integral_inner_bayesParamClm_bayesJoint A x hx τ hR hS]
  have hc : 0 ≤ bayesC τ := by
    rw [bayesC]
    positivity
  gcongr
  exact integral_inner_bayesLSclm_le A x hx τ hne hR hS hτ

end regret

section pac

/-! ### The PAC upper bound on the Bayesian expected regret -/

variable [MeasurableEq 𝒳] (A : IdentAlg 𝒳 ℝ 𝒳) (x : Fin T → EuclideanSpace ℝ ι)
  (hx : ∀ t, x t ∈ 𝒳) (τ : ℝ) [IsMarkovKernel (A.output T)]

omit [MeasurableEq 𝒳] in
/-- Conditionally on `g`, the history of the Bayesian model is the fixed-design history with
reward vector `θ = bayesParam x τ g`. -/
lemma map_bayesHist_stdGaussian (g : EuclideanSpace ℝ ι) :
    (stdGaussian (EuclideanSpace ℝ (Fin T))).map (fun η ↦ bayesHist x hx τ (g, η)) =
      fixedDesignHistLaw (fun t ↦ (⟨x t, hx t⟩ : 𝒳)) (bayesParam x τ g) := by
  have h1 : (stdGaussian (EuclideanSpace ℝ (Fin T))).map (fun η ↦ bayesHist x hx τ (g, η)) =
      (Measure.pi fun _ : Fin T ↦ gaussianReal 0 1).map
        ((fun η ↦ bayesHist x hx τ (g, η)) ∘ WithLp.toLp 2) := by
    have hg : Measurable fun η : EuclideanSpace ℝ (Fin T) ↦ bayesHist x hx τ (g, η) :=
      (measurable_bayesHist x hx τ).comp measurable_prodMk_left
    rw [← map_pi_eq_stdGaussian, Measure.map_map hg (WithLp.measurable_toLp 2 _)]
  rw [h1, fixedDesignHistLaw]
  rfl

omit [MeasurableEq 𝒳] [IsMarkovKernel (A.output T)] in
/-- The kernel of the Bayesian model, conditionally on `g`. -/
lemma bayesKernel_comap (g : EuclideanSpace ℝ ι) :
    (bayesKernel A x hx τ).comap (Prod.mk g) measurable_prodMk_left =
      (A.output T).comap (fun η ↦ bayesHist x hx τ (g, η))
        (measurable_bayesHist x hx τ |>.comp measurable_prodMk_left) := by
  ext η s _
  simp [bayesKernel, Kernel.comap_apply]

/-- **The conditional PAC guarantee**: for every `g`, the recommendation of a fixed-design
`(ε, δ)`-PAC algorithm has simple regret more than `ε` with probability at most `δ`, under the
law of `(η, rec)` given `θ = bayesParam x τ g`. -/
lemma measureReal_lt_simpleRegret_bayes_le {E : Type u} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    [SecondCountableTopology E] {𝒳 : Set E} {A : IdentAlg 𝒳 ℝ 𝒳}
    {T : ℕ} [IsMarkovKernel (A.output T)] {x' : ℕ → 𝒳} {ε δ : ℝ} (hpac : IsPAC 𝒳 A ε δ)
    (hA : A.IsFixedBudget T) (hdes : A.alg = fixedDesignAlg x') (θ : E) :
    (fixedDesignPairLaw A (fun t : Fin T ↦ x' t) θ).real
      {p | ε < simpleRegret 𝒳 θ (p.2 : E)} ≤ δ := by
  have hmeas : MeasurableSet {p : (Fin T → 𝒳 × ℝ) × 𝒳 | simpleRegret 𝒳 θ (p.2 : E) ≤ ε} := by
    refine measurableSet_le ?_ measurable_const
    exact (continuous_const.sub ((continuous_subtype_val.comp continuous_snd).inner
      continuous_const)).measurable
  have h := hpac.le_measureReal_fixedDesignPairLaw hA hdes θ
  have hcompl : {p : (Fin T → 𝒳 × ℝ) × 𝒳 | ε < simpleRegret 𝒳 θ (p.2 : E)} =
      {p : (Fin T → 𝒳 × ℝ) × 𝒳 | simpleRegret 𝒳 θ (p.2 : E) ≤ ε}ᶜ := by
    ext p
    simp [not_le]
  rw [hcompl, measureReal_compl hmeas, probReal_univ]
  linarith

omit [MeasurableEq 𝒳] in
/-- The conditional failure probability of the Bayesian model equals that of the fixed-design
pair law with reward vector `θ = bayesParam x τ g`. -/
lemma measureReal_lt_simpleRegret_comap_eq (g : EuclideanSpace ℝ ι) {ε : ℝ} :
    ((stdGaussian (EuclideanSpace ℝ (Fin T))) ⊗ₘ
        (bayesKernel A x hx τ).comap (Prod.mk g) measurable_prodMk_left).real
      {q | ε < simpleRegret 𝒳 (bayesParam x τ g) (q.2 : EuclideanSpace ℝ ι)} =
      (fixedDesignPairLaw A (fun t : Fin T ↦ (⟨x t, hx t⟩ : 𝒳)) (bayesParam x τ g)).real
        {p | ε < simpleRegret 𝒳 (bayesParam x τ g) (p.2 : EuclideanSpace ℝ ι)} := by
  have hg : Measurable fun η : EuclideanSpace ℝ (Fin T) ↦ bayesHist x hx τ (g, η) :=
    (measurable_bayesHist x hx τ).comp measurable_prodMk_left
  have hset : MeasurableSet {z : 𝒳 | ε < simpleRegret 𝒳 (bayesParam x τ g) (z : _)} := by
    refine measurableSet_lt measurable_const ?_
    exact (continuous_const.sub (continuous_subtype_val.inner continuous_const)).measurable
  have hmap := map_snd_compProd_comap (stdGaussian (EuclideanSpace ℝ (Fin T))) (A.output T) hg
    (fun _ ↦ inferInstance)
  rw [bayesKernel_comap A x hx τ g, fixedDesignPairLaw, ← map_bayesHist_stdGaussian x hx τ g]
  have h1 : ∀ (μ : Measure ((Fin T → 𝒳 × ℝ) × 𝒳)),
      μ.real {p | ε < simpleRegret 𝒳 (bayesParam x τ g) (p.2 : EuclideanSpace ℝ ι)} =
        (μ.map Prod.snd).real {z : 𝒳 | ε < simpleRegret 𝒳 (bayesParam x τ g) (z : _)} := by
    intro μ
    rw [Measure.real, Measure.real, Measure.map_apply measurable_snd hset]
    rfl
  have h2 : ∀ (μ : Measure (EuclideanSpace ℝ (Fin T) × 𝒳)),
      μ.real {q | ε < simpleRegret 𝒳 (bayesParam x τ g) (q.2 : EuclideanSpace ℝ ι)} =
        (μ.map Prod.snd).real {z : 𝒳 | ε < simpleRegret 𝒳 (bayesParam x τ g) (z : _)} := by
    intro μ
    rw [Measure.real, Measure.real, Measure.map_apply measurable_snd hset]
    rfl
  rw [h1, h2, hmap]

omit [MeasurableEq 𝒳] in
/-- **The PAC upper bound on the Bayesian expected regret** (blueprint
`lem:pac_expected_regret`): `E[r(rec, θ)] ≤ ε + δ · 2 τ w_T`. -/
lemma integral_simpleRegret_bayesJoint_le (hne : 𝒳.Nonempty) (hR : ∀ z ∈ 𝒳, ‖z‖ ≤ R)
    (hS : (∑ t, outerSelf (x t)).PosDef) (hτ : 0 ≤ τ) {ε δ : ℝ} (hε : 0 ≤ ε)
    (hδ : ∀ g, (fixedDesignPairLaw A (fun t : Fin T ↦ (⟨x t, hx t⟩ : 𝒳)) (bayesParam x τ g)).real
      {p | ε < simpleRegret 𝒳 (bayesParam x τ g) (p.2 : EuclideanSpace ℝ ι)} ≤ δ) :
    ∫ q, simpleRegret 𝒳 (bayesParam x τ q.1.1) (q.2 : EuclideanSpace ℝ ι)
        ∂bayesJoint A x hx τ ≤ ε + δ * (2 * τ * gwMat 𝒳 (∑ t, outerSelf (x t))) := by
  have hZ : Integrable (fun g ↦ diffSup 𝒳 (bayesParam x τ g))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
    have h1 := integrable_supportFn_comp (𝒳 := 𝒳) (R := R)
      (μ := stdGaussian (EuclideanSpace ℝ ι)) hne hR (τ • sqrtInvDesign x)
    have h2 := integrable_supportFn_comp (𝒳 := 𝒳) (R := R)
      (μ := stdGaussian (EuclideanSpace ℝ ι)) hne hR (-(τ • sqrtInvDesign x))
    exact h1.add h2
  have hZint : ∫ g, diffSup 𝒳 (bayesParam x τ g) ∂stdGaussian (EuclideanSpace ℝ ι) =
      2 * τ * gwMat 𝒳 (∑ t, outerSelf (x t)) := integral_diffSup_bayesParam x τ hne hR hS hτ
  have hmeas : Measurable (Function.uncurry fun (g : EuclideanSpace ℝ ι) (z : 𝒳) ↦
      simpleRegret 𝒳 (bayesParam x τ g) (z : EuclideanSpace ℝ ι)) := by
    refine Continuous.measurable ?_
    exact ((continuous_supportFn hne hR).comp
      (((sqrtInvDesign x).continuous.const_smul τ).comp continuous_fst)).sub
      ((continuous_subtype_val.comp continuous_snd).inner
        (((sqrtInvDesign x).continuous.const_smul τ).comp continuous_fst))
  have hr0 : ∀ (g : EuclideanSpace ℝ ι) (z : 𝒳),
      0 ≤ simpleRegret 𝒳 (bayesParam x τ g) (z : EuclideanSpace ℝ ι) := fun g z ↦ by
    rw [simpleRegret_eq_supportFn_sub, sub_nonneg]
    exact inner_le_supportFn hR z.2 _
  have hrZ : ∀ (g : EuclideanSpace ℝ ι) (z : 𝒳),
      simpleRegret 𝒳 (bayesParam x τ g) (z : EuclideanSpace ℝ ι) ≤
        diffSup 𝒳 (bayesParam x τ g) := fun g z ↦ by
    rw [simpleRegret_eq_supportFn_sub, diffSup, sub_eq_add_neg]
    gcongr
    rw [← inner_neg_right]
    exact inner_le_supportFn hR z.2 _
  have hmain := integral_le_add_mul_integral_of_measureReal_le
    (stdGaussian (EuclideanSpace ℝ ι)) (stdGaussian (EuclideanSpace ℝ (Fin T)))
    (bayesKernel A x hx τ) hmeas hZ hr0 hrZ hε
    (fun g ↦ by rw [measureReal_lt_simpleRegret_comap_eq A x hx τ g]; exact hδ g)
  rw [hZint] at hmain
  exact hmain

end pac



end COLT83
