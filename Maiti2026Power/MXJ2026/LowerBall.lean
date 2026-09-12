/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.MXJ2026.BayesKernel
public import Maiti2026Power.MXJ2026.PosteriorGaussian
public import Maiti2026Power.MXJ2026.UnitBall
public import Maiti2026Power.Mathlib.Matrix.TraceInv
public import Maiti2026Power.Mathlib.Probability.GaussianAbsMoment
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The Bayesian lower bound on the unit ball

For an identification algorithm `A` with budget `T` on the unit ball of `ℝ^ι`, under the prior
`θ ~ N(0, σ² I)` the joint law of `(θ, history, recommendation)` is
`bayesJointLaw A T σ = (π.prod Q₀).withDensity (likelihood θ h)`, where `Q₀` is the law of
(history, recommendation) under pure noise (`bayesJointLaw_eq_withDensity`). The likelihood of a
history `h` is the Gaussian tilt with parameters `b(h) = ∑ y_t x_t` and `S(h) = ∑ x_t x_tᵀ`
(`likelihood_eq_gaussTilt`), so the posterior identities of `PosteriorGaussian.lean` apply for
each fixed history: writing `u(h) = ∫ ℓ_θ(h) • θ dπ = Z(h) m(h)`, the Bayesian expectation of
`⟪rec, θ⟫` is at most `∫ ‖u(h)‖ dQ₀` (`integral_inner_bayesJointLaw_le`), which is at most
`√(σ² d - d² / (d σ⁻² + T))` by Cauchy–Schwarz and the posterior second moment
(`integral_norm_postU_le`, using `tr V(h) ≥ d² / (d σ⁻² + T)`, `le_trace_postCov_histS`).
Hence the Bayesian simple regret is at least `√(2/π) σ √d - √(σ² d - d² / (d σ⁻² + T))`
(`integral_simpleRegret_bayesJointLaw_ge`, blueprint `lem:bayes_regret_ball`), and truncating
the prior gives a reward vector of norm at most `10 d / √T` with expected simple regret at least
`3 d / (40 √T)` (`exists_norm_le_and_le_integral_simpleRegret_pairKernel`, blueprint
`thm:ball_simple_regret_lower`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Learning.LinearBandit Real Matrix Finset
open scoped ENNReal RealInnerProductSpace MatrixOrder

namespace Maiti2026Power

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {T : ℕ}

section stats

/-- The statistic `b(h) = ∑ t, y_t x_t` of a history on the unit ball. -/
noncomputable def histB (h : Hist Unit (unitBall ι) ℝ T) : EuclideanSpace ℝ ι :=
  ∑ t, (h t).feedback • ((h t).action : EuclideanSpace ℝ ι)

/-- The design matrix `S(h) = ∑ t, x_t x_tᵀ` of a history on the unit ball. -/
noncomputable def histS (h : Hist Unit (unitBall ι) ℝ T) : Matrix ι ι ℝ :=
  ∑ t, outerSelf ((h t).action : EuclideanSpace ℝ ι)

omit [DecidableEq ι] in
lemma posSemidef_histS (h : Hist Unit (unitBall ι) ℝ T) : (histS h).PosSemidef :=
  posSemidef_sum_outerSelf _ _

omit [DecidableEq ι] in
lemma trace_histS_le (h : Hist Unit (unitBall ι) ℝ T) : (histS h).trace ≤ T := by
  rw [histS, Matrix.trace_sum]
  simp_rw [trace_outerSelf]
  calc ∑ t, ‖((h t).action : EuclideanSpace ℝ ι)‖ ^ 2 ≤ ∑ _t : Fin T, (1 : ℝ) :=
        Finset.sum_le_sum fun t _ ↦
          pow_le_one₀ (norm_nonneg _) (norm_le_one_of_mem_unitBall (h t).action.2)
    _ = T := by simp

/-- The likelihood ratio of a history on the unit ball is the Gaussian tilt with parameters
`b(h)`, `S(h)`. -/
lemma likelihood_eq_gaussTilt (θ : EuclideanSpace ℝ ι) (h : Hist Unit (unitBall ι) ℝ T) :
    likelihood θ h = gaussTilt (histB h) (histS h) θ := by
  unfold likelihood gaussTilt stepLogLR
  congr 1
  rw [histB, histS, sum_inner, toEuclideanCLM_sum_outerSelf_apply, inner_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [real_inner_smul_left, real_inner_smul_right, real_inner_comm]
  ring

/-- **Lower bound on the posterior trace** (blueprint `lem:trace_inv_lower`):
`tr V(h) ≥ d² / (d σ⁻² + T)`. -/
lemma le_trace_postCov_histS {σ : ℝ} (hσ : 0 < σ) (h : Hist Unit (unitBall ι) ℝ T) :
    (Fintype.card ι : ℝ) ^ 2 / (Fintype.card ι * σ⁻¹ ^ 2 + T) ≤
      (postCov σ (histS h)).trace := by
  have hP := posDef_postPrec (posSemidef_histS h) hσ.ne'
  have h1 := hP.card_sq_div_trace_le_trace_inv
  have h2 : (postPrec σ (histS h)).trace ≤ Fintype.card ι * σ⁻¹ ^ 2 + T := by
    rw [postPrec, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    linarith [trace_histS_le h]
  refine le_trans ?_ h1
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp
  exact div_le_div_of_nonneg_left (by positivity) hP.trace_pos h2

end stats

section joint

variable (A : IdentAlg (unitBall ι) ℝ (unitBall ι)) (T : ℕ) (σ : ℝ)

/-- The law of (history, recommendation) of `A` under pure noise. -/
noncomputable def noisePairLaw : Measure (Hist Unit (unitBall ι) ℝ T × unitBall ι) :=
  noiseHistLaw A.alg T ⊗ₘ A.output T

instance : IsProbabilityMeasure (noisePairLaw A T) := by
  unfold noisePairLaw
  infer_instance

omit [DecidableEq ι] in
lemma measurable_likelihood_fst (θ : EuclideanSpace ℝ ι) :
    Measurable fun p : Hist Unit (unitBall ι) ℝ T × unitBall ι ↦ likelihood θ p.1 :=
  (measurable_likelihood θ T).comp measurable_fst

omit [DecidableEq ι] in
lemma measurable_likelihood_prod_fst :
    Measurable fun q : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦
      likelihood q.1 q.2.1 :=
  (measurable_likelihood_prod T).comp (measurable_fst.prodMk measurable_snd.fst)

omit [DecidableEq ι] in
lemma pairKernel_eq_withDensity (θ : EuclideanSpace ℝ ι) :
    pairKernel A T θ =
      (noisePairLaw A T).withDensity fun p ↦ ENNReal.ofReal (likelihood θ p.1) := by
  have hf : Measurable fun h : Hist Unit (unitBall ι) ℝ T ↦ ENNReal.ofReal (likelihood θ h) :=
    ENNReal.measurable_ofReal.comp (measurable_likelihood θ T)
  rw [pairKernel_apply, histKernel_apply, noisePairLaw, Measure.withDensity_compProd hf]

omit [DecidableEq ι] in
/-- The likelihood integrates to `1` against the pure-noise law. -/
lemma lintegral_ofReal_likelihood_noisePairLaw (θ : EuclideanSpace ℝ ι) :
    ∫⁻ p, ENNReal.ofReal (likelihood θ p.1) ∂noisePairLaw A T = 1 := by
  have h1 : (pairKernel A T θ) Set.univ = 1 := measure_univ
  rwa [pairKernel_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] at h1

omit [DecidableEq ι] in
lemma integral_likelihood_noisePairLaw (θ : EuclideanSpace ℝ ι) :
    ∫ p, likelihood θ p.1 ∂noisePairLaw A T = 1 := by
  have hf : Measurable fun p : Hist Unit (unitBall ι) ℝ T × unitBall ι ↦
      ENNReal.ofReal (likelihood θ p.1) :=
    ENNReal.measurable_ofReal.comp (measurable_likelihood_fst T θ)
  have h := integral_withDensity_eq_integral_toReal_smul (μ := noisePairLaw A T) hf
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) (fun _ ↦ (1 : ℝ))
  rw [← pairKernel_eq_withDensity, integral_const, probReal_univ, one_smul] at h
  calc ∫ p, likelihood θ p.1 ∂noisePairLaw A T
      = ∫ p, (ENNReal.ofReal (likelihood θ p.1)).toReal • (1 : ℝ) ∂noisePairLaw A T :=
        integral_congr_ae (ae_of_all _ fun p ↦ by
          simp [ENNReal.toReal_ofReal (likelihood_pos _ _).le])
    _ = 1 := h.symm

omit [DecidableEq ι] in
lemma integrable_likelihood_noisePairLaw (θ : EuclideanSpace ℝ ι) :
    Integrable (fun p ↦ likelihood θ p.1) (noisePairLaw A T) := by
  have h1 := lintegral_ofReal_likelihood_noisePairLaw A T θ
  have := integrable_toReal_of_lintegral_ne_top (μ := noisePairLaw A T)
    (f := fun p ↦ ENNReal.ofReal (likelihood θ p.1))
    (ENNReal.measurable_ofReal.comp (measurable_likelihood_fst T θ)).aemeasurable
    (by rw [h1]; exact ENNReal.one_ne_top)
  simpa [ENNReal.toReal_ofReal (likelihood_pos _ _).le] using this

/-- **The Bayesian joint law** of (reward vector, history, recommendation): the prior
`N(0, σ² I)` composed with the run kernel. -/
noncomputable def bayesJointLaw :
    Measure (EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι)) :=
  gaussPrior σ ⊗ₘ pairKernel A T

instance : IsProbabilityMeasure (bayesJointLaw A T σ) := by
  unfold bayesJointLaw
  infer_instance

/-- The joint law is the product of the prior and the pure-noise law, with density the
likelihood. -/
lemma bayesJointLaw_eq_withDensity :
    bayesJointLaw A T σ = ((gaussPrior σ).prod (noisePairLaw A T)).withDensity
      fun q ↦ ENNReal.ofReal (likelihood q.1 q.2.1) := by
  have hm : Measurable (Function.uncurry fun (θ : EuclideanSpace ℝ ι)
      (p : Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦ ENNReal.ofReal (likelihood θ p.1)) :=
    ENNReal.measurable_ofReal.comp (measurable_likelihood_prod_fst T)
  have hk : pairKernel A T = Kernel.withDensity (Kernel.const _ (noisePairLaw A T))
      fun θ p ↦ ENNReal.ofReal (likelihood θ p.1) := by
    ext θ : 1
    rw [Kernel.withDensity_apply _ hm, Kernel.const_apply, pairKernel_eq_withDensity]
  have : IsSFiniteKernel (Kernel.withDensity (Kernel.const _ (noisePairLaw A T))
      fun (θ : EuclideanSpace ℝ ι) (p : Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦
        ENNReal.ofReal (likelihood θ p.1)) := by
    rw [← hk]
    infer_instance
  rw [bayesJointLaw, hk, Measure.compProd_withDensity hm, Measure.compProd_const]

/-- Integrals against the joint law as integrals against the product measure. -/
lemma integral_bayesJointLaw
    (f : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) → ℝ) :
    ∫ q, f q ∂bayesJointLaw A T σ =
      ∫ q, likelihood q.1 q.2.1 * f q ∂((gaussPrior σ).prod (noisePairLaw A T)) := by
  have hf : Measurable fun q : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦
      ENNReal.ofReal (likelihood q.1 q.2.1) :=
    ENNReal.measurable_ofReal.comp (measurable_likelihood_prod_fst T)
  rw [bayesJointLaw_eq_withDensity, integral_withDensity_eq_integral_toReal_smul hf
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (likelihood_pos _ _).le, smul_eq_mul]

lemma integrable_bayesJointLaw_iff
    (f : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) → ℝ) :
    Integrable f (bayesJointLaw A T σ) ↔
      Integrable (fun q ↦ likelihood q.1 q.2.1 * f q) ((gaussPrior σ).prod (noisePairLaw A T)) := by
  have hf : Measurable fun q : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦
      ENNReal.ofReal (likelihood q.1 q.2.1) :=
    ENNReal.measurable_ofReal.comp (measurable_likelihood_prod_fst T)
  rw [bayesJointLaw_eq_withDensity, integrable_withDensity_iff_integrable_smul' hf
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (likelihood_pos _ _).le, smul_eq_mul]

/-- For a function `g` of `θ` alone, `∫ ℓ(θ, h) g(θ) d(π ⊗ Q₀) = ∫ g dπ`, with integrability. -/
lemma integrable_likelihood_mul_prod {g : EuclideanSpace ℝ ι → ℝ} (hg : Measurable g)
    (hgi : Integrable g (gaussPrior σ)) :
    Integrable (fun q ↦ likelihood q.1 q.2.1 * g q.1) ((gaussPrior σ).prod (noisePairLaw A T)) := by
  have hmeas : Measurable fun q : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦
      likelihood q.1 q.2.1 * g q.1 :=
    (measurable_likelihood_prod_fst T).mul (hg.comp measurable_fst)
  refine (integrable_prod_iff hmeas.aestronglyMeasurable).2 ⟨ae_of_all _ fun θ ↦ ?_, ?_⟩
  · exact (integrable_likelihood_noisePairLaw A T θ).mul_const (g θ)
  · refine hgi.norm.congr (ae_of_all _ fun θ ↦ ?_)
    simp only [norm_mul, Real.norm_of_nonneg (likelihood_pos _ _).le]
    rw [integral_mul_const, integral_likelihood_noisePairLaw, one_mul]

lemma integral_likelihood_mul_prod {g : EuclideanSpace ℝ ι → ℝ} (hg : Measurable g)
    (hgi : Integrable g (gaussPrior σ)) :
    ∫ q, likelihood q.1 q.2.1 * g q.1 ∂((gaussPrior σ).prod (noisePairLaw A T)) =
      ∫ θ, g θ ∂gaussPrior σ := by
  rw [integral_prod _ (integrable_likelihood_mul_prod A T σ hg hgi)]
  refine integral_congr_ae (ae_of_all _ fun θ ↦ ?_)
  simp only
  rw [integral_mul_const, integral_likelihood_noisePairLaw, one_mul]

end joint

section regret

variable (A : IdentAlg (unitBall ι) ℝ (unitBall ι)) {σ : ℝ}

/-- The posterior quantities of a history: `u(h) = ∫ ℓ_θ(h) • θ dπ = Z(h) m(h)`. -/
noncomputable def postU (σ : ℝ) (h : Hist Unit (unitBall ι) ℝ T) : EuclideanSpace ℝ ι :=
  ∫ θ, likelihood θ h • θ ∂gaussPrior σ

/-- `Z(h) = ∫ ℓ_θ(h) dπ`. -/
noncomputable def postZ (σ : ℝ) (h : Hist Unit (unitBall ι) ℝ T) : ℝ :=
  ∫ θ, likelihood θ h ∂gaussPrior σ

/-- `N(h) = ∫ ‖θ‖² ℓ_θ(h) dπ`. -/
noncomputable def postN (σ : ℝ) (h : Hist Unit (unitBall ι) ℝ T) : ℝ :=
  ∫ θ, ‖θ‖ ^ 2 * likelihood θ h ∂gaussPrior σ

omit [DecidableEq ι] in
lemma measurable_likelihood_swap :
    Measurable fun p : Hist Unit (unitBall ι) ℝ T × EuclideanSpace ℝ ι ↦ likelihood p.2 p.1 :=
  (measurable_likelihood_prod T).comp (measurable_snd.prodMk measurable_fst)

lemma stronglyMeasurable_postU : StronglyMeasurable (postU (T := T) (ι := ι) σ) :=
  StronglyMeasurable.integral_prod_right'
    (f := fun p : Hist Unit (unitBall ι) ℝ T × EuclideanSpace ℝ ι ↦ likelihood p.2 p.1 • p.2)
    ((measurable_likelihood_swap (T := T)).smul measurable_snd).stronglyMeasurable

lemma stronglyMeasurable_postZ : StronglyMeasurable (postZ (T := T) (ι := ι) σ) :=
  StronglyMeasurable.integral_prod_right'
    (f := fun p : Hist Unit (unitBall ι) ℝ T × EuclideanSpace ℝ ι ↦ likelihood p.2 p.1)
    (measurable_likelihood_swap (T := T)).stronglyMeasurable

lemma stronglyMeasurable_postN : StronglyMeasurable (postN (T := T) (ι := ι) σ) :=
  StronglyMeasurable.integral_prod_right'
    (f := fun p : Hist Unit (unitBall ι) ℝ T × EuclideanSpace ℝ ι ↦ ‖p.2‖ ^ 2 * likelihood p.2 p.1)
    ((measurable_snd.norm.pow_const 2).mul (measurable_likelihood_swap (T := T))).stronglyMeasurable

lemma postZ_pos (h : Hist Unit (unitBall ι) ℝ T) : 0 < postZ σ h := by
  unfold postZ
  simp_rw [likelihood_eq_gaussTilt]
  exact integral_gaussTilt_pos (posSemidef_histS h)

/-- `‖u(h)‖² ≤ Z(h) (N(h) - c Z(h))` with `c = d² / (d σ⁻² + T)`: the posterior second moment. -/
lemma norm_postU_sq_le (hσ : 0 < σ) (h : Hist Unit (unitBall ι) ℝ T) :
    ‖postU σ h‖ ^ 2 ≤ postZ σ h *
      (postN σ h - (Fintype.card ι : ℝ) ^ 2 / (Fintype.card ι * σ⁻¹ ^ 2 + T) * postZ σ h) := by
  have hS := posSemidef_histS h
  have hZ := postZ_pos (σ := σ) h
  have hu : postU σ h = postZ σ h • postMean σ (histB h) (histS h) := by
    unfold postU postZ
    simp_rw [likelihood_eq_gaussTilt]
    exact integral_gaussTilt_smul_eq hS hσ
  have hN : postN σ h = ((postCov σ (histS h)).trace + ‖postMean σ (histB h) (histS h)‖ ^ 2) *
      postZ σ h := by
    unfold postN postZ
    simp_rw [likelihood_eq_gaussTilt]
    exact integral_norm_sq_mul_gaussTilt hS hσ
  have htr := le_trace_postCov_histS hσ h
  rw [hu, norm_smul, Real.norm_of_nonneg hZ.le, mul_pow, hN]
  nlinarith [sq_nonneg ‖postMean σ (histB h) (histS h)‖, mul_le_mul_of_nonneg_right htr hZ.le]

/-- `‖u(h)‖ ≤ √Z(h) √(N(h) - c Z(h))`. -/
lemma norm_postU_le (hσ : 0 < σ) (h : Hist Unit (unitBall ι) ℝ T) :
    ‖postU σ h‖ ≤ √(postZ σ h) *
      √(postN σ h - (Fintype.card ι : ℝ) ^ 2 / (Fintype.card ι * σ⁻¹ ^ 2 + T) * postZ σ h) := by
  rw [← Real.sqrt_mul (postZ_pos h).le, Real.le_sqrt (norm_nonneg _)]
  · exact norm_postU_sq_le hσ h
  · have := norm_postU_sq_le hσ h
    nlinarith [sq_nonneg ‖postU σ h‖, postZ_pos (σ := σ) h]

section prior

lemma integrable_norm_gaussPrior :
    Integrable (fun θ : EuclideanSpace ℝ ι ↦ ‖θ‖) (gaussPrior σ) :=
  (IsGaussian.integrable_id (μ := gaussPrior σ)).norm

lemma integrable_norm_sq_gaussPrior :
    Integrable (fun θ : EuclideanSpace ℝ ι ↦ ‖θ‖ ^ 2) (gaussPrior σ) := by
  have h : MemLp (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) 2 (gaussPrior σ) :=
    IsGaussian.memLp_two_id
  exact h.norm.integrable_sq

lemma integral_norm_sq_gaussPrior :
    ∫ θ : EuclideanSpace ℝ ι, ‖θ‖ ^ 2 ∂gaussPrior σ = σ ^ 2 * Fintype.card ι := by
  rw [gaussPrior, integral_norm_sq_multivariateGaussian (posSemidef_sq_smul_one (ι := ι) σ),
    Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]

/-- `E‖θ‖ ≥ √(2/π) σ √d` under the prior. -/
lemma le_integral_norm_gaussPrior (hσ : 0 < σ) :
    √(2 / π) * σ * √(Fintype.card ι) ≤ ∫ θ : EuclideanSpace ℝ ι, ‖θ‖ ∂gaussPrior σ := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Fintype.card_eq_zero, Nat.cast_zero, Real.sqrt_zero, mul_zero]
    exact integral_nonneg fun _ ↦ norm_nonneg _
  have hd : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hc : ∑ _i : ι, (1 / √(Fintype.card ι : ℝ)) ^ 2 ≤ 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_pow, one_pow, Real.sq_sqrt hd.le,
      mul_one_div_cancel hd.ne']
  have h := sum_mul_sqrt_diag_le_integral_norm_multivariateGaussian
    (posSemidef_sq_smul_one (ι := ι) σ) (c := fun _ ↦ 1 / √(Fintype.card ι))
    (fun _ ↦ by positivity) hc
  refine le_trans (le_of_eq ?_) h
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, Real.sqrt_sq hσ.le,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have e : (Fintype.card ι : ℝ) * (1 / √(Fintype.card ι) * σ) = √(Fintype.card ι) * σ := by
    rw [← mul_assoc, mul_one_div, Real.div_sqrt]
  rw [e]
  ring

end prior

section bound

/-- The mean recommendation: `⟪rec, θ⟫` is `P`-integrable against the likelihood. -/
lemma integrable_likelihood_mul_inner_prod :
    Integrable (fun q : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦
      likelihood q.1 q.2.1 * ⟪((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι), q.1⟫)
      ((gaussPrior σ).prod (noisePairLaw A T)) := by
  have hmeas : Measurable fun q : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦
      likelihood q.1 q.2.1 * ⟪((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι), q.1⟫ :=
    (measurable_likelihood_prod_fst T).mul
      ((measurable_subtype_coe.comp measurable_snd.snd).inner measurable_fst)
  refine (integrable_likelihood_mul_prod A T σ (g := fun θ ↦ ‖θ‖) measurable_norm
    (integrable_norm_gaussPrior (ι := ι) (σ := σ))).mono' hmeas.aestronglyMeasurable
    (ae_of_all _ fun q ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (likelihood_pos _ _)]
  refine mul_le_mul_of_nonneg_left ?_ (likelihood_pos _ _).le
  calc |⟪((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι), q.1⟫|
      ≤ ‖((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι)‖ * ‖q.1‖ := abs_real_inner_le_norm _ _
    _ ≤ 1 * ‖q.1‖ := by gcongr; exact norm_le_one_of_mem_unitBall q.2.2.2
    _ = ‖q.1‖ := one_mul _

lemma integrable_norm_postU :
    Integrable (fun p : Hist Unit (unitBall ι) ℝ T × unitBall ι ↦ ‖postU σ p.1‖)
      (noisePairLaw A T) := by
  have hdom := (integrable_likelihood_mul_prod A T σ (g := fun θ ↦ ‖θ‖) measurable_norm
    (integrable_norm_gaussPrior (ι := ι) (σ := σ))).integral_prod_right
  refine hdom.mono' ((stronglyMeasurable_postU (T := T) (σ := σ)).norm.comp_measurable
    measurable_fst).aestronglyMeasurable (ae_of_all _ fun p ↦ ?_)
  rw [norm_norm]
  unfold postU
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext θ
  rw [norm_smul, Real.norm_of_nonneg (likelihood_pos _ _).le]

/-- **The Bayesian expectation of `⟪rec, θ⟫`** is at most `∫ ‖u(h)‖ dQ₀`. -/
lemma integral_inner_bayesJointLaw_le :
    ∫ q, ⟪((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι), q.1⟫ ∂bayesJointLaw A T σ ≤
      ∫ p, ‖postU σ p.1‖ ∂noisePairLaw A T := by
  have hint := integrable_likelihood_mul_inner_prod A (T := T) (σ := σ)
  rw [integral_bayesJointLaw, integral_prod_symm _ hint]
  have hpt : ∀ p : Hist Unit (unitBall ι) ℝ T × unitBall ι,
      ∫ θ, likelihood θ p.1 * ⟪((p.2 : unitBall ι) : EuclideanSpace ℝ ι), θ⟫ ∂gaussPrior σ =
        ⟪((p.2 : unitBall ι) : EuclideanSpace ℝ ι), postU σ p.1⟫ := by
    intro p
    unfold postU
    simp_rw [likelihood_eq_gaussTilt]
    rw [← integral_inner_mul_gaussTilt (posSemidef_histS p.1)]
    congr 1
    funext θ
    ring
  refine integral_mono hint.integral_prod_right (integrable_norm_postU A) fun p ↦ ?_
  simp only
  rw [hpt]
  calc ⟪((p.2 : unitBall ι) : EuclideanSpace ℝ ι), postU σ p.1⟫
      ≤ ‖((p.2 : unitBall ι) : EuclideanSpace ℝ ι)‖ * ‖postU σ p.1‖ := real_inner_le_norm _ _
    _ ≤ 1 * ‖postU σ p.1‖ := by gcongr; exact norm_le_one_of_mem_unitBall p.2.2
    _ = ‖postU σ p.1‖ := one_mul _

lemma integrable_postZ :
    Integrable (fun p : Hist Unit (unitBall ι) ℝ T × unitBall ι ↦ postZ σ p.1) (noisePairLaw A T) :=
  ((integrable_likelihood_mul_prod A T σ (g := fun _ ↦ 1) measurable_const
    (integrable_const 1)).integral_prod_right).congr (ae_of_all _ fun p ↦ by simp [postZ])

lemma integral_postZ : ∫ p, postZ σ p.1 ∂noisePairLaw A T = 1 := by
  have h := integral_likelihood_mul_prod A T σ (g := fun _ ↦ 1) measurable_const
    (integrable_const 1)
  rw [integral_prod_symm _ (integrable_likelihood_mul_prod A T σ measurable_const
    (integrable_const 1))] at h
  simpa [postZ] using h

lemma integrable_postN :
    Integrable (fun p : Hist Unit (unitBall ι) ℝ T × unitBall ι ↦ postN σ p.1) (noisePairLaw A T) :=
  ((integrable_likelihood_mul_prod A T σ (g := fun θ ↦ ‖θ‖ ^ 2) (by fun_prop)
    (integrable_norm_sq_gaussPrior (ι := ι) (σ := σ))).integral_prod_right).congr
    (ae_of_all _ fun p ↦ by
      simp only [postN]
      congr 1
      funext θ
      ring)

lemma integral_postN : ∫ p, postN σ p.1 ∂noisePairLaw A T = σ ^ 2 * Fintype.card ι := by
  have h := integral_likelihood_mul_prod A T σ (g := fun θ ↦ ‖θ‖ ^ 2) (by fun_prop)
    (integrable_norm_sq_gaussPrior (ι := ι) (σ := σ))
  rw [integral_prod_symm _ (integrable_likelihood_mul_prod A T σ (g := fun θ ↦ ‖θ‖ ^ 2)
    (by fun_prop) (integrable_norm_sq_gaussPrior (ι := ι) (σ := σ))),
    integral_norm_sq_gaussPrior] at h
  rw [← h]
  refine integral_congr_ae (ae_of_all _ fun p ↦ ?_)
  simp only [postN]
  congr 1
  funext θ
  ring

/-- **Cauchy–Schwarz**: `∫ ‖u(h)‖ dQ₀ ≤ √(σ² d - d² / (d σ⁻² + T))`. -/
lemma integral_norm_postU_le (hσ : 0 < σ) :
    ∫ p, ‖postU σ p.1‖ ∂noisePairLaw A T ≤
      √(σ ^ 2 * Fintype.card ι -
        (Fintype.card ι : ℝ) ^ 2 / (Fintype.card ι * σ⁻¹ ^ 2 + T)) := by
  set c : ℝ := (Fintype.card ι : ℝ) ^ 2 / (Fintype.card ι * σ⁻¹ ^ 2 + T) with hc
  have hZ := integrable_postZ A (T := T) (σ := σ)
  have hN := integrable_postN A (T := T) (σ := σ)
  have hZ0 : ∀ p : Hist Unit (unitBall ι) ℝ T × unitBall ι, 0 ≤ postZ σ p.1 :=
    fun p ↦ (postZ_pos _).le
  have hNZ : ∀ p : Hist Unit (unitBall ι) ℝ T × unitBall ι, 0 ≤ postN σ p.1 - c * postZ σ p.1 := by
    intro p
    have h1 := norm_postU_sq_le hσ p.1
    have h2 := postZ_pos (σ := σ) p.1
    by_contra hlt
    push Not at hlt
    nlinarith [sq_nonneg ‖postU σ p.1‖]
  have hmZ : Measurable fun p : Hist Unit (unitBall ι) ℝ T × unitBall ι ↦ postZ σ p.1 :=
    (stronglyMeasurable_postZ (T := T) (σ := σ)).measurable.comp measurable_fst
  have hmN : Measurable fun p : Hist Unit (unitBall ι) ℝ T × unitBall ι ↦ postN σ p.1 :=
    (stronglyMeasurable_postN (T := T) (σ := σ)).measurable.comp measurable_fst
  have hNZi : Integrable (fun p : Hist Unit (unitBall ι) ℝ T × unitBall ι ↦
      postN σ p.1 - c * postZ σ p.1) (noisePairLaw A T) := hN.sub (hZ.const_mul c)
  have hm2 : Measurable fun p : Hist Unit (unitBall ι) ℝ T × unitBall ι ↦
      postN σ p.1 - c * postZ σ p.1 := hmN.sub (hmZ.const_mul c)
  have hbound : Integrable (fun p : Hist Unit (unitBall ι) ℝ T × unitBall ι ↦
      1 / 2 * (postZ σ p.1 + (postN σ p.1 - c * postZ σ p.1))) (noisePairLaw A T) :=
    (hZ.add hNZi).const_mul _
  have hI1 : Integrable (fun p : Hist Unit (unitBall ι) ℝ T × unitBall ι ↦
      √(postZ σ p.1) * √(postN σ p.1 - c * postZ σ p.1)) (noisePairLaw A T) := by
    refine hbound.mono' (hmZ.sqrt.mul hm2.sqrt).aestronglyMeasurable (ae_of_all _ fun p ↦ ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    have h3 := two_mul_le_add_sq (√(postZ σ p.1)) (√(postN σ p.1 - c * postZ σ p.1))
    rw [Real.sq_sqrt (hZ0 p), Real.sq_sqrt (hNZ p)] at h3
    linarith
  have hL1 : MemLp (fun p : Hist Unit (unitBall ι) ℝ T × unitBall ι ↦ √(postZ σ p.1))
      (ENNReal.ofReal 2) (noisePairLaw A T) := by
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq hmZ.sqrt.aestronglyMeasurable]
    refine hZ.congr (ae_of_all _ fun p ↦ ?_)
    simp [Real.sq_sqrt (hZ0 p)]
  have hL2 : MemLp (fun p : Hist Unit (unitBall ι) ℝ T × unitBall ι ↦
      √(postN σ p.1 - c * postZ σ p.1)) (ENNReal.ofReal 2) (noisePairLaw A T) := by
    rw [ENNReal.ofReal_ofNat, memLp_two_iff_integrable_sq hm2.sqrt.aestronglyMeasurable]
    refine hNZi.congr (ae_of_all _ fun p ↦ ?_)
    simp [Real.sq_sqrt (hNZ p)]
  calc ∫ p, ‖postU σ p.1‖ ∂noisePairLaw A T
      ≤ ∫ p, √(postZ σ p.1) * √(postN σ p.1 - c * postZ σ p.1) ∂noisePairLaw A T :=
        integral_mono (integrable_norm_postU A) hI1 fun p ↦ norm_postU_le hσ p.1
    _ ≤ (∫ p, √(postZ σ p.1) ^ (2 : ℝ) ∂noisePairLaw A T) ^ (1 / (2 : ℝ)) *
        (∫ p, √(postN σ p.1 - c * postZ σ p.1) ^ (2 : ℝ) ∂noisePairLaw A T) ^ (1 / (2 : ℝ)) :=
        integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
          (ae_of_all _ fun p ↦ Real.sqrt_nonneg _) (ae_of_all _ fun p ↦ Real.sqrt_nonneg _) hL1 hL2
    _ = √(σ ^ 2 * Fintype.card ι - c) := by
        simp_rw [Real.rpow_two, Real.sq_sqrt (hZ0 _), Real.sq_sqrt (hNZ _)]
        rw [integral_postZ, integral_sub hN (hZ.const_mul c), integral_const_mul, integral_postN,
          integral_postZ, mul_one, Real.one_rpow, one_mul, Real.sqrt_eq_rpow]

/-- **Bayesian simple regret on the ball** (blueprint `lem:bayes_regret_ball`):
`E[r] ≥ √(2/π) σ √d - √(σ² d - d² / (d σ⁻² + T))`. -/
theorem integral_simpleRegret_bayesJointLaw_ge (hσ : 0 < σ) :
    √(2 / π) * σ * √(Fintype.card ι) -
      √(σ ^ 2 * Fintype.card ι - (Fintype.card ι : ℝ) ^ 2 / (Fintype.card ι * σ⁻¹ ^ 2 + T)) ≤
      ∫ q, simpleRegret (unitBall ι) q.1 ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι)
        ∂bayesJointLaw A T σ := by
  have hQ1 : Integrable (fun q : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦
      ‖q.1‖) (bayesJointLaw A T σ) :=
    (integrable_bayesJointLaw_iff A T σ _).2
      (integrable_likelihood_mul_prod A T σ measurable_norm
        (integrable_norm_gaussPrior (ι := ι) (σ := σ)))
  have hQ2 : Integrable (fun q : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦
      ⟪((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι), q.1⟫) (bayesJointLaw A T σ) :=
    (integrable_bayesJointLaw_iff A T σ _).2 (integrable_likelihood_mul_inner_prod A)
  have h1 : ∫ q, simpleRegret (unitBall ι) q.1 ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι)
      ∂bayesJointLaw A T σ = ∫ q, ‖q.1‖ ∂bayesJointLaw A T σ -
        ∫ q, ⟪((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι), q.1⟫ ∂bayesJointLaw A T σ := by
    simp_rw [simpleRegret_unitBall]
    exact integral_sub hQ1 hQ2
  have h2 : ∫ q, ‖q.1‖ ∂bayesJointLaw A T σ = ∫ θ : EuclideanSpace ℝ ι, ‖θ‖ ∂gaussPrior σ := by
    rw [integral_bayesJointLaw, integral_likelihood_mul_prod A T σ measurable_norm
      (integrable_norm_gaussPrior (ι := ι) (σ := σ))]
  rw [h1, h2]
  have h3 := integral_inner_bayesJointLaw_le A (T := T) (σ := σ)
  have h4 := integral_norm_postU_le A (T := T) hσ
  have h5 := le_integral_norm_gaussPrior (ι := ι) hσ
  linarith

end bound

section hardInstance

omit [DecidableEq ι] in
lemma simpleRegret_unitBall_nonneg (θ : EuclideanSpace ℝ ι) (x : unitBall ι) :
    0 ≤ simpleRegret (unitBall ι) θ x := by
  rw [simpleRegret_unitBall]
  have h1 := real_inner_le_norm (x : EuclideanSpace ℝ ι) θ
  have h2 := norm_le_one_of_mem_unitBall x.2
  nlinarith [norm_nonneg θ, norm_nonneg (x : EuclideanSpace ℝ ι)]

omit [DecidableEq ι] in
lemma simpleRegret_unitBall_le (θ : EuclideanSpace ℝ ι) (x : unitBall ι) :
    simpleRegret (unitBall ι) θ x ≤ 2 * ‖θ‖ := by
  rw [simpleRegret_unitBall]
  have h1 := abs_real_inner_le_norm (x : EuclideanSpace ℝ ι) θ
  have h2 := norm_le_one_of_mem_unitBall x.2
  have h3 : ‖(x : EuclideanSpace ℝ ι)‖ * ‖θ‖ ≤ ‖θ‖ := mul_le_of_le_one_left (norm_nonneg _) h2
  have h4 := neg_abs_le ⟪(x : EuclideanSpace ℝ ι), θ⟫
  linarith

omit [DecidableEq ι] in
lemma measurable_simpleRegret_unitBall_prod :
    Measurable fun q : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦
      simpleRegret (unitBall ι) q.1 ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι) := by
  simp_rw [simpleRegret_unitBall]
  exact measurable_fst.norm.sub
    ((measurable_subtype_coe.comp measurable_snd.snd).inner measurable_fst)

variable (T) in
/-- The expected simple regret of `A` on the instance `θ` (budget `T`). -/
noncomputable def expRegret (θ : EuclideanSpace ℝ ι) : ℝ :=
  ∫ p, simpleRegret (unitBall ι) θ ((p.2 : unitBall ι) : EuclideanSpace ℝ ι) ∂pairKernel A T θ

omit [DecidableEq ι] in
/-- `θ ↦ E_θ[r]` is measurable (blueprint `lem:pb_kernel_of_likelihood`). -/
lemma stronglyMeasurable_expRegret : StronglyMeasurable (expRegret T A) :=
  StronglyMeasurable.integral_kernel_prod_right'
    (f := fun q : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦
      simpleRegret (unitBall ι) q.1 ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι))
    (measurable_simpleRegret_unitBall_prod (T := T)).stronglyMeasurable

omit [DecidableEq ι] in
lemma expRegret_nonneg (θ : EuclideanSpace ℝ ι) : 0 ≤ expRegret T A θ :=
  integral_nonneg fun p ↦ simpleRegret_unitBall_nonneg θ p.2

omit [DecidableEq ι] in
lemma expRegret_le (θ : EuclideanSpace ℝ ι) : expRegret T A θ ≤ 2 * ‖θ‖ := by
  unfold expRegret
  calc ∫ p, simpleRegret (unitBall ι) θ ((p.2 : unitBall ι) : EuclideanSpace ℝ ι) ∂pairKernel A T θ
      ≤ ∫ _p, 2 * ‖θ‖ ∂pairKernel A T θ :=
        integral_mono_of_nonneg (ae_of_all _ fun p ↦ simpleRegret_unitBall_nonneg θ p.2)
          (integrable_const _) (ae_of_all _ fun p ↦ simpleRegret_unitBall_le θ p.2)
    _ = 2 * ‖θ‖ := by rw [integral_const, probReal_univ, one_smul]

lemma integrable_expRegret : Integrable (expRegret T A) (gaussPrior σ) :=
  ((integrable_norm_gaussPrior (ι := ι) (σ := σ)).const_mul 2).mono'
    (stronglyMeasurable_expRegret A).aestronglyMeasurable (ae_of_all _ fun θ ↦ by
      rw [Real.norm_of_nonneg (expRegret_nonneg A θ)]
      exact expRegret_le A θ)

lemma integrable_simpleRegret_bayesJointLaw :
    Integrable (fun q : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦
      simpleRegret (unitBall ι) q.1 ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι))
      (bayesJointLaw A T σ) := by
  have h : Integrable (fun q : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦
      2 * ‖q.1‖) (bayesJointLaw A T σ) :=
    (integrable_bayesJointLaw_iff A T σ _).2 (integrable_likelihood_mul_prod A T σ
      (g := fun θ ↦ 2 * ‖θ‖) (by fun_prop)
      ((integrable_norm_gaussPrior (ι := ι) (σ := σ)).const_mul 2))
  refine h.mono' (measurable_simpleRegret_unitBall_prod (T := T)).aestronglyMeasurable
    (ae_of_all _ fun q ↦ ?_)
  rw [Real.norm_of_nonneg (simpleRegret_unitBall_nonneg _ _)]
  exact simpleRegret_unitBall_le _ _

lemma integrable_norm_sq_bayesJointLaw :
    Integrable (fun q : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦ ‖q.1‖ ^ 2)
      (bayesJointLaw A T σ) :=
  (integrable_bayesJointLaw_iff A T σ _).2 (integrable_likelihood_mul_prod A T σ
    (g := fun θ ↦ ‖θ‖ ^ 2) (by fun_prop) (integrable_norm_sq_gaussPrior (ι := ι) (σ := σ)))

lemma integral_norm_sq_bayesJointLaw :
    ∫ q, ‖q.1‖ ^ 2 ∂bayesJointLaw A T σ = σ ^ 2 * Fintype.card ι := by
  rw [integral_bayesJointLaw, integral_likelihood_mul_prod A T σ (g := fun θ ↦ ‖θ‖ ^ 2)
    (by fun_prop) (integrable_norm_sq_gaussPrior (ι := ι) (σ := σ)), integral_norm_sq_gaussPrior]

/-- **Truncation of the prior**: `E[1{‖θ‖ ≤ R} r] ≥ E[r] - 2 σ² d / R`. -/
lemma integral_indicator_mul_simpleRegret_bayesJointLaw_ge {R : ℝ} (hR : 0 < R) :
    ∫ q, simpleRegret (unitBall ι) q.1 ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι)
        ∂bayesJointLaw A T σ - 2 * σ ^ 2 * Fintype.card ι / R ≤
      ∫ q, {θ : EuclideanSpace ℝ ι | ‖θ‖ ≤ R}.indicator (fun _ ↦ (1 : ℝ)) q.1 *
        simpleRegret (unitBall ι) q.1 ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι)
        ∂bayesJointLaw A T σ := by
  have hint := integrable_simpleRegret_bayesJointLaw A (T := T) (σ := σ)
  have hB : MeasurableSet {θ : EuclideanSpace ℝ ι | ‖θ‖ ≤ R} :=
    measurableSet_le measurable_norm measurable_const
  have hind : Integrable (fun q : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦
      {θ : EuclideanSpace ℝ ι | ‖θ‖ ≤ R}.indicator (fun _ ↦ (1 : ℝ)) q.1 *
        simpleRegret (unitBall ι) q.1 ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι))
      (bayesJointLaw A T σ) := by
    refine hint.mono' (((measurable_const.indicator hB).comp measurable_fst).mul
      (measurable_simpleRegret_unitBall_prod (T := T))).aestronglyMeasurable
      (ae_of_all _ fun q ↦ ?_)
    rw [norm_mul, Real.norm_of_nonneg (simpleRegret_unitBall_nonneg _ _)]
    refine mul_le_of_le_one_left (simpleRegret_unitBall_nonneg _ _) ?_
    exact (norm_indicator_le_norm_self _ _).trans (by simp)
  have h2 : ∫ q, simpleRegret (unitBall ι) q.1 ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι)
      ∂bayesJointLaw A T σ -
      ∫ q, {θ : EuclideanSpace ℝ ι | ‖θ‖ ≤ R}.indicator (fun _ ↦ (1 : ℝ)) q.1 *
        simpleRegret (unitBall ι) q.1 ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι)
        ∂bayesJointLaw A T σ ≤ ∫ q, 2 * ‖q.1‖ ^ 2 / R ∂bayesJointLaw A T σ := by
    rw [← integral_sub hint hind]
    refine integral_mono (hint.sub hind)
      (((integrable_norm_sq_bayesJointLaw A (T := T) (σ := σ)).const_mul 2).div_const R) fun q ↦ ?_
    simp only
    by_cases hq : ‖q.1‖ ≤ R
    · rw [Set.indicator_of_mem (show q.1 ∈ {θ : EuclideanSpace ℝ ι | ‖θ‖ ≤ R} from hq), one_mul,
        sub_self]
      positivity
    · rw [Set.indicator_of_notMem (show q.1 ∉ {θ : EuclideanSpace ℝ ι | ‖θ‖ ≤ R} from hq),
        zero_mul, sub_zero]
      push Not at hq
      calc simpleRegret (unitBall ι) q.1 ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι)
          ≤ 2 * ‖q.1‖ := simpleRegret_unitBall_le _ _
        _ ≤ 2 * ‖q.1‖ ^ 2 / R := by
            rw [le_div_iff₀ hR]
            nlinarith [norm_nonneg q.1]
  rw [integral_div, integral_const_mul, integral_norm_sq_bayesJointLaw,
    show (2 : ℝ) * (σ ^ 2 * Fintype.card ι) / R = 2 * σ ^ 2 * Fintype.card ι / R by ring] at h2
  linarith

/-- The truncated Bayesian regret is the prior average of `E_θ[r]` over `‖θ‖ ≤ R`
(blueprint `lem:pb_joint_fubini`). -/
lemma integral_indicator_mul_simpleRegret_bayesJointLaw (R : ℝ) :
    ∫ q, {θ : EuclideanSpace ℝ ι | ‖θ‖ ≤ R}.indicator (fun _ ↦ (1 : ℝ)) q.1 *
        simpleRegret (unitBall ι) q.1 ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι)
        ∂bayesJointLaw A T σ =
      ∫ θ, {θ : EuclideanSpace ℝ ι | ‖θ‖ ≤ R}.indicator (fun _ ↦ (1 : ℝ)) θ * expRegret T A θ
        ∂gaussPrior σ := by
  have hint := integrable_simpleRegret_bayesJointLaw A (T := T) (σ := σ)
  have hB : MeasurableSet {θ : EuclideanSpace ℝ ι | ‖θ‖ ≤ R} :=
    measurableSet_le measurable_norm measurable_const
  have hind : Integrable (fun q : EuclideanSpace ℝ ι × (Hist Unit (unitBall ι) ℝ T × unitBall ι) ↦
      {θ : EuclideanSpace ℝ ι | ‖θ‖ ≤ R}.indicator (fun _ ↦ (1 : ℝ)) q.1 *
        simpleRegret (unitBall ι) q.1 ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι))
      (gaussPrior σ ⊗ₘ pairKernel A T) := by
    refine hint.mono' (((measurable_const.indicator hB).comp measurable_fst).mul
      (measurable_simpleRegret_unitBall_prod (T := T))).aestronglyMeasurable
      (ae_of_all _ fun q ↦ ?_)
    rw [norm_mul, Real.norm_of_nonneg (simpleRegret_unitBall_nonneg _ _)]
    refine mul_le_of_le_one_left (simpleRegret_unitBall_nonneg _ _) ?_
    exact (norm_indicator_le_norm_self _ _).trans (by simp)
  rw [bayesJointLaw, Measure.integral_compProd hind]
  refine integral_congr_ae (ae_of_all _ fun θ ↦ ?_)
  simp only
  rw [integral_const_mul]
  rfl

/-- **Markov**: the prior puts mass at least `1 - σ² d / R²` on the ball of radius `R`. -/
lemma le_measureReal_norm_le_gaussPrior {R : ℝ} (hR : 0 < R) :
    1 - σ ^ 2 * Fintype.card ι / R ^ 2 ≤
      (gaussPrior σ).real {θ : EuclideanSpace ℝ ι | ‖θ‖ ≤ R} := by
  have h := mul_meas_ge_le_integral_of_nonneg (μ := gaussPrior σ)
    (f := fun θ : EuclideanSpace ℝ ι ↦ ‖θ‖ ^ 2) (ae_of_all _ fun θ ↦ sq_nonneg _)
    (integrable_norm_sq_gaussPrior (ι := ι) (σ := σ)) (R ^ 2)
  rw [integral_norm_sq_gaussPrior] at h
  have hmeas : MeasurableSet {θ : EuclideanSpace ℝ ι | R ^ 2 ≤ ‖θ‖ ^ 2} :=
    measurableSet_le measurable_const (measurable_norm.pow_const 2)
  have hsub : {θ : EuclideanSpace ℝ ι | R ^ 2 ≤ ‖θ‖ ^ 2}ᶜ ⊆ {θ | ‖θ‖ ≤ R} := by
    intro θ hθ
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hθ
    exact (lt_of_pow_lt_pow_left₀ 2 hR.le hθ).le
  have hR2 : 0 < R ^ 2 := by positivity
  calc 1 - σ ^ 2 * Fintype.card ι / R ^ 2
      ≤ 1 - (gaussPrior σ).real {θ : EuclideanSpace ℝ ι | R ^ 2 ≤ ‖θ‖ ^ 2} := by
        rw [sub_le_sub_iff_left, le_div_iff₀ hR2]
        linarith
    _ = (gaussPrior σ).real {θ : EuclideanSpace ℝ ι | R ^ 2 ≤ ‖θ‖ ^ 2}ᶜ := by
        rw [measureReal_compl hmeas, probReal_univ]
    _ ≤ (gaussPrior σ).real {θ | ‖θ‖ ≤ R} := measureReal_mono hsub

/-- **Existence of a hard instance** (blueprint `thm:ball_simple_regret_lower` (ii)): if the
truncated Bayesian regret is at least `c ≥ 0` and the prior charges the ball of radius `R`, some
`θ` with `‖θ‖ ≤ R` has `E_θ[r] ≥ c`. -/
lemma exists_norm_le_and_le_expRegret {R : ℝ} (hR : 0 < R)
    (hRσ : σ ^ 2 * Fintype.card ι < R ^ 2) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : c ≤ ∫ q, {θ : EuclideanSpace ℝ ι | ‖θ‖ ≤ R}.indicator (fun _ ↦ (1 : ℝ)) q.1 *
        simpleRegret (unitBall ι) q.1 ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι)
        ∂bayesJointLaw A T σ) :
    ∃ θ : EuclideanSpace ℝ ι, ‖θ‖ ≤ R ∧ c ≤ expRegret T A θ := by
  by_contra hcon
  push Not at hcon
  rw [integral_indicator_mul_simpleRegret_bayesJointLaw (ι := ι) A (T := T) (σ := σ) R] at hc
  set B : Set (EuclideanSpace ℝ ι) := {θ | ‖θ‖ ≤ R} with hB_def
  have hB : MeasurableSet B := measurableSet_le measurable_norm measurable_const
  have hBpos : 0 < (gaussPrior σ).real B := by
    have h1 := le_measureReal_norm_le_gaussPrior (ι := ι) (σ := σ) hR
    have h2 : σ ^ 2 * Fintype.card ι / R ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]
      exact hRσ
    linarith
  set g : EuclideanSpace ℝ ι → ℝ := fun θ ↦ B.indicator (fun _ ↦ (1 : ℝ)) θ * (c - expRegret T A θ)
    with hg_def
  have hgint : Integrable g (gaussPrior σ) := by
    have h1 : Integrable (fun θ ↦ B.indicator (fun _ ↦ (1 : ℝ)) θ * c) (gaussPrior σ) :=
      ((integrable_const (1 : ℝ)).indicator hB).mul_const c
    have h2 : Integrable (fun θ ↦ B.indicator (fun _ ↦ (1 : ℝ)) θ * expRegret T A θ)
        (gaussPrior σ) :=
      (integrable_expRegret A (σ := σ)).bdd_mul (c := 1)
        ((measurable_const.indicator hB).aestronglyMeasurable)
        (ae_of_all _ fun θ ↦ (norm_indicator_le_norm_self _ _).trans (by simp))
    refine (h1.sub h2).congr (ae_of_all _ fun θ ↦ ?_)
    simp only [hg_def, Pi.sub_apply]
    ring
  have hg0 : 0 ≤ g := fun θ ↦ by
    simp only [hg_def, Pi.zero_apply]
    by_cases hθ : θ ∈ B
    · rw [Set.indicator_of_mem hθ, one_mul]
      have := hcon θ hθ
      linarith
    · rw [Set.indicator_of_notMem hθ, zero_mul]
  have hpos : 0 < ∫ θ, g θ ∂gaussPrior σ := by
    rw [integral_pos_iff_support_of_nonneg hg0 hgint]
    refine lt_of_lt_of_le ?_ (measure_mono (s := B) (t := Function.support g) fun θ hθ ↦ ?_)
    · rw [measureReal_def] at hBpos
      exact (ENNReal.toReal_pos_iff.1 hBpos).1
    · simp only [Function.mem_support, hg_def, Set.indicator_of_mem hθ, one_mul]
      exact (sub_pos.2 (hcon θ hθ)).ne'
  have hle : ∫ θ, g θ ∂gaussPrior σ ≤ 0 := by
    have h1 : ∫ θ, g θ ∂gaussPrior σ = c * (gaussPrior σ).real B -
        ∫ θ, B.indicator (fun _ ↦ (1 : ℝ)) θ * expRegret T A θ ∂gaussPrior σ := by
      have h2 : Integrable (fun θ ↦ B.indicator (fun _ ↦ (1 : ℝ)) θ * expRegret T A θ)
          (gaussPrior σ) :=
        (integrable_expRegret A (σ := σ)).bdd_mul (c := 1)
          ((measurable_const.indicator hB).aestronglyMeasurable)
          (ae_of_all _ fun θ ↦ (norm_indicator_le_norm_self _ _).trans (by simp))
      have h3 : Integrable (fun θ ↦ c * B.indicator (fun _ ↦ (1 : ℝ)) θ) (gaussPrior σ) :=
        ((integrable_const (1 : ℝ)).indicator hB).const_mul c
      have e : g = fun θ ↦ c * B.indicator (fun _ ↦ (1 : ℝ)) θ -
          B.indicator (fun _ ↦ (1 : ℝ)) θ * expRegret T A θ := by
        funext θ
        simp only [hg_def]
        ring
      have h5 : ∫ x, B.indicator (fun _ ↦ (1 : ℝ)) x ∂gaussPrior σ = (gaussPrior σ).real B :=
        integral_indicator_one hB
      rw [e, integral_sub h3 h2, integral_const_mul, h5]
    rw [h1]
    have h4 : (gaussPrior σ).real B ≤ 1 := measureReal_le_one
    nlinarith
  linarith

end hardInstance

section main

omit [DecidableEq ι] in
/-- With budget `0`, the law of the recommendation does not depend on the reward vector. -/
lemma pairKernel_zero_eq (θ θ' : EuclideanSpace ℝ ι) :
    pairKernel A 0 θ = pairKernel A 0 θ' := by
  have h : ∀ ϑ : EuclideanSpace ℝ ι, pairKernel A 0 ϑ = noisePairLaw A 0 := fun ϑ ↦ by
    rw [pairKernel_eq_withDensity]
    have : (fun p : Hist Unit (unitBall ι) ℝ 0 × unitBall ι ↦
        ENNReal.ofReal (likelihood ϑ p.1)) = 1 := by
      funext p
      simp [likelihood]
    rw [this, withDensity_one]
  rw [h θ, h θ']

omit [DecidableEq ι] in
/-- **No algorithm with budget `0` is PAC** on the unit ball (`d ≥ 1`) for `δ < 1/2`: the
recommendation does not depend on `θ`, and the instances `± 2ε e` have regrets summing to `4ε`
at every arm. -/
lemma not_isPAC_unitBall_of_isFixedBudget_zero (hd : 0 < Fintype.card ι) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : δ < 1 / 2) (hA : A.IsFixedBudget 0) : ¬ IsPAC (unitBall ι) A ε δ := by
  classical
  intro hpac
  obtain ⟨i⟩ : Nonempty ι := Fintype.card_pos_iff.1 hd
  set e : EuclideanSpace ℝ ι := EuclideanSpace.single i 1 with he
  have hen : ‖e‖ = 1 := by simp [he]
  set θ : EuclideanSpace ℝ ι := (2 * ε) • e with hθ
  have hθn : ‖θ‖ = 2 * ε := by
    rw [hθ, norm_smul, hen, mul_one, Real.norm_of_nonneg (by positivity)]
  have h1 := hpac.le_measureReal_pairKernel hA θ
  have h2 := hpac.le_measureReal_pairKernel hA (-θ)
  rw [pairKernel_zero_eq A (-θ) θ] at h2
  have hdisj : {p : Hist Unit (unitBall ι) ℝ 0 × unitBall ι |
      simpleRegret (unitBall ι) (-θ) ((p.2 : unitBall ι) : EuclideanSpace ℝ ι) ≤ ε} ⊆
      {p : Hist Unit (unitBall ι) ℝ 0 × unitBall ι |
        simpleRegret (unitBall ι) θ ((p.2 : unitBall ι) : EuclideanSpace ℝ ι) ≤ ε}ᶜ := by
    intro p hp
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le] at hp ⊢
    rw [simpleRegret_unitBall, norm_neg, inner_neg_right, hθn] at hp
    rw [simpleRegret_unitBall, hθn]
    linarith
  have h3 := measureReal_mono (μ := pairKernel A 0 θ) hdisj
  rw [measureReal_compl (measurableSet_simpleRegret_le θ ε), probReal_univ] at h3
  linarith

omit [DecidableEq ι] in
/-- **Simple-regret lower bound on the unit ball** (blueprint `thm:ball_simple_regret_lower`):
for a budget `T ≥ 1` and `d ≥ 1`, some reward vector `θ` with `‖θ‖ ≤ 10 d / √T` has expected
simple regret at least `3 d / (40 √T)`. The prior is `N(0, σ² I)` with `σ² = d / (4 T)` and the
truncation radius is `R = 10 d / √T`. -/
theorem exists_norm_le_and_le_expRegret_unitBall (hT : 0 < T)
    (hd : 0 < Fintype.card ι) :
    ∃ θ : EuclideanSpace ℝ ι, ‖θ‖ ≤ 10 * Fintype.card ι / √T ∧
      3 * Fintype.card ι / (40 * √T) ≤ expRegret T A θ := by
  classical
  obtain ⟨d, hd_def⟩ : ∃ d : ℝ, d = Fintype.card ι := ⟨_, rfl⟩
  obtain ⟨s, hs_def⟩ : ∃ s : ℝ, s = √T := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd_def]; exact_mod_cast hd
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
  have hs0 : 0 < s := by rw [hs_def]; exact Real.sqrt_pos.2 hT0
  have hs2 : s ^ 2 = T := by rw [hs_def]; exact Real.sq_sqrt hT0.le
  set σ : ℝ := √d / (2 * s) with hσ_def
  have hσ : 0 < σ := by positivity
  have hσ2 : σ ^ 2 = d / (4 * s ^ 2) := by
    rw [hσ_def, div_pow, mul_pow, Real.sq_sqrt hd0.le]
    ring
  have hσd : σ * √d = d / (2 * s) := by
    rw [hσ_def, div_mul_eq_mul_div, Real.mul_self_sqrt hd0.le]
  set R : ℝ := 10 * d / s with hR_def
  have hR : 0 < R := by positivity
  -- the Bayesian regret is at least `d / (8 s)`
  have h1 := integral_simpleRegret_bayesJointLaw_ge A (T := T) hσ
  rw [← hd_def, ← hs2] at h1
  have hinner : σ ^ 2 * d - d ^ 2 / (d * σ⁻¹ ^ 2 + s ^ 2) = d ^ 2 / (20 * s ^ 2) := by
    rw [inv_pow, hσ2]
    field_simp
    ring
  rw [hinner] at h1
  have hsqrt2pi : (79 / 100 : ℝ) ≤ √(2 / π) := by
    rw [Real.le_sqrt (by norm_num) (by positivity), le_div_iff₀ Real.pi_pos]
    nlinarith [Real.pi_lt_d2]
  have hsq20 : √(d ^ 2 / (20 * s ^ 2)) ≤ d / ((447 / 100 : ℝ) * s) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    rw [div_pow, mul_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg d) (by positivity) (by nlinarith)
  have hlow : (79 / 100 : ℝ) * (d / (2 * s)) ≤ √(2 / π) * σ * √d := by
    rw [mul_assoc, hσd]
    exact mul_le_mul_of_nonneg_right hsqrt2pi (by positivity)
  set u : ℝ := d / s with hu_def
  have hu0 : 0 < u := by positivity
  have e1 : d / (2 * s) = u / 2 := by rw [hu_def]; ring
  have e2 : d / ((447 / 100 : ℝ) * s) = u / (447 / 100 : ℝ) := by rw [hu_def]; ring
  have e3 : d / (8 * s) = u / 8 := by rw [hu_def]; ring
  have e4 : d / (20 * s) = u / 20 := by rw [hu_def]; ring
  have e5 : 3 * d / (40 * s) = 3 * u / 40 := by rw [hu_def]; ring
  have hbayes : d / (8 * s) ≤ ∫ q, simpleRegret (unitBall ι) q.1
      ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι) ∂bayesJointLaw A T σ := by
    rw [e1] at hlow
    rw [e2] at hsq20
    rw [e3]
    linarith
  -- truncation
  have h2 := integral_indicator_mul_simpleRegret_bayesJointLaw_ge A (T := T) (σ := σ) hR
  rw [← hd_def] at h2
  have htr : 2 * σ ^ 2 * d / R = d / (20 * s) := by
    rw [hσ2, hR_def]
    field_simp
    ring
  rw [htr] at h2
  have hc : 3 * d / (40 * s) ≤ ∫ q, {θ : EuclideanSpace ℝ ι | ‖θ‖ ≤ R}.indicator
      (fun _ ↦ (1 : ℝ)) q.1 * simpleRegret (unitBall ι) q.1
        ((q.2.2 : unitBall ι) : EuclideanSpace ℝ ι) ∂bayesJointLaw A T σ := by
    rw [e3] at hbayes
    rw [e4] at h2
    rw [e5]
    linarith
  have hRσ : σ ^ 2 * d < R ^ 2 := by
    rw [hσ2, hR_def, div_pow, mul_pow, show d / (4 * s ^ 2) * d = d ^ 2 / (4 * s ^ 2) by ring,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg d, sq_nonneg s, mul_pos hd0 hs0]
  have hRσ' : σ ^ 2 * Fintype.card ι < R ^ 2 := by rwa [← hd_def]
  obtain ⟨θ, hθR, hθ⟩ := exists_norm_le_and_le_expRegret A hR hRσ' (by positivity) hc
  refine ⟨θ, ?_, ?_⟩
  · rwa [← hd_def, ← hs_def]
  · rwa [← hd_def, ← hs_def]

end main

end regret

end Maiti2026Power
