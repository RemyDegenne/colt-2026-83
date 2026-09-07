/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.LeanMachineLearning.EnvDensity
public import Maiti2026Power.Mathlib.Probability.GaussianDensityRatio
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Likelihood ratio of a linear Gaussian history

In the linear Gaussian bandit with reward vector `θ`, the observation kernel at `x` is
`N(⟪x, θ⟫, 1) = N(0, 1).withDensity (y ↦ exp (y ⟪x, θ⟫ - ⟪x, θ⟫² / 2))`
(`linearGaussianKernel_eq_withDensity`). Hence, for any algorithm, the law of the history of `T`
rounds under `θ` is the law under pure noise (`θ = 0`) with density the likelihood ratio
`likelihood θ h = exp (∑ t, (y t ⟪x t, θ⟫ - ⟪x t, θ⟫² / 2))`
(`IsAlgEnvSeq.map_finHistory_eq_withDensity_likelihood`, blueprint `cor:pb_gaussian_likelihood`),
by the environment likelihood ratio `IsAlgEnvSeq.map_finHistory_eq_withDensity_env`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Real
open scoped ENNReal RealInnerProductSpace

namespace Learning.LinearBandit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {𝒳 : Set E}

/-- The one-step log-likelihood ratio of the observation `y` at the action `x` under `θ` with
respect to pure noise: `y ⟪x, θ⟫ - ⟪x, θ⟫² / 2`. -/
noncomputable def stepLogLR (θ : E) (x : 𝒳) (y : ℝ) : ℝ := y * ⟪(x : E), θ⟫ - ⟪(x : E), θ⟫ ^ 2 / 2

/-- The one-step density ratio `exp (stepLogLR θ x y)` as an `ℝ≥0∞`-valued density. -/
noncomputable def stepLR (θ : E) (x : 𝒳) (y : ℝ) : ℝ≥0∞ := ENNReal.ofReal (rexp (stepLogLR θ x y))

lemma measurable_uncurry_stepLR (θ : E) : Measurable (Function.uncurry (stepLR (𝒳 := 𝒳) θ)) := by
  have h1 : Measurable fun p : 𝒳 × ℝ ↦ ⟪((p.1 : 𝒳) : E), θ⟫ :=
    (continuous_subtype_val.inner continuous_const).measurable.comp measurable_fst
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((measurable_snd.mul h1).sub ((h1.pow_const 2).div_const 2)))

/-- The reward kernel under `θ` has density `stepLR θ` with respect to the pure-noise kernel. -/
lemma linearGaussianKernel_eq_withDensity (θ : E) :
    linearGaussianKernel 𝒳 θ = (linearGaussianKernel 𝒳 0).withDensity (stepLR θ) := by
  ext x : 1
  rw [Kernel.withDensity_apply _ (measurable_uncurry_stepLR θ)]
  change gaussianReal ⟪(x : E), θ⟫ 1 = (gaussianReal ⟪(x : E), 0⟫ 1).withDensity (stepLR θ x)
  rw [inner_zero_right, gaussianReal_eq_withDensity_exp]
  rfl

/-- The likelihood ratio of the history `h` of `T` rounds under the reward vector `θ` with
respect to pure noise: `exp (∑ t, (y t ⟪x t, θ⟫ - ⟪x t, θ⟫² / 2))`. -/
noncomputable def likelihood (θ : E) {T : ℕ} (h : Fin T → 𝒳 × ℝ) : ℝ :=
  rexp (∑ t, stepLogLR θ (h t).1 (h t).2)

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
lemma likelihood_pos (θ : E) {T : ℕ} (h : Fin T → 𝒳 × ℝ) : 0 < likelihood θ h := exp_pos _

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
lemma envDensity_stepLR (θ : E) {T : ℕ} (h : Fin T → 𝒳 × ℝ) :
    envDensity (stepLR θ) T h = ENNReal.ofReal (likelihood θ h) := by
  simp only [envDensity, stepLR, likelihood, Real.exp_sum]
  rw [ENNReal.ofReal_prod_of_nonneg fun t _ ↦ (exp_pos _).le]

lemma measurable_likelihood (θ : E) (T : ℕ) : Measurable (likelihood (𝒳 := 𝒳) θ (T := T)) := by
  refine Real.measurable_exp.comp (Finset.measurable_sum _ fun t _ ↦ ?_)
  have h1 : Measurable fun h : Fin T → 𝒳 × ℝ ↦ ⟪(((h t).1 : 𝒳) : E), θ⟫ :=
    (continuous_subtype_val.inner continuous_const).measurable.comp (measurable_pi_apply t).fst
  exact ((measurable_pi_apply t).snd.mul h1).sub ((h1.pow_const 2).div_const 2)

/-- Joint measurability of the likelihood ratio in `(θ, h)`. -/
lemma measurable_likelihood_prod [SecondCountableTopology E] (T : ℕ) :
    Measurable fun p : E × (Fin T → 𝒳 × ℝ) ↦ likelihood p.1 p.2 := by
  refine Real.measurable_exp.comp (Finset.measurable_sum _ fun t _ ↦ ?_)
  have h1 : Measurable fun p : E × (Fin T → 𝒳 × ℝ) ↦ ⟪(((p.2 t).1 : 𝒳) : E), p.1⟫ :=
    (measurable_subtype_coe.comp ((measurable_pi_apply t).comp measurable_snd).fst).inner
      measurable_fst
  exact (((measurable_pi_apply t).comp measurable_snd).snd.mul h1).sub
    ((h1.pow_const 2).div_const 2)

section law

variable {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] {P : Measure Ω}
  {P₀ : Measure Ω₀} [IsProbabilityMeasure P] [IsProbabilityMeasure P₀]
  {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → ℝ} {X₀ : ℕ → Ω₀ → 𝒳} {Y₀ : ℕ → Ω₀ → ℝ}
  {alg : Algorithm 𝒳 ℝ} {θ : E}

/-- **Likelihood ratio of a linear Gaussian history** (blueprint `cor:pb_gaussian_likelihood`):
for any algorithm, the law of the history of `T` rounds under the reward vector `θ` is the law
under pure noise with density `likelihood θ`. -/
lemma _root_.Learning.IsAlgEnvSeq.map_finHistory_eq_withDensity_likelihood
    (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P)
    (h₀ : IsAlgEnvSeq X₀ Y₀ alg (linearGaussianEnv 𝒳 0) P₀) (T : ℕ) :
    P.map (finHistory X Y T) =
      (P₀.map (finHistory X₀ Y₀ T)).withDensity fun h ↦ ENNReal.ofReal (likelihood θ h) := by
  have h' : IsAlgEnvSeq X Y alg (stationaryEnv (linearGaussianKernel 𝒳 θ)) P := h
  have h₀' : IsAlgEnvSeq X₀ Y₀ alg (stationaryEnv (linearGaussianKernel 𝒳 0)) P₀ := h₀
  rw [h'.map_finHistory_eq_withDensity_env (measurable_uncurry_stepLR θ)
    (linearGaussianKernel_eq_withDensity θ) h₀' T]
  congr 1
  funext hh
  exact envDensity_stepLR θ hh

end law

end Learning.LinearBandit
