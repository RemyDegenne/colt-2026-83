/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.GaussianNoise
public import COLT83.LeanMachineLearning.IdentAlg
public import COLT83.Mathlib.Probability.IidOfCondDistrib
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# The noise of a linear Gaussian run is i.i.d.; fixed-design runs

For any algorithm run in the linear Gaussian environment with reward vector `θ`, the noise
`noise θ X Y t = Y t - ⟪X t, θ⟫` has, conditionally on the past noises, the constant law `N(0,1)`
(`IsAlgEnvSeq.hasCondDistrib_noise_finVec`), hence the noise vector `(noise 0, …, noise (n-1))`
has the product law `N(0,1)^n` (`IsAlgEnvSeq.hasLaw_noise_finVec`), the noises are independent
(`IsAlgEnvSeq.iIndepFun_noise`) and, as a vector of `EuclideanSpace ℝ (Fin n)`, the noise is
standard Gaussian (`IsAlgEnvSeq.hasLaw_toLp_noise_finVec`).

Under a fixed design `fixedDesignAlg x`, the actions are `x t` almost surely and the observation
vector `(Y 0, …, Y (n-1))` is `(⟪x t, θ⟫)_t` plus the noise vector
(`IsAlgEnvSeq.hasLaw_feedback_finVec_of_fixedDesign`, blueprint `lem:fixed_design_law`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset Learning
open scoped RealInnerProductSpace

namespace Learning.LinearBandit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {𝒳 : Set E} {θ : E} {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝒳 ℝ}

section noise

variable (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P)
include h

/-- Conditionally on the noises of the rounds `0, …, n`, the noise of the round `n + 1` has the
law `N(0, 1)`. -/
lemma _root_.Learning.IsAlgEnvSeq.hasCondDistrib_noise_finVec (n : ℕ) :
    HasCondDistrib (noise θ X Y (n + 1)) (fun ω (i : Fin (n + 1)) ↦ noise θ X Y i ω)
      (Kernel.const _ (gaussianReal 0 1)) P := by
  have h1 : ∀ i : Fin (n + 1), Measurable fun p : (Iic n → 𝒳 × ℝ) × 𝒳 ↦
      p.1 ⟨i, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 i.2)⟩ :=
    fun i ↦ (measurable_pi_apply _).comp measurable_fst
  have hf : Measurable fun p : (Iic n → 𝒳 × ℝ) × 𝒳 ↦ fun i : Fin (n + 1) ↦
      (p.1 ⟨i, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 i.2)⟩).2 -
        ⟪((p.1 ⟨i, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 i.2)⟩).1 : E), θ⟫ :=
    measurable_pi_lambda _ fun i ↦ (h1 i).snd.sub
      ((continuous_id.inner continuous_const).measurable.comp
        (measurable_subtype_coe.comp (h1 i).fst))
  exact (h.hasCondDistrib_noise n).const_comp_right hf

/-- **The noise of a linear Gaussian run is i.i.d. `N(0, 1)`**, for any algorithm: the noise
vector of the rounds `0, …, n - 1` has the product law. -/
theorem _root_.Learning.IsAlgEnvSeq.hasLaw_noise_finVec (n : ℕ) :
    HasLaw (fun ω (i : Fin n) ↦ noise θ X Y i ω) (Measure.pi fun _ ↦ gaussianReal 0 1) P :=
  hasLaw_pi_of_hasCondDistrib_const (h.hasLaw_noise 0) h.hasCondDistrib_noise_finVec n

/-- The noises of the rounds `0, …, n - 1` are independent. -/
theorem _root_.Learning.IsAlgEnvSeq.iIndepFun_noise (n : ℕ) :
    iIndepFun (fun i : Fin n ↦ noise θ X Y i) P :=
  iIndepFun_of_hasCondDistrib_const (h.hasLaw_noise 0) h.hasCondDistrib_noise_finVec n

/-- The noise vector of the rounds `0, …, n - 1`, as a vector of `EuclideanSpace ℝ (Fin n)`, is
standard Gaussian. -/
theorem _root_.Learning.IsAlgEnvSeq.hasLaw_toLp_noise_finVec (n : ℕ) :
    HasLaw (fun ω ↦ WithLp.toLp 2 (fun i : Fin n ↦ noise θ X Y i ω))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) P := by
  rw [← map_pi_eq_stdGaussian]
  exact (⟨(WithLp.measurable_toLp 2 _).aemeasurable, rfl⟩ :
    HasLaw (WithLp.toLp 2) _ _).comp (h.hasLaw_noise_finVec n)

end noise

section fixedDesign

variable [MeasurableEq 𝒳] {x : ℕ → 𝒳}
  (h : IsAlgEnvSeq X Y (fixedDesignAlg x) (linearGaussianEnv 𝒳 θ) P)
include h

/-- Under the fixed design `x`, the actions are `x t` almost surely. -/
lemma _root_.Learning.IsAlgEnvSeq.ae_action_eq_of_fixedDesign :
    ∀ᵐ ω ∂P, ∀ t, X t ω = x t := by
  have h' : IsAlgEnvSeq X Y (detAlgorithm (fun n _ ↦ x (n + 1)) (fun _ ↦ measurable_const) (x 0))
      (linearGaussianEnv 𝒳 θ) P := h
  filter_upwards [h'.action_detAlgorithm_ae_all_eq] with ω hω t
  cases t with
  | zero => exact hω.1
  | succ t => exact hω.2 t

/-- Under the fixed design `x`, the observations are `Y t = ⟪x t, θ⟫ + noise t` almost surely. -/
lemma _root_.Learning.IsAlgEnvSeq.ae_feedback_eq_of_fixedDesign :
    ∀ᵐ ω ∂P, ∀ t, Y t ω = ⟪(x t : E), θ⟫ + noise θ X Y t ω := by
  filter_upwards [h.ae_action_eq_of_fixedDesign] with ω hω t
  simp [noise, hω t]

/-- **Law of the observations under a fixed design** (blueprint `lem:fixed_design_law`): the
observation vector of the rounds `0, …, n - 1` is `(⟪x t, θ⟫)_t` plus an `N(0, 1)^n` noise
vector. -/
theorem _root_.Learning.IsAlgEnvSeq.hasLaw_feedback_finVec_of_fixedDesign (n : ℕ) :
    HasLaw (fun ω (i : Fin n) ↦ Y i ω)
      ((Measure.pi fun _ : Fin n ↦ gaussianReal 0 1).map
        (fun η (i : Fin n) ↦ ⟪(x i : E), θ⟫ + η i)) P := by
  have hm : Measurable fun η : Fin n → ℝ ↦ fun i : Fin n ↦ ⟪(x i : E), θ⟫ + η i :=
    measurable_pi_lambda _ fun i ↦ measurable_const.add (measurable_pi_apply i)
  refine ((⟨hm.aemeasurable, rfl⟩ : HasLaw _ _ _).comp (h.hasLaw_noise_finVec n)).congr ?_
  filter_upwards [h.ae_feedback_eq_of_fixedDesign] with ω hω
  funext i
  exact hω i

end fixedDesign

end Learning.LinearBandit
