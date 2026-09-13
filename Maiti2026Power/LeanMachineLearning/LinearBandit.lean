/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.LeanMachineLearning.Run
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Linear Gaussian bandits and `(ε, δ)`-PAC identification

A linear Gaussian bandit on an action set `𝒳 ⊆ E` (`E` a real inner product space) with reward
vector `θ : E`: playing `x ∈ 𝒳` gives the observation `⟪x, θ⟫ + η` with `η ~ N(0, 1)`, independent
of the past. This is the stationary environment `linearGaussianEnv 𝒳 θ`.

An identification algorithm for this problem is an `IdentAlg Unit 𝒳 ℝ 𝒳` (sampling rule,
stopping rule, output rule; LML `Learning.IdentAlg`) with no observations, actions in `𝒳`, real
feedbacks and outputs (recommendations) in `𝒳`. It is `(ε, δ)`-PAC if for every `θ` its
recommendation has simple regret more than `ε` with probability at most `δ`
(`LinearBandit.IsPAC`, a statement about the law of the output, LML `IdentAlg.outputMeasure`);
equivalently, for every run of the algorithm on a probability space in the universe of the
canonical run, the recommendation has simple regret at most `ε` with probability at least
`1 - δ` (`IsPAC.le_measureReal_of_isRun`, `isPAC_of_forall_isRun`).

## Main definitions

* `LinearBandit.linearGaussianKernel 𝒳 θ`, `LinearBandit.linearGaussianEnv 𝒳 θ`
* `LinearBandit.simpleRegret 𝒳 θ x = sup_{y ∈ 𝒳} ⟪y, θ⟫ - ⟪x, θ⟫`
* `LinearBandit.IsPAC 𝒳 A ε δ`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace NNReal

universe u

namespace Learning.LinearBandit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E]

/-- Reward kernel of the linear Gaussian bandit on `𝒳` with reward vector `θ`: playing `x` gives an
observation with law `N(⟪x, θ⟫, 1)`. -/
noncomputable def linearGaussianKernel (𝒳 : Set E) (θ : E) : Kernel 𝒳 ℝ where
  toFun x := gaussianReal ⟪(x : E), θ⟫ 1
  measurable' := by
    change Measurable (gaussianReal.uncurry ∘ fun x : 𝒳 ↦ (⟪(x : E), θ⟫, (1 : ℝ≥0)))
    exact measurable_gaussianReal.comp (by fun_prop)

instance (𝒳 : Set E) (θ : E) : IsMarkovKernel (linearGaussianKernel 𝒳 θ) :=
  ⟨fun _ ↦ inferInstanceAs (IsProbabilityMeasure (gaussianReal _ 1))⟩

/-- The linear Gaussian environment on the action set `𝒳` with reward vector `θ`: the stationary
environment with reward kernel `linearGaussianKernel 𝒳 θ`.

The Markov-kernel argument of `stationaryEnv` is given inline rather than through the instance
above: the nested proof of an exposed `def` becomes a public auxiliary constant, whereas the proof
inside an instance (a theorem) becomes a module-private one, which the standalone comparator
challenges (`comparator/`) could not reproduce. -/
noncomputable def linearGaussianEnv (𝒳 : Set E) (θ : E) : Environment Unit 𝒳 ℝ :=
  @stationaryEnv _ _ _ _ (linearGaussianKernel 𝒳 θ)
    ⟨fun _ ↦ inferInstanceAs (IsProbabilityMeasure (gaussianReal _ 1))⟩

/-- Simple regret of the arm `x` for the reward vector `θ` on the action set `𝒳`:
`sup_{y ∈ 𝒳} ⟪y, θ⟫ - ⟪x, θ⟫`. -/
noncomputable def simpleRegret (𝒳 : Set E) (θ x : E) : ℝ :=
  (⨆ y : 𝒳, ⟪(y : E), θ⟫) - ⟪x, θ⟫

/-- An identification algorithm (with actions in `𝒳`, real feedbacks and recommendations in
`𝒳`) is `(ε, δ)`-PAC on `𝒳` if for every reward vector `θ`, run against the linear Gaussian
environment `linearGaussianEnv 𝒳 θ`, its recommendation has simple regret more than `ε` with
probability at most `δ`. -/
def IsPAC (𝒳 : Set E) (A : IdentAlg Unit 𝒳 ℝ 𝒳) (ε δ : ℝ) : Prop :=
  A.IsPAC (linearGaussianEnv 𝒳) (fun θ x ↦ ε < simpleRegret 𝒳 θ x) δ

lemma measurable_simpleRegret (𝒳 : Set E) (θ : E) :
    Measurable fun x : 𝒳 ↦ simpleRegret 𝒳 θ x :=
  (continuous_const.sub (continuous_subtype_val.inner continuous_const)).measurable

section run

variable {𝒳 : Set E} {A : IdentAlg Unit 𝒳 ℝ 𝒳} {ε δ : ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {O : ℕ → Ω → Unit} {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → ℝ}
  {out : Ω → 𝒳}

/-- For an `(ε, δ)`-PAC algorithm, the recommendation of any run in the linear Gaussian
environment with reward vector `θ` has simple regret at most `ε` with probability at least
`1 - δ`. -/
lemma IsPAC.le_measureReal_of_isRun (hpac : IsPAC 𝒳 A ε δ) {θ : E}
    (h : A.IsRun (linearGaussianEnv 𝒳 θ) O X Y out P) :
    1 - δ ≤ P.real {ω | simpleRegret 𝒳 θ (out ω) ≤ ε} := by
  have hmeas : MeasurableSet {x : 𝒳 | simpleRegret 𝒳 θ x ≤ ε} :=
    measurableSet_le (measurable_simpleRegret 𝒳 θ) measurable_const
  have h1 := hpac.measureReal_bad_of_isRun
    (measurableSet_lt measurable_const (measurable_simpleRegret 𝒳 θ)) h
  rw [h.hasLaw_output.measureReal_eq hmeas]
  rw [h.hasLaw_output.measureReal_eq (measurableSet_lt measurable_const
    (measurable_simpleRegret 𝒳 θ)), show {x : 𝒳 | ε < simpleRegret 𝒳 θ x} =
      {x : 𝒳 | simpleRegret 𝒳 θ x ≤ ε}ᶜ by ext; simp, measureReal_compl hmeas, probReal_univ]
    at h1
  linarith

/-- **PAC from a bound on every run**: `A` is `(ε, δ)`-PAC on `𝒳` as soon as, for every reward
vector `θ` and every run of `A` in the linear Gaussian environment with reward vector `θ` on a
probability space in the universe of `E` (the universe of the canonical run
`IdentAlg.runMeasure`), the recommendation has simple regret at most `ε` with probability at
least `1 - δ`. -/
lemma isPAC_of_forall_isRun {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {𝒳 : Set E} {A : IdentAlg Unit 𝒳 ℝ 𝒳} {ε δ : ℝ}
    (h : ∀ θ : E, ∀ {Ω : Type u} {_mΩ : MeasurableSpace Ω} (P : Measure Ω)
      [IsProbabilityMeasure P] (O : ℕ → Ω → Unit) (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → ℝ) (out : Ω → 𝒳),
      A.IsRun (linearGaussianEnv 𝒳 θ) O X Y out P →
        1 - δ ≤ P.real {ω | simpleRegret 𝒳 θ (out ω) ≤ ε}) :
    IsPAC 𝒳 A ε δ := by
  refine IdentAlg.IsPAC.of_forall_isRun
    (fun θ ↦ measurableSet_lt measurable_const (measurable_simpleRegret 𝒳 θ))
    fun θ Ω _ P _ O X Y out hrun ↦ ?_
  have hmeas : MeasurableSet {x : 𝒳 | simpleRegret 𝒳 θ x ≤ ε} :=
    measurableSet_le (measurable_simpleRegret 𝒳 θ) measurable_const
  have h1 := h θ P O X Y out hrun
  rw [hrun.hasLaw_output.measureReal_eq hmeas] at h1
  rw [hrun.hasLaw_output.measureReal_eq (measurableSet_lt measurable_const
    (measurable_simpleRegret 𝒳 θ)), show {x : 𝒳 | ε < simpleRegret 𝒳 θ x} =
      {x : 𝒳 | simpleRegret 𝒳 θ x ≤ ε}ᶜ by ext; simp, measureReal_compl hmeas, probReal_univ]
  linarith

end run

end Learning.LinearBandit
