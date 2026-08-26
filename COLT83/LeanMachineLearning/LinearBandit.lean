/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.IdentAlg
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

/-!
# Linear Gaussian bandits and `(ε, δ)`-PAC identification

A linear Gaussian bandit on an action set `𝒳 ⊆ E` (`E` a real inner product space) with reward
vector `θ : E`: playing `x ∈ 𝒳` gives the observation `⟪x, θ⟫ + η` with `η ~ N(0, 1)`, independent
of the past. This is the stationary environment `linearGaussianEnv 𝒳 θ`.

An identification algorithm for this problem is an `IdentAlg 𝒳 ℝ 𝒳` (sampling rule, stopping
rule, output rule) with actions in `𝒳`, real observations and outputs (recommendations) in `𝒳`.
It is `(ε, δ)`-PAC if for every `θ` its recommendation has simple regret at most `ε` with
probability at least `1 - δ`.

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

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
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
noncomputable def linearGaussianEnv (𝒳 : Set E) (θ : E) : Environment 𝒳 ℝ :=
  @stationaryEnv _ _ _ _ (linearGaussianKernel 𝒳 θ)
    ⟨fun _ ↦ inferInstanceAs (IsProbabilityMeasure (gaussianReal _ 1))⟩

/-- Simple regret of the arm `x` for the reward vector `θ` on the action set `𝒳`:
`sup_{y ∈ 𝒳} ⟪y, θ⟫ - ⟪x, θ⟫`. -/
noncomputable def simpleRegret (𝒳 : Set E) (θ x : E) : ℝ :=
  (⨆ y : 𝒳, ⟪(y : E), θ⟫) - ⟪x, θ⟫

/-- An identification algorithm (with actions in `𝒳`, real observations and recommendations in
`𝒳`) is `(ε, δ)`-PAC on `𝒳` if for every reward vector `θ`, run against the linear Gaussian
environment `linearGaussianEnv 𝒳 θ`, its recommendation has simple regret at most `ε` with
probability at least `1 - δ`, for every run on every probability space `Ω` in the universe of `E`
(the universe in which runs of `A` can be constructed, see `IdentAlg.exists_isRun`). -/
def IsPAC (𝒳 : Set E) (A : IdentAlg 𝒳 ℝ 𝒳) (ε δ : ℝ) : Prop :=
  A.IsPAC.{u} (linearGaussianEnv 𝒳) (fun θ x ↦ simpleRegret 𝒳 θ x ≤ ε) δ

end Learning.LinearBandit
