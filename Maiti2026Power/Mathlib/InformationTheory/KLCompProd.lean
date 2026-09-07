/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.ChainRule
public import LeanMachineLearning.ForMathlib.Probability.Kernel.Composition.Lemmas

/-!
# The Kullback–Leibler divergence of a policy/reward decomposition

LML's `klDiv_compProd_right_eq_lintegral` gives the integrated form of the conditional divergence,
`klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) = ∫⁻ a, klDiv (κ a) (η a) ∂μ`, when the target space of the kernels is
countably generated (or the source is countable). We deduce from it the one-step divergence of a
policy/reward decomposition:

* `klDiv_compProd_compProd_prodMkLeft`:
  `klDiv (μ ⊗ₘ (π ⊗ₖ κ̃)) (μ ⊗ₘ (π ⊗ₖ η̃)) = ∫⁻ b, klDiv (κ b) (η b) ∂(π ∘ₘ μ)` where
  `κ̃ = prodMkLeft α κ` ignores the first coordinate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  [MeasurableSpace.CountableOrCountablyGenerated β γ]

/-- The divergence of one step of a policy/reward decomposition: the policy `π` is shared and the
reward kernels `κ`, `η` (which ignore the history) differ, so the divergence is the expected
divergence of the reward kernels at the played action, whose law is `π ∘ₘ μ`. -/
lemma klDiv_compProd_compProd_prodMkLeft (μ : Measure α) [IsFiniteMeasure μ] (π : Kernel α β)
    [IsMarkovKernel π] (κ η : Kernel β γ) [IsFiniteKernel κ] [IsFiniteKernel η]
    [MeasurableSpace.CountableOrCountablyGenerated α (β × γ)] :
    klDiv (μ ⊗ₘ (π ⊗ₖ Kernel.prodMkLeft α κ)) (μ ⊗ₘ (π ⊗ₖ Kernel.prodMkLeft α η)) =
      ∫⁻ b, klDiv (κ b) (η b) ∂(π ∘ₘ μ) := by
  rw [klDiv_compProd_right_eq_lintegral, Measure.lintegral_bind π.aemeasurable
    (measurable_klDiv_kernel κ η).aemeasurable]
  refine lintegral_congr fun a ↦ ?_
  rw [Kernel.compProd_prodMkLeft_apply, Kernel.compProd_prodMkLeft_apply,
    klDiv_compProd_right_eq_lintegral]

end InformationTheory
