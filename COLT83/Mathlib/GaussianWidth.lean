/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Gaussian width of a set with respect to a measure

For a set `K` in a real inner product space `E` and a measure `μ` on `E` (typically a centered
Gaussian measure), the *Gaussian width* of `K` for `μ` is
`gaussianWidth K μ = ∫ ξ, sup_{x ∈ K} ⟪x, ξ⟫ ∂μ`.

For the standard Gaussian measure this is the usual Gaussian width (or mean width) of `K`.
-/

@[expose] public section

open MeasureTheory

open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {mE : MeasurableSpace E}

/-- Gaussian width of the set `K` with respect to the measure `μ`:
`∫ ξ, sup_{x ∈ K} ⟪x, ξ⟫ ∂μ`. -/
noncomputable def gaussianWidth (K : Set E) (μ : Measure E) : ℝ :=
  ∫ ξ, ⨆ x : K, ⟪(x : E), ξ⟫ ∂μ

end ProbabilityTheory
