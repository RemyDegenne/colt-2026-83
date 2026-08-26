/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.LinearBandit
public import COLT83.MXJ2026.StructuredSets
public import COLT83.MXJ2026.Width

/-!
# `ℓ₂`-norm estimation on the unit ball (Theorem 8)

An *estimation algorithm* on the unit ball is an identification algorithm with actions in the
unit ball, real observations and a real output `r̂`; it is `(ε, δ)`-accurate if for
every reward vector `θ`, `|r̂ - ‖θ‖| ≤ ε` with probability at least `1 - δ`.

Theorem 8: there is an `(ε, δ)`-accurate estimation algorithm with budget
`T ≤ 10⁵ d log(4/δ) / ε²`.

Blueprint: `def:norm_estimator`, `thm:norm_estimation` (stated there for an explicit meta-algorithm,
of which `exists_isAccurateNormEst` is the existence form).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Learning Learning.LinearBandit

universe u

namespace COLT83

variable {ι : Type*} [Fintype ι]

/-- An estimation algorithm on the unit ball (an identification algorithm with actions in the
unit ball, real observations and a real output) is `(ε, δ)`-accurate if for every reward vector `θ`,
run against the linear Gaussian environment with reward vector `θ`, its output `r̂` satisfies
`|r̂ - ‖θ‖| ≤ ε` with probability at least `1 - δ`. -/
def IsAccurateNormEst (A : IdentAlg (unitBall ι) ℝ ℝ) (ε δ : ℝ) : Prop :=
  A.IsPAC.{u} (linearGaussianEnv (unitBall ι)) (fun θ r ↦ |r - ‖θ‖| ≤ ε) δ

/-- **Theorem 8** (Maiti, Xu, Jamieson 2026): for `ε ∈ (0, 1]` and `δ ∈ (0, 1)` there is an
(adaptive) `(ε, δ)`-accurate `ℓ₂`-norm estimation algorithm on the unit ball of `ℝ^d` with budget
`T ≤ 10⁵ d log(4/δ) / ε²`. -/
theorem exists_isAccurateNormEst {ε δ : ℝ} (hε : ε ∈ Set.Ioc 0 1) (hδ : δ ∈ Set.Ioo 0 1) :
    ∃ T : ℕ, (T : ℝ) ≤ 100000 * Fintype.card ι * log (4 / δ) / ε ^ 2 ∧
      ∃ A : IdentAlg (unitBall ι) ℝ ℝ, A.IsFixedBudget T ∧ IsAccurateNormEst A ε δ := by
  sorry

end COLT83
