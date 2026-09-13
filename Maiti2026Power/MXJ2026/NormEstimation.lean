/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.LeanMachineLearning.LinearBandit
public import Maiti2026Power.MXJ2026.StructuredSets
public import Maiti2026Power.MXJ2026.Width
public import Maiti2026Power.MXJ2026.NormEstProof
public import Maiti2026Power.MXJ2026.NormEstBudget
public import Maiti2026Power.Mathlib.MeasureTheory.Measure.Real

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

namespace Maiti2026Power

variable {ι : Type*} [Fintype ι]

/-- An estimation algorithm on the unit ball (an identification algorithm with actions in the
unit ball, real observations and a real output) is `(ε, δ)`-accurate if for every reward vector `θ`,
run against the linear Gaussian environment with reward vector `θ`, its output `r̂` satisfies
`ε < |r̂ - ‖θ‖|` with probability at most `δ`. -/
def IsAccurateNormEst (A : IdentAlg Unit (unitBall ι) ℝ ℝ) (ε δ : ℝ) : Prop :=
  A.IsPAC (linearGaussianEnv (unitBall ι)) (fun θ r ↦ ε < |r - ‖θ‖|) δ

/-- **Theorem 8** (Maiti, Xu, Jamieson 2026): for `ε ∈ (0, 1]` and `δ ∈ (0, 1)` there is an
(adaptive) `(ε, δ)`-accurate `ℓ₂`-norm estimation algorithm on the unit ball of `ℝ^d` with budget
`T ≤ 10⁵ d log(4/δ) / ε²`. -/
theorem exists_isAccurateNormEst {ε δ : ℝ} (hε : ε ∈ Set.Ioc 0 1) (hδ : δ ∈ Set.Ioo 0 1) :
    ∃ T : ℕ, (T : ℝ) ≤ 100000 * Fintype.card ι * log (4 / δ) / ε ^ 2 ∧
      ∃ A : IdentAlg Unit (unitBall ι) ℝ ℝ, A.IsFixedBudget T ∧ IsAccurateNormEst A ε δ := by
  classical
  let P : NormEstParam := ⟨ε, δ, hε, hδ⟩
  have habs : ∀ θ : EuclideanSpace ℝ ι, Measurable fun r : ℝ ↦ |r - ‖θ‖| := fun θ ↦
    continuous_abs.measurable.comp (measurable_id.sub_const _)
  have hbad : ∀ θ : EuclideanSpace ℝ ι, MeasurableSet {r : ℝ | ε < |r - ‖θ‖|} := fun θ ↦
    measurableSet_lt measurable_const (habs θ)
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- degenerate case `d = 0`: every reward vector is `0`, the constant output `ε` is accurate
    refine ⟨0, by simp, IdentAlg.fixedBudget (P.alg ι).toAlgorithm 0
      (Kernel.deterministic (fun _ ↦ ε) measurable_const),
      IdentAlg.isFixedBudget_fixedBudget _ _ _, ?_⟩
    refine SeededAlg.linearBandit_isPAC_fixedBudget_deterministic (P.alg ι) measurable_const hbad
      fun θ ↦ ?_
    have hθ : θ = 0 := by
      ext i
      exact isEmptyElim i
    have hempty : {ω : ℕ → (ι → Bool) × ℝ | ε < |ε - ‖θ‖|} = ∅ :=
      Set.eq_empty_of_forall_notMem fun ω hω ↦ absurd hω (by simp [hθ, abs_of_pos hε.1])
    rw [hempty, measureReal_empty]
    exact hδ.1.le
  · have hd : 0 < Fintype.card ι := Fintype.card_pos
    refine ⟨P.T ι, P.T_le hd, IdentAlg.fixedBudget (P.alg ι).toAlgorithm (P.T ι)
      (Kernel.deterministic (P.output ι) P.measurable_output),
      IdentAlg.isFixedBudget_fixedBudget _ _ _, ?_⟩
    exact SeededAlg.linearBandit_isPAC_fixedBudget_deterministic (P.alg ι) P.measurable_output
      hbad fun θ ↦ measureReal_lt_le_of_one_sub_le_measureReal_le
        ((habs θ).comp (P.measurable_output.comp
          (SeededAlg.measurable_seedFinHist (by fun_prop) _)))
        (P.one_sub_le_seedMeasure_real_output hd θ)

end Maiti2026Power
