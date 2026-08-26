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
# Polynomial separation between adaptive and non-adaptive algorithms (Theorem 7)

On the block-ball set `𝒳 ⊆ ℝ^{kd}` (the union of the unit balls of `k` coordinate blocks of
dimension `d`):

* every fixed-design `(ε, δ)`-PAC algorithm with `δ ≤ 1/10` has budget `T ≥ k d² / (210 ε²)`
  (`blockBallSet_le_budget_of_isFixedDesign_of_isPAC`), and every `(ε, δ)`-PAC algorithm with
  `δ < 1/16` has budget `T ≥ kd log(1/δ) / (20000 ε²)` (`blockBallSet_le_budget_of_isPAC`,
  from Theorem 2);
* there is an adaptive `(ε, δ)`-PAC algorithm with budget
  `T ≤ 2·10⁶ (kd log(8k/δ) + d²) / ε²` (`exists_isPAC_blockBallSet`).

For `d ≤ k` the adaptive budget is `O(kd (log(1/δ) + log k) / ε²)`, polynomially smaller than the
non-adaptive `Ω(kd log(1/δ) / ε² + kd² / ε²)`.

Blueprint: `thm:separation_lower_nonadaptive`, `thm:separation` (stated there for an explicit block
algorithm, of which `exists_isPAC_blockBallSet` is the existence form).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Learning Learning.LinearBandit

namespace COLT83

/-- **Theorem 7, non-adaptive lower bound**: a fixed-design (non-adaptive) identification
algorithm which is `(ε, δ)`-PAC on the block-ball set of `ℝ^{kd}`, with `ε ∈ (0, 1]` and
`δ ≤ 1/10`, has budget `T ≥ k d² / (210 ε²)`. -/
theorem blockBallSet_le_budget_of_isFixedDesign_of_isPAC (k d : ℕ) {ε δ : ℝ}
    (hε : ε ∈ Set.Ioc 0 1) (hδ : δ ∈ Set.Ioc 0 (1 / 10)) {T : ℕ}
    (A : IdentAlg (blockBallSet k d) ℝ (blockBallSet k d)) (hA : A.IsFixedBudget T)
    (hdes : A.IsFixedDesign)
    (hpac : IsPAC (blockBallSet k d) A ε δ) :
    k * (d : ℝ) ^ 2 / (210 * ε ^ 2) ≤ T := by
  sorry

/-- **Theorem 7, adaptive lower bound** (from Theorem 2): an identification algorithm which is
`(ε, δ)`-PAC on the block-ball set of `ℝ^{kd}`, `kd ≥ 2`, with `δ < 1/16`, has budget
`T ≥ kd log(1/δ) / (20000 ε²)`. -/
theorem blockBallSet_le_budget_of_isPAC (k d : ℕ) (hkd : 2 ≤ k * d) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : δ ∈ Set.Ioo 0 (1 / 16)) {T : ℕ}
    (A : IdentAlg (blockBallSet k d) ℝ (blockBallSet k d)) (hA : A.IsFixedBudget T)
    (hpac : IsPAC (blockBallSet k d) A ε δ) :
    k * d * log (1 / δ) / (20000 * ε ^ 2) ≤ T := by
  sorry

/-- **Theorem 7, adaptive upper bound**: for `k ≥ 1`, `ε ∈ (0, 1]` and `δ ∈ (0, 1)`, there is an
(adaptive) `(ε, δ)`-PAC identification algorithm on the block-ball set of `ℝ^{kd}` with budget
`T ≤ 2·10⁶ (kd log(8k/δ) + d²) / ε²`. -/
theorem exists_isPAC_blockBallSet (k d : ℕ) (hk : 1 ≤ k) {ε δ : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hδ : δ ∈ Set.Ioo 0 1) :
    ∃ T : ℕ, (T : ℝ) ≤ 2000000 * (k * d * log (8 * k / δ) + (d : ℝ) ^ 2) / ε ^ 2 ∧
      ∃ A : IdentAlg (blockBallSet k d) ℝ (blockBallSet k d), A.IsFixedBudget T ∧
        IsPAC (blockBallSet k d) A ε δ := by
  sorry

end COLT83
