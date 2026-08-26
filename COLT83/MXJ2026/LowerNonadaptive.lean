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
# The lower bound for non-adaptive fixed designs (Theorem 3)

Every fixed-design `(ε, δ)`-PAC identification algorithm on a spanning action set `𝒳` with
`δ ≤ 1/10` has budget `T ≥ w(𝒳)² / (70 ε²)`.

Blueprint: `thm:lower_nonadaptive`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Learning Learning.LinearBandit

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 3** (Maiti, Xu, Jamieson 2026): a fixed-design (non-adaptive) identification
algorithm with budget `T ≥ 1` which is `(ε, δ)`-PAC on a spanning compact action set `𝒳`, with
`δ ≤ 1/10`, satisfies `T ≥ w(𝒳)² / (70 ε²)`. -/
theorem le_budget_of_isFixedDesign_of_isPAC (𝒳 : Set (EuclideanSpace ℝ ι)) (h𝒳 : IsCompact 𝒳)
    (hne : 𝒳.Nonempty) (hspan : Submodule.span ℝ 𝒳 = ⊤)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : δ ∈ Set.Ioc 0 (1 / 10)) {T : ℕ} (hT : 1 ≤ T)
    (A : IdentAlg 𝒳 ℝ 𝒳) (hA : A.IsFixedBudget T)
    (hdes : A.IsFixedDesign) (hpac : IsPAC 𝒳 A ε δ) :
    gw 𝒳 ^ 2 / (70 * ε ^ 2) ≤ T := by
  sorry

end COLT83
