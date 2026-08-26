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
# The lower bound for adaptive algorithms (Theorem 2)

Every `(ε, δ)`-PAC identification algorithm (adaptive or not) on a spanning action set
`𝒳 ⊆ ℝ^d`, `d ≥ 2`, with `δ < 1/16`, has budget `T ≥ d log(1/δ) / (20000 ε²)`.

Blueprint: `thm:lower_adaptive` (with the constant `c_ad = 1/(11556 + 5760√2) ≥ 1/20000`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Learning Learning.LinearBandit

namespace COLT83

variable {ι : Type*} [Fintype ι]

/-- **Theorem 2** (Maiti, Xu, Jamieson 2026): an identification algorithm (adaptive or not) with
budget `T` which is `(ε, δ)`-PAC on a spanning compact action set `𝒳 ⊆ ℝ^d`, `d ≥ 2`, with
`δ < 1/16`, satisfies `T ≥ d log(1/δ) / (20000 ε²)`. -/
theorem le_budget_of_isPAC (𝒳 : Set (EuclideanSpace ℝ ι)) (h𝒳 : IsCompact 𝒳)
    (hne : 𝒳.Nonempty) (hspan : Submodule.span ℝ 𝒳 = ⊤) (hd : 2 ≤ Fintype.card ι)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : δ ∈ Set.Ioo 0 (1 / 16)) {T : ℕ}
    (A : IdentAlg 𝒳 ℝ 𝒳) (hA : A.IsFixedBudget T) (hpac : IsPAC 𝒳 A ε δ) :
    Fintype.card ι * log (1 / δ) / (20000 * ε ^ 2) ≤ T := by
  sorry

end COLT83
