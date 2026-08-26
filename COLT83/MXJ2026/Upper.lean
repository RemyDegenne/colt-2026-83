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
# The fixed-design upper bound (Theorem 1)

For a spanning action set `𝒳`, there is a non-adaptive fixed-design `(ε, δ)`-PAC identification
algorithm with budget `T ≤ 600 (w(𝒳)² + d log(2/δ)) / ε² + 1`, where `w(𝒳) = gw 𝒳` is the Gaussian
width term of `𝒳`.

Blueprint: `thm:upper` is stated for an explicit algorithm (a rounded mixed `G`-optimal /
width-optimal design, least squares, approximate argmax); `exists_isFixedDesign_isPAC` is the
existence statement of the paper's Theorem 1, which follows from it.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Learning Learning.LinearBandit

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 1** (Maiti, Xu, Jamieson 2026): for a spanning compact action set `𝒳 ⊆ ℝ^d`,
`ε ∈ (0, 1]` and `δ ∈ (0, 1)`, there is a fixed-design (non-adaptive) identification algorithm
which is `(ε, δ)`-PAC on `𝒳` with budget `T ≤ 600 (w(𝒳)² + d log(2/δ)) / ε² + 1`. -/
theorem exists_isFixedDesign_isPAC (𝒳 : Set (EuclideanSpace ℝ ι)) (h𝒳 : IsCompact 𝒳)
    (hne : 𝒳.Nonempty) (hspan : Submodule.span ℝ 𝒳 = ⊤)
    {ε δ : ℝ} (hε : ε ∈ Set.Ioc 0 1) (hδ : δ ∈ Set.Ioo 0 1) :
    ∃ T : ℕ, (T : ℝ) ≤ 600 * (gw 𝒳 ^ 2 + Fintype.card ι * log (2 / δ)) / ε ^ 2 + 1 ∧
      ∃ A : IdentAlg 𝒳 ℝ 𝒳, A.IsFixedBudget T ∧ A.IsFixedDesign ∧ IsPAC 𝒳 A ε δ := by
  sorry

end COLT83
