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
# Structured sets on which adaptivity gives at most logarithmic gains (Theorem 6, Table 1)

* `exists_isPAC_of_finite` (**Theorem 6**): on every finite spanning action set `𝒳 ⊆ ℝ^d` there
  is an adaptive `(ε, δ)`-PAC algorithm with budget `O(d log((|𝒳|/d)₊ / δ) / ε²)`.
* Adaptive lower bounds of Table 1, for every (possibly adaptive) `(ε, δ)`-PAC identification
  algorithm with `δ` below an absolute constant:
  `T > (∑ⱼ √dⱼ)² / (20000 ε²)` on the multi-task set, `T > d² / (100 ε²)` on `{-1, 1}^d`,
  `T > d² / (400 ε²)` on `{0, 1}^d`, `T > m (d - m + 1) / (2500 ε²)` on the `m`-sets, and
  `T ≥ d² / (1000 ε²)` on the unit ball.

Blueprint: `thm:log_gains` (stated there for an explicit region-based algorithm built on Median
Elimination, of which `exists_isPAC_of_finite` is the existence form, with
`C_reg = 1281 + 6 C_ME = 97281`), `thm:lower_multitask`, `thm:lower_hypercube_pm`,
`thm:lower_hypercube_01`, `thm:lower_msets`, `cor:lower_ball_adaptive`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Learning Learning.LinearBandit

namespace COLT83

variable {ι : Type*} [Fintype ι]

/-- **Theorem 6** (Maiti, Xu, Jamieson 2026): for every finite spanning action set `𝒳 ⊆ ℝ^d`,
`ε ∈ (0, 1]` and `δ ∈ (0, 1)`, there is an (adaptive) `(ε, δ)`-PAC identification algorithm on
`𝒳` with budget `T ≤ C d (log((|𝒳|/d)₊) + log(4/δ)) / ε²`, `C = 97281`, where
`(u)₊ = max 1 u`. -/
theorem exists_isPAC_of_finite (𝒳 : Set (EuclideanSpace ℝ ι)) (hfin : 𝒳.Finite)
    (hne : 𝒳.Nonempty) (hspan : Submodule.span ℝ 𝒳 = ⊤)
    {ε δ : ℝ} (hε : ε ∈ Set.Ioc 0 1) (hδ : δ ∈ Set.Ioo 0 1) :
    ∃ T : ℕ, (T : ℝ) ≤ 97281 * Fintype.card ι *
        (log (max 1 ((𝒳.ncard : ℝ) / Fintype.card ι)) + log (4 / δ)) / ε ^ 2 ∧
      ∃ A : IdentAlg 𝒳 ℝ 𝒳, A.IsFixedBudget T ∧ IsPAC 𝒳 A ε δ := by
  sorry

/-- **Table 1, multi-task bandits**: an `(ε, δ)`-PAC identification algorithm with budget `T ≥ 1`
on the multi-task set with block sizes `dⱼ ≥ 2`, with `δ < 2/5`, satisfies
`T > (∑ⱼ √dⱼ)² / (20000 ε²)`. -/
theorem multitaskSet_lt_budget_of_isPAC {m : ℕ} (d : Fin m → ℕ) (hd : ∀ j, 2 ≤ d j)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : δ < 2 / 5) {T : ℕ} (hT : 1 ≤ T)
    (A : IdentAlg (multitaskSet d) ℝ (multitaskSet d)) (hA : A.IsFixedBudget T)
    (hpac : IsPAC (multitaskSet d) A ε δ) :
    (∑ j, √(d j)) ^ 2 / (20000 * ε ^ 2) < T := by
  sorry

/-- **Table 1, hypercube `{-1, 1}^d`**: an `(ε, δ)`-PAC identification algorithm with budget
`T ≥ 1` on `{-1, 1}^d`, with `δ < 1/6`, satisfies `T > d² / (100 ε²)`. -/
theorem hypercubePM_lt_budget_of_isPAC {ε δ : ℝ} (hε : 0 < ε) (hδ : δ < 1 / 6) {T : ℕ}
    (hT : 1 ≤ T) (A : IdentAlg (hypercubePM ι) ℝ (hypercubePM ι)) (hA : A.IsFixedBudget T)
    (hpac : IsPAC (hypercubePM ι) A ε δ) :
    (Fintype.card ι : ℝ) ^ 2 / (100 * ε ^ 2) < T := by
  sorry

/-- **Table 1, hypercube `{0, 1}^d`**: an `(ε, δ)`-PAC identification algorithm with budget
`T ≥ 1` on `{0, 1}^d`, with `δ < 1/6`, satisfies `T > d² / (400 ε²)`. -/
theorem hypercube01_lt_budget_of_isPAC {ε δ : ℝ} (hε : 0 < ε) (hδ : δ < 1 / 6) {T : ℕ}
    (hT : 1 ≤ T) (A : IdentAlg (hypercube01 ι) ℝ (hypercube01 ι)) (hA : A.IsFixedBudget T)
    (hpac : IsPAC (hypercube01 ι) A ε δ) :
    (Fintype.card ι : ℝ) ^ 2 / (400 * ε ^ 2) < T := by
  sorry

/-- **Table 1, `m`-sets**: for `1 ≤ m` with `n := d - m + 1 ≥ 20 m`, an `(ε, δ)`-PAC
identification algorithm with budget `T ≥ 1` on the `m`-sets of `ℝ^d`, with `δ < 2/9`, satisfies
`T > m n / (2500 ε²)`. -/
theorem mSet_lt_budget_of_isPAC (m : ℕ) (hm : 1 ≤ m) (hmd : 20 * m ≤ Fintype.card ι - m + 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : δ < 2 / 9) {T : ℕ} (hT : 1 ≤ T)
    (A : IdentAlg (mSet ι m) ℝ (mSet ι m)) (hA : A.IsFixedBudget T)
    (hpac : IsPAC (mSet ι m) A ε δ) :
    m * ((Fintype.card ι : ℝ) - m + 1) / (2500 * ε ^ 2) < T := by
  sorry

/-- **Table 1, unit ball**: an `(ε, δ)`-PAC identification algorithm with budget `T` on the unit
ball of `ℝ^d`, `d ≥ 2`, with `δ ≤ 1/500`, satisfies `T ≥ d² / (1000 ε²)`. -/
theorem unitBall_le_budget_of_isPAC (hd : 2 ≤ Fintype.card ι) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : δ ≤ 1 / 500) {T : ℕ} (A : IdentAlg (unitBall ι) ℝ (unitBall ι)) (hA : A.IsFixedBudget T)
    (hpac : IsPAC (unitBall ι) A ε δ) :
    (Fintype.card ι : ℝ) ^ 2 / (1000 * ε ^ 2) ≤ T := by
  sorry

end COLT83
