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
# Properties of the Gaussian width term (Proposition 4 and Theorem 5)

* `gw_le_card`: `w(𝒳) ≤ d` for every spanning action set `𝒳 ⊆ ℝ^d`;
* `gw_le_sqrt_log_ncard`: `w(𝒳) ≤ √(2 d log |𝒳|)` for a finite spanning action set;
* `sqrt_log_le_gw`: `w(𝒳) ≥ (1/8) √(d log ⌊d/2⌋)` for `d ≥ 4`;
* `width_separation`: a finite set `𝒳` (a multi-task set with `m - 1` blocks of size `2` and one
  block of size `m²`, in dimension `d = m² + 2m - 2`) whose span has dimension `r ∈ [d/2, d]`,
  whose intrinsic Gaussian width term is `≤ 3 √(d log d)`, while `√(d log |𝒳|) ≥ 0.49 d^{3/4}`.

Blueprint: `prop:width_le_d`, `prop:width_finite`, `prop:width_lower_sqrt_dlogd`,
`thm:width_separation`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Proposition 4 (i)**: the Gaussian width term of a spanning compact action set in `ℝ^d` is at
most `d`. -/
theorem gw_le_card (𝒳 : Set (EuclideanSpace ℝ ι)) (h𝒳 : IsCompact 𝒳) (hne : 𝒳.Nonempty)
    (hspan : Submodule.span ℝ 𝒳 = ⊤) :
    gw 𝒳 ≤ Fintype.card ι := by
  sorry

/-- **Proposition 4 (ii)**: the Gaussian width term of a finite spanning action set `𝒳 ⊆ ℝ^d` is
at most `√(2 d log |𝒳|)`. -/
theorem gw_le_sqrt_log_ncard (𝒳 : Set (EuclideanSpace ℝ ι)) (hfin : 𝒳.Finite)
    (hne : 𝒳.Nonempty) (hspan : Submodule.span ℝ 𝒳 = ⊤) :
    gw 𝒳 ≤ √(2 * Fintype.card ι * log 𝒳.ncard) := by
  sorry

/-- **Proposition 4 (iii)**: the Gaussian width term of a spanning compact action set in `ℝ^d`,
`d ≥ 4`, is at least `(1/8) √(d log ⌊d/2⌋)`. -/
theorem sqrt_log_le_gw (𝒳 : Set (EuclideanSpace ℝ ι)) (h𝒳 : IsCompact 𝒳) (hne : 𝒳.Nonempty)
    (hspan : Submodule.span ℝ 𝒳 = ⊤) (hd : 4 ≤ Fintype.card ι) :
    √(Fintype.card ι * log (Fintype.card ι / 2 : ℕ)) / 8 ≤ gw 𝒳 := by
  sorry

/-- Block sizes of the multi-task set of Theorem 5: `m - 1` blocks of size `2` and one block of
size `m ^ 2`. -/
def widthSepDims (m : ℕ) : Fin m → ℕ := fun j ↦ if (j : ℕ) + 1 < m then 2 else m ^ 2

/-- **Theorem 5** (Maiti, Xu, Jamieson 2026): for `m ≥ 2`, the multi-task set `𝒳` with `m - 1`
blocks of size `2` and one block of size `m²` lives in dimension `d = m² + 2m - 2`, has
`|𝒳| = 2^{m-1} m²` elements, spans a subspace of dimension `r = m² + m - 1 ∈ [d/2, d]`, and its
intrinsic Gaussian width term satisfies `w_int(𝒳) ≤ 3 √(d log d)`, whereas
`√(d log |𝒳|) ≥ 0.49 d^{3/4}` and `√(r log |𝒳|) ≥ 0.34 d^{3/4}`. -/
theorem width_separation (m : ℕ) (hm : 2 ≤ m) :
    Fintype.card (Σ j, Fin (widthSepDims m j)) = m ^ 2 + 2 * m - 2 ∧
    (multitaskSet (widthSepDims m)).ncard = 2 ^ (m - 1) * m ^ 2 ∧
    Module.finrank ℝ (Submodule.span ℝ (multitaskSet (widthSepDims m))) = m ^ 2 + m - 1 ∧
    ((m ^ 2 + 2 * m - 2 : ℕ) : ℝ) / 2 ≤ (m ^ 2 + m - 1 : ℕ) ∧
    intrinsicGw (multitaskSet (widthSepDims m)) ≤
      3 * √((m ^ 2 + 2 * m - 2 : ℕ) * log (m ^ 2 + 2 * m - 2 : ℕ)) ∧
    0.49 * ((m ^ 2 + 2 * m - 2 : ℕ) : ℝ) ^ (3 / 4 : ℝ) ≤
      √((m ^ 2 + 2 * m - 2 : ℕ) * log (2 ^ (m - 1) * m ^ 2 : ℕ)) ∧
    0.34 * ((m ^ 2 + 2 * m - 2 : ℕ) : ℝ) ^ (3 / 4 : ℝ) ≤
      √((m ^ 2 + m - 1 : ℕ) * log (2 ^ (m - 1) * m ^ 2 : ℕ)) := by
  sorry

end COLT83
