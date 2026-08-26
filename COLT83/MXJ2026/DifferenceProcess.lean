/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.LinearBandit
public import COLT83.Mathlib.GaussianWidth

/-!
# The simple regret is controlled by the difference process

If the recommendation `x` is a `γ`-approximate maximizer of `⟪·, θ'⟫` on `𝒳` (for an estimate
`θ'` of the reward vector `θ`), then its simple regret is at most
`sup_{y ∈ 𝒳} ⟪y, θ - θ'⟫ + sup_{y ∈ 𝒳} ⟪y, θ' - θ⟫ + γ = sup_{y, y' ∈ 𝒳} ⟪y - y', θ' - θ⟫ + γ`
(blueprint `lem:regret_le_difference_process`).
-/

@[expose] public section

open Learning.LinearBandit
open scoped RealInnerProductSpace

namespace COLT83

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {𝒳 : Set E} {R : ℝ}

lemma simpleRegret_eq_supportFn_sub (θ x : E) :
    simpleRegret 𝒳 θ x = supportFn 𝒳 θ - ⟪x, θ⟫ := rfl

/-- **The simple regret is controlled by the difference process**
(blueprint `lem:regret_le_difference_process`): if `x ∈ 𝒳` is a `γ`-approximate maximizer of
`⟪·, θ'⟫` on the bounded set `𝒳`, then
`r(x, θ) ≤ sup_{y ∈ 𝒳} ⟪y, θ - θ'⟫ + sup_{y ∈ 𝒳} ⟪y, θ' - θ⟫ + γ`. -/
theorem simpleRegret_le_supportFn_add_supportFn (hne : 𝒳.Nonempty) (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R)
    {θ θ' x : E} (hx : x ∈ 𝒳) {γ : ℝ} (hrec : supportFn 𝒳 θ' - γ ≤ ⟪x, θ'⟫) :
    simpleRegret 𝒳 θ x ≤ supportFn 𝒳 (θ - θ') + supportFn 𝒳 (θ' - θ) + γ := by
  have h1 : supportFn 𝒳 θ ≤ supportFn 𝒳 (θ - θ') + supportFn 𝒳 θ' := by
    have := supportFn_add_le hne hR (θ - θ') θ'
    rwa [sub_add_cancel] at this
  have h2 : ⟪x, θ' - θ⟫ ≤ supportFn 𝒳 (θ' - θ) := inner_le_supportFn hR hx _
  rw [simpleRegret_eq_supportFn_sub]
  rw [inner_sub_right] at h2
  linarith

end COLT83
