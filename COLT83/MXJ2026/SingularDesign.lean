/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.DifferenceProcess

/-!
# Singular designs fail: the geometric part

Let `x : Fin T → EuclideanSpace ℝ ι` be a design of length `T ≥ 1` in a compact spanning set
`𝒳`, whose design matrix `∑ t, outerSelf (x t)` is singular (not positive definite). Then there
is a direction `v ≠ 0` orthogonal to every `x t` (`exists_ne_zero_inner_eq_zero_of_not_posDef`)
which is not constant on `𝒳`, i.e. `diffSup 𝒳 v > 0` (`diffSup_pos_of_inner_eq_zero`). The two
reward vectors `± α v` are invisible to the design, and their simple regrets sum to
`α diffSup 𝒳 v` at every arm (`simpleRegret_smul_add_simpleRegret_neg_smul`); choosing
`α = 4 ε / diffSup 𝒳 v` gives two instances with the same observation means and regrets summing
to `4 ε` (`exists_singular_instances`, Steps 1–3 of blueprint `lem:singular_design_fails`).
-/

@[expose] public section

open Matrix Learning.LinearBandit
open scoped RealInnerProductSpace

namespace COLT83

variable {ι : Type*} [Fintype ι] {𝒳 : Set (EuclideanSpace ℝ ι)} {T : ℕ}

/-- A direction invisible to a singular design: if `∑ t, outerSelf (x t)` is not positive
definite, some `v ≠ 0` is orthogonal to all `x t`. -/
lemma exists_ne_zero_inner_eq_zero_of_not_posDef {x : Fin T → EuclideanSpace ℝ ι}
    (h : ¬ (∑ t, outerSelf (x t)).PosDef) :
    ∃ v : EuclideanSpace ℝ ι, v ≠ 0 ∧ ∀ t, ⟪x t, v⟫ = 0 := by
  have hpsd := posSemidef_sum_outerSelf Finset.univ x
  have key (u : EuclideanSpace ℝ ι) :
      WithLp.ofLp u ⬝ᵥ (∑ t, outerSelf (x t)) *ᵥ WithLp.ofLp u = ∑ t, ⟪u, x t⟫ ^ 2 := by
    simp only [Matrix.sum_mulVec, dotProduct_sum, dotProduct_outerSelf_mulVec]
  rw [Matrix.posDef_iff_dotProduct_mulVec] at h
  push Not at h
  obtain ⟨v, hv, hle⟩ := h hpsd.1
  rw [star_trivial] at hle
  have hsum : ∑ t, ⟪WithLp.toLp 2 v, x t⟫ ^ 2 ≤ 0 := (key (WithLp.toLp 2 v)).symm.trans_le hle
  refine ⟨WithLp.toLp 2 v, fun h0 ↦ hv (by simpa using congrArg WithLp.ofLp h0), fun t ↦ ?_⟩
  rw [real_inner_comm]
  exact (pow_eq_zero_iff two_ne_zero).1
    ((Finset.sum_eq_zero_iff_of_nonneg fun t _ ↦ sq_nonneg _).1
      (le_antisymm hsum (Finset.sum_nonneg fun t _ ↦ sq_nonneg _)) t (Finset.mem_univ _))

/-- On a spanning compact set, a nonzero direction orthogonal to a nonempty design (`T ≥ 1`)
is not constant on `𝒳`: `diffSup 𝒳 v > 0`. -/
lemma diffSup_pos_of_inner_eq_zero (h𝒳 : IsCompact 𝒳) (hspan : Submodule.span ℝ 𝒳 = ⊤)
    {x : Fin T → EuclideanSpace ℝ ι} (hx : ∀ t, x t ∈ 𝒳) (hT : 1 ≤ T)
    {v : EuclideanSpace ℝ ι} (hv : v ≠ 0) (h0 : ∀ t, ⟪x t, v⟫ = 0) :
    0 < diffSup 𝒳 v := by
  obtain ⟨R, hR⟩ : ∃ R, ∀ y ∈ 𝒳, ‖y‖ ≤ R := by
    obtain ⟨r, hr⟩ := h𝒳.isBounded.subset_closedBall (0 : EuclideanSpace ℝ ι)
    exact ⟨r, fun y hy ↦ mem_closedBall_zero_iff.1 (hr hy)⟩
  by_contra hle
  rw [not_lt, diffSup] at hle
  have h1 : 0 ≤ supportFn 𝒳 v := by
    have := inner_le_supportFn hR (hx ⟨0, hT⟩) v
    rwa [h0] at this
  have h2 : 0 ≤ supportFn 𝒳 (-v) := by
    have := inner_le_supportFn hR (hx ⟨0, hT⟩) (-v)
    rwa [inner_neg_right, h0, neg_zero] at this
  have h3 : ∀ y ∈ 𝒳, ⟪v, y⟫ = 0 := fun y hy ↦ by
    have hy1 := inner_le_supportFn hR hy v
    have hy2 := inner_le_supportFn hR hy (-v)
    rw [inner_neg_right] at hy2
    rw [real_inner_comm]
    linarith
  have hsub : Submodule.span ℝ 𝒳 ≤ (ℝ ∙ v)ᗮ := by
    rw [Submodule.span_le]
    exact fun y hy ↦ Submodule.mem_orthogonal_singleton_iff_inner_right.2 (h3 y hy)
  have hvmem : v ∈ (ℝ ∙ v)ᗮ := hsub (hspan ▸ Submodule.mem_top)
  exact hv (inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 hvmem))

/-- The two instances `±α v` have simple regrets summing to `α diffSup 𝒳 v` at every arm. -/
lemma simpleRegret_smul_add_simpleRegret_neg_smul {α : ℝ} (hα : 0 ≤ α)
    (v y : EuclideanSpace ℝ ι) :
    simpleRegret 𝒳 (α • v) y + simpleRegret 𝒳 (-(α • v)) y = α * diffSup 𝒳 v := by
  simp only [simpleRegret_eq_supportFn_sub, ← smul_neg, supportFn_smul _ hα, inner_smul_right,
    inner_neg_right, diffSup]
  ring

/-- **Singular designs fail** (geometric part, blueprint `lem:singular_design_fails`): for a
singular design of length `T ≥ 1` on a spanning compact set and `ε > 0`, there are two reward
vectors `θ θ'` giving the same observation means `⟪x t, θ⟫ = ⟪x t, θ'⟫` (in fact `0`) and
whose simple regrets sum to `4 ε` at every arm. -/
lemma exists_singular_instances (h𝒳 : IsCompact 𝒳) (hspan : Submodule.span ℝ 𝒳 = ⊤)
    {x : Fin T → EuclideanSpace ℝ ι} (hx : ∀ t, x t ∈ 𝒳) (hT : 1 ≤ T)
    (hS : ¬ (∑ t, outerSelf (x t)).PosDef) {ε : ℝ} (hε : 0 < ε) :
    ∃ θ θ' : EuclideanSpace ℝ ι, (∀ t, ⟪x t, θ⟫ = 0) ∧ (∀ t, ⟪x t, θ'⟫ = 0) ∧
      ∀ y, simpleRegret 𝒳 θ y + simpleRegret 𝒳 θ' y = 4 * ε := by
  obtain ⟨v, hv, h0⟩ := exists_ne_zero_inner_eq_zero_of_not_posDef hS
  have hD := diffSup_pos_of_inner_eq_zero h𝒳 hspan hx hT hv h0
  have hα : 0 ≤ 4 * ε / diffSup 𝒳 v := by positivity
  refine ⟨(4 * ε / diffSup 𝒳 v) • v, -((4 * ε / diffSup 𝒳 v) • v),
    fun t ↦ by simp [inner_smul_right, h0], fun t ↦ by simp [inner_smul_right, h0], fun y ↦ ?_⟩
  rw [simpleRegret_smul_add_simpleRegret_neg_smul hα, div_mul_cancel₀ _ hD.ne']

end COLT83
