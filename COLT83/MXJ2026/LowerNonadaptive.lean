/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.LinearBandit
public import COLT83.MXJ2026.StructuredSets
public import COLT83.MXJ2026.Width
public import COLT83.MXJ2026.BayesModel
public import COLT83.MXJ2026.SingularDesign
public import COLT83.MXJ2026.WidthDesign

/-!
# The lower bound for non-adaptive fixed designs (Theorem 3)

Every fixed-design `(ε, δ)`-PAC identification algorithm on a spanning action set `𝒳` with
`δ ≤ 1/10` has budget `T ≥ w(𝒳)² / (70 ε²)`.

The proof is Bayesian (`COLT83/MXJ2026/BayesModel.lean`): with the prior
`θ ~ N(0, τ² Σ_T⁻¹)` and `τ = √2 - 1`, the expected simple regret of *any* recommendation rule
is at least `(√2 - 1)/2 · w(𝒳, Σ_T)` (`le_integral_simpleRegret_bayesJoint`), while for an
`(ε, δ)`-PAC algorithm it is at most `ε + 2 τ δ w(𝒳, Σ_T)`
(`integral_simpleRegret_bayesJoint_le`); singular designs are ruled out separately
(`exists_singular_instances`), and `w(𝒳, Σ_T) ≥ w(𝒳)/√T` (`gw_le_sqrt_mul_gwMat_sum`).

Blueprint: `thm:lower_nonadaptive`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Learning Learning.LinearBandit

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The optimized constant of the Bayesian lower bound: for `τ = √2 - 1`,
`τ - c (τ + 1) = (√2 - 1)/2` with `c = τ²/(1 + τ²)`. -/
lemma bayesC_identity : (√2 - 1) - bayesC (√2 - 1) * ((√2 - 1) + 1) = (√2 - 1) / 2 := by
  have hs : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h1 : (1 : ℝ) + (√2 - 1) ^ 2 ≠ 0 := by positivity
  rw [bayesC]
  field_simp
  nlinarith [hs, Real.sqrt_nonneg 2]

/-- **Theorem 3** (Maiti, Xu, Jamieson 2026): a fixed-design (non-adaptive) identification
algorithm with budget `T ≥ 1` which is `(ε, δ)`-PAC on a spanning compact action set `𝒳`, with
`δ ≤ 1/10`, satisfies `T ≥ w(𝒳)² / (70 ε²)`. -/
theorem le_budget_of_isFixedDesign_of_isPAC (𝒳 : Set (EuclideanSpace ℝ ι)) (h𝒳 : IsCompact 𝒳)
    (hne : 𝒳.Nonempty) (hspan : Submodule.span ℝ 𝒳 = ⊤)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : δ ∈ Set.Ioc 0 (1 / 10)) {T : ℕ} (hT : 1 ≤ T)
    (A : IdentAlg 𝒳 ℝ 𝒳) (hA : A.IsFixedBudget T)
    (hdes : A.IsFixedDesign) (hpac : IsPAC 𝒳 A ε δ) :
    gw 𝒳 ^ 2 / (70 * ε ^ 2) ≤ T := by
  obtain ⟨x', hx'⟩ := hdes
  obtain ⟨R, hR⟩ : ∃ R, ∀ z ∈ 𝒳, ‖z‖ ≤ R := by
    obtain ⟨r, hr⟩ := h𝒳.isBounded.subset_closedBall (0 : EuclideanSpace ℝ ι)
    exact ⟨r, fun z hz ↦ mem_closedBall_zero_iff.1 (hr hz)⟩
  have := hA.isMarkovKernel_output
  set x : Fin T → EuclideanSpace ℝ ι := fun t ↦ (x' t : EuclideanSpace ℝ ι) with hx_def
  have hx : ∀ t, x t ∈ 𝒳 := fun t ↦ (x' t).2
  have hxeta : (fun t : Fin T ↦ (⟨x t, hx t⟩ : 𝒳)) = fun t : Fin T ↦ x' t := by
    funext t
    exact Subtype.coe_eta _ _
  have hδ0 : 0 < δ := hδ.1
  have hδ1 : δ ≤ 1 / 10 := hδ.2
  by_cases hS : (∑ t, outerSelf (x t)).PosDef
  · -- the Bayesian argument
    set τ : ℝ := √2 - 1 with hτ_def
    have hs2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hs_lb : (1.414 : ℝ) ≤ √2 := by
      rw [show (1.414 : ℝ) = √(1.414 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hs_ub : √2 ≤ 1.4143 := by
      rw [show (1.4143 : ℝ) = √(1.4143 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hτ0 : 0 ≤ τ := by rw [hτ_def]; linarith
    set w : ℝ := gwMat 𝒳 (∑ t, outerSelf (x t)) with hw_def
    have hw0 : 0 ≤ w := gwMat_nonneg hne hR _
    -- lower bound on the Bayesian regret
    have hlow := le_integral_simpleRegret_bayesJoint A x hx τ hne hR hS hτ0
    rw [← hw_def, show τ * w - bayesC τ * (τ * w + w) = ((√2 - 1) / 2) * w by
      have := bayesC_identity
      rw [hτ_def]
      nlinarith [this]] at hlow
    -- upper bound from the PAC property
    have hup := integral_simpleRegret_bayesJoint_le A x hx τ hne hR hS hτ0 hε.le
      (fun g ↦ by
        rw [hxeta]
        exact measureReal_lt_simpleRegret_bayes_le hpac hA hx' (bayesParam x τ g))
    rw [← hw_def] at hup
    -- arithmetic
    have hcomb : ((√2 - 1) / 2) * w ≤ ε + δ * (2 * τ * w) := le_trans hlow hup
    have h207 : (0.207 : ℝ) * w ≤ ((√2 - 1) / 2) * w := by
      have : (0.207 : ℝ) ≤ (√2 - 1) / 2 := by linarith
      exact mul_le_mul_of_nonneg_right this hw0
    have hδτ : δ * (2 * τ * w) ≤ 0.083 * w := by
      have hτ_ub : τ ≤ 0.4143 := by rw [hτ_def]; linarith
      nlinarith [hδ0.le, hδ1, hw0, hτ0, mul_nonneg hτ0 hw0, mul_nonneg hδ0.le hw0]
    have hkey : (0.12 : ℝ) * w ≤ ε := by linarith
    -- from the design width to the width term
    have hTpos : 0 < T := hT
    have hgw : gw 𝒳 ≤ √T * w := gw_le_sqrt_mul_gwMat_sum hne hR hTpos hx hS
    have hgw0 : 0 ≤ gw 𝒳 := gw_nonneg hne hR
    have hsqrtT : (0 : ℝ) ≤ √T := Real.sqrt_nonneg _
    have hTsq : √T ^ 2 = T := Real.sq_sqrt (Nat.cast_nonneg T)
    have h1 : (0.12 : ℝ) * gw 𝒳 ≤ √T * ε := by
      calc (0.12 : ℝ) * gw 𝒳 ≤ 0.12 * (√T * w) := by gcongr
        _ = √T * (0.12 * w) := by ring
        _ ≤ √T * ε := by gcongr
    have h2 : (0.0144 : ℝ) * gw 𝒳 ^ 2 ≤ T * ε ^ 2 := by
      have := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 0.12 * gw 𝒳) h1
      nlinarith [hTsq]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [h2, sq_nonneg (gw 𝒳)]
  · -- singular design: the algorithm cannot be PAC
    exfalso
    obtain ⟨θ, θ', h0, h0', hsum⟩ := exists_singular_instances h𝒳 hspan hx hT hS hε
    have hlaw : fixedDesignPairLaw A (fun t : Fin T ↦ x' t) θ =
        fixedDesignPairLaw A (fun t : Fin T ↦ x' t) θ' :=
      fixedDesignPairLaw_congr A _ fun t ↦ by
        rw [show ((x' t : EuclideanSpace ℝ ι)) = x t from rfl, h0 t, h0' t]
    have hp1 := hpac.le_measureReal_fixedDesignPairLaw hA hx' θ
    have hp2 := hpac.le_measureReal_fixedDesignPairLaw hA hx' θ'
    rw [hlaw] at hp1
    set μ := fixedDesignPairLaw A (fun t : Fin T ↦ x' t) θ' with hμ_def
    have hmeas : ∀ ϑ : EuclideanSpace ℝ ι,
        MeasurableSet {p : (Fin T → 𝒳 × ℝ) × 𝒳 |
          simpleRegret 𝒳 ϑ (p.2 : EuclideanSpace ℝ ι) ≤ ε} := fun ϑ ↦ by
      refine measurableSet_le ?_ measurable_const
      exact (continuous_const.sub ((continuous_subtype_val.comp continuous_snd).inner
        continuous_const)).measurable
    have hsub : {p : (Fin T → 𝒳 × ℝ) × 𝒳 |
        simpleRegret 𝒳 θ' (p.2 : EuclideanSpace ℝ ι) ≤ ε} ⊆
        {p : (Fin T → 𝒳 × ℝ) × 𝒳 |
          simpleRegret 𝒳 θ (p.2 : EuclideanSpace ℝ ι) ≤ ε}ᶜ := by
      intro p hp
      have h := hsum (p.2 : EuclideanSpace ℝ ι)
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
      simp only [Set.mem_ofPred_eq] at hp
      linarith
    have h3 := measureReal_mono (μ := μ) hsub
    rw [measureReal_compl (hmeas θ), probReal_univ] at h3
    linarith

end COLT83
