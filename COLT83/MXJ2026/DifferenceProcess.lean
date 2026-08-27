/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.LinearBandit
public import COLT83.Mathlib.Probability.GaussianWidth
public import COLT83.Mathlib.Probability.BorellTIS
public import COLT83.Mathlib.Matrix.Loewner
public import COLT83.MXJ2026.Width

/-!
# The simple regret is controlled by the difference process

If the recommendation `x` is a `γ`-approximate maximizer of `⟪·, θ'⟫` on `𝒳` (for an estimate
`θ'` of the reward vector `θ`), then its simple regret is at most
`sup_{y ∈ 𝒳} ⟪y, θ - θ'⟫ + sup_{y ∈ 𝒳} ⟪y, θ' - θ⟫ + γ = sup_{y, y' ∈ 𝒳} ⟪y - y', θ' - θ⟫ + γ`
(blueprint `lem:regret_le_difference_process`).
-/

@[expose] public section

open Learning.LinearBandit
open scoped RealInnerProductSpace Pointwise

namespace COLT83

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {𝒳 : Set E} {R : ℝ}

lemma simpleRegret_eq_supportFn_sub (θ x : E) :
    simpleRegret 𝒳 θ x = supportFn 𝒳 θ - ⟪x, θ⟫ := rfl

/-- **The simple regret is controlled by the difference process**
(blueprint `lem:regret_le_difference_process`): if `x ∈ 𝒳` is a `γ`-approximate maximizer of
`⟪·, θ'⟫` on the bounded set `𝒳`, then
`r(x, θ) ≤ sup_{y ∈ 𝒳} ⟪y, θ - θ'⟫ + sup_{y ∈ 𝒳} ⟪y, θ' - θ⟫ + γ`. -/
lemma simpleRegret_le_supportFn_add_supportFn (hne : 𝒳.Nonempty) (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R)
    {θ θ' x : E} (hx : x ∈ 𝒳) {γ : ℝ} (hrec : supportFn 𝒳 θ' - γ ≤ ⟪x, θ'⟫) :
    simpleRegret 𝒳 θ x ≤ supportFn 𝒳 (θ - θ') + supportFn 𝒳 (θ' - θ) + γ := by
  have h1 : supportFn 𝒳 θ ≤ supportFn 𝒳 (θ - θ') + supportFn 𝒳 θ' := by
    have := supportFn_add_le hne hR (θ - θ') θ'
    rwa [sub_add_cancel] at this
  have h2 : ⟪x, θ' - θ⟫ ≤ supportFn 𝒳 (θ' - θ) := inner_le_supportFn hR hx _
  rw [simpleRegret_eq_supportFn_sub]
  rw [inner_sub_right] at h2
  linarith

/-- The difference process
`D v = sup_{x, x' ∈ 𝒳} ⟪x - x', v⟫ = supportFn 𝒳 v + supportFn 𝒳 (-v)`. -/
noncomputable def diffSup (𝒳 : Set E) (v : E) : ℝ := supportFn 𝒳 v + supportFn 𝒳 (-v)

lemma diffSup_eq_supportFn_add_neg (hne : 𝒳.Nonempty) (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) (v : E) :
    diffSup 𝒳 v = supportFn (𝒳 + -𝒳) v := by
  rw [diffSup, supportFn_add hne hR hne.neg (fun x hx ↦ by
    rw [Set.mem_neg] at hx
    simpa using hR _ hx), supportFn_neg_set]

lemma continuous_diffSup (hne : 𝒳.Nonempty) (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) :
    Continuous (diffSup 𝒳) :=
  (continuous_supportFn hne hR).add ((continuous_supportFn hne hR).comp continuous_neg)

end COLT83

namespace COLT83

open MeasureTheory ProbabilityTheory Real Matrix
open scoped Pointwise MatrixOrder NNReal RealInnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒳 : Set (EuclideanSpace ℝ ι)} {R : ℝ}

/-- The mean of the difference process under `N(0, Σ⁻¹)` is `2 gwMat 𝒳 Σ`. -/
lemma integral_diffSup_multivariateGaussian (hne : 𝒳.Nonempty) (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    ∫ v, diffSup 𝒳 v ∂multivariateGaussian 0 S =
      2 * gaussianWidth 𝒳 (multivariateGaussian 0 S) := by
  have hnorm : Integrable (fun ξ : EuclideanSpace ℝ ι ↦ ‖ξ‖) (multivariateGaussian 0 S) :=
    IsGaussian.integrable_id.norm
  have h1 : Integrable (supportFn 𝒳) (multivariateGaussian 0 S) := integrable_supportFn hne hR hnorm
  have h2 : Integrable (fun v ↦ supportFn 𝒳 (-v)) (multivariateGaussian 0 S) := by
    have := (integrable_map_measure (continuous_supportFn hne hR).aestronglyMeasurable
      continuous_neg.measurable.aemeasurable).1 (by rwa [multivariateGaussian_zero_map_neg hS])
    exact this
  simp_rw [diffSup]
  rw [integral_add h1 h2, two_mul, gaussianWidth]
  congr 1
  rw [← multivariateGaussian_zero_map_neg hS, integral_map continuous_neg.measurable.aemeasurable
    (continuous_supportFn hne hR).aestronglyMeasurable]
  rw [multivariateGaussian_zero_map_neg hS]

/-- **Concentration of the difference process** (blueprint `lem:difference_process_concentration`):
for `Δ ~ N(0, Σ⁻¹)` with `xᵀ Σ⁻¹ x ≤ σ²` on the compact set `𝒳`, `D(Δ)` exceeds
`2 gwMat 𝒳 Σ + 2 σ √(2 c_G log(1/δ))` with probability at most `δ`. -/
lemma measureReal_diffSup_gt_le (h𝒳 : IsCompact 𝒳) (hne : 𝒳.Nonempty) {A : Matrix ι ι ℝ}
    (hA : A.PosDef) {σ : ℝ≥0} (hσ0 : 0 < σ)
    (hσ : ∀ x ∈ 𝒳, WithLp.ofLp x ⬝ᵥ A⁻¹ *ᵥ WithLp.ofLp x ≤ σ ^ 2) {δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1) :
    (multivariateGaussian 0 A⁻¹).real
      {v | 2 * gwMat 𝒳 A + 2 * σ * √(2 * gaussianConcentrationConst * log (1 / δ)) <
        diffSup 𝒳 v} ≤ δ := by
  set S := A⁻¹ with hS
  have hSpsd : S.PosSemidef := hA.inv.posSemidef
  have hne' : (𝒳 + -𝒳).Nonempty := hne.add hne.neg
  have hK' : IsCompact (𝒳 + -𝒳) := h𝒳.add h𝒳.neg
  obtain ⟨R, hR⟩ : ∃ R, ∀ x ∈ 𝒳, ‖x‖ ≤ R := by
    obtain ⟨r, hr⟩ := h𝒳.isBounded.subset_closedBall (0 : EuclideanSpace ℝ ι)
    exact ⟨r, fun x hx ↦ mem_closedBall_zero_iff.1 (hr hx)⟩
  set L := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) with hL
  have hLx : ∀ x ∈ 𝒳, ‖L x‖ ≤ σ := fun x hx ↦ by
    have h := norm_toEuclideanCLM_sqrt_sq hSpsd x
    rw [← hL] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) σ.2 two_ne_zero).1 (h.trans_le (hσ x hx))
  have hσ' : ∀ z ∈ 𝒳 + -𝒳, WithLp.ofLp z ⬝ᵥ S *ᵥ WithLp.ofLp z ≤ ((2 * σ : ℝ≥0) : ℝ) ^ 2 := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [Set.mem_neg] at hy
    rw [← norm_toEuclideanCLM_sqrt_sq hSpsd, ← hL]
    have h2 : ‖L (x + y)‖ ≤ (2 * σ : ℝ≥0) := by
      rw [map_add, NNReal.coe_mul, NNReal.coe_ofNat]
      calc ‖L x + L y‖ ≤ ‖L x‖ + ‖L y‖ := norm_add_le _ _
        _ = ‖L x‖ + ‖L (-y)‖ := by rw [map_neg, norm_neg]
        _ ≤ σ + σ := add_le_add (hLx x hx) (hLx (-y) hy)
        _ = 2 * σ := by ring
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have hsg := hasSubgaussianMGF_supportFn_multivariateGaussian hK' hne' hSpsd hσ'
  set u := 2 * σ * √(2 * gaussianConcentrationConst * log (1 / δ)) with hu_def
  have hlog : 0 < log (1 / δ) := by
    rw [one_div]
    exact Real.log_pos (one_lt_inv₀ hδ.1 |>.2 hδ.2)
  have hu : 0 ≤ u := by positivity
  have hmean : ∫ v, supportFn (𝒳 + -𝒳) v ∂multivariateGaussian 0 S = 2 * gwMat 𝒳 A := by
    rw [gwMat, ← hS, ← integral_diffSup_multivariateGaussian hne hR hSpsd]
    exact integral_congr_ae (Filter.Eventually.of_forall fun v ↦
      (diffSup_eq_supportFn_add_neg hne hR v).symm)
  have htail := hsg.measure_ge_le hu
  have hcG : (0 : ℝ) < gaussianConcentrationConst := by
    rw [coe_gaussianConcentrationConst]
    positivity
  have hexp : exp (-u ^ 2 / (2 * ↑(gaussianConcentrationConst * (2 * σ : ℝ≥0) ^ 2))) = δ := by
    have hsq : u ^ 2 = 4 * σ ^ 2 * (2 * gaussianConcentrationConst * log (1 / δ)) := by
      rw [hu_def, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    have hσ0' : (0 : ℝ) < σ := hσ0
    have : -u ^ 2 / (2 * ↑(gaussianConcentrationConst * (2 * σ : ℝ≥0) ^ 2)) = log δ := by
      rw [hsq]
      push_cast
      rw [one_div, Real.log_inv]
      field_simp
      ring
    rw [this, Real.exp_log hδ.1]
  calc (multivariateGaussian 0 A⁻¹).real {v | 2 * gwMat 𝒳 A + u < diffSup 𝒳 v}
      ≤ (multivariateGaussian 0 S).real
          {v | u ≤ supportFn (𝒳 + -𝒳) v - ∫ w, supportFn (𝒳 + -𝒳) w ∂multivariateGaussian 0 S} := by
        refine measureReal_mono fun v hv ↦ ?_
        simp only [Set.mem_ofPred_eq] at hv ⊢
        rw [diffSup_eq_supportFn_add_neg hne hR] at hv
        rw [hmean]
        linarith
    _ ≤ exp (-u ^ 2 / (2 * ↑(gaussianConcentrationConst * (2 * σ : ℝ≥0) ^ 2))) := htail
    _ = δ := hexp

end COLT83
