/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.Run
public import COLT83.MXJ2026.NormalizedDesign

/-!
# The baseline lower bound for adaptive algorithms

Every `(ε, δ)`-PAC fixed-budget identification algorithm on a spanning compact action set
`𝒳 ⊆ ℝ^d`, `d ≥ 2`, with `δ < 1/4`, has budget
`T ≥ (2 - √2) / (32 ε²) log (1 / (4 δ))` (`baseline_le_budget_of_isPAC`, blueprint
`lem:baseline_lower`). This is the two-point step of the proof of Theorem 2.

The argument works in the original coordinates: with `M = normalizeMat A_G` the normalizing matrix
of a `G`-optimal design (so that `‖M x‖ ≤ 1` on `𝒳`) and a well-separated pair `x₁, k` of support
points (`‖M x₁ - M k‖² ≥ 2 - √2`, `IsGOptimalDesign.exists_separated_pair`), the two reward
vectors are `θ± = ±(4ε/ϱ) M u` with `u = (M x₁ - M k) / ϱ`. An `ε`-optimal recommendation under
`θ₊` satisfies `⟪M rec, u⟫ ≥ s + ϱ/4` and under `θ₋` it satisfies `⟪M rec, u⟫ ≤ s - ϱ/4`, so the
test `{⟪M rec, u⟫ ≥ s}` has error at most `δ` under both, while the divergence between the laws
of the recommendations is at most `32 T ε² / ϱ²`; the Bretagnolle–Huber inequality concludes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Real Learning Learning.LinearBandit
open scoped RealInnerProductSpace ENNReal

namespace COLT83

variable {ι : Type*} [Fintype ι]

/-- **Baseline lower bound** (blueprint `lem:baseline_lower`): an `(ε, δ)`-PAC fixed-budget
identification algorithm on a spanning compact action set in dimension `d ≥ 2`, with
`δ < 1/4`, has budget `T ≥ (2 - √2) / (32 ε²) log (1 / (4 δ))`. -/
lemma baseline_le_budget_of_isPAC (𝒳 : Set (EuclideanSpace ℝ ι)) (h𝒳 : IsCompact 𝒳)
    (hspan : Submodule.span ℝ 𝒳 = ⊤) (hd : 2 ≤ Fintype.card ι) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : δ ∈ Set.Ioo 0 (1 / 4)) {T : ℕ} (A : IdentAlg 𝒳 ℝ 𝒳) (hA : A.IsFixedBudget T)
    (hpac : IsPAC 𝒳 A ε δ) :
    (2 - √2) / (32 * ε ^ 2) * log (1 / (4 * δ)) ≤ T := by
  classical
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨R, hR⟩ : ∃ R, ∀ x ∈ 𝒳, ‖x‖ ≤ R := by
    obtain ⟨r, hr⟩ := h𝒳.isBounded.subset_closedBall (0 : EuclideanSpace ℝ ι)
    exact ⟨r, fun x hx ↦ mem_closedBall_zero_iff.1 (hr hx)⟩
  -- a `G`-optimal design and a well-separated pair of support points
  obtain ⟨w, hw⟩ := exists_isGOptimalDesign h𝒳 hspan
  obtain ⟨x₁, hx₁⟩ := hw.isDesign.support_nonempty
  obtain ⟨k, hk, -, hsep⟩ := hw.exists_separated_pair hd hx₁
  set L := Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) with hL
  have hx₁𝒳 : x₁ ∈ 𝒳 := hw.isDesign.mem_of_mem_support hx₁
  have hk𝒳 : k ∈ 𝒳 := hw.isDesign.mem_of_mem_support hk
  -- the two-point instance
  set ϱ := ‖L x₁ - L k‖ with hϱ
  have hϱ2 : 2 - √2 ≤ ϱ ^ 2 := hsep
  have hsqrt2 : √2 < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hϱpos : 0 < ϱ := by nlinarith [norm_nonneg (L x₁ - L k)]
  set u := ϱ⁻¹ • (L x₁ - L k) with hu
  have hu_norm : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, Real.norm_of_nonneg hϱpos.le, ← hϱ, inv_mul_cancel₀ hϱpos.ne']
  have hinner_diff : ⟪L x₁ - L k, u⟫ = ϱ := by
    rw [hu, real_inner_smul_right, real_inner_self_eq_norm_sq, ← hϱ]
    field_simp
  set s := (⟪L x₁, u⟫ + ⟪L k, u⟫) / 2 with hs
  rw [inner_sub_left] at hinner_diff
  have hx₁u : ⟪L x₁, u⟫ = s + ϱ / 2 := by rw [hs]; linarith
  have hku : ⟪L k, u⟫ = s - ϱ / 2 := by rw [hs]; linarith
  set c := 4 * ε / ϱ with hc
  have hcpos : 0 < c := by positivity
  have hcϱ : c * (ϱ / 4) = ε := by rw [hc]; field_simp
  set θp := c • L u with hθp
  set θm := -θp with hθm
  have hinner : ∀ x : EuclideanSpace ℝ ι, ⟪x, θp⟫ = c * ⟪L x, u⟫ := fun x ↦ by
    rw [hθp, real_inner_smul_right, hL, inner_toEuclideanCLM_normalizeMat]
  have hinnerm : ∀ x : EuclideanSpace ℝ ι, ⟪x, θm⟫ = -(c * ⟪L x, u⟫) := fun x ↦ by
    rw [hθm, inner_neg_right, hinner]
  -- the divergence bound
  have hC : ∀ x ∈ 𝒳, ⟪x, θm - θp⟫ ^ 2 ≤ (2 * c) ^ 2 := by
    intro x hx
    rw [inner_sub_right, hinnerm, hinner]
    have h1 : |⟪L x, u⟫| ≤ 1 := by
      calc |⟪L x, u⟫| ≤ ‖L x‖ * ‖u‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 := by rw [hu_norm, mul_one]; exact hw.norm_normalizeMat_le hx
    have h2 : ⟪L x, u⟫ ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) h1
    nlinarith [sq_nonneg c]
  -- the test
  set B : Set 𝒳 := {x | s ≤ ⟪L x, u⟫} with hB
  have hcont : Continuous fun x : 𝒳 ↦ ⟪L (x : EuclideanSpace ℝ ι), u⟫ :=
    (L.continuous.comp continuous_subtype_val).inner continuous_const
  have hBm : MeasurableSet B := measurableSet_le measurable_const hcont.measurable
  have hsup : ∀ θ, ∀ x ∈ 𝒳, ⟪x, θ⟫ ≤ ⨆ y : 𝒳, ⟪(y : EuclideanSpace ℝ ι), θ⟫ :=
    fun θ x hx ↦ inner_le_supportFn hR hx θ
  have hgood_p : ∀ x : 𝒳, simpleRegret 𝒳 θp x ≤ ε → x ∈ B := by
    intro x hx
    have h1 := hsup θp x₁ hx₁𝒳
    simp only [simpleRegret] at hx
    rw [hinner, hx₁u] at h1
    rw [hinner] at hx
    have h3 : s + ϱ / 4 - ⟪L x, u⟫ ≤ 0 := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_pos hcpos hcon]
    change s ≤ ⟪L x, u⟫
    linarith
  have hgood_m : ∀ x : 𝒳, simpleRegret 𝒳 θm x ≤ ε → x ∉ B := by
    intro x hx
    have h1 := hsup θm k hk𝒳
    simp only [simpleRegret] at hx
    rw [hinnerm, hku] at h1
    rw [hinnerm] at hx
    have h3 : ⟪L x, u⟫ - s + ϱ / 4 ≤ 0 := by
      by_contra hcon
      push Not at hcon
      nlinarith [mul_pos hcpos hcon]
    change ¬ s ≤ ⟪L x, u⟫
    linarith
  -- the canonical runs
  have := hA.isMarkovKernel_output
  have hrun_p := hA.isRun_fixedBudgetRunMeasure (env := linearGaussianEnv 𝒳 θp)
  have hrun_m := hA.isRun_fixedBudgetRunMeasure (env := linearGaussianEnv 𝒳 θm)
  set Pp := A.fixedBudgetRunMeasure (linearGaussianEnv 𝒳 θp) T with hPp
  set Pm := A.fixedBudgetRunMeasure (linearGaussianEnv 𝒳 θm) T with hPm
  have hpac_p := hpac θp Pp _ _ _ hrun_p
  have hpac_m := hpac θm Pm _ _ _ hrun_m
  change 1 - δ ≤ Pp.real {ω : (ℕ → 𝒳 × ℝ) × 𝒳 | simpleRegret 𝒳 θp (ω.2 : EuclideanSpace ℝ ι) ≤ ε}
    at hpac_p
  change 1 - δ ≤ Pm.real {ω : (ℕ → 𝒳 × ℝ) × 𝒳 | simpleRegret 𝒳 θm (ω.2 : EuclideanSpace ℝ ι) ≤ ε}
    at hpac_m
  have hmeas : ∀ θ : EuclideanSpace ℝ ι,
      MeasurableSet {ω : (ℕ → 𝒳 × ℝ) × 𝒳 | simpleRegret 𝒳 θ (ω.2 : EuclideanSpace ℝ ι) ≤ ε} := by
    intro θ
    have : Continuous fun x : 𝒳 ↦ simpleRegret 𝒳 θ x :=
      continuous_const.sub (continuous_subtype_val.inner continuous_const)
    exact measurable_snd (measurableSet_le this.measurable measurable_const)
  have herr_p : Pp.real (Prod.snd ⁻¹' Bᶜ) ≤ δ := by
    calc Pp.real (Prod.snd ⁻¹' Bᶜ)
        ≤ Pp.real {ω : (ℕ → 𝒳 × ℝ) × 𝒳 | simpleRegret 𝒳 θp (ω.2 : EuclideanSpace ℝ ι) ≤ ε}ᶜ :=
          measureReal_mono fun ω hω hgood ↦ hω (hgood_p _ hgood)
      _ ≤ δ := by rw [measureReal_compl (hmeas θp), probReal_univ]; linarith
  have herr_m : Pm.real (Prod.snd ⁻¹' B) ≤ δ := by
    calc Pm.real (Prod.snd ⁻¹' B)
        ≤ Pm.real {ω : (ℕ → 𝒳 × ℝ) × 𝒳 | simpleRegret 𝒳 θm (ω.2 : EuclideanSpace ℝ ι) ≤ ε}ᶜ :=
          measureReal_mono fun ω hω hgood ↦ hgood_m _ hgood hω
      _ ≤ δ := by rw [measureReal_compl (hmeas θm), probReal_univ]; linarith
  -- Bretagnolle–Huber
  have hbh := IsRun.exp_neg_le_measureReal_add_of_sq_le hC hA hrun_m hrun_p hBm
  have hexp : Real.exp (-(T * ((2 * c) ^ 2 / 2))) ≤ 4 * δ := by linarith
  have hlog : -(T * ((2 * c) ^ 2 / 2)) ≤ log (4 * δ) :=
    (Real.le_log_iff_exp_le (by linarith [hδ.1])).2 hexp
  have hlogpos : 0 < log (1 / (4 * δ)) := by
    refine Real.log_pos ?_
    rw [lt_one_div (by norm_num) (by linarith [hδ.1])]
    linarith [hδ.2]
  have hkey : log (1 / (4 * δ)) ≤ T * (2 * c ^ 2) := by
    rw [one_div, Real.log_inv]
    nlinarith
  have hc2 : ϱ ^ 2 * c ^ 2 = 16 * ε ^ 2 := by
    rw [hc]
    field_simp
    norm_num
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  calc (2 - √2) * log (1 / (4 * δ)) ≤ ϱ ^ 2 * log (1 / (4 * δ)) :=
        mul_le_mul_of_nonneg_right hϱ2 hlogpos.le
    _ ≤ ϱ ^ 2 * (T * (2 * c ^ 2)) := mul_le_mul_of_nonneg_left hkey (sq_nonneg _)
    _ = T * (32 * ε ^ 2) := by linear_combination (2 * (T : ℝ)) * hc2

end COLT83
