/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.DivergenceDecomposition
public import LeanMachineLearning.SequentialLearning.IonescuTulceaSpace
public import COLT83.MXJ2026.NormalizedDesign
public import COLT83.Mathlib.InformationTheory.KLMixture
public import COLT83.Mathlib.InformationTheory.BretagnolleHuber

/-!
# The mixture testing problem

Let `w` be a `G`-optimal design on `𝒳 ⊆ ℝ^d` with normalizing matrix `M = normalizeMat A(w)`
(`COLT83.normalizeMat`), so that `‖M x‖ ≤ 1` on `𝒳`, `‖M x‖ = 1` on the support of `w` and
`∑ₓ w x (M x)(M x)ᵀ = I / d`. The *mixture testing problem* with parameter `ε` opposes the reward
vector `0` to the mixture, with weights `w x`, of the reward vectors
`mixtureParam w ε x = 3 ε M (M x)`, `x` in the support of `w` (these are the vectors
`3 ε v` of the normalized instance, `v = M x`, pulled back to the original coordinates).

For any algorithm `alg` and horizon `N`, `histLaw alg N θ` is the law of the history up to time
`N` in the linear Gaussian environment with reward vector `θ`, and `mixtureHistLaw alg N w ε` is
the mixture of these laws over the alternatives.

## Main results

* `IsGOptimalDesign.klDiv_histLaw_zero_mixtureHistLaw_le` (blueprint `lem:mixture_kl`): the
  divergence from the law under `0` to the mixture is at most `(N + 1) · 9 ε² / (2 d)`, by
  convexity of the divergence in its second argument, the divergence decomposition and the
  identity `∑ₓ w x ⟪y, θ⁽ˣ⁾⟫² = 9 ε² ‖M y‖² / d ≤ 9 ε² / d`.
* `IsGOptimalDesign.exp_neg_le_of_mixture` (blueprint `lem:test_lower`): for every measurable
  set `E` of histories, `½ exp (-(N + 1) 9 ε² / (2 d)) ≤ P₀(E) + max_x P_{θ⁽ˣ⁾}(Eᶜ)`
  (Bretagnolle–Huber for the mixture).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Real Finset Learning Learning.LinearBandit
open scoped RealInnerProductSpace ENNReal NNReal

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒳 : Set (EuclideanSpace ℝ ι)}
  {w : EuclideanSpace ℝ ι →₀ ℝ}

/-- The reward vector `3 ε M (M x)` of the mixture alternative associated with the support point
`x` of the design `w`, where `M = normalizeMat (designMatrix w)`; on the normalized instance
this is `3 ε v` with `v = M x`. -/
noncomputable def mixtureParam (w : EuclideanSpace ℝ ι →₀ ℝ) (ε : ℝ) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι :=
  (3 * ε) • Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w))
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) x)

lemma inner_mixtureParam (ε : ℝ) (y x : EuclideanSpace ℝ ι) :
    ⟪y, mixtureParam w ε x⟫ =
      3 * ε * ⟪Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) y,
        Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) x⟫ := by
  rw [mixtureParam, real_inner_smul_right, inner_toEuclideanCLM_normalizeMat]

/-- The value of the support point `x` under the alternative `mixtureParam w ε x` is `3 ε`. -/
lemma IsGOptimalDesign.inner_mixtureParam_self [Nonempty ι] (hw : IsGOptimalDesign 𝒳 w) (ε : ℝ)
    {x : EuclideanSpace ℝ ι} (hx : x ∈ w.support) :
    ⟪x, mixtureParam w ε x⟫ = 3 * ε := by
  rw [inner_mixtureParam, real_inner_self_eq_norm_sq, hw.norm_normalizeMat_eq_one hx]
  ring

/-- The weight of `x` in the design `w`, as a nonnegative real. -/
noncomputable def designWeight (w : EuclideanSpace ℝ ι →₀ ℝ) (x : EuclideanSpace ℝ ι) : ℝ≥0 :=
  (w x).toNNReal

omit [Fintype ι] [DecidableEq ι] in
lemma IsDesign.coe_designWeight (hw : IsDesign 𝒳 w) (x : EuclideanSpace ℝ ι) :
    (designWeight w x : ℝ) = w x :=
  Real.coe_toNNReal _ (hw.nonneg x)

omit [Fintype ι] [DecidableEq ι] in
lemma IsDesign.sum_designWeight (hw : IsDesign 𝒳 w) : ∑ x ∈ w.support, designWeight w x = 1 := by
  rw [← NNReal.coe_inj, NNReal.coe_sum, NNReal.coe_one, ← hw.sum_eq_one]
  exact sum_congr rfl fun x _ ↦ hw.coe_designWeight x

/-- `∑ₓ w x ⟪y, θ⁽ˣ⁾⟫² = 9 ε² ‖M y‖² / d`. -/
lemma IsGOptimalDesign.sum_mul_inner_mixtureParam_sq [Nonempty ι] (hw : IsGOptimalDesign 𝒳 w)
    (ε : ℝ)
    (y : EuclideanSpace ℝ ι) :
    ∑ x ∈ w.support, w x * ⟪y, mixtureParam w ε x⟫ ^ 2 =
      9 * ε ^ 2 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) y‖ ^ 2 /
        Fintype.card ι) := by
  rw [← hw.sum_mul_inner_normalizeMat_sq y, mul_sum]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [inner_mixtureParam]
  ring

/-- `∑ₓ w x ⟪y, θ⁽ˣ⁾⟫² ≤ 9 ε² / d` for `y ∈ 𝒳`. -/
lemma IsGOptimalDesign.sum_mul_inner_mixtureParam_sq_le [Nonempty ι] (hw : IsGOptimalDesign 𝒳 w)
    (ε : ℝ)
    {y : EuclideanSpace ℝ ι} (hy : y ∈ 𝒳) :
    ∑ x ∈ w.support, w x * ⟪y, mixtureParam w ε x⟫ ^ 2 ≤ 9 * ε ^ 2 / Fintype.card ι := by
  rw [hw.sum_mul_inner_mixtureParam_sq]
  have h2 : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) y‖ ^ 2 ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (hw.norm_normalizeMat_le hy)
  calc 9 * ε ^ 2 * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) y‖ ^ 2 /
        Fintype.card ι)
      ≤ 9 * ε ^ 2 * (1 / Fintype.card ι) := by gcongr
    _ = 9 * ε ^ 2 / Fintype.card ι := by ring

section kl

variable (alg : Algorithm 𝒳 ℝ) (N : ℕ)

/-- The law of the history up to time `N` of the algorithm `alg` in the linear Gaussian
environment on `𝒳` with reward vector `θ`. -/
noncomputable def histLaw (θ : EuclideanSpace ℝ ι) : Measure (Iic N → 𝒳 × ℝ) :=
  (trajMeasure alg (linearGaussianEnv 𝒳 θ)).map (IT.hist N)

instance (θ : EuclideanSpace ℝ ι) : IsProbabilityMeasure (histLaw alg N θ) :=
  Measure.isProbabilityMeasure_map (IT.measurable_hist N).aemeasurable

omit [DecidableEq ι] in
lemma histLaw_apply (θ : EuclideanSpace ℝ ι) {E : Set (Iic N → 𝒳 × ℝ)} (hE : MeasurableSet E) :
    histLaw alg N θ E = trajMeasure alg (linearGaussianEnv 𝒳 θ) (IT.hist N ⁻¹' E) :=
  Measure.map_apply (IT.measurable_hist N) hE

omit [DecidableEq ι] in
lemma histLaw_real_apply (θ : EuclideanSpace ℝ ι) {E : Set (Iic N → 𝒳 × ℝ)}
    (hE : MeasurableSet E) :
    (histLaw alg N θ).real E = (trajMeasure alg (linearGaussianEnv 𝒳 θ)).real (IT.hist N ⁻¹' E) :=
  by rw [measureReal_def, histLaw_apply alg N θ hE, measureReal_def]

/-- The mixture, with the weights of the design `w`, of the laws of the history up to time `N`
under the alternatives `mixtureParam w ε x`, `x` in the support of `w`. -/
noncomputable def mixtureHistLaw (w : EuclideanSpace ℝ ι →₀ ℝ) (ε : ℝ) :
    Measure (Iic N → 𝒳 × ℝ) :=
  ∑ x ∈ w.support, (designWeight w x : ℝ≥0∞) • histLaw alg N (mixtureParam w ε x)

lemma IsDesign.isProbabilityMeasure_mixtureHistLaw (hw : IsDesign 𝒳 w) (ε : ℝ) :
    IsProbabilityMeasure (mixtureHistLaw alg N w ε) :=
  isProbabilityMeasure_finsetSum_smul hw.sum_designWeight

/-- **Divergence to the mixture** (blueprint `lem:mixture_kl`): for every algorithm and horizon
`N`, the divergence from the law of the history under `θ = 0` to the mixture of the laws under
the alternatives is at most `(N + 1) · 9 ε² / (2 d)`. -/
theorem IsGOptimalDesign.klDiv_histLaw_zero_mixtureHistLaw_le [Nonempty ι]
    (hw : IsGOptimalDesign 𝒳 w)
    {R : ℝ} (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) (ε : ℝ) :
    klDiv (histLaw alg N 0) (mixtureHistLaw alg N w ε) ≤
      ENNReal.ofReal ((N + 1) * (9 * ε ^ 2 / (2 * Fintype.card ι))) := by
  have hwd := hw.isDesign
  set P₀ := trajMeasure alg (linearGaussianEnv 𝒳 0) with hP₀
  have hrun := IT.isAlgEnvSeq_trajMeasure alg (linearGaussianEnv 𝒳 0)
  set f : EuclideanSpace ℝ ι → ℕ → (ℕ → 𝒳 × ℝ) → ℝ := fun x t h ↦
    ⟪((IT.action t h : 𝒳) : EuclideanSpace ℝ ι), 0 - mixtureParam w ε x⟫ ^ 2 / 2 with hf
  have hf_meas : ∀ x t, Measurable (f x t) := fun x t ↦
    ((measurable_inner_action hrun t _).pow_const 2).div_const 2
  have hf_nonneg : ∀ x t h, 0 ≤ f x t h := fun x t h ↦ by positivity
  have hf_int : ∀ x t, Integrable (f x t) P₀ := fun x t ↦
    Integrable.of_bound (hf_meas x t).aestronglyMeasurable
      (R ^ 2 * ‖0 - mixtureParam w ε x‖ ^ 2 / 2) (Filter.Eventually.of_forall fun h ↦ by
        rw [Real.norm_of_nonneg (hf_nonneg _ _ _)]
        exact div_le_div_of_nonneg_right (inner_sq_le hR _ _) (by norm_num))
  refine (klDiv_finsetSum_smul_le hwd.sum_designWeight).trans ?_
  have hhist : ∀ θ, histLaw alg N θ =
      (trajMeasure alg (linearGaussianEnv 𝒳 θ)).map (history IT.action IT.feedback N) :=
    fun _ ↦ rfl
  have hterm : ∀ x, klDiv (histLaw alg N 0) (histLaw alg N (mixtureParam w ε x)) =
      ENNReal.ofReal (∑ t ∈ range (N + 1), ∫ h, f x t h ∂P₀) := fun x ↦ by
    rw [hhist, hhist]
    exact klDiv_map_history hrun (IT.isAlgEnvSeq_trajMeasure _ _) hR N
  simp_rw [hterm]
  calc ∑ x ∈ w.support, (designWeight w x : ℝ≥0∞) *
        ENNReal.ofReal (∑ t ∈ range (N + 1), ∫ h, f x t h ∂P₀)
      = ENNReal.ofReal (∑ x ∈ w.support, w x * ∑ t ∈ range (N + 1), ∫ h, f x t h ∂P₀) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun x _ ↦ mul_nonneg (hwd.nonneg x)
          (sum_nonneg fun t _ ↦ integral_nonneg (hf_nonneg x t))]
        refine sum_congr rfl fun x _ ↦ ?_
        rw [ENNReal.ofReal_mul (hwd.nonneg x)]
        rfl
    _ ≤ ENNReal.ofReal ((N + 1) * (9 * ε ^ 2 / (2 * Fintype.card ι))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ∑ x ∈ w.support, w x * ∑ t ∈ range (N + 1), ∫ h, f x t h ∂P₀
            = ∑ t ∈ range (N + 1), ∫ h, ∑ x ∈ w.support, w x * f x t h ∂P₀ := by
              simp_rw [mul_sum]
              rw [sum_comm]
              refine sum_congr rfl fun t _ ↦ ?_
              rw [integral_finsetSum _ fun x _ ↦ (hf_int x t).const_mul _]
              exact sum_congr rfl fun x _ ↦ (integral_const_mul _ _).symm
          _ ≤ ∑ t ∈ range (N + 1), ∫ _, 9 * ε ^ 2 / (2 * Fintype.card ι) ∂P₀ := by
              refine sum_le_sum fun t _ ↦ integral_mono_of_nonneg
                (Filter.Eventually.of_forall fun h ↦ sum_nonneg fun x _ ↦
                  mul_nonneg (hwd.nonneg x) (hf_nonneg x t h))
                (integrable_const _) (Filter.Eventually.of_forall fun h ↦ ?_)
              have hle := hw.sum_mul_inner_mixtureParam_sq_le ε (IT.action t h).2
              calc ∑ x ∈ w.support, w x * f x t h
                  = (∑ x ∈ w.support, w x *
                      ⟪((IT.action t h : 𝒳) : EuclideanSpace ℝ ι), mixtureParam w ε x⟫ ^ 2) /
                        2 := by
                    rw [sum_div]
                    refine sum_congr rfl fun x _ ↦ ?_
                    simp only [hf, zero_sub, inner_neg_right, neg_sq]
                    ring
                _ ≤ (9 * ε ^ 2 / Fintype.card ι) / 2 := by gcongr
                _ = 9 * ε ^ 2 / (2 * Fintype.card ι) := by ring
          _ = (N + 1) * (9 * ε ^ 2 / (2 * Fintype.card ι)) := by simp

/-- **Lower bound for the mixture testing problem** (blueprint `lem:test_lower`,
Bretagnolle–Huber form): for every algorithm, horizon `N` and measurable set `E` of histories,
if `P₀(E) ≤ α` and `P_{θ⁽ˣ⁾}(Eᶜ) ≤ β` for every support point `x`, then
`½ exp (-(N + 1) 9 ε² / (2 d)) ≤ α + β`. -/
theorem IsGOptimalDesign.exp_neg_le_of_mixture [Nonempty ι] (hw : IsGOptimalDesign 𝒳 w) {R : ℝ}
    (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) (ε : ℝ) {E : Set (Iic N → 𝒳 × ℝ)} (hE : MeasurableSet E)
    {α β : ℝ} (hβ0 : 0 ≤ β) (hα : (histLaw alg N 0).real E ≤ α)
    (hβ : ∀ x ∈ w.support, (histLaw alg N (mixtureParam w ε x)).real Eᶜ ≤ β) :
    1 / 2 * exp (-((N + 1) * (9 * ε ^ 2 / (2 * Fintype.card ι)))) ≤ α + β := by
  have hmix := hw.isDesign.isProbabilityMeasure_mixtureHistLaw alg N ε
  have hkl := hw.klDiv_histLaw_zero_mixtureHistLaw_le alg N hR ε
  have hne : klDiv (histLaw alg N 0) (mixtureHistLaw alg N w ε) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  have hbh := bretagnolle_huber (μ := histLaw alg N 0) (ν := mixtureHistLaw alg N w ε) hE hne
  have hC : 0 ≤ (N + 1) * (9 * ε ^ 2 / (2 * Fintype.card ι)) := by positivity
  have h1 : exp (-((N + 1) * (9 * ε ^ 2 / (2 * Fintype.card ι)))) ≤
      exp (-(klDiv (histLaw alg N 0) (mixtureHistLaw alg N w ε)).toReal) :=
    exp_le_exp.2 (neg_le_neg (ENNReal.toReal_le_of_le_ofReal hC hkl))
  have h2 : (mixtureHistLaw alg N w ε).real Eᶜ ≤ β := by
    rw [measureReal_def]
    refine ENNReal.toReal_le_of_le_ofReal hβ0 ?_
    unfold mixtureHistLaw
    rw [Measure.finsetSum_apply]
    calc ∑ x ∈ w.support, ((designWeight w x : ℝ≥0∞) • histLaw alg N (mixtureParam w ε x)) Eᶜ
        = ∑ x ∈ w.support, (designWeight w x : ℝ≥0∞) * histLaw alg N (mixtureParam w ε x) Eᶜ := by
          simp only [Measure.smul_apply, smul_eq_mul]
      _ ≤ ∑ x ∈ w.support, (designWeight w x : ℝ≥0∞) * ENNReal.ofReal β := by
          gcongr with x hx
          exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hβ0).2 (hβ x hx)
      _ = ENNReal.ofReal β := by
          rw [← sum_mul, ← ENNReal.ofNNReal_finsetSum, hw.isDesign.sum_designWeight,
            ENNReal.coe_one, one_mul]
  linarith

end kl

end COLT83
