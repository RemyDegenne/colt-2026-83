/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import COLT83.Mathlib.Probability.MultivariateGaussian
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Support functions and Gaussian widths

For a set `K` in a real inner product space `E`, the *support function* of `K` is
`supportFn K ξ = sup_{x ∈ K} ⟪x, ξ⟫`. For a nonempty set bounded by `R` it is `R`-Lipschitz,
convex and positively homogeneous.

For a measure `μ` on `E` (typically a centered Gaussian measure), the *Gaussian width* of `K`
for `μ` is `gaussianWidth K μ = ∫ ξ, supportFn K ξ ∂μ`. For the standard Gaussian measure this is
the usual Gaussian width (or mean width) of `K`.

## Main results

* `lipschitzWith_supportFn`, `convexOn_supportFn`, `supportFn_smul`, `supportFn_image`,
  `supportFn_add`: the basic properties of the support function.
* `integrable_supportFn`: the support function of a nonempty bounded set is integrable with
  respect to every measure with an integrable norm (Gaussian measures in particular).
* `gaussianWidth_mono`, `gaussianWidth_smul_set`, `gaussianWidth_map`, `gaussianWidth_add`:
  monotonicity, homogeneity, images by linear maps, Minkowski sums.
* `gaussianWidth_le_gaussianWidth_conv`: the Gaussian width of a compact set for `μ` is at most
  its width for `μ ∗ ν` when `ν` is centered (Jensen). For Gaussian measures this is the
  comparison by covariance domination: `N(0, S₁)` has a smaller width than `N(0, S₂)` when
  `S₁ ≤ S₂`.
-/

@[expose] public section

open MeasureTheory Set

open scoped RealInnerProductSpace Pointwise NNReal

section SupportFn

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The support function of a set `K`: `supportFn K ξ = sup_{x ∈ K} ⟪x, ξ⟫`. -/
noncomputable def supportFn (K : Set E) (ξ : E) : ℝ := ⨆ x : K, ⟪(x : E), ξ⟫

variable {K K' : Set E} {R : ℝ} {ξ : E}

lemma supportFn_eq_sSup (K : Set E) (ξ : E) : supportFn K ξ = sSup ((fun x ↦ ⟪x, ξ⟫) '' K) := by
  rw [supportFn, iSup, image_eq_range]

lemma supportFn_of_subsingleton [Subsingleton E] (K : Set E) (ξ : E) : supportFn K ξ = 0 := by
  simp [supportFn, Subsingleton.elim ξ 0, Real.iSup_const_zero]

lemma bddAbove_range_inner (hK : ∀ x ∈ K, ‖x‖ ≤ R) (ξ : E) :
    BddAbove (range fun x : K ↦ ⟪(x : E), ξ⟫) := by
  refine ⟨R * ‖ξ‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hK x x.2) (norm_nonneg _))

lemma inner_le_supportFn (hK : ∀ x ∈ K, ‖x‖ ≤ R) {x : E} (hx : x ∈ K) (ξ : E) :
    ⟪x, ξ⟫ ≤ supportFn K ξ :=
  le_ciSup (bddAbove_range_inner hK ξ) ⟨x, hx⟩

lemma supportFn_le (hne : K.Nonempty) {c : ℝ} (h : ∀ x ∈ K, ⟪x, ξ⟫ ≤ c) : supportFn K ξ ≤ c := by
  have : Nonempty K := hne.to_subtype
  exact ciSup_le fun x ↦ h x x.2

lemma supportFn_le_mul_norm (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (ξ : E) :
    supportFn K ξ ≤ R * ‖ξ‖ :=
  supportFn_le hne fun x hx ↦
    (real_inner_le_norm x ξ).trans (mul_le_mul_of_nonneg_right (hK x hx) (norm_nonneg _))

lemma neg_mul_norm_le_supportFn (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (ξ : E) :
    -(R * ‖ξ‖) ≤ supportFn K ξ := by
  obtain ⟨x, hx⟩ := hne
  refine le_trans ?_ (inner_le_supportFn hK hx ξ)
  have h1 := abs_real_inner_le_norm x ξ
  have h2 : ‖x‖ * ‖ξ‖ ≤ R * ‖ξ‖ := mul_le_mul_of_nonneg_right (hK x hx) (norm_nonneg _)
  linarith [(abs_le.1 h1).1]

lemma abs_supportFn_le (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (ξ : E) :
    |supportFn K ξ| ≤ R * ‖ξ‖ :=
  abs_le.2 ⟨neg_mul_norm_le_supportFn hne hK ξ, supportFn_le_mul_norm hne hK ξ⟩

lemma supportFn_sub_le (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (ξ ξ' : E) :
    supportFn K ξ - supportFn K ξ' ≤ R * ‖ξ - ξ'‖ := by
  rw [sub_le_iff_le_add']
  refine supportFn_le hne fun x hx ↦ ?_
  calc ⟪x, ξ⟫ = ⟪x, ξ'⟫ + ⟪x, ξ - ξ'⟫ := by rw [← inner_add_right, add_sub_cancel]
    _ ≤ supportFn K ξ' + R * ‖ξ - ξ'‖ :=
      add_le_add (inner_le_supportFn hK hx ξ') ((real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hK x hx) (norm_nonneg _)))

omit [InnerProductSpace ℝ E] in
lemma nonneg_of_norm_le (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) : 0 ≤ R :=
  hne.elim fun x hx ↦ (norm_nonneg x).trans (hK x hx)

lemma lipschitzWith_supportFn (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) :
    LipschitzWith R.toNNReal (supportFn K) := by
  refine LipschitzWith.of_dist_le_mul fun ξ ξ' ↦ ?_
  rw [Real.dist_eq, Real.coe_toNNReal R (nonneg_of_norm_le hne hK), dist_eq_norm]
  refine abs_sub_le_iff.2 ⟨supportFn_sub_le hne hK ξ ξ', ?_⟩
  simpa [norm_sub_rev] using supportFn_sub_le hne hK ξ' ξ

lemma continuous_supportFn (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) :
    Continuous (supportFn K) :=
  (lipschitzWith_supportFn hne hK).continuous

lemma supportFn_add_le (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (ξ ξ' : E) :
    supportFn K (ξ + ξ') ≤ supportFn K ξ + supportFn K ξ' :=
  supportFn_le hne fun x hx ↦ by
    rw [inner_add_right]
    exact add_le_add (inner_le_supportFn hK hx ξ) (inner_le_supportFn hK hx ξ')

/-- The support function is positively homogeneous (this holds for every set `K`, by the
convention `sSup ∅ = 0` of `ℝ`). -/
lemma supportFn_smul (K : Set E) {c : ℝ} (hc : 0 ≤ c) (ξ : E) :
    supportFn K (c • ξ) = c * supportFn K ξ := by
  simp only [supportFn, inner_smul_right]
  rw [Real.mul_iSup_of_nonneg hc]

lemma convexOn_supportFn (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) :
    ConvexOn ℝ univ (supportFn K) := by
  refine ⟨convex_univ, fun ξ _ ξ' _ a b ha hb _ ↦ ?_⟩
  calc supportFn K (a • ξ + b • ξ') ≤ supportFn K (a • ξ) + supportFn K (b • ξ') :=
        supportFn_add_le hne hK _ _
    _ = a • supportFn K ξ + b • supportFn K ξ' := by
        rw [supportFn_smul K ha, supportFn_smul K hb, smul_eq_mul, smul_eq_mul]

/-- The support function of an image `L '' K` is the support function of `K` composed with the
adjoint `L'` of `L`. -/
lemma supportFn_image {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K : Set E) {L : E → F} {L' : F → E} (h : ∀ x ξ, ⟪L x, ξ⟫ = ⟪x, L' ξ⟫) (ξ : F) :
    supportFn (L '' K) ξ = supportFn K (L' ξ) := by
  rw [supportFn_eq_sSup, supportFn_eq_sSup, image_image]
  simp_rw [h]

lemma supportFn_neg_set (K : Set E) (ξ : E) : supportFn (-K) ξ = supportFn K (-ξ) := by
  rw [← image_neg_eq_neg]
  exact supportFn_image K (fun _ _ ↦ by rw [inner_neg_left, inner_neg_right]) ξ

lemma supportFn_smul_set (K : Set E) {c : ℝ} (hc : 0 ≤ c) (ξ : E) :
    supportFn (c • K) ξ = c * supportFn K ξ := by
  rw [← image_smul, supportFn_image K (L' := fun ξ ↦ c • ξ) (fun _ _ ↦ by
    simp [inner_smul_left, inner_smul_right]), supportFn_smul K hc]

lemma supportFn_mono (hne : K.Nonempty) (hK' : ∀ x ∈ K', ‖x‖ ≤ R) (hsub : K ⊆ K') (ξ : E) :
    supportFn K ξ ≤ supportFn K' ξ :=
  supportFn_le hne fun _ hx ↦ inner_le_supportFn hK' (hsub hx) ξ

/-- The support function of a Minkowski sum is the sum of the support functions. -/
lemma supportFn_add {R' : ℝ} (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (hne' : K'.Nonempty)
    (hK' : ∀ x ∈ K', ‖x‖ ≤ R') (ξ : E) :
    supportFn (K + K') ξ = supportFn K ξ + supportFn K' ξ := by
  have hKK' : ∀ z ∈ K + K', ‖z‖ ≤ R + R' := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact (norm_add_le _ _).trans (add_le_add (hK x hx) (hK' y hy))
  refine le_antisymm (supportFn_le (hne.add hne') ?_) ?_
  · rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [inner_add_left]
    exact add_le_add (inner_le_supportFn hK hx ξ) (inner_le_supportFn hK' hy ξ)
  · have h : supportFn K' ξ ≤ supportFn (K + K') ξ - supportFn K ξ := by
      refine supportFn_le hne' fun y hy ↦ ?_
      rw [le_sub_comm]
      refine supportFn_le hne fun x hx ↦ ?_
      rw [le_sub_iff_add_le, ← inner_add_left]
      exact inner_le_supportFn hKK' (add_mem_add hx hy) ξ
    linarith

/-- On a compact set, the support function is attained. -/
lemma exists_supportFn_eq_inner (hK : IsCompact K) (hne : K.Nonempty) (ξ : E) :
    ∃ x ∈ K, supportFn K ξ = ⟪x, ξ⟫ := by
  have hc : Continuous fun x : E ↦ ⟪x, ξ⟫ := continuous_id.inner continuous_const
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne hc.continuousOn
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  exact ⟨x, hx, le_antisymm (supportFn_le hne fun y hy ↦ hmax hy) (inner_le_supportFn hR hx ξ)⟩

section finite

variable {ι : Type*} [Finite ι] [Nonempty ι] {y : ι → E} {σ : ℝ≥0}

lemma abs_ciSup_inner_le (hσ : ∀ i, ‖y i‖ ≤ σ) (v : E) :
    |⨆ i, ⟪y i, v⟫| ≤ σ * ‖v‖ := by
  have hb : ∀ i, |⟪y i, v⟫| ≤ σ * ‖v‖ := fun i ↦
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hσ i) (norm_nonneg _))
  refine abs_le.2 ⟨?_, ciSup_le fun i ↦ (le_abs_self _).trans (hb i)⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (neg_le.2 ((neg_le_abs _).trans (hb i))).trans
    (le_ciSup (Finite.bddAbove_range fun i ↦ ⟪y i, v⟫) i)

end finite

end SupportFn

namespace ProbabilityTheory

section GaussianWidth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {mE : MeasurableSpace E}
  [OpensMeasurableSpace E] {μ ν : Measure E} {K K' : Set E} {R : ℝ}

lemma measurable_ciSup_inner {ι : Type*} [Finite ι] (y : ι → E) :
    Measurable fun v : E ↦ ⨆ i, ⟪y i, v⟫ :=
  Measurable.iSup fun _ ↦ (continuous_const.inner continuous_id).measurable

lemma measurable_ciSup_apply {κ : Type*} [Finite κ] :
    Measurable fun x : EuclideanSpace ℝ κ ↦ ⨆ k, x k :=
  Measurable.iSup fun k ↦ (PiLp.proj (𝕜 := ℝ) 2 (fun _ : κ ↦ ℝ) k).continuous.measurable

/-- Gaussian width of the set `K` with respect to the measure `μ`:
`∫ ξ, sup_{x ∈ K} ⟪x, ξ⟫ ∂μ`. -/
noncomputable def gaussianWidth (K : Set E) (μ : Measure E) : ℝ := ∫ ξ, supportFn K ξ ∂μ

/-- The support function of a nonempty bounded set is integrable for every measure with an
integrable norm. -/
lemma integrable_supportFn (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R)
    (hμ : Integrable (fun ξ ↦ ‖ξ‖) μ) : Integrable (supportFn K) μ :=
  (hμ.const_mul R).mono' (continuous_supportFn hne hK).aestronglyMeasurable
    (ae_of_all _ fun ξ ↦ by simpa [Real.norm_eq_abs] using abs_supportFn_le hne hK ξ)

lemma integrable_supportFn_of_isGaussian [BorelSpace E] [CompleteSpace E]
    [SecondCountableTopology E] [IsGaussian μ] (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) :
    Integrable (supportFn K) μ :=
  integrable_supportFn hne hK (IsGaussian.integrable_id (μ := μ)).norm

lemma abs_gaussianWidth_le (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R)
    (hμ : Integrable (fun ξ ↦ ‖ξ‖) μ) :
    |gaussianWidth K μ| ≤ R * ∫ ξ, ‖ξ‖ ∂μ := by
  rw [gaussianWidth, ← integral_const_mul]
  exact abs_integral_le_integral_abs.trans (integral_mono (integrable_supportFn hne hK hμ).abs
    (hμ.const_mul R) fun ξ ↦ abs_supportFn_le hne hK ξ)

omit [OpensMeasurableSpace E] in
lemma gaussianWidth_of_subsingleton [Subsingleton E] (K : Set E) (μ : Measure E) :
    gaussianWidth K μ = 0 := by
  simp [gaussianWidth, supportFn_of_subsingleton]

lemma gaussianWidth_mono (hne : K.Nonempty) (hK' : ∀ x ∈ K', ‖x‖ ≤ R) (hsub : K ⊆ K')
    (hμ : Integrable (fun ξ ↦ ‖ξ‖) μ) :
    gaussianWidth K μ ≤ gaussianWidth K' μ :=
  integral_mono (integrable_supportFn hne (fun x hx ↦ hK' x (hsub hx)) hμ)
    (integrable_supportFn (hne.mono hsub) hK' hμ) (supportFn_mono hne hK' hsub)

omit [OpensMeasurableSpace E] in
lemma gaussianWidth_smul_set (K : Set E) {c : ℝ} (hc : 0 ≤ c) (μ : Measure E) :
    gaussianWidth (c • K) μ = c * gaussianWidth K μ := by
  simp only [gaussianWidth, supportFn_smul_set K hc]
  exact integral_const_mul c _

lemma gaussianWidth_neg_set [BorelSpace E] (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R)
    (μ : Measure E) :
    gaussianWidth (-K) μ = gaussianWidth K (μ.map fun ξ ↦ -ξ) := by
  rw [gaussianWidth, gaussianWidth, integral_map continuous_neg.measurable.aemeasurable
    (continuous_supportFn hne hK).aestronglyMeasurable]
  simp only [supportFn_neg_set]

lemma gaussianWidth_map_smul [BorelSpace E] (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R)
    {c : ℝ} (hc : 0 ≤ c) (μ : Measure E) :
    gaussianWidth K (μ.map fun ξ ↦ c • ξ) = c * gaussianWidth K μ := by
  rw [gaussianWidth, gaussianWidth, integral_map (continuous_const_smul c).measurable.aemeasurable
    (continuous_supportFn hne hK).aestronglyMeasurable, ← integral_const_mul]
  simp only [supportFn_smul K hc]

/-- The Gaussian width of `K` for the image measure `μ.map L` is the width of the image of `K`
by the adjoint of `L` for `μ`. -/
lemma gaussianWidth_map [CompleteSpace E] {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [CompleteSpace F] {mF : MeasurableSpace F} [BorelSpace F]
    {K : Set F} (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (L : E →L[ℝ] F) (μ : Measure E) :
    gaussianWidth K (μ.map L) = gaussianWidth (ContinuousLinearMap.adjoint L '' K) μ := by
  rw [gaussianWidth, gaussianWidth, integral_map L.continuous.measurable.aemeasurable
    (continuous_supportFn hne hK).aestronglyMeasurable]
  congr 1
  ext ξ
  exact (supportFn_image K (fun x ξ ↦ ContinuousLinearMap.adjoint_inner_left L ξ x) ξ).symm

lemma inner_integral_le_gaussianWidth [CompleteSpace E] (hK : ∀ x ∈ K, ‖x‖ ≤ R) {x : E} (hx : x ∈ K)
    (hμ : Integrable id μ) :
    ⟪x, ∫ ξ, ξ ∂μ⟫ ≤ gaussianWidth K μ := by
  have h := integral_inner (𝕜 := ℝ) hμ x
  simp only [id] at h
  rw [← h]
  exact integral_mono (hμ.const_inner x) (integrable_supportFn ⟨x, hx⟩ hK hμ.norm)
    fun ξ ↦ inner_le_supportFn hK hx ξ

/-- The Gaussian width of a nonempty bounded set for a centered measure is nonnegative. -/
lemma gaussianWidth_nonneg_of_integral_eq_zero [CompleteSpace E] (hne : K.Nonempty)
    (hK : ∀ x ∈ K, ‖x‖ ≤ R) (hμ : Integrable id μ) (h0 : ∫ ξ, ξ ∂μ = 0) :
    0 ≤ gaussianWidth K μ := by
  obtain ⟨x, hx⟩ := hne
  have := inner_integral_le_gaussianWidth hK hx hμ
  rwa [h0, inner_zero_right] at this

omit [OpensMeasurableSpace E] in
lemma gaussianWidth_nonneg_of_zero_mem (hK : ∀ x ∈ K, ‖x‖ ≤ R) (h0 : (0 : E) ∈ K) :
    0 ≤ gaussianWidth K μ :=
  integral_nonneg fun ξ ↦ by simpa using inner_le_supportFn hK h0 ξ

/-- The Gaussian width of a Minkowski sum is the sum of the Gaussian widths. -/
lemma gaussianWidth_add {R' : ℝ} (hne : K.Nonempty) (hK : ∀ x ∈ K, ‖x‖ ≤ R) (hne' : K'.Nonempty)
    (hK' : ∀ x ∈ K', ‖x‖ ≤ R') (hμ : Integrable (fun ξ ↦ ‖ξ‖) μ) :
    gaussianWidth (K + K') μ = gaussianWidth K μ + gaussianWidth K' μ := by
  simp_rw [gaussianWidth, supportFn_add hne hK hne' hK']
  exact integral_add (integrable_supportFn hne hK hμ) (integrable_supportFn hne' hK' hμ)

omit [InnerProductSpace ℝ E] in
lemma integrable_norm_conv [BorelSpace E] [SecondCountableTopology E] [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hμ : Integrable (fun ξ ↦ ‖ξ‖) μ) (hν : Integrable (fun ξ ↦ ‖ξ‖) ν) :
    Integrable (fun ξ ↦ ‖ξ‖) (μ ∗ ν) := by
  rw [Measure.conv, integrable_map_measure continuous_norm.aestronglyMeasurable (by fun_prop)]
  refine ((hμ.comp_fst ν).add (hν.comp_snd μ)).mono' (by fun_prop) (ae_of_all _ fun p ↦ ?_)
  simpa using norm_add_le p.1 p.2

/-- **Comparison by convolution.** For a compact set `K` and a centered probability measure `ν`,
the Gaussian width of `K` for `μ` is at most its width for `μ ∗ ν`: adding an independent
centered noise can only increase the expected supremum (Jensen's inequality). -/
lemma gaussianWidth_le_gaussianWidth_conv [BorelSpace E] [SecondCountableTopology E]
    [CompleteSpace E] [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hK : IsCompact K)
    (hne : K.Nonempty) (hμ : Integrable id μ) (hν : Integrable id ν) (h0 : ∫ ξ, ξ ∂ν = 0) :
    gaussianWidth K μ ≤ gaussianWidth K (μ ∗ ν) := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hint : Integrable (supportFn K) (μ ∗ ν) :=
    integrable_supportFn hne hR (integrable_norm_conv hμ.norm hν.norm)
  rw [gaussianWidth, gaussianWidth, integral_conv hint]
  have hprod : Integrable (fun p : E × E ↦ supportFn K (p.1 + p.2)) (μ.prod ν) := by
    have h := hint
    rwa [Measure.conv, integrable_map_measure hint.1 (by fun_prop)] at h
  refine integral_mono (integrable_supportFn hne hR hμ.norm) hprod.integral_prod_left fun a ↦ ?_
  obtain ⟨x, hx, hxa⟩ := exists_supportFn_eq_inner hK hne a
  have hb : Integrable (fun b ↦ supportFn K (a + b)) ν := by
    refine (((integrable_const ‖a‖).add hν.norm).const_mul R).mono'
      ((continuous_supportFn hne hR).comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun b ↦ ?_)
    simp only [Real.norm_eq_abs]
    exact (abs_supportFn_le hne hR _).trans
      (mul_le_mul_of_nonneg_left (norm_add_le _ _) (nonneg_of_norm_le hne hR))
  have hab : Integrable (fun b ↦ a + b) ν := (integrable_const a).add hν
  calc supportFn K a = ⟪x, a⟫ := hxa
    _ = ∫ b, ⟪x, a + b⟫ ∂ν := by
        rw [integral_inner (𝕜 := ℝ) hab, integral_add (integrable_const a) (g := fun b ↦ b) hν,
          integral_const, h0]
        simp
    _ ≤ ∫ b, supportFn K (a + b) ∂ν :=
        integral_mono (hab.const_inner x) hb fun b ↦ inner_le_supportFn hR hx _

end GaussianWidth

section Multivariate

open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Set (EuclideanSpace ℝ ι)}
  {S₁ S₂ : Matrix ι ι ℝ}

/-- **Comparison by covariance domination**: if `S₁ ≤ S₂` in the Loewner order, the Gaussian
width of a compact set for `N(0, S₁)` is at most its width for `N(0, S₂)`. -/
lemma gaussianWidth_multivariateGaussian_le (hK : IsCompact K) (hne : K.Nonempty)
    (hS₁ : S₁.PosSemidef) (h : S₁ ≤ S₂) :
    gaussianWidth K (multivariateGaussian 0 S₁) ≤ gaussianWidth K (multivariateGaussian 0 S₂) := by
  have h2 : multivariateGaussian 0 S₂ =
      multivariateGaussian 0 S₁ ∗ multivariateGaussian 0 (S₂ - S₁) := by
    rw [multivariateGaussian_conv hS₁ (Matrix.le_iff.1 h)]
    simp
  rw [h2]
  exact gaussianWidth_le_gaussianWidth_conv hK hne IsGaussian.integrable_id
    IsGaussian.integrable_id (by simp)

end Multivariate

end ProbabilityTheory
