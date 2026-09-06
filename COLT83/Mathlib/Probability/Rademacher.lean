/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Integration
public import COLT83.Mathlib.Probability.SubgaussianSquare

/-!
# Rademacher vectors

* `signMeasure`: the law `(δ₁ + δ₋₁) / 2` of a uniform random sign;
* `rademacherMeasure ι`: the law of a Rademacher vector in `ι → ℝ`, i.e. i.i.d. uniform signs;
* `hasSubgaussianMGF_sum_mul_rademacherMeasure`: the linear form `∑ i, ε i * θ i` is sub-Gaussian
  with constant `‖θ‖²` (Hoeffding's lemma coordinatewise);
* `integral_sq_sum_mul_rademacherMeasure`: its second moment is `‖θ‖²`;
* `hasSubexponentialMGF_sq_sum_mul_sub_rademacherMeasure`: its centered square
  `(∑ i, ε i * θ i)² - ‖θ‖²` is sub-exponential with parameters `(16 ‖θ‖⁴, 4 ‖θ‖²)`.
-/

@[expose] public section

open MeasureTheory Real Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

section Sign

/-- The law of a uniform random sign: `(δ₁ + δ₋₁) / 2`. -/
noncomputable def signMeasure : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac 1 + Measure.dirac (-1))

instance : IsProbabilityMeasure signMeasure := by
  constructor
  rw [signMeasure, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
    one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

lemma integrable_signMeasure {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) :
    Integrable f signMeasure := by
  rw [signMeasure]
  exact ((integrable_dirac (by simp)).add_measure (integrable_dirac (by simp))).smul_measure
    (by simp)

lemma integral_signMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) :
    ∫ x, f x ∂signMeasure = (2⁻¹ : ℝ) • (f 1 + f (-1)) := by
  rw [signMeasure, integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp)), integral_dirac, integral_dirac]
  simp

lemma integral_signMeasure_real (f : ℝ → ℝ) : ∫ x, f x ∂signMeasure = (f 1 + f (-1)) / 2 := by
  rw [integral_signMeasure, smul_eq_mul]
  ring

lemma integral_id_signMeasure : ∫ x, x ∂signMeasure = 0 := by
  rw [integral_signMeasure_real]
  norm_num

lemma integral_sq_signMeasure : ∫ x, x ^ 2 ∂signMeasure = 1 := by
  rw [integral_signMeasure_real]
  norm_num

lemma ae_signMeasure_mem_Icc : ∀ᵐ x ∂signMeasure, x ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [ae_iff, signMeasure, Measure.smul_apply, Measure.add_apply, Measure.dirac_apply,
    Measure.dirac_apply]
  simp

end Sign

section Rademacher

variable {ι : Type*} [Fintype ι]

/-- The law of a Rademacher vector in `ι → ℝ`: i.i.d. uniform signs. -/
noncomputable def rademacherMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi fun _ ↦ signMeasure

instance : IsProbabilityMeasure (rademacherMeasure ι) := by
  unfold rademacherMeasure
  infer_instance

lemma iIndepFun_eval_rademacherMeasure :
    iIndepFun (fun i (ε : ι → ℝ) ↦ ε i) (rademacherMeasure ι) :=
  iIndepFun_pi (X := fun _ ↦ id) fun _ ↦ aemeasurable_id

lemma map_eval_rademacherMeasure (i : ι) :
    (rademacherMeasure ι).map (fun ε ↦ ε i) = signMeasure :=
  (measurePreserving_eval (fun _ : ι ↦ signMeasure) i).map_eq

lemma ae_rademacherMeasure_mem_Icc (i : ι) :
    ∀ᵐ ε ∂rademacherMeasure ι, ε i ∈ Set.Icc (-1 : ℝ) 1 := by
  refine ae_of_ae_map (measurable_pi_apply i).aemeasurable ?_
  rw [map_eval_rademacherMeasure]
  exact ae_signMeasure_mem_Icc

lemma integral_eval_rademacherMeasure (i : ι) : ∫ ε, ε i ∂rademacherMeasure ι = 0 := by
  rw [← integral_id_signMeasure, ← map_eval_rademacherMeasure i,
    integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]

lemma integral_eval_sq_rademacherMeasure (i : ι) : ∫ ε, ε i ^ 2 ∂rademacherMeasure ι = 1 := by
  rw [← integral_sq_signMeasure, ← map_eval_rademacherMeasure i,
    integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]

lemma integral_eval_mul_eval_rademacherMeasure [DecidableEq ι] (i j : ι) :
    ∫ ε, ε i * ε j ∂rademacherMeasure ι = if i = j then 1 else 0 := by
  split_ifs with hij
  · subst hij
    simpa only [sq] using integral_eval_sq_rademacherMeasure i
  · have hind : IndepFun (fun ε : ι → ℝ ↦ ε i) (fun ε ↦ ε j) (rademacherMeasure ι) :=
      iIndepFun_eval_rademacherMeasure.indepFun hij
    have := IndepFun.integral_mul_eq_mul_integral hind
      (measurable_pi_apply i).aestronglyMeasurable (measurable_pi_apply j).aestronglyMeasurable
    simp only [Pi.mul_apply] at this
    rw [this, integral_eval_rademacherMeasure, zero_mul]

lemma integrable_eval_mul_eval_rademacherMeasure (i j : ι) (θ : ι → ℝ) :
    Integrable (fun ε : ι → ℝ ↦ ε i * θ i * (ε j * θ j)) (rademacherMeasure ι) := by
  refine Integrable.of_bound (by fun_prop) (|θ i| * |θ j|) ?_
  filter_upwards [ae_rademacherMeasure_mem_Icc i, ae_rademacherMeasure_mem_Icc j] with ε hi hj
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
  have h1 : |ε i| ≤ 1 := abs_le.2 hi
  have h2 : |ε j| ≤ 1 := abs_le.2 hj
  calc |ε i| * |θ i| * (|ε j| * |θ j|) ≤ 1 * |θ i| * (1 * |θ j|) := by gcongr
    _ = |θ i| * |θ j| := by ring

lemma integrable_eval_rademacherMeasure (i : ι) :
    Integrable (fun ε : ι → ℝ ↦ ε i) (rademacherMeasure ι) := by
  have h := integrable_signMeasure (id : ℝ → ℝ)
  rw [← map_eval_rademacherMeasure i] at h
  exact (integrable_map_measure (f := fun ε : ι → ℝ ↦ ε i) (μ := rademacherMeasure ι)
    measurable_id.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).1 h

lemma integrable_eval_mul_const_rademacherMeasure (i : ι) (a : ℝ) :
    Integrable (fun ε : ι → ℝ ↦ ε i * a) (rademacherMeasure ι) :=
  (integrable_eval_rademacherMeasure i).mul_const a

/-- A Rademacher linear form is centered. -/
lemma integral_sum_mul_rademacherMeasure (θ : ι → ℝ) :
    ∫ ε, ∑ i, ε i * θ i ∂rademacherMeasure ι = 0 := by
  rw [integral_finsetSum _ fun i _ ↦ integrable_eval_mul_const_rademacherMeasure i (θ i)]
  simp_rw [integral_mul_const, integral_eval_rademacherMeasure, zero_mul, Finset.sum_const_zero]

/-- Second moment of a Rademacher linear form: `E[(∑ i, ε i * θ i)²] = ∑ i, θ i ^ 2`. -/
lemma integral_sq_sum_mul_rademacherMeasure (θ : ι → ℝ) :
    ∫ ε, (∑ i, ε i * θ i) ^ 2 ∂rademacherMeasure ι = ∑ i, θ i ^ 2 := by
  classical
  have hint := integrable_eval_mul_eval_rademacherMeasure (ι := ι)
  simp_rw [sq, Finset.sum_mul_sum]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hint i j θ]
  simp_rw [integral_finsetSum _ fun j _ ↦ hint _ j θ]
  have h : ∀ i j, ∫ ε, ε i * θ i * (ε j * θ j) ∂rademacherMeasure ι
      = θ i * θ j * (if i = j then 1 else 0) := by
    intro i j
    rw [← integral_eval_mul_eval_rademacherMeasure, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ε ↦ ?_)
    ring
  simp_rw [h]
  simp [mul_ite, Finset.sum_ite_eq]

/-- **Rademacher linear forms are sub-Gaussian**: `∑ i, ε i * θ i` has a sub-Gaussian MGF with
constant `∑ i, ‖θ i‖₊ ^ 2`. -/
lemma hasSubgaussianMGF_sum_mul_rademacherMeasure (θ : ι → ℝ) :
    HasSubgaussianMGF (fun ε ↦ ∑ i, ε i * θ i) (∑ i, ‖θ i‖₊ ^ 2) (rademacherMeasure ι) := by
  have h_indep : iIndepFun (fun i (ε : ι → ℝ) ↦ ε i * θ i) (rademacherMeasure ι) :=
    iIndepFun_pi (X := fun i x ↦ x * θ i) fun i ↦ by fun_prop
  refine HasSubgaussianMGF.sum_of_iIndepFun h_indep (s := Finset.univ) fun i _ ↦ ?_
  have hI : HasSubgaussianMGF (fun x : ℝ ↦ x * θ i) ((‖|θ i| - -|θ i|‖₊ / 2) ^ 2) signMeasure := by
    refine hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (by fun_prop) ?_ ?_
    · filter_upwards [ae_signMeasure_mem_Icc] with x hx
      have : |x * θ i| ≤ |θ i| := by
        rw [abs_mul]
        calc |x| * |θ i| ≤ 1 * |θ i| := by
              gcongr
              exact abs_le.2 hx
          _ = |θ i| := one_mul _
      exact abs_le.1 this
    · rw [integral_mul_const, integral_id_signMeasure, zero_mul]
  have e : (‖|θ i| - -|θ i|‖₊ / 2 : ℝ≥0) = ‖θ i‖₊ := by
    apply NNReal.coe_injective
    push_cast
    rw [Real.norm_eq_abs, Real.norm_eq_abs, sub_neg_eq_add, abs_of_nonneg (by positivity)]
    ring
  rw [e, ← map_eval_rademacherMeasure i] at hI
  exact HasSubgaussianMGF.of_map (X := fun x : ℝ ↦ x * θ i) (Y := fun ε : ι → ℝ ↦ ε i)
    (μ := rademacherMeasure ι) (measurable_pi_apply i).aemeasurable (by exact hI)

/-- **Rademacher linear forms are sub-Gaussian**, Euclidean form: for `θ ∈ ℝ^d`,
`∑ i, ε i * θ i` has a sub-Gaussian MGF with constant `‖θ‖²`. -/
lemma hasSubgaussianMGF_sum_mul_rademacherMeasure' (θ : EuclideanSpace ℝ ι) :
    HasSubgaussianMGF (fun ε ↦ ∑ i, ε i * θ i) (‖θ‖₊ ^ 2) (rademacherMeasure ι) := by
  have := hasSubgaussianMGF_sum_mul_rademacherMeasure (fun i ↦ θ i)
  rwa [EuclideanSpace.nnnorm_eq, NNReal.sq_sqrt]

/-- **The centered square of a Rademacher linear form is sub-exponential**: for `θ ∈ ℝ^d` with
`r = ‖θ‖`, `(∑ i, ε i * θ i)² - r²` has sub-exponential parameters `(16 r⁴, 4 r²)`. -/
lemma hasSubexponentialMGF_sq_sum_mul_sub_rademacherMeasure (θ : EuclideanSpace ℝ ι) :
    HasSubexponentialMGF (fun ε ↦ (∑ i, ε i * θ i) ^ 2 - ‖θ‖ ^ 2) (16 * ‖θ‖ ^ 4) (4 * ‖θ‖ ^ 2)
      (rademacherMeasure ι) := by
  have h := (hasSubgaussianMGF_sum_mul_rademacherMeasure' θ).hasSubexponentialMGF_sq_sub (by
    rw [integral_sq_sum_mul_rademacherMeasure (fun i ↦ θ i), ← EuclideanSpace.real_norm_sq_eq]
    push_cast
    rfl)
  have e1 : ((‖θ‖₊ ^ 2 : ℝ≥0) : ℝ) = ‖θ‖ ^ 2 := by push_cast; rfl
  rw [e1] at h
  exact h.mono (le_of_eq (by ring)) le_rfl

lemma inner_toLp_eq_sum (ε : ι → ℝ) (θ : EuclideanSpace ℝ ι) :
    inner ℝ (WithLp.toLp 2 ε) θ = ∑ i, ε i * θ i := by
  simp [PiLp.inner_apply, mul_comm]

end Rademacher

end ProbabilityTheory

namespace ProbabilityTheory

section BoolSeed

/-- The uniform law on `Bool`. -/
noncomputable def uniformBool : Measure Bool :=
  (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure uniformBool := by
  constructor
  rw [uniformBool, Measure.smul_apply, Measure.add_apply, measure_univ, measure_univ, smul_eq_mul,
    one_add_one_eq_two, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The sign of a Boolean: `true ↦ 1`, `false ↦ -1`. -/
def signOf (b : Bool) : ℝ := if b then 1 else -1

lemma measurable_signOf : Measurable signOf := measurable_of_countable _

lemma uniformBool_map_signOf : uniformBool.map signOf = signMeasure := by
  rw [uniformBool, signMeasure, Measure.map_smul, Measure.map_add _ _ measurable_signOf,
    Measure.map_dirac' measurable_signOf, Measure.map_dirac' measurable_signOf]
  rfl

variable {ι : Type*} [Fintype ι]

/-- The law of a vector of i.i.d. uniform Booleans. -/
noncomputable def uniformBoolVec (ι : Type*) [Fintype ι] : Measure (ι → Bool) :=
  Measure.pi fun _ ↦ uniformBool

instance : IsProbabilityMeasure (uniformBoolVec ι) := by
  unfold uniformBoolVec
  infer_instance

/-- The sign vector of a Boolean vector. -/
def signVec (u : ι → Bool) : ι → ℝ := fun i ↦ signOf (u i)

omit [Fintype ι] in
lemma measurable_signVec : Measurable (signVec (ι := ι)) :=
  measurable_pi_lambda _ fun i ↦ measurable_signOf.comp (measurable_pi_apply i)

lemma uniformBoolVec_map_signVec : (uniformBoolVec ι).map signVec = rademacherMeasure ι := by
  unfold uniformBoolVec rademacherMeasure signVec
  rw [Measure.pi_map_pi (fun _ ↦ measurable_signOf.aemeasurable)]
  simp_rw [uniformBool_map_signOf]

/-- **The centered square of a Rademacher linear form is sub-exponential**, Boolean-seed form:
for `θ ∈ ℝ^d` with `r = ‖θ‖`, `(∑ i, signOf (u i) * θ i)² - r²` has sub-exponential parameters
`(16 r⁴, 4 r²)` under `uniformBoolVec ι`. -/
lemma hasSubexponentialMGF_sq_sum_signOf_mul_sub_uniformBoolVec (θ : EuclideanSpace ℝ ι) :
    HasSubexponentialMGF (fun u : ι → Bool ↦ (∑ i, signOf (u i) * θ i) ^ 2 - ‖θ‖ ^ 2)
      (16 * ‖θ‖ ^ 4) (4 * ‖θ‖ ^ 2) (uniformBoolVec ι) := by
  have h := hasSubexponentialMGF_sq_sum_mul_sub_rademacherMeasure θ
  rw [← uniformBoolVec_map_signVec] at h
  exact HasSubexponentialMGF.of_map (X := fun ε : ι → ℝ ↦ (∑ i, ε i * θ i) ^ 2 - ‖θ‖ ^ 2)
    (Y := signVec) (μ := uniformBoolVec ι) measurable_signVec.aemeasurable (by exact h)

end BoolSeed

end ProbabilityTheory
