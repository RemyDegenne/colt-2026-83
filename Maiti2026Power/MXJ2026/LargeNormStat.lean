/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.MXJ2026.RademacherEst
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The large-norm estimator (norm estimation, Algorithm 3 of the paper)

The large-norm estimator plays each basis vector `n` times and estimates `‖θ‖²` by
`‖θ̂‖² - d / n`, where `θ̂ = θ + Δ` and `Δ_i` is the mean of the `n` noises observed at `e_i`.
On the product space `lnNoise ι n` of the `d × n` standard Gaussian noises,
`‖θ̂‖² - ‖θ‖² = 2 ⟪θ, Δ⟫ + (‖Δ‖² - d / n)`: the first term is `N(0, 4 ‖θ‖² / n)` and the second
is `(1/n) (‖g‖² - d)` for a standard Gaussian vector `g`, which is sub-exponential.

With `n = ⌈48 log(4/δ) / ε²⌉` and `‖θ‖ ≥ √d`, the estimate `√(max (‖θ̂‖² - d/n) 0)` is within `ε`
of `‖θ‖` with probability at least `1 - δ/2`.

Blueprint: `def:large_norm_algorithm`, `lem:large_norm_decomposition`, `thm:large_norm_guarantee`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace ProbabilityTheory

/-- Two-sided sub-Gaussian tail bound, real form. -/
lemma HasSubgaussianMGF.measureReal_abs_ge_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * exp (-ε ^ 2 / (2 * c)) := by
  have h1 := h.measure_ge_le hε
  have h2 := h.neg.measure_ge_le hε
  have hsub : {ω | ε ≤ |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | ε ≤ (-X) ω} := fun ω hω ↦ by
    rcases le_abs.1 (show ε ≤ |X ω| from hω) with h | h
    · exact Or.inl h
    · exact Or.inr h
  calc μ.real {ω | ε ≤ |X ω|}
      ≤ μ.real ({ω | ε ≤ X ω} ∪ {ω | ε ≤ (-X) ω}) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ (-X) ω} := measureReal_union_le _ _
    _ ≤ exp (-ε ^ 2 / (2 * c)) + exp (-ε ^ 2 / (2 * c)) := add_le_add h1 h2
    _ = 2 * exp (-ε ^ 2 / (2 * c)) := by ring

/-- `exp (-(L/2)) ≤ 1/2` when `L ≥ log 4`. -/
lemma exp_neg_half_le_half {L : ℝ} (hL : log 4 ≤ L) : exp (-(L / 2)) ≤ 1 / 2 := by
  have h5 : exp (-(L / 2)) ≤ exp (-(log 4 / 2)) := exp_le_exp.2 (by linarith)
  have h6 : exp (-(log 4 / 2)) = 1 / 2 := by
    rw [exp_neg, show log 4 / 2 = log 2 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring, Real.exp_log (by norm_num)]
    norm_num
  linarith

lemma one_lt_log_four : 1 < log 4 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

end ProbabilityTheory

namespace Maiti2026Power

variable {ι : Type*} [Fintype ι]

/-- The noises of the basis design: `n` standard Gaussians for each of the `d` basis vectors. -/
noncomputable def lnNoise (ι : Type*) [Fintype ι] (n : ℕ) : Measure (ι → Fin n → ℝ) :=
  Measure.pi fun _ ↦ Measure.pi fun _ ↦ gaussianReal 0 1

instance (n : ℕ) : IsProbabilityMeasure (lnNoise ι n) := by
  unfold lnNoise
  infer_instance

/-- The estimation error `Δ = θ̂ - θ`: coordinate `i` is the mean of the `n` noises at `e_i`. -/
noncomputable def lnDelta (n : ℕ) (e : ι → Fin n → ℝ) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 fun i ↦ (∑ ℓ, e i ℓ) / n

omit [Fintype ι] in
lemma measurable_lnDelta [Finite ι] (n : ℕ) : Measurable (lnDelta (ι := ι) n) := by
  have := Fintype.ofFinite ι
  exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_lambda _ fun i ↦
    (Finset.measurable_sum _ fun ℓ _ ↦
      (measurable_pi_apply ℓ).comp (measurable_pi_apply i)).div_const _)

/-- The squared-norm estimate `‖θ + Δ‖² - d / n`. -/
noncomputable def lnR (θ : EuclideanSpace ℝ ι) (n : ℕ) (e : ι → Fin n → ℝ) : ℝ :=
  ‖θ + lnDelta n e‖ ^ 2 - Fintype.card ι / n

/-- The norm estimate `√(max R̂ 0)`. -/
noncomputable def lnEst (θ : EuclideanSpace ℝ ι) (n : ℕ) (e : ι → Fin n → ℝ) : ℝ :=
  √(max (lnR θ n e) 0)

lemma measurable_lnR (θ : EuclideanSpace ℝ ι) (n : ℕ) : Measurable (lnR θ n) :=
  ((continuous_norm.measurable.comp (measurable_const.add (measurable_lnDelta n))).pow_const 2
    ).sub_const _

lemma measurable_lnEst (θ : EuclideanSpace ℝ ι) (n : ℕ) : Measurable (lnEst θ n) :=
  Real.continuous_sqrt.measurable.comp ((measurable_lnR θ n).max measurable_const)

/-- Decomposition of the estimate (blueprint `lem:large_norm_decomposition`). -/
lemma lnR_sub_eq (θ : EuclideanSpace ℝ ι) (n : ℕ) (e : ι → Fin n → ℝ) :
    lnR θ n e - ‖θ‖ ^ 2
      = 2 * inner ℝ θ (lnDelta n e) + (‖lnDelta n e‖ ^ 2 - Fintype.card ι / n) := by
  rw [lnR, norm_add_sq_real]
  ring

variable (θ : EuclideanSpace ℝ ι) {n : ℕ}

/-- The Gaussian term: `2 ⟪θ, Δ⟫ ~ N(0, 4 ‖θ‖² / n)`. -/
lemma hasLaw_two_mul_inner_lnDelta (hn : 0 < n) :
    HasLaw (fun e : ι → Fin n → ℝ ↦ 2 * inner ℝ θ (lnDelta n e))
      (gaussianReal 0 (4 * ‖θ‖₊ ^ 2 / n)) (lnNoise ι n) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have h_indep : iIndepFun (fun i (e : ι → Fin n → ℝ) ↦ 0 + (2 * θ i / n) * ∑ ℓ, e i ℓ)
      (lnNoise ι n) :=
    iIndepFun_pi (X := fun i (v : Fin n → ℝ) ↦ 0 + (2 * θ i / n) * ∑ ℓ, v ℓ) fun i ↦ by fun_prop
  have hX : ∀ i, HasLaw (fun e : ι → Fin n → ℝ ↦ 0 + (2 * θ i / n) * ∑ ℓ, e i ℓ)
      (gaussianReal 0 (‖2 * θ i / n‖₊ ^ 2 * n)) (lnNoise ι n) := by
    intro i
    have hmap : (lnNoise ι n).map (fun e : ι → Fin n → ℝ ↦ e i)
        = Measure.pi fun _ : Fin n ↦ gaussianReal 0 1 :=
      (measurePreserving_eval (fun _ : ι ↦ Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) i).map_eq
    have h := HasLaw.comp (hasLaw_const_add_const_mul_sum_pi_gaussianReal 0 (2 * θ i / n))
      ⟨(measurable_pi_apply i).aemeasurable, hmap⟩
    exact h
  have hsum := hasLaw_finset_sum_gaussianReal h_indep hX Finset.univ
  simp only [Finset.sum_const, Finset.card_univ, smul_zero] at hsum
  have hv : ∑ i, ‖2 * θ i / n‖₊ ^ 2 * (n : ℝ≥0) = 4 * ‖θ‖₊ ^ 2 / n := by
    apply NNReal.eq
    push_cast
    simp only [Real.norm_eq_abs, sq_abs]
    rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    field_simp
    ring
  have h2 : HasLaw (∑ i, fun e : ι → Fin n → ℝ ↦ 0 + (2 * θ i / n) * ∑ ℓ, e i ℓ)
      (gaussianReal 0 (4 * ‖θ‖₊ ^ 2 / n)) (lnNoise ι n) :=
    ⟨hsum.aemeasurable, hsum.map_eq.trans (congrArg (gaussianReal _) hv)⟩
  refine h2.congr (ae_of_all _ fun e ↦ ?_)
  simp only [Finset.sum_apply, zero_add]
  rw [real_inner_comm, lnDelta, inner_toLp_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  field_simp

/-- Tail of the Gaussian term. -/
lemma lnNoise_real_abs_two_mul_inner_ge_le (hn : 0 < n) {u : ℝ} (hu : 0 ≤ u) :
    (lnNoise ι n).real {e | u ≤ |2 * inner ℝ θ (lnDelta n e)|}
      ≤ 2 * exp (-u ^ 2 / (2 * (4 * ‖θ‖ ^ 2 / n))) := by
  have hlaw := hasLaw_two_mul_inner_lnDelta θ hn
  have hsg := hasSubgaussianMGF_fun_id_gaussianReal (4 * ‖θ‖₊ ^ 2 / n)
  rw [← hlaw.map_eq] at hsg
  have h1 := (HasSubgaussianMGF.of_map hlaw.aemeasurable hsg).measureReal_abs_ge_le hu
  push_cast at h1
  exact h1

/-- The standard Gaussian vector `g_i = (∑ ℓ, e i ℓ) / √n`. -/
noncomputable def lnG (n : ℕ) (e : ι → Fin n → ℝ) : ι → ℝ := fun i ↦ (∑ ℓ, e i ℓ) / √n

lemma hasLaw_lnG (hn : 0 < n) :
    HasLaw (lnG (ι := ι) n) (Measure.pi fun _ : ι ↦ gaussianReal 0 1) (lnNoise ι n) := by
  have hn' : (0 : ℝ) < n := by positivity
  have h_indep : iIndepFun (fun i (e : ι → Fin n → ℝ) ↦ 0 + (1 / √(n : ℝ)) * ∑ ℓ, e i ℓ)
      (lnNoise ι n) :=
    iIndepFun_pi (X := fun _ (v : Fin n → ℝ) ↦ 0 + (1 / √(n : ℝ)) * ∑ ℓ, v ℓ) fun _ ↦ by fun_prop
  have hX : ∀ i, HasLaw (fun e : ι → Fin n → ℝ ↦ 0 + (1 / √(n : ℝ)) * ∑ ℓ, e i ℓ)
      (gaussianReal 0 1) (lnNoise ι n) := by
    intro i
    have hmap : (lnNoise ι n).map (fun e : ι → Fin n → ℝ ↦ e i)
        = Measure.pi fun _ : Fin n ↦ gaussianReal 0 1 :=
      (measurePreserving_eval (fun _ : ι ↦ Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) i).map_eq
    have h := HasLaw.comp (hasLaw_const_add_const_mul_sum_pi_gaussianReal 0 (1 / √(n : ℝ)))
      ⟨(measurable_pi_apply i).aemeasurable, hmap⟩
    have hv : ‖1 / √(n : ℝ)‖₊ ^ 2 * (n : ℝ≥0) = 1 := by
      apply NNReal.eq
      push_cast
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_pow, one_pow,
        Real.sq_sqrt hn'.le]
      field_simp
    exact ⟨h.aemeasurable, h.map_eq.trans (congrArg (gaussianReal _) hv)⟩
  have := h_indep.hasLaw_pi hX
  refine this.congr (ae_of_all _ fun e ↦ ?_)
  funext i
  simp only [lnG, zero_add]
  ring

lemma norm_lnDelta_sq_sub_eq (hn : 0 < n) (e : ι → Fin n → ℝ) :
    ‖lnDelta n e‖ ^ 2 - Fintype.card ι / n = (1 / n) * ∑ i, (lnG n e i ^ 2 - 1) := by
  have hn' : (0 : ℝ) < n := by positivity
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [lnDelta, PiLp.toLp_apply, lnG, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, mul_sub, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [div_pow, div_pow, Real.sq_sqrt hn'.le]
    field_simp
  · ring

/-- The chi-square term `‖Δ‖² - d / n` is sub-exponential with parameters `(8 d / n², 4 / n)`
(blueprint `lem:large_norm_decomposition`). -/
lemma hasSubexponentialMGF_lnQ (hn : 0 < n) :
    HasSubexponentialMGF (fun e : ι → Fin n → ℝ ↦ ‖lnDelta n e‖ ^ 2 - Fintype.card ι / n)
      ((1 / n) ^ 2 * (8 * Fintype.card ι)) (|1 / (n : ℝ)| * 4) (lnNoise ι n) := by
  have h := hasSubexponentialMGF_sum_sq_sub_one_pi_gaussianReal (ι := ι)
  have hlaw := hasLaw_lnG (ι := ι) hn
  rw [← hlaw.map_eq] at h
  have h2 := HasSubexponentialMGF.of_map (X := fun g : ι → ℝ ↦ ∑ i, (g i ^ 2 - 1)) (Y := lnG n)
    (μ := lnNoise ι n) hlaw.aemeasurable (by exact h)
  have h3 := h2.const_mul (1 / n)
  -- the library bound is sharper (`4 d` in place of `8 d`); we keep the paper's constant here
  refine (h3.congr (ae_of_all _ fun e ↦ ?_)).mono
    (by nlinarith [sq_nonneg (1 / (n : ℝ)), (Nat.cast_nonneg (Fintype.card ι) : (0:ℝ) ≤ _)])
    le_rfl
  simp only [Function.comp_apply]
  rw [norm_lnDelta_sq_sub_eq hn]

/-- The number of repetitions of each basis vector: `⌈48 log(4/δ) / ε²⌉`. -/
noncomputable def lnN (ε δ : ℝ) : ℕ := ⌈48 * log (4 / δ) / ε ^ 2⌉₊

/-- **Guarantee in the large-norm regime** (blueprint `thm:large_norm_guarantee`): if
`‖θ‖ ≥ √d`, the large-norm estimate is within `ε` of `‖θ‖` with probability at least
`1 - δ/2`. -/
theorem lnNoise_real_lnEst_gt_le (hd : 0 < Fintype.card ι) {ε δ : ℝ} (hε : ε ∈ Set.Ioc 0 1)
    (hδ : δ ∈ Set.Ioo 0 1) (hθ : √(Fintype.card ι) ≤ ‖θ‖) :
    (lnNoise ι (lnN ε δ)).real {e | ε < |lnEst θ (lnN ε δ) e - ‖θ‖|} ≤ δ / 2 := by
  have hL : 0 < log (4 / δ) := Real.log_pos (by rw [lt_div_iff₀ hδ.1]; linarith [hδ.2])
  have hlog4 : log 4 ≤ log (4 / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ.1]; nlinarith [hδ.2])
  have hL1 : 1 < log (4 / δ) := lt_of_lt_of_le one_lt_log_four hlog4
  have hnge : 48 * log (4 / δ) / ε ^ 2 ≤ lnN ε δ := Nat.le_ceil _
  have hnpos : 0 < lnN ε δ :=
    Nat.ceil_pos.2 (div_pos (mul_pos (by norm_num) hL) (pow_pos hε.1 2))
  set n := lnN ε δ with hn_def
  clear_value n
  have hn' : (0 : ℝ) < n := by positivity
  have hd' : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.2 hd
  have hd1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hd
  have hsqrt1 : 1 ≤ √(Fintype.card ι : ℝ) := by
    rw [Real.le_sqrt (by norm_num) hd'.le]
    simpa using hd1
  have hr1 : 1 ≤ ‖θ‖ := hsqrt1.trans hθ
  have hr : 0 < ‖θ‖ := by linarith
  have hrd : (Fintype.card ι : ℝ) ≤ ‖θ‖ ^ 2 := by
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hθ 2
    rwa [Real.sq_sqrt hd'.le] at this
  have hn48 : (48 : ℝ) ≤ n := by
    calc (48 : ℝ) ≤ 48 * log (4 / δ) / ε ^ 2 := by
          rw [le_div_iff₀ (pow_pos hε.1 2)]
          nlinarith [hε.2, hε.1, hL1]
      _ ≤ n := hnge
  have hnε : 48 * log (4 / δ) ≤ n * ε ^ 2 := by
    rwa [div_le_iff₀ (pow_pos hε.1 2)] at hnge
  set u : ℝ := ε * ‖θ‖ / 2 with hu_def
  have hu : 0 ≤ u := by
    rw [hu_def]
    exact div_nonneg (mul_nonneg hε.1.le (norm_nonneg θ)) (by norm_num)
  clear_value u
  -- inclusion of the error event in the union of the two tail events
  have hsub : {e | ε < |lnEst θ n e - ‖θ‖|}
      ⊆ {e | u ≤ |2 * inner ℝ θ (lnDelta n e)|}
        ∪ {e | u ≤ |‖lnDelta n e‖ ^ 2 - Fintype.card ι / n|} := by
    intro e he
    simp only [Set.mem_ofPred_eq, Set.mem_union] at he ⊢
    by_contra hcon
    push Not at hcon
    have h1 : |lnR θ n e - ‖θ‖ ^ 2| < ε * ‖θ‖ := by
      rw [lnR_sub_eq]
      calc |2 * inner ℝ θ (lnDelta n e) + (‖lnDelta n e‖ ^ 2 - Fintype.card ι / n)|
          ≤ |2 * inner ℝ θ (lnDelta n e)| + |‖lnDelta n e‖ ^ 2 - Fintype.card ι / n| :=
            abs_add_le _ _
        _ < u + u := add_lt_add hcon.1 hcon.2
        _ = ε * ‖θ‖ := by rw [hu_def]; ring
    rw [abs_lt] at h1
    have hR : 0 ≤ lnR θ n e := by
      nlinarith [mul_nonneg hr.le (by linarith [hε.2] : (0 : ℝ) ≤ ‖θ‖ - ε)]
    have hEst : lnEst θ n e = √(lnR θ n e) := by rw [lnEst, max_eq_left hR]
    rw [hEst] at he
    set R := lnR θ n e with hR_def
    have hsq : √R ^ 2 = R := Real.sq_sqrt hR
    have hsqrt0 := Real.sqrt_nonneg R
    have hpos : 0 < √R + ‖θ‖ := add_pos_of_nonneg_of_pos hsqrt0 hr
    have hfac : (√R - ‖θ‖) * (√R + ‖θ‖) = R - ‖θ‖ ^ 2 := by nlinarith
    have h2 : |√R - ‖θ‖| * (√R + ‖θ‖) < ε * ‖θ‖ := by
      rw [← abs_of_pos hpos, ← abs_mul, hfac]
      exact abs_lt.2 h1
    have h3 : |√R - ‖θ‖| * ‖θ‖ ≤ |√R - ‖θ‖| * (√R + ‖θ‖) := by
      gcongr
      linarith
    have h4 : |√R - ‖θ‖| < ε := lt_of_mul_lt_mul_right (h3.trans_lt h2) hr.le
    linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans ?_)
  -- the Gaussian term
  have hg : (lnNoise ι n).real {e | u ≤ |2 * inner ℝ θ (lnDelta n e)|} ≤ δ / 4 := by
    refine (lnNoise_real_abs_two_mul_inner_ge_le θ hnpos hu).trans ?_
    have e1 : -u ^ 2 / (2 * (4 * ‖θ‖ ^ 2 / n)) = -(n * ε ^ 2 / 32) := by
      rw [hu_def]
      field_simp
      ring
    rw [e1]
    have h1 : exp (-(n * ε ^ 2 / 32)) ≤ exp (-(log (4 / δ) + log (4 / δ) / 2)) :=
      exp_le_exp.2 (by linarith)
    have h2 : exp (-(log (4 / δ) + log (4 / δ) / 2))
        = exp (-log (4 / δ)) * exp (-(log (4 / δ) / 2)) := by
      rw [← exp_add]
      ring_nf
    have h3 : exp (-log (4 / δ)) = δ / 4 := by
      rw [exp_neg, Real.exp_log (div_pos (by norm_num) hδ.1)]
      field_simp
    have h4 : exp (-(log (4 / δ) / 2)) ≤ 1 / 2 := exp_neg_half_le_half hlog4
    have h5 : exp (-(n * ε ^ 2 / 32)) ≤ δ / 4 * (1 / 2) := by
      rw [h2, h3] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left h4 (by linarith [hδ.1]))
    linarith
  -- the chi-square term
  have hq : (lnNoise ι n).real {e | u ≤ |‖lnDelta n e‖ ^ 2 - Fintype.card ι / n|} ≤ δ / 4 := by
    have hse := hasSubexponentialMGF_lnQ (ι := ι) hnpos
    have hV : (0 : ℝ) < (1 / n) ^ 2 * (8 * Fintype.card ι) :=
      mul_pos (pow_pos (one_div_pos.2 hn') 2) (mul_pos (by norm_num) hd')
    refine (hse.measure_abs_ge_le hu).trans ?_
    have h3L : 3 * log (4 / δ) ≤ min (u ^ 2 / (2 * ((1 / n) ^ 2 * (8 * Fintype.card ι))))
        (u / (2 * (|1 / (n : ℝ)| * 4))) := by
      refine le_min ?_ ?_
      · rw [hu_def, le_div_iff₀ (mul_pos (by norm_num) hV)]
        have hn2 : 2304 * log (4 / δ) ≤ n ^ 2 * ε ^ 2 := by
          have := mul_le_mul_of_nonneg_left hnε hn'.le
          nlinarith
        have e2 : 3 * log (4 / δ) * (2 * ((1 / n) ^ 2 * (8 * Fintype.card ι)))
            = 48 * log (4 / δ) * Fintype.card ι / n ^ 2 := by
          field_simp
          ring
        rw [e2, div_le_iff₀ (pow_pos hn' 2)]
        have h5 : (ε * ‖θ‖ / 2) ^ 2 * n ^ 2 = n ^ 2 * ε ^ 2 * ‖θ‖ ^ 2 / 4 := by ring
        rw [h5]
        nlinarith [mul_le_mul_of_nonneg_left hrd (by positivity : (0 : ℝ) ≤ n ^ 2 * ε ^ 2),
          mul_le_mul_of_nonneg_right hn2 hd'.le]
      · rw [hu_def, abs_of_pos (one_div_pos.2 hn'),
          le_div_iff₀ (mul_pos (by norm_num) (mul_pos (one_div_pos.2 hn') (by norm_num)))]
        have e3 : 3 * log (4 / δ) * (2 * (1 / (n : ℝ) * 4)) = 24 * log (4 / δ) / n := by
          field_simp
          ring
        rw [e3, div_le_iff₀ hn']
        have h6 : ε ^ 2 ≤ ε * ‖θ‖ := by nlinarith [hε.1, hε.2, hr1]
        nlinarith [hnε, mul_le_mul_of_nonneg_left h6 hn'.le]
    calc 2 * exp (-min (u ^ 2 / (2 * ((1 / n) ^ 2 * (8 * Fintype.card ι))))
          (u / (2 * (|1 / (n : ℝ)| * 4))))
        ≤ 2 * exp (-(3 * log (4 / δ))) :=
          mul_le_mul_of_nonneg_left (exp_le_exp.2 (neg_le_neg h3L)) (by norm_num)
      _ = 2 * (δ / 4) ^ 3 := by
          rw [exp_neg, show (3 : ℝ) * log (4 / δ) = ((3 : ℕ) : ℝ) * log (4 / δ) by norm_num,
            Real.exp_nat_mul, Real.exp_log (div_pos (by norm_num) hδ.1)]
          field_simp
      _ ≤ δ / 4 := by
          have hδ2 : δ ^ 2 ≤ 1 := by nlinarith [hδ.1, hδ.2]
          nlinarith [mul_nonneg hδ.1.le (by linarith : (0 : ℝ) ≤ 8 - δ ^ 2)]
  linarith

end Maiti2026Power
