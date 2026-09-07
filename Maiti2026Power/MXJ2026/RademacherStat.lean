/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.Mathlib.Probability.Rademacher
public import Maiti2026Power.Mathlib.Probability.GaussianSum
public import Maiti2026Power.MXJ2026.UnitBall

/-!
# The Rademacher block statistic (norm estimation, Section 3 of the paper)

A *Rademacher direction* is `radDir u = σ / √d` for a sign vector `σ` given by a Boolean seed
`u`. The Rademacher block sampling rule plays `K` fresh directions, each `s` times. On the product
space `rbMeasure ι s K` of the `K` seeds and the `K × s` standard Gaussian noises, the block means
are `rbMean θ s p k = ⟪radDir (u k), θ⟫ + (∑ ℓ, e k ℓ) / s` and the squared statistic is
`rbStat θ s K p = (∑ k, d (rbMean k ^ 2 - 1 / s)) / K`, which decomposes as
`rbStat - ‖θ‖² = (∑ k, rbX k) / K + (∑ k, rbW k) / K` (Term 1: fluctuations of the directions,
Term 2: fluctuations of the noise).

Blueprint: `def:rademacher_direction`, `lem:direction_second_moment`, `def:squared_statistic`,
`lem:statistic_structure`, `lem:term1_subexp`, `lem:term1_bound`, `lem:term2_conditional`,
`lem:term2_bound`, `lem:vbar_bound`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset
open scoped ENNReal NNReal

namespace Maiti2026Power

variable {ι : Type*} [Fintype ι]

section Direction

/-- The Rademacher direction `σ / √d` given by the Boolean seed `u`. -/
noncomputable def radDir (u : ι → Bool) : EuclideanSpace ℝ ι :=
  (√(Fintype.card ι))⁻¹ • WithLp.toLp 2 (signVec u)

lemma signOf_sq (b : Bool) : signOf b ^ 2 = 1 := by cases b <;> simp [signOf]

lemma norm_toLp_signVec (u : ι → Bool) : ‖(WithLp.toLp 2 (signVec u) : EuclideanSpace ℝ ι)‖
    = √(Fintype.card ι) := by
  rw [EuclideanSpace.norm_eq]
  simp [signVec, Real.norm_eq_abs, sq_abs, signOf_sq]

lemma norm_radDir_le_one (u : ι → Bool) : ‖radDir u‖ ≤ 1 := by
  rw [radDir, norm_smul, norm_toLp_signVec, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rcases eq_or_ne (Fintype.card ι : ℝ) 0 with h | h
  · simp [h]
  · rw [inv_mul_cancel₀ (Real.sqrt_ne_zero'.2 (by positivity))]

lemma radDir_mem_unitBall (u : ι → Bool) : radDir u ∈ unitBall ι :=
  mem_unitBall_iff.2 (norm_radDir_le_one u)

lemma measurable_radDir : Measurable (radDir (ι := ι)) :=
  (measurable_const_smul _).comp
    ((PiLp.continuous_toLp 2 _).measurable.comp measurable_signVec)

lemma inner_radDir (u : ι → Bool) (θ : EuclideanSpace ℝ ι) :
    inner ℝ (radDir u) θ = (√(Fintype.card ι))⁻¹ * ∑ i, signOf (u i) * θ i := by
  rw [radDir, real_inner_smul_left, inner_toLp_eq_sum]
  rfl

/-- `d ⟪radDir u, θ⟫² = ⟪σ, θ⟫²` (blueprint `lem:direction_second_moment`). -/
lemma card_mul_inner_radDir_sq (u : ι → Bool) (θ : EuclideanSpace ℝ ι) :
    (Fintype.card ι : ℝ) * inner ℝ (radDir u) θ ^ 2 = (∑ i, signOf (u i) * θ i) ^ 2 := by
  rw [inner_radDir, mul_pow, inv_pow, Real.sq_sqrt (by positivity)]
  rcases eq_or_ne (Fintype.card ι : ℝ) 0 with h | h
  · have : Fintype.card ι = 0 := by exact_mod_cast h
    have := Fintype.card_eq_zero_iff.1 this
    simp [Finset.univ_eq_empty]
  · field_simp

lemma measurable_inner_radDir (θ : EuclideanSpace ℝ ι) :
    Measurable fun u : ι → Bool ↦ inner ℝ (radDir u) θ :=
  (continuous_id.inner continuous_const).measurable.comp measurable_radDir

end Direction

section Statistic

variable (ι) (s K : ℕ)

/-- The probability space of the Rademacher block sampling rule: `K` Boolean seeds and `K` blocks
of `s` standard Gaussian noises. -/
noncomputable def rbMeasure : Measure ((Fin K → ι → Bool) × (Fin K → Fin s → ℝ)) :=
  (Measure.pi fun _ ↦ uniformBoolVec ι).prod
    (Measure.pi fun _ ↦ Measure.pi fun _ ↦ gaussianReal 0 1)

instance : IsProbabilityMeasure (rbMeasure ι s K) := by
  unfold rbMeasure
  infer_instance

variable {ι} (θ : EuclideanSpace ℝ ι)

/-- The mean observation of block `k`: `⟪radDir (u k), θ⟫ + (∑ ℓ, e k ℓ) / s`. -/
noncomputable def rbMean (p : (Fin K → ι → Bool) × (Fin K → Fin s → ℝ)) (k : Fin K) : ℝ :=
  inner ℝ (radDir (p.1 k)) θ + (∑ ℓ, p.2 k ℓ) / s

/-- The squared statistic `(∑ k, d (ȳ_k² - 1 / s)) / K`. -/
noncomputable def rbStat (p : (Fin K → ι → Bool) × (Fin K → Fin s → ℝ)) : ℝ :=
  (∑ k, (Fintype.card ι : ℝ) * (rbMean s K θ p k ^ 2 - 1 / s)) / K

/-- Term 1: `d ⟪radDir (u k), θ⟫² - ‖θ‖²`. -/
noncomputable def rbX (u : Fin K → ι → Bool) (k : Fin K) : ℝ :=
  (Fintype.card ι : ℝ) * inner ℝ (radDir (u k)) θ ^ 2 - ‖θ‖ ^ 2

/-- Term 2: `d (ȳ_k² - 1 / s) - d ⟪radDir (u k), θ⟫²`. -/
noncomputable def rbW (p : (Fin K → ι → Bool) × (Fin K → Fin s → ℝ)) (k : Fin K) : ℝ :=
  (Fintype.card ι : ℝ) * (rbMean s K θ p k ^ 2 - 1 / s)
    - (Fintype.card ι : ℝ) * inner ℝ (radDir (p.1 k)) θ ^ 2

/-- The variance proxy of Term 2 as a function of the directions:
`8 ((d / s)² + (d² / s) (∑ k, ⟪radDir (u k), θ⟫²) / K)`. -/
noncomputable def rbVbar (u : Fin K → ι → Bool) : ℝ :=
  8 * (((Fintype.card ι : ℝ) / s) ^ 2
    + (Fintype.card ι : ℝ) ^ 2 / s * ((∑ k, inner ℝ (radDir (u k)) θ ^ 2) / K))

variable {s K θ}

lemma rbStat_sub_sq_eq (hK : 0 < K) (p : (Fin K → ι → Bool) × (Fin K → Fin s → ℝ)) :
    rbStat s K θ p - ‖θ‖ ^ 2 = (∑ k, rbX K θ p.1 k) / K + (∑ k, rbW s K θ p k) / K := by
  have hK' : (K : ℝ) ≠ 0 := by positivity
  rw [rbStat, ← add_div, eq_div_iff hK', sub_mul, div_mul_cancel₀ _ hK']
  simp only [rbX, rbW]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

lemma measurable_rbMean (k : Fin K) : Measurable fun p ↦ rbMean s K θ p k := by
  unfold rbMean
  exact ((measurable_inner_radDir θ).comp ((measurable_pi_apply k).comp measurable_fst)).add
    ((Finset.measurable_sum _ fun ℓ _ ↦ (measurable_pi_apply ℓ).comp
      ((measurable_pi_apply k).comp measurable_snd)).div_const _)

lemma measurable_rbStat : Measurable (rbStat s K θ) := by
  unfold rbStat
  exact (Finset.measurable_sum _ fun k _ ↦
    ((measurable_rbMean k).pow_const 2 |>.sub_const _).const_mul _).div_const _

lemma measurable_rbX (k : Fin K) : Measurable fun u ↦ rbX K θ u k := by
  unfold rbX
  exact (((measurable_inner_radDir θ).comp (measurable_pi_apply k)).pow_const 2
    |>.const_mul _).sub_const _

lemma measurable_rbW (k : Fin K) : Measurable fun p ↦ rbW s K θ p k := by
  unfold rbW
  exact (((measurable_rbMean k).pow_const 2 |>.sub_const _).const_mul _).sub
    ((((measurable_inner_radDir θ).comp ((measurable_pi_apply k).comp measurable_fst)).pow_const 2
      ).const_mul _)

lemma measurable_rbVbar : Measurable (rbVbar s K θ) := by
  unfold rbVbar
  exact (measurable_const.add ((Finset.measurable_sum _ fun k _ ↦
    ((measurable_inner_radDir θ).comp (measurable_pi_apply k)).pow_const 2).div_const _
      |>.const_mul _)).const_mul _

/-- A set of seeds has the same probability under `rbMeasure` as under the seed marginal. -/
lemma rbMeasure_real_fst (A : Set (Fin K → ι → Bool)) :
    (rbMeasure ι s K).real {p | p.1 ∈ A}
      = (Measure.pi fun _ : Fin K ↦ uniformBoolVec ι).real A := by
  rw [measureReal_def, measureReal_def, rbMeasure,
    show {p : (Fin K → ι → Bool) × (Fin K → Fin s → ℝ) | p.1 ∈ A} = A ×ˢ Set.univ from
      Set.ext fun p ↦ by simp,
    Measure.prod_prod, measure_univ, mul_one]

/-- **Term 1 is sub-exponential** (blueprint `lem:term1_subexp`): the `rbX k` are i.i.d. with
parameters `(16 ‖θ‖⁴, 4 ‖θ‖²)` under the seed marginal. -/
lemma hasSubexponentialMGF_rbX (k : Fin K) :
    HasSubexponentialMGF (fun u ↦ rbX K θ u k) (16 * ‖θ‖ ^ 4) (4 * ‖θ‖ ^ 2)
      (Measure.pi fun _ : Fin K ↦ uniformBoolVec ι) := by
  have h := hasSubexponentialMGF_sq_sum_signOf_mul_sub_uniformBoolVec θ
  have hmap : (Measure.pi fun _ : Fin K ↦ uniformBoolVec ι).map (fun u : Fin K → ι → Bool ↦ u k)
      = uniformBoolVec ι :=
    (measurePreserving_eval (fun _ : Fin K ↦ uniformBoolVec ι) k).map_eq
  have h2 := HasSubexponentialMGF.of_map
    (X := fun v : ι → Bool ↦ (∑ i, signOf (v i) * θ i) ^ 2 - ‖θ‖ ^ 2)
    (Y := fun u : Fin K → ι → Bool ↦ u k) (μ := Measure.pi fun _ : Fin K ↦ uniformBoolVec ι)
    (measurable_pi_apply k).aemeasurable (by rw [hmap]; exact h)
  refine h2.congr (ae_of_all _ fun u ↦ ?_)
  simp only [Function.comp_apply, rbX, card_mul_inner_radDir_sq]

lemma iIndepFun_rbX :
    iIndepFun (fun k (u : Fin K → ι → Bool) ↦ rbX K θ u k)
      (Measure.pi fun _ : Fin K ↦ uniformBoolVec ι) :=
  iIndepFun_pi
    (X := fun _ (v : ι → Bool) ↦ (Fintype.card ι : ℝ) * inner ℝ (radDir v) θ ^ 2 - ‖θ‖ ^ 2)
    fun _ ↦ (((measurable_inner_radDir θ).pow_const 2).const_mul _ |>.sub_const _).aemeasurable

lemma rbX_eq_zero_of_eq_zero (u : Fin K → ι → Bool) (k : Fin K) :
    rbX K (0 : EuclideanSpace ℝ ι) u k = 0 := by
  simp [rbX]

/-- **Tail bound for Term 1** (blueprint `lem:term1_bound`). -/
lemma rbMeasure_real_avg_rbX_gt_le (hr : 0 < ‖θ‖) (hK : 0 < K) {t : ℝ} (ht : 0 ≤ t) :
    (rbMeasure ι s K).real {p | t < |(∑ k, rbX K θ p.1 k) / K|}
      ≤ 2 * exp (-(K * min (t ^ 2 / (32 * ‖θ‖ ^ 4)) (t / (8 * ‖θ‖ ^ 2)))) := by
  have : Nonempty (Fin K) := ⟨(⟨0, hK⟩ : Fin K)⟩
  rw [show {p : (Fin K → ι → Bool) × (Fin K → Fin s → ℝ) | t < |(∑ k, rbX K θ p.1 k) / K|}
      = {p | p.1 ∈ {u | t < |(∑ k, rbX K θ u k) / K|}} from rfl, rbMeasure_real_fst]
  have := HasSubexponentialMGF.measure_abs_average_ge_le_of_forall (ι := Fin K)
    (iIndepFun_rbX (K := K) (θ := θ)) (fun k ↦ measurable_rbX k)
    (fun k ↦ hasSubexponentialMGF_rbX k) (by positivity) (by positivity) ht
  simp only [Fintype.card_fin] at this
  have hsub : {u : Fin K → ι → Bool | t < |(∑ k, rbX K θ u k) / K|}
      ⊆ {u | t ≤ |(∑ k, rbX K θ u k) / K|} :=
    fun u hu ↦ by
      change t ≤ |(∑ k, rbX K θ u k) / K|
      exact le_of_lt hu
  have e1 : 2 * (16 * ‖θ‖ ^ 4) = 32 * ‖θ‖ ^ 4 := by ring
  have e2 : 2 * (4 * ‖θ‖ ^ 2) = 8 * ‖θ‖ ^ 2 := by ring
  rw [e1, e2] at this
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans this

end Statistic

section Term2

variable {s K : ℕ} {θ : EuclideanSpace ℝ ι}

/-- The noise marginal of `rbMeasure`: `K` blocks of `s` standard Gaussians. -/
noncomputable def rbNoise (s K : ℕ) : Measure (Fin K → Fin s → ℝ) :=
  Measure.pi fun _ ↦ Measure.pi fun _ ↦ gaussianReal 0 1

instance : IsProbabilityMeasure (rbNoise s K) := by
  unfold rbNoise
  infer_instance

lemma rbMeasure_eq :
    rbMeasure ι s K = (Measure.pi fun _ : Fin K ↦ uniformBoolVec ι).prod (rbNoise s K) := rfl

/-- `W_k = (√d ȳ_k)² - ((√d μ_k)² + d / s)`. -/
lemma rbW_eq (p : (Fin K → ι → Bool) × (Fin K → Fin s → ℝ)) (k : Fin K) :
    rbW s K θ p k = (√(Fintype.card ι) * rbMean s K θ p k) ^ 2
      - ((√(Fintype.card ι) * inner ℝ (radDir (p.1 k)) θ) ^ 2 + (Fintype.card ι : ℝ) / s) := by
  unfold rbW
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  ring

/-- For fixed directions `u`, `√d ȳ_k` has law `N(√d μ_k, d / s)` (blueprint
`lem:statistic_structure`, noise part). -/
lemma hasLaw_sqrt_mul_rbMean (hs : 0 < s) (u : Fin K → ι → Bool) (k : Fin K) :
    HasLaw (fun e : Fin K → Fin s → ℝ ↦ √(Fintype.card ι) * rbMean s K θ (u, e) k)
      (gaussianReal (√(Fintype.card ι) * inner ℝ (radDir (u k)) θ)
        ((Fintype.card ι : ℝ≥0) / (s : ℝ≥0)))
      (rbNoise s K) := by
  have h1 := hasLaw_const_add_const_mul_sum_pi_gaussianReal (s := s)
    (√(Fintype.card ι) * inner ℝ (radDir (u k)) θ) (√(Fintype.card ι) / s)
  have hmap : (rbNoise s K).map (fun e : Fin K → Fin s → ℝ ↦ e k)
      = Measure.pi fun _ : Fin s ↦ gaussianReal 0 1 :=
    (measurePreserving_eval (fun _ : Fin K ↦ Measure.pi fun _ : Fin s ↦ gaussianReal 0 1) k).map_eq
  have h2 := HasLaw.comp h1 ⟨(measurable_pi_apply k).aemeasurable, hmap⟩
  have hv : ‖√(Fintype.card ι) / s‖₊ ^ 2 * (s : ℝ≥0)
      = (Fintype.card ι : ℝ≥0) / (s : ℝ≥0) := by
    apply NNReal.eq
    push_cast
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have h3 : HasLaw ((fun e : Fin s → ℝ ↦ √(Fintype.card ι) * inner ℝ (radDir (u k)) θ
      + √(Fintype.card ι) / s * ∑ ℓ, e ℓ) ∘ fun e : Fin K → Fin s → ℝ ↦ e k)
      (gaussianReal (√(Fintype.card ι) * inner ℝ (radDir (u k)) θ)
        ((Fintype.card ι : ℝ≥0) / (s : ℝ≥0))) (rbNoise s K) :=
    ⟨h2.aemeasurable, h2.map_eq.trans (congrArg (gaussianReal _) hv)⟩
  refine h3.congr (ae_of_all _ fun e ↦ ?_)
  simp only [Function.comp_apply, rbMean]
  ring

/-- **Term 2 is conditionally sub-exponential** (blueprint `lem:term2_conditional`): for fixed
directions `u`, `W_k` has parameters `(8 ((d/s)² + d μ_k² (d/s)), 4 d/s)` under the noise. -/
lemma hasSubexponentialMGF_rbW (hs : 0 < s) (u : Fin K → ι → Bool) (k : Fin K) :
    HasSubexponentialMGF (fun e : Fin K → Fin s → ℝ ↦ rbW s K θ (u, e) k)
      (8 * (((Fintype.card ι : ℝ) / s) ^ 2
        + (√(Fintype.card ι) * inner ℝ (radDir (u k)) θ) ^ 2 * ((Fintype.card ι : ℝ) / s)))
      (4 * ((Fintype.card ι : ℝ) / s)) (rbNoise s K) := by
  have hbase := hasSubexponentialMGF_sq_sub_gaussianReal
    (√(Fintype.card ι) * inner ℝ (radDir (u k)) θ) ((Fintype.card ι : ℝ≥0) / (s : ℝ≥0))
  have hlaw := hasLaw_sqrt_mul_rbMean (θ := θ) hs u k
  rw [← hlaw.map_eq] at hbase
  have h2 := HasSubexponentialMGF.of_map
    (X := fun x : ℝ ↦ x ^ 2 - ((√(Fintype.card ι) * inner ℝ (radDir (u k)) θ) ^ 2
      + (((Fintype.card ι : ℝ≥0) / (s : ℝ≥0) : ℝ≥0) : ℝ)))
    (Y := fun e : Fin K → Fin s → ℝ ↦ √(Fintype.card ι) * rbMean s K θ (u, e) k)
    (μ := rbNoise s K) hlaw.aemeasurable (by exact hbase)
  push_cast at h2
  refine h2.congr (ae_of_all _ fun e ↦ ?_)
  simp only [Function.comp_apply]
  rw [rbW_eq]

lemma iIndepFun_rbW (u : Fin K → ι → Bool) :
    iIndepFun (fun k (e : Fin K → Fin s → ℝ) ↦ rbW s K θ (u, e) k) (rbNoise s K) := by
  have := iIndepFun_pi (μ := fun _ : Fin K ↦ Measure.pi fun _ : Fin s ↦ gaussianReal 0 1)
    (X := fun k (v : Fin s → ℝ) ↦ (Fintype.card ι : ℝ)
      * ((inner ℝ (radDir (u k)) θ + (∑ ℓ, v ℓ) / s) ^ 2 - 1 / s)
      - (Fintype.card ι : ℝ) * inner ℝ (radDir (u k)) θ ^ 2)
    fun k ↦ (((measurable_const.add
      ((Finset.measurable_sum _ fun ℓ _ ↦ measurable_pi_apply ℓ).div_const _)).pow_const 2
      |>.sub_const _).const_mul _ |>.sub_const _).aemeasurable
  exact this

lemma sum_rbVbar_eq (hK : 0 < K) (u : Fin K → ι → Bool) :
    (∑ k, 8 * (((Fintype.card ι : ℝ) / s) ^ 2
        + (√(Fintype.card ι) * inner ℝ (radDir (u k)) θ) ^ 2 * ((Fintype.card ι : ℝ) / s))) / K
      = rbVbar s K θ u := by
  have h : ∀ k, 8 * (((Fintype.card ι : ℝ) / s) ^ 2
      + (√(Fintype.card ι) * inner ℝ (radDir (u k)) θ) ^ 2 * ((Fintype.card ι : ℝ) / s))
      = 8 * ((Fintype.card ι : ℝ) / s) ^ 2
        + 8 * ((Fintype.card ι : ℝ) ^ 2 / s) * inner ℝ (radDir (u k)) θ ^ 2 := by
    intro k
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  simp_rw [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, rbVbar]
  have hK' : (K : ℝ) ≠ 0 := by positivity
  field_simp

lemma rbVbar_pos (hd : 0 < Fintype.card ι) (hs : 0 < s) (u : Fin K → ι → Bool) :
    0 < rbVbar s K θ u := by
  unfold rbVbar
  have h1 : 0 < ((Fintype.card ι : ℝ) / s) ^ 2 := by positivity
  have h2 : 0 ≤ (Fintype.card ι : ℝ) ^ 2 / s * ((∑ k, inner ℝ (radDir (u k)) θ ^ 2) / K) := by
    positivity
  linarith

/-- Conditional tail bound for Term 2, for fixed directions. -/
lemma rbNoise_real_avg_rbW_ge_le (hd : 0 < Fintype.card ι) (hs : 0 < s) (hK : 0 < K)
    (u : Fin K → ι → Bool) {t : ℝ} (ht : 0 ≤ t) :
    (rbNoise s K).real {e | t ≤ |(∑ k, rbW s K θ (u, e) k) / K|}
      ≤ 2 * exp (-(K * min (t ^ 2 / (2 * rbVbar s K θ u))
        (t / (2 * (4 * ((Fintype.card ι : ℝ) / s)))))) := by
  have : Nonempty (Fin K) := ⟨(⟨0, hK⟩ : Fin K)⟩
  have hsum : 0 < ∑ k : Fin K, 8 * (((Fintype.card ι : ℝ) / s) ^ 2
      + (√(Fintype.card ι) * inner ℝ (radDir (u k)) θ) ^ 2 * ((Fintype.card ι : ℝ) / s)) := by
    have hK' : (0 : ℝ) < K := by positivity
    have := rbVbar_pos (θ := θ) hd hs u
    rw [← sum_rbVbar_eq hK, div_pos_iff_of_pos_right hK'] at this
    exact this
  have := HasSubexponentialMGF.measure_abs_average_ge_le (ι := Fin K) (iIndepFun_rbW (θ := θ) u)
    (fun k ↦ (measurable_rbW k).comp (measurable_const.prodMk measurable_id))
    (fun k ↦ hasSubexponentialMGF_rbW hs u k) hsum (by positivity) ht
  rw [Fintype.card_fin, sum_rbVbar_eq hK] at this
  exact this

/-- **Tail bound for Term 2** (blueprint `lem:term2_bound`), by Fubini over the directions. -/
lemma rbMeasure_real_avg_rbW_gt_le (hd : 0 < Fintype.card ι) (hs : 0 < s) (hK : 0 < K)
    {t τ : ℝ} (ht : 0 ≤ t) :
    (rbMeasure ι s K).real {p | t < |(∑ k, rbW s K θ p k) / K|}
      ≤ (rbMeasure ι s K).real {p | τ < rbVbar s K θ p.1}
        + 2 * exp (-(K * min (t ^ 2 / (2 * τ)) (t / (2 * (4 * ((Fintype.card ι : ℝ) / s)))))) := by
  set c := 2 * exp (-(K * min (t ^ 2 / (2 * τ)) (t / (2 * (4 * ((Fintype.card ι : ℝ) / s))))))
    with hc
  have hc0 : 0 ≤ c := by positivity
  set A := {p : (Fin K → ι → Bool) × (Fin K → Fin s → ℝ) | t < |(∑ k, rbW s K θ p k) / K|} with hA
  set B := {p : (Fin K → ι → Bool) × (Fin K → Fin s → ℝ) | τ < rbVbar s K θ p.1} with hB
  have hAm : MeasurableSet A :=
    measurableSet_lt measurable_const
      (continuous_abs.measurable.comp
        ((Finset.measurable_sum _ fun k _ ↦ measurable_rbW k).div_const _))
  have hBm : MeasurableSet B :=
    measurableSet_lt measurable_const (measurable_rbVbar.comp measurable_fst)
  have hsub : A ⊆ B ∪ (Bᶜ ∩ A) := fun p hp ↦ by
    by_cases hpB : p ∈ B
    · exact Or.inl hpB
    · exact Or.inr ⟨hpB, hp⟩
  have hkey : (rbMeasure ι s K) (Bᶜ ∩ A) ≤ ENNReal.ofReal c := by
    rw [rbMeasure_eq, Measure.prod_apply (hBm.compl.inter hAm)]
    calc ∫⁻ u, rbNoise s K (Prod.mk u ⁻¹' (Bᶜ ∩ A)) ∂(Measure.pi fun _ : Fin K ↦ uniformBoolVec ι)
        ≤ ∫⁻ _, ENNReal.ofReal c ∂(Measure.pi fun _ : Fin K ↦ uniformBoolVec ι) := by
          refine lintegral_mono fun u ↦ ?_
          by_cases hu : rbVbar s K θ u ≤ τ
          · have hsub' : Prod.mk u ⁻¹' (Bᶜ ∩ A)
                ⊆ {e | t ≤ |(∑ k, rbW s K θ (u, e) k) / K|} :=
              fun e he ↦ by
                change t ≤ |(∑ k, rbW s K θ (u, e) k) / K|
                exact le_of_lt he.2
            refine (measure_mono hsub').trans ?_
            rw [← ENNReal.ofReal_toReal (measure_ne_top _ _), ← measureReal_def]
            refine ENNReal.ofReal_le_ofReal ((rbNoise_real_avg_rbW_ge_le hd hs hK u ht).trans ?_)
            rw [hc]
            have hV := rbVbar_pos (θ := θ) hd hs u
            have h1 : t ^ 2 / (2 * τ) ≤ t ^ 2 / (2 * rbVbar s K θ u) :=
              div_le_div_of_nonneg_left (sq_nonneg t) (by positivity) (by linarith)
            have h2 := min_le_min h1 (le_refl (t / (2 * (4 * ((Fintype.card ι : ℝ) / s)))))
            have h3 := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg K)
            have h4 := Real.exp_le_exp.2 (neg_le_neg h3)
            linarith
          · have : Prod.mk u ⁻¹' (Bᶜ ∩ A) = ∅ := by
              ext e
              simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_compl_iff, hB,
                Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
              intro h
              exact absurd (not_lt.1 h) hu
            rw [this, measure_empty]
            exact zero_le
      _ = ENNReal.ofReal c := by rw [lintegral_const, measure_univ, mul_one]
  calc (rbMeasure ι s K).real A
      ≤ (rbMeasure ι s K).real (B ∪ (Bᶜ ∩ A)) := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (rbMeasure ι s K).real B + (rbMeasure ι s K).real (Bᶜ ∩ A) := measureReal_union_le _ _
    _ ≤ (rbMeasure ι s K).real B + c := by
        gcongr
        rw [measureReal_def]
        exact ENNReal.toReal_le_of_le_ofReal hc0 hkey

/-- **Bound on the variance proxy** (blueprint `lem:vbar_bound`): with
`τ = 8 ((d/s)² + 3 d r² / (2 s))`, `P(V̄ > τ) ≤ 2 exp (-K / 128)`. -/
lemma rbMeasure_real_rbVbar_gt_le (hK : 0 < K) :
    (rbMeasure ι s K).real
      {p | 8 * (((Fintype.card ι : ℝ) / s) ^ 2 + 3 * Fintype.card ι * ‖θ‖ ^ 2 / (2 * s))
        < rbVbar s K θ p.1} ≤ 2 * exp (-(K / 128)) := by
  have hK' : (0 : ℝ) < K := by positivity
  have hd0 : (0 : ℝ) ≤ Fintype.card ι := by positivity
  -- (∑ k, d μ_k²) / K = ‖θ‖² + (∑ k, rbX k) / K
  have hsum : ∀ u : Fin K → ι → Bool,
      (Fintype.card ι : ℝ) * ((∑ k, inner ℝ (radDir (u k)) θ ^ 2) / K)
        = ‖θ‖ ^ 2 + (∑ k, rbX K θ u k) / K := by
    intro u
    simp only [rbX, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    field_simp
    ring
  rcases eq_or_lt_of_le (norm_nonneg θ) with hr | hr
  · -- `θ = 0`: the event is empty
    have hθ : θ = 0 := norm_eq_zero.1 hr.symm
    subst hθ
    have : {p : (Fin K → ι → Bool) × (Fin K → Fin s → ℝ) |
        8 * (((Fintype.card ι : ℝ) / s) ^ 2
          + 3 * Fintype.card ι * ‖(0 : EuclideanSpace ℝ ι)‖ ^ 2 / (2 * s))
          < rbVbar s K 0 p.1} = ∅ := by
      ext p
      simp [rbVbar]
    rw [this, measureReal_empty]
    positivity
  · -- `{V̄ > τ} ⊆ {|avg X| > r²/2}`
    have hsub : {p : (Fin K → ι → Bool) × (Fin K → Fin s → ℝ) |
        8 * (((Fintype.card ι : ℝ) / s) ^ 2 + 3 * Fintype.card ι * ‖θ‖ ^ 2 / (2 * s))
          < rbVbar s K θ p.1}
        ⊆ {p | ‖θ‖ ^ 2 / 2 < |(∑ k, rbX K θ p.1 k) / K|} := by
      intro p hp
      simp only [Set.mem_ofPred_eq] at hp ⊢
      by_contra hcon
      rw [not_lt, abs_le] at hcon
      have h1 := hsum p.1
      have h2 : rbVbar s K θ p.1 = 8 * (((Fintype.card ι : ℝ) / s) ^ 2
          + (Fintype.card ι : ℝ) / s
            * ((Fintype.card ι : ℝ) * ((∑ k, inner ℝ (radDir (p.1 k)) θ ^ 2) / K))) := by
        rw [rbVbar]
        ring
      rw [h2, h1] at hp
      have hds : (0 : ℝ) ≤ Fintype.card ι / s := by positivity
      have key := mul_le_mul_of_nonneg_left hcon.2 hds
      have h3 : (Fintype.card ι : ℝ) / s * (‖θ‖ ^ 2 + (∑ k, rbX K θ p.1 k) / K)
          ≤ 3 * Fintype.card ι * ‖θ‖ ^ 2 / (2 * s) := by
        have e1 : (Fintype.card ι : ℝ) / s * (‖θ‖ ^ 2 + (∑ k, rbX K θ p.1 k) / K)
            = (Fintype.card ι : ℝ) / s * ‖θ‖ ^ 2
              + (Fintype.card ι : ℝ) / s * ((∑ k, rbX K θ p.1 k) / K) := by ring
        have e2 : 3 * (Fintype.card ι : ℝ) * ‖θ‖ ^ 2 / (2 * s)
            = (Fintype.card ι : ℝ) / s * ‖θ‖ ^ 2 + (Fintype.card ι : ℝ) / s * (‖θ‖ ^ 2 / 2) := by
          ring
        rw [e1, e2]
        linarith [key]
      linarith [h3, hp]
    refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
    refine (rbMeasure_real_avg_rbX_gt_le hr hK (by positivity)).trans (le_of_eq ?_)
    congr 2
    have h1 : (‖θ‖ ^ 2 / 2) ^ 2 / (32 * ‖θ‖ ^ 4) = 1 / 128 := by
      field_simp
      ring
    have h2 : ‖θ‖ ^ 2 / 2 / (8 * ‖θ‖ ^ 2) = 1 / 16 := by
      field_simp
      ring
    rw [h1, h2, min_eq_left (by norm_num)]
    ring

end Term2

end Maiti2026Power
