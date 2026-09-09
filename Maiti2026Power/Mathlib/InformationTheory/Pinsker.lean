/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Maiti2026Power.Mathlib.InformationTheory.KLBer
public import Maiti2026Power.Mathlib.Probability.Distributions.Bernoulli

/-!
# Pinsker's inequality for a single event

We prove **Pinsker's inequality** in the form `2 (μ A - ν A)² ≤ KL(μ ‖ ν)` for probability
measures `μ ν` and a measurable set `A`.

The proof goes through the Bernoulli case: for the Bernoulli measures `Ber(x, y, p)` and
`Ber(x, y, q)` (Mathlib's `ProbabilityTheory.bernoulliMeasure`, `p q : unitInterval`), the
Kullback-Leibler divergence is the binary divergence `klBer p q`
(`Maiti2026Power/Mathlib/InformationTheory/KLBer.lean`), which dominates `2 (p - q)²` by a
calculus argument. The general case follows from the data processing inequality
`klDiv_map_le` applied to the map `ω ↦ (ω ∈ A)`, whose image measure is the Bernoulli
measure `Ber(True, False, μ.real A)` (`map_mem_eq_bernoulliMeasure`).

## Main results

* `sq_sub_le_klBerReal`: `2 * (p - q) ^ 2 ≤ klBerReal p q` for `p ∈ [0, 1]` and `q ∈ (0, 1)`;
  `sq_sub_le_klBer`: `ENNReal.ofReal (2 * (p - q) ^ 2) ≤ klBer p q` for `p, q ∈ [0, 1]`.
* `klDiv_bernoulliMeasure`: `klDiv Ber(x, y, p) Ber(x, y, q) = klBer p q` for `x ≠ y`, and
  `klDiv_bernoulliMeasure_eq_klBerReal`, its `ENNReal.ofReal (klBerReal p q)` form for
  `0 < q < 1`.
* `ofReal_le_klDiv_bernoulliMeasure`: `ENNReal.ofReal (2 * (p - q) ^ 2) ≤ klDiv Ber(x, y, p)
  Ber(x, y, q)` for all `p q : unitInterval`.
* `sq_sub_le_klDiv`: `ENNReal.ofReal (2 * (μ.real A - ν.real A) ^ 2) ≤ klDiv μ ν`.
* `abs_sub_le_sqrt_klDiv`: `|μ.real A - ν.real A| ≤ √((klDiv μ ν).toReal / 2)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set unitInterval
open scoped ENNReal

namespace InformationTheory

/-! ### The binary Pinsker inequality -/

/-- Auxiliary function for the proof of the binary Pinsker inequality: the difference
`klBerReal p q - 2 * (p - q) ^ 2`, written as a function of `q` without divisions inside
the logarithms. -/
noncomputable def klBerRealGap (p q : ℝ) : ℝ :=
  p * (log p - log q) + (1 - p) * (log (1 - p) - log (1 - q)) - 2 * (p - q) ^ 2

/-- Derivative of `klBerRealGap p` in the second variable, in factored form: its sign is the sign
of `q - p` on `(0, 1)`. -/
lemma hasDerivAt_klBerRealGap {p q : ℝ} (hq : q ≠ 0) (hq1 : q ≠ 1) :
    HasDerivAt (klBerRealGap p) ((q - p) * (1 - 2 * q) ^ 2 / (q * (1 - q))) q := by
  have hq1' : 1 - q ≠ 0 := sub_ne_zero.2 hq1.symm
  have h1 : HasDerivAt (fun x ↦ p * (log p - log x)) (p * (-q⁻¹)) q :=
    ((hasDerivAt_log hq).const_sub (log p)).const_mul p
  have h2 : HasDerivAt (fun x ↦ (1 - p) * (log (1 - p) - log (1 - x)))
      ((1 - p) * (-(-1 / (1 - q)))) q :=
    ((((hasDerivAt_id' (x := q)).const_sub 1).log hq1').const_sub (log (1 - p))).const_mul (1 - p)
  have h3 := (((hasDerivAt_id' (x := q)).const_sub p).pow 2).const_mul 2
  refine ((h1.add h2).sub h3).congr_deriv ?_
  simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one]
  field_simp
  ring

/-- `klBerRealGap p` is continuous on `[p, 1)` for `0 ≤ p` (including at `p = 0`, where the
logarithmic term has a zero coefficient). -/
lemma continuousOn_klBerRealGap {p : ℝ} (hp : 0 ≤ p) : ContinuousOn (klBerRealGap p) (Ico p 1) := by
  have h1 : ContinuousOn (fun x ↦ p * (log p - log x)) (Ico p 1) := by
    rcases hp.eq_or_lt with rfl | hp
    · simp [continuousOn_const]
    · exact continuousOn_const.mul (continuousOn_const.sub
        (continuousOn_log.mono fun x hx ↦ (hp.trans_le hx.1).ne'))
  have h2 : ContinuousOn (fun x ↦ (1 - p) * (log (1 - p) - log (1 - x))) (Ico p 1) :=
    continuousOn_const.mul (continuousOn_const.sub
      ((continuousOn_const.sub continuousOn_id).log fun x hx ↦ (sub_pos.2 hx.2).ne'))
  exact (h1.add h2).sub (by fun_prop)

/-- `klBerRealGap p` vanishes at `q = p`. -/
lemma klBerRealGap_self (p : ℝ) : klBerRealGap p p = 0 := by simp [klBerRealGap]

/-- Binary Pinsker inequality when `p ≤ q`. -/
lemma sq_le_klBerReal_of_le {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ klBerReal p q := by
  rcases (hp.trans hpq).eq_or_lt with rfl | hq0
  · obtain rfl : p = 0 := le_antisymm hpq hp
    simp
  have hmono : MonotoneOn (klBerRealGap p) (Ico p 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico p 1) (continuousOn_klBerRealGap hp)
      (f' := fun q ↦ (q - p) * (1 - 2 * q) ^ 2 / (q * (1 - q))) (fun x hx ↦ ?_) fun x hx ↦ ?_
    · rw [interior_Ico] at hx ⊢
      exact (hasDerivAt_klBerRealGap (hp.trans_lt hx.1).ne' hx.2.ne).hasDerivWithinAt
    · rw [interior_Ico] at hx
      exact div_nonneg (mul_nonneg (sub_nonneg.2 hx.1.le) (sq_nonneg _))
        (mul_pos (hp.trans_lt hx.1) (sub_pos.2 hx.2)).le
  have h := hmono ⟨le_rfl, hpq.trans_lt hq1⟩ ⟨hpq, hq1⟩ hpq
  rw [klBerRealGap_self] at h
  unfold klBerRealGap at h
  rw [klBerReal_eq_of_ne hq0.ne' hq1.ne]
  linarith

/-- **Binary Pinsker inequality**: `2 * (p - q) ^ 2 ≤ klBerReal p q` for `p ∈ [0, 1]` and
`q ∈ (0, 1)`. -/
lemma sq_sub_le_klBerReal {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ klBerReal p q := by
  rcases le_or_gt p q with hpq | hpq
  · exact sq_le_klBerReal_of_le hp hpq hq1
  · have := sq_le_klBerReal_of_le (sub_nonneg.2 hp1) (sub_le_sub_left hpq.le 1) (by linarith)
    rw [klBerReal_one_sub, sub_sub_sub_cancel_left] at this
    linarith [this, show (p - q) ^ 2 = (q - p) ^ 2 by ring]

/-- **Binary Pinsker inequality**: `2 * (p - q) ^ 2 ≤ klBer p q` for `p, q ∈ [0, 1]`. -/
lemma sq_sub_le_klBer {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    ENNReal.ofReal (2 * (p - q) ^ 2) ≤ klBer p q := by
  by_cases hq0 : q = 0
  · by_cases hp0 : p = 0
    · simp [hq0, hp0]
    · simp [hq0, klBer_zero_right, hp0]
  by_cases hq1' : q = 1
  · by_cases hp1' : p = 1
    · simp [hq1', hp1']
    · simp [hq1', klBer_one_right, hp1']
  have hq0' : 0 < q := lt_of_le_of_ne' hq hq0
  have hq1' : q < 1 := lt_of_le_of_ne hq1 hq1'
  rw [klBer_eq_ofReal hq0'.ne' hq1'.ne]
  exact ENNReal.ofReal_le_ofReal (sq_sub_le_klBerReal hp hp1 hq0' hq1')

/-! ### Bernoulli measures -/

section bernoulli

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {x y : X}

/-- The Kullback-Leibler divergence between two Bernoulli measures `Ber(x, y, p)` and
`Ber(x, y, q)` (Mathlib's `ProbabilityTheory.bernoulliMeasure`), for `x ≠ y` and `0 < q < 1`, is
the binary divergence `klBerReal p q`. -/
lemma klDiv_bernoulliMeasure_eq_klBerReal (hxy : x ≠ y) (p : I) {q : I} (hq : (q : ℝ) ≠ 0)
    (hq1 : (q : ℝ) ≠ 1) :
    klDiv Ber(x, y, p) Ber(x, y, q) = ENNReal.ofReal (klBerReal p q) := by
  classical
  have hq0 : (0 : ℝ) < q := lt_of_le_of_ne q.2.1 hq.symm
  have hq1' : (0 : ℝ) < 1 - q := sub_pos.2 (lt_of_le_of_ne q.2.2 hq1)
  have hp0 : (0 : ℝ) ≤ p := p.2.1
  have hp1 : (0 : ℝ) ≤ 1 - p := sub_nonneg.2 p.2.2
  rw [klDiv_eq_lintegral_klFun_of_ac (bernoulliMeasure_absolutelyContinuous hxy p hq hq1),
    lintegral_congr_ae ((rnDeriv_bernoulliMeasure hxy p hq hq1).mono fun z hz ↦ by rw [hz]),
    lintegral_bernoulliMeasure]
  simp only [ite_true, ite_eq_right hxy.symm, ENNReal.toReal_ofReal (div_nonneg hp0 hq0.le),
    ENNReal.toReal_ofReal (div_nonneg hp1 hq1'.le)]
  rw [← ENNReal.ofReal_mul hq0.le, ← ENNReal.ofReal_mul hq1'.le, ← ENNReal.ofReal_add
      (mul_nonneg hq0.le (klFun_nonneg (div_nonneg hp0 hq0.le)))
      (mul_nonneg hq1'.le (klFun_nonneg (div_nonneg hp1 hq1'.le)))]
  congr 1
  simp only [klFun, klBerReal]
  field

/-- The Kullback-Leibler divergence between two Bernoulli measures `Ber(x, y, p)` and
`Ber(x, y, q)` (Mathlib's `ProbabilityTheory.bernoulliMeasure`), for `x ≠ y`, is
the binary divergence `klBer p q`. -/
lemma klDiv_bernoulliMeasure (hxy : x ≠ y) (p q : I) :
    klDiv Ber(x, y, p) Ber(x, y, q) = klBer p q := by
  by_cases hq0 : (q : ℝ) = 0
  · simp only [Icc.coe_eq_zero] at hq0
    simp only [hq0, bernoulliMeasure_zero, Icc.coe_zero, klBer_zero_right, Icc.coe_eq_zero]
    split_ifs with hp0
    · simp [hp0]
    · rw [klDiv_of_not_ac]
      intro h
      have hdx : Measure.dirac y {x} = 0 := by simp [hxy.symm]
      have hx := h hdx
      rw [bernoulliMeasure_apply_singleton_left hxy, ENNReal.ofReal_eq_zero] at hx
      exact hp0 (Icc.coe_eq_zero.mp (le_antisymm hx p.2.1))
  by_cases hq1 : (q : ℝ) = 1
  · simp only [Icc.coe_eq_one] at hq1
    simp only [hq1, bernoulliMeasure_one, Icc.coe_one, klBer_one_right, Icc.coe_eq_one]
    split_ifs with hp1
    · simp [hp1]
    · rw [klDiv_of_not_ac]
      intro h
      have hdy : Measure.dirac x {y} = 0 := by simp [hxy]
      have hy := h hdy
      rw [bernoulliMeasure_apply_singleton_right hxy, ENNReal.ofReal_eq_zero, sub_nonpos] at hy
      exact hp1 (Icc.coe_eq_one.mp (le_antisymm p.2.2 hy))
  rw [klDiv_bernoulliMeasure_eq_klBerReal hxy p hq0 hq1, klBer_eq_ofReal hq0 hq1]

/-- Bernoulli Pinsker inequality in `ℝ≥0∞`, for all parameters in `[0, 1]`:
`2 (p - q) ^ 2 ≤ KL(Ber(x, y, p) ‖ Ber(x, y, q))` (the divergence is infinite when `q ∈ {0, 1}`
and `p ≠ q`). -/
lemma ofReal_le_klDiv_bernoulliMeasure (hxy : x ≠ y) (p q : I) :
    ENNReal.ofReal (2 * (p - q) ^ 2) ≤ klDiv Ber(x, y, p) Ber(x, y, q) :=
  (sq_sub_le_klBer p.2.1 p.2.2 q.2.1 q.2.2).trans_eq (klDiv_bernoulliMeasure hxy p q).symm

end bernoulli

/-! ### Pinsker's inequality -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {A : Set Ω}

/-- The pushforward of a probability measure by the `Prop`-valued membership map `ω ↦ ω ∈ A` is
the Bernoulli measure `Ber(True, False, μ.real A)`. -/
lemma map_mem_eq_bernoulliMeasure [IsProbabilityMeasure μ] (hA : MeasurableSet A) :
    μ.map (· ∈ A) =
      Ber(True, False, ⟨μ.real A, measureReal_nonneg, measureReal_le_one⟩) := by
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [Measure.map_apply hA.mem (measurableSet_singleton b)]
  by_cases hb : b
  · simp only [hb, preimage_singleton_true, ofPred_mem_eq, MeasurableSpace.measurableSet_top,
      mem_singleton_iff, eq_iff_iff, iff_true, not_false_eq_true,
      bernoulliMeasure_apply_of_mem_of_notMem]
    rw [coe_toNNReal_eq_ofReal]
    dsimp only
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · simp only [hb, preimage_singleton_false, MeasurableSpace.measurableSet_top, mem_singleton_iff,
      eq_iff_iff, iff_false, not_true_eq_false, not_false_eq_true,
      bernoulliMeasure_apply_of_notMem_of_mem]
    change μ Aᶜ = _
    rw [coe_toNNReal_eq_ofReal, coe_symm_eq]
    dsimp only
    rw [← probReal_univ (μ := μ), ← measureReal_compl hA, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Pinsker's inequality** for a single event: `2 (μ A - ν A)² ≤ KL(μ ‖ ν)`. -/
theorem sq_sub_le_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : MeasurableSet A) :
    ENNReal.ofReal (2 * (μ.real A - ν.real A) ^ 2) ≤ klDiv μ ν := by
  classical
  calc ENNReal.ofReal (2 * (μ.real A - ν.real A) ^ 2)
  _ ≤ klDiv (μ.map (· ∈ A)) (ν.map (· ∈ A)) := by
      rw [map_mem_eq_bernoulliMeasure hA, map_mem_eq_bernoulliMeasure hA]
      exact ofReal_le_klDiv_bernoulliMeasure (by decide) ⟨μ.real A, _⟩ ⟨ν.real A, _⟩
  _ ≤ klDiv μ ν := klDiv_map_le μ ν hA.mem

/-- **Pinsker's inequality** for a single event, real form:
`|μ A - ν A| ≤ √(KL(μ ‖ ν) / 2)`. -/
lemma abs_sub_le_sqrt_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : MeasurableSet A) (h : klDiv μ ν ≠ ∞) :
    |μ.real A - ν.real A| ≤ √((klDiv μ ν).toReal / 2) := by
  have := sq_sub_le_klDiv (μ := μ) (ν := ν) hA
  rw [ENNReal.ofReal_le_iff_le_toReal h] at this
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

end InformationTheory
