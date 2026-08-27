/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import COLT83.Mathlib.Probability.Distributions.Bernoulli

/-!
# Pinsker's inequality for a single event

We prove **Pinsker's inequality** in the form `2 (μ A - ν A)² ≤ KL(μ ‖ ν)` for probability
measures `μ ν` and a measurable set `A`.

The proof goes through the Bernoulli case: for the Bernoulli measures `Ber(x, y, p)` and
`Ber(x, y, q)` (Mathlib's `ProbabilityTheory.bernoulliMeasure`, `p q : unitInterval`), the
Kullback-Leibler divergence is the binary divergence
`klBin p q = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))`, which dominates `2 (p - q)²`
by a calculus argument. The general case follows from the data processing inequality
`klDiv_map_le` applied to the map `ω ↦ decide (ω ∈ A)`, whose image measure is the Bernoulli
measure `Ber(true, false, μ.real A)` (`map_decide_mem_eq_bernoulliMeasure`).

## Main results

* `klBin_pinsker`: `2 * (p - q) ^ 2 ≤ klBin p q` for `p ∈ [0, 1]` and `q ∈ (0, 1)`.
* `klDiv_bernoulliMeasure`: `klDiv Ber(x, y, p) Ber(x, y, q) = ENNReal.ofReal (klBin p q)` for
  `x ≠ y` and `0 < q < 1`.
* `ofReal_le_klDiv_bernoulliMeasure`: `ENNReal.ofReal (2 * (p - q) ^ 2) ≤ klDiv Ber(x, y, p)
  Ber(x, y, q)` for all `p q : unitInterval`.
* `pinsker_measureReal`: `ENNReal.ofReal (2 * (μ.real A - ν.real A) ^ 2) ≤ klDiv μ ν`.
* `abs_sub_le_sqrt_klDiv`: `|μ.real A - ν.real A| ≤ √((klDiv μ ν).toReal / 2)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set unitInterval
open scoped ENNReal

namespace InformationTheory

/-! ### The binary Kullback-Leibler divergence -/

/-- The Kullback-Leibler divergence between Bernoulli distributions with parameters `p` and `q`,
`p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))`. -/
noncomputable def klBin (p q : ℝ) : ℝ := p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))

/-- Unfolding lemma for `klBin`. -/
lemma klBin_apply (p q : ℝ) :
    klBin p q = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q)) := rfl

/-- The binary divergence is invariant under the swap of the two outcomes. -/
lemma klBin_one_sub (p q : ℝ) : klBin (1 - p) (1 - q) = klBin p q := by
  simp only [klBin, sub_sub_cancel]
  ring

/-- The binary divergence between identical parameters vanishes. -/
@[simp] lemma klBin_self (p : ℝ) : klBin p p = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [klBin]
  rcases eq_or_ne p 1 with rfl | hp1
  · simp [klBin]
  simp [klBin, div_self hp, sub_ne_zero.2 hp1.symm]

/-- `a * log (a / b) = a * (log a - log b)`, also when `a = 0` thanks to `log 0 = 0`. -/
lemma mul_log_div_eq_mul_sub {a b : ℝ} (hb : b ≠ 0) : a * log (a / b) = a * (log a - log b) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [log_div ha hb]

/-- The binary divergence written without divisions inside the logarithms. -/
lemma klBin_eq_of_ne {p q : ℝ} (hq : q ≠ 0) (hq1 : q ≠ 1) :
    klBin p q = p * (log p - log q) + (1 - p) * (log (1 - p) - log (1 - q)) := by
  rw [klBin, mul_log_div_eq_mul_sub hq, mul_log_div_eq_mul_sub (sub_ne_zero.2 hq1.symm)]

/-- Auxiliary function for the proof of the binary Pinsker inequality: the difference
`klBin p q - 2 * (p - q) ^ 2`, written as a function of `q` without divisions inside
the logarithms. -/
noncomputable def klBinGap (p q : ℝ) : ℝ :=
  p * (log p - log q) + (1 - p) * (log (1 - p) - log (1 - q)) - 2 * (p - q) ^ 2

/-- Derivative of `klBinGap p` in the second variable, in factored form: its sign is the sign
of `q - p` on `(0, 1)`. -/
lemma hasDerivAt_klBinGap {p q : ℝ} (hq : q ≠ 0) (hq1 : q ≠ 1) :
    HasDerivAt (klBinGap p) ((q - p) * (1 - 2 * q) ^ 2 / (q * (1 - q))) q := by
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

/-- `klBinGap p` is continuous on `[p, 1)` for `0 ≤ p` (including at `p = 0`, where the
logarithmic term has a zero coefficient). -/
lemma continuousOn_klBinGap {p : ℝ} (hp : 0 ≤ p) : ContinuousOn (klBinGap p) (Ico p 1) := by
  have h1 : ContinuousOn (fun x ↦ p * (log p - log x)) (Ico p 1) := by
    rcases hp.eq_or_lt with rfl | hp
    · simp [continuousOn_const]
    · exact continuousOn_const.mul (continuousOn_const.sub
        (continuousOn_log.mono fun x hx ↦ (hp.trans_le hx.1).ne'))
  have h2 : ContinuousOn (fun x ↦ (1 - p) * (log (1 - p) - log (1 - x))) (Ico p 1) :=
    continuousOn_const.mul (continuousOn_const.sub
      ((continuousOn_const.sub continuousOn_id).log fun x hx ↦ (sub_pos.2 hx.2).ne'))
  exact (h1.add h2).sub (by fun_prop)

/-- `klBinGap p` vanishes at `q = p`. -/
lemma klBinGap_self (p : ℝ) : klBinGap p p = 0 := by simp [klBinGap]

/-- Binary Pinsker inequality when `p ≤ q`. -/
lemma sq_le_klBin_of_le {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ klBin p q := by
  rcases (hp.trans hpq).eq_or_lt with rfl | hq0
  · obtain rfl : p = 0 := le_antisymm hpq hp
    simp
  have hmono : MonotoneOn (klBinGap p) (Ico p 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico p 1) (continuousOn_klBinGap hp)
      (f' := fun q ↦ (q - p) * (1 - 2 * q) ^ 2 / (q * (1 - q))) (fun x hx ↦ ?_) fun x hx ↦ ?_
    · rw [interior_Ico] at hx ⊢
      exact (hasDerivAt_klBinGap (hp.trans_lt hx.1).ne' hx.2.ne).hasDerivWithinAt
    · rw [interior_Ico] at hx
      exact div_nonneg (mul_nonneg (sub_nonneg.2 hx.1.le) (sq_nonneg _))
        (mul_pos (hp.trans_lt hx.1) (sub_pos.2 hx.2)).le
  have h := hmono ⟨le_rfl, hpq.trans_lt hq1⟩ ⟨hpq, hq1⟩ hpq
  rw [klBinGap_self] at h
  unfold klBinGap at h
  rw [klBin_eq_of_ne hq0.ne' hq1.ne]
  linarith

/-- **Binary Pinsker inequality**: `2 * (p - q) ^ 2 ≤ klBin p q` for `p ∈ [0, 1]`, `q ∈ (0, 1)`. -/
lemma klBin_pinsker {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    2 * (p - q) ^ 2 ≤ klBin p q := by
  rcases le_or_gt p q with hpq | hpq
  · exact sq_le_klBin_of_le hp hpq hq1
  · have := sq_le_klBin_of_le (sub_nonneg.2 hp1) (sub_le_sub_left hpq.le 1) (by linarith)
    rw [klBin_one_sub, sub_sub_sub_cancel_left] at this
    linarith [this, show (p - q) ^ 2 = (q - p) ^ 2 by ring]

/-! ### Bernoulli measures -/

section bernoulli

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] {x y : X}

/-- The Kullback-Leibler divergence between two Bernoulli measures `Ber(x, y, p)` and
`Ber(x, y, q)` (Mathlib's `ProbabilityTheory.bernoulliMeasure`), for `x ≠ y` and `0 < q < 1`, is
the binary divergence `klBin p q`. -/
lemma klDiv_bernoulliMeasure (hxy : x ≠ y) (p : I) {q : I} (hq : (q : ℝ) ≠ 0)
    (hq1 : (q : ℝ) ≠ 1) :
    klDiv Ber(x, y, p) Ber(x, y, q) = ENNReal.ofReal (klBin p q) := by
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
  simp only [klFun, klBin]
  field_simp
  ring

/-- Bernoulli Pinsker inequality in `ℝ≥0∞`, for all parameters in `[0, 1]`:
`2 (p - q) ^ 2 ≤ KL(Ber(x, y, p) ‖ Ber(x, y, q))` (the divergence is infinite when `q ∈ {0, 1}`
and `p ≠ q`). -/
lemma ofReal_le_klDiv_bernoulliMeasure (hxy : x ≠ y) (p q : I) :
    ENNReal.ofReal (2 * (p - q) ^ 2) ≤ klDiv Ber(x, y, p) Ber(x, y, q) := by
  rcases eq_or_ne p q with rfl | hpq
  · simp
  have hpq' : (p : ℝ) ≠ q := fun h ↦ hpq (Subtype.ext h)
  rcases eq_or_ne (q : ℝ) 0 with hq | hq
  · rw [klDiv_of_not_ac]
    · exact le_top
    · intro h
      have := h (s := {x}) (by rw [bernoulliMeasure_apply_singleton_left hxy, hq]; simp)
      rw [bernoulliMeasure_apply_singleton_left hxy, ENNReal.ofReal_eq_zero] at this
      exact hpq' (by rw [hq]; exact le_antisymm this p.2.1)
  rcases eq_or_ne (q : ℝ) 1 with hq1 | hq1
  · rw [klDiv_of_not_ac]
    · exact le_top
    · intro h
      have := h (s := {y}) (by rw [bernoulliMeasure_apply_singleton_right hxy, hq1]; simp)
      rw [bernoulliMeasure_apply_singleton_right hxy, ENNReal.ofReal_eq_zero, sub_nonpos] at this
      exact hpq' (by rw [hq1]; exact le_antisymm p.2.2 this)
  rw [klDiv_bernoulliMeasure hxy p hq hq1]
  exact ENNReal.ofReal_le_ofReal
    (klBin_pinsker p.2.1 p.2.2 (lt_of_le_of_ne q.2.1 hq.symm) (lt_of_le_of_ne q.2.2 hq1))

end bernoulli

/-! ### Pinsker's inequality -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ ν : Measure Ω} {A : Set Ω}

/-- The preimage of `{true}` by the indicator `ω ↦ decide (ω ∈ A)` is `A`. -/
lemma preimage_decide_mem_singleton_true [DecidablePred (· ∈ A)] :
    (fun ω ↦ decide (ω ∈ A)) ⁻¹' {true} = A := by ext; simp

/-- The preimage of `{false}` by the indicator `ω ↦ decide (ω ∈ A)` is `Aᶜ`. -/
lemma preimage_decide_mem_singleton_false [DecidablePred (· ∈ A)] :
    (fun ω ↦ decide (ω ∈ A)) ⁻¹' {false} = Aᶜ := by ext; simp

/-- The indicator `ω ↦ decide (ω ∈ A)` of a measurable set is measurable. -/
lemma measurable_decide_mem [DecidablePred (· ∈ A)] (hA : MeasurableSet A) :
    Measurable fun ω ↦ decide (ω ∈ A) :=
  measurable_to_bool (by rw [preimage_decide_mem_singleton_true]; exact hA)

/-- The pushforward of a probability measure by the indicator of a set `A` is the Bernoulli
measure `Ber(true, false, μ.real A)`. -/
lemma map_decide_mem_eq_bernoulliMeasure [IsProbabilityMeasure μ] [DecidablePred (· ∈ A)]
    (hA : MeasurableSet A) :
    μ.map (fun ω ↦ decide (ω ∈ A)) =
      Ber(true, false, ⟨μ.real A, measureReal_nonneg, measureReal_le_one⟩) := by
  have htf : (true : Bool) ≠ false := by decide
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [Measure.map_apply (measurable_decide_mem hA) (measurableSet_singleton b)]
  cases b
  · rw [preimage_decide_mem_singleton_false, bernoulliMeasure_apply_singleton_right htf]
    dsimp only
    rw [← probReal_univ (μ := μ), ← measureReal_compl hA, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · rw [preimage_decide_mem_singleton_true, bernoulliMeasure_apply_singleton_left htf]
    dsimp only
    rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Pinsker's inequality** for a single event: `2 (μ A - ν A)² ≤ KL(μ ‖ ν)`. -/
theorem pinsker_measureReal [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : MeasurableSet A) :
    ENNReal.ofReal (2 * (μ.real A - ν.real A) ^ 2) ≤ klDiv μ ν := by
  classical
  calc ENNReal.ofReal (2 * (μ.real A - ν.real A) ^ 2)
      ≤ klDiv (μ.map fun ω ↦ decide (ω ∈ A)) (ν.map fun ω ↦ decide (ω ∈ A)) := by
        rw [map_decide_mem_eq_bernoulliMeasure hA, map_decide_mem_eq_bernoulliMeasure hA]
        exact ofReal_le_klDiv_bernoulliMeasure (by decide) _ _
    _ ≤ klDiv μ ν := klDiv_map_le μ ν (measurable_decide_mem hA)

/-- **Pinsker's inequality** for a single event, real form:
`|μ A - ν A| ≤ √(KL(μ ‖ ν) / 2)`. -/
lemma abs_sub_le_sqrt_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : MeasurableSet A) (h : klDiv μ ν ≠ ∞) :
    |μ.real A - ν.real A| ≤ √((klDiv μ ν).toReal / 2) := by
  have := pinsker_measureReal (μ := μ) (ν := ν) hA
  rw [ENNReal.ofReal_le_iff_le_toReal h] at this
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

end InformationTheory
