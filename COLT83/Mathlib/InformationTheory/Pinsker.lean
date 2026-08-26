/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Pinsker's inequality for a single event

We prove **Pinsker's inequality** in the form `2 (μ A - ν A)² ≤ KL(μ ‖ ν)` for probability
measures `μ ν` and a measurable set `A`.

The proof goes through the Bernoulli case: for the Bernoulli measures `bernoulliBool p` and
`bernoulliBool q` on `Bool`, the Kullback-Leibler divergence is the binary divergence
`klBin p q = p * log (p / q) + (1 - p) * log ((1 - p) / (1 - q))`, which dominates `2 (p - q)²`
by a calculus argument. The general case follows from the data processing inequality
`klDiv_map_le` applied to the map `ω ↦ decide (ω ∈ A)`.

## Main results

* `klBin_pinsker`: `2 * (p - q) ^ 2 ≤ klBin p q` for `p ∈ [0, 1]` and `q ∈ (0, 1)`.
* `klDiv_bernoulliBool`: `klDiv (bernoulliBool p) (bernoulliBool q) = ENNReal.ofReal (klBin p q)`.
* `pinsker_measureReal`: `ENNReal.ofReal (2 * (μ.real A - ν.real A) ^ 2) ≤ klDiv μ ν`.
* `abs_sub_le_sqrt_klDiv`: `|μ.real A - ν.real A| ≤ √((klDiv μ ν).toReal / 2)`.
-/

@[expose] public section

open MeasureTheory Real Set
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

/-! ### Bernoulli measures on `Bool` -/

/-- The Bernoulli measure on `Bool` with parameter `p : ℝ`: mass `p` on `true` and `1 - p` on
`false` (for `p ∈ [0, 1]`; negative masses are truncated to `0`). -/
noncomputable def bernoulliBool (p : ℝ) : Measure Bool :=
  p.toNNReal • Measure.dirac true + (1 - p).toNNReal • Measure.dirac false

/-- `bernoulliBool p` gives mass `p` to `true`. -/
@[simp] lemma bernoulliBool_singleton_true (p : ℝ) :
    bernoulliBool p {true} = ENNReal.ofReal p := by
  simp [bernoulliBool, ENNReal.ofReal]

/-- `bernoulliBool p` gives mass `1 - p` to `false`. -/
@[simp] lemma bernoulliBool_singleton_false (p : ℝ) :
    bernoulliBool p {false} = ENNReal.ofReal (1 - p) := by
  simp [bernoulliBool, ENNReal.ofReal]

/-- `bernoulliBool p` is a finite measure for every real `p`. -/
instance (p : ℝ) : IsFiniteMeasure (bernoulliBool p) := by unfold bernoulliBool; infer_instance

/-- `bernoulliBool p` is a probability measure when `p ∈ [0, 1]`. -/
lemma isProbabilityMeasure_bernoulliBool {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliBool p) where
  measure_univ := by
    rw [Bool.univ_eq, Set.insert_eq, measure_union (by simp) (measurableSet_singleton _),
      bernoulliBool_singleton_false, bernoulliBool_singleton_true,
      ← ENNReal.ofReal_add (sub_nonneg.2 hp1) hp, sub_add_cancel, ENNReal.ofReal_one]

/-- The Bernoulli measure `bernoulliBool p` has density `p / q` on `true` and `(1 - p) / (1 - q)`
on `false` with respect to `bernoulliBool q`. -/
lemma bernoulliBool_eq_withDensity {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    bernoulliBool p = (bernoulliBool q).withDensity
      (fun b ↦ bif b then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q))) := by
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [withDensity_apply _ (measurableSet_singleton b), lintegral_singleton]
  cases b
  · simp only [Bool.cond_false, bernoulliBool_singleton_false]
    rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ (sub_pos.2 hq1).ne']
  · simp only [Bool.cond_true, bernoulliBool_singleton_true]
    rw [← ENNReal.ofReal_mul (by positivity), div_mul_cancel₀ _ hq.ne']

/-- The Kullback-Leibler divergence between two Bernoulli measures is the binary divergence. -/
lemma klDiv_bernoulliBool {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 < q) (hq1 : q < 1) :
    klDiv (bernoulliBool p) (bernoulliBool q) = ENNReal.ofReal (klBin p q) := by
  set f : Bool → ℝ≥0∞ :=
    fun b ↦ bif b then ENNReal.ofReal (p / q) else ENNReal.ofReal ((1 - p) / (1 - q)) with hf
  have h_eq := bernoulliBool_eq_withDensity hp hp1 hq hq1
  have h_ac : bernoulliBool p ≪ bernoulliBool q := h_eq ▸ withDensity_absolutelyContinuous _ _
  have h_rn : (bernoulliBool p).rnDeriv (bernoulliBool q) =ᵐ[bernoulliBool q] f :=
    h_eq ▸ Measure.rnDeriv_withDensity _ Measurable.of_discrete
  rw [klDiv_eq_lintegral_klFun_of_ac h_ac,
    lintegral_congr_ae (h_rn.mono fun x hx ↦ by rw [hx]), lintegral_fintype, Fintype.sum_bool]
  simp only [hf, Bool.cond_true, Bool.cond_false, bernoulliBool_singleton_true,
    bernoulliBool_singleton_false, ENNReal.toReal_ofReal (div_nonneg hp hq.le),
    ENNReal.toReal_ofReal (div_nonneg (sub_nonneg.2 hp1) (sub_pos.2 hq1).le)]
  have h1 : 0 ≤ klFun (p / q) := klFun_nonneg (by positivity)
  have h2 : 0 ≤ klFun ((1 - p) / (1 - q)) := klFun_nonneg (div_nonneg (by linarith) (by linarith))
  rw [← ENNReal.ofReal_mul h1, ← ENNReal.ofReal_mul h2, ← ENNReal.ofReal_add (by positivity)
    (mul_nonneg h2 (by linarith))]
  congr 1
  have hq' : q ≠ 0 := hq.ne'
  have hq1' : 1 - q ≠ 0 := (sub_pos.2 hq1).ne'
  simp only [klFun, klBin]
  field_simp
  ring

/-- Bernoulli Pinsker inequality in `ℝ≥0∞`, for all parameters in `[0, 1]`. -/
lemma ofReal_le_klDiv_bernoulliBool {p q : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (hq : 0 ≤ q)
    (hq1 : q ≤ 1) :
    ENNReal.ofReal (2 * (p - q) ^ 2) ≤ klDiv (bernoulliBool p) (bernoulliBool q) := by
  rcases eq_or_ne p q with rfl | hpq
  · simp
  rcases hq.eq_or_lt with rfl | hq
  · rw [klDiv_of_not_ac]
    · exact le_top
    · intro h
      have := h (s := {true}) (by simp)
      simp only [bernoulliBool_singleton_true, ENNReal.ofReal_eq_zero] at this
      exact hpq (le_antisymm this hp)
  rcases hq1.eq_or_lt with rfl | hq1
  · rw [klDiv_of_not_ac]
    · exact le_top
    · intro h
      have := h (s := {false}) (by simp)
      simp only [bernoulliBool_singleton_false, ENNReal.ofReal_eq_zero, sub_nonpos] at this
      exact hpq (le_antisymm hp1 this)
  rw [klDiv_bernoulliBool hp hp1 hq hq1]
  exact ENNReal.ofReal_le_ofReal (klBin_pinsker hp hp1 hq hq1)

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
measure with parameter `μ.real A`. -/
lemma map_decide_mem_eq_bernoulliBool [IsProbabilityMeasure μ] [DecidablePred (· ∈ A)]
    (hA : MeasurableSet A) :
    μ.map (fun ω ↦ decide (ω ∈ A)) = bernoulliBool (μ.real A) := by
  refine Measure.ext_of_singleton fun b ↦ ?_
  rw [Measure.map_apply (measurable_decide_mem hA) (measurableSet_singleton b)]
  cases b
  · rw [preimage_decide_mem_singleton_false, bernoulliBool_singleton_false,
      ← probReal_univ (μ := μ), ← measureReal_compl hA, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  · rw [preimage_decide_mem_singleton_true, bernoulliBool_singleton_true, measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- **Pinsker's inequality** for a single event: `2 (μ A - ν A)² ≤ KL(μ ‖ ν)`. -/
theorem pinsker_measureReal [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : MeasurableSet A) :
    ENNReal.ofReal (2 * (μ.real A - ν.real A) ^ 2) ≤ klDiv μ ν := by
  classical
  calc ENNReal.ofReal (2 * (μ.real A - ν.real A) ^ 2)
      ≤ klDiv (μ.map fun ω ↦ decide (ω ∈ A)) (ν.map fun ω ↦ decide (ω ∈ A)) := by
        rw [map_decide_mem_eq_bernoulliBool hA, map_decide_mem_eq_bernoulliBool hA]
        exact ofReal_le_klDiv_bernoulliBool measureReal_nonneg measureReal_le_one
          measureReal_nonneg measureReal_le_one
    _ ≤ klDiv μ ν := klDiv_map_le μ ν (measurable_decide_mem hA)

/-- **Pinsker's inequality** for a single event, real form:
`|μ A - ν A| ≤ √(KL(μ ‖ ν) / 2)`. -/
theorem abs_sub_le_sqrt_klDiv [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hA : MeasurableSet A) (h : klDiv μ ν ≠ ∞) :
    |μ.real A - ν.real A| ≤ √((klDiv μ ν).toReal / 2) := by
  have := pinsker_measureReal (μ := μ) (ν := ν) hA
  rw [ENNReal.ofReal_le_iff_le_toReal h] at this
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

end InformationTheory
