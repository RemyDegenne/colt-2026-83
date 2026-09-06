/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.Moments.MGFAnalytic

/-!
# Sub-exponential moment generating functions

A real random variable `X` has a sub-exponential moment generating function with parameters
`(V, b)` if for every `t` with `b * |t| ≤ 1`, `exp (t * X)` is integrable and
`mgf X μ t ≤ exp (V * t ^ 2 / 2)`. The range of `t` is written as `b * |t| ≤ 1` (rather than
`|t| ≤ 1 / b`) so that `b = 0` imposes no restriction on `t`: the case `b = 0` is exactly
Mathlib's `HasSubgaussianMGF`.

## Main results

* `HasSubexponentialMGF.integral_eq_zero`: a sub-exponential variable is integrable and centered.
* `HasSubexponentialMGF.const_mul`, `neg`, `mono`, `add_of_indepFun`, `sum_of_iIndepFun`:
  stability under scaling and independent sums.
* `HasSubexponentialMGF.measure_ge_le`, `measure_le_le`, `measure_abs_ge_le`: Bernstein-type
  tail bounds `exp (-min (t ^ 2 / (2 * V)) (t / (2 * b)))`.
* `HasSubexponentialMGF.measure_abs_average_ge_le`: tail bound for the average of independent
  sub-exponential variables.
-/

@[expose] public section

open MeasureTheory Real Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {V b : ℝ}

/-- `X` has a sub-exponential moment generating function with parameters `(V, b)`: for every
`t` with `b * |t| ≤ 1`, `exp (t * X)` is integrable and `mgf X μ t ≤ exp (V * t ^ 2 / 2)`.
For `b = 0` this is `HasSubgaussianMGF X V μ`. -/
structure HasSubexponentialMGF (X : Ω → ℝ) (V b : ℝ) (μ : Measure Ω) : Prop where
  integrable_exp_mul : ∀ t : ℝ, b * |t| ≤ 1 → Integrable (fun ω ↦ exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, b * |t| ≤ 1 → mgf X μ t ≤ exp (V * t ^ 2 / 2)

namespace HasSubexponentialMGF

lemma of_hasSubgaussianMGF {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) (b : ℝ) :
    HasSubexponentialMGF X c b μ where
  integrable_exp_mul t _ := h.integrable_exp_mul t
  mgf_le t _ := h.mgf_le t

lemma hasSubgaussianMGF (h : HasSubexponentialMGF X V 0 μ) (hV : 0 ≤ V) :
    HasSubgaussianMGF X ⟨V, hV⟩ μ where
  integrable_exp_mul t := h.integrable_exp_mul t (by simp)
  mgf_le t := h.mgf_le t (by simp)

lemma mono (h : HasSubexponentialMGF X V b μ) {V' b' : ℝ} (hV : V ≤ V') (hb : b ≤ b') :
    HasSubexponentialMGF X V' b' μ where
  integrable_exp_mul t ht :=
    h.integrable_exp_mul t ((mul_le_mul_of_nonneg_right hb (abs_nonneg t)).trans ht)
  mgf_le t ht := by
    refine (h.mgf_le t ((mul_le_mul_of_nonneg_right hb (abs_nonneg t)).trans ht)).trans ?_
    gcongr

lemma congr (h : HasSubexponentialMGF X V b μ) {Y : Ω → ℝ} (h' : X =ᵐ[μ] Y) :
    HasSubexponentialMGF Y V b μ where
  integrable_exp_mul t ht :=
    (h.integrable_exp_mul t ht).congr (by filter_upwards [h'] with ω hω; rw [hω])
  mgf_le t ht := by
    rw [← mgf_congr h']
    exact h.mgf_le t ht

lemma of_map {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {Y : Ω' → Ω} {X : Ω → ℝ} (hY : AEMeasurable Y μ) (h : HasSubexponentialMGF X V b (μ.map Y)) :
    HasSubexponentialMGF (X ∘ Y) V b μ where
  integrable_exp_mul t ht := by
    have h1 := h.integrable_exp_mul t ht
    rwa [integrable_map_measure h1.aestronglyMeasurable (by fun_prop)] at h1
  mgf_le t ht := by
    convert! h.mgf_le t ht using 1
    rw [mgf_map hY (h.integrable_exp_mul t ht).1]

lemma map_iff {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'}
    {Y : Ω' → Ω} {X : Ω → ℝ} (hY : AEMeasurable Y μ) (hX : Measurable X) :
    HasSubexponentialMGF X V b (μ.map Y) ↔ HasSubexponentialMGF (X ∘ Y) V b μ := by
  refine ⟨fun h ↦ .of_map hY h, fun h ↦ ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩⟩
  · rw [integrable_map_measure (by fun_prop) hY]
    exact h.integrable_exp_mul t ht
  · rw [mgf_map hY (by fun_prop)]
    exact h.mgf_le t ht

lemma id_map_iff (hX : AEMeasurable X μ) :
    HasSubexponentialMGF id V b (μ.map X) ↔ HasSubexponentialMGF X V b μ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩⟩
  · rw [← Function.id_comp X]
    exact .of_map hX h
  · rw [integrable_map_measure (by fun_prop) hX]
    exact h.integrable_exp_mul t ht
  · rw [mgf_id_map hX]
    exact h.mgf_le t ht

lemma congr_identDistrib {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'}
    {Y : Ω' → ℝ} (hX : HasSubexponentialMGF X V b μ) (hXY : IdentDistrib X Y μ μ') :
    HasSubexponentialMGF Y V b μ' := by
  rw [← id_map_iff hXY.aemeasurable_fst] at hX
  rwa [← id_map_iff hXY.aemeasurable_snd, ← hXY.map_eq]

protected lemma const_mul (h : HasSubexponentialMGF X V b μ) (a : ℝ) :
    HasSubexponentialMGF (fun ω ↦ a * X ω) (a ^ 2 * V) (|a| * b) μ where
  integrable_exp_mul t ht := by
    have h1 := h.integrable_exp_mul (a * t) (by rw [abs_mul, ← mul_assoc, mul_comm b]; exact ht)
    refine h1.congr (ae_of_all _ fun ω ↦ ?_)
    simp only
    ring_nf
  mgf_le t ht := by
    rw [mgf_const_mul]
    refine (h.mgf_le (a * t) (by rw [abs_mul, ← mul_assoc, mul_comm b]; exact ht)).trans
      (le_of_eq ?_)
    congr 1
    ring

lemma neg (h : HasSubexponentialMGF X V b μ) : HasSubexponentialMGF (-X) V b μ := by
  have := h.const_mul (-1)
  simp only [neg_one_mul, even_two, Even.neg_pow, one_pow, one_mul, abs_neg, abs_one] at this
  exact this

lemma eventually_mul_abs_le (b : ℝ) : ∀ᶠ t : ℝ in nhds 0, b * |t| ≤ 1 := by
  have hcont : Continuous fun t : ℝ ↦ b * |t| := by fun_prop
  have h := hcont.tendsto 0
  simp only [abs_zero, mul_zero] at h
  exact (h.eventually (gt_mem_nhds one_pos)).mono fun t ht ↦ ht.le

lemma zero_mem_interior_integrableExpSet (h : HasSubexponentialMGF X V b μ) :
    0 ∈ interior (integrableExpSet X μ) := by
  rw [mem_interior_iff_mem_nhds]
  filter_upwards [eventually_mul_abs_le b] with t ht
  exact h.integrable_exp_mul t ht

lemma aemeasurable (h : HasSubexponentialMGF X V b μ) : AEMeasurable X μ :=
  aemeasurable_of_mem_interior_integrableExpSet h.zero_mem_interior_integrableExpSet

lemma integrable (h : HasSubexponentialMGF X V b μ) : Integrable X μ :=
  integrable_of_mem_interior_integrableExpSet h.zero_mem_interior_integrableExpSet

lemma memLp (h : HasSubexponentialMGF X V b μ) (p : ℝ≥0) : MemLp X p μ :=
  memLp_of_mem_interior_integrableExpSet h.zero_mem_interior_integrableExpSet p

lemma integrable_pow (h : HasSubexponentialMGF X V b μ) (n : ℕ) :
    Integrable (fun ω ↦ X ω ^ n) μ :=
  integrable_pow_of_mem_interior_integrableExpSet h.zero_mem_interior_integrableExpSet n

/-- A sub-exponential random variable is centered. -/
lemma integral_eq_zero (h : HasSubexponentialMGF X V b μ) [IsProbabilityMeasure μ] : μ[X] = 0 := by
  have hd : HasDerivAt (fun t ↦ mgf X μ t - exp (V * t ^ 2 / 2)) (μ[X] - 0) 0 := by
    have h1 : HasDerivAt (mgf X μ) μ[X] 0 := by
      simpa using hasDerivAt_mgf h.zero_mem_interior_integrableExpSet
    have h2 : HasDerivAt (fun t : ℝ ↦ exp (V * t ^ 2 / 2)) 0 0 := by
      have := (((hasDerivAt_pow 2 (0 : ℝ)).const_mul V).div_const 2).exp
      simpa using this
    exact h1.sub h2
  have hmax : IsLocalMax (fun t ↦ mgf X μ t - exp (V * t ^ 2 / 2)) 0 := by
    filter_upwards [eventually_mul_abs_le b] with t ht
    simp only [mgf_zero', probReal_univ, zero_pow two_ne_zero, mul_zero, zero_div, exp_zero,
      sub_self]
    linarith [h.mgf_le t ht]
  simpa using hmax.hasDerivAt_eq_zero hd

section Tail

variable [IsFiniteMeasure μ]

/-- Chernoff bound in the Gaussian regime `t * b ≤ V`. -/
lemma measure_ge_le_exp_neg_sq (h : HasSubexponentialMGF X V b μ) (hV : 0 < V) {t : ℝ}
    (ht : 0 ≤ t) (htb : t * b ≤ V) :
    μ.real {ω | t ≤ X ω} ≤ exp (-(t ^ 2 / (2 * V))) := by
  have hlam : b * |t / V| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), ← mul_div_assoc, div_le_one hV, mul_comm]
    exact htb
  calc μ.real {ω | t ≤ X ω}
      ≤ exp (-(t / V) * t) * mgf X μ (t / V) :=
        measure_ge_le_exp_mul_mgf t (by positivity) (h.integrable_exp_mul _ hlam)
    _ ≤ exp (-(t / V) * t) * exp (V * (t / V) ^ 2 / 2) := by
        gcongr
        exact h.mgf_le _ hlam
    _ = exp (-(t ^ 2 / (2 * V))) := by
        rw [← exp_add]
        congr 1
        field_simp
        ring

/-- Chernoff bound in the exponential regime `V ≤ t * b`. -/
lemma measure_ge_le_exp_neg_div (h : HasSubexponentialMGF X V b μ) (hb : 0 < b) {t : ℝ}
    (htb : V ≤ t * b) :
    μ.real {ω | t ≤ X ω} ≤ exp (-(t / (2 * b))) := by
  have hlam : b * |1 / b| ≤ 1 := by
    rw [abs_of_nonneg (by positivity), mul_one_div_cancel hb.ne']
  calc μ.real {ω | t ≤ X ω}
      ≤ exp (-(1 / b) * t) * mgf X μ (1 / b) :=
        measure_ge_le_exp_mul_mgf t (by positivity) (h.integrable_exp_mul _ hlam)
    _ ≤ exp (-(1 / b) * t) * exp (V * (1 / b) ^ 2 / 2) := by
        gcongr
        exact h.mgf_le _ hlam
    _ = exp (-(t / b) + V / (2 * b ^ 2)) := by
        rw [← exp_add]
        congr 1
        field_simp
    _ ≤ exp (-(t / (2 * b))) := by
        gcongr
        have : V / (2 * b ^ 2) ≤ t / (2 * b) := by
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
        have : t / (2 * b) = t / b - t / (2 * b) := by field_simp; ring
        linarith

/-- **Bernstein-type tail bound** for the upper tail of a sub-exponential random variable. -/
lemma measure_ge_le (h : HasSubexponentialMGF X V b μ) (hV : 0 < V) (hb : 0 < b) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ X ω} ≤ exp (-min (t ^ 2 / (2 * V)) (t / (2 * b))) := by
  rcases le_or_gt (t * b) V with htb | htb
  · exact (h.measure_ge_le_exp_neg_sq hV ht htb).trans
      (exp_le_exp.2 (neg_le_neg (min_le_left _ _)))
  · exact (h.measure_ge_le_exp_neg_div hb htb.le).trans
      (exp_le_exp.2 (neg_le_neg (min_le_right _ _)))

/-- **Bernstein-type tail bound** for the lower tail of a sub-exponential random variable. -/
lemma measure_le_le (h : HasSubexponentialMGF X V b μ) (hV : 0 < V) (hb : 0 < b) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | X ω ≤ -t} ≤ exp (-min (t ^ 2 / (2 * V)) (t / (2 * b))) := by
  have := h.neg.measure_ge_le hV hb ht
  simpa only [Pi.neg_apply, le_neg] using this

/-- **Bernstein-type tail bound**, two-sided. -/
lemma measure_abs_ge_le (h : HasSubexponentialMGF X V b μ) (hV : 0 < V) (hb : 0 < b) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |X ω|} ≤ 2 * exp (-min (t ^ 2 / (2 * V)) (t / (2 * b))) := by
  calc μ.real {ω | t ≤ |X ω|}
      ≤ μ.real ({ω | t ≤ X ω} ∪ {ω | X ω ≤ -t}) := by
        refine measureReal_mono (fun ω hω ↦ ?_) (measure_ne_top _ _)
        simp only [Set.mem_ofPred_eq, Set.mem_union] at hω ⊢
        rcases le_abs.1 hω with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (le_neg.1 h1)
    _ ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | X ω ≤ -t} := measureReal_union_le _ _
    _ ≤ exp (-min (t ^ 2 / (2 * V)) (t / (2 * b)))
        + exp (-min (t ^ 2 / (2 * V)) (t / (2 * b))) :=
        add_le_add (h.measure_ge_le hV hb ht) (h.measure_le_le hV hb ht)
    _ = 2 * exp (-min (t ^ 2 / (2 * V)) (t / (2 * b))) := by ring

lemma measure_abs_gt_le (h : HasSubexponentialMGF X V b μ) (hV : 0 < V) (hb : 0 < b) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | t < |X ω|} ≤ 2 * exp (-min (t ^ 2 / (2 * V)) (t / (2 * b))) := by
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (h.measure_abs_ge_le hV hb ht)
  intro ω hω
  exact le_of_lt (Set.mem_ofPred_eq.mp hω)

end Tail

section Sum

lemma add_of_indepFun {Y : Ω → ℝ} {VX VY : ℝ} (hX : HasSubexponentialMGF X VX b μ)
    (hY : HasSubexponentialMGF Y VY b μ) (hindep : IndepFun X Y μ) :
    HasSubexponentialMGF (X + Y) (VX + VY) b μ where
  integrable_exp_mul t ht :=
    hindep.integrable_exp_mul_add (hX.integrable_exp_mul t ht) (hY.integrable_exp_mul t ht)
  mgf_le t ht := by
    rw [hindep.mgf_add (hX.integrable_exp_mul t ht).aestronglyMeasurable
      (hY.integrable_exp_mul t ht).aestronglyMeasurable]
    calc mgf X μ t * mgf Y μ t
        ≤ exp (VX * t ^ 2 / 2) * exp (VY * t ^ 2 / 2) :=
          mul_le_mul (hX.mgf_le t ht) (hY.mgf_le t ht) mgf_nonneg (exp_pos _).le
      _ = exp ((VX + VY) * t ^ 2 / 2) := by rw [← exp_add]; ring_nf

lemma sum_of_iIndepFun {ι : Type*} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i)) {V : ι → ℝ} (s : Finset ι)
    (h : ∀ i ∈ s, HasSubexponentialMGF (X i) (V i) b μ) :
    HasSubexponentialMGF (∑ i ∈ s, X i) (∑ i ∈ s, V i) b μ where
  integrable_exp_mul t ht := by
    have := h_indep.isProbabilityMeasure
    exact h_indep.integrable_exp_mul_sum h_meas fun i hi ↦ (h i hi).integrable_exp_mul t ht
  mgf_le t ht := by
    rw [h_indep.mgf_sum h_meas]
    calc ∏ i ∈ s, mgf (X i) μ t
        ≤ ∏ i ∈ s, exp (V i * t ^ 2 / 2) :=
          Finset.prod_le_prod (fun i _ ↦ mgf_nonneg) fun i hi ↦ (h i hi).mgf_le t ht
      _ = exp ((∑ i ∈ s, V i) * t ^ 2 / 2) := by rw [← exp_sum, Finset.sum_mul, Finset.sum_div]

lemma fun_sum_of_iIndepFun {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i)) {V : ι → ℝ}
    (h : ∀ i, HasSubexponentialMGF (X i) (V i) b μ) :
    HasSubexponentialMGF (fun ω ↦ ∑ i, X i ω) (∑ i, V i) b μ := by
  have := sum_of_iIndepFun h_indep h_meas Finset.univ fun i _ ↦ h i
  have h1 : (fun ω ↦ ∑ i, X i ω) = ∑ i, X i := by
    ext ω
    simp [Finset.sum_apply]
  rw [h1]
  exact this

/-- The average of `K` independent sub-exponential variables with parameters `(V i, b)` has
parameters `((∑ i, V i) / K ^ 2, b / K)`. -/
lemma average_of_iIndepFun {ι : Type*} [Fintype ι] {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (h_meas : ∀ i, Measurable (X i)) {V : ι → ℝ}
    (h : ∀ i, HasSubexponentialMGF (X i) (V i) b μ) :
    HasSubexponentialMGF (fun ω ↦ (∑ i, X i ω) / Fintype.card ι)
      ((∑ i, V i) / (Fintype.card ι : ℝ) ^ 2) (b / Fintype.card ι) μ := by
  have := (fun_sum_of_iIndepFun h_indep h_meas h).const_mul (1 / Fintype.card ι)
  have h1 : (fun ω ↦ (∑ i, X i ω) / Fintype.card ι)
      = fun ω ↦ (1 / Fintype.card ι) * ∑ i, X i ω := by
    ext ω
    ring
  have h2 : (∑ i, V i) / (Fintype.card ι : ℝ) ^ 2 = (1 / Fintype.card ι) ^ 2 * ∑ i, V i := by
    ring
  have h3 : b / Fintype.card ι = |1 / (Fintype.card ι : ℝ)| * b := by
    rw [abs_of_nonneg (by positivity)]
    ring
  rw [h1, h2, h3]
  exact this

/-- **Tail bound for an average** of independent sub-exponential variables with parameters
`(V i, b)`: writing `K` for the number of variables and `V̄ := (∑ i, V i) / K`,
`P(|(∑ i, X i) / K| ≥ t) ≤ 2 exp (-K min (t ^ 2 / (2 V̄)) (t / (2 b)))`. -/
lemma measure_abs_average_ge_le {ι : Type*} [Fintype ι] [Nonempty ι] {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i)) {V : ι → ℝ}
    (h : ∀ i, HasSubexponentialMGF (X i) (V i) b μ) (hV : 0 < ∑ i, V i) (hb : 0 < b) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(∑ i, X i ω) / Fintype.card ι|}
      ≤ 2 * exp (-(Fintype.card ι
        * min (t ^ 2 / (2 * ((∑ i, V i) / Fintype.card ι))) (t / (2 * b)))) := by
  have := h_indep.isProbabilityMeasure
  have hK : (0 : ℝ) < Fintype.card ι := by
    have := Fintype.card_pos (α := ι)
    positivity
  have hbound := (average_of_iIndepFun h_indep h_meas h).measure_abs_ge_le
    (by positivity) (by positivity) ht
  refine hbound.trans (le_of_eq ?_)
  congr 3
  rw [(monotone_mul_left_of_nonneg hK.le).map_min]
  congr 1
  · field_simp
  · field_simp

/-- **Tail bound for an average** of independent sub-exponential variables with the same
parameters `(V, b)`. -/
lemma measure_abs_average_ge_le_of_forall {ι : Type*} [Fintype ι] [Nonempty ι] {X : ι → Ω → ℝ}
    (h_indep : iIndepFun X μ) (h_meas : ∀ i, Measurable (X i))
    (h : ∀ i, HasSubexponentialMGF (X i) V b μ) (hV : 0 < V) (hb : 0 < b) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |(∑ i, X i ω) / Fintype.card ι|}
      ≤ 2 * exp (-(Fintype.card ι * min (t ^ 2 / (2 * V)) (t / (2 * b)))) := by
  have hK : (0 : ℝ) < Fintype.card ι := by
    have := Fintype.card_pos (α := ι)
    positivity
  have := measure_abs_average_ge_le h_indep h_meas (V := fun _ ↦ V) h
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; positivity) hb ht
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hK.ne']
    using this

end Sum

end HasSubexponentialMGF

end ProbabilityTheory
