/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.Mathlib.Probability.GaussianMGF
public import COLT83.Mathlib.GaussianWidth
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.Convex.Integral

/-!
# Expected maximum of finitely many sub-Gaussian random variables

* `HasSubgaussianMGF.mono`: the sub-Gaussian constant can be increased.
* `integrable_iSup_of_hasSubgaussianMGF`: the maximum of finitely many sub-Gaussian variables is
  integrable.
* `integral_iSup_le_of_hasSubgaussianMGF`: if `Z i`, `i ∈ ι` (finite, nonempty), have
  sub-Gaussian moment generating functions with constant `c` (no assumption on their joint law),
  then `E[max_i Z i] ≤ √(2 c log |ι|)`.
* `hasSubgaussianMGF_inner_stdGaussian`: `⟪a, ·⟫` is sub-Gaussian with constant `‖a‖²` under
  the standard Gaussian measure.
* `integral_iSup_inner_stdGaussian_le`: `E[max_i ⟪y i, g⟫] ≤ σ √(2 log |ι|)` for `‖y i‖ ≤ σ`.
* `gaussianWidth_stdGaussian_le_of_finite`: the Gaussian width of a finite set `K` contained in
  the ball of radius `σ` is at most `σ √(2 log |K|)`.
-/

@[expose] public section

open MeasureTheory Real
open scoped RealInnerProductSpace NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ} {c c' : ℝ≥0}

/-- The sub-Gaussian constant of a random variable can be increased. -/
lemma HasSubgaussianMGF.mono (h : HasSubgaussianMGF X c μ) (hc : c ≤ c') :
    HasSubgaussianMGF X c' μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans (exp_le_exp.2 (by gcongr))

section iSup

variable {ι : Type*} [Finite ι] [Nonempty ι] {Z : ι → Ω → ℝ}

omit [Finite ι] in
lemma abs_le_sum_abs_iSup (f : ι → ℝ) [Fintype ι] : |⨆ i, f i| ≤ ∑ i, |f i| := by
  refine abs_le.2 ⟨?_, ciSup_le fun i ↦ (le_abs_self _).trans (Finset.single_le_sum
    (f := fun i ↦ |f i|) (fun i _ ↦ abs_nonneg _) (Finset.mem_univ i))⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine (neg_le.2 ?_).trans (le_ciSup (Finite.bddAbove_range f) i)
  exact (neg_le_abs _).trans (Finset.single_le_sum (f := fun i ↦ |f i|)
    (fun i _ ↦ abs_nonneg _) (Finset.mem_univ i))

/-- The maximum of finitely many sub-Gaussian random variables is integrable. -/
lemma integrable_iSup_of_hasSubgaussianMGF (h : ∀ i, HasSubgaussianMGF (Z i) c μ) :
    Integrable (fun ω ↦ ⨆ i, Z i ω) μ := by
  have := Fintype.ofFinite ι
  refine (integrable_finsetSum Finset.univ fun i _ ↦ (h i).integrable.abs).mono' ?_ ?_
  · exact aestronglyMeasurable_iff_aemeasurable.2
      (AEMeasurable.iSup fun i ↦ (h i).aemeasurable)
  · exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [Real.norm_eq_abs] using abs_le_sum_abs_iSup (fun i ↦ Z i ω)

omit [Finite ι] in
lemma exp_mul_iSup_le_sum [Fintype ι] (t : ℝ) (f : ι → ℝ) :
    exp (t * ⨆ i, f i) ≤ ∑ i, exp (t * f i) := by
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, ⨆ i, f i = f i₀ := by
    obtain ⟨i₀, hi₀⟩ := Finite.exists_max f
    exact ⟨i₀, le_antisymm (ciSup_le hi₀) (le_ciSup (Finite.bddAbove_range f) i₀)⟩
  rw [hi₀]
  exact Finset.single_le_sum (f := fun i ↦ exp (t * f i)) (fun i _ ↦ (exp_pos _).le)
    (Finset.mem_univ i₀)

/-- For every `β > 0`, `E[max_i Z i] ≤ log |ι| / β + c β / 2`. -/
lemma integral_iSup_le_of_hasSubgaussianMGF_aux [IsProbabilityMeasure μ]
    (h : ∀ i, HasSubgaussianMGF (Z i) c μ) {β : ℝ} (hβ : 0 < β) :
    μ[fun ω ↦ ⨆ i, Z i ω] ≤ log (Nat.card ι) / β + c * β / 2 := by
  have := Fintype.ofFinite ι
  set M : Ω → ℝ := fun ω ↦ ⨆ i, Z i ω with hM
  have hMint : Integrable M μ := integrable_iSup_of_hasSubgaussianMGF h
  have hexp_le : ∀ ω, exp (β * M ω) ≤ ∑ i, exp (β * Z i ω) := fun ω ↦
    exp_mul_iSup_le_sum β fun i ↦ Z i ω
  have hsum_int : Integrable (fun ω ↦ ∑ i, exp (β * Z i ω)) μ :=
    integrable_finsetSum _ fun i _ ↦ (h i).integrable_exp_mul β
  have hexp_int : Integrable (fun ω ↦ exp (β * M ω)) μ := by
    refine hsum_int.mono' ?_ (Filter.Eventually.of_forall fun ω ↦ ?_)
    · exact (measurable_exp.comp_aemeasurable (hMint.aemeasurable.const_mul β)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact hexp_le ω
  -- Jensen: `exp (β E M) ≤ E exp (β M)`
  have hjensen : exp (β * μ[M]) ≤ μ[fun ω ↦ exp (β * M ω)] := by
    have h := convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun ω ↦ Set.mem_univ _) (hMint.const_mul β) (by
        simpa [Function.comp_def] using hexp_int)
    simpa [integral_const_mul] using h
  have hsum : μ[fun ω ↦ ∑ i, exp (β * Z i ω)] ≤ Nat.card ι * exp (c * β ^ 2 / 2) := by
    rw [integral_finsetSum _ fun i _ ↦ (h i).integrable_exp_mul β, Nat.card_eq_fintype_card]
    calc ∑ i, ∫ ω, exp (β * Z i ω) ∂μ ≤ ∑ _i : ι, exp (c * β ^ 2 / 2) :=
          Finset.sum_le_sum fun i _ ↦ (h i).mgf_le β
      _ = Fintype.card ι * exp (c * β ^ 2 / 2) := by simp
  have hbound : exp (β * μ[M]) ≤ Nat.card ι * exp (c * β ^ 2 / 2) :=
    hjensen.trans ((integral_mono hexp_int hsum_int hexp_le).trans hsum)
  have hcard : (0 : ℝ) < Nat.card ι := by exact_mod_cast Nat.card_pos
  have hlog : β * μ[M] ≤ log (Nat.card ι) + c * β ^ 2 / 2 := by
    have := Real.log_le_log (exp_pos _) hbound
    rwa [log_exp, log_mul hcard.ne' (exp_pos _).ne', log_exp] at this
  have heq : log (Nat.card ι) / β + c * β / 2 = (log (Nat.card ι) + c * β ^ 2 / 2) / β := by
    field_simp
  rw [heq, le_div_iff₀ hβ, mul_comm]
  exact hlog

/-- **Expected maximum of finitely many sub-Gaussian variables**: if the `Z i`, `i ∈ ι` (finite,
nonempty), have sub-Gaussian moment generating functions with constant `c` (no assumption on
their joint law), then `E[max_i Z i] ≤ √(2 c log |ι|)`. -/
lemma integral_iSup_le_of_hasSubgaussianMGF [IsProbabilityMeasure μ]
    (h : ∀ i, HasSubgaussianMGF (Z i) c μ) :
    μ[fun ω ↦ ⨆ i, Z i ω] ≤ √(2 * c * log (Nat.card ι)) := by
  have key : ∀ β : ℝ, 0 < β → μ[fun ω ↦ ⨆ i, Z i ω] ≤ log (Nat.card ι) / β + c * β / 2 :=
    fun β hβ ↦ integral_iSup_le_of_hasSubgaussianMGF_aux h hβ
  set L := log (Nat.card ι) with hL
  have hL0 : 0 ≤ L := log_natCast_nonneg _
  rcases eq_or_lt_of_le hL0 with hL0' | hLpos
  · -- `log |ι| = 0`: let `β → 0`
    rw [← hL0', mul_zero, Real.sqrt_zero]
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    have hβ : 0 < ε / (c + 1) := by positivity
    refine (key _ hβ).trans_lt ?_
    rw [← hL0', zero_div, zero_add]
    have : (c : ℝ) * (ε / (c + 1)) ≤ ε := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [hε.le]
    linarith
  rcases eq_zero_or_pos c with rfl | hcpos
  · -- `c = 0`: let `β → ∞`
    simp only [NNReal.coe_zero, mul_zero, zero_mul, Real.sqrt_zero]
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    have hβ : 0 < 2 * L / ε := by positivity
    refine (key _ hβ).trans_lt ?_
    have : L / (2 * L / ε) = ε / 2 := by
      rw [div_div_eq_mul_div, div_eq_iff (by positivity)]
      ring
    simp only [NNReal.coe_zero, zero_mul, zero_div, add_zero, this]
    linarith
  · -- main case: `β = √(2 L / c)`
    have hcpos' : (0 : ℝ) < c := hcpos
    set s := √(2 * L / c) with hs_def
    have hβ : 0 < s := by positivity
    have hs2 : s ^ 2 = 2 * L / c := Real.sq_sqrt (by positivity)
    have hs : √(2 * c * L) = c * s := by
      calc √(2 * c * L) = √(c ^ 2 * (2 * L / c)) := by
            congr 1
            field_simp
        _ = √(c ^ 2) * s := Real.sqrt_mul (sq_nonneg _) _
        _ = c * s := by rw [Real.sqrt_sq hcpos'.le]
    have hLs : L / s = c * s / 2 := by
      rw [div_eq_iff hβ.ne']
      have : (c : ℝ) * s / 2 * s = c * s ^ 2 / 2 := by ring
      rw [this, hs2, mul_div_assoc', mul_div_cancel_left₀ _ hcpos'.ne']
      ring
    refine (key _ hβ).trans (le_of_eq ?_)
    rw [hLs, hs]
    ring

end iSup

section gaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The linear form `⟪a, ·⟫` is sub-Gaussian with constant `‖a‖²` under the standard Gaussian
measure. -/
lemma hasSubgaussianMGF_inner_stdGaussian (a : E) :
    HasSubgaussianMGF (fun x ↦ ⟪a, x⟫) (‖a‖₊ ^ 2) (stdGaussian E) where
  integrable_exp_mul t := integrable_exp_mul_inner_stdGaussian a t
  mgf_le t := by
    rw [mgf, integral_exp_mul_inner_stdGaussian]
    push_cast
    exact le_of_eq (by ring_nf)

variable {ι : Type*} [Finite ι] [Nonempty ι] {y : ι → E} {σ : ℝ}

/-- **Expected maximum of Gaussian linear forms**: for finitely many vectors `y i` with
`‖y i‖ ≤ σ`, `E[max_i ⟪y i, g⟫] ≤ σ √(2 log |ι|)` under the standard Gaussian measure. -/
lemma integral_iSup_inner_stdGaussian_le (hσ : ∀ i, ‖y i‖ ≤ σ) :
    ∫ x, ⨆ i, ⟪y i, x⟫ ∂stdGaussian E ≤ σ * √(2 * log (Nat.card ι)) := by
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  have hσ0 : 0 ≤ σ := (norm_nonneg _).trans (hσ i₀)
  have h : ∀ i, HasSubgaussianMGF (fun x ↦ ⟪y i, x⟫) (σ.toNNReal ^ 2) (stdGaussian E) :=
    fun i ↦ (hasSubgaussianMGF_inner_stdGaussian (y i)).mono (by
      rw [← NNReal.coe_le_coe]
      push_cast
      rw [Real.coe_toNNReal σ hσ0]
      gcongr
      exact hσ i)
  refine (integral_iSup_le_of_hasSubgaussianMGF h).trans (le_of_eq ?_)
  push_cast
  rw [Real.coe_toNNReal σ hσ0,
    show 2 * σ ^ 2 * log (Nat.card ι) = σ ^ 2 * (2 * log (Nat.card ι)) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hσ0]

omit [Finite ι] [Nonempty ι] in
/-- **Gaussian width of a finite set**: if `K` is finite, nonempty and contained in the ball of
radius `σ`, then its Gaussian width under the standard Gaussian measure is at most
`σ √(2 log |K|)`. -/
lemma gaussianWidth_stdGaussian_le_of_finite {K : Set E} (hK : K.Finite) (hne : K.Nonempty)
    (hσ : ∀ x ∈ K, ‖x‖ ≤ σ) :
    gaussianWidth K (stdGaussian E) ≤ σ * √(2 * log K.ncard) := by
  have : Finite K := hK.to_subtype
  have : Nonempty K := hne.to_subtype
  have h := integral_iSup_inner_stdGaussian_le (E := E) (y := fun x : K ↦ (x : E))
    (fun x ↦ hσ x x.2)
  rwa [Nat.card_coe_set_eq] at h

end gaussian

end ProbabilityTheory
