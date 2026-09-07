/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Averages under a prior of a loss controlled with high probability

Let `π` be a probability measure on a parameter space `Θ` (a "prior"), `ν` a probability measure
on an auxiliary noise space `B`, and `κ : Kernel (Θ × B) O` a Markov kernel giving the law of an
output `o` given `(θ, b)`. The joint law of `((θ, b), o)` is `(π.prod ν) ⊗ₘ κ`, and for a fixed
`θ`, the law of `(b, o)` is `ν ⊗ₘ κ.comap (Prod.mk θ) measurable_prodMk_left`.

We show that if a nonnegative loss `r θ o` bounded by `Z θ` exceeds `ε` with probability at most
`δ` for every `θ`, then its expectation under the joint law is at most `ε + δ * ∫ θ, Z θ ∂π`.

## Main statements

* `ProbabilityTheory.integral_compProd_prod_eq_integral_compProd_comap`: the integral of a
  function under the joint law `(π.prod ν) ⊗ₘ κ` is the integral over `θ` of its integral under
  the conditional law of `(b, o)` given `θ`.
* `ProbabilityTheory.integral_le_add_mul_integral_of_measureReal_le`: expected loss of a procedure
  which is accurate with high probability for every parameter, averaged under a prior.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

variable {Θ B O : Type*} {mΘ : MeasurableSpace Θ} {mB : MeasurableSpace B}
  {mO : MeasurableSpace O}

/-- The first marginal of the joint law `(π.prod ν) ⊗ₘ κ` is the prior `π`. -/
lemma map_fst_fst_compProd_prod (π : Measure Θ) [SFinite π] (ν : Measure B)
    [IsProbabilityMeasure ν] (κ : Kernel (Θ × B) O) [IsMarkovKernel κ] :
    ((π.prod ν) ⊗ₘ κ).map (fun p ↦ p.1.1) = π := by
  have : (fun p : (Θ × B) × O ↦ p.1.1) = Prod.fst ∘ Prod.fst := rfl
  rw [this, ← Measure.map_map measurable_fst measurable_fst, ← Measure.fst, ← Measure.fst,
    Measure.fst_compProd, Measure.fst_prod]

/-- A function of `θ` integrable for the prior is integrable for the joint law. -/
lemma integrable_fst_fst_compProd_prod (π : Measure Θ) [SFinite π] (ν : Measure B)
    [IsProbabilityMeasure ν] (κ : Kernel (Θ × B) O) [IsMarkovKernel κ] {f : Θ → ℝ}
    (hf : Integrable f π) :
    Integrable (fun p ↦ f p.1.1) ((π.prod ν) ⊗ₘ κ) := by
  have h := map_fst_fst_compProd_prod π ν κ
  rw [← h] at hf
  exact hf.comp_measurable (by fun_prop)

/-- Integrating a function of `θ` against the joint law is integrating it against the prior. -/
lemma integral_fst_fst_compProd_prod (π : Measure Θ) [SFinite π] (ν : Measure B)
    [IsProbabilityMeasure ν] (κ : Kernel (Θ × B) O) [IsMarkovKernel κ] {f : Θ → ℝ}
    (hf : Integrable f π) :
    ∫ p, f p.1.1 ∂((π.prod ν) ⊗ₘ κ) = ∫ θ, f θ ∂π := by
  have h := map_fst_fst_compProd_prod π ν κ
  conv_rhs => rw [← h]
  rw [integral_map (by fun_prop) (by rw [h]; exact hf.aestronglyMeasurable)]

/-- The joint law `(π.prod ν) ⊗ₘ κ` is the composition-product of `π` with the kernel
`θ ↦ ν ⊗ₘ κ.comap (Prod.mk θ) _`, up to reassociation of the product. -/
lemma compProd_prod_eq_map_compProd_compProd_const (π : Measure Θ) [SFinite π] (ν : Measure B)
    [SFinite ν] (κ : Kernel (Θ × B) O) :
    (π.prod ν) ⊗ₘ κ =
      (π ⊗ₘ (Kernel.const Θ ν ⊗ₖ κ)).map MeasurableEquiv.prodAssoc.symm := by
  rw [Measure.compProd_assoc, Measure.compProd_const]

/-- The joint integral of a function `F ((θ, b), o)`, integrating first over `(b, o)` given `θ`. -/
lemma integral_compProd_prod_eq_integral_compProd_comap (π : Measure Θ) [SFinite π]
    (ν : Measure B) [SFinite ν] (κ : Kernel (Θ × B) O) [IsSFiniteKernel κ]
    {F : (Θ × B) × O → ℝ} (hF : Integrable F ((π.prod ν) ⊗ₘ κ)) :
    ∫ p, F p ∂((π.prod ν) ⊗ₘ κ) =
      ∫ θ, ∫ q, F ((θ, q.1), q.2) ∂(ν ⊗ₘ κ.comap (Prod.mk θ) measurable_prodMk_left) ∂π := by
  rw [compProd_prod_eq_map_compProd_compProd_const] at hF ⊢
  have hF' : Integrable (fun x ↦ F (MeasurableEquiv.prodAssoc.symm x))
      (π ⊗ₘ (Kernel.const Θ ν ⊗ₖ κ)) := (integrable_map_equiv _ _).mp hF
  rw [integral_map_equiv, Measure.integral_compProd hF']
  congr with θ
  rw [Kernel.compProd_apply_eq_compProd_sectR, Kernel.const_apply]
  rfl

/-- **Expected loss of a PAC procedure under a prior.** If for every parameter `θ`, a nonnegative
loss `r θ o` bounded by `Z θ` exceeds `ε` with probability at most `δ` under the law of `(b, o)`
given `θ`, then its expectation under the joint law `(π.prod ν) ⊗ₘ κ` is at most
`ε + δ * ∫ θ, Z θ ∂π`. -/
lemma integral_le_add_mul_integral_of_measureReal_le (π : Measure Θ) [IsProbabilityMeasure π]
    (ν : Measure B) [IsProbabilityMeasure ν] (κ : Kernel (Θ × B) O) [IsMarkovKernel κ]
    {r : Θ → O → ℝ} (hr : Measurable (Function.uncurry r)) {Z : Θ → ℝ} (hZ : Integrable Z π)
    (hr0 : ∀ θ o, 0 ≤ r θ o) (hrZ : ∀ θ o, r θ o ≤ Z θ) {ε δ : ℝ} (hε : 0 ≤ ε)
    (hδ : ∀ θ, (ν ⊗ₘ κ.comap (Prod.mk θ) measurable_prodMk_left).real {q | ε < r θ q.2} ≤ δ) :
    ∫ p, r p.1.1 p.2 ∂((π.prod ν) ⊗ₘ κ) ≤ ε + δ * ∫ θ, Z θ ∂π := by
  -- the output space is nonempty, hence `Z` is nonnegative
  have hO : Nonempty O := by
    obtain ⟨θ⟩ := nonempty_of_isProbabilityMeasure π
    obtain ⟨b⟩ := nonempty_of_isProbabilityMeasure ν
    exact nonempty_of_isProbabilityMeasure (κ (θ, b))
  have hZ0 θ : 0 ≤ Z θ := (hr0 θ (Classical.arbitrary O)).trans (hrZ θ _)
  -- measurability of the sets `{ε < r θ q.2}`
  have hs θ : MeasurableSet {q : B × O | ε < r θ q.2} :=
    measurableSet_lt measurable_const (hr.comp (measurable_const.prodMk measurable_snd))
  have hS : MeasurableSet {p : (Θ × B) × O | ε < r p.1.1 p.2} :=
    measurableSet_lt measurable_const (hr.comp (measurable_fst.fst.prodMk measurable_snd))
  -- the dominating function `G`
  set G : (Θ × B) × O → ℝ :=
    fun p ↦ ε + Z p.1.1 * {p : (Θ × B) × O | ε < r p.1.1 p.2}.indicator 1 p with hG
  have hG_int : Integrable G ((π.prod ν) ⊗ₘ κ) := by
    refine (integrable_const _).add ?_
    refine (integrable_fst_fst_compProd_prod π ν κ hZ).mul_bdd (c := 1)
      ((measurable_const.indicator hS).aestronglyMeasurable) (ae_of_all _ fun p ↦ ?_)
    rw [Set.indicator_apply]
    split_ifs <;> simp
  have hrG : ∀ p, r p.1.1 p.2 ≤ G p := by
    intro p
    simp only [hG, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    split_ifs with h
    · rw [mul_one]
      exact (hrZ _ _).trans (le_add_of_nonneg_left hε)
    · rw [mul_zero, add_zero]
      exact not_lt.mp h
  have hr_int : Integrable (fun p ↦ r p.1.1 p.2) ((π.prod ν) ⊗ₘ κ) := by
    refine (integrable_fst_fst_compProd_prod π ν κ hZ).mono' ?_ (ae_of_all _ fun p ↦ ?_)
    · exact (hr.comp (measurable_fst.fst.prodMk measurable_snd)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (hr0 _ _)]
      exact hrZ _ _
  -- for each `θ`, the conditional integral of `G` is `ε + Z θ * P(ε < r θ o)`
  have hG_cond θ : ∫ q, G ((θ, q.1), q.2) ∂(ν ⊗ₘ κ.comap (Prod.mk θ) measurable_prodMk_left)
      = ε + Z θ * (ν ⊗ₘ κ.comap (Prod.mk θ) measurable_prodMk_left).real {q | ε < r θ q.2} := by
    have : (fun q : B × O ↦ G ((θ, q.1), q.2))
        = fun q ↦ ε + Z θ * {q : B × O | ε < r θ q.2}.indicator 1 q := by
      ext q
      simp only [hG, Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
    rw [this,
      integral_add (integrable_const _) (((integrable_const _).indicator (hs θ)).const_mul _),
      integral_const_mul, integral_indicator_one (hs θ)]
    simp
  calc ∫ p, r p.1.1 p.2 ∂((π.prod ν) ⊗ₘ κ)
      ≤ ∫ p, G p ∂((π.prod ν) ⊗ₘ κ) := integral_mono hr_int hG_int hrG
    _ = ∫ θ, ∫ q, G ((θ, q.1), q.2) ∂(ν ⊗ₘ κ.comap (Prod.mk θ) measurable_prodMk_left) ∂π :=
        integral_compProd_prod_eq_integral_compProd_comap π ν κ hG_int
    _ ≤ ∫ θ, (ε + Z θ * δ) ∂π := by
        refine integral_mono_of_nonneg (ae_of_all _ fun θ ↦ ?_)
          ((integrable_const _).add (hZ.mul_const _)) (ae_of_all _ fun θ ↦ ?_)
        · simp only [Pi.zero_apply]
          rw [hG_cond]
          have := hZ0 θ
          positivity
        · simp only
          rw [hG_cond]
          exact add_le_add_right (mul_le_mul_of_nonneg_left (hδ θ) (hZ0 θ)) ε
    _ = ε + δ * ∫ θ, Z θ ∂π := by
        rw [integral_add (integrable_const _) (hZ.mul_const _), integral_mul_const, integral_const]
        simp [mul_comm]

end ProbabilityTheory
