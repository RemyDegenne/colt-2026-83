/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.ForMathlib.InformationTheory.KullbackLeibler.ChainRule
public import LeanMachineLearning.ForMathlib.Probability.Kernel.Composition.Lemmas
public import Maiti2026Power.Mathlib.Probability.CondDistrib

/-!
# Conditional Kullback–Leibler divergences: composition-product and integral forms

The conditional divergence of two kernels `κ, η` given a law `μ` on their source can be written
in *composition-product form*, `klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η)`, which makes sense on every measurable
space, or in *integral form*, `∫⁻ a, klDiv (κ a) (η a) ∂μ`, which requires the measurability of
`a ↦ klDiv (κ a) (η a)`, guaranteed when the target space is countably generated (LML's
`klDiv_compProd_right_eq_lintegral`). This file collects the facts about the composition-product
form used by the divergence decomposition of algorithm-environment sequences.

* `klDiv_map_of_leftInverse`: the divergence is invariant under a measurable map with a
  measurable left inverse.
* `klDiv_map_of_eq_withDensity_comp`: if `μ` has density `f ∘ g` with respect to `ν`, then
  `klDiv (μ.map g) (ν.map g) = klDiv μ ν` (`g` is a sufficient statistic).
* `klDiv_compProd_comap`: the conditional divergence of two kernels which depend on the
  conditioning variable only through a statistic `f` is the conditional divergence given `f`:
  `klDiv (μ ⊗ₘ κ.comap f) (μ ⊗ₘ η.comap f) = klDiv (μ.map f ⊗ₘ κ) (μ.map f ⊗ₘ η)`.
* `klDiv_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd`,
  `klDiv_compProd_compProd_prodMkLeft`: the one-step divergence of a policy/reward
  decomposition, in composition-product form
  `klDiv (μ ⊗ₘ (π ⊗ₖ κ̃)) (μ ⊗ₘ (π ⊗ₖ η̃)) = klDiv ((π ∘ₘ μ) ⊗ₘ κ) ((π ∘ₘ μ) ⊗ₘ η)` and in
  integral form `∫⁻ b, klDiv (κ b) (η b) ∂(π ∘ₘ μ)`, where `κ̃ = prodMkLeft α κ` ignores the
  first coordinate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace InformationTheory

section map

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}
  [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The Kullback–Leibler divergence is invariant under a measurable map with a measurable left
inverse. -/
lemma klDiv_map_of_leftInverse {f : α → β} {g : β → α} (hf : Measurable f) (hg : Measurable g)
    (hgf : Function.LeftInverse g f) :
    klDiv (μ.map f) (ν.map f) = klDiv μ ν := by
  refine le_antisymm (klDiv_map_le μ ν hf) ?_
  have h := klDiv_map_le (μ.map f) (ν.map f) hg
  rwa [Measure.map_map hg hf, Measure.map_map hg hf, hgf.comp_eq_id, Measure.map_id,
    Measure.map_id] at h

/-- If `μ` has density `f ∘ g` with respect to `ν`, then the divergence of the images by `g` is
the divergence of `μ` and `ν`: `g` is a sufficient statistic. -/
lemma klDiv_map_of_eq_withDensity_comp {f : β → ℝ≥0∞} (hf : Measurable f) {g : α → β}
    (hg : Measurable g) (hμ : μ = ν.withDensity (f ∘ g)) :
    klDiv (μ.map g) (ν.map g) = klDiv μ ν := by
  have h_map : μ.map g = (ν.map g).withDensity f := by
    rw [hμ]
    ext s hs
    rw [Measure.map_apply hg hs, withDensity_apply _ (hg hs), withDensity_apply _ hs,
      ← lintegral_indicator hs, ← lintegral_indicator (hg hs), lintegral_map (hf.indicator hs) hg]
    congr with x
  have hac : μ ≪ ν := by
    rw [hμ]
    exact withDensity_absolutelyContinuous _ _
  have h1 : μ.rnDeriv ν =ᵐ[ν] f ∘ g := by
    rw [hμ]
    exact Measure.rnDeriv_withDensity ν (hf.comp hg)
  have h2 : (μ.map g).rnDeriv (ν.map g) =ᵐ[ν.map g] f := by
    rw [h_map]
    exact Measure.rnDeriv_withDensity _ hf
  have hmeas : Measurable fun x : β ↦
      ENNReal.ofReal (klFun ((μ.map g).rnDeriv (ν.map g) x).toReal) :=
    (measurable_klFun.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal).ennreal_ofReal
  rw [klDiv_eq_lintegral_klFun_of_ac (hac.map hg), klDiv_eq_lintegral_klFun_of_ac hac,
    lintegral_map hmeas hg]
  refine lintegral_congr_ae ?_
  filter_upwards [h1, ae_of_ae_map hg.aemeasurable h2] with x hx1 hx2
  rw [hx1, hx2]
  rfl

end map

section comap

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- The conditional divergence of two kernels which depend on the conditioning variable only
through a statistic `f` is the conditional divergence given `f`. -/
lemma klDiv_compProd_comap (μ : Measure α) [IsFiniteMeasure μ] (κ η : Kernel β γ)
    [IsFiniteKernel κ] [IsFiniteKernel η] {f : α → β} (hf : Measurable f) :
    klDiv (μ ⊗ₘ κ.comap f hf) (μ ⊗ₘ η.comap f hf) = klDiv (μ.map f ⊗ₘ κ) (μ.map f ⊗ₘ η) := by
  have hg : Measurable fun p : α × γ ↦ (f p.1, p.2) := by fun_prop
  by_cases hac : μ.map f ⊗ₘ κ ≪ μ.map f ⊗ₘ η
  swap
  · rw [klDiv_of_not_ac hac, klDiv_of_not_ac]
    intro h
    have := h.map hg
    rw [Measure.map_compProd_comap, Measure.map_compProd_comap] at this
    exact hac this
  set D := (μ.map f ⊗ₘ κ).rnDeriv (μ.map f ⊗ₘ η) with hD_def
  have hD : Measurable D := Measure.measurable_rnDeriv _ _
  have hDκ : μ.map f ⊗ₘ κ = (μ.map f ⊗ₘ η).withDensity D :=
    (Measure.withDensity_rnDeriv_eq _ _ hac).symm
  -- for every measurable `t`, the sections of the density integrate to `κ (f a) t`, `μ`-a.e.
  have h_sect : ∀ {t : Set γ}, MeasurableSet t →
      ∀ᵐ a ∂μ, ∫⁻ c in t, D (f a, c) ∂(η (f a)) = κ (f a) t := by
    intro t ht
    refine ae_of_ae_map (p := fun b ↦ ∫⁻ c in t, D (b, c) ∂(η b) = κ b t) hf.aemeasurable ?_
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite
      (Measurable.setLIntegral_kernel_prod_right (f := fun b c ↦ D (b, c)) hD ht)
      (Kernel.measurable_coe κ ht) fun u hu _ ↦ ?_
    have h1 := congrArg (fun ρ : Measure (β × γ) ↦ ρ (u ×ˢ t)) hDκ
    rw [Measure.compProd_apply_prod hu ht, withDensity_apply _ (hu.prod ht),
      Measure.setLIntegral_compProd hD hu ht] at h1
    exact h1.symm
  have h_rect : ∀ s t, MeasurableSet s → MeasurableSet t →
      (μ ⊗ₘ κ.comap f hf) (s ×ˢ t) =
        ((μ ⊗ₘ η.comap f hf).withDensity (D ∘ fun p ↦ (f p.1, p.2))) (s ×ˢ t) := by
    intro s t hs ht
    rw [Measure.compProd_apply_prod hs ht, withDensity_apply _ (hs.prod ht),
      Measure.setLIntegral_compProd (hD.comp hg) hs ht]
    refine setLIntegral_congr_fun_ae hs ?_
    filter_upwards [h_sect ht] with a ha _
    simp only [Kernel.comap_apply, Function.comp_apply]
    exact ha.symm
  have key : μ ⊗ₘ κ.comap f hf =
      (μ ⊗ₘ η.comap f hf).withDensity (D ∘ fun p ↦ (f p.1, p.2)) := by
    refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
    · rintro _ ⟨s, hs, t, ht, rfl⟩
      exact h_rect s t hs ht
    · simpa using h_rect Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
  rw [← Measure.map_compProd_comap μ κ hf, ← Measure.map_compProd_comap μ η hf,
    klDiv_map_of_eq_withDensity_comp hD hg key]

/-- The divergence of one step of a policy/reward decomposition, in composition-product form:
the policy `π` is shared and the reward kernels `κ`, `η` (which ignore the history) differ, so
the divergence is the conditional divergence of the reward kernels given the played action,
whose law is `π ∘ₘ μ`. -/
lemma klDiv_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd (μ : Measure α)
    [IsFiniteMeasure μ] (π : Kernel α β) [IsMarkovKernel π] (κ η : Kernel β γ) [IsFiniteKernel κ]
    [IsFiniteKernel η] :
    klDiv (μ ⊗ₘ (π ⊗ₖ Kernel.prodMkLeft α κ)) (μ ⊗ₘ (π ⊗ₖ Kernel.prodMkLeft α η)) =
      klDiv ((π ∘ₘ μ) ⊗ₘ κ) ((π ∘ₘ μ) ⊗ₘ η) := by
  rw [← klDiv_map_measurableEquiv _ _ MeasurableEquiv.prodAssoc.symm, Measure.compProd_assoc,
    Measure.compProd_assoc, ← Measure.snd_compProd, Measure.snd]
  exact klDiv_compProd_comap _ _ _ measurable_snd

end comap

section kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} [MeasurableSpace.CountableOrCountablyGenerated β γ]

/-- The divergence of one step of a policy/reward decomposition, in integral form: the policy
`π` is shared and the reward kernels `κ`, `η` (which ignore the history) differ, so the
divergence is the expected divergence of the reward kernels at the played action, whose law is
`π ∘ₘ μ`. -/
lemma klDiv_compProd_compProd_prodMkLeft (μ : Measure α) [IsFiniteMeasure μ] (π : Kernel α β)
    [IsMarkovKernel π] (κ η : Kernel β γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (μ ⊗ₘ (π ⊗ₖ Kernel.prodMkLeft α κ)) (μ ⊗ₘ (π ⊗ₖ Kernel.prodMkLeft α η)) =
      ∫⁻ b, klDiv (κ b) (η b) ∂(π ∘ₘ μ) := by
  rw [klDiv_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd,
    klDiv_compProd_right_eq_lintegral]

end kernel

end InformationTheory
