/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.LeanMachineLearning.FixedDesignLaw

/-!
# Transport of a fixed-design algorithm through a linear map

Let `A` be a fixed-budget (budget `T`) fixed-design algorithm on `𝒳 ⊆ E` with design `x`, let
`𝒴 ⊆ F`, let `L : F →ₗ[ℝ] E` and let `x' : ℕ → 𝒴` be a design on `𝒴` with
`⟪x' t, ϑ⟫ = ⟪x t, L ϑ⟫` for all `t` and `ϑ` (for instance `x' t = L† (x t)`), so that the
observations of `x'` under the reward vector `ϑ` and those of `x` under `L ϑ` have the same law.
The *transported algorithm* `fixedDesignTransport A T x x' hπ` plays `x'` and recommends
`π rec`, where `rec` is drawn from the output rule of `A` applied to the history relabelled with
the actions of `x` (`transportKernel`). If `π : 𝒳 → 𝒴` does not increase the simple regret,
`simpleRegret 𝒴 ϑ (π y) ≤ simpleRegret 𝒳 (L ϑ) y`, then the transported algorithm inherits the
PAC guarantee of `A` (`isPAC_fixedDesignTransport`, blueprint `lem:fixed_design_transport`).

The law of (history, output) of a fixed-design run is explicit (`fixedDesignPairLaw`), and the
proof is a computation with these laws: the law of the recommendation of the transported
algorithm under `ϑ` is the image by `π` of the law of the recommendation of `A` under `L ϑ`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning
open scoped RealInnerProductSpace

universe u v

namespace Learning.LinearBandit

variable {E F : Type*} [MeasurableSpace E] [MeasurableSpace F] {𝒳 : Set E} {𝒴 : Set F} {T : ℕ}

/-- Relabelling of a history on `𝒴` with the actions of the design `x` on `𝒳`. -/
def relabelHist (x : ℕ → 𝒳) (h : Hist Unit 𝒴 ℝ T) : Hist Unit 𝒳 ℝ T :=
  fun t ↦ ((), x t, (h t).feedback)

lemma measurable_relabelHist (x : ℕ → 𝒳) : Measurable (relabelHist (T := T) (𝒴 := 𝒴) x) :=
  Measurable.of_eval fun t ↦ measurable_const.prodMk
    (measurable_const.prodMk (Round.measurable_feedback.comp (measurable_pi_apply t)))

/-- The output kernel of the transported algorithm: relabel the history with the actions of
`x`, draw a recommendation from `ρ` and apply `π`. -/
noncomputable def transportKernel (ρ : Kernel (Hist Unit 𝒳 ℝ T) 𝒳) (x : ℕ → 𝒳) {π : 𝒳 → 𝒴}
    (hπ : Measurable π) : Kernel (Hist Unit 𝒴 ℝ T) 𝒴 :=
  Kernel.deterministic π hπ ∘ₖ ρ.comap (relabelHist x) (measurable_relabelHist x)

instance (ρ : Kernel (Hist Unit 𝒳 ℝ T) 𝒳) [IsMarkovKernel ρ] (x : ℕ → 𝒳) {π : 𝒳 → 𝒴}
    (hπ : Measurable π) : IsMarkovKernel (transportKernel ρ x hπ) := by
  unfold transportKernel
  infer_instance

/-- The transported fixed-design algorithm: play the design `x'` on `𝒴`, then draw a
recommendation from the output rule of `A` on the history relabelled with the actions of `x`, and
apply `π`. -/
noncomputable def fixedDesignTransport (A : IdentAlg 𝒳 ℝ 𝒳) (T : ℕ) [IsMarkovKernel (A.output T)]
    (x : ℕ → 𝒳) (x' : ℕ → 𝒴) {π : 𝒳 → 𝒴} (hπ : Measurable π) : IdentAlg 𝒴 ℝ 𝒴 :=
  IdentAlg.fixedBudget (fixedDesignAlg x') T (transportKernel (A.output T) x hπ)

variable {A : IdentAlg 𝒳 ℝ 𝒳} [IsMarkovKernel (A.output T)] {x : ℕ → 𝒳} {x' : ℕ → 𝒴}
  {π : 𝒳 → 𝒴} {hπ : Measurable π}

lemma isFixedBudget_fixedDesignTransport :
    (fixedDesignTransport A T x x' hπ).IsFixedBudget T :=
  IdentAlg.isFixedBudget_fixedBudget _ _ _

lemma alg_fixedDesignTransport : (fixedDesignTransport A T x x' hπ).alg = fixedDesignAlg x' := rfl

lemma isFixedDesign_fixedDesignTransport : (fixedDesignTransport A T x x' hπ).IsFixedDesign :=
  ⟨x', rfl⟩

lemma output_fixedDesignTransport :
    (fixedDesignTransport A T x x' hπ).output T = transportKernel (A.output T) x hπ :=
  IdentAlg.output_fixedBudget _ _ _

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- The relabelled history law of `x'` under `ϑ` is the history law of `x` under `L ϑ`. -/
lemma fixedDesignHistLaw_map_relabelHist (L : F →ₗ[ℝ] E)
    (hx' : ∀ t (ϑ : F), ⟪(x' t : F), ϑ⟫ = ⟪(x t : E), L ϑ⟫) (ϑ : F) :
    (fixedDesignHistLaw (fun t : Fin T ↦ x' t) ϑ).map (relabelHist x) =
      fixedDesignHistLaw (fun t : Fin T ↦ x t) (L ϑ) := by
  rw [fixedDesignHistLaw, fixedDesignHistLaw,
    Measure.map_map (measurable_relabelHist x) (measurable_fixedDesignHist _ _)]
  congr 1
  funext η t
  simp [relabelHist, fixedDesignHist, hx']

/-- **Transport of the PAC guarantee** (blueprint `lem:fixed_design_transport`): if `A` is
`(ε, δ)`-PAC on `𝒳`, the design `x'` on `𝒴` has the same observation laws as `x` through `L`,
and `π` does not increase the simple regret, then the transported algorithm is `(ε, δ)`-PAC on
`𝒴`. -/
theorem isPAC_fixedDesignTransport {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F]
    [OpensMeasurableSpace F] {𝒳 : Set E} {𝒴 : Set F} [MeasurableEq 𝒴]
    {A : IdentAlg 𝒳 ℝ 𝒳} {T : ℕ} [IsMarkovKernel (A.output T)] (hA : A.IsFixedBudget T)
    {x : ℕ → 𝒳} (hdes : A.alg = fixedDesignAlg x) {ε δ : ℝ} (hpac : IsPAC 𝒳 A ε δ)
    (L : F →ₗ[ℝ] E) {x' : ℕ → 𝒴} (hx' : ∀ t (ϑ : F), ⟪(x' t : F), ϑ⟫ = ⟪(x t : E), L ϑ⟫)
    {π : 𝒳 → 𝒴} (hπ : Measurable π)
    (hreg : ∀ (ϑ : F) (y : 𝒳), simpleRegret 𝒴 ϑ (π y) ≤ simpleRegret 𝒳 (L ϑ) y) :
    IsPAC 𝒴 (fixedDesignTransport A T x x' hπ) ε δ := by
  intro ϑ Ω _ P _ O X Y out hrun
  have hlaw := hrun.hasLaw_history_out_of_fixedDesign isFixedBudget_fixedDesignTransport
    alg_fixedDesignTransport
  have hG' : MeasurableSet {y : 𝒴 | simpleRegret 𝒴 ϑ y ≤ ε} :=
    measurableSet_le
      (continuous_const.sub (continuous_subtype_val.inner continuous_const)).measurable
      measurable_const
  have hG : MeasurableSet {y : 𝒳 | simpleRegret 𝒳 (L ϑ) y ≤ ε} :=
    measurableSet_le
      (continuous_const.sub (continuous_subtype_val.inner continuous_const)).measurable
      measurable_const
  have h1 : P.real {ω | simpleRegret 𝒴 ϑ (out ω) ≤ ε} =
      (fixedDesignPairLaw (fixedDesignTransport A T x x' hπ) (fun t : Fin T ↦ x' t) ϑ).real
        (Prod.snd ⁻¹' {y : 𝒴 | simpleRegret 𝒴 ϑ y ≤ ε}) :=
    hlaw.measureReal_eq (p := fun p ↦ simpleRegret 𝒴 ϑ p.2 ≤ ε) (measurable_snd hG')
  rw [h1, fixedDesignPairLaw, output_fixedDesignTransport, Measure.real, ← Measure.snd_apply hG',
    Measure.snd_compProd, transportKernel, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map, ← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map, fixedDesignHistLaw_map_relabelHist L hx' ϑ,
    Measure.map_apply hπ hG']
  have h4 := hpac.le_measureReal_fixedDesignPairLaw hA hdes (L ϑ)
  change 1 - δ ≤ (fixedDesignPairLaw A (fun t : Fin T ↦ x t) (L ϑ)).real
    (Prod.snd ⁻¹' {y : 𝒳 | simpleRegret 𝒳 (L ϑ) y ≤ ε}) at h4
  rw [fixedDesignPairLaw, Measure.real, ← Measure.snd_apply hG, Measure.snd_compProd] at h4
  refine h4.trans (measureReal_mono ?_)
  intro y hy
  exact (hreg ϑ y).trans hy

end Learning.LinearBandit
