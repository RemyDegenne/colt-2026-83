/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.LeanMachineLearning.RunDivergence
public import Maiti2026Power.Mathlib.InformationTheory.BretagnolleHuber

/-!
# Runs of fixed-budget identification algorithms and data processing

For a fixed-budget identification algorithm `A` with budget `T` (`A.IsFixedBudget T`), the
history at the stopping time of every run is the history of the first `T` rounds
(`IsFixedBudget.stoppedHist_eq`). Consequently, for two runs of `A` (on arbitrary probability
spaces) in two environments, the divergence between the laws of the outputs is at most the
divergence between the laws of the histories of the first `T` rounds, by the data-processing
inequality (`IsRun.klDiv_map_out_le`):
appending the recommendation does not increase the divergence. Combined with the divergence
decomposition for linear Gaussian environments, the divergence between the laws of the outputs
under `θ` and `θ'` is at most `T R ^ 2 ‖θ - θ'‖ ^ 2 / 2` (`LinearBandit.klDiv_map_out_le`), and the
Bretagnolle–Huber inequality bounds the sum of the error probabilities of any test on the output
from below (`LinearBandit.exp_neg_le_measureReal_add`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal RealInnerProductSpace

namespace Learning

namespace IdentAlg

variable {𝓐 𝓨 𝓓 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {m𝓓 : MeasurableSpace 𝓓} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {A : IdentAlg Unit 𝓐 𝓨 𝓓} {T : ℕ} {O : ℕ → Ω → Unit} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {O' : ℕ → Ω' → Unit} {X' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨} {out : Ω → 𝓓} {out' : Ω' → 𝓓}
  {env env' : Environment Unit 𝓐 𝓨}

/-- **Data processing for runs of a fixed-budget algorithm**: for two runs (in two environments)
of a fixed-budget algorithm with budget `T`, the divergence between the laws of the outputs is
at most the divergence between the laws of the histories of the first `T` rounds. -/
lemma IsRun.klDiv_map_out_le (hA : A.IsFixedBudget T) (h : A.IsRun env O X Y out P)
    (h' : A.IsRun env' O' X' Y' out' P') :
    klDiv (P.map out) (P'.map out') ≤
      klDiv (P.map (history O X Y T)) (P'.map (history O' X' Y' T)) := by
  have hfin : Measurable (history O X Y T) := h.isAlgEnvSeq.measurable_history T
  have hfin' : Measurable (history O' X' Y' T) := h'.isAlgEnvSeq.measurable_history T
  let ι : Hist Unit 𝓐 𝓨 T → Σ n, Hist Unit 𝓐 𝓨 n := Sigma.mk (β := fun n ↦ Hist Unit 𝓐 𝓨 n) T
  have hι : Measurable ι := measurable_sigma_mk _
  calc klDiv (P.map out) (P'.map out')
      ≤ klDiv (P.map (A.stoppedHist O X Y)) (P'.map (A.stoppedHist O' X' Y')) :=
        h.klDiv_map_out_le_stoppedHist h'
    _ = klDiv ((P.map (history O X Y T)).map ι) ((P'.map (history O' X' Y' T)).map ι) := by
        rw [Measure.map_map hι hfin, Measure.map_map hι hfin']
        congr 2 <;> exact funext fun ω ↦ hA.stoppedHist_eq ω
    _ ≤ klDiv (P.map (history O X Y T)) (P'.map (history O' X' Y' T)) := klDiv_map_le _ _ hι

/-- For two runs of a fixed-budget algorithm with budget `0`, the laws of the outputs coincide:
their divergence is `0`. -/
lemma IsRun.klDiv_map_out_eq_zero (hA : A.IsFixedBudget 0) (h : A.IsRun env O X Y out P)
    (h' : A.IsRun env' O' X' Y' out' P') :
    klDiv (P.map out) (P'.map out') = 0 := by
  rw [h.map_out_eq_of_isFixedBudget_zero hA, h'.map_out_eq_of_isFixedBudget_zero hA, klDiv_self]

end IdentAlg

namespace LinearBandit

open IdentAlg

variable {E 𝓓 : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {m𝓓 : MeasurableSpace 𝓓}
  {𝒳 : Set E} {θ θ' : E} {A : IdentAlg Unit 𝒳 ℝ 𝓓} {T : ℕ} {R : ℝ}
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → ℝ} {O' : ℕ → Ω' → Unit} {X' : ℕ → Ω' → 𝒳}
  {Y' : ℕ → Ω' → ℝ} {out : Ω → 𝓓} {out' : Ω' → 𝓓}

/-- For two runs of a fixed-budget algorithm with budget `T` in the linear Gaussian environments
with reward vectors `θ` and `θ'`, with `⟪x, θ - θ'⟫ ^ 2 ≤ C` on the action set, the divergence
between the laws of the outputs is at most `T C / 2`. -/
lemma IsRun.klDiv_map_out_le_of_sq_le {C : ℝ} (hC : ∀ x ∈ 𝒳, ⟪x, θ - θ'⟫ ^ 2 ≤ C)
    (hA : A.IsFixedBudget T) (h : A.IsRun (linearGaussianEnv 𝒳 θ) O X Y out P)
    (h' : A.IsRun (linearGaussianEnv 𝒳 θ') O' X' Y' out' P') :
    klDiv (P.map out) (P'.map out') ≤ ENNReal.ofReal (T * (C / 2)) :=
  (IdentAlg.IsRun.klDiv_map_out_le hA h h').trans
    (klDiv_map_history_le_of_sq_le h.isAlgEnvSeq h'.isAlgEnvSeq hC T)

/-- For two runs of a fixed-budget algorithm with budget `T` in the linear Gaussian environments
with reward vectors `θ` and `θ'` on an action set contained in the ball of radius `R`, the
divergence between the laws of the outputs is at most `T R ^ 2 ‖θ - θ'‖ ^ 2 / 2`. -/
lemma IsRun.klDiv_map_out_le (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) (hA : A.IsFixedBudget T)
    (h : A.IsRun (linearGaussianEnv 𝒳 θ) O X Y out P)
    (h' : A.IsRun (linearGaussianEnv 𝒳 θ') O' X' Y' out' P') :
    klDiv (P.map out) (P'.map out') ≤ ENNReal.ofReal (T * (R ^ 2 * ‖θ - θ'‖ ^ 2 / 2)) :=
  IsRun.klDiv_map_out_le_of_sq_le (fun x hx ↦ inner_sq_le hR ⟨x, hx⟩ (θ - θ')) hA h h'

/-- **Bretagnolle–Huber for the outputs of a fixed-budget algorithm**: in the setting of
`IsRun.klDiv_map_out_le_of_sq_le`, for every measurable set `B` of outputs,
`P (out ∈ B) + P' (out' ∉ B) ≥ (1/2) exp (-T C / 2)`. -/
lemma IsRun.exp_neg_le_measureReal_add_of_sq_le {C : ℝ} (hC : ∀ x ∈ 𝒳, ⟪x, θ - θ'⟫ ^ 2 ≤ C)
    (hA : A.IsFixedBudget T) (h : A.IsRun (linearGaussianEnv 𝒳 θ) O X Y out P)
    (h' : A.IsRun (linearGaussianEnv 𝒳 θ') O' X' Y' out' P') {B : Set 𝓓} (hB : MeasurableSet B) :
    (1 / 2) * Real.exp (-(T * (C / 2))) ≤ P.real (out ⁻¹' B) + P'.real (out' ⁻¹' Bᶜ) := by
  have hout : AEMeasurable out P := h.hasCondDistrib_output.aemeasurable_snd
  have hout' : AEMeasurable out' P' := h'.hasCondDistrib_output.aemeasurable_snd
  have hkl := IsRun.klDiv_map_out_le_of_sq_le hC hA h h'
  have hne : klDiv (P.map out) (P'.map out') ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  have : IsProbabilityMeasure (P.map out) := inferInstance
  have : IsProbabilityMeasure (P'.map out') := inferInstance
  have hC0 : 0 ≤ C := by
    obtain ⟨ω⟩ := Measure.nonempty_of_neZero P
    exact (sq_nonneg _).trans (hC _ (X 0 ω).2)
  calc (1 / 2) * Real.exp (-(T * (C / 2)))
      ≤ (1 / 2) * Real.exp (-(klDiv (P.map out) (P'.map out')).toReal) := by
        gcongr
        exact ENNReal.toReal_le_of_le_ofReal (by positivity) hkl
    _ ≤ (P.map out).real B + (P'.map out').real Bᶜ := by
        rw [one_div_mul_eq_div]
        exact bretagnolle_huber hB hne
    _ = P.real (out ⁻¹' B) + P'.real (out' ⁻¹' Bᶜ) := by
        rw [map_measureReal_apply_of_aemeasurable hout hB,
          map_measureReal_apply_of_aemeasurable hout' hB.compl]

end LinearBandit

end Learning
