/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Maiti2026Power.LeanMachineLearning.DivergenceDecomposition

/-!
# Data processing for runs of identification algorithms

For two runs of the same identification algorithm `A` (on arbitrary probability spaces, in two
environments), whose stopping times are almost surely finite, the divergence between the laws of
the pairs (history at the stopping time, output) is the divergence between the laws of the
histories at the stopping time (`IsRun.klDiv_map_stoppedHist_out`), since the output rule is the
same probability kernel on the stopping set; consequently the divergence between the laws of
the outputs is at most the divergence between the laws of the stopped histories
(`IsRun.klDiv_map_out_le_stoppedHist`), by the data-processing inequality.

Combined with the divergence decomposition for stopped histories, this bounds the divergence
between the laws of the outputs of two runs in two stationary environments by the expected sum,
along the first run, of the divergences of the reward kernels at the actions played before
stopping (`IsRun.klDiv_map_out_le_lintegral`; in composition-product form
`IsRun.klDiv_map_out_le_tsum_compProd`). This is the standard change-of-measure argument of
fixed-confidence lower bounds (Kaufmann, Cappé and Garivier, 2016).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal ENat

namespace Learning.IdentAlg

variable {𝓐 𝓨 𝓞 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {m𝓞 : MeasurableSpace 𝓞} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {A : IdentAlg 𝓐 𝓨 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {X' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}
  {out : Ω → 𝓞} {out' : Ω' → 𝓞} {env env' : Environment 𝓐 𝓨}

/-- When the stopping time of a run is almost surely finite, the history at the stopping time
belongs to the stopping set almost surely. -/
lemma IsRun.ae_stoppedHist_mem_stopSet (h : A.IsRun env X Y out P)
    (hτ : ∀ᵐ ω ∂P, A.stoppingTime X Y ω ≠ ⊤) :
    ∀ᵐ s ∂(P.map (A.stoppedHist X Y)), s ∈ A.stopSet := by
  rw [ae_map_iff (p := fun a ↦ a ∈ A.stopSet) h.hasCondDistrib_output.aemeasurable_fst
    A.measurableSet_stopSet]
  filter_upwards [hτ] with ω hω using A.stoppedHist_mem_stopSet_of_ne_top X Y hω

/-- **Data processing for runs**: for two runs of the same identification algorithm with almost
surely finite stopping times, the divergence between the laws of the pairs (history at the
stopping time, output) is the divergence between the laws of the histories at the stopping
time. -/
lemma IsRun.klDiv_map_stoppedHist_out (h : A.IsRun env X Y out P) (h' : A.IsRun env' X' Y' out' P')
    (hτ : ∀ᵐ ω ∂P, A.stoppingTime X Y ω ≠ ⊤) (hτ' : ∀ᵐ ω ∂P', A.stoppingTime X' Y' ω ≠ ⊤) :
    klDiv (P.map fun ω ↦ (A.stoppedHist X Y ω, out ω))
        (P'.map fun ω ↦ (A.stoppedHist X' Y' ω, out' ω)) =
      klDiv (P.map (A.stoppedHist X Y)) (P'.map (A.stoppedHist X' Y')) := by
  have hne : Nonempty 𝓞 := ⟨out (Measure.nonempty_of_neZero P).some⟩
  rw [h.hasCondDistrib_output.map_eq, h'.hasCondDistrib_output.map_eq]
  exact klDiv_compProd_left_of_ae _ _ _ A.measurableSet_stopSet
    (fun s hs ↦ A.isProbabilityMeasure_output s.1 s.2 hs) (h.ae_stoppedHist_mem_stopSet hτ)
    (h'.ae_stoppedHist_mem_stopSet hτ')

/-- **Data processing for runs**: for two runs of the same identification algorithm with almost
surely finite stopping times, the divergence between the laws of the outputs is at most the
divergence between the laws of the histories at the stopping time. -/
lemma IsRun.klDiv_map_out_le_stoppedHist (h : A.IsRun env X Y out P)
    (h' : A.IsRun env' X' Y' out' P') (hτ : ∀ᵐ ω ∂P, A.stoppingTime X Y ω ≠ ⊤)
    (hτ' : ∀ᵐ ω ∂P', A.stoppingTime X' Y' ω ≠ ⊤) :
    klDiv (P.map out) (P'.map out') ≤
      klDiv (P.map (A.stoppedHist X Y)) (P'.map (A.stoppedHist X' Y')) := by
  rw [← h.klDiv_map_stoppedHist_out h' hτ hτ']
  have := klDiv_map_le (P.map fun ω ↦ (A.stoppedHist X Y ω, out ω))
    (P'.map fun ω ↦ (A.stoppedHist X' Y' ω, out' ω)) measurable_snd
  rwa [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
    h.hasCondDistrib_output.aemeasurable, AEMeasurable.map_map_of_aemeasurable
    measurable_snd.aemeasurable h'.hasCondDistrib_output.aemeasurable] at this

variable {κ κ' : Kernel 𝓐 𝓨} [IsMarkovKernel κ] [IsMarkovKernel κ']

/-- **Change of measure at a stopping time**, composition-product form: for two runs of the same
identification algorithm in two stationary environments with reward kernels `κ` and `κ'`, with
almost surely finite stopping times, the divergence between the laws of the outputs is at most
the series over the rounds `t` of the conditional divergences of the reward kernels given the
played action, on the event that the algorithm has not stopped after `t` rounds. -/
lemma IsRun.klDiv_map_out_le_tsum_compProd (h : A.IsRun (stationaryEnv κ) X Y out P)
    (h' : A.IsRun (stationaryEnv κ') X' Y' out' P') (hτ : ∀ᵐ ω ∂P, A.stoppingTime X Y ω ≠ ⊤)
    (hτ' : ∀ᵐ ω ∂P', A.stoppingTime X' Y' ω ≠ ⊤) :
    klDiv (P.map out) (P'.map out') ≤
      ∑' t : ℕ, klDiv ((P.restrict {ω | (t : ℕ∞) < A.stoppingTime X Y ω}).map (X t) ⊗ₘ κ)
        ((P.restrict {ω | (t : ℕ∞) < A.stoppingTime X Y ω}).map (X t) ⊗ₘ κ') :=
  (h.klDiv_map_out_le_stoppedHist h' hτ hτ').trans_eq
    (h.isAlgEnvSeq.klDiv_map_stoppedHist_compProd h'.isAlgEnvSeq A.measurableSet_stopSet hτ hτ')

/-- **Change of measure at a stopping time**, integral form: for two runs of the same
identification algorithm in two stationary environments with reward kernels `κ` and `κ'`, with
almost surely finite stopping times, the divergence between the laws of the outputs is at most
the expected sum, along the first run, of the divergences of the reward kernels at the actions
played before stopping. -/
lemma IsRun.klDiv_map_out_le_lintegral [MeasurableSpace.CountablyGenerated 𝓨]
    (h : A.IsRun (stationaryEnv κ) X Y out P) (h' : A.IsRun (stationaryEnv κ') X' Y' out' P')
    (hτ : ∀ᵐ ω ∂P, A.stoppingTime X Y ω ≠ ⊤) (hτ' : ∀ᵐ ω ∂P', A.stoppingTime X' Y' ω ≠ ⊤) :
    klDiv (P.map out) (P'.map out') ≤
      ∫⁻ ω, ∑ t ∈ range (A.stoppingTime X Y ω).toNat, klDiv (κ (X t ω)) (κ' (X t ω)) ∂P :=
  (h.klDiv_map_out_le_stoppedHist h' hτ hτ').trans_eq
    (h.isAlgEnvSeq.klDiv_map_stoppedHist h'.isAlgEnvSeq A.measurableSet_stopSet hτ hτ')

end Learning.IdentAlg
