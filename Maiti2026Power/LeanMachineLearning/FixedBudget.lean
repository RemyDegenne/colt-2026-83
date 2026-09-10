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
stopping time of every run is `T` (`IsFixedBudget.stoppingTime_eq`) and the history at the
stopping time is the history of the first `T` rounds (`IsFixedBudget.stoppedHist_eq`).

Consequently, for two runs of `A` (on arbitrary probability spaces) in two environments, the
divergence between the laws of the outputs is at most the divergence between the laws of the
histories of the first `T` rounds, by the data-processing inequality (`IsRun.klDiv_map_out_le`):
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

variable {𝓐 𝓨 𝓞 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {m𝓞 : MeasurableSpace 𝓞} {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {A : IdentAlg 𝓐 𝓨 𝓞} {T : ℕ} {O : ℕ → Ω → Unit} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}

/-- The stopping time of a fixed-budget algorithm with budget `T` is `T`. -/
lemma IsFixedBudget.stoppingTime_eq (hA : A.IsFixedBudget T) (ω : Ω) :
    A.stoppingTime O X Y ω = T := by
  have hmem : ∀ n, (⟨n, history O X Y n ω⟩ : Σ n, Hist Unit 𝓐 𝓨 n) ∈ A.stopSet ↔ n = T := by
    intro n
    unfold IsFixedBudget at hA
    simp only [stopSet, Set.mem_ofPred_eq, hA]
  exact stoppingTime_eq_coe_iff.2
    ⟨(hmem T).2 rfl, fun j hj hjS ↦ hj.ne ((hmem j).1 hjS)⟩

/-- The history at the stopping time of a fixed-budget algorithm with budget `T` is the history
of the first `T` rounds. -/
lemma IsFixedBudget.stoppedHist_eq (hA : A.IsFixedBudget T) (ω : Ω) :
    A.stoppedHist O X Y ω = ⟨T, history O X Y T ω⟩ := by
  rw [stoppedHist_def,
    stoppedHist_congr (A.stoppingTime O X Y) (fun _ ↦ (T : ℕ∞)) (hA.stoppingTime_eq ω),
    stoppedHist_coe]

variable {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {O' : ℕ → Ω' → Unit} {X' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨} {out : Ω → 𝓞} {out' : Ω' → 𝓞}
  {env env' : Environment Unit 𝓐 𝓨}

/-- For a fixed-budget algorithm, the history at the stopping time belongs to the stopping set. -/
lemma IsFixedBudget.stoppedHist_mem_stopSet (hA : A.IsFixedBudget T) (ω : Ω) :
    A.stoppedHist O X Y ω ∈ A.stopSet := by
  rw [hA.stoppedHist_eq]
  unfold IsFixedBudget at hA
  simp [stopSet, hA]

/-- The stopping time of a fixed-budget algorithm is finite. -/
lemma IsFixedBudget.stoppingTime_ne_top (hA : A.IsFixedBudget T) (ω : Ω) :
    A.stoppingTime O X Y ω ≠ ⊤ := by
  rw [hA.stoppingTime_eq]
  exact ENat.natCast_ne_top T

/-- **Data processing for runs**: for two runs of the same fixed-budget identification algorithm,
the divergence between the laws of the pairs (history at the stopping time, output) is the
divergence between the laws of the histories at the stopping time. -/
lemma IsRun.klDiv_map_stoppedHist_out_of_isFixedBudget (hA : A.IsFixedBudget T)
    (h : A.IsRun env O X Y out P) (h' : A.IsRun env' O' X' Y' out' P') :
    klDiv (P.map fun ω ↦ (A.stoppedHist O X Y ω, out ω))
        (P'.map fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) =
      klDiv (P.map (A.stoppedHist O X Y)) (P'.map (A.stoppedHist O' X' Y')) :=
  h.klDiv_map_stoppedHist_out h' (Filter.Eventually.of_forall hA.stoppingTime_ne_top)
    (Filter.Eventually.of_forall hA.stoppingTime_ne_top)

/-- **Data processing for runs of a fixed-budget algorithm**: for two runs (in two environments)
of a fixed-budget algorithm with budget `T`, the divergence between the laws of the outputs is
at most the divergence between the laws of the histories of the first `T` rounds. -/
lemma IsRun.klDiv_map_out_le (hA : A.IsFixedBudget T) (h : A.IsRun env O X Y out P)
    (h' : A.IsRun env' O' X' Y' out' P') :
    klDiv (P.map out) (P'.map out') ≤
      klDiv (P.map (history O X Y T)) (P'.map (history O' X' Y' T)) := by
  have hout : AEMeasurable out P := h.hasCondDistrib_output.aemeasurable_snd
  have hout' : AEMeasurable out' P' := h'.hasCondDistrib_output.aemeasurable_snd
  have hfin : Measurable (history O X Y T) := h.isAlgEnvSeq.measurable_history T
  have hfin' : Measurable (history O' X' Y' T) := h'.isAlgEnvSeq.measurable_history T
  let ι : Hist Unit 𝓐 𝓨 T → Σ n, Hist Unit 𝓐 𝓨 n := Sigma.mk (β := fun n ↦ Hist Unit 𝓐 𝓨 n) T
  have hι : Measurable ι := measurable_sigma_mk _
  have hsh : Measurable (A.stoppedHist O X Y) := by
    have : A.stoppedHist O X Y = ι ∘ history O X Y T := funext hA.stoppedHist_eq
    rw [this]
    exact hι.comp hfin
  have hsh' : Measurable (A.stoppedHist O' X' Y') := by
    have : A.stoppedHist O' X' Y' = ι ∘ history O' X' Y' T := funext hA.stoppedHist_eq
    rw [this]
    exact hι.comp hfin'
  calc klDiv (P.map out) (P'.map out')
      = klDiv ((P.map fun ω ↦ (A.stoppedHist O X Y ω, out ω)).map Prod.snd)
          ((P'.map fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)).map Prod.snd) := by
        rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
          (hsh.aemeasurable.prodMk hout), AEMeasurable.map_map_of_aemeasurable
          measurable_snd.aemeasurable (hsh'.aemeasurable.prodMk hout')]
        rfl
    _ ≤ klDiv (P.map fun ω ↦ (A.stoppedHist O X Y ω, out ω))
          (P'.map fun ω ↦ (A.stoppedHist O' X' Y' ω, out' ω)) := klDiv_map_le _ _ measurable_snd
    _ = klDiv (P.map (A.stoppedHist O X Y)) (P'.map (A.stoppedHist O' X' Y')) :=
        h.klDiv_map_stoppedHist_out_of_isFixedBudget hA h'
    _ = klDiv ((P.map (history O X Y T)).map ι) ((P'.map (history O' X' Y' T)).map ι) := by
        rw [Measure.map_map hι hfin, Measure.map_map hι hfin']
        congr 2 <;> exact funext fun ω ↦ hA.stoppedHist_eq ω
    _ ≤ klDiv (P.map (history O X Y T)) (P'.map (history O' X' Y' T)) := klDiv_map_le _ _ hι

/-- For a run of a fixed-budget algorithm with budget `0`, the law of the output is the output
rule applied to the empty history. -/
lemma IsRun.map_out_eq_of_isFixedBudget_zero (hA : A.IsFixedBudget 0)
    (h : A.IsRun env O X Y out P) :
    P.map out = A.output 0 Fin.elim0 := by
  have hout : AEMeasurable out P := h.hasCondDistrib_output.aemeasurable_snd
  have hsh : A.stoppedHist O X Y = fun _ ↦ (⟨0, Fin.elim0⟩ : Σ n, Hist Unit 𝓐 𝓨 n) := by
    funext ω
    rw [hA.stoppedHist_eq]
    congr
    exact Subsingleton.elim _ _
  have hjoint := h.hasCondDistrib_output.map_eq
  rw [hsh, Measure.map_const, measure_univ, one_smul] at hjoint
  calc P.map out
      = (P.map fun ω ↦ ((⟨0, Fin.elim0⟩ : Σ n, Hist Unit 𝓐 𝓨 n), out ω)).map Prod.snd := by
        rw [AEMeasurable.map_map_of_aemeasurable measurable_snd.aemeasurable
          (aemeasurable_const.prodMk hout)]
        rfl
    _ = (Measure.dirac (⟨0, Fin.elim0⟩ : Σ n, Hist Unit 𝓐 𝓨 n) ⊗ₘ A.outputKernel).map Prod.snd := by
        rw [hjoint]
    _ = A.output 0 Fin.elim0 := by
        ext s hs
        rw [Measure.map_apply measurable_snd hs, Measure.compProd_apply (measurable_snd hs),
          lintegral_dirac' _ (Kernel.measurable_kernel_prodMk_left (measurable_snd hs))]
        rfl

/-- For two runs of a fixed-budget algorithm with budget `0`, the laws of the outputs coincide:
their divergence is `0`. -/
lemma IsRun.klDiv_map_out_eq_zero (hA : A.IsFixedBudget 0) (h : A.IsRun env O X Y out P)
    (h' : A.IsRun env' O' X' Y' out' P') :
    klDiv (P.map out) (P'.map out') = 0 := by
  have : IsProbabilityMeasure (A.output 0 Fin.elim0) :=
    A.isProbabilityMeasure_output 0 _ (by unfold IsFixedBudget at hA; simp [hA])
  rw [h.map_out_eq_of_isFixedBudget_zero hA, h'.map_out_eq_of_isFixedBudget_zero hA, klDiv_self]

end IdentAlg

namespace LinearBandit

open IdentAlg

variable {E 𝓞 : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {m𝓞 : MeasurableSpace 𝓞}
  {𝒳 : Set E} {θ θ' : E} {A : IdentAlg 𝒳 ℝ 𝓞} {T : ℕ} {R : ℝ}
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → ℝ} {O' : ℕ → Ω' → Unit} {X' : ℕ → Ω' → 𝒳}
  {Y' : ℕ → Ω' → ℝ} {out : Ω → 𝓞} {out' : Ω' → 𝓞}

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
    (h' : A.IsRun (linearGaussianEnv 𝒳 θ') O' X' Y' out' P') {B : Set 𝓞} (hB : MeasurableSet B) :
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

namespace Learning.IdentAlg

variable {𝓐 𝓨 𝓞 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {m𝓞 : MeasurableSpace 𝓞} {Ω : Type*} {mΩ : MeasurableSpace Ω} {A : IdentAlg 𝓐 𝓨 𝓞} {T : ℕ}
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {P : Measure Ω} [IsProbabilityMeasure P]
  {out : Ω → 𝓞} {env : Environment Unit 𝓐 𝓨}

/-- The output rule of `A` at length `T` is the output kernel on histories of variable length
composed with `Sigma.mk T`. -/
lemma outputKernel_comap_sigma_mk (A : IdentAlg 𝓐 𝓨 𝓞) (T : ℕ) :
    A.outputKernel.comap (Sigma.mk (β := fun n ↦ Hist Unit 𝓐 𝓨 n) T) (measurable_sigma_mk T) =
      A.output T := by
  ext h s _
  rfl

/-- **The output of a run of a fixed-budget algorithm has conditional law `A.output T` given the
history of the first `T` rounds.** -/
lemma IsRun.hasCondDistrib_output_history (hA : A.IsFixedBudget T)
    (h : A.IsRun env O X Y out P) :
    HasCondDistrib out (history O X Y T) (A.output T) P := by
  have hX := h.isAlgEnvSeq.measurable_action
  have hY := h.isAlgEnvSeq.measurable_feedback
  have hfin : Measurable (history O X Y T) := h.isAlgEnvSeq.measurable_history T
  have hout : AEMeasurable out P := h.hasCondDistrib_output.aemeasurable_snd
  set ι : Hist Unit 𝓐 𝓨 T → Σ n, Hist Unit 𝓐 𝓨 n := Sigma.mk (β := fun n ↦ Hist Unit 𝓐 𝓨 n) T
    with hι_def
  have hι : MeasurableEmbedding ι := measurableEmbedding_sigma_mk T
  have hsh : A.stoppedHist O X Y = ι ∘ history O X Y T := funext hA.stoppedHist_eq
  have hg : MeasurableEmbedding (Prod.map ι (id : 𝓞 → 𝓞)) := hι.prodMap MeasurableEmbedding.id
  have h1 := h.hasCondDistrib_output.map_eq
  rw [hsh] at h1
  -- both sides of `h1` are images under `Prod.map ι id`
  have h2 : (P.map fun ω ↦ ((ι ∘ history O X Y T) ω, out ω)) =
      (P.map fun ω ↦ (history O X Y T ω, out ω)).map (Prod.map ι id) := by
    rw [AEMeasurable.map_map_of_aemeasurable hg.measurable.aemeasurable
      (hfin.aemeasurable.prodMk hout)]
    rfl
  have h3 : P.map (ι ∘ history O X Y T) ⊗ₘ A.outputKernel =
      (P.map (history O X Y T) ⊗ₘ A.output T).map (Prod.map ι id) := by
    rw [← outputKernel_comap_sigma_mk A T, ← Measure.map_map hι.measurable hfin]
    ext s hs
    rw [Measure.map_apply hg.measurable hs, Measure.compProd_apply (hg.measurable hs),
      Measure.compProd_apply hs, lintegral_map (Kernel.measurable_kernel_prodMk_left hs)
      hι.measurable]
    rfl
  rw [h2, h3] at h1
  refine ⟨hfin.aemeasurable.prodMk hout, ?_⟩
  calc P.map (fun ω ↦ (history O X Y T ω, out ω))
      = ((P.map fun ω ↦ (history O X Y T ω, out ω)).map (Prod.map ι id)).comap
          (Prod.map ι id) := (hg.comap_map _).symm
    _ = ((P.map (history O X Y T) ⊗ₘ A.output T).map (Prod.map ι id)).comap (Prod.map ι id) := by
        rw [h1]
    _ = P.map (history O X Y T) ⊗ₘ A.output T := hg.comap_map _

/-- For a fixed-budget algorithm whose output rule is the deterministic map `g` of the history,
the output of a run is `g` of the history of the first `T` rounds, almost surely. -/
lemma IsRun.output_ae_eq_of_output_eq_deterministic [MeasurableEq 𝓞] (hA : A.IsFixedBudget T)
    (h : A.IsRun env O X Y out P) {g : Hist Unit 𝓐 𝓨 T → 𝓞} (hg : Measurable g)
    (hout : A.output T = Kernel.deterministic g hg) :
    out =ᵐ[P] fun ω ↦ g (history O X Y T ω) := by
  have h1 := h.hasCondDistrib_output_history hA
  rw [hout] at h1
  have hX := h.isAlgEnvSeq.measurable_action
  have hY := h.isAlgEnvSeq.measurable_feedback
  have hfin : Measurable (history O X Y T) := h.isAlgEnvSeq.measurable_history T
  exact ae_eq_of_hasCondDistrib_deterministic hg hfin.aemeasurable
    h.hasCondDistrib_output.aemeasurable_snd h1

end Learning.IdentAlg
