/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.GaussianLikelihood
public import COLT83.LeanMachineLearning.FixedBudget
public import COLT83.LeanMachineLearning.Run
public import COLT83.LeanMachineLearning.TwoPoint

/-!
# The law of a run as a Markov kernel in the reward vector

For an algorithm `alg` with actions in `𝒳` and a budget `T`, the law of the history of `T` rounds
under the reward vector `θ` is `histKernel alg T θ = noiseHistLaw.withDensity (likelihood θ)`,
where `noiseHistLaw` is the law under pure noise (`θ = 0`); since the likelihood is jointly
measurable, this is a Markov kernel in `θ` (`histKernel`), which agrees with the law of the
history of every algorithm-environment sequence under `θ`
(`IsAlgEnvSeq.map_finHistory_eq_histKernel`). For a fixed-budget identification algorithm `A`,
the law of (history, recommendation) is the Markov kernel `pairKernel A T = histKernel ⊗ₖ output`
(`IsRun.hasLaw_finHistory_out_pairKernel`), and the PAC property of `A` is a statement about
`pairKernel A T θ` for every `θ` (`IsPAC.le_measureReal_pairKernel`,
`IsPAC.integral_simpleRegret_pairKernel_le`).

Blueprint: `lem:pb_kernel_of_likelihood`. This construction sidesteps the measurability of
`θ ↦ trajMeasure alg (linearGaussianEnv 𝒳 θ)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning Real
open scoped ENNReal RealInnerProductSpace

universe u

namespace Learning.LinearBandit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [SecondCountableTopology E] {𝒳 : Set E}

/-- The law of the history of `T` rounds of `alg` under pure noise (`θ = 0`). -/
noncomputable def noiseHistLaw (alg : Algorithm 𝒳 ℝ) (T : ℕ) : Measure (Fin T → 𝒳 × ℝ) :=
  (trajMeasure alg (linearGaussianEnv 𝒳 0)).map (finHistory IT.action IT.feedback T)

instance (alg : Algorithm 𝒳 ℝ) (T : ℕ) : IsProbabilityMeasure (noiseHistLaw alg T) :=
  Measure.isProbabilityMeasure_map (IdentAlg.measurable_finHistory_traj T).aemeasurable

lemma measurable_uncurry_ofReal_likelihood (T : ℕ) :
    Measurable (Function.uncurry fun (θ : E) (h : Fin T → 𝒳 × ℝ) ↦
      ENNReal.ofReal (likelihood θ h)) :=
  ENNReal.measurable_ofReal.comp (measurable_likelihood_prod T)

/-- **The law of the history under `θ` as a Markov kernel in `θ`**: the pure-noise law with
density `likelihood θ`. -/
noncomputable def histKernel (alg : Algorithm 𝒳 ℝ) (T : ℕ) : Kernel E (Fin T → 𝒳 × ℝ) :=
  Kernel.withDensity (Kernel.const E (noiseHistLaw alg T))
    fun θ h ↦ ENNReal.ofReal (likelihood θ h)

lemma histKernel_apply (alg : Algorithm 𝒳 ℝ) (T : ℕ) (θ : E) :
    histKernel alg T θ =
      (noiseHistLaw alg T).withDensity fun h ↦ ENNReal.ofReal (likelihood θ h) := by
  rw [histKernel, Kernel.withDensity_apply _ (measurable_uncurry_ofReal_likelihood T),
    Kernel.const_apply]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝒳 ℝ} {θ : E}

/-- The history of any algorithm-environment sequence under `θ` has law `histKernel alg T θ`. -/
lemma _root_.Learning.IsAlgEnvSeq.map_finHistory_eq_histKernel
    (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P) (T : ℕ) :
    P.map (finHistory X Y T) = histKernel alg T θ := by
  rw [histKernel_apply, noiseHistLaw]
  exact h.map_finHistory_eq_withDensity_likelihood (IT.isAlgEnvSeq_trajMeasure alg _) T

instance (alg : Algorithm 𝒳 ℝ) (T : ℕ) : IsMarkovKernel (histKernel (E := E) alg T) :=
  ⟨fun θ ↦ by
    rw [← (IT.isAlgEnvSeq_trajMeasure alg (linearGaussianEnv 𝒳 θ)).map_finHistory_eq_histKernel T]
    exact Measure.isProbabilityMeasure_map (IdentAlg.measurable_finHistory_traj T).aemeasurable⟩

lemma _root_.Learning.IsAlgEnvSeq.hasLaw_finHistory_histKernel
    (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P) (T : ℕ) :
    HasLaw (finHistory X Y T) (histKernel alg T θ) P := by
  have hX := h.measurable_action
  have hY := h.measurable_feedback
  have hfin : Measurable (finHistory X Y T) := by unfold finHistory; fun_prop
  exact ⟨hfin.aemeasurable, h.map_finHistory_eq_histKernel T⟩

section identAlg

variable {A : IdentAlg 𝒳 ℝ 𝒳} {T : ℕ}

/-- **The law of (history, recommendation) of the fixed-budget algorithm `A` under `θ`, as a
Markov kernel in `θ`**: the history kernel composed with the output rule. -/
noncomputable def pairKernel (A : IdentAlg 𝒳 ℝ 𝒳) (T : ℕ) : Kernel E ((Fin T → 𝒳 × ℝ) × 𝒳) :=
  histKernel A.alg T ⊗ₖ (A.output T).prodMkLeft E

instance [IsMarkovKernel (A.output T)] : IsMarkovKernel (pairKernel (E := E) A T) := by
  unfold pairKernel
  infer_instance

lemma pairKernel_apply (θ : E) :
    pairKernel A T θ = histKernel A.alg T θ ⊗ₘ A.output T := by
  rw [pairKernel, Kernel.compProd_apply_eq_compProd_sectR]
  congr 1

/-- For any run of `A` under `θ`, (history of the `T` rounds, recommendation) has law
`pairKernel A T θ`. -/
lemma _root_.Learning.IdentAlg.IsRun.hasLaw_finHistory_out_pairKernel
    (hA : A.IsFixedBudget T) {out : Ω → 𝒳}
    (h : A.IsRun (linearGaussianEnv 𝒳 θ) X Y out P) :
    HasLaw (fun ω ↦ (finHistory X Y T ω, out ω)) (pairKernel A T θ) P := by
  rw [pairKernel_apply]
  exact (h.isAlgEnvSeq.hasLaw_finHistory_histKernel T).prodMk_of_hasCondDistrib
    (h.hasCondDistrib_output_finHistory hA)

lemma measurableSet_simpleRegret_le (θ : E) (ε : ℝ) :
    MeasurableSet {p : (Fin T → 𝒳 × ℝ) × 𝒳 | simpleRegret 𝒳 θ p.2 ≤ ε} :=
  measurableSet_le (continuous_const.sub ((continuous_subtype_val.comp continuous_snd).inner
    continuous_const)).measurable measurable_const

end identAlg

section pac

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [SecondCountableTopology E] {𝒳 : Set E}
  {A : IdentAlg 𝒳 ℝ 𝒳} {T : ℕ} {ε δ : ℝ}

/-- **The PAC property on the kernel**: for every `θ`, the recommendation is `ε`-optimal with
probability at least `1 - δ` under `pairKernel A T θ`. -/
lemma _root_.Learning.LinearBandit.IsPAC.le_measureReal_pairKernel (hpac : IsPAC 𝒳 A ε δ)
    (hA : A.IsFixedBudget T) (θ : E) :
    1 - δ ≤ (pairKernel A T θ).real {p | simpleRegret 𝒳 θ p.2 ≤ ε} := by
  have := hA.isMarkovKernel_output
  have hrun := hA.isRun_fixedBudgetRunMeasure (env := linearGaussianEnv 𝒳 θ)
  have hlaw := hrun.hasLaw_finHistory_out_pairKernel hA
  have hpac' := hpac θ (A.fixedBudgetRunMeasure (linearGaussianEnv 𝒳 θ) T) _ _ _ hrun
  rw [← hlaw.measureReal_eq (p := fun p ↦ simpleRegret 𝒳 θ p.2 ≤ ε)
    (measurableSet_simpleRegret_le θ ε)]
  exact hpac'

/-- **Expected regret of a PAC algorithm** under `pairKernel A T θ`: if the simple regret on the
instance `θ` is between `0` and `Z ≥ ε` on `𝒳`, then `E_θ[r] ≤ ε + (Z - ε) δ`. -/
lemma _root_.Learning.LinearBandit.IsPAC.integral_simpleRegret_pairKernel_le
    (hpac : IsPAC 𝒳 A ε δ) (hA : A.IsFixedBudget T)
    (θ : E) {Z : ℝ} (h0 : ∀ x ∈ 𝒳, 0 ≤ simpleRegret 𝒳 θ x) (hZ : ∀ x ∈ 𝒳, simpleRegret 𝒳 θ x ≤ Z)
    (hεZ : ε ≤ Z) :
    ∫ p, simpleRegret 𝒳 θ p.2 ∂(pairKernel A T θ) ≤ ε + (Z - ε) * δ := by
  have := hA.isMarkovKernel_output
  exact integral_simpleRegret_le_of_measureReal_le (P := pairKernel A T θ) measurable_snd h0 hZ
    hεZ (hpac.le_measureReal_pairKernel hA θ)

end pac

end Learning.LinearBandit
