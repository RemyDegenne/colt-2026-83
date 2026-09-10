/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.AlgorithmDensity
public import Maiti2026Power.LeanMachineLearning.AlgorithmPrefix

/-!
# Environment density along a history

Let `κ₀ κ : Kernel 𝓐 𝓨` be Markov kernels with `κ = κ₀.withDensity ρ` for a jointly measurable
`ρ : 𝓐 → 𝓨 → ℝ≥0∞`. For any algorithm, the law of the history of the first `n` rounds under the
stationary environment with reward kernel `κ` is the law under the environment with kernel `κ₀`
with density `envDensity ρ n h = ∏ t, ρ (x t) (y t)`
(`IsAlgEnvSeq.map_history_eq_withDensity_env`, blueprint `lem:env_likelihood_ratio`). This is
the environment analogue of LML's `Algorithm.density` / `IsAlgEnvSeq.hasLaw_history_withDensity`,
and the proof follows the same induction,
with the kernel-level identity `Kernel.compProd_withDensity_right` (a density on the
right factor of a composition-product of kernels, blueprint
`lem:pb_kernel_compProd_withDensity_right`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ}

/-- **A composition-product of kernels with a density on the right factor**:
`κ ⊗ₖ (η.withDensity f) = (κ ⊗ₖ η).withDensity (fun a (b, c) ↦ f (a, b) c)`. -/
lemma compProd_withDensity_right (κ : Kernel α β) [IsSFiniteKernel κ] (η : Kernel (α × β) γ)
    [IsSFiniteKernel η] {f : α × β → γ → ℝ≥0∞} (hf : Measurable (Function.uncurry f))
    [IsSFiniteKernel (η.withDensity f)] :
    κ ⊗ₖ η.withDensity f = (κ ⊗ₖ η).withDensity (fun a p ↦ f (a, p.1) p.2) := by
  have hg : Measurable (Function.uncurry fun a (p : β × γ) ↦ f (a, p.1) p.2) := by
    change Measurable fun q : α × (β × γ) ↦ Function.uncurry f ((q.1, q.2.1), q.2.2)
    exact hf.comp (by fun_prop)
  ext a s hs
  have hind : Measurable (s.indicator fun p : β × γ ↦ f (a, p.1) p.2) :=
    (hg.comp measurable_prodMk_left).indicator hs
  rw [Kernel.compProd_apply hs, Kernel.withDensity_apply' _ hg a s, ← lintegral_indicator hs,
    Kernel.lintegral_compProd _ _ _ hind]
  congr with b
  rw [Kernel.withDensity_apply' _ hf, ← lintegral_indicator (measurable_prodMk_left hs)]
  rfl

/-- `prodMkLeft` of a kernel with a density. -/
lemma prodMkLeft_withDensity (γ : Type*) [MeasurableSpace γ] (κ : Kernel α β)
    [IsSFiniteKernel κ] {ρ : α → β → ℝ≥0∞} (hρ : Measurable (Function.uncurry ρ)) :
    (κ.withDensity ρ).prodMkLeft γ = (κ.prodMkLeft γ).withDensity (fun p b ↦ ρ p.2 b) := by
  have hρ' : Measurable (Function.uncurry fun (p : γ × α) b ↦ ρ p.2 b) :=
    hρ.comp (measurable_fst.snd.prodMk measurable_snd)
  ext p s hs
  rw [prodMkLeft_apply', Kernel.withDensity_apply' _ hρ, Kernel.withDensity_apply' _ hρ',
    prodMkLeft_apply]

end ProbabilityTheory.Kernel

namespace Learning

variable {𝓐 𝓨 : Type*} [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]

/-- The product of the one-step densities `ρ (x t) (y t)` along a history of length `n`. -/
noncomputable def envDensity (ρ : 𝓐 → 𝓨 → ℝ≥0∞) (n : ℕ) (h : Hist Unit 𝓐 𝓨 n) : ℝ≥0∞ :=
  ∏ t, ρ (h t).action (h t).feedback

variable {ρ : 𝓐 → 𝓨 → ℝ≥0∞}

@[fun_prop]
lemma measurable_envDensity (hρ : Measurable (Function.uncurry ρ)) (n : ℕ) :
    Measurable (envDensity ρ n) :=
  Finset.measurable_prod _ fun t _ ↦ hρ.comp (measurable_pi_apply t).snd

omit [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] in
lemma envDensity_zero (ρ : 𝓐 → 𝓨 → ℝ≥0∞) (h : Hist Unit 𝓐 𝓨 0) : envDensity ρ 0 h = 1 := by
  simp [envDensity]

omit [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] in
lemma envDensity_snoc (ρ : 𝓐 → 𝓨 → ℝ≥0∞) {n : ℕ} (h : Hist Unit 𝓐 𝓨 n) (p : Round Unit 𝓐 𝓨) :
    envDensity ρ (n + 1) (Fin.snoc h p) = envDensity ρ n h * ρ p.action p.feedback := by
  simp [envDensity, Fin.prod_univ_castSucc]

section law

variable {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] {P : Measure Ω}
  {P₀ : Measure Ω₀} [IsProbabilityMeasure P] [IsProbabilityMeasure P₀]
  {O : ℕ → Ω → Unit} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {O₀ : ℕ → Ω₀ → Unit} {X₀ : ℕ → Ω₀ → 𝓐} {Y₀ : ℕ → Ω₀ → 𝓨}
  {alg : Algorithm Unit 𝓐 𝓨} {κ₀ κ : Kernel 𝓐 𝓨} [IsMarkovKernel κ₀] [IsMarkovKernel κ]

/-- **Environment likelihood ratio** (blueprint `lem:env_likelihood_ratio`): if
`κ = κ₀.withDensity ρ`, then for any algorithm the law of the history of the first `n` rounds
under the stationary environment with kernel `κ` is the law under the environment with kernel
`κ₀`, with density `envDensity ρ n = ∏ t < n, ρ (x t) (y t)`. -/
lemma IsAlgEnvSeq.map_history_eq_withDensity_env (hρ : Measurable (Function.uncurry ρ))
    (hκ : κ = κ₀.withDensity ρ) (h : IsAlgEnvSeq O X Y alg (stationaryEnv κ) P)
    (h₀ : IsAlgEnvSeq O₀ X₀ Y₀ alg (stationaryEnv κ₀) P₀) (n : ℕ) :
    P.map (history O X Y n) = (P₀.map (history O₀ X₀ Y₀ n)).withDensity (envDensity ρ n) := by
  induction n with
  | zero =>
    rw [(hasLaw_history_zero O X Y).map_eq, (hasLaw_history_zero O₀ X₀ Y₀).map_eq,
      show envDensity ρ 0 = 1 from funext (envDensity_zero ρ), withDensity_one]
  | succ n ih =>
    have hs : stepKernel alg (stationaryEnv κ) n =
        (stepKernel alg (stationaryEnv κ₀) n).withDensity fun _ p ↦ ρ p.action p.feedback := by
      have hρ' : Measurable
          (Function.uncurry fun (p : (Hist Unit 𝓐 𝓨 n × Unit) × 𝓐) b ↦ ρ p.2 b) :=
        hρ.comp (measurable_fst.snd.prodMk measurable_snd)
      have hρ'' : Measurable
          (Function.uncurry fun (_ : Hist Unit 𝓐 𝓨 n × Unit) (p : 𝓐 × 𝓨) ↦ ρ p.1 p.2) :=
        hρ.comp (measurable_snd.fst.prodMk measurable_snd.snd)
      have i1 : IsSFiniteKernel ((κ₀.prodMkLeft (Hist Unit 𝓐 𝓨 n × Unit)).withDensity
          fun p b ↦ ρ p.2 b) := by
        rw [← Kernel.prodMkLeft_withDensity _ _ hρ, ← hκ]
        infer_instance
      have h1 : stepKernel alg (stationaryEnv κ) n =
          Kernel.const _ (Measure.dirac ()) ⊗ₖ (alg.policy n ⊗ₖ
            (κ₀.prodMkLeft (Hist Unit 𝓐 𝓨 n × Unit)).withDensity fun p b ↦ ρ p.2 b) := by
        rw [stepKernel_def, obs_stationaryEnv, feedback_stationaryEnv, hκ,
          Kernel.prodMkLeft_withDensity _ _ hρ]
      have h2 : alg.policy n ⊗ₖ
            (κ₀.prodMkLeft (Hist Unit 𝓐 𝓨 n × Unit)).withDensity (fun p b ↦ ρ p.2 b) =
          (alg.policy n ⊗ₖ κ₀.prodMkLeft (Hist Unit 𝓐 𝓨 n × Unit)).withDensity
            fun _ p ↦ ρ p.1 p.2 :=
        Kernel.compProd_withDensity_right _ _ hρ'
      have i2 : IsSFiniteKernel
          ((alg.policy n ⊗ₖ κ₀.prodMkLeft (Hist Unit 𝓐 𝓨 n × Unit)).withDensity
            fun _ p ↦ ρ p.1 p.2) := by
        rw [← h2]
        infer_instance
      rw [h1, h2, Kernel.compProd_withDensity_right _ _ hρ'']
      rfl
    have : IsMarkovKernel ((stepKernel alg (stationaryEnv κ₀) n).withDensity
        fun _ p ↦ ρ p.action p.feedback) := by
      rw [← hs]
      infer_instance
    rw [h.map_history_succ, h₀.map_history_succ, ih, hs,
      Measure.withDensity_compProd_withDensity (by fun_prop) (by fun_prop),
      map_equiv_withDensity (by fun_prop)]
    congr 1
    funext q
    obtain ⟨h', p, rfl⟩ : ∃ h' p,
        q = (MeasurableEquiv.finSuccProd (Round Unit 𝓐 𝓨) n).symm (h', p) :=
      ⟨_, _, (MeasurableEquiv.symm_apply_apply _ q).symm⟩
    have hq : (MeasurableEquiv.finSuccProd (Round Unit 𝓐 𝓨) n) (Fin.snoc h' p) = (h', p) := by
      simp
    simp only [Function.comp_apply, MeasurableEquiv.symm_symm,
      MeasurableEquiv.finSuccProd_symm_apply, hq, envDensity_snoc]

end law

end Learning
