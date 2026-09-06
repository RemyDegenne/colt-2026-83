/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.AlgorithmDensity
public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import COLT83.LeanMachineLearning.AlgorithmPrefix

/-!
# Environment density along a history

Let `κ₀ κ : Kernel 𝓐 𝓨` be Markov kernels with `κ = κ₀.withDensity ρ` for a jointly measurable
`ρ : 𝓐 → 𝓨 → ℝ≥0∞`. For any algorithm, the law of the history of the first `n` rounds under the
stationary environment with reward kernel `κ` is the law under the environment with kernel `κ₀`
with density `envDensity ρ n h = ∏ t, ρ (x t) (y t)`
(`IsAlgEnvSeq.map_finHistory_eq_withDensity_env`, blueprint `lem:env_likelihood_ratio`). This is
the environment analogue of LML's `Algorithm.density` / `IsAlgEnvSeq.hasLaw_history_withDensity`,
and the proof follows the same
induction, with the kernel-level identity `Kernel.compProd_withDensity_right` (a density on the
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
noncomputable def envDensity (ρ : 𝓐 → 𝓨 → ℝ≥0∞) (n : ℕ) (h : Fin n → 𝓐 × 𝓨) : ℝ≥0∞ :=
  ∏ t, ρ (h t).1 (h t).2

variable {ρ : 𝓐 → 𝓨 → ℝ≥0∞}

@[fun_prop]
lemma measurable_envDensity (hρ : Measurable (Function.uncurry ρ)) (n : ℕ) :
    Measurable (envDensity ρ n) :=
  Finset.measurable_prod _ fun t _ ↦ hρ.comp (measurable_pi_apply t)

omit [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] in
lemma envDensity_zero (ρ : 𝓐 → 𝓨 → ℝ≥0∞) (h : Fin 0 → 𝓐 × 𝓨) : envDensity ρ 0 h = 1 := by
  simp [envDensity]

omit [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] in
lemma envDensity_snoc (ρ : 𝓐 → 𝓨 → ℝ≥0∞) {n : ℕ} (h : Fin n → 𝓐 × 𝓨) (p : 𝓐 × 𝓨) :
    envDensity ρ (n + 1) (Fin.snoc h p) = envDensity ρ n h * ρ p.1 p.2 := by
  simp [envDensity, Fin.prod_univ_castSucc]

/-- The history of the first `n + 2` rounds obtained by appending a step to a history up to time
`n`. -/
lemma toFinHistory_IicSuccProd_symm (n : ℕ) (h : Iic n → 𝓐 × 𝓨) (p : 𝓐 × 𝓨) :
    toFinHistory (n + 1) ((MeasurableEquiv.IicSuccProd (fun _ : ℕ ↦ 𝓐 × 𝓨) n).symm (h, p)) =
      Fin.snoc (toFinHistory n h) p := by
  set h' := (MeasurableEquiv.IicSuccProd (fun _ : ℕ ↦ 𝓐 × 𝓨) n).symm (h, p) with hh'
  have he : (MeasurableEquiv.IicSuccProd (fun _ : ℕ ↦ 𝓐 × 𝓨) n) h' = (h, p) :=
    MeasurableEquiv.apply_symm_apply _ _
  rw [Kernel.MeasurableEquiv.IicSuccProd_apply] at he
  obtain ⟨he1, he2⟩ := Prod.mk.inj he
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · rw [Fin.snoc_last, ← he2]
    rfl
  · rw [Fin.snoc_castSucc, ← he1]
    rfl

section law

variable {Ω Ω₀ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₀] {P : Measure Ω}
  {P₀ : Measure Ω₀} [IsProbabilityMeasure P] [IsProbabilityMeasure P₀]
  {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {X₀ : ℕ → Ω₀ → 𝓐} {Y₀ : ℕ → Ω₀ → 𝓨}
  {alg : Algorithm 𝓐 𝓨} {κ₀ κ : Kernel 𝓐 𝓨} [IsMarkovKernel κ₀] [IsMarkovKernel κ]

/-- **Environment likelihood ratio**, history form: under `κ = κ₀.withDensity ρ`, the law of the
history up to time `n` is the law under `κ₀` with density `∏ t ≤ n, ρ (x t) (y t)`. -/
lemma IsAlgEnvSeq.map_history_eq_withDensity_env (hρ : Measurable (Function.uncurry ρ))
    (hκ : κ = κ₀.withDensity ρ) (h : IsAlgEnvSeq X Y alg (stationaryEnv κ) P)
    (h₀ : IsAlgEnvSeq X₀ Y₀ alg (stationaryEnv κ₀) P₀) (n : ℕ) :
    P.map (history X Y n) =
      (P₀.map (history X₀ Y₀ n)).withDensity (envDensity ρ (n + 1) ∘ toFinHistory n) := by
  induction n with
  | zero =>
    rw [h.hasLaw_history_zero.map_eq, h₀.hasLaw_history_zero.map_eq, h.hasLaw_step_zero.map_eq,
      h₀.hasLaw_step_zero.map_eq, ν0_stationaryEnv, ν0_stationaryEnv]
    have : IsSFiniteKernel (κ₀.withDensity ρ) := by rw [← hκ]; infer_instance
    rw [hκ, Measure.compProd_withDensity hρ, map_equiv_withDensity (by fun_prop)]
    congr 1
    funext h'
    simp [envDensity, toFinHistory, MeasurableEquiv.piUnique_apply]
    rfl
  | succ n ih =>
    have hs : stepKernel alg (stationaryEnv κ) n =
        (stepKernel alg (stationaryEnv κ₀) n).withDensity fun _ p ↦ ρ p.1 p.2 := by
      have hρ' : Measurable (Function.uncurry fun (p : (Iic n → 𝓐 × 𝓨) × 𝓐) b ↦ ρ p.2 b) :=
        hρ.comp (measurable_fst.snd.prodMk measurable_snd)
      have : IsSFiniteKernel ((κ₀.prodMkLeft (Iic n → 𝓐 × 𝓨)).withDensity
          fun p b ↦ ρ p.2 b) := by
        rw [← Kernel.prodMkLeft_withDensity _ _ hρ, ← hκ]
        infer_instance
      have h1 : stepKernel alg (stationaryEnv κ) n =
          alg.policy n ⊗ₖ (κ₀.prodMkLeft (Iic n → 𝓐 × 𝓨)).withDensity fun p b ↦ ρ p.2 b := by
        rw [stepKernel_def, feedback_stationaryEnv, hκ, Kernel.prodMkLeft_withDensity _ _ hρ]
      rw [h1, Kernel.compProd_withDensity_right _ _ hρ']
      rfl
    have : IsMarkovKernel ((stepKernel alg (stationaryEnv κ₀) n).withDensity
        fun _ p ↦ ρ p.1 p.2) := by
      rw [← hs]
      infer_instance
    simp_rw [history_succ]
    rw [← Measure.map_map (by fun_prop), ← Measure.map_map (by fun_prop)]
    rotate_left
    · exact (h₀.measurable_history n).prodMk (h₀.measurable_step (n + 1))
    · exact (h.measurable_history n).prodMk (h.measurable_step (n + 1))
    rw [(h.hasCondDistrib_step n).map_eq, (h₀.hasCondDistrib_step n).map_eq, ih, hs,
      Measure.compProd_withDensity_withDensity (by fun_prop) (by fun_prop),
      map_equiv_withDensity (by fun_prop)]
    congr 1
    funext q
    obtain ⟨h', p, rfl⟩ : ∃ h' p,
        q = (MeasurableEquiv.IicSuccProd (fun _ : ℕ ↦ 𝓐 × 𝓨) n).symm (h', p) :=
      ⟨_, _, (MeasurableEquiv.symm_apply_apply _ q).symm⟩
    simp only [Function.comp_apply, MeasurableEquiv.symm_symm, MeasurableEquiv.apply_symm_apply,
      toFinHistory_IicSuccProd_symm, envDensity_snoc]

/-- **Environment likelihood ratio** (blueprint `lem:env_likelihood_ratio`): if
`κ = κ₀.withDensity ρ`, then for any algorithm the law of the history of the first `n` rounds
under the stationary environment with kernel `κ` is the law under the environment with kernel
`κ₀`, with density `envDensity ρ n = ∏ t < n, ρ (x t) (y t)`. -/
lemma IsAlgEnvSeq.map_finHistory_eq_withDensity_env (hρ : Measurable (Function.uncurry ρ))
    (hκ : κ = κ₀.withDensity ρ) (h : IsAlgEnvSeq X Y alg (stationaryEnv κ) P)
    (h₀ : IsAlgEnvSeq X₀ Y₀ alg (stationaryEnv κ₀) P₀) (n : ℕ) :
    P.map (finHistory X Y n) = (P₀.map (finHistory X₀ Y₀ n)).withDensity (envDensity ρ n) := by
  cases n with
  | zero =>
    have h1 : finHistory X Y 0 = fun _ ↦ (isEmptyElim : Fin 0 → 𝓐 × 𝓨) :=
      funext fun _ ↦ funext fun i ↦ i.elim0
    have h1' : finHistory X₀ Y₀ 0 = fun _ ↦ (isEmptyElim : Fin 0 → 𝓐 × 𝓨) :=
      funext fun _ ↦ funext fun i ↦ i.elim0
    have h2 : envDensity ρ 0 = 1 := funext (envDensity_zero ρ)
    rw [h1, h1', Measure.map_const, Measure.map_const, measure_univ, measure_univ, one_smul, h2,
      withDensity_one]
  | succ n =>
    rw [finHistory_succ_eq_toFinHistory_comp, finHistory_succ_eq_toFinHistory_comp,
      ← Measure.map_map (measurable_toFinHistory n) (h.measurable_history n),
      ← Measure.map_map (measurable_toFinHistory n) (h₀.measurable_history n),
      h.map_history_eq_withDensity_env hρ hκ h₀ n,
      map_withDensity_comp (measurable_toFinHistory n) (measurable_envDensity hρ (n + 1))]

end law

end Learning
