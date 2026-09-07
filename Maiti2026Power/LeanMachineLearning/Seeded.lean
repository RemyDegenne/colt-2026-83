/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Maiti2026Power.Mathlib.Probability.CondDistribConst
public import Maiti2026Power.LeanMachineLearning.FixedBudget
public import Maiti2026Power.LeanMachineLearning.LinearBandit

/-!
# Seeded algorithms: internal randomness as a product measure

A *seeded algorithm* (`SeededAlg 𝓐 𝓨 U`) draws at every round a fresh seed `u ~ seed` and plays
the action `next n h u`, a measurable function of the history `h` and of the seed. It is an LML
algorithm (`SeededAlg.toAlgorithm`) whose policy at round `n` is the kernel
`h ↦ seed.map (next n h)`.

A *noise environment* (`noiseEnv μe F`) answers the action `x` with `F x e` for a fresh noise
`e ~ μe`; the linear Gaussian environment is the case `F x e = ⟪x, θ⟫ + e` with `e ~ N(0, 1)`
(`LinearBandit.linearGaussianEnv_eq_noiseEnv`).

The main result is the **seed representation** of a run: on the product space `ℕ → U × E` with the
product measure `seedMeasure = ⊗ₙ (seed ⊗ μe)`, the recursively defined action-feedback pairs
`seedStep n` form an algorithm-environment sequence for the seeded algorithm and the noise
environment (`SeededAlg.isAlgEnvSeq_seed`). Since the law of the history is determined by the
algorithm and the environment (`IsAlgEnvSeq.map_history_eq`), the history of *any* run has the law
of `seedFinHist T` under `seedMeasure` (`SeededAlg.IsAlgEnvSeq.map_finHistory_eq_seed`), and the
PAC property of a fixed-budget seeded algorithm with deterministic output reduces to a computation
on the product space (`SeededAlg.isPAC_fixedBudget_deterministic`,
`SeededAlg.linearBandit_isPAC_fixedBudget_deterministic`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

universe u

namespace Learning

section Uniqueness

variable {𝓐 𝓨 Ω Ω' : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
  {X' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨} {alg : Algorithm 𝓐 𝓨} {env : Environment 𝓐 𝓨}
  {P : Measure Ω} {P' : Measure Ω'} [IsFiniteMeasure P] [IsFiniteMeasure P']

/-- The law of the history of an algorithm-environment sequence is determined by the algorithm
and the environment. -/
lemma IsAlgEnvSeq.map_history_eq (h : IsAlgEnvSeq X Y alg env P)
    (h' : IsAlgEnvSeq X' Y' alg env P') (n : ℕ) :
    P.map (history X Y n) = P'.map (history X' Y' n) := by
  induction n with
  | zero =>
    rw [h.hasLaw_history_zero.map_eq, h'.hasLaw_history_zero.map_eq, h.hasLaw_step_zero.map_eq,
      h'.hasLaw_step_zero.map_eq]
  | succ n ih =>
    simp_rw [history_succ]
    rw [← Measure.map_map (by fun_prop)
        ((h.measurable_history n).prodMk (h.measurable_step (n + 1))),
      ← Measure.map_map (by fun_prop)
        ((h'.measurable_history n).prodMk (h'.measurable_step (n + 1))),
      (h.hasCondDistrib_step n).map_eq, (h'.hasCondDistrib_step n).map_eq, ih]

/-- The law of the history of the first `T` rounds of an algorithm-environment sequence is
determined by the algorithm and the environment. -/
lemma IsAlgEnvSeq.map_finHistory_eq [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (h : IsAlgEnvSeq X Y alg env P) (h' : IsAlgEnvSeq X' Y' alg env P') (T : ℕ) :
    P.map (finHistory X Y T) = P'.map (finHistory X' Y' T) := by
  cases T with
  | zero =>
    rw [show finHistory X Y 0 = fun _ ↦ (finZeroElim : Fin 0 → 𝓐 × 𝓨) from
        funext fun _ ↦ Subsingleton.elim _ _,
      show finHistory X' Y' 0 = fun _ ↦ (finZeroElim : Fin 0 → 𝓐 × 𝓨) from
        funext fun _ ↦ Subsingleton.elim _ _,
      Measure.map_const, Measure.map_const, measure_univ, measure_univ]
  | succ n =>
    rw [IdentAlg.finHistory_succ_eq_comp_history, IdentAlg.finHistory_succ_eq_comp_history,
      ← Measure.map_map (by fun_prop) (h.measurable_history n),
      ← Measure.map_map (by fun_prop) (h'.measurable_history n), h.map_history_eq h' n]

end Uniqueness

variable {𝓐 𝓨 U E : Type*} [MeasurableSpace 𝓐] [MeasurableSpace 𝓨] [MeasurableSpace U]

/-- A *seeded algorithm*: at every round a fresh seed `u ~ seed` is drawn and the action
`next n h u` is played, where `h` is the history of the previous rounds (the first action is
`act0 u`). -/
structure SeededAlg (𝓐 𝓨 U : Type*) [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]
    [MeasurableSpace U] where
  /-- The law of the seeds. -/
  seed : Measure U
  [isProbabilityMeasure_seed : IsProbabilityMeasure seed]
  /-- The first action as a function of the seed. -/
  act0 : U → 𝓐
  measurable_act0 : Measurable act0
  /-- The action at round `n + 1` as a function of the history of rounds `0..n` and the seed. -/
  next : (n : ℕ) → (Iic n → 𝓐 × 𝓨) → U → 𝓐
  measurable_next : ∀ n, Measurable (Function.uncurry (next n))

namespace SeededAlg

variable (A : SeededAlg 𝓐 𝓨 U)

instance : IsProbabilityMeasure A.seed := A.isProbabilityMeasure_seed

/-- The policy kernel at round `n`: `h ↦ seed.map (next n h)`. -/
noncomputable def policy (n : ℕ) : Kernel (Iic n → 𝓐 × 𝓨) 𝓐 :=
  Kernel.mapOfConst A.seed (A.next n) (A.measurable_next n)

lemma policy_apply (n : ℕ) (h : Iic n → 𝓐 × 𝓨) : A.policy n h = A.seed.map (A.next n h) :=
  Kernel.mapOfConst_apply _ h

instance (n : ℕ) : IsMarkovKernel (A.policy n) := by
  unfold policy
  infer_instance

/-- The seeded algorithm as an LML algorithm. -/
noncomputable def toAlgorithm : Algorithm 𝓐 𝓨 where
  policy := A.policy
  p0 := A.seed.map A.act0
  hp0 := Measure.isProbabilityMeasure_map A.measurable_act0.aemeasurable

@[simp] lemma policy_toAlgorithm (n : ℕ) : A.toAlgorithm.policy n = A.policy n := rfl

@[simp] lemma p0_toAlgorithm : A.toAlgorithm.p0 = A.seed.map A.act0 := rfl

end SeededAlg

section NoiseEnv

variable [MeasurableSpace E] (μe : Measure E) [IsProbabilityMeasure μe] (F : 𝓐 → E → 𝓨)
  (hF : Measurable (Function.uncurry F))

/-- The reward kernel `x ↦ law of F x e` for a fresh noise `e ~ μe`. -/
noncomputable def noiseKernel : Kernel 𝓐 𝓨 := Kernel.mapOfConst μe F hF

instance : IsMarkovKernel (noiseKernel μe F hF) := by
  unfold noiseKernel
  infer_instance

lemma noiseKernel_apply (x : 𝓐) : noiseKernel μe F hF x = μe.map (F x) :=
  Kernel.mapOfConst_apply _ x

/-- The stationary environment answering the action `x` with `F x e`, `e ~ μe`. -/
noncomputable def noiseEnv : Environment 𝓐 𝓨 := stationaryEnv (noiseKernel μe F hF)

lemma ν0_noiseEnv : (noiseEnv μe F hF).ν0 = noiseKernel μe F hF := ν0_stationaryEnv _

lemma feedback_noiseEnv (n : ℕ) :
    (noiseEnv μe F hF).feedback n = (noiseKernel μe F hF).prodMkLeft _ :=
  feedback_stationaryEnv _ n

end NoiseEnv

section LinearGaussian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] (𝒳 : Set E) (θ : E)

/-- The noise function of the linear Gaussian bandit: `F x e = ⟪x, θ⟫ + e`. -/
def LinearBandit.linearNoise (x : 𝒳) (e : ℝ) : ℝ := inner ℝ (x : E) θ + e

lemma LinearBandit.measurable_uncurry_linearNoise :
    Measurable (Function.uncurry (LinearBandit.linearNoise 𝒳 θ)) := by
  unfold LinearBandit.linearNoise Function.uncurry
  fun_prop

/-- The linear Gaussian environment is the noise environment with `F x e = ⟪x, θ⟫ + e` and
`e ~ N(0, 1)`. -/
lemma LinearBandit.linearGaussianEnv_eq_noiseEnv :
    LinearBandit.linearGaussianEnv 𝒳 θ = noiseEnv (gaussianReal 0 1) (LinearBandit.linearNoise 𝒳 θ)
      (LinearBandit.measurable_uncurry_linearNoise 𝒳 θ) := by
  have hk : LinearBandit.linearGaussianKernel 𝒳 θ
      = noiseKernel (gaussianReal 0 1) (LinearBandit.linearNoise 𝒳 θ)
        (LinearBandit.measurable_uncurry_linearNoise 𝒳 θ) := by
    ext x : 1
    rw [noiseKernel_apply]
    change gaussianReal (inner ℝ (x : E) θ) 1
      = (gaussianReal 0 1).map (fun e ↦ inner ℝ (x : E) θ + e)
    rw [gaussianReal_map_const_add, zero_add]
  have key : ∀ (κ₁ κ₂ : Kernel 𝒳 ℝ) [IsMarkovKernel κ₁] [IsMarkovKernel κ₂], κ₁ = κ₂ →
      stationaryEnv κ₁ = stationaryEnv κ₂ := by
    rintro κ₁ κ₂ _ _ rfl
    congr
  exact key _ _ hk

end LinearGaussian

namespace SeededAlg

variable (A : SeededAlg 𝓐 𝓨 U) (F : 𝓐 → E → 𝓨)

/-- The action-feedback pair at round `n` as a function of the seeds and noises. -/
noncomputable def seedStep (n : ℕ) (ω : ℕ → U × E) : 𝓐 × 𝓨 :=
  match n with
  | 0 => (A.act0 (ω 0).1, F (A.act0 (ω 0).1) (ω 0).2)
  | n + 1 =>
    let x := A.next n (fun i : Iic n ↦ seedStep (i : ℕ) ω) (ω (n + 1)).1
    (x, F x (ω (n + 1)).2)
termination_by n
decreasing_by exact Nat.lt_succ_of_le (Finset.mem_Iic.1 i.2)

lemma seedStep_zero (ω : ℕ → U × E) :
    A.seedStep F 0 ω = (A.act0 (ω 0).1, F (A.act0 (ω 0).1) (ω 0).2) := by
  rw [seedStep]

lemma seedStep_succ (n : ℕ) (ω : ℕ → U × E) :
    A.seedStep F (n + 1) ω
      = (A.next n (fun i : Iic n ↦ A.seedStep F i ω) (ω (n + 1)).1,
        F (A.next n (fun i : Iic n ↦ A.seedStep F i ω) (ω (n + 1)).1) (ω (n + 1)).2) := by
  rw [seedStep]

lemma seedFeedback_eq (n : ℕ) (ω : ℕ → U × E) :
    (A.seedStep F n ω).2 = F (A.seedStep F n ω).1 (ω n).2 := by
  cases n with
  | zero => rw [seedStep_zero]
  | succ n => rw [seedStep_succ]

/-- The action at round `n` as a function of the seeds and noises. -/
noncomputable def seedAction (n : ℕ) (ω : ℕ → U × E) : 𝓐 := (A.seedStep F n ω).1

/-- The feedback at round `n` as a function of the seeds and noises. -/
noncomputable def seedFeedback (n : ℕ) (ω : ℕ → U × E) : 𝓨 := (A.seedStep F n ω).2

lemma history_seed (n : ℕ) :
    history (A.seedAction F) (A.seedFeedback F) n = fun ω (i : Iic n) ↦ A.seedStep F i ω := rfl

/-- The history of the first `T` rounds as a function of the seeds and noises. -/
noncomputable def seedFinHist (T : ℕ) (ω : ℕ → U × E) : Fin T → 𝓐 × 𝓨 :=
  fun i ↦ A.seedStep F i ω

lemma finHistory_seed (T : ℕ) :
    finHistory (A.seedAction F) (A.seedFeedback F) T = A.seedFinHist F T := rfl

/-- The restriction of a seed sequence to the coordinates `0..n`. -/
def seedPrefix (n : ℕ) (ω : ℕ → U × E) : Iic n → U × E := fun i ↦ ω i

variable {A F}

lemma seedStep_congr {n : ℕ} {ω ω' : ℕ → U × E} (h : ∀ k ≤ n, ω k = ω' k) :
    A.seedStep F n ω = A.seedStep F n ω' := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => rw [seedStep_zero, seedStep_zero, h 0 le_rfl]
    | succ n =>
      have hfun : (fun i : Iic n ↦ A.seedStep F i ω) = fun i : Iic n ↦ A.seedStep F i ω' :=
        funext fun i ↦ ih i (Nat.lt_succ_of_le (mem_Iic.1 i.2))
          fun k hk ↦ h k (hk.trans (Nat.le_succ_of_le (mem_Iic.1 i.2)))
      rw [seedStep_succ, seedStep_succ, hfun, h (n + 1) le_rfl]

variable [MeasurableSpace E]

lemma measurable_seedStep (hF : Measurable (Function.uncurry F)) (n : ℕ) :
    Measurable (A.seedStep F n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero =>
      have h0 : Measurable fun ω : ℕ → U × E ↦ ω 0 := measurable_pi_apply 0
      have e : A.seedStep F 0 = fun ω ↦ (A.act0 (ω 0).1, F (A.act0 (ω 0).1) (ω 0).2) :=
        funext (A.seedStep_zero F)
      rw [e]
      exact (A.measurable_act0.comp h0.fst).prodMk
        (hF.comp ((A.measurable_act0.comp h0.fst).prodMk h0.snd))
    | succ n =>
      have hn : Measurable fun ω : ℕ → U × E ↦ ω (n + 1) := measurable_pi_apply _
      have hh : Measurable fun ω ↦ (fun i : Iic n ↦ A.seedStep F i ω) :=
        measurable_pi_lambda _ fun i ↦ ih i (Nat.lt_succ_of_le (mem_Iic.1 i.2))
      have hx : Measurable fun ω ↦ A.next n (fun i : Iic n ↦ A.seedStep F i ω) (ω (n + 1)).1 :=
        (A.measurable_next n).comp (hh.prodMk hn.fst)
      have e : A.seedStep F (n + 1) = fun ω ↦
          (A.next n (fun i : Iic n ↦ A.seedStep F i ω) (ω (n + 1)).1,
            F (A.next n (fun i : Iic n ↦ A.seedStep F i ω) (ω (n + 1)).1) (ω (n + 1)).2) :=
        funext (A.seedStep_succ F n)
      rw [e]
      exact hx.prodMk (hF.comp (hx.prodMk hn.snd))

lemma measurable_seedFinHist (hF : Measurable (Function.uncurry F)) (T : ℕ) :
    Measurable (A.seedFinHist F T) :=
  measurable_pi_lambda _ fun i ↦ measurable_seedStep hF i

variable (A F) (μe : Measure E) [IsProbabilityMeasure μe]
  (hF : Measurable (Function.uncurry F))

/-- The product measure of the seeds and noises: coordinate `n` is `(u n, e n) ~ seed ⊗ μe`. -/
noncomputable def seedMeasure : Measure (ℕ → U × E) := Measure.infinitePi fun _ ↦ A.seed.prod μe

instance : IsProbabilityMeasure (A.seedMeasure μe) := by
  unfold seedMeasure
  infer_instance

lemma measurable_seedPrefix (n : ℕ) : Measurable (seedPrefix (U := U) (E := E) n) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

lemma nonempty_of_isProbabilityMeasure {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] : Nonempty α := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := measure_univ (μ := μ)
  rw [Set.univ_eq_empty_iff.2 h, measure_empty] at this
  exact zero_ne_one this

/-- Extension of a seed prefix to a full seed sequence (by an arbitrary value). -/
noncomputable def seedExtend (n : ℕ) (w : Iic n → U × E) : ℕ → U × E :=
  haveI := nonempty_of_isProbabilityMeasure (A.seed.prod μe)
  fun k ↦ if h : k ∈ Iic n then w ⟨k, h⟩ else Classical.arbitrary _

lemma seedExtend_seedPrefix_of_le (n : ℕ) (ω : ℕ → U × E) {k : ℕ} (hk : k ≤ n) :
    A.seedExtend μe n (seedPrefix n ω) k = ω k := by
  simp [seedExtend, seedPrefix, mem_Iic.2 hk]

lemma measurable_seedExtend (n : ℕ) : Measurable (A.seedExtend μe n) := by
  refine measurable_pi_lambda _ fun k ↦ ?_
  unfold seedExtend
  split_ifs
  exacts [measurable_pi_apply _, measurable_const]

/-- The history of the first `n + 1` rounds as a function of the first `n + 1` seeds and
noises. -/
noncomputable def seedHist (n : ℕ) (w : Iic n → U × E) : Iic n → 𝓐 × 𝓨 :=
  fun i ↦ A.seedStep F i (A.seedExtend μe n w)

include hF in
lemma measurable_seedHist (n : ℕ) : Measurable (A.seedHist F μe n) :=
  measurable_pi_lambda _ fun i ↦ (measurable_seedStep hF i).comp (A.measurable_seedExtend μe n)

lemma seedHist_seedPrefix (n : ℕ) (ω : ℕ → U × E) :
    A.seedHist F μe n (seedPrefix n ω) = history (A.seedAction F) (A.seedFeedback F) n ω := by
  funext i
  exact seedStep_congr fun k hk ↦
    A.seedExtend_seedPrefix_of_le μe n ω (hk.trans (mem_Iic.1 i.2))

lemma hasLaw_coord (n : ℕ) :
    HasLaw (fun ω : ℕ → U × E ↦ ω n) (A.seed.prod μe) (A.seedMeasure μe) :=
  ⟨(measurable_pi_apply n).aemeasurable, Measure.infinitePi_map_eval _ n⟩

lemma hasCondDistrib_coord_succ (n : ℕ) :
    HasCondDistrib (fun ω : ℕ → U × E ↦ ω (n + 1)) (seedPrefix n)
      (Kernel.const _ (A.seed.prod μe)) (A.seedMeasure μe) := by
  refine IndepFun.hasCondDistrib_const ?_ (measurable_seedPrefix n).aemeasurable
    (A.hasLaw_coord μe (n + 1))
  have hind := iIndepFun_infinitePi (P := fun _ : ℕ ↦ A.seed.prod μe) (X := fun _ ↦ id)
    (fun _ ↦ measurable_id)
  have h := hind.indepFun_finset (Iic n) {n + 1}
    (Finset.disjoint_singleton_right.2 (by simp)) (fun i ↦ measurable_pi_apply i)
  exact h.comp measurable_id
    (measurable_pi_apply (⟨n + 1, Finset.mem_singleton_self _⟩ : ({n + 1} : Finset ℕ)))

/-- **Seed representation of a run**: the recursively defined action-feedback pairs on the
product space of seeds and noises form an algorithm-environment sequence for the seeded algorithm
and the noise environment. -/
lemma isAlgEnvSeq_seed :
    IsAlgEnvSeq (A.seedAction F) (A.seedFeedback F) A.toAlgorithm (noiseEnv μe F hF)
      (A.seedMeasure μe) where
  measurable_action n := (measurable_seedStep hF n).fst
  measurable_feedback n := (measurable_seedStep hF n).snd
  hasLaw_action_zero := by
    have h1 : HasLaw (fun ω : ℕ → U × E ↦ (ω 0).1) A.seed (A.seedMeasure μe) := by
      refine ⟨(measurable_pi_apply 0).fst.aemeasurable, ?_⟩
      change (A.seedMeasure μe).map (Prod.fst ∘ fun ω : ℕ → U × E ↦ ω 0) = A.seed
      rw [← Measure.map_map measurable_fst (measurable_pi_apply 0), (A.hasLaw_coord μe 0).map_eq]
      exact Measure.fst_prod
    have h2 := HasLaw.comp ⟨A.measurable_act0.aemeasurable, rfl⟩ h1
    refine h2.congr (ae_of_all _ fun ω ↦ ?_)
    simp [seedAction, seedStep_zero]
  hasCondDistrib_feedback_zero := by
    rw [ν0_noiseEnv]
    have h0 : HasCondDistrib (fun ω : ℕ → U × E ↦ (ω 0).2) (fun ω ↦ (ω 0).1)
        (Kernel.const _ μe) (A.seedMeasure μe) :=
      (A.hasLaw_coord μe 0).hasCondDistrib_snd_const
    have hG : Measurable (Function.uncurry fun u e ↦ F (A.act0 u) e) :=
      hF.comp (A.measurable_act0.prodMap measurable_id)
    have h1 := h0.mapOfConst hG
    rw [← Kernel.comap_mapOfConst (hG := hF) A.measurable_act0 hG] at h1
    have h2 := HasCondDistrib.comp_right h1
    have e1 : A.seedFeedback F 0 = fun ω ↦ F (A.act0 (ω 0).1) (ω 0).2 :=
      funext fun ω ↦ by simp [seedFeedback, seedStep_zero]
    have e2 : A.seedAction F 0 = A.act0 ∘ fun ω ↦ (ω 0).1 :=
      funext fun ω ↦ by simp [seedAction, seedStep_zero]
    rw [e1, e2]
    exact h2
  hasCondDistrib_action n := by
    have hc := A.hasCondDistrib_coord_succ μe n
    have hG' : Measurable (fun q : (Iic n → U × E) × (U × E) ↦ (A.seedHist F μe n q.1, q.2.1)) :=
      ((A.measurable_seedHist F μe hF n).comp measurable_fst).prodMk measurable_snd.fst
    have hG : Measurable (Function.uncurry fun (w : Iic n → U × E) (p : U × E) ↦
        A.next n (A.seedHist F μe n w) p.1) := (A.measurable_next n).comp hG'
    have h1 := hc.mapOfConst hG
    have hk : Kernel.mapOfConst (A.seed.prod μe) (fun (w : Iic n → U × E) (p : U × E) ↦
        A.next n (A.seedHist F μe n w) p.1) hG
        = (A.policy n).comap (A.seedHist F μe n) (A.measurable_seedHist F μe hF n) := by
      ext w : 1
      rw [Kernel.mapOfConst_apply hG, Kernel.comap_apply, policy_apply]
      have hnext : Measurable (A.next n (A.seedHist F μe n w)) :=
        (A.measurable_next n).comp (measurable_const.prodMk measurable_id)
      have hfst : (A.seed.prod μe).map Prod.fst = A.seed := Measure.fst_prod
      calc (A.seed.prod μe).map (fun p ↦ A.next n (A.seedHist F μe n w) p.1)
          = ((A.seed.prod μe).map Prod.fst).map (A.next n (A.seedHist F μe n w)) :=
            (Measure.map_map hnext measurable_fst).symm
        _ = A.seed.map (A.next n (A.seedHist F μe n w)) := by rw [hfst]
    rw [hk] at h1
    have h2 := HasCondDistrib.comp_right h1
    have e1 : (fun ω : ℕ → U × E ↦ A.next n (A.seedHist F μe n (seedPrefix n ω)) (ω (n + 1)).1)
        = A.seedAction F (n + 1) := by
      funext ω
      rw [A.seedHist_seedPrefix F μe n ω, seedAction, seedStep_succ]
      rfl
    have e2 : A.seedHist F μe n ∘ seedPrefix n = history (A.seedAction F) (A.seedFeedback F) n :=
      funext fun ω ↦ A.seedHist_seedPrefix F μe n ω
    rw [e1, e2] at h2
    exact h2
  hasCondDistrib_feedback n := by
    rw [feedback_noiseEnv]
    have hc : HasCondDistrib (fun ω : ℕ → U × E ↦ ((ω (n + 1)).1, (ω (n + 1)).2)) (seedPrefix n)
        (Kernel.const _ (A.seed.prod μe)) (A.seedMeasure μe) := A.hasCondDistrib_coord_succ μe n
    have h1 := hc.snd_of_const_prod
    have hx : Measurable (fun q : (Iic n → U × E) × U ↦ A.next n (A.seedHist F μe n q.1) q.2) := by
      have h' : Measurable (fun q : (Iic n → U × E) × U ↦ (A.seedHist F μe n q.1, q.2)) :=
        ((A.measurable_seedHist F μe hF n).comp measurable_fst).prodMk measurable_snd
      exact (A.measurable_next n).comp h'
    have hG' : Measurable (fun r : ((Iic n → U × E) × U) × E ↦
        (A.next n (A.seedHist F μe n r.1.1) r.1.2, r.2)) :=
      (hx.comp measurable_fst).prodMk measurable_snd
    have hG : Measurable (Function.uncurry fun (q : (Iic n → U × E) × U) (e : E) ↦
        F (A.next n (A.seedHist F μe n q.1) q.2) e) := hF.comp hG'
    have h2 := h1.mapOfConst hG
    have hf : Measurable (fun q : (Iic n → U × E) × U ↦
        (A.seedHist F μe n q.1, A.next n (A.seedHist F μe n q.1) q.2)) :=
      ((A.measurable_seedHist F μe hF n).comp measurable_fst).prodMk hx
    have hk : Kernel.mapOfConst μe (fun (q : (Iic n → U × E) × U) (e : E) ↦
        F (A.next n (A.seedHist F μe n q.1) q.2) e) hG
        = ((noiseKernel μe F hF).prodMkLeft (Iic n → 𝓐 × 𝓨)).comap _ hf := by
      ext q : 1
      rw [Kernel.mapOfConst_apply hG, Kernel.comap_apply, Kernel.prodMkLeft_apply,
        noiseKernel_apply]
    rw [hk] at h2
    have h3 := HasCondDistrib.comp_right h2
    have e1 : (fun ω : ℕ → U × E ↦
        F (A.next n (A.seedHist F μe n (seedPrefix n ω)) (ω (n + 1)).1) (ω (n + 1)).2)
        = A.seedFeedback F (n + 1) := by
      funext ω
      rw [A.seedHist_seedPrefix F μe n ω, seedFeedback, seedStep_succ]
      rfl
    have e2 : ((fun q : (Iic n → U × E) × U ↦
        (A.seedHist F μe n q.1, A.next n (A.seedHist F μe n q.1) q.2))
          ∘ fun ω ↦ (seedPrefix n ω, (ω (n + 1)).1))
        = fun ω ↦ (history (A.seedAction F) (A.seedFeedback F) n ω, A.seedAction F (n + 1) ω) := by
      funext ω
      simp only [Function.comp_apply, A.seedHist_seedPrefix F μe n ω, seedAction, seedStep_succ]
      rfl
    rw [e1, e2] at h3
    exact h3

variable {A μe F}

/-- **Seed representation of the history**: the history of the first `T` rounds of any run of the
seeded algorithm in the noise environment has the law of `seedFinHist T` under the product measure
of seeds and noises. -/
lemma _root_.Learning.IsAlgEnvSeq.map_finHistory_eq_seed {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨}
    (h : IsAlgEnvSeq X Y A.toAlgorithm (noiseEnv μe F hF) P) (T : ℕ) :
    P.map (finHistory X Y T) = (A.seedMeasure μe).map (A.seedFinHist F T) :=
  h.map_finHistory_eq (A.isAlgEnvSeq_seed F μe hF) T

/-- For a run of a fixed-budget seeded algorithm with deterministic output `g`, the probability
of an event of the output is computed on the product space of seeds and noises. -/
lemma _root_.Learning.IdentAlg.IsRun.measureReal_eq_seed {𝓞 : Type*} [MeasurableSpace 𝓞]
    [MeasurableEq 𝓞] {T : ℕ} {g : (Fin T → 𝓐 × 𝓨) → 𝓞} (hg : Measurable g)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {out : Ω → 𝓞}
    (h : (IdentAlg.fixedBudget A.toAlgorithm T (Kernel.deterministic g hg)).IsRun
      (noiseEnv μe F hF) X Y out P) {s : Set 𝓞} (hs : MeasurableSet s) :
    P.real {ω | out ω ∈ s} = (A.seedMeasure μe).real {ω | g (A.seedFinHist F T ω) ∈ s} := by
  have hae := h.output_ae_eq_of_output_eq_deterministic (IdentAlg.isFixedBudget_fixedBudget _ _ _)
    hg (IdentAlg.output_fixedBudget _ _ _)
  have hX := h.isAlgEnvSeq.measurable_action
  have hY := h.isAlgEnvSeq.measurable_feedback
  have hfin : Measurable (finHistory X Y T) := by
    unfold finHistory
    fun_prop
  calc P.real {ω | out ω ∈ s}
      = P.real {ω | g (finHistory X Y T ω) ∈ s} := by
        apply measureReal_congr
        filter_upwards [hae] with ω hω
        change (out ω ∈ s) = (g (finHistory X Y T ω) ∈ s)
        rw [hω]
    _ = (P.map (finHistory X Y T)).real (g ⁻¹' s) := by
        rw [measureReal_def, measureReal_def, Measure.map_apply hfin (hg hs)]
        rfl
    _ = ((A.seedMeasure μe).map (A.seedFinHist F T)).real (g ⁻¹' s) := by
        rw [h.isAlgEnvSeq.map_finHistory_eq_seed hF]
    _ = (A.seedMeasure μe).real {ω | g (A.seedFinHist F T ω) ∈ s} := by
        rw [measureReal_def, measureReal_def,
          Measure.map_apply (measurable_seedFinHist hF T) (hg hs)]
        rfl

/-- **PAC guarantee of a fixed-budget seeded algorithm** with deterministic output `g`, from a
bound on the product space of seeds and noises. -/
lemma isPAC_fixedBudget_deterministic {Θ : Type*} {𝓞 : Type*} [MeasurableSpace 𝓞]
    [MeasurableEq 𝓞] {T : ℕ} {g : (Fin T → 𝓐 × 𝓨) → 𝓞} (hg : Measurable g)
    {F : Θ → 𝓐 → E → 𝓨} (hF : ∀ θ, Measurable (Function.uncurry (F θ)))
    {good : Θ → 𝓞 → Prop} (hgood : ∀ θ, MeasurableSet {o | good θ o}) {δ : ℝ}
    (h : ∀ θ, 1 - δ ≤ (A.seedMeasure μe).real {ω | good θ (g (A.seedFinHist (F θ) T ω))}) :
    (IdentAlg.fixedBudget A.toAlgorithm T (Kernel.deterministic g hg)).IsPAC.{u}
      (fun θ ↦ noiseEnv μe (F θ) (hF θ)) good δ := by
  intro θ Ω _ P _ X Y out hrun
  rw [show {ω | good θ (out ω)} = {ω | out ω ∈ {o | good θ o}} from rfl,
    IdentAlg.IsRun.measureReal_eq_seed (hF θ) hg hrun (hgood θ)]
  exact h θ

/-- **PAC guarantee of a fixed-budget seeded algorithm in a linear Gaussian bandit** with
deterministic output `g`, from a bound on the product space of seeds and Gaussian noises. -/
lemma linearBandit_isPAC_fixedBudget_deterministic {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E] {𝒳 : Set E}
    (A : SeededAlg 𝒳 ℝ U) {𝓞 : Type*} [MeasurableSpace 𝓞] [MeasurableEq 𝓞] {T : ℕ}
    {g : (Fin T → 𝒳 × ℝ) → 𝓞} (hg : Measurable g) {good : E → 𝓞 → Prop}
    (hgood : ∀ θ, MeasurableSet {o | good θ o}) {δ : ℝ}
    (h : ∀ θ : E, 1 - δ ≤ (A.seedMeasure (gaussianReal 0 1)).real
      {ω | good θ (g (A.seedFinHist (fun (x : 𝒳) (e : ℝ) ↦ inner ℝ (x : E) θ + e) T ω))}) :
    (IdentAlg.fixedBudget A.toAlgorithm T (Kernel.deterministic g hg)).IsPAC.{u}
      (LinearBandit.linearGaussianEnv 𝒳) good δ := by
  have e : LinearBandit.linearGaussianEnv 𝒳 = fun θ ↦
      noiseEnv (gaussianReal 0 1) (fun (x : 𝒳) (e : ℝ) ↦ inner ℝ (x : E) θ + e) (by fun_prop) :=
    funext fun θ ↦ LinearBandit.linearGaussianEnv_eq_noiseEnv 𝒳 θ
  rw [e]
  exact A.isPAC_fixedBudget_deterministic hg (fun θ ↦ by fun_prop) hgood h

end SeededAlg

end Learning
