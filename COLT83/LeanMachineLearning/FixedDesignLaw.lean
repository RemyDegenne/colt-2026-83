/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.FixedDesignRun
public import COLT83.LeanMachineLearning.FixedBudget
public import COLT83.LeanMachineLearning.Run

/-!
# The law of a fixed-design, fixed-budget run

For a fixed-budget identification algorithm `A` (budget `T`) with the fixed design `x` in the
linear Gaussian environment with reward vector `θ`, the pair (history of the `T` rounds, output)
has the explicit law
`fixedDesignPairLaw A x θ = (N(0,1)^T).map (η ↦ (x t, ⟪x t, θ⟫ + η t)_t) ⊗ₘ A.output T`
(`IsRun.hasLaw_finHistory_out_of_fixedDesign`, blueprint `lem:fixed_design_law` and
`def:bayes_prior`). Consequently the PAC property of `A` is a statement about this law
(`IsPAC.le_measureReal_fixedDesignPairLaw`), which is what the Bayesian lower bound of
Theorem 3 uses.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Learning
open scoped RealInnerProductSpace

universe u

namespace Learning.LinearBandit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  {𝒳 : Set E} {θ : E} {T : ℕ}

/-- The history of the `T` rounds of the fixed design `x` with reward vector `θ` and noise
vector `η`: round `t` plays `x t` and observes `⟪x t, θ⟫ + η t`. -/
def fixedDesignHist (x : Fin T → 𝒳) (θ : E) (η : Fin T → ℝ) : Fin T → 𝒳 × ℝ :=
  fun t ↦ (x t, ⟪(x t : E), θ⟫ + η t)

lemma measurable_fixedDesignHist (x : Fin T → 𝒳) (θ : E) : Measurable (fixedDesignHist x θ) :=
  measurable_pi_lambda _ fun t ↦
    measurable_const.prodMk (measurable_const.add (measurable_pi_apply t))

/-- The law of the history of the `T` rounds of the fixed design `x` with reward vector `θ`:
the image of the standard Gaussian noise `N(0,1)^T` by `fixedDesignHist x θ`. -/
noncomputable def fixedDesignHistLaw (x : Fin T → 𝒳) (θ : E) : Measure (Fin T → 𝒳 × ℝ) :=
  (Measure.pi fun _ : Fin T ↦ gaussianReal 0 1).map (fixedDesignHist x θ)

instance (x : Fin T → 𝒳) (θ : E) : IsProbabilityMeasure (fixedDesignHistLaw x θ) :=
  Measure.isProbabilityMeasure_map (measurable_fixedDesignHist x θ).aemeasurable

/-- The joint law of (history of the `T` rounds, output) of the fixed-budget algorithm `A` with
the fixed design `x` in the linear Gaussian environment with reward vector `θ`. -/
noncomputable def fixedDesignPairLaw (A : IdentAlg 𝒳 ℝ 𝒳) (x : Fin T → 𝒳) (θ : E) :
    Measure ((Fin T → 𝒳 × ℝ) × 𝒳) :=
  fixedDesignHistLaw x θ ⊗ₘ A.output T

instance (A : IdentAlg 𝒳 ℝ 𝒳) (x : Fin T → 𝒳) (θ : E) [IsMarkovKernel (A.output T)] :
    IsProbabilityMeasure (fixedDesignPairLaw A x θ) := by
  unfold fixedDesignPairLaw
  infer_instance

/-- Two reward vectors with the same means `⟪x t, θ⟫` on the design give the same pair law. -/
lemma fixedDesignPairLaw_congr (A : IdentAlg 𝒳 ℝ 𝒳) (x : Fin T → 𝒳) {θ θ' : E}
    (h : ∀ t, ⟪(x t : E), θ⟫ = ⟪(x t : E), θ'⟫) :
    fixedDesignPairLaw A x θ = fixedDesignPairLaw A x θ' := by
  have : fixedDesignHist x θ = fixedDesignHist x θ' := by
    funext η t
    simp [fixedDesignHist, h t]
  simp [fixedDesignPairLaw, fixedDesignHistLaw, this]

section run

variable [OpensMeasurableSpace E] [MeasurableEq 𝒳] {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → ℝ} {out : Ω → 𝒳}
  {A : IdentAlg 𝒳 ℝ 𝒳} {x : ℕ → 𝒳}

/-- Under a fixed-design run, the history of the first `T` rounds has law
`fixedDesignHistLaw`. -/
lemma _root_.Learning.IsAlgEnvSeq.hasLaw_finHistory_of_fixedDesign
    (h : IsAlgEnvSeq X Y (fixedDesignAlg x) (linearGaussianEnv 𝒳 θ) P) (T : ℕ) :
    HasLaw (finHistory X Y T) (fixedDesignHistLaw (fun t : Fin T ↦ x t) θ) P := by
  have hY := h.hasLaw_feedback_finVec_of_fixedDesign T
  have hm : Measurable fun y : Fin T → ℝ ↦ fun t : Fin T ↦ (x t, y t) :=
    measurable_pi_lambda _ fun t ↦ measurable_const.prodMk (measurable_pi_apply t)
  have h1 : HasLaw (fun ω ↦ fun t : Fin T ↦ (x t, Y t ω))
      (fixedDesignHistLaw (fun t : Fin T ↦ x t) θ) P := by
    have := (⟨hm.aemeasurable, rfl⟩ : HasLaw (fun y : Fin T → ℝ ↦ fun t : Fin T ↦ (x t, y t)) _ _)
      |>.comp hY
    have hμ : ((Measure.pi fun _ : Fin T ↦ gaussianReal 0 1).map
        (fun η (i : Fin T) ↦ ⟪(x i : E), θ⟫ + η i)).map
          (fun y : Fin T → ℝ ↦ fun t : Fin T ↦ (x t, y t)) =
        fixedDesignHistLaw (fun t : Fin T ↦ x t) θ := by
      rw [fixedDesignHistLaw, Measure.map_map hm (by fun_prop)]
      rfl
    rwa [hμ] at this
  refine h1.congr ?_
  filter_upwards [h.ae_action_eq_of_fixedDesign] with ω hω
  funext t
  simp [finHistory, hω t]

/-- **Law of a fixed-design run** (blueprint `lem:fixed_design_law`, `def:bayes_prior`): the
pair (history of the `T` rounds, output) of a run of the fixed-budget algorithm `A` (budget `T`)
with the fixed design `x` in the linear Gaussian environment with reward vector `θ` has law
`fixedDesignPairLaw A x θ`. -/
lemma _root_.Learning.IdentAlg.IsRun.hasLaw_finHistory_out_of_fixedDesign
    (hA : A.IsFixedBudget T) (h : A.IsRun (linearGaussianEnv 𝒳 θ) X Y out P)
    (hdes : A.alg = fixedDesignAlg x) :
    HasLaw (fun ω ↦ (finHistory X Y T ω, out ω)) (fixedDesignPairLaw A (fun t : Fin T ↦ x t) θ)
      P := by
  have hseq : IsAlgEnvSeq X Y (fixedDesignAlg x) (linearGaussianEnv 𝒳 θ) P := by
    have := h.isAlgEnvSeq
    rwa [hdes] at this
  exact (hseq.hasLaw_finHistory_of_fixedDesign T).prodMk_of_hasCondDistrib
    (h.hasCondDistrib_output_finHistory hA)

end run

section pac

variable {A : IdentAlg 𝒳 ℝ 𝒳} {x : ℕ → 𝒳}

/-- **The PAC property of a fixed-design algorithm, on its explicit law**: for every reward
vector `θ`, the recommendation has simple regret at most `ε` with probability at least `1 - δ`
under `fixedDesignPairLaw A x θ`. -/
lemma _root_.Learning.LinearBandit.IsPAC.le_measureReal_fixedDesignPairLaw
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
    [OpensMeasurableSpace E] [SecondCountableTopology E] {𝒳 : Set E} {A : IdentAlg 𝒳 ℝ 𝒳}
    {x : ℕ → 𝒳} {ε δ : ℝ} (hpac : IsPAC 𝒳 A ε δ) (hA : A.IsFixedBudget T)
    (hdes : A.alg = fixedDesignAlg x) (θ : E) :
    1 - δ ≤ (fixedDesignPairLaw A (fun t : Fin T ↦ x t) θ).real
      {p | simpleRegret 𝒳 θ p.2 ≤ ε} := by
  have := hA.isMarkovKernel_output
  have hrun := hA.isRun_fixedBudgetRunMeasure (env := linearGaussianEnv 𝒳 θ)
  have hlaw := hrun.hasLaw_finHistory_out_of_fixedDesign hA hdes
  have hpac' := hpac θ (A.fixedBudgetRunMeasure (linearGaussianEnv 𝒳 θ) T) _ _ _ hrun
  have hmeas : MeasurableSet {p : (Fin T → 𝒳 × ℝ) × 𝒳 | simpleRegret 𝒳 θ p.2 ≤ ε} := by
    refine measurableSet_le ?_ measurable_const
    exact (continuous_const.sub ((continuous_subtype_val.comp continuous_snd).inner
      continuous_const)).measurable
  rw [← hlaw.map_eq, Measure.real, Measure.map_apply_of_aemeasurable hlaw.aemeasurable hmeas]
  exact hpac'

end pac

end Learning.LinearBandit
