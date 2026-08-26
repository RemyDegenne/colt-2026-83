/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.LinearBandit
public import COLT83.Mathlib.InformationTheory.KLCompProd
public import COLT83.Mathlib.Probability.KLGaussian

/-!
# The divergence decomposition

Let `alg` be an algorithm and `κ, κ'` two reward kernels, and consider the stationary environments
`stationaryEnv κ`, `stationaryEnv κ'`. For any two algorithm-environment sequences of `alg` against
these environments (on arbitrary probability spaces), the Kullback–Leibler divergence between the
laws of the histories up to time `n` is the expected sum of the one-step divergences of the reward
kernels along the trajectory of the first sequence:

`klDiv (P.map (history X Y n)) (P'.map (history X' Y' n))
  = ∑ t ≤ n, ∫⁻ ω, klDiv (κ (X t ω)) (κ' (X t ω)) ∂P`

(`IsAlgEnvSeq.klDiv_map_history`, the *divergence decomposition* or chain rule of bandit lower
bounds). The proof is an induction on `n` using the integrated chain rule
`klDiv_compProd_eq_add_lintegral`: the policy kernels are shared by the two sequences and only
the feedback kernels differ.

For the linear Gaussian environments `linearGaussianEnv 𝒳 θ`, `linearGaussianEnv 𝒳 θ'` the one-step
divergence is `⟪x, θ - θ'⟫ ^ 2 / 2`, which gives
`klDiv (P.map (history X Y n)) (P'.map (history X' Y' n))
  = ofReal (∑ t ≤ n, ∫ ω, ⟪X t ω, θ - θ'⟫ ^ 2 / 2 ∂P)`
(`LinearBandit.klDiv_map_history`) and the bound `(n + 1) R ^ 2 ‖θ - θ'‖ ^ 2 / 2` when `𝒳`
is contained in the ball of radius `R` (`LinearBandit.klDiv_map_history_le`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal RealInnerProductSpace

namespace Learning

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {X' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}
  {alg : Algorithm 𝓐 𝓨} {κ κ' : Kernel 𝓐 𝓨} [IsMarkovKernel κ] [IsMarkovKernel κ']

/-- The law of the history up to time `n + 1` is the composition-product of the law of the history
up to time `n` with the step kernel, transported by `MeasurableEquiv.IicSuccProd`. -/
lemma IsAlgEnvSeq.map_history_succ {env : Environment 𝓐 𝓨} (h : IsAlgEnvSeq X Y alg env P) (n : ℕ) :
    P.map (history X Y (n + 1)) =
      (P.map (history X Y n) ⊗ₘ stepKernel alg env n).map
        (MeasurableEquiv.IicSuccProd (fun _ : ℕ ↦ 𝓐 × 𝓨) n).symm := by
  rw [history_succ, ← (h.hasCondDistrib_step n).map_eq, Measure.map_map (by fun_prop)]
  have hX := h.measurable_action
  have hY := h.measurable_feedback
  fun_prop

variable [MeasurableSpace.CountablyGenerated 𝓐] [MeasurableSpace.CountablyGenerated 𝓨]

/-- **Divergence decomposition.** For an algorithm `alg` run against two stationary environments
with reward kernels `κ` and `κ'`, the Kullback–Leibler divergence between the laws of the
histories up to time `n` is the expected sum, along the first trajectory, of the divergences of
the reward kernels at the played actions. -/
theorem IsAlgEnvSeq.klDiv_map_history (h : IsAlgEnvSeq X Y alg (stationaryEnv κ) P)
    (h' : IsAlgEnvSeq X' Y' alg (stationaryEnv κ') P') (n : ℕ) :
    klDiv (P.map (history X Y n)) (P'.map (history X' Y' n)) =
      ∑ t ∈ range (n + 1), ∫⁻ ω, klDiv (κ (X t ω)) (κ' (X t ω)) ∂P := by
  induction n with
  | zero =>
    rw [h.hasLaw_history_zero.map_eq, h'.hasLaw_history_zero.map_eq, klDiv_map_measurableEquiv,
      h.hasLaw_step_zero.map_eq, h'.hasLaw_step_zero.map_eq, ν0_stationaryEnv, ν0_stationaryEnv,
      klDiv_compProd_right_eq_lintegral, sum_range_one, ← h.hasLaw_action_zero.map_eq,
      lintegral_map (measurable_klDiv_kernel κ κ') (h.measurable_action 0)]
  | succ n ih =>
    rw [h.map_history_succ, h'.map_history_succ, klDiv_map_measurableEquiv, stepKernel_def,
      stepKernel_def, feedback_stationaryEnv, feedback_stationaryEnv, klDiv_compProd_eq_add, ih,
      klDiv_compProd_compProd_prodMkLeft, ← (h.hasLaw_action_comp n).map_eq,
      lintegral_map (measurable_klDiv_kernel κ κ') (h.measurable_action (n + 1)),
      sum_range_succ _ (n + 1)]

namespace LinearBandit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] [MeasurableSpace.CountablyGenerated E] {𝒳 : Set E} {θ θ' : E}
  {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → ℝ} {X' : ℕ → Ω' → 𝒳} {Y' : ℕ → Ω' → ℝ} {alg : Algorithm 𝒳 ℝ}

omit [MeasurableSpace.CountablyGenerated E] in
/-- The one-step divergence of two linear Gaussian reward kernels at the action `x` is
`⟪x, θ - θ'⟫ ^ 2 / 2`. -/
lemma klDiv_linearGaussianKernel (x : 𝒳) :
    klDiv (linearGaussianKernel 𝒳 θ x) (linearGaussianKernel 𝒳 θ' x) =
      ENNReal.ofReal (⟪(x : E), θ - θ'⟫ ^ 2 / 2) := by
  change klDiv (gaussianReal ⟪(x : E), θ⟫ 1) (gaussianReal ⟪(x : E), θ'⟫ 1) = _
  rw [klDiv_gaussianReal_one, inner_sub_right]

omit [MeasurableSpace.CountablyGenerated E] in
lemma measurable_inner_action (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P) (t : ℕ)
    (v : E) : Measurable fun ω ↦ ⟪(X t ω : E), v⟫ :=
  (continuous_id.inner continuous_const).measurable.comp
    (measurable_subtype_coe.comp (h.measurable_action t))

omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E] in
/-- `⟪x, v⟫ ^ 2 ≤ R ^ 2 ‖v‖ ^ 2` for `x ∈ 𝒳` in the ball of radius `R`. -/
lemma inner_sq_le {R : ℝ} (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) (x : 𝒳) (v : E) :
    ⟪(x : E), v⟫ ^ 2 ≤ R ^ 2 * ‖v‖ ^ 2 := by
  have h1 : |⟪(x : E), v⟫| ≤ R * ‖v‖ :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hR _ x.2) (norm_nonneg _))
  have h2 : ⟪(x : E), v⟫ ^ 2 ≤ (R * ‖v‖) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  rwa [mul_pow] at h2

/-- **Divergence decomposition for linear Gaussian environments**, under a pointwise bound
`⟪x, θ - θ'⟫ ^ 2 ≤ C` on `𝒳`. -/
theorem klDiv_map_history_of_sq_le (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P)
    (h' : IsAlgEnvSeq X' Y' alg (linearGaussianEnv 𝒳 θ') P') {C : ℝ}
    (hC : ∀ x ∈ 𝒳, ⟪x, θ - θ'⟫ ^ 2 ≤ C) (n : ℕ) :
    klDiv (P.map (history X Y n)) (P'.map (history X' Y' n)) =
      ENNReal.ofReal (∑ t ∈ range (n + 1), ∫ ω, ⟪(X t ω : E), θ - θ'⟫ ^ 2 / 2 ∂P) := by
  have h₁ : IsAlgEnvSeq X Y alg (stationaryEnv (linearGaussianKernel 𝒳 θ)) P := h
  have h₁' : IsAlgEnvSeq X' Y' alg (stationaryEnv (linearGaussianKernel 𝒳 θ')) P' := h'
  rw [h₁.klDiv_map_history h₁', ENNReal.ofReal_sum_of_nonneg
    fun t _ ↦ integral_nonneg fun ω ↦ by positivity]
  refine sum_congr rfl fun t _ ↦ ?_
  simp_rw [klDiv_linearGaussianKernel]
  refine (ofReal_integral_eq_lintegral_ofReal ?_ (Filter.Eventually.of_forall fun ω ↦ by
    positivity)).symm
  refine Integrable.of_bound ((measurable_inner_action h t (θ - θ')).pow_const 2 |>.div_const 2
    |>.aestronglyMeasurable) (C / 2) (Filter.Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  linarith [hC _ (X t ω).2]

/-- **Divergence decomposition for linear Gaussian environments.** -/
theorem klDiv_map_history (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P)
    (h' : IsAlgEnvSeq X' Y' alg (linearGaussianEnv 𝒳 θ') P') {R : ℝ} (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R)
    (n : ℕ) :
    klDiv (P.map (history X Y n)) (P'.map (history X' Y' n)) =
      ENNReal.ofReal (∑ t ∈ range (n + 1), ∫ ω, ⟪(X t ω : E), θ - θ'⟫ ^ 2 / 2 ∂P) :=
  klDiv_map_history_of_sq_le h h' (fun x hx ↦ inner_sq_le hR ⟨x, hx⟩ (θ - θ')) n

/-- The divergence between the laws of histories of length `n + 1` under two linear Gaussian
environments is at most `(n + 1) C / 2` when `⟪x, θ - θ'⟫ ^ 2 ≤ C` on `𝒳`. -/
theorem klDiv_map_history_le_of_sq_le (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P)
    (h' : IsAlgEnvSeq X' Y' alg (linearGaussianEnv 𝒳 θ') P') {C : ℝ}
    (hC : ∀ x ∈ 𝒳, ⟪x, θ - θ'⟫ ^ 2 ≤ C) (n : ℕ) :
    klDiv (P.map (history X Y n)) (P'.map (history X' Y' n)) ≤
      ENNReal.ofReal ((n + 1) * (C / 2)) := by
  rw [klDiv_map_history_of_sq_le h h' hC]
  refine ENNReal.ofReal_le_ofReal ?_
  have hbound : ∀ t ∈ range (n + 1), ∫ ω, ⟪(X t ω : E), θ - θ'⟫ ^ 2 / 2 ∂P ≤ C / 2 := by
    intro t _
    calc ∫ ω, ⟪(X t ω : E), θ - θ'⟫ ^ 2 / 2 ∂P ≤ ∫ _, C / 2 ∂P :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω ↦ by positivity)
            (integrable_const _) (Filter.Eventually.of_forall fun ω ↦ by
              linarith [hC _ (X t ω).2])
      _ = C / 2 := by simp
  calc ∑ t ∈ range (n + 1), ∫ ω, ⟪(X t ω : E), θ - θ'⟫ ^ 2 / 2 ∂P
      ≤ ∑ _ ∈ range (n + 1), C / 2 := sum_le_sum hbound
    _ = (n + 1) * (C / 2) := by simp

/-- The divergence between the laws of histories of length `n + 1` under two linear Gaussian
environments is at most `(n + 1) R ^ 2 ‖θ - θ'‖ ^ 2 / 2` when `𝒳` lies in the ball of
radius `R`. -/
theorem klDiv_map_history_le (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P)
    (h' : IsAlgEnvSeq X' Y' alg (linearGaussianEnv 𝒳 θ') P') {R : ℝ} (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R)
    (n : ℕ) :
    klDiv (P.map (history X Y n)) (P'.map (history X' Y' n)) ≤
      ENNReal.ofReal ((n + 1) * (R ^ 2 * ‖θ - θ'‖ ^ 2 / 2)) :=
  klDiv_map_history_le_of_sq_le h h' (fun x hx ↦ inner_sq_le hR ⟨x, hx⟩ (θ - θ')) n

end LinearBandit

end Learning
