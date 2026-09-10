/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.DivergenceDecomposition
public import Maiti2026Power.LeanMachineLearning.LinearBandit
public import Maiti2026Power.LeanMachineLearning.StoppedHistory
public import Maiti2026Power.Mathlib.Probability.KLGaussian

/-!
# The divergence decomposition at a stopping time

LML's `LeanMachineLearning.SequentialLearning.DivergenceDecomposition` proves the chain rule and
the divergence decomposition for the history of a *fixed* number of rounds
(`IsAlgEnvSeq.klDiv_map_history_stepKernel`, `IsAlgEnvSeq.klDiv_map_history_compProd`,
`IsAlgEnvSeq.klDiv_map_history`) and for the whole trajectory
(`IsAlgEnvSeq.klDiv_map_trajectory_stepKernel`, `IsAlgEnvSeq.klDiv_map_trajectory_compProd`,
`IsAlgEnvSeq.klDiv_map_trajectory`). This file proves the corresponding statements for the
history stopped at a stopping time, and specializes the decomposition to linear Gaussian
environments.

Let `alg` be an algorithm and `env, env'` two environments, and consider two algorithm-environment
sequences of `alg` against these environments, on arbitrary probability spaces. For a stopping
rule `S` with stopping time `τ = stoppingTime X Y S` (the number of rounds played), the divergence
between the laws of the histories stopped at `min τ M` is the sum over the rounds `t < M` of the
conditional divergences of the step at round `t`, on the event `{t < τ}`
(`IsAlgEnvSeq.klDiv_map_stoppedHist_min_stepKernel`, a chain rule: the policy kernels are shared
and only the feedback kernels differ), and when `τ` is almost surely finite under both laws, the
divergence between the laws of the stopped histories is the series of these terms
(`IsAlgEnvSeq.klDiv_map_stoppedHist_stepKernel`).

For two stationary environments with reward kernels `κ, κ'`, the conditional divergence of a
step is the conditional divergence of the reward given the played action. This is the
*divergence decomposition* of bandit lower bounds, in composition-product form
(`klDiv_map_stoppedHist_min_compProd`, `klDiv_map_stoppedHist_compProd`, on arbitrary measurable
spaces) and in integral form (`klDiv_map_stoppedHist_min`, `klDiv_map_stoppedHist`, when `𝓨` is
countably generated), the latter reading
`klDiv (P.map (stoppedHist X Y τ)) (P'.map (stoppedHist X' Y' τ'))
  = ∫⁻ ω, ∑ t < τ ω, klDiv (κ (X t ω)) (κ' (X t ω)) ∂P`
for an almost surely finite stopping time.

The bounded stopping-time version is proved by induction on `M`: the law of the history stopped
at `min τ (M + 1)` splits according to whether `τ ≤ M` (`map_stoppedHist_min_succ_eq_add`), the
divergence is additive over disjoint supports (`klDiv_add_add_of_measure_eq_zero`) and the chain
rule `klDiv_compProd_eq_add` handles the step at round `M`. The almost surely finite version
follows by monotone convergence (`klDiv_eq_iSup_restrict`) and the data-processing inequality,
since the history stopped at `min τ M` is the truncation of the stopped history. The integral
forms follow from the composition-product forms by LML's integrated chain rule
`klDiv_compProd_right_eq_lintegral`; the same passage turns LML's one-step composition-product
identity `klDiv_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd` into its integral form
`klDiv_compProd_compProd_prodMkLeft`.

For the linear Gaussian environments `linearGaussianEnv 𝒳 θ`, `linearGaussianEnv 𝒳 θ'` the one-step
divergence is `⟪x, θ - θ'⟫ ^ 2 / 2`, which gives
`klDiv (P.map (history X Y n)) (P'.map (history X' Y' n))
  = ofReal (∑ t < n, ∫ ω, ⟪X t ω, θ - θ'⟫ ^ 2 / 2 ∂P)`
(`LinearBandit.klDiv_map_history`) and the bound `n R ^ 2 ‖θ - θ'‖ ^ 2 / 2` when `𝒳`
is contained in the ball of radius `R` (`LinearBandit.klDiv_map_history_le`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Finset
open scoped ENNReal RealInnerProductSpace ENat

namespace Learning

variable {𝓐 𝓨 : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {X' : ℕ → Ω' → 𝓐} {Y' : ℕ → Ω' → 𝓨}
  {alg : Algorithm 𝓐 𝓨} {env env' : Environment 𝓐 𝓨} {κ κ' : Kernel 𝓐 𝓨} [IsMarkovKernel κ]
  [IsMarkovKernel κ'] {S : Set (Σ n : ℕ, (Fin n → 𝓐 × 𝓨))}

section OneStep

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} [MeasurableSpace.CountableOrCountablyGenerated β γ]

/-- The divergence of one step of a policy/reward decomposition, in integral form: the policy
`π` is shared and the reward kernels `κ`, `η` (which ignore the history) differ, so the
divergence is the expected divergence of the reward kernels at the played action, whose law is
`π ∘ₘ μ`. -/
lemma klDiv_compProd_compProd_prodMkLeft (μ : Measure α) [IsFiniteMeasure μ] (π : Kernel α β)
    [IsMarkovKernel π] (κ η : Kernel β γ) [IsFiniteKernel κ] [IsFiniteKernel η] :
    klDiv (μ ⊗ₘ (π ⊗ₖ Kernel.prodMkLeft α κ)) (μ ⊗ₘ (π ⊗ₖ Kernel.prodMkLeft α η)) =
      ∫⁻ b, klDiv (κ b) (η b) ∂(π ∘ₘ μ) := by
  rw [klDiv_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd,
    klDiv_compProd_right_eq_lintegral]

end OneStep

/-! ### Histories stopped at a bounded stopping time -/

/-- **Chain rule for histories stopped at a bounded stopping time.** For an algorithm `alg` run
against two environments `env`, `env'`, and a stopping rule `S` with stopping time `τ`, the
divergence between the laws of the histories stopped at `min τ M` is the sum over the rounds
`t < M` of the conditional divergences, on the event `{t < τ}`, of the step at round `t` given
the first `t` rounds (composition-product form). -/
lemma IsAlgEnvSeq.klDiv_map_stoppedHist_min_stepKernel (h : IsAlgEnvSeq X Y alg env P)
    (h' : IsAlgEnvSeq X' Y' alg env' P') (hS : MeasurableSet S) (M : ℕ) :
    klDiv (P.map (stoppedHist X Y fun ω ↦ min (stoppingTime X Y S ω) M))
        (P'.map (stoppedHist X' Y' fun ω ↦ min (stoppingTime X' Y' S ω) M)) =
      ∑ t ∈ range M,
        klDiv ((P.restrict {ω | (t : ℕ∞) < stoppingTime X Y S ω}).map (history X Y t) ⊗ₘ
            stepKernel alg env t)
          ((P.restrict {ω | (t : ℕ∞) < stoppingTime X Y S ω}).map (history X Y t) ⊗ₘ
            stepKernel alg env' t) := by
  have hX := h.measurable_action
  have hY := h.measurable_feedback
  have hX' := h'.measurable_action
  have hY' := h'.measurable_feedback
  induction M with
  | zero => rw [map_stoppedHist_min_zero, map_stoppedHist_min_zero, klDiv_self, sum_range_zero]
  | succ M ih =>
    have hB : MeasurableSet {h : Σ n : ℕ, (Fin n → 𝓐 × 𝓨) | h.1 ≤ M} := measurableSet_fst_le M
    rw [sum_range_succ, ← ih, map_stoppedHist_min_succ_eq_add hX hY hS (P := P) M,
      map_stoppedHist_min_succ_eq_add hX' hY' hS (P := P') M,
      map_stoppedHist_min_eq_add hX hY hS (P := P) M,
      map_stoppedHist_min_eq_add hX' hY' hS (P := P') M,
      klDiv_add_add_of_measure_eq_zero hB
        (map_restrict_stoppedHist_min_apply_compl_fst_le hX hY hS _ M)
        (map_restrict_stoppedHist_min_apply_compl_fst_le hX' hY' hS _ M)
        (map_sigmaMk_succ_apply_fst_le _) (map_sigmaMk_succ_apply_fst_le _),
      klDiv_add_add_of_measure_eq_zero hS
        (map_restrict_stoppingTime_le_stoppedHist_min_apply_compl hX hY hS M)
        (map_restrict_stoppingTime_le_stoppedHist_min_apply_compl hX' hY' hS M)
        (map_restrict_lt_stoppingTime_map_sigmaMk_apply hX hY hS M)
        (map_restrict_lt_stoppingTime_map_sigmaMk_apply hX' hY' hS M),
      klDiv_map_measurableEmbedding _ _ (measurableEmbedding_sigma_mk (M + 1)),
      klDiv_map_measurableEmbedding _ _ (measurableEmbedding_sigma_mk M),
      h.map_history_succ_restrict_lt_stoppingTime hS M,
      h'.map_history_succ_restrict_lt_stoppingTime hS M, klDiv_map_measurableEquiv, add_assoc]
    congr 1
    exact klDiv_compProd_eq_add _ _ _ _

/-- **Divergence decomposition for histories stopped at a bounded stopping time**,
composition-product form. For an algorithm `alg` run against two stationary environments with
reward kernels `κ` and `κ'`, and a stopping rule `S` with stopping time `τ`, the divergence
between the laws of the histories stopped at `min τ M` is the sum over the rounds `t < M` of the
conditional divergences of the reward kernels given the played action, on the event `{t < τ}`. -/
lemma IsAlgEnvSeq.klDiv_map_stoppedHist_min_compProd (h : IsAlgEnvSeq X Y alg (stationaryEnv κ) P)
    (h' : IsAlgEnvSeq X' Y' alg (stationaryEnv κ') P') (hS : MeasurableSet S) (M : ℕ) :
    klDiv (P.map (stoppedHist X Y fun ω ↦ min (stoppingTime X Y S ω) M))
        (P'.map (stoppedHist X' Y' fun ω ↦ min (stoppingTime X' Y' S ω) M)) =
      ∑ t ∈ range M,
        klDiv ((P.restrict {ω | (t : ℕ∞) < stoppingTime X Y S ω}).map (X t) ⊗ₘ κ)
          ((P.restrict {ω | (t : ℕ∞) < stoppingTime X Y S ω}).map (X t) ⊗ₘ κ') := by
  rw [h.klDiv_map_stoppedHist_min_stepKernel h' hS M]
  refine sum_congr rfl fun t _ ↦ ?_
  rw [stepKernel_stationaryEnv, stepKernel_stationaryEnv,
    klDiv_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd,
    ← h.map_action_restrict_lt_stoppingTime hS t]

omit m𝓐 m𝓨 in
/-- A sum over `t < M` of terms which vanish unless `t < τ` is a sum over `t < min τ M`. -/
lemma sum_ite_lt_eq_sum_range_toNat_min {β : Type*} [AddCommMonoid β] (f : ℕ → β) (τ : ℕ∞)
    (M : ℕ) :
    ∑ t ∈ range M, (if (t : ℕ∞) < τ then f t else 0) = ∑ t ∈ range (min τ M).toNat, f t := by
  induction τ using ENat.recTopCoe with
  | top => simp
  | coe k =>
    rw [← sum_filter]
    congr 1
    ext t
    simp only [mem_filter, mem_range, ENat.natCast_lt_natCast]
    rcases le_total k M with hkM | hkM
    · rw [min_eq_left (by exact_mod_cast hkM), ENat.toNat_natCast]
      omega
    · rw [min_eq_right (by exact_mod_cast hkM), ENat.toNat_natCast]
      omega

/-- **Divergence decomposition for histories stopped at a bounded stopping time**, integral
form: the divergence between the laws of the histories stopped at `min τ M` is the expected sum,
along the first trajectory, of the divergences of the reward kernels at the actions played before
`min τ M`. -/
lemma IsAlgEnvSeq.klDiv_map_stoppedHist_min [MeasurableSpace.CountablyGenerated 𝓨]
    (h : IsAlgEnvSeq X Y alg (stationaryEnv κ) P) (h' : IsAlgEnvSeq X' Y' alg (stationaryEnv κ') P')
    (hS : MeasurableSet S) (M : ℕ) :
    klDiv (P.map (stoppedHist X Y fun ω ↦ min (stoppingTime X Y S ω) M))
        (P'.map (stoppedHist X' Y' fun ω ↦ min (stoppingTime X' Y' S ω) M)) =
      ∫⁻ ω, ∑ t ∈ range (min (stoppingTime X Y S ω) M).toNat,
        klDiv (κ (X t ω)) (κ' (X t ω)) ∂P := by
  have hX := h.measurable_action
  have hmeas : ∀ t, Measurable fun ω ↦ klDiv (κ (X t ω)) (κ' (X t ω)) := fun t ↦
    (measurable_klDiv_kernel κ κ').comp (hX t)
  have hlt : ∀ t : ℕ, MeasurableSet {ω | (t : ℕ∞) < stoppingTime X Y S ω} :=
    measurableSet_lt_stoppingTime hX h.measurable_feedback hS
  rw [h.klDiv_map_stoppedHist_min_compProd h' hS M]
  simp_rw [klDiv_compProd_right_eq_lintegral, lintegral_map (measurable_klDiv_kernel κ κ') (hX _),
    ← lintegral_indicator (hlt _)]
  rw [← lintegral_finsetSum _ fun t _ ↦ (hmeas t).indicator (hlt t)]
  refine lintegral_congr fun ω ↦ ?_
  simp_rw [Set.indicator_apply, Set.mem_ofPred_eq]
  exact sum_ite_lt_eq_sum_range_toNat_min _ _ M

/-! ### Histories stopped at an almost surely finite stopping time -/

/-- **Chain rule for histories stopped at an almost surely finite stopping time.** For an
algorithm `alg` run against two environments `env`, `env'`, and a stopping rule `S` whose stopping
time is almost surely finite under both laws, the divergence between the laws of the stopped
histories is the series over the rounds `t` of the conditional divergences, on the event
`{t < τ}`, of the step at round `t` given the first `t` rounds (composition-product form). -/
lemma IsAlgEnvSeq.klDiv_map_stoppedHist_stepKernel (h : IsAlgEnvSeq X Y alg env P)
    (h' : IsAlgEnvSeq X' Y' alg env' P') (hS : MeasurableSet S)
    (hτ : ∀ᵐ ω ∂P, stoppingTime X Y S ω ≠ ⊤) (hτ' : ∀ᵐ ω ∂P', stoppingTime X' Y' S ω ≠ ⊤) :
    klDiv (P.map (stoppedHist X Y (stoppingTime X Y S)))
        (P'.map (stoppedHist X' Y' (stoppingTime X' Y' S))) =
      ∑' t : ℕ,
        klDiv ((P.restrict {ω | (t : ℕ∞) < stoppingTime X Y S ω}).map (history X Y t) ⊗ₘ
            stepKernel alg env t)
          ((P.restrict {ω | (t : ℕ∞) < stoppingTime X Y S ω}).map (history X Y t) ⊗ₘ
            stepKernel alg env' t) := by
  have hX := h.measurable_action
  have hY := h.measurable_feedback
  have hX' := h'.measurable_action
  have hY' := h'.measurable_feedback
  have hτm := measurable_stoppingTime hX hY hS
  have hτm' := measurable_stoppingTime hX' hY' hS
  have hB : ∀ M, MeasurableSet {h : Σ n : ℕ, (Fin n → 𝓐 × 𝓨) | h.1 < M} :=
    measurableSet_fst_lt
  rw [ENNReal.tsum_eq_iSup_nat]
  simp_rw [← h.klDiv_map_stoppedHist_min_stepKernel h' hS,
    map_stoppedHist_min_eq_map_truncHist hX hY hτm hτ,
    map_stoppedHist_min_eq_map_truncHist hX' hY' hτm' hτ']
  set μ := P.map (stoppedHist X Y (stoppingTime X Y S)) with hμ
  set ν := P'.map (stoppedHist X' Y' (stoppingTime X' Y' S)) with hν
  refine le_antisymm ?_ (iSup_le fun M ↦ klDiv_map_le _ _ (measurable_truncHist M))
  rw [klDiv_eq_iSup_restrict hB (fun M N hMN h hh ↦ lt_of_lt_of_le hh hMN) (by
    ext h
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨h.1 + 1, h.1.lt_succ_self⟩)]
  refine iSup_mono fun M ↦ ?_
  calc klDiv (μ.restrict {h | h.1 < M}) (ν.restrict {h | h.1 < M})
      = klDiv ((μ.map (truncHist M)).restrict {h | h.1 < M})
          ((ν.map (truncHist M)).restrict {h | h.1 < M}) := by
        rw [restrict_map_truncHist, restrict_map_truncHist]
    _ ≤ klDiv (μ.map (truncHist M)) (ν.map (truncHist M)) := klDiv_restrict_le (hB M)

/-- **Divergence decomposition for histories stopped at an almost surely finite stopping time**,
composition-product form. For an algorithm `alg` run against two stationary environments with
reward kernels `κ` and `κ'`, and a stopping rule `S` whose stopping time is almost surely finite
under both laws, the divergence between the laws of the stopped histories is the series over the
rounds `t` of the conditional divergences of the reward kernels given the played action, on the
event `{t < τ}`. -/
lemma IsAlgEnvSeq.klDiv_map_stoppedHist_compProd (h : IsAlgEnvSeq X Y alg (stationaryEnv κ) P)
    (h' : IsAlgEnvSeq X' Y' alg (stationaryEnv κ') P') (hS : MeasurableSet S)
    (hτ : ∀ᵐ ω ∂P, stoppingTime X Y S ω ≠ ⊤) (hτ' : ∀ᵐ ω ∂P', stoppingTime X' Y' S ω ≠ ⊤) :
    klDiv (P.map (stoppedHist X Y (stoppingTime X Y S)))
        (P'.map (stoppedHist X' Y' (stoppingTime X' Y' S))) =
      ∑' t : ℕ, klDiv ((P.restrict {ω | (t : ℕ∞) < stoppingTime X Y S ω}).map (X t) ⊗ₘ κ)
        ((P.restrict {ω | (t : ℕ∞) < stoppingTime X Y S ω}).map (X t) ⊗ₘ κ') := by
  rw [h.klDiv_map_stoppedHist_stepKernel h' hS hτ hτ']
  refine tsum_congr fun t ↦ ?_
  rw [stepKernel_stationaryEnv, stepKernel_stationaryEnv,
    klDiv_compProd_compProd_prodMkLeft_eq_klDiv_comp_compProd,
    ← h.map_action_restrict_lt_stoppingTime hS t]

/-- **Divergence decomposition for histories stopped at an almost surely finite stopping time**,
integral form: the divergence between the laws of the stopped histories is the expected sum,
along the first trajectory, of the divergences of the reward kernels at the actions played before
stopping. -/
lemma IsAlgEnvSeq.klDiv_map_stoppedHist [MeasurableSpace.CountablyGenerated 𝓨]
    (h : IsAlgEnvSeq X Y alg (stationaryEnv κ) P) (h' : IsAlgEnvSeq X' Y' alg (stationaryEnv κ') P')
    (hS : MeasurableSet S) (hτ : ∀ᵐ ω ∂P, stoppingTime X Y S ω ≠ ⊤)
    (hτ' : ∀ᵐ ω ∂P', stoppingTime X' Y' S ω ≠ ⊤) :
    klDiv (P.map (stoppedHist X Y (stoppingTime X Y S)))
        (P'.map (stoppedHist X' Y' (stoppingTime X' Y' S))) =
      ∫⁻ ω, ∑ t ∈ range (stoppingTime X Y S ω).toNat, klDiv (κ (X t ω)) (κ' (X t ω)) ∂P := by
  have hX := h.measurable_action
  have hmeas : ∀ t, Measurable fun ω ↦ klDiv (κ (X t ω)) (κ' (X t ω)) := fun t ↦
    (measurable_klDiv_kernel κ κ').comp (hX t)
  have hlt : ∀ t : ℕ, MeasurableSet {ω | (t : ℕ∞) < stoppingTime X Y S ω} :=
    measurableSet_lt_stoppingTime hX h.measurable_feedback hS
  rw [h.klDiv_map_stoppedHist_compProd h' hS hτ hτ']
  simp_rw [klDiv_compProd_right_eq_lintegral, lintegral_map (measurable_klDiv_kernel κ κ') (hX _),
    ← lintegral_indicator (hlt _)]
  rw [← lintegral_tsum fun t ↦ ((hmeas t).indicator (hlt t)).aemeasurable]
  refine lintegral_congr_ae ?_
  filter_upwards [hτ] with ω hω
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hω
  simp_rw [Set.indicator_apply, Set.mem_ofPred_eq, ← hk, ENat.natCast_lt_natCast,
    ENat.toNat_natCast]
  rw [tsum_eq_sum (s := range k) fun t ht ↦ ite_eq_right (by simpa using ht)]
  exact sum_congr rfl fun t ht ↦ ite_eq_left (mem_range.1 ht)

namespace LinearBandit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {𝒳 : Set E} {θ θ' : E}
  {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → ℝ} {X' : ℕ → Ω' → 𝒳} {Y' : ℕ → Ω' → ℝ} {alg : Algorithm 𝒳 ℝ}

/-- The one-step divergence of two linear Gaussian reward kernels at the action `x` is
`⟪x, θ - θ'⟫ ^ 2 / 2`. -/
lemma klDiv_linearGaussianKernel (x : 𝒳) :
    klDiv (linearGaussianKernel 𝒳 θ x) (linearGaussianKernel 𝒳 θ' x) =
      ENNReal.ofReal (⟪(x : E), θ - θ'⟫ ^ 2 / 2) := by
  change klDiv (gaussianReal ⟪(x : E), θ⟫ 1) (gaussianReal ⟪(x : E), θ'⟫ 1) = _
  rw [klDiv_gaussianReal_one, inner_sub_right]

lemma measurable_inner_action (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P) (t : ℕ)
    (v : E) : Measurable fun ω ↦ ⟪(X t ω : E), v⟫ :=
  (continuous_id.inner continuous_const).measurable.comp
    (measurable_subtype_coe.comp (h.measurable_action t))

omit [MeasurableSpace E] in
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
lemma klDiv_map_history_of_sq_le (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P)
    (h' : IsAlgEnvSeq X' Y' alg (linearGaussianEnv 𝒳 θ') P') {C : ℝ}
    (hC : ∀ x ∈ 𝒳, ⟪x, θ - θ'⟫ ^ 2 ≤ C) (n : ℕ) :
    klDiv (P.map (history X Y n)) (P'.map (history X' Y' n)) =
      ENNReal.ofReal (∑ t ∈ range n, ∫ ω, ⟪(X t ω : E), θ - θ'⟫ ^ 2 / 2 ∂P) := by
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
lemma klDiv_map_history (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P)
    (h' : IsAlgEnvSeq X' Y' alg (linearGaussianEnv 𝒳 θ') P') {R : ℝ} (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R)
    (n : ℕ) :
    klDiv (P.map (history X Y n)) (P'.map (history X' Y' n)) =
      ENNReal.ofReal (∑ t ∈ range n, ∫ ω, ⟪(X t ω : E), θ - θ'⟫ ^ 2 / 2 ∂P) :=
  klDiv_map_history_of_sq_le h h' (fun x hx ↦ inner_sq_le hR ⟨x, hx⟩ (θ - θ')) n

/-- The divergence between the laws of the histories of the first `n` rounds under two linear
Gaussian environments is at most `n C / 2` when `⟪x, θ - θ'⟫ ^ 2 ≤ C` on `𝒳`. -/
lemma klDiv_map_history_le_of_sq_le (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P)
    (h' : IsAlgEnvSeq X' Y' alg (linearGaussianEnv 𝒳 θ') P') {C : ℝ}
    (hC : ∀ x ∈ 𝒳, ⟪x, θ - θ'⟫ ^ 2 ≤ C) (n : ℕ) :
    klDiv (P.map (history X Y n)) (P'.map (history X' Y' n)) ≤
      ENNReal.ofReal (n * (C / 2)) := by
  rw [klDiv_map_history_of_sq_le h h' hC]
  refine ENNReal.ofReal_le_ofReal ?_
  have hbound : ∀ t ∈ range n, ∫ ω, ⟪(X t ω : E), θ - θ'⟫ ^ 2 / 2 ∂P ≤ C / 2 := by
    intro t _
    calc ∫ ω, ⟪(X t ω : E), θ - θ'⟫ ^ 2 / 2 ∂P ≤ ∫ _, C / 2 ∂P :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω ↦ by positivity)
            (integrable_const _) (Filter.Eventually.of_forall fun ω ↦ by
              linarith [hC _ (X t ω).2])
      _ = C / 2 := by simp
  calc ∑ t ∈ range n, ∫ ω, ⟪(X t ω : E), θ - θ'⟫ ^ 2 / 2 ∂P
      ≤ ∑ _ ∈ range n, C / 2 := sum_le_sum hbound
    _ = n * (C / 2) := by simp

/-- The divergence between the laws of the histories of the first `n` rounds under two linear
Gaussian environments is at most `n R ^ 2 ‖θ - θ'‖ ^ 2 / 2` when `𝒳` lies in the ball of
radius `R`. -/
lemma klDiv_map_history_le (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P)
    (h' : IsAlgEnvSeq X' Y' alg (linearGaussianEnv 𝒳 θ') P') {R : ℝ} (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R)
    (n : ℕ) :
    klDiv (P.map (history X Y n)) (P'.map (history X' Y' n)) ≤
      ENNReal.ofReal (n * (R ^ 2 * ‖θ - θ'‖ ^ 2 / 2)) :=
  klDiv_map_history_le_of_sq_le h h' (fun x hx ↦ inner_sq_le hR ⟨x, hx⟩ (θ - θ')) n

end LinearBandit

end Learning
