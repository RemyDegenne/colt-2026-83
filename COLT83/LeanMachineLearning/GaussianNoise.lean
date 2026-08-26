/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.LinearBandit
public import LeanMachineLearning.SequentialLearning.Means
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Sub-Gaussian noise of linear Gaussian environments

For an algorithm-environment sequence `(X, Y)` in the linear Gaussian environment
`linearGaussianEnv 𝒳 θ`, the *noise* `η t := Y t - ⟪X t, θ⟫` has, conditionally on the history up
to time `t - 1` and the action `X t`, the law `N(0, 1)`
(`IsAlgEnvSeq.hasCondDistrib_noise`, `IsAlgEnvSeq.hasCondDistrib_noise_zero`). It is therefore
conditionally sub-Gaussian with variance proxy `1` with respect to the filtration
`filtrationAction` (`IsAlgEnvSeq.hasCondSubgaussianMGF_noise`), and Mathlib's Azuma–Hoeffding
inequality bounds the noise sums of any block of rounds:
`P (ε ≤ ∑_{s < m} η (n + s)) ≤ exp (-ε² / (2 m))` (`IsAlgEnvSeq.measureReal_sum_noise_ge_le`) and
`P (ε ≤ |∑_{s < m} η (n + s)|) ≤ 2 exp (-ε² / (2 m))`
(`IsAlgEnvSeq.measureReal_abs_sum_noise_ge_le`).

The general ingredients are stated for Mathlib: a centered real Gaussian is sub-Gaussian
(`hasSubgaussianMGF_fun_id_gaussianReal`), and a random variable whose conditional distribution
given `Z` is a constant sub-Gaussian law is conditionally sub-Gaussian given `σ(Z)`
(`HasCondDistrib.hasCondSubgaussianMGF_of_const`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset
open scoped RealInnerProductSpace NNReal

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- A centered real Gaussian with variance `v` is sub-Gaussian with variance proxy `v`. -/
lemma hasSubgaussianMGF_fun_id_gaussianReal (v : ℝ≥0) :
    HasSubgaussianMGF (fun x ↦ x) v (gaussianReal 0 v) where
  integrable_exp_mul t := integrable_exp_mul_gaussianReal t
  mgf_le t := by
    rw [mgf_fun_id_gaussianReal]
    simp

/-- If the conditional distribution of `W` given `Z` is a constant law `ν` which is sub-Gaussian
with variance proxy `c`, then `W` is conditionally sub-Gaussian given `σ(Z)` with variance
proxy `c`. -/
lemma HasCondDistrib.hasCondSubgaussianMGF_of_const [StandardBorelSpace Ω] {W : Ω → ℝ}
    {Z : Ω → 𝓧} {ν : Measure ℝ} [IsFiniteMeasure ν] (h : HasCondDistrib W Z (Kernel.const 𝓧 ν) P)
    (hW : Measurable W) (hZ : Measurable Z) {c : ℝ≥0} (hν : HasSubgaussianMGF (fun x ↦ x) c ν) :
    HasCondSubgaussianMGF (m𝓧.comap Z) hZ.comap_le W c P := by
  have hW : HasLaw W ν P := h.hasLaw_of_const
  have hint : ∀ t : ℝ, Integrable (fun ω ↦ exp (t * W ω)) P := fun t ↦ by
    have := hν.integrable_exp_mul t
    rw [← hW.map_eq] at this
    exact (integrable_map_measure (by fun_prop) hW.aemeasurable).1 this
  refine Kernel.HasSubgaussianMGF.of_rat (fun t ↦ ?_) fun q ↦ ?_
  · rw [condExpKernel_comp_trim]
    exact hint t
  · have hm : m𝓧.comap Z ≤ mΩ := hZ.comap_le
    have h1 := condExp_ae_eq_trim_integral_condExpKernel_of_stronglyMeasurable hm
      (f := fun ω ↦ exp ((q : ℝ) * W ω)) (by fun_prop) (hint q)
    have h2 : P[fun ω ↦ exp ((q : ℝ) * W ω) | m𝓧.comap Z] =ᵐ[P] fun _ ↦ mgf (fun x ↦ x) ν q := by
      have := h.condExp_comp_eq hZ (g := fun x ↦ exp ((q : ℝ) * x)) (by fun_prop) (hint q)
      filter_upwards [this] with ω hω
      rw [hω, Kernel.const_apply]
      rfl
    have h2' : P[fun ω ↦ exp ((q : ℝ) * W ω) | m𝓧.comap Z] =ᵐ[P.trim hm]
        fun _ ↦ mgf (fun x ↦ x) ν q :=
      (StronglyMeasurable.ae_eq_trim_iff hm stronglyMeasurable_condExp
        stronglyMeasurable_const).2 h2
    filter_upwards [h1, h2'] with ω hω1 hω2
    change ∫ y, exp ((q : ℝ) * W y) ∂condExpKernel P (m𝓧.comap Z) ω ≤ _
    rw [← hω1, hω2]
    exact hν.mgf_le q

end ProbabilityTheory

namespace Learning.LinearBandit

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {𝒳 : Set E} {θ : E} {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → ℝ} {alg : Algorithm 𝒳 ℝ}

/-- The noise at time `t` of a sequence of actions and feedbacks in the linear Gaussian environment
with reward vector `θ`: `Y t - ⟪X t, θ⟫`. -/
noncomputable def noise (θ : E) (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Y t ω - ⟪(X t ω : E), θ⟫

/-- If `W` given `Z` has the law `N(⟪a Z, θ⟫, 1)`, then `W - ⟪a Z, θ⟫` given `Z` has the law
`N(0, 1)`. -/
lemma hasCondDistrib_sub_inner_of_hasCondDistrib {𝓧 : Type*} {m𝓧 : MeasurableSpace 𝓧}
    {Z : Ω → 𝓧} {a : 𝓧 → 𝒳} (ha : Measurable a) {W : Ω → ℝ}
    (h : HasCondDistrib W Z ((linearGaussianKernel 𝒳 θ).comap a ha) P) :
    HasCondDistrib (fun ω ↦ W ω - ⟪(a (Z ω) : E), θ⟫) Z (Kernel.const 𝓧 (gaussianReal 0 1)) P := by
  have hZ : AEMeasurable Z P := h.aemeasurable_fst
  have hW : AEMeasurable W P := h.aemeasurable_snd
  have hinner : Measurable fun z : 𝓧 ↦ ⟪(a z : E), θ⟫ :=
    (continuous_id.inner continuous_const).measurable.comp (measurable_subtype_coe.comp ha)
  let F : 𝓧 × ℝ → 𝓧 × ℝ := fun p ↦ (p.1, p.2 - ⟪(a p.1 : E), θ⟫)
  have hF : Measurable F := measurable_fst.prodMk (measurable_snd.sub (hinner.comp measurable_fst))
  refine ⟨by fun_prop, ?_⟩
  have h1 : P.map (fun ω ↦ (Z ω, W ω - ⟪(a (Z ω) : E), θ⟫)) =
      (P.map (fun ω ↦ (Z ω, W ω))).map F := by
    rw [AEMeasurable.map_map_of_aemeasurable hF.aemeasurable (hZ.prodMk hW)]
    rfl
  rw [h1, h.map_eq]
  ext s hs
  rw [Measure.map_apply hF hs, Measure.compProd_apply (hF hs), Measure.compProd_apply hs]
  refine lintegral_congr fun z ↦ ?_
  have h2 : Prod.mk z ⁻¹' (F ⁻¹' s) = (fun y ↦ y - ⟪(a z : E), θ⟫) ⁻¹' (Prod.mk z ⁻¹' s) := by
    ext y
    simp [F]
  rw [h2, Kernel.comap_apply, Kernel.const_apply, ← Measure.map_apply (by fun_prop)
    (measurable_prodMk_left hs)]
  change (gaussianReal ⟪(a z : E), θ⟫ 1).map (fun y ↦ y - ⟪(a z : E), θ⟫) _ = _
  rw [gaussianReal_map_sub_const, sub_self]

variable (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P)
include h

/-- Conditionally on the history up to time `n` and the action at time `n + 1`, the noise at time
`n + 1` has the law `N(0, 1)`. -/
lemma _root_.Learning.IsAlgEnvSeq.hasCondDistrib_noise (n : ℕ) :
    HasCondDistrib (noise θ X Y (n + 1)) (fun ω ↦ (history X Y n ω, X (n + 1) ω))
      (Kernel.const _ (gaussianReal 0 1)) P :=
  hasCondDistrib_sub_inner_of_hasCondDistrib measurable_snd (h.hasCondDistrib_feedback n)

/-- Conditionally on the first action, the noise at time `0` has the law `N(0, 1)`. -/
lemma _root_.Learning.IsAlgEnvSeq.hasCondDistrib_noise_zero :
    HasCondDistrib (noise θ X Y 0) (X 0) (Kernel.const _ (gaussianReal 0 1)) P :=
  hasCondDistrib_sub_inner_of_hasCondDistrib measurable_id h.hasCondDistrib_feedback_zero

lemma _root_.Learning.IsAlgEnvSeq.measurable_noise (t : ℕ) : Measurable (noise θ X Y t) :=
  (h.measurable_feedback t).sub
    ((continuous_id.inner continuous_const).measurable.comp
      (measurable_subtype_coe.comp (h.measurable_action t)))

/-- The noise at time `t` has the law `N(0, 1)`. -/
lemma _root_.Learning.IsAlgEnvSeq.hasLaw_noise (t : ℕ) :
    HasLaw (noise θ X Y t) (gaussianReal 0 1) P := by
  cases t with
  | zero => exact h.hasCondDistrib_noise_zero.hasLaw_of_const
  | succ n => exact (h.hasCondDistrib_noise n).hasLaw_of_const

/-- The noise at time `t` is sub-Gaussian with variance proxy `1`. -/
lemma _root_.Learning.IsAlgEnvSeq.hasSubgaussianMGF_noise (t : ℕ) :
    HasSubgaussianMGF (noise θ X Y t) 1 P := by
  rw [← HasSubgaussianMGF.id_map_iff (h.hasLaw_noise t).aemeasurable, (h.hasLaw_noise t).map_eq]
  exact hasSubgaussianMGF_fun_id_gaussianReal 1

variable [StandardBorelSpace Ω]

/-- The noise at time `n + 1` is conditionally sub-Gaussian with variance proxy `1` given the
history up to time `n` and the action at time `n + 1`. -/
lemma _root_.Learning.IsAlgEnvSeq.hasCondSubgaussianMGF_noise (n : ℕ) :
    HasCondSubgaussianMGF (h.filtrationAction (n + 1)) (h.filtrationAction.le (n + 1))
      (noise θ X Y (n + 1)) 1 P := by
  have hZ : Measurable fun ω ↦ (history X Y n ω, X (n + 1) ω) :=
    (h.measurable_history n).prodMk (h.measurable_action (n + 1))
  have key := (h.hasCondDistrib_noise n).hasCondSubgaussianMGF_of_const (h.measurable_noise (n + 1))
    hZ (hasSubgaussianMGF_fun_id_gaussianReal 1)
  have heq : h.filtrationAction (n + 1) =
      MeasurableSpace.comap (fun ω ↦ (history X Y n ω, X (n + 1) ω)) inferInstance :=
    h.filtrationAction_eq_comap (n + 1) n.succ_ne_zero
  have hgen : ∀ (m : MeasurableSpace Ω) (hm : m ≤ mΩ),
      m = MeasurableSpace.comap (fun ω ↦ (history X Y n ω, X (n + 1) ω)) inferInstance →
      HasCondSubgaussianMGF m hm (noise θ X Y (n + 1)) 1 P := by
    rintro m hm rfl
    exact key
  exact hgen _ _ heq

/-- The shifted filtration `s ↦ filtrationAction (n + s + 1)`. -/
noncomputable def _root_.Learning.IsAlgEnvSeq.shiftedFiltrationAction (n : ℕ) :
    Filtration ℕ mΩ where
  seq s := h.filtrationAction (n + s + 1)
  mono' s t hst := h.filtrationAction.mono (by omega)
  le' s := h.filtrationAction.le _

omit [StandardBorelSpace Ω] in
/-- The shifted noise process `s ↦ noise (n + s)` is adapted to the shifted filtration. -/
lemma _root_.Learning.IsAlgEnvSeq.stronglyAdapted_noise_shifted (n : ℕ) :
    StronglyAdapted (h.shiftedFiltrationAction n) fun s ↦ noise θ X Y (n + s) := by
  intro s
  have hinner : Measurable fun x : 𝒳 ↦ ⟪(x : E), θ⟫ :=
    (continuous_id.inner continuous_const).measurable.comp measurable_subtype_coe
  have hm : Measurable[h.filtration (n + s)] (noise θ X Y (n + s)) :=
    (h.adapted_feedback (n + s)).sub (hinner.comp (h.adapted_action (n + s)))
  exact (hm.mono (h.filtration_le_filtrationAction_succ (n + s)) le_rfl).stronglyMeasurable

/-- The shifted noise process is conditionally sub-Gaussian for the shifted filtration. -/
lemma _root_.Learning.IsAlgEnvSeq.hasCondSubgaussianMGF_noise_shifted (n i : ℕ) :
    HasCondSubgaussianMGF (h.shiftedFiltrationAction n i) ((h.shiftedFiltrationAction n).le i)
      (noise θ X Y (n + (i + 1))) 1 P :=
  h.hasCondSubgaussianMGF_noise (n + i)

/-- **Azuma–Hoeffding for the noise**: the sum of the noises of the rounds `n, …, n + m - 1`
exceeds `ε ≥ 0` with probability at most `exp (-ε² / (2 m))`. -/
lemma _root_.Learning.IsAlgEnvSeq.measureReal_sum_noise_ge_le (n m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ ∑ s ∈ range m, noise θ X Y (n + s) ω} ≤ exp (-ε ^ 2 / (2 * m)) := by
  have := measure_sum_ge_le_of_hasCondSubgaussianMGF (cY := fun _ ↦ 1)
    (h.stronglyAdapted_noise_shifted n) (by simpa using h.hasSubgaussianMGF_noise n) m
    (fun i _ ↦ h.hasCondSubgaussianMGF_noise_shifted n i) hε
  simpa using this

/-- **Azuma–Hoeffding for the noise**, lower tail: the sum of the noises of the rounds
`n, …, n + m - 1` is at most `-ε` with probability at most `exp (-ε² / (2 m))`. -/
lemma _root_.Learning.IsAlgEnvSeq.measureReal_sum_noise_le_le (n m : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ∑ s ∈ range m, noise θ X Y (n + s) ω ≤ -ε} ≤ exp (-ε ^ 2 / (2 * m)) := by
  have hadapted : StronglyAdapted (h.shiftedFiltrationAction n) fun s ↦ -noise θ X Y (n + s) :=
    fun s ↦ (h.stronglyAdapted_noise_shifted n s).neg
  have h0 : HasSubgaussianMGF (-noise θ X Y (n + 0)) 1 P := (h.hasSubgaussianMGF_noise (n + 0)).neg
  have hsub : ∀ i < m - 1, HasCondSubgaussianMGF (h.shiftedFiltrationAction n i)
      ((h.shiftedFiltrationAction n).le i) (-noise θ X Y (n + (i + 1))) 1 P := fun i _ ↦
    Kernel.HasSubgaussianMGF.neg (h.hasCondSubgaussianMGF_noise_shifted n i)
  have := measure_sum_ge_le_of_hasCondSubgaussianMGF (cY := fun _ ↦ 1) hadapted h0 m hsub hε
  simp only [Pi.neg_apply, Finset.sum_neg_distrib, le_neg, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] at this
  simpa using this

/-- **Azuma–Hoeffding for the noise, two-sided**: the absolute value of the sum of the noises of
the rounds `n, …, n + m - 1` exceeds `ε ≥ 0` with probability at most `2 exp (-ε² / (2 m))`. -/
lemma _root_.Learning.IsAlgEnvSeq.measureReal_abs_sum_noise_ge_le (n m : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ |∑ s ∈ range m, noise θ X Y (n + s) ω|} ≤ 2 * exp (-ε ^ 2 / (2 * m)) := by
  have h1 := h.measureReal_sum_noise_ge_le n m hε
  have h2 := h.measureReal_sum_noise_le_le n m hε
  calc P.real {ω | ε ≤ |∑ s ∈ range m, noise θ X Y (n + s) ω|}
      ≤ P.real ({ω | ε ≤ ∑ s ∈ range m, noise θ X Y (n + s) ω} ∪
          {ω | ∑ s ∈ range m, noise θ X Y (n + s) ω ≤ -ε}) := by
        refine measureReal_mono fun ω hω ↦ ?_
        rcases le_abs'.1 (show ε ≤ |∑ s ∈ range m, noise θ X Y (n + s) ω| from hω) with h | h
        · exact Or.inr h
        · exact Or.inl h
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ 2 * exp (-ε ^ 2 / (2 * m)) := by linarith

end Learning.LinearBandit
