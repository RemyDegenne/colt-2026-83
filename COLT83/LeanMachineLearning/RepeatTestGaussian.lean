/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.RepeatTest
public import COLT83.LeanMachineLearning.GaussianNoise
public import COLT83.Mathlib.Analysis.InnerProductSpace.SupportFn

/-!
# The repeated-action test in a linear Gaussian bandit

Under the algorithm `alg.thenRepeat n ρ` (play `alg` for `n + 1` rounds, then repeat an action
drawn from `ρ`) in the linear Gaussian environment with reward vector `θ`, the empirical mean
`phaseMean Y n m` of the observations of the rounds `n + 1, …, n + m` is `⟪X (n + 1), θ⟫` plus
the mean of the Gaussian noise of these rounds (`phaseMean_ae_eq_of_thenRepeat`), and the
Azuma–Hoeffding bound for the noise (`IsAlgEnvSeq.measureReal_abs_sum_noise_ge_le`) gives
`P (phaseMean ≥ ⟪X (n + 1), θ⟫ + ε) ≤ 2 exp (-m ε² / 2)` and the symmetric bound.

For the test algorithm `IdentAlg.testAlg A n` built from an `(ε, δ)`-PAC identification
algorithm `A` with budget `n + 1`, the decision `phaseMean > ε` is wrong with probability at most
`2 exp (-m ε² / 8)` when `θ = 0`, and at most `δ + 2 exp (-m ε² / 8)` when some action has value
`⟪v, θ⟫ ≥ 3 ε` (blueprint `lem:test_from_alg`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset Learning
open scoped RealInnerProductSpace

universe u

namespace Learning.LinearBandit

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {𝒳 : Set E} {θ : E} {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → ℝ} {n m : ℕ}

/-- The empirical mean of the `m` observations of the rounds `n + 1, …, n + m`. -/
noncomputable def phaseMean (Y : ℕ → Ω → ℝ) (n m : ℕ) (ω : Ω) : ℝ :=
  (∑ s ∈ range m, Y (n + 1 + s) ω) / m

omit [IsProbabilityMeasure P] in
@[fun_prop]
lemma measurable_phaseMean (hY : ∀ t, Measurable (Y t)) : Measurable (phaseMean Y n m) :=
  (Finset.measurable_sum _ fun _ _ ↦ hY _).div_const _

variable {alg : Algorithm 𝒳 ℝ} {ρ : Kernel (Fin (n + 1) → 𝒳 × ℝ) 𝒳} [IsMarkovKernel ρ]

/-- Under `alg.thenRepeat n ρ` in the linear Gaussian environment with reward vector `θ`, the
empirical mean of the observations of the rounds `n + 1, …, n + m` is `⟪X (n + 1), θ⟫` plus the
mean of the noise of these rounds. -/
lemma phaseMean_ae_eq_of_thenRepeat [MeasurableEq 𝒳] (hm : 0 < m)
    (h : IsAlgEnvSeq X Y (alg.thenRepeat n ρ) (linearGaussianEnv 𝒳 θ) P) :
    phaseMean Y n m =ᵐ[P] fun ω ↦
      ⟪(X (n + 1) ω : E), θ⟫ + (∑ s ∈ range m, noise θ X Y (n + 1 + s) ω) / m := by
  filter_upwards [h.ae_forall_action_add_eq_of_thenRepeat] with ω hω
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have : ∑ s ∈ range m, Y (n + 1 + s) ω =
      ∑ s ∈ range m, (⟪(X (n + 1) ω : E), θ⟫ + noise θ X Y (n + 1 + s) ω) := by
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    simp only [noise, hω]
    ring
  rw [phaseMean, this, Finset.sum_add_distrib, Finset.sum_const, card_range, nsmul_eq_mul,
    add_div, mul_div_cancel_left₀ _ hm']

variable [StandardBorelSpace Ω]

/-- Azuma–Hoeffding for the mean of the noise of the rounds `n + 1, …, n + m`. -/
lemma measureReal_abs_sum_noise_div_ge_le (h : IsAlgEnvSeq X Y alg (linearGaussianEnv 𝒳 θ) P)
    (hm : 0 < m) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | ε ≤ |(∑ s ∈ range m, noise θ X Y (n + 1 + s) ω) / m|} ≤
      2 * exp (-(m * ε ^ 2 / 2)) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hset : {ω | ε ≤ |(∑ s ∈ range m, noise θ X Y (n + 1 + s) ω) / m|} =
      {ω | m * ε ≤ |∑ s ∈ range m, noise θ X Y (n + 1 + s) ω|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, abs_div, abs_of_pos hm', le_div_iff₀ hm', mul_comm ε]
  have hexp : -(m * ε ^ 2 / 2) = -(m * ε) ^ 2 / (2 * m) := by
    field_simp
  rw [hset, hexp]
  exact h.measureReal_abs_sum_noise_ge_le (n + 1) m (mul_nonneg hm'.le hε)

/-- Under `alg.thenRepeat n ρ`, the empirical mean of the observations of the rounds
`n + 1, …, n + m` exceeds `⟪X (n + 1), θ⟫ + ε` with probability at most `2 exp (-m ε² / 2)`. -/
lemma measureReal_inner_add_le_phaseMean_le [MeasurableEq 𝒳]
    (h : IsAlgEnvSeq X Y (alg.thenRepeat n ρ) (linearGaussianEnv 𝒳 θ) P) (hm : 0 < m) {ε : ℝ}
    (hε : 0 ≤ ε) :
    P.real {ω | ⟪(X (n + 1) ω : E), θ⟫ + ε ≤ phaseMean Y n m ω} ≤ 2 * exp (-(m * ε ^ 2 / 2)) := by
  refine le_trans ?_ (measureReal_abs_sum_noise_div_ge_le (n := n) h hm hε)
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  change ∀ᵐ ω ∂P, ω ∈ {ω | ⟪(X (n + 1) ω : E), θ⟫ + ε ≤ phaseMean Y n m ω} →
    ω ∈ {ω | ε ≤ |(∑ s ∈ range m, noise θ X Y (n + 1 + s) ω) / m|}
  filter_upwards [phaseMean_ae_eq_of_thenRepeat hm h] with ω hω hmem
  have hmem' : ⟪(X (n + 1) ω : E), θ⟫ + ε ≤ phaseMean Y n m ω := hmem
  rw [hω] at hmem'
  exact le_abs.2 (Or.inl (by linarith))

/-- Under `alg.thenRepeat n ρ`, the empirical mean of the observations of the rounds
`n + 1, …, n + m` is below `⟪X (n + 1), θ⟫ - ε` with probability at most `2 exp (-m ε² / 2)`. -/
lemma measureReal_phaseMean_le_inner_sub_le [MeasurableEq 𝒳]
    (h : IsAlgEnvSeq X Y (alg.thenRepeat n ρ) (linearGaussianEnv 𝒳 θ) P) (hm : 0 < m) {ε : ℝ}
    (hε : 0 ≤ ε) :
    P.real {ω | phaseMean Y n m ω ≤ ⟪(X (n + 1) ω : E), θ⟫ - ε} ≤ 2 * exp (-(m * ε ^ 2 / 2)) := by
  refine le_trans ?_ (measureReal_abs_sum_noise_div_ge_le (n := n) h hm hε)
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
  change ∀ᵐ ω ∂P, ω ∈ {ω | phaseMean Y n m ω ≤ ⟪(X (n + 1) ω : E), θ⟫ - ε} →
    ω ∈ {ω | ε ≤ |(∑ s ∈ range m, noise θ X Y (n + 1 + s) ω) / m|}
  filter_upwards [phaseMean_ae_eq_of_thenRepeat hm h] with ω hω hmem
  have hmem' : phaseMean Y n m ω ≤ ⟪(X (n + 1) ω : E), θ⟫ - ε := hmem
  rw [hω] at hmem'
  exact le_abs.2 (Or.inr (by linarith))

section testAlg

variable [MeasurableEq 𝒳] {A : IdentAlg 𝒳 ℝ 𝒳} [IsMarkovKernel (A.output (n + 1))]

/-- **The test decides `θ ≠ 0` wrongly with small probability.** Under `θ = 0`, the empirical mean
of the observations of the second phase of the test algorithm exceeds `ε` with probability at
most `2 exp (-m ε² / 8)`. -/
lemma measureReal_lt_phaseMean_le_of_testAlg
    (h : IsAlgEnvSeq X Y (A.testAlg n) (linearGaussianEnv 𝒳 0) P) (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε) :
    P.real {ω | ε < phaseMean Y n m ω} ≤ 2 * exp (-(m * ε ^ 2 / 8)) := by
  have h1 := measureReal_inner_add_le_phaseMean_le (θ := 0) h hm (ε := ε / 2) (by positivity)
  simp only [inner_zero_right, zero_add] at h1
  refine le_trans (measureReal_mono fun ω hω ↦ ?_) (h1.trans_eq ?_)
  · have hω' : ε < phaseMean Y n m ω := hω
    exact (by linarith : ε / 2 ≤ phaseMean Y n m ω)
  · congr 2
    ring

/-- **The test detects a good action with small probability of failure.** If `A` is
`(ε, δ)`-PAC, the actions are bounded and some action `v` has value `⟪v, θ⟫ ≥ 3 ε`, then the
empirical mean of the observations of the second phase of the test algorithm is at most `ε`
with probability at most `δ + 2 exp (-m ε² / 8)`. -/
lemma measureReal_phaseMean_le_le_of_testAlg {R : ℝ} (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) {ε δ : ℝ}
    (hε : 0 < ε) (hpac : IsPAC 𝒳 A ε δ) (hA : A.IsFixedBudget (n + 1)) {v : E} (hv : v ∈ 𝒳)
    (hθ : 3 * ε ≤ ⟪v, θ⟫) (h : IsAlgEnvSeq X Y (A.testAlg n) (linearGaussianEnv 𝒳 θ) P)
    (hm : 0 < m) :
    P.real {ω | phaseMean Y n m ω ≤ ε} ≤ δ + 2 * exp (-(m * ε ^ 2 / 8)) := by
  have hgood : MeasurableSet {x : 𝒳 | simpleRegret 𝒳 θ x ≤ ε} := by
    have : Continuous fun x : 𝒳 ↦ simpleRegret 𝒳 θ x :=
      continuous_const.sub (continuous_subtype_val.inner continuous_const)
    exact measurableSet_le this.measurable measurable_const
  have hp := hpac.le_measureReal_action_succ_of_testAlg hA θ h hgood
  have hmeas : MeasurableSet {ω | simpleRegret 𝒳 θ (X (n + 1) ω) ≤ ε} :=
    h.measurable_action (n + 1) hgood
  have h2 := measureReal_phaseMean_le_inner_sub_le h hm (ε := ε / 2) (by positivity)
  have hsub : {ω | phaseMean Y n m ω ≤ ε} ⊆
      {ω | simpleRegret 𝒳 θ (X (n + 1) ω) ≤ ε}ᶜ ∪
        {ω | phaseMean Y n m ω ≤ ⟪(X (n + 1) ω : E), θ⟫ - ε / 2} := by
    intro ω hω
    by_cases hg : simpleRegret 𝒳 θ (X (n + 1) ω) ≤ ε
    · right
      have h1 : ⟪v, θ⟫ ≤ ⨆ y : 𝒳, ⟪(y : E), θ⟫ := inner_le_supportFn hR hv θ
      simp only [simpleRegret] at hg
      simp only [Set.mem_ofPred_eq] at hω ⊢
      linarith
    · exact Or.inl hg
  calc P.real {ω | phaseMean Y n m ω ≤ ε}
      ≤ P.real ({ω | simpleRegret 𝒳 θ (X (n + 1) ω) ≤ ε}ᶜ ∪
          {ω | phaseMean Y n m ω ≤ ⟪(X (n + 1) ω : E), θ⟫ - ε / 2}) := measureReal_mono hsub
    _ ≤ P.real {ω | simpleRegret 𝒳 θ (X (n + 1) ω) ≤ ε}ᶜ +
          P.real {ω | phaseMean Y n m ω ≤ ⟪(X (n + 1) ω : E), θ⟫ - ε / 2} :=
        measureReal_union_le _ _
    _ ≤ δ + 2 * exp (-(m * (ε / 2) ^ 2 / 2)) := by
        gcongr
        rw [measureReal_compl hmeas, probReal_univ]
        linarith
    _ = δ + 2 * exp (-(m * ε ^ 2 / 8)) := by
        congr 3
        ring

end testAlg

end Learning.LinearBandit
