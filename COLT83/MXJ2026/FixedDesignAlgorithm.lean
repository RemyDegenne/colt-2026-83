/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.FixedBudget
public import COLT83.MXJ2026.LeastSquares
public import COLT83.MXJ2026.DifferenceProcess
public import COLT83.Mathlib.MeasureTheory.ApproxArgmax

/-!
# The fixed-design identification algorithm and its guarantee

`fixedDesignIdentAlg T x s` is the identification algorithm which plays the fixed design `x`
for `T` rounds, computes the least-squares estimate `θ̂` of the reward vector and recommends
`s θ̂`, where `s` is a measurable selector (blueprint `def:fixed_design_algorithm`).

`isPAC_fixedDesignIdentAlg` is the guarantee (blueprint `thm:upper`, general form): if the design
matrix `Σ = ∑ t, x t x tᵀ` is positive definite, `xᵀ Σ⁻¹ x ≤ σ²` on `𝒳`, the selector is an
`ε/4`-approximate maximizer and `2 gwMat 𝒳 Σ + 2 σ √(2 c_G log(1/δ)) ≤ 3ε/4`, then the algorithm
is `(ε, δ)`-PAC. The proof: under any run, `θ̂ - θ ~ N(0, Σ⁻¹)`
(`hasLaw_leastSquares_of_fixedDesign`), the difference process `D(θ̂ - θ)` is at most `3ε/4`
except on an event of probability `δ` (`measureReal_diffSup_gt_le`, Borell–TIS), and on the
complement the simple regret is at most `D + ε/4 ≤ ε`
(`simpleRegret_le_supportFn_add_supportFn`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset Learning Learning.LinearBandit Matrix
open scoped RealInnerProductSpace NNReal MatrixOrder

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒳 : Set (EuclideanSpace ℝ ι)} {T : ℕ}

/-- The recommendation rule of the fixed-design algorithm: least squares on the observations of
the history, then the selector `s`. -/
noncomputable def lsRecommend (T : ℕ) (x : ℕ → 𝒳) (s : EuclideanSpace ℝ ι → 𝒳)
    (y : Fin T → 𝒳 × ℝ) : 𝒳 :=
  s (leastSquares (fun t : Fin T ↦ (x t : EuclideanSpace ℝ ι)) fun t ↦ (y t).2)

lemma measurable_lsRecommend (T : ℕ) (x : ℕ → 𝒳) {s : EuclideanSpace ℝ ι → 𝒳}
    (hs : Measurable s) : Measurable (lsRecommend T x s) :=
  hs.comp ((continuous_leastSquares _).measurable.comp
    (measurable_pi_lambda _ fun t ↦ (measurable_pi_apply t).snd))

/-- **The fixed-design identification algorithm** (blueprint `def:fixed_design_algorithm`):
play the design `x` for `T` rounds, then recommend `s θ̂` where `θ̂` is the least-squares
estimate and `s` a measurable selector. -/
noncomputable def fixedDesignIdentAlg (T : ℕ) (x : ℕ → 𝒳) (s : EuclideanSpace ℝ ι → 𝒳)
    (hs : Measurable s) : IdentAlg 𝒳 ℝ 𝒳 :=
  IdentAlg.fixedBudget (fixedDesignAlg x) T
    (Kernel.deterministic (lsRecommend T x s) (measurable_lsRecommend T x hs))

variable {x : ℕ → 𝒳} {s : EuclideanSpace ℝ ι → 𝒳} {hs : Measurable s}

lemma isFixedBudget_fixedDesignIdentAlg : (fixedDesignIdentAlg T x s hs).IsFixedBudget T :=
  IdentAlg.isFixedBudget_fixedBudget _ _ _

lemma isFixedDesign_fixedDesignIdentAlg : (fixedDesignIdentAlg T x s hs).IsFixedDesign := ⟨x, rfl⟩

lemma output_fixedDesignIdentAlg :
    (fixedDesignIdentAlg T x s hs).output T =
      Kernel.deterministic (lsRecommend T x s) (measurable_lsRecommend T x hs) :=
  IdentAlg.output_fixedBudget _ _ _

/-- **Fixed-design upper bound** (blueprint `thm:upper`, general form): the fixed-design
algorithm with design `x`, design matrix `Σ = ∑ t < T, x t x tᵀ ≻ 0`, `xᵀ Σ⁻¹ x ≤ σ²` on `𝒳`, an
`ε/4`-approximate argmax selector `s`, and `2 gwMat 𝒳 Σ + 2 σ √(2 c_G log(1/δ)) ≤ 3 ε / 4`, is
`(ε, δ)`-PAC on `𝒳`. -/
lemma isPAC_fixedDesignIdentAlg (h𝒳 : IsCompact 𝒳) (hne : 𝒳.Nonempty)
    (hS : (∑ t : Fin T, outerSelf (x t : EuclideanSpace ℝ ι)).PosDef) {σ : ℝ≥0} (hσ0 : 0 < σ)
    (hσ : ∀ y ∈ 𝒳, WithLp.ofLp y ⬝ᵥ (∑ t : Fin T, outerSelf (x t : EuclideanSpace ℝ ι))⁻¹ *ᵥ
      WithLp.ofLp y ≤ σ ^ 2)
    {ε δ : ℝ} (hδ : δ ∈ Set.Ioo 0 1)
    (hsel : ∀ v, supportFn 𝒳 v - ε / 4 ≤ ⟪(s v : EuclideanSpace ℝ ι), v⟫)
    (hbudget : 2 * gwMat 𝒳 (∑ t : Fin T, outerSelf (x t : EuclideanSpace ℝ ι)) +
      2 * σ * √(2 * gaussianConcentrationConst * log (1 / δ)) ≤ 3 * ε / 4) :
    IsPAC 𝒳 (fixedDesignIdentAlg T x s hs) ε δ := by
  intro θ Ω _ P _ X Y out hrun
  obtain ⟨R, hR⟩ : ∃ R, ∀ y ∈ 𝒳, ‖y‖ ≤ R := by
    obtain ⟨r, hr⟩ := h𝒳.isBounded.subset_closedBall (0 : EuclideanSpace ℝ ι)
    exact ⟨r, fun y hy ↦ mem_closedBall_zero_iff.1 (hr hy)⟩
  set Sm := ∑ t : Fin T, outerSelf (x t : EuclideanSpace ℝ ι) with hS'
  set xT : Fin T → EuclideanSpace ℝ ι := fun t ↦ (x t : EuclideanSpace ℝ ι) with hxT
  set θh : Ω → EuclideanSpace ℝ ι := fun ω ↦ leastSquares xT fun t ↦ Y t ω with hθh
  have hY := hrun.isAlgEnvSeq.measurable_feedback
  have hθhm : Measurable θh :=
    (continuous_leastSquares xT).measurable.comp (measurable_pi_lambda _ fun t ↦ hY t)
  -- the law of the estimation error
  have hls := hasLaw_leastSquares_of_fixedDesign hrun.isAlgEnvSeq T hS
  have hΔ : HasLaw (fun ω ↦ θh ω - θ) (multivariateGaussian 0 Sm⁻¹) P := by
    have := (⟨(measurable_id.sub_const θ).aemeasurable, rfl⟩ :
      HasLaw (fun v : EuclideanSpace ℝ ι ↦ v - θ) _ _).comp hls
    rwa [multivariateGaussian_map_sub_const] at this
  -- the output is the selector applied to the estimate
  have hout : out =ᵐ[P] fun ω ↦ s (θh ω) :=
    hrun.output_ae_eq_of_output_eq_deterministic isFixedBudget_fixedDesignIdentAlg _
      output_fixedDesignIdentAlg
  -- the bad event
  set u := 2 * σ * √(2 * gaussianConcentrationConst * log (1 / δ)) with hu
  have hbad := measureReal_diffSup_gt_le h𝒳 hne hS hσ0 hσ hδ
  have hbad_meas : MeasurableSet {ω | 2 * gwMat 𝒳 Sm + u < diffSup 𝒳 (θh ω - θ)} :=
    measurableSet_lt measurable_const
      ((continuous_diffSup hne hR).measurable.comp (hθhm.sub_const θ))
  have hbadP : P.real {ω | 2 * gwMat 𝒳 Sm + u < diffSup 𝒳 (θh ω - θ)} ≤ δ := by
    rw [hΔ.measureReal_eq (measurableSet_lt measurable_const
      (continuous_diffSup hne hR).measurable)]
    exact hbad
  -- on the complement, the regret is at most `ε`
  have hgood : ∀ᵐ ω ∂P, ω ∈ {ω | 2 * gwMat 𝒳 Sm + u < diffSup 𝒳 (θh ω - θ)}ᶜ →
      ω ∈ {ω | simpleRegret 𝒳 θ (out ω) ≤ ε} := by
    filter_upwards [hout] with ω hω hD
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hD ⊢
    rw [hω]
    have h1 := simpleRegret_le_supportFn_add_supportFn (θ := θ) hne hR (s (θh ω)).2 (hsel (θh ω))
    have h2 : supportFn 𝒳 (θ - θh ω) + supportFn 𝒳 (θh ω - θ) ≤ 3 * ε / 4 := by
      rw [diffSup, neg_sub] at hD
      linarith
    linarith
  calc 1 - δ ≤ 1 - P.real {ω | 2 * gwMat 𝒳 Sm + u < diffSup 𝒳 (θh ω - θ)} := by linarith
    _ = P.real {ω | 2 * gwMat 𝒳 Sm + u < diffSup 𝒳 (θh ω - θ)}ᶜ := by
        rw [measureReal_compl hbad_meas, probReal_univ]
    _ ≤ P.real {ω | simpleRegret 𝒳 θ (out ω) ≤ ε} :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hgood)

end COLT83
