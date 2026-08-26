/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.LinearBandit
public import COLT83.MXJ2026.StructuredSets
public import COLT83.MXJ2026.Width
public import COLT83.MXJ2026.FixedDesignAlgorithm
public import COLT83.MXJ2026.MixedDesign
public import COLT83.MXJ2026.Rounding
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The fixed-design upper bound (Theorem 1)

For a spanning action set `𝒳`, there is a non-adaptive fixed-design `(ε, δ)`-PAC identification
algorithm with budget `T ≤ 600 (w(𝒳)² + d log(2/δ)) / ε² + 1`, where `w(𝒳) = gw 𝒳` is the Gaussian
width term of `𝒳`.

Blueprint: `thm:upper` is stated for an explicit algorithm (a rounded mixed `G`-optimal /
width-optimal design, least squares, approximate argmax); `exists_isFixedDesign_isPAC` is the
existence statement of the paper's Theorem 1, which follows from it.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Learning Learning.LinearBandit Matrix
open scoped NNReal MatrixOrder

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Theorem 1** (Maiti, Xu, Jamieson 2026): for a spanning compact action set `𝒳 ⊆ ℝ^d`,
`ε ∈ (0, 1]` and `δ ∈ (0, 1)`, there is a fixed-design (non-adaptive) identification algorithm
which is `(ε, δ)`-PAC on `𝒳` with budget `T ≤ 600 (w(𝒳)² + d log(2/δ)) / ε² + 1`. -/
theorem exists_isFixedDesign_isPAC (𝒳 : Set (EuclideanSpace ℝ ι)) (h𝒳 : IsCompact 𝒳)
    (hne : 𝒳.Nonempty) (hspan : Submodule.span ℝ 𝒳 = ⊤)
    {ε δ : ℝ} (hε : ε ∈ Set.Ioc 0 1) (hδ : δ ∈ Set.Ioo 0 1) :
    ∃ T : ℕ, (T : ℝ) ≤ 600 * (gw 𝒳 ^ 2 + Fintype.card ι * log (2 / δ)) / ε ^ 2 + 1 ∧
      ∃ A : IdentAlg 𝒳 ℝ 𝒳, A.IsFixedBudget T ∧ A.IsFixedDesign ∧ IsPAC 𝒳 A ε δ := by
  classical
  obtain ⟨R, hR⟩ : ∃ R, ∀ x ∈ 𝒳, ‖x‖ ≤ R := by
    obtain ⟨r, hr⟩ := h𝒳.isBounded.subset_closedBall (0 : EuclideanSpace ℝ ι)
    exact ⟨r, fun x hx ↦ mem_closedBall_zero_iff.1 (hr hx)⟩
  have hε0 : 0 < ε := hε.1
  have hδ0 : 0 < δ := hδ.1
  have hlog2 : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hL2 : log 2 ≤ log (2 / δ) :=
    Real.log_le_log two_pos (by rw [le_div_iff₀ hδ0]; nlinarith [hδ.2])
  have hgw0 : 0 ≤ gw 𝒳 := gw_nonneg hne hR
  have hd0 : (0 : ℝ) ≤ Fintype.card ι := by positivity
  set Q := gw 𝒳 ^ 2 + Fintype.card ι * log (2 / δ) with hQ
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ (Fintype.card ι : ℝ) * log (2 / δ) := mul_nonneg hd0 (by linarith)
    positivity
  set T := ⌈600 * Q / ε ^ 2⌉₊ with hT
  refine ⟨T, (Nat.ceil_lt_add_one (by positivity)).le, ?_⟩
  have hTQ : 600 * Q / ε ^ 2 ≤ T := Nat.le_ceil _
  obtain ⟨x₀, hx₀⟩ := hne
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- degenerate case `d = 0`: every reward vector is `0` and every recommendation is optimal
    refine ⟨fixedDesignIdentAlg T (fun _ ↦ ⟨x₀, hx₀⟩) (fun _ ↦ ⟨x₀, hx₀⟩) measurable_const,
      isFixedBudget_fixedDesignIdentAlg, isFixedDesign_fixedDesignIdentAlg, ?_⟩
    intro θ Ω _ P _ X Y out hrun
    have hθ : θ = 0 := by
      ext i
      exact isEmptyElim i
    have hreg : ∀ ω, simpleRegret 𝒳 θ (out ω) ≤ ε := fun ω ↦ by
      have : Nonempty 𝒳 := ⟨⟨x₀, hx₀⟩⟩
      simp [simpleRegret, hθ, hε0.le]
    have huniv : {ω | simpleRegret 𝒳 θ (out ω) ≤ ε} = Set.univ := Set.eq_univ_of_forall hreg
    rw [huniv, probReal_univ]
    linarith [hδ.2]
  -- main case
  have hd1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  obtain ⟨wG, hwG⟩ := exists_isGOptimalDesign h𝒳 hspan
  have hne' : Nonempty (posDefDesigns 𝒳) :=
    ⟨⟨designMatrix wG, hwG.isDesign.designMatrix_mem_designSet, hwG.posDef⟩⟩
  -- an approximate minimizer of the width
  obtain ⟨⟨A₁, hA₁mem, hA₁pd⟩, hA₁⟩ : ∃ A : posDefDesigns 𝒳,
      gwMat 𝒳 A < √(gw 𝒳 ^ 2 + log 2 / 4) := by
    refine exists_lt_of_ciInf_lt ?_
    rw [← gw_eq_iInf, Real.lt_sqrt hgw0]
    linarith
  obtain ⟨w₁, hw₁, hw₁A, -⟩ := exists_isDesign_of_mem_designSet hA₁mem
  have hw₁pd : (designMatrix w₁).PosDef := hw₁A ▸ hA₁pd
  -- the mixed design
  set w₀ := mixDesign w₁ wG with hw₀
  have hw₀d : IsDesign 𝒳 w₀ := hw₁.mixDesign hwG.isDesign
  have hA₀ : (designMatrix w₀).PosDef :=
    posDef_designMatrix_mixDesign hw₁pd hwG.posDef.posSemidef
  -- the budget is at least `4 d`
  have hT4 : 4 * Fintype.card ι ≤ T := by
    have h1 : (4 * Fintype.card ι : ℝ) ≤ 600 * Q / ε ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have hε1 : ε ^ 2 ≤ 1 := by nlinarith [hε.1, hε.2]
      have h2 : (Fintype.card ι : ℝ) * log 2 ≤ Q := by
        rw [hQ]
        linarith [mul_le_mul_of_nonneg_left hL2 hd0, sq_nonneg (gw 𝒳)]
      have h3 := mul_le_mul_of_nonneg_left hlog2.le hd0
      have h4 := mul_le_mul_of_nonneg_left hε1 hd0
      linarith
    exact_mod_cast h1.trans hTQ
  have hTpos : 0 < T := by
    have := Fintype.card_pos (α := ι)
    omega
  have hT0 : (0 : ℝ) < T := by exact_mod_cast hTpos
  -- the rounded design
  obtain ⟨xr, hxr, hround⟩ := exists_rounding hw₀d hA₀ hT4
  obtain ⟨x, hxT⟩ : ∃ x : ℕ → 𝒳, ∀ t : Fin T, (x t : EuclideanSpace ℝ ι) = xr t :=
    ⟨fun n ↦ if h : n < T then ⟨xr ⟨n, h⟩, hw₀d.mem_of_mem_support (hxr ⟨n, h⟩)⟩ else ⟨x₀, hx₀⟩,
      fun t ↦ by simp [t.2]⟩
  -- the selector
  obtain ⟨s, hs, hsel⟩ :=
    exists_measurable_approx_argmax h𝒳 ⟨x₀, hx₀⟩ (by positivity : (0 : ℝ) < ε / 4)
  refine ⟨fixedDesignIdentAlg T x s hs, isFixedBudget_fixedDesignIdentAlg,
    isFixedDesign_fixedDesignIdentAlg, ?_⟩
  set Sm := ∑ t : Fin T, outerSelf (x t : EuclideanSpace ℝ ι) with hSm
  have hSm_eq : Sm = ∑ t, outerSelf (xr t) := by simp_rw [hSm, hxT]
  have hround' : ((T : ℝ) / 4) • designMatrix w₀ ≤ Sm := hSm_eq ▸ hround
  have hSmpd : Sm.PosDef := posDef_of_smul_le hA₀ hTpos hround'
  -- the variance proxy `σ² = 8 d / T`
  obtain ⟨σ, hσ2, hσ0⟩ : ∃ σ : ℝ≥0, (σ : ℝ) ^ 2 = 8 * Fintype.card ι / T ∧ 0 < σ :=
    ⟨⟨√(8 * Fintype.card ι / T), Real.sqrt_nonneg _⟩, Real.sq_sqrt (by positivity),
      NNReal.coe_pos.1 (show (0 : ℝ) < √(8 * Fintype.card ι / T) by positivity)⟩
  have hσ : ∀ y ∈ 𝒳, WithLp.ofLp y ⬝ᵥ Sm⁻¹ *ᵥ WithLp.ofLp y ≤ σ ^ 2 := fun y hy ↦ by
    have h1 := dotProduct_inv_mulVec_le_of_smul_le hA₀ hTpos hround' (WithLp.ofLp y)
    have h2 := hwG.dotProduct_inv_designMatrix_mixDesign_le hw₁pd.posSemidef hy
    rw [hσ2]
    calc WithLp.ofLp y ⬝ᵥ Sm⁻¹ *ᵥ WithLp.ofLp y
        ≤ 4 / T * (WithLp.ofLp y ⬝ᵥ (designMatrix w₀)⁻¹ *ᵥ WithLp.ofLp y) := h1
      _ ≤ 4 / T * (2 * Fintype.card ι) := by gcongr
      _ = 8 * Fintype.card ι / T := by ring
  -- the width of the rounded design
  set g1 := gwMat 𝒳 A₁ with hg1
  have hg10 : 0 ≤ g1 := gwMat_nonneg ⟨x₀, hx₀⟩ hR _
  have hgw1 : gwMat 𝒳 Sm ≤ 2 / √T * (√2 * g1) := by
    refine (gwMat_le_of_smul_le h𝒳 ⟨x₀, hx₀⟩ hR hA₀ hTpos hround').trans ?_
    gcongr
    rw [hg1, ← hw₁A]
    exact gwMat_designMatrix_mixDesign_le h𝒳 ⟨x₀, hx₀⟩ hw₁pd hwG.posDef.posSemidef
  refine isPAC_fixedDesignIdentAlg h𝒳 ⟨x₀, hx₀⟩ hSmpd hσ0 hσ hδ hsel ?_
  -- the arithmetic of the constants
  have hg1sq : g1 ^ 2 < gw 𝒳 ^ 2 + log 2 / 4 := (Real.lt_sqrt hg10).1 hA₁
  set L := log (1 / δ) with hL
  have hL0 : 0 ≤ L := by
    rw [hL, one_div, Real.log_inv]
    linarith [Real.log_nonpos hδ0.le hδ.2.le]
  have hLle : L ≤ log (2 / δ) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_right (by norm_num) hδ0.le)
  have hcG : (gaussianConcentrationConst : ℝ) ≤ 2.5 := by
    rw [coe_gaussianConcentrationConst]
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hcG0 : 0 ≤ (gaussianConcentrationConst : ℝ) := gaussianConcentrationConst.2
  set a := 2 * gwMat 𝒳 Sm with ha
  set b := 2 * (σ : ℝ) * √(2 * gaussianConcentrationConst * L) with hb
  have ha0 : 0 ≤ a := by
    have := gwMat_nonneg ⟨x₀, hx₀⟩ hR Sm
    positivity
  have hb0 : 0 ≤ b := by positivity
  have ha2 : a ^ 2 ≤ 32 * g1 ^ 2 / T := by
    have h : a ≤ 4 * √2 * g1 / √T := by
      calc a = 2 * gwMat 𝒳 Sm := rfl
        _ ≤ 2 * (2 / √T * (√2 * g1)) := by gcongr
        _ = 4 * √2 * g1 / √T := by ring
    calc a ^ 2 ≤ (4 * √2 * g1 / √T) ^ 2 := pow_le_pow_left₀ ha0 h 2
      _ = 32 * g1 ^ 2 / T := by
          rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt two_pos.le, Real.sq_sqrt hT0.le]
          ring
  have hb2 : b ^ 2 = 64 * gaussianConcentrationConst * Fintype.card ι * L / T := by
    rw [hb, mul_pow, mul_pow, Real.sq_sqrt (by positivity), hσ2]
    ring
  have hsum : (a + b) ^ 2 ≤ (3 * ε / 4) ^ 2 := by
    have h1 : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
    have h3 : 128 * (gaussianConcentrationConst : ℝ) * Fintype.card ι * L ≤
        320 * Fintype.card ι * log (2 / δ) := by
      have := mul_le_mul hcG hLle hL0 (by norm_num)
      linarith [mul_le_mul_of_nonneg_left this hd0]
    have h4 : 16 * log 2 ≤ 17.5 * Fintype.card ι * log (2 / δ) := by
      have ha := mul_le_mul_of_nonneg_left hL2 hd0
      have hb : log 2 ≤ Fintype.card ι * log 2 := le_mul_of_one_le_left (by linarith) hd1
      have hc : 0 ≤ (Fintype.card ι : ℝ) * log (2 / δ) := mul_nonneg hd0 (by linarith)
      linarith
    have h2 : 64 * g1 ^ 2 + 128 * gaussianConcentrationConst * Fintype.card ι * L ≤
        337.5 * Q := by
      rw [hQ]
      linarith [sq_nonneg (gw 𝒳)]
    have h5 : Q / T ≤ ε ^ 2 / 600 := by
      rw [div_le_iff₀ (by positivity)] at hTQ
      rw [div_le_div_iff₀ hT0 (by norm_num)]
      linarith
    calc (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := h1
      _ ≤ 2 * (32 * g1 ^ 2 / T) +
          2 * (64 * gaussianConcentrationConst * Fintype.card ι * L / T) := by
          rw [hb2]
          gcongr
      _ = (64 * g1 ^ 2 + 128 * gaussianConcentrationConst * Fintype.card ι * L) / T := by ring
      _ ≤ 337.5 * Q / T := div_le_div_of_nonneg_right h2 hT0.le
      _ = 337.5 * (Q / T) := by ring
      _ ≤ 337.5 * (ε ^ 2 / 600) := by gcongr
      _ = (3 * ε / 4) ^ 2 := by ring
  change a + b ≤ 3 * ε / 4
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsum

end COLT83
