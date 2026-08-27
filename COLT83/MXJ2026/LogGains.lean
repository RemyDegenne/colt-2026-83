/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.LinearBandit
public import COLT83.MXJ2026.LowerCube
public import COLT83.MXJ2026.LowerMSet
public import COLT83.MXJ2026.LowerMultitask
public import COLT83.MXJ2026.StructuredSets
public import COLT83.MXJ2026.Width
public import COLT83.MXJ2026.RegionAlgorithm
public import COLT83.MXJ2026.LogGainsArith
public import COLT83.MXJ2026.FixedDesignAlgorithm
public import COLT83.MXJ2026.Rounding
public import COLT83.Mathlib.Data.Set.CoverSmall
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Structured sets on which adaptivity gives at most logarithmic gains (Theorem 6, Table 1)

* `exists_isPAC_of_finite` (**Theorem 6**): on every finite spanning action set `𝒳 ⊆ ℝ^d` there
  is an adaptive `(ε, δ)`-PAC algorithm with budget `O(d log((|𝒳|/d)₊ / δ) / ε²)`.
* Adaptive lower bounds of Table 1, for every (possibly adaptive) `(ε, δ)`-PAC identification
  algorithm with `δ` below an absolute constant:
  `T > (∑ⱼ √dⱼ)² / (20000 ε²)` on the multi-task set, `T > d² / (100 ε²)` on `{-1, 1}^d`,
  `T > d² / (400 ε²)` on `{0, 1}^d`, `T > m (d - m + 1) / (2500 ε²)` on the `m`-sets, and
  `T ≥ d² / (1000 ε²)` on the unit ball.

Blueprint: `thm:log_gains` (stated there for an explicit region-based algorithm built on Median
Elimination, of which `exists_isPAC_of_finite` is the existence form, with
`C_reg = 1281 + 6 C_ME = 97281`), `thm:lower_multitask`, `thm:lower_hypercube_pm`,
`thm:lower_hypercube_01`, `thm:lower_msets`, `cor:lower_ball_adaptive`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Learning Learning.LinearBandit Learning.MedianElim Matrix
open scoped RealInnerProductSpace NNReal MatrixOrder

namespace COLT83

variable {ι : Type*} [Fintype ι]

/-- **Theorem 6** (Maiti, Xu, Jamieson 2026): for every finite spanning action set `𝒳 ⊆ ℝ^d`,
`ε ∈ (0, 1]` and `δ ∈ (0, 1)`, there is an (adaptive) `(ε, δ)`-PAC identification algorithm on
`𝒳` with budget `T ≤ C d (log((|𝒳|/d)₊) + log(4/δ)) / ε²`, `C = 97281`, where
`(u)₊ = max 1 u`. -/
theorem exists_isPAC_of_finite (𝒳 : Set (EuclideanSpace ℝ ι)) (hfin : 𝒳.Finite)
    (hne : 𝒳.Nonempty) (hspan : Submodule.span ℝ 𝒳 = ⊤)
    {ε δ : ℝ} (hε : ε ∈ Set.Ioc 0 1) (hδ : δ ∈ Set.Ioo 0 1) :
    ∃ T : ℕ, (T : ℝ) ≤ 97281 * Fintype.card ι *
        (log (max 1 ((𝒳.ncard : ℝ) / Fintype.card ι)) + log (4 / δ)) / ε ^ 2 ∧
      ∃ A : IdentAlg 𝒳 ℝ 𝒳, A.IsFixedBudget T ∧ IsPAC 𝒳 A ε δ := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  have hε0 : 0 < ε := hε.1
  have hδ0 : 0 < δ := hδ.1
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- degenerate case `d = 0`: every reward vector is `0` and every recommendation is optimal
    refine ⟨0, by simp, fixedDesignIdentAlg 0 (fun _ ↦ ⟨x₀, hx₀⟩) (fun _ ↦ ⟨x₀, hx₀⟩)
      measurable_const, isFixedBudget_fixedDesignIdentAlg, ?_⟩
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
  have hd1 : 0 < Fintype.card ι := Fintype.card_pos
  have hd0 : (0 : ℝ) ≤ Fintype.card ι := by positivity
  -- a spanning set has at least `d` elements
  have hdm : Fintype.card ι ≤ 𝒳.ncard := by
    have := hfin.fintype
    have h1 := finrank_span_le_card (R := ℝ) 𝒳
    rw [hspan, finrank_top, finrank_euclideanSpace] at h1
    rwa [Set.ncard_eq_toFinset_card' 𝒳]
  -- the regions
  obtain ⟨R, hRsub, hRne, hRcard, hcover⟩ := Set.exists_cover_ncard_le hfin hd1 hdm
  have hRfin : ∀ i, (R i).Finite := fun i ↦ hfin.subset (hRsub i)
  obtain ⟨R₀, hR₀⟩ := hfin.isCompact.isBounded.exists_norm_le
  have hRnorm : ∀ i, ∀ y ∈ R i, ‖y‖ ≤ R₀ := fun i y hy ↦ hR₀ y (hRsub i hy)
  -- the exact argmax selectors of the regions
  choose sel hselm hsel using fun i ↦ exists_measurable_argmax_of_finite (hRfin i) (hRne i)
  obtain ⟨sel', hsel'⟩ : ∃ sel' : Fin (Fintype.card ι) → EuclideanSpace ℝ ι → 𝒳,
      ∀ i v, (sel' i v : EuclideanSpace ℝ ι) = sel i v :=
    ⟨fun i v ↦ ⟨sel i v, hRsub i (sel i v).2⟩, fun _ _ ↦ rfl⟩
  have hsel'm : ∀ i, Measurable (sel' i) := fun i ↦ by
    have : sel' i = fun v ↦ ⟨(sel i v : EuclideanSpace ℝ ι), hRsub i (sel i v).2⟩ :=
      funext fun v ↦ Subtype.ext (hsel' i v)
    rw [this]
    exact (measurable_subtype_coe.comp (hselm i)).subtype_mk
  have hsel'' : ∀ i v, (sel' i v : EuclideanSpace ℝ ι) ∈ R i ∧
      supportFn (R i) v ≤ ⟪(sel' i v : EuclideanSpace ℝ ι), v⟫ := fun i v ↦ by
    rw [hsel' i v]
    exact ⟨(sel i v).2, (hsel i v).symm.le⟩
  -- the `G`-optimal design and the regionalized width
  obtain ⟨wG, hwG⟩ := exists_isGOptimalDesign hfin.isCompact hspan
  set wR := regionalizedGw (designMatrix wG) R with hwR_def
  have hwR0 : 0 ≤ wR := regionalizedGw_nonneg hRne hRnorm _
  have hwR : wR ^ 2 ≤ 2 * Fintype.card ι *
      log (((𝒳.ncard / Fintype.card ι : ℕ) : ℝ) + 1) := by
    have h := hwG.regionalizedGw_le_sqrt_log hRsub hRfin hRne hRcard hR₀
    push_cast at h
    have hlogp : 0 ≤ log (((𝒳.ncard / Fintype.card ι : ℕ) : ℝ) + 1) :=
      Real.log_nonneg (by linarith [(Nat.cast_nonneg (𝒳.ncard / Fintype.card ι) : (0 : ℝ) ≤ _)])
    exact (Real.le_sqrt hwR0 (mul_nonneg (by positivity) hlogp)).1 h
  -- the length of the first phase
  have hlog2 : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hL4 : log 4 ≤ log (4 / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ0]; nlinarith [hδ.2])
  have hlog4 : (1 : ℝ) < log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith
  set Q := wR ^ 2 + Fintype.card ι * log (4 / δ) with hQ
  have hQd : (Fintype.card ι : ℝ) ≤ Q := by
    have : (Fintype.card ι : ℝ) ≤ Fintype.card ι * log (4 / δ) :=
      le_mul_of_one_le_right hd0 (by linarith)
    nlinarith [sq_nonneg wR]
  set T₁ := ⌈640 * Q / ε ^ 2⌉₊ with hT₁
  have hT₁Q : 640 * Q / ε ^ 2 ≤ T₁ := Nat.le_ceil _
  have hQ0 : 0 ≤ Q := hd0.trans hQd
  have hT₁lt : (T₁ : ℝ) < 640 * Q / ε ^ 2 + 1 :=
    Nat.ceil_lt_add_one (div_nonneg (mul_nonneg (by norm_num) hQ0) (sq_nonneg ε))
  have hT4 : 4 * Fintype.card ι ≤ T₁ := by
    have h1 : (4 * Fintype.card ι : ℝ) ≤ 640 * Q / ε ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      have hε1 : ε ^ 2 ≤ 1 := by nlinarith [hε.1, hε.2]
      nlinarith [mul_le_mul_of_nonneg_left hε1 hd0]
    exact_mod_cast h1.trans hT₁Q
  have hT₁pos : 0 < T₁ := by omega
  have hT₁0 : (0 : ℝ) < T₁ := by exact_mod_cast hT₁pos
  -- the rounded design
  obtain ⟨xr, hxr, hround⟩ := exists_rounding hwG.isDesign hwG.posDef hT4
  obtain ⟨x, hx⟩ : ∃ x : Fin T₁ → 𝒳, ∀ t, (x t : EuclideanSpace ℝ ι) = xr t :=
    ⟨fun t ↦ ⟨xr t, hwG.isDesign.mem_of_mem_support (hxr t)⟩, fun _ ↦ rfl⟩
  set Sm := ∑ t, outerSelf (x t : EuclideanSpace ℝ ι) with hSm
  have hround' : ((T₁ : ℝ) / 4) • designMatrix wG ≤ Sm := by
    simp_rw [hSm, hx]
    exact hround
  have hSmpd : Sm.PosDef := posDef_of_smul_le hwG.posDef hT₁pos hround'
  -- the variance proxy `σ² = 4 d / T₁`
  obtain ⟨σ, hσ2, hσ0⟩ : ∃ σ : ℝ≥0, (σ : ℝ) ^ 2 = 4 * Fintype.card ι / T₁ ∧ 0 < σ :=
    ⟨⟨√(4 * Fintype.card ι / T₁), Real.sqrt_nonneg _⟩, Real.sq_sqrt (by positivity),
      NNReal.coe_pos.1 (show (0 : ℝ) < √(4 * Fintype.card ι / T₁) by positivity)⟩
  have hσ : ∀ y ∈ 𝒳, WithLp.ofLp y ⬝ᵥ Sm⁻¹ *ᵥ WithLp.ofLp y ≤ σ ^ 2 := fun y hy ↦ by
    rw [hσ2]
    calc WithLp.ofLp y ⬝ᵥ Sm⁻¹ *ᵥ WithLp.ofLp y
        ≤ 4 / T₁ * (WithLp.ofLp y ⬝ᵥ (designMatrix wG)⁻¹ *ᵥ WithLp.ofLp y) :=
          dotProduct_inv_mulVec_le_of_smul_le hwG.posDef hT₁pos hround' _
      _ ≤ 4 / T₁ * Fintype.card ι := by gcongr; exact hwG.dotProduct_inv_mulVec_le y hy
      _ = 4 * Fintype.card ι / T₁ := by ring
  -- the widths of the regions for the rounded design
  have hgw : ∀ i, gwMat (R i) Sm ≤ 2 / √T₁ * wR := fun i ↦
    (gwMat_le_of_smul_le (hRfin i).isCompact (hRne i) (hRnorm i) hwG.posDef hT₁pos
      hround').trans (by gcongr; exact gwMat_le_regionalizedGw _ _ i)
  have hcG : (gaussianConcentrationConst : ℝ) ≤ 5 / 2 := by
    rw [coe_gaussianConcentrationConst]
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  have hbound : ∀ i, 2 * gwMat (R i) Sm +
      2 * σ * √(2 * gaussianConcentrationConst * log (1 / (δ / 2))) ≤ ε / 2 := fun i ↦ by
    have h1 := region_phase1_arith hwR0 hd0 hT₁0 hε0 hδ σ.2 hσ2 gaussianConcentrationConst.2 hcG
      hT₁Q
    calc 2 * gwMat (R i) Sm + 2 * σ * √(2 * gaussianConcentrationConst * log (1 / (δ / 2)))
        ≤ 2 * (2 / √T₁ * wR) + 2 * σ * √(2 * gaussianConcentrationConst * log (1 / (δ / 2))) := by
          gcongr
          exact hgw i
      _ ≤ ε / 2 := h1
  -- the region algorithm
  set B : PhasedAlg 𝒳 ℝ ((Fin (Fintype.card ι) → 𝒳) × Finset (Fin (Fintype.card ι))) :=
    regionAlg hd1 x hT₁pos sel' hsel'm hε0 hδ with hB
  have hpac : IsPAC 𝒳 (B.toIdentAlg (numRounds (Fintype.card ι) + 1) (meOut (𝓐 := 𝒳) hd1)
      (measurable_meOut hd1)) ε δ :=
    isPAC_regionAlg hfin ⟨x₀, hx₀⟩ hRsub hRne hcover hsel'' hSmpd hσ0 hσ hbound
  refine ⟨T₁ + budget (Fintype.card ι) (ε / 2) (δ / 2), ?_,
    B.toIdentAlg (numRounds (Fintype.card ι) + 1) (meOut (𝓐 := 𝒳) hd1) (measurable_meOut hd1),
    ?_, hpac⟩
  · -- the budget
    push_cast
    exact logGains_budget_arith hd1 hdm hε hδ hwR hT₁lt.le
      (budget_le_of_le_one ⟨half_pos hε0, by linarith [hε.2]⟩ ⟨half_pos hδ0, by linarith [hδ.2]⟩ _)
  · rw [← start_regionAlg (hK := hd1) (x := x) (hT₁ := hT₁pos) (hsel := hsel'm) (hε := hε0)
      (hδ := hδ)]
    exact PhasedAlg.isFixedBudget_toIdentAlg _

/-- **Table 1, multi-task bandits**: an `(ε, δ)`-PAC identification algorithm with budget `T ≥ 1`
on the multi-task set with block sizes `dⱼ ≥ 2`, with `δ < 2/5`, satisfies
`T > (∑ⱼ √dⱼ)² / (20000 ε²)`. -/
theorem multitaskSet_lt_budget_of_isPAC {m : ℕ} (d : Fin m → ℕ) (hd : ∀ j, 2 ≤ d j)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : δ < 2 / 5) {T : ℕ} (hT : 1 ≤ T)
    (A : IdentAlg (multitaskSet d) ℝ (multitaskSet d)) (hA : A.IsFixedBudget T)
    (hpac : IsPAC (multitaskSet d) A ε δ) :
    (∑ j, √(d j)) ^ 2 / (20000 * ε ^ 2) < T := by
  by_contra hcon
  push Not at hcon
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hcon
    rw [show (0 : ℝ) ^ 2 / (20000 * ε ^ 2) = 0 by simp] at hcon
    linarith
  · have hkey := le_of_isPAC_multitaskSet hm hd hε A hA hpac (by rw [mtSum]; exact hcon)
    linarith

/-- **Table 1, hypercube `{-1, 1}^d`**: an `(ε, δ)`-PAC identification algorithm with budget
`T ≥ 1` on `{-1, 1}^d`, with `δ < 1/6`, satisfies `T > d² / (100 ε²)`. -/
theorem hypercubePM_lt_budget_of_isPAC {ε δ : ℝ} (hε : 0 < ε) (hδ : δ < 1 / 6) {T : ℕ}
    (hT : 1 ≤ T) (A : IdentAlg (hypercubePM ι) ℝ (hypercubePM ι)) (hA : A.IsFixedBudget T)
    (hpac : IsPAC (hypercubePM ι) A ε δ) :
    (Fintype.card ι : ℝ) ^ 2 / (100 * ε ^ 2) < T := by
  classical
  by_contra hcon
  push Not at hcon
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hd | hd
  · rw [hd] at hcon
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    simp only [Nat.cast_zero] at hcon
    rw [show (0 : ℝ) ^ 2 / (100 * ε ^ 2) = 0 by simp] at hcon
    linarith
  · have hd' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hd
    have h2 : (T : ℝ) * (100 * ε ^ 2) ≤ (Fintype.card ι : ℝ) ^ 2 :=
      (le_div_iff₀ (by positivity)).1 hcon
    have hkey := le_of_isPAC_cubeSet hypercubePM_eq_cubeSet (by norm_num)
      (M := 1) (c := 5 * ε / Fintype.card ι) (fun b ↦ by cases b <;> norm_num) hε
      (by positivity) (by field_simp; norm_num) A hA hpac ?_
    · linarith
    · rw [mul_one, div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [h2]

/-- **Table 1, hypercube `{0, 1}^d`**: an `(ε, δ)`-PAC identification algorithm with budget
`T ≥ 1` on `{0, 1}^d`, with `δ < 1/6`, satisfies `T > d² / (400 ε²)`. -/
theorem hypercube01_lt_budget_of_isPAC {ε δ : ℝ} (hε : 0 < ε) (hδ : δ < 1 / 6) {T : ℕ}
    (hT : 1 ≤ T) (A : IdentAlg (hypercube01 ι) ℝ (hypercube01 ι)) (hA : A.IsFixedBudget T)
    (hpac : IsPAC (hypercube01 ι) A ε δ) :
    (Fintype.card ι : ℝ) ^ 2 / (400 * ε ^ 2) < T := by
  classical
  by_contra hcon
  push Not at hcon
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hd | hd
  · rw [hd] at hcon
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    simp only [Nat.cast_zero] at hcon
    rw [show (0 : ℝ) ^ 2 / (400 * ε ^ 2) = 0 by simp] at hcon
    linarith
  · have hd' : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hd
    have h2 : (T : ℝ) * (400 * ε ^ 2) ≤ (Fintype.card ι : ℝ) ^ 2 :=
      (le_div_iff₀ (by positivity)).1 hcon
    have hkey := le_of_isPAC_cubeSet hypercube01_eq_cubeSet (by norm_num)
      (M := 1) (c := 10 * ε / Fintype.card ι) (fun b ↦ by cases b <;> norm_num) hε
      (by positivity) (by field_simp; norm_num) A hA hpac ?_
    · linarith
    · rw [mul_one, div_pow, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [h2]

/-- **Table 1, `m`-sets**: for `1 ≤ m` with `n := d - m + 1 ≥ 20 m`, an `(ε, δ)`-PAC
identification algorithm with budget `T ≥ 1` on the `m`-sets of `ℝ^d`, with `δ < 2/9`, satisfies
`T > m n / (2500 ε²)`. -/
theorem mSet_lt_budget_of_isPAC (m : ℕ) (hm : 1 ≤ m) (hmd : 20 * m ≤ Fintype.card ι - m + 1)
    {ε δ : ℝ} (hε : 0 < ε) (hδ : δ < 2 / 9) {T : ℕ} (hT : 1 ≤ T)
    (A : IdentAlg (mSet ι m) ℝ (mSet ι m)) (hA : A.IsFixedBudget T)
    (hpac : IsPAC (mSet ι m) A ε δ) :
    m * ((Fintype.card ι : ℝ) - m + 1) / (2500 * ε ^ 2) < T := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hkd : k ≤ Fintype.card ι := by omega
  have hn : Fintype.card ι = k + (Fintype.card ι - k) := by omega
  have hk : 20 * (k + 1) ≤ Fintype.card ι - k := by omega
  have hcast : ((Fintype.card ι - k : ℕ) : ℝ) = (Fintype.card ι : ℝ) - k := Nat.cast_sub hkd
  have hbud : (T : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * ((Fintype.card ι - k : ℕ) : ℝ) / (2500 * ε ^ 2) := by
    refine hcon.trans_eq ?_
    rw [hcast]
    push_cast
    ring
  have hkey := le_of_isPAC_mSet rfl hn hk hε hT A hA hpac hbud
  linarith

/-- **Table 1, unit ball**: an `(ε, δ)`-PAC identification algorithm with budget `T` on the unit
ball of `ℝ^d`, `d ≥ 2`, with `δ ≤ 1/500`, satisfies `T ≥ d² / (1000 ε²)`. -/
theorem unitBall_le_budget_of_isPAC (hd : 2 ≤ Fintype.card ι) {ε δ : ℝ} (hε : 0 < ε)
    (hδ : δ ≤ 1 / 500) {T : ℕ} (A : IdentAlg (unitBall ι) ℝ (unitBall ι)) (hA : A.IsFixedBudget T)
    (hpac : IsPAC (unitBall ι) A ε δ) :
    (Fintype.card ι : ℝ) ^ 2 / (1000 * ε ^ 2) ≤ T := by
  sorry

end COLT83
