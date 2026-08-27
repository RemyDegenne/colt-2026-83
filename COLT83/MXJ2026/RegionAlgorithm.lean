/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.MedianElimination
public import COLT83.MXJ2026.LeastSquares
public import COLT83.MXJ2026.DifferenceProcess
public import COLT83.MXJ2026.WidthUpper

/-!
# The region algorithm: fixed design, then Median Elimination on regional candidates

The *region algorithm* (blueprint `def:region_algorithm`, paper Appendix C) on a finite action set
`𝒳` covered by `K` regions `R i` is the phased algorithm `regionAlg` which

1. plays a fixed design `x` for `T₁` rounds, computes the least-squares estimate `θ̂` of the reward
   vector and selects in each region a candidate `sel i θ̂` maximizing `⟪·, θ̂⟫` on `R i`
   (`regionCandidates`);
2. runs Median Elimination with parameters `(ε / 2, δ / 2)` on the `K` candidates
   (`MedianElim.medianElim`) and recommends the surviving candidate.

`one_sub_le_measureReal_regionCandidates` (blueprint `lem:region_phase1`) is the guarantee of the
first phase: with probability at least `1 - δ'`, the candidate of the region of an optimal arm is
`ε'`-optimal, when `2 gwMat (R i) Σ + 2 σ √(2 c_G log(1/δ')) ≤ ε'` for the design matrix `Σ`
(Borell–TIS concentration of the difference process on the region). `isPAC_regionAlg`
(blueprint `thm:log_gains` (i)) combines it with the guarantee of Median Elimination through the
phase-by-phase analysis of `Phased.lean`: the algorithm is `(ε, δ)`-PAC with budget
`T₁ + N_ME(K, ε/2, δ/2)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Finset Learning Learning.LinearBandit
  Learning.MedianElim Matrix
open scoped RealInnerProductSpace NNReal MatrixOrder

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒳 : Set (EuclideanSpace ℝ ι)} {K T₁ : ℕ}
  {sel : Fin K → EuclideanSpace ℝ ι → 𝒳} {ε δ : ℝ}

/-- The state after the first phase of the region algorithm: the candidates `sel i θ̂` of the
regions, where `θ̂` is the least-squares estimate from the design `x` and the observations `y`,
and the set of all arms. -/
noncomputable def regionCandidates (x : Fin T₁ → 𝒳) (sel : Fin K → EuclideanSpace ℝ ι → 𝒳)
    (y : Fin T₁ → ℝ) : (Fin K → 𝒳) × Finset (Fin K) :=
  (fun i ↦ sel i (leastSquares (fun t ↦ (x t : EuclideanSpace ℝ ι)) y), univ)

lemma measurable_regionCandidates (x : Fin T₁ → 𝒳) (hsel : ∀ i, Measurable (sel i)) :
    Measurable (regionCandidates x sel) :=
  (measurable_pi_lambda _ fun i ↦ (hsel i).comp (continuous_leastSquares _).measurable).prodMk
    measurable_const

/-- **The region algorithm** (blueprint `def:region_algorithm`): play the design `x` for `T₁`
rounds, select a candidate per region from the least-squares estimate, then run Median
Elimination with parameters `(ε / 2, δ / 2)` on the candidates. -/
noncomputable def regionAlg (hK : 0 < K) (x : Fin T₁ → 𝒳) (hT₁ : 0 < T₁)
    (sel : Fin K → EuclideanSpace ℝ ι → 𝒳) (hsel : ∀ i, Measurable (sel i)) (hε : 0 < ε)
    (hδ : δ ∈ Set.Ioo 0 1) : PhasedAlg 𝒳 ℝ ((Fin K → 𝒳) × Finset (Fin K)) :=
  (medianElim 𝒳 hK (fun _ ↦ x ⟨0, hT₁⟩) (half_pos hε)
    ⟨half_pos hδ.1, by linarith [hδ.2]⟩).cons T₁ hT₁ x (regionCandidates x sel)
    (measurable_regionCandidates x hsel)

variable {hK : 0 < K} {x : Fin T₁ → 𝒳} {hT₁ : 0 < T₁} {hsel : ∀ i, Measurable (sel i)}
  {hε : 0 < ε} {hδ : δ ∈ Set.Ioo 0 1}

/-- The budget of the region algorithm: `T₁ + N_ME(K, ε/2, δ/2)`. -/
lemma start_regionAlg :
    (regionAlg hK x hT₁ sel hsel hε hδ).start (numRounds K + 1) = T₁ + budget K (ε / 2) (δ / 2) :=
  PhasedAlg.cons_start_succ _

section phase1

variable {R : Fin K → Set (EuclideanSpace ℝ ι)}

/-- **The candidate of the region of an optimal arm is good** (blueprint `lem:region_phase1`):
for a design `x` with positive definite design matrix `Σ`, `xᵀ Σ⁻¹ x ≤ σ²` on `𝒳`, regions `R i`
covering `𝒳` with exact argmax selectors `sel i`, and
`2 gwMat (R i) Σ + 2 σ √(2 c_G log(1/δ')) ≤ ε'` for every region, with probability at least
`1 - δ'` over the noise some candidate is `ε'`-optimal. -/
lemma one_sub_le_measureReal_regionCandidates (h𝒳 : 𝒳.Finite) (hne : 𝒳.Nonempty)
    (hRsub : ∀ i, R i ⊆ 𝒳) (hRne : ∀ i, (R i).Nonempty) (hcover : 𝒳 ⊆ ⋃ i, R i)
    (hsel : ∀ i v, (sel i v : EuclideanSpace ℝ ι) ∈ R i ∧
      supportFn (R i) v ≤ ⟪(sel i v : EuclideanSpace ℝ ι), v⟫)
    (x : Fin T₁ → 𝒳) (hS : (∑ t, outerSelf (x t : EuclideanSpace ℝ ι)).PosDef) {σ : ℝ≥0}
    (hσ0 : 0 < σ)
    (hσ : ∀ y ∈ 𝒳, WithLp.ofLp y ⬝ᵥ (∑ t, outerSelf (x t : EuclideanSpace ℝ ι))⁻¹ *ᵥ
      WithLp.ofLp y ≤ σ ^ 2)
    {ε' δ' : ℝ} (hδ' : δ' ∈ Set.Ioo 0 1)
    (hbound : ∀ i, 2 * gwMat (R i) (∑ t, outerSelf (x t : EuclideanSpace ℝ ι)) +
      2 * σ * √(2 * gaussianConcentrationConst * log (1 / δ')) ≤ ε') (θ : EuclideanSpace ℝ ι) :
    1 - δ' ≤ (Measure.pi fun _ : Fin T₁ ↦ gaussianReal 0 1).real
      {η | ∃ b, supportFn 𝒳 θ - ε' ≤ ⟪(sel b (leastSquares (fun t ↦ (x t : EuclideanSpace ℝ ι))
        fun t ↦ ⟪(x t : EuclideanSpace ℝ ι), θ⟫ + η t) : EuclideanSpace ℝ ι), θ⟫} := by
  obtain ⟨R₀, hR₀⟩ := h𝒳.isCompact.isBounded.exists_norm_le
  have hRnorm : ∀ i, ∀ y ∈ R i, ‖y‖ ≤ R₀ := fun i y hy ↦ hR₀ y (hRsub i hy)
  have hRfin : ∀ i, (R i).Finite := fun i ↦ h𝒳.subset (hRsub i)
  obtain ⟨y₀, hy₀, hy₀eq⟩ := exists_supportFn_eq_inner h𝒳.isCompact hne θ
  obtain ⟨i₀, hi₀⟩ := Set.mem_iUnion.1 (hcover hy₀)
  set xT : Fin T₁ → EuclideanSpace ℝ ι := fun t ↦ (x t : EuclideanSpace ℝ ι) with hxT
  set Sm := ∑ t, outerSelf (xT t) with hSm
  set θh : (Fin T₁ → ℝ) → EuclideanSpace ℝ ι :=
    fun η ↦ leastSquares xT fun t ↦ ⟪xT t, θ⟫ + η t with hθh
  set P : Measure (Fin T₁ → ℝ) := Measure.pi fun _ ↦ gaussianReal 0 1 with hP
  have hθhm : Measurable θh :=
    (continuous_leastSquares xT).measurable.comp
      (measurable_pi_lambda _ fun t ↦ measurable_const.add (measurable_pi_apply t))
  -- the law of the estimation error
  have hΔ : HasLaw (fun η ↦ θh η - θ) (multivariateGaussian 0 Sm⁻¹) P := by
    have := (⟨(measurable_id.sub_const θ).aemeasurable, rfl⟩ :
      HasLaw (fun v : EuclideanSpace ℝ ι ↦ v - θ) _ _).comp (hasLaw_leastSquares_add_pi xT θ hS)
    rwa [multivariateGaussian_map_sub_const] at this
  -- the bad event
  set u := 2 * gwMat (R i₀) Sm + 2 * σ * √(2 * gaussianConcentrationConst * log (1 / δ')) with hu
  have hbad := measureReal_diffSup_gt_le (hRfin i₀).isCompact (hRne i₀) hS hσ0
    (fun y hy ↦ hσ y (hRsub i₀ hy)) hδ'
  have hbad_meas : MeasurableSet {η | u < diffSup (R i₀) (θh η - θ)} :=
    measurableSet_lt measurable_const
      ((continuous_diffSup (hRne i₀) (hRnorm i₀)).measurable.comp (hθhm.sub_const θ))
  have hbadP : P.real {η | u < diffSup (R i₀) (θh η - θ)} ≤ δ' := by
    rw [hΔ.measureReal_eq (measurableSet_lt measurable_const
      (continuous_diffSup (hRne i₀) (hRnorm i₀)).measurable)]
    exact hbad
  -- on the complement, the candidate of the region `i₀` is `ε'`-optimal
  have hgood : {η | u < diffSup (R i₀) (θh η - θ)}ᶜ ⊆
      {η | ∃ b, supportFn 𝒳 θ - ε' ≤ ⟪(sel b (θh η) : EuclideanSpace ℝ ι), θ⟫} := by
    intro η hη
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hη
    refine ⟨i₀, ?_⟩
    have h1 : ⟪y₀, θh η⟫ ≤ ⟪(sel i₀ (θh η) : EuclideanSpace ℝ ι), θh η⟫ :=
      (inner_le_supportFn (hRnorm i₀) hi₀ _).trans (hsel i₀ (θh η)).2
    have h2 : ⟪(sel i₀ (θh η) : EuclideanSpace ℝ ι), θh η - θ⟫ ≤ supportFn (R i₀) (θh η - θ) :=
      inner_le_supportFn (hRnorm i₀) (hsel i₀ (θh η)).1 _
    have h3 : ⟪y₀, -(θh η - θ)⟫ ≤ supportFn (R i₀) (-(θh η - θ)) :=
      inner_le_supportFn (hRnorm i₀) hi₀ _
    have h4 : diffSup (R i₀) (θh η - θ) ≤ ε' := hη.trans (hbound i₀)
    rw [diffSup] at h4
    rw [inner_sub_right] at h2
    rw [inner_neg_right, inner_sub_right] at h3
    rw [hy₀eq]
    linarith
  calc 1 - δ' ≤ 1 - P.real {η | u < diffSup (R i₀) (θh η - θ)} := by linarith
    _ = P.real {η | u < diffSup (R i₀) (θh η - θ)}ᶜ := by
        rw [measureReal_compl hbad_meas, probReal_univ]
    _ ≤ _ := measureReal_mono hgood

end phase1

section pac

universe u

variable {R : Fin K → Set (EuclideanSpace ℝ ι)}

omit [DecidableEq ι] in
/-- The good states of the region algorithm after `ℓ + 1` phases for the reward vector `θ`: the
surviving set is good for Median Elimination (blueprint `def:me_schedule`) with the means
`⟪c a, θ⟫` of the candidates `c` and the target value `sup_{y ∈ 𝒳} ⟪y, θ⟫ - ε / 2`. -/
def regionGood (𝒳 : Set (EuclideanSpace ℝ ι)) (ε : ℝ) (θ : EuclideanSpace ℝ ι) (ℓ : ℕ) :
    Set ((Fin K → 𝒳) × Finset (Fin K)) :=
  {p | p.2 ∈ goodSet (fun a ↦ ⟪(p.1 a : EuclideanSpace ℝ ι), θ⟫) (supportFn 𝒳 θ - ε / 2) (ε / 2) ℓ}

omit [DecidableEq ι] in
lemma measurableSet_regionGood (𝒳 : Set (EuclideanSpace ℝ ι)) (ε : ℝ) (θ : EuclideanSpace ℝ ι)
    (ℓ : ℕ) : MeasurableSet (regionGood (K := K) 𝒳 ε θ ℓ) := by
  refine measurableSet_setOfPred.2 (measurable_from_prod_countable_left fun S ↦ ?_)
  simp only [goodSet, Set.mem_ofPred_eq]
  refine measurable_const.and ?_
  refine Measurable.exists fun b ↦ ?_
  refine measurable_const.and (measurableSet_setOfPred.1 (measurableSet_le measurable_const ?_))
  exact (continuous_id.inner continuous_const).measurable.comp
    (measurable_subtype_coe.comp (measurable_pi_apply b))

/-- **The region algorithm is `(ε, δ)`-PAC** (blueprint `thm:log_gains` (i)), for a design `x`
with positive definite design matrix `Σ`, `xᵀ Σ⁻¹ x ≤ σ²` on `𝒳`, regions covering `𝒳` with exact
argmax selectors, and `2 gwMat (R i) Σ + 2 σ √(2 c_G log(2/δ)) ≤ ε / 2` for every region. -/
lemma isPAC_regionAlg (h𝒳 : 𝒳.Finite) (hne : 𝒳.Nonempty)
    (hRsub : ∀ i, R i ⊆ 𝒳) (hRne : ∀ i, (R i).Nonempty) (hcover : 𝒳 ⊆ ⋃ i, R i)
    (hsel' : ∀ i v, (sel i v : EuclideanSpace ℝ ι) ∈ R i ∧
      supportFn (R i) v ≤ ⟪(sel i v : EuclideanSpace ℝ ι), v⟫)
    (hS : (∑ t, outerSelf (x t : EuclideanSpace ℝ ι)).PosDef) {σ : ℝ≥0} (hσ0 : 0 < σ)
    (hσ : ∀ y ∈ 𝒳, WithLp.ofLp y ⬝ᵥ (∑ t, outerSelf (x t : EuclideanSpace ℝ ι))⁻¹ *ᵥ
      WithLp.ofLp y ≤ σ ^ 2)
    (hbound : ∀ i, 2 * gwMat (R i) (∑ t, outerSelf (x t : EuclideanSpace ℝ ι)) +
      2 * σ * √(2 * gaussianConcentrationConst * log (1 / (δ / 2))) ≤ ε / 2) :
    IsPAC 𝒳 ((regionAlg hK x hT₁ sel hsel hε hδ).toIdentAlg (numRounds K + 1) (meOut hK)
      (measurable_meOut hK)) ε δ := by
  refine PhasedAlg.linearBandit_isPAC_toIdentAlg _ fun θ ↦ ?_
  have hδ2 : δ / 2 ∈ Set.Ioo 0 1 := ⟨half_pos hδ.1, by linarith [hδ.2]⟩
  refine ⟨fun ℓ ↦ Nat.casesOn ℓ Set.univ fun ℓ ↦ regionGood 𝒳 ε θ ℓ, fun ℓ ↦ ?_, Set.mem_univ _,
    ⟨fun ℓ ↦ Nat.casesOn ℓ (δ / 2) fun ℓ ↦ deltaSched (δ / 2) ℓ, fun ℓ ↦ ?_, ?_, ?_⟩, ?_⟩
  · cases ℓ with
    | zero => exact MeasurableSet.univ
    | succ ℓ => exact measurableSet_regionGood 𝒳 ε θ ℓ
  · cases ℓ with
    | zero => exact hδ2.1.le
    | succ ℓ => exact (deltaSched_pos hδ2.1 ℓ).le
  · rw [sum_range_succ']
    have := sum_deltaSched_le hδ2.1.le (numRounds K)
    simp only [Nat.rec_zero]
    linarith
  · intro ℓ hℓ p hp
    cases ℓ with
    | zero =>
      -- first phase: the candidate of the region of an optimal arm is `ε / 2`-optimal
      refine (one_sub_le_measureReal_regionCandidates h𝒳 hne hRsub hRne hcover hsel' x hS hσ0 hσ
        hδ2 hbound θ).trans (measureReal_mono fun η hη ↦ ?_)
      obtain ⟨b, hb⟩ := hη
      change (regionCandidates x sel fun t ↦ ⟪(x t : EuclideanSpace ℝ ι), θ⟫ + η t) ∈
        regionGood 𝒳 ε θ 0
      refine ⟨by simp [regionCandidates, survivors_zero], b, mem_univ b, ?_⟩
      simpa [regionCandidates] using hb
    | succ ℓ =>
      -- Median Elimination rounds
      obtain ⟨c, S⟩ := p
      refine (one_sub_le_measureReal_roundNext_mem (half_pos hε) hδ2
        (fun a ↦ ⟪(c a : EuclideanSpace ℝ ι), θ⟫) (supportFn 𝒳 θ - ε / 2) ℓ ⟨0, hK⟩ hp).trans
        (measureReal_mono fun η hη ↦ hη)
  · rintro ⟨c, S⟩ ⟨hcard, b, hb, hMb⟩
    obtain ⟨b', rfl⟩ := Finset.card_eq_one.1 (hcard.trans (survivors_numRounds hK))
    rw [mem_singleton] at hb
    subst hb
    rw [meOut_singleton]
    have h1 := sum_epsSched_le (half_pos hε).le (numRounds K)
    change supportFn 𝒳 θ - ⟪(c b : EuclideanSpace ℝ ι), θ⟫ ≤ ε
    linarith

end pac

end COLT83
