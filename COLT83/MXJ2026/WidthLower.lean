/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.NormalizedDesign
public import COLT83.MXJ2026.Width
public import COLT83.Mathlib.Probability.SudakovFernique
public import COLT83.Mathlib.Probability.GaussianMaxLower
public import COLT83.Mathlib.Analysis.InnerProductSpace.IsotropicSeparated

/-!
# Lower bound on the Gaussian width term: `w(𝒳) ≥ (1/8) √(d log ⌊d/2⌋)`

For a design `w` on `𝒳` with positive definite design matrix `A`, the whitened points
`A^{-1/2} x`, `x ∈ supp w`, are in isotropic position (`sum_mul_inner_sqrt_inv_sq`), so that
`⌊d/2⌋` of them are pairwise at distance at least `√(d/2)`
(`exists_separated_of_isotropic`). The Sudakov–Fernique inequality compares the maximum of the
Gaussian process `⟪A^{-1/2} x, g⟫` over these points with the maximum of `⌊d/2⌋` independent
`N(0, d/4)` variables, whose expectation is at least `(√d / 2) (√(log ⌊d/2⌋) / 4)`
(`sqrt_log_div_four_le_integral_iSup_pi_gaussianReal`). This gives
`gwMat 𝒳 A ≥ √(d log ⌊d/2⌋) / 8` (`sqrt_log_le_gwMat`) for every such `A`, hence the bound on
`gw 𝒳` (Proposition 4 (iii), `sqrt_log_le_gw` in `WidthBounds`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Matrix
open scoped RealInnerProductSpace MatrixOrder NNReal

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒳 : Set (EuclideanSpace ℝ ι)}
  {w : EuclideanSpace ℝ ι →₀ ℝ} {R : ℝ}

/-- The whitened weighted family `(w x, A^{-1/2} x)` of a design `w` with positive definite
design matrix `A` is in isotropic position: `∑ₓ w x ⟪A^{-1/2} x, v⟫² = ‖v‖²`. -/
lemma sum_mul_inner_sqrt_inv_sq (hA : (designMatrix w).PosDef) (v : EuclideanSpace ℝ ι) :
    ∑ x ∈ w.support,
      w x * ⟪toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (designMatrix w)⁻¹) x, v⟫ ^ 2 = ‖v‖ ^ 2 := by
  set L := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (designMatrix w)⁻¹)
  have h1 : ∑ x ∈ w.support, w x * ⟪L x, v⟫ ^ 2 =
      WithLp.ofLp v ⬝ᵥ designMatrix (Finsupp.mapDomain L w) *ᵥ WithLp.ofLp v := by
    rw [designMatrix_mapDomain, sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul, dotProduct_outerSelf_mulVec, real_inner_comm]
  rw [h1, designMatrix_mapDomain_toEuclideanCLM, transpose_sqrt, hA.sqrt_inv_mul_mul_sqrt_inv,
    one_mulVec, ← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial]

/-- **Sudakov minoration for a design matrix**: for a design `w` on `𝒳 ⊆ ℝ^d` with positive
definite design matrix `A` and `d ≥ 4`, `gwMat 𝒳 A ≥ √(d log ⌊d/2⌋) / 8`. -/
lemma sqrt_log_le_gwMat (hw : IsDesign 𝒳 w) (hA : (designMatrix w).PosDef) (hne : 𝒳.Nonempty)
    (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) (hd : 4 ≤ Fintype.card ι) :
    √(Fintype.card ι * log (Fintype.card ι / 2 : ℕ)) / 8 ≤ gwMat 𝒳 (designMatrix w) := by
  classical
  set d := Fintype.card ι with hd_def
  set m := d / 2 with hm_def
  have hm2 : 2 ≤ m := by omega
  have hmd : (m : ℝ) ≤ d / 2 := by rw [hm_def]; exact Nat.cast_div_le
  have : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  have hR0 : 0 ≤ R := nonneg_of_norm_le hne hR
  set L := toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (designMatrix w)⁻¹) with hL
  -- separated points in the whitened support
  have hiso : ∀ v, ∑ x : w.support, w x * ⟪L x, v⟫ ^ 2 = ‖v‖ ^ 2 := fun v ↦ by
    rw [← sum_mul_inner_sqrt_inv_sq hA v]
    exact Finset.sum_coe_sort w.support fun x ↦ w x * ⟪L x, v⟫ ^ 2
  obtain ⟨t, -, ht⟩ := exists_separated_of_isotropic (u := fun x : w.support ↦ L x)
    (w := fun x : w.support ↦ w x) (fun x ↦ hw.nonneg x)
    (by rw [Finset.sum_coe_sort w.support fun x ↦ w x]; exact hw.sum_eq_one) hiso m
  set y : Fin m → EuclideanSpace ℝ ι := fun k ↦ L (t k) with hy_def
  have hsep : ∀ k l, k ≠ l → (d : ℝ) / 2 ≤ ‖y k - y l‖ ^ 2 := fun k l hkl ↦ by
    refine le_trans ?_ (ht k l hkl)
    rw [finrank_euclideanSpace]
    linarith
  have hy𝒳 : ∀ k, (t k : EuclideanSpace ℝ ι) ∈ w.support := fun k ↦ (t k).2
  -- the Gaussian process over the separated points is below the support function
  have hLR : ∀ x ∈ L '' 𝒳, ‖x‖ ≤ ‖L‖ * R := by
    rintro _ ⟨x, hx, rfl⟩
    exact (L.le_opNorm x).trans (mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg _))
  have hy : ∀ k, ‖y k‖ ≤ ((‖L‖₊ * ‖R‖₊ : ℝ≥0) : ℝ) := fun k ↦ by
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg hR0]
    exact (L.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hR _ (hw.mem_of_mem_support (hy𝒳 k))) (norm_nonneg _))
  have hyint : Integrable (fun g ↦ ⨆ k, ⟪y k, g⟫) (stdGaussian (EuclideanSpace ℝ ι)) := by
    refine IsGaussian.integrable_of_abs_le_add_mul_norm (A := 0) (B := ‖L‖ * R)
      (measurable_ciSup_inner y).aestronglyMeasurable fun g ↦ ?_
    rw [zero_add]
    simpa [abs_of_nonneg hR0] using abs_ciSup_inner_le hy g
  have hA1 : ∫ g, ⨆ k, ⟪y k, g⟫ ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      gaussianWidth (L '' 𝒳) (stdGaussian (EuclideanSpace ℝ ι)) := by
    refine integral_mono hyint (integrable_supportFn_of_isGaussian (hne.image L) hLR) fun g ↦ ?_
    exact ciSup_le fun k ↦ inner_le_supportFn hLR ⟨t k, hw.mem_of_mem_support (hy𝒳 k), rfl⟩ g
  -- the law of the Gaussian process is `N(0, C Cᵀ)` with `C` the matrix of rows `y k`
  set C : Matrix (Fin m) ι ℝ := Matrix.of fun k j ↦ y k j with hC_def
  have hCg : ∀ (g : EuclideanSpace ℝ ι) (k : Fin m),
      (LinearMap.toContinuousLinearMap (toEuclideanLin C) g) k = ⟪y k, g⟫ := fun g k ↦ by
    simp only [LinearMap.coe_toContinuousLinearMap', EuclideanSpace.inner_eq_star_dotProduct,
      star_trivial, dotProduct]
    rw [show (toEuclideanLin C g) k = (C *ᵥ WithLp.ofLp g) k from rfl]
    simp only [mulVec, dotProduct, hC_def, Matrix.of_apply]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hCC : ∀ k l, (C * Cᵀ) k l = ⟪y k, y l⟫ := fun k l ↦ by
    simp only [mul_apply, transpose_apply, hC_def, Matrix.of_apply,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct]
    exact Finset.sum_congr rfl fun j _ ↦ mul_comm _ _
  have hlaw : (stdGaussian (EuclideanSpace ℝ ι)).map
      (LinearMap.toContinuousLinearMap (toEuclideanLin C)) = multivariateGaussian 0 (C * Cᵀ) := by
    rw [← multivariateGaussian_zero_one, multivariateGaussian_zero_map_toEuclideanLin
      PosSemidef.one, Matrix.mul_one]
  have hB : ∫ g, ⨆ k, ⟪y k, g⟫ ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∫ x, ⨆ k, x k ∂multivariateGaussian 0 (C * Cᵀ) := by
    rw [← hlaw, integral_map (by fun_prop) measurable_ciSup_apply.aestronglyMeasurable]
    simp_rw [hCg]
  -- Sudakov–Fernique comparison with `√(d/4)` times independent standard Gaussians
  set c : ℝ := √d / 2 with hc_def
  have hc0 : 0 ≤ c := by positivity
  have hc : c ^ 2 = d / 4 := by
    rw [hc_def, div_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    ring
  have hSF : ∫ x, ⨆ k, x k ∂multivariateGaussian 0 (c ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ)) ≤
      ∫ x, ⨆ k, x k ∂multivariateGaussian 0 (C * Cᵀ) := by
    refine sudakov_fernique (PosSemidef.one.smul (by positivity)) ?_ fun k l ↦ ?_
    · simpa [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose C
    · rw [hCC, hCC, hCC]
      by_cases hkl : k = l
      · subst hkl
        simp only [Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
        linarith
      · have h1 := hsep k l hkl
        rw [norm_sub_sq_real, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at *
        simp only [Matrix.smul_apply, one_apply_eq, one_apply_ne hkl, smul_eq_mul, mul_one,
          mul_zero, hc]
        linarith
  have hD : ∫ x, ⨆ k, x k ∂multivariateGaussian 0 (c ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ)) =
      c * ∫ x, ⨆ k, x k ∂multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ) := by
    rw [← multivariateGaussian_zero_map_smul PosSemidef.one c,
      integral_map (by fun_prop) measurable_ciSup_apply.aestronglyMeasurable, ← integral_const_mul]
    congr 1
    ext x
    rw [Real.mul_iSup_of_nonneg hc0]
    simp
  have hE : √(log m) / 4 ≤
      ∫ x, ⨆ k, x k ∂multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ) := by
    rw [multivariateGaussian_zero_one, ← map_pi_eq_stdGaussian,
      integral_map (by fun_prop) measurable_ciSup_apply.aestronglyMeasurable]
    have := sqrt_log_div_four_le_integral_iSup_pi_gaussianReal (ι := Fin m) (by simpa using hm2)
    simpa using this
  rw [gwMat_eq_gaussianWidth_stdGaussian hne hR]
  calc √(d * log m) / 8 = c * (√(log m) / 4) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), hc_def]
        ring
    _ ≤ c * ∫ x, ⨆ k, x k ∂multivariateGaussian 0 (1 : Matrix (Fin m) (Fin m) ℝ) := by gcongr
    _ = ∫ x, ⨆ k, x k ∂multivariateGaussian 0 (c ^ 2 • (1 : Matrix (Fin m) (Fin m) ℝ)) := hD.symm
    _ ≤ ∫ x, ⨆ k, x k ∂multivariateGaussian 0 (C * Cᵀ) := hSF
    _ = ∫ g, ⨆ k, ⟪y k, g⟫ ∂stdGaussian (EuclideanSpace ℝ ι) := hB.symm
    _ ≤ gaussianWidth (L '' 𝒳) (stdGaussian (EuclideanSpace ℝ ι)) := hA1

end COLT83
