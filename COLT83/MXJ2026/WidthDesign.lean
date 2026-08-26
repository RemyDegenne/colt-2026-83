/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.DesignSet

/-!
# The Gaussian width term and design matrices

Properties of the Gaussian width term `gw 𝒳 = inf {gwMat 𝒳 A : A ∈ designSet 𝒳, A ≻ 0}` that
involve the structure of the set of design matrices:

* `gw_le_sqrt_mul_gwMat_sum`: for an empirical design `x₀, …, x_{T-1} ∈ 𝒳` with positive
  definite design matrix `Σ = ∑ xₜ xₜᵀ`, `gwMat 𝒳 Σ ≥ gw 𝒳 / √T` (blueprint
  `lem:width_empirical`);
* `gw_image`: the Gaussian width term is invariant under invertible linear maps,
  `gw (M '' 𝒳) = gw 𝒳` (blueprint `lem:width_iso`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

open scoped RealInnerProductSpace MatrixOrder Matrix

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒳 : Set (EuclideanSpace ℝ ι)} {R : ℝ}

/-- The width of an empirical design of `T` points of `𝒳` is at least `gw 𝒳 / √T`. -/
lemma gw_le_sqrt_mul_gwMat_sum (hne : 𝒳.Nonempty) (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) {T : ℕ} (hT : 0 < T)
    {x : Fin T → EuclideanSpace ℝ ι} (hx : ∀ t, x t ∈ 𝒳) (hS : (∑ t, outerSelf (x t)).PosDef) :
    gw 𝒳 ≤ √T * gwMat 𝒳 (∑ t, outerSelf (x t)) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  set A := (T : ℝ)⁻¹ • ∑ t, outerSelf (x t) with hA
  have hAmem : A ∈ designSet 𝒳 := inv_smul_sum_outerSelf_mem_designSet hT hx
  have hApd : A.PosDef := hS.smul (inv_pos.2 hTpos)
  have hSA : ∑ t, outerSelf (x t) = (T : ℝ) • A := by
    rw [hA, smul_smul, mul_inv_cancel₀ hTpos.ne', one_smul]
  rw [hSA, gwMat_smul hne hR hApd hTpos, ← mul_assoc,
    mul_inv_cancel₀ (Real.sqrt_pos.2 hTpos).ne', one_mul]
  exact gw_le_gwMat hne hR hAmem hApd

/-- Invariance of the Gaussian width term under invertible linear maps:
`gw (M '' 𝒳) = gw 𝒳` (for a set admitting a positive definite design matrix, e.g. a spanning
set). -/
lemma gw_image (hne : 𝒳.Nonempty) (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) (hex : ∃ A ∈ designSet 𝒳, A.PosDef)
    {M : Matrix ι ι ℝ} (hM : IsUnit M) :
    gw (Matrix.toEuclideanCLM (𝕜 := ℝ) M '' 𝒳) = gw 𝒳 := by
  set L := Matrix.toEuclideanCLM (𝕜 := ℝ) M with hL
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hM
  have hne' : (L '' 𝒳).Nonempty := hne.image L
  have hR' : ∀ y ∈ L '' 𝒳, ‖y‖ ≤ ‖L‖ * R := by
    rintro _ ⟨x, hx, rfl⟩
    exact (L.le_opNorm x).trans (mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg _))
  have himg : designSet (L '' 𝒳) = (fun A ↦ M * A * Mᵀ) '' designSet 𝒳 :=
    designSet_image_toEuclideanCLM M
  have hpd : ∀ {A : Matrix ι ι ℝ}, A.PosDef → (M * A * Mᵀ).PosDef := fun hA ↦ by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hA.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.2 hM)
  have hpd' : ∀ {A : Matrix ι ι ℝ}, (M * A * Mᵀ).PosDef → A.PosDef := fun {A} hB ↦ by
    have hMinv : IsUnit M⁻¹ := Matrix.isUnit_nonsing_inv_iff.2 hM
    have h := hB.mul_mul_conjTranspose_same (Matrix.vecMul_injective_iff_isUnit.2 hMinv)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hdet, one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul,
      Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one, mul_one] at h
    exact h
  refine le_antisymm ?_ ?_
  · refine le_gw hex fun A hA hApd ↦ ?_
    rw [← gwMat_image hne hR hApd hdet]
    exact gw_le_gwMat hne' hR' (by rw [himg]; exact ⟨A, hA, rfl⟩) (hpd hApd)
  · obtain ⟨A₀, hA₀, hA₀'⟩ := hex
    refine le_gw ⟨M * A₀ * Mᵀ, by rw [himg]; exact ⟨A₀, hA₀, rfl⟩, hpd hA₀'⟩ fun B hB hBpd ↦ ?_
    rw [himg] at hB
    obtain ⟨A, hA, rfl⟩ := hB
    rw [gwMat_image hne hR (hpd' hBpd) hdet]
    exact gw_le_gwMat hne hR hA (hpd' hBpd)

end COLT83
