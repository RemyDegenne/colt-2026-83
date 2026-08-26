/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.Mathlib.Analysis.Calculus.LocalExtr
public import COLT83.Mathlib.Matrix.Loewner
public import COLT83.MXJ2026.DesignSet
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import COLT83.Mathlib.Analysis.InnerProductSpace.EuclideanMatrix

/-!
# Design distributions and the Kiefer–Wolfowitz theorem

A *design distribution* on an action set `𝒳 ⊆ EuclideanSpace ℝ ι` is a finitely supported
probability vector on points of `𝒳`, encoded as a finitely supported function
`w : EuclideanSpace ℝ ι →₀ ℝ` with `IsDesign 𝒳 w`. Its *design matrix* is
`designMatrix w = ∑ₓ w x • x xᵀ`.

## Main definitions

* `designMatrix`: the linear map `w ↦ ∑ₓ w x • x xᵀ`;
* `IsDesign 𝒳 w`: `w` is a design distribution on `𝒳`;
* `gValue 𝒳 A = sup_{x ∈ 𝒳} xᵀ A⁻¹ x`: the `G`-value of the matrix `A` on `𝒳`;
* `IsGOptimalDesign 𝒳 w`: `w` is a design distribution with positive definite design matrix
  `A` such that `xᵀ A⁻¹ x ≤ card ι` for all `x ∈ 𝒳` (a `G`-optimal design).

## Main results

* `exists_isDesign_of_mem_designSet`: Carathéodory's theorem for design matrices: every element
  of `designSet 𝒳` is the design matrix of a design distribution on `𝒳` supported on at most
  `card ι ^ 2 + 1` points.
* `sum_mul_dotProduct_inv_mulVec`: `∑ₓ w x * xᵀ A(w)⁻¹ x = card ι` when `A(w)` is invertible;
  hence the `G`-value of a design matrix is at least `card ι` (`IsDesign.card_le_gValue`).
* `exists_isGOptimalDesign` (**Kiefer–Wolfowitz**): if `𝒳` is compact and spans the space, a
  `G`-optimal design exists. It is obtained as a `D`-optimal design, i.e. a maximizer of the
  determinant over `designSet 𝒳` (`exists_isMaxOn_det_designSet`, `posDef_of_isMaxOn_det`):
  moving the maximizer `A` towards `x xᵀ` cannot increase the determinant, and the matrix
  determinant lemma computes `det ((1 - t) • A + t • x xᵀ)` explicitly, so that the derivative
  at `t = 0` gives `xᵀ A⁻¹ x ≤ card ι`.
* Properties of `G`-optimal designs: the `G`-value is exactly `card ι`
  (`IsGOptimalDesign.gValue_eq`), `xᵀ A⁻¹ x = card ι` on the support
  (`IsGOptimalDesign.dotProduct_inv_mulVec_eq_card`), the whitened arms `√(A⁻¹) x` have norm at
  most `√(card ι)` (`IsGOptimalDesign.norm_sqrt_inv_le`), and the normalized design
  `x ↦ (card ι)^{-1/2} √(A⁻¹) x` has unit-norm support points and design matrix
  `(card ι)⁻¹ • 1` (`IsGOptimalDesign.norm_normalizeMat_eq_one`,
  `IsGOptimalDesign.designMatrix_mapDomain_normalizeMat`).
-/

@[expose] public section

open Real Filter Set
open scoped RealInnerProductSpace MatrixOrder Matrix Topology

namespace COLT83

variable {ι : Type*} {𝒳 : Set (EuclideanSpace ℝ ι)} {w : EuclideanSpace ℝ ι →₀ ℝ}
  {A : Matrix ι ι ℝ} {x : EuclideanSpace ℝ ι}

/-- The design matrix `∑ₓ w x • x xᵀ` of finitely supported weights `w` on the space. -/
noncomputable def designMatrix : (EuclideanSpace ℝ ι →₀ ℝ) →ₗ[ℝ] Matrix ι ι ℝ :=
  Finsupp.linearCombination ℝ outerSelf

lemma designMatrix_apply (w : EuclideanSpace ℝ ι →₀ ℝ) :
    designMatrix w = ∑ x ∈ w.support, w x • outerSelf x :=
  Finsupp.linearCombination_apply ℝ w

/-- A design distribution on `𝒳`: finitely supported nonnegative weights on points of `𝒳`
summing to one. -/
structure IsDesign (𝒳 : Set (EuclideanSpace ℝ ι)) (w : EuclideanSpace ℝ ι →₀ ℝ) : Prop where
  support_subset : ↑w.support ⊆ 𝒳
  nonneg : ∀ x, 0 ≤ w x
  sum_eq_one : ∑ x ∈ w.support, w x = 1

lemma IsDesign.mono {𝒴 : Set (EuclideanSpace ℝ ι)} (hw : IsDesign 𝒳 w) (h : 𝒳 ⊆ 𝒴) :
    IsDesign 𝒴 w :=
  ⟨hw.support_subset.trans h, hw.nonneg, hw.sum_eq_one⟩

lemma IsDesign.mem_of_mem_support (hw : IsDesign 𝒳 w) (hx : x ∈ w.support) : x ∈ 𝒳 :=
  hw.support_subset hx

lemma IsDesign.pos_of_mem_support (hw : IsDesign 𝒳 w) (hx : x ∈ w.support) : 0 < w x :=
  lt_of_le_of_ne (hw.nonneg x) (Finsupp.mem_support_iff.mp hx).symm

lemma IsDesign.support_nonempty (hw : IsDesign 𝒳 w) : w.support.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  rintro h
  simpa [h] using hw.sum_eq_one

/-- The design matrix of a design distribution on `𝒳` belongs to `designSet 𝒳`. -/
lemma IsDesign.designMatrix_mem_designSet (hw : IsDesign 𝒳 w) : designMatrix w ∈ designSet 𝒳 := by
  rw [designMatrix_apply]
  exact convex_designSet.sum_mem (fun x _ ↦ hw.nonneg x) hw.sum_eq_one
    fun x hx ↦ outerSelf_mem_designSet (hw.mem_of_mem_support hx)

/-- The image of a design distribution on `𝒳` by a map `f` is a design distribution on
`f '' 𝒳`. -/
lemma IsDesign.mapDomain (hw : IsDesign 𝒳 w) (f : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) :
    IsDesign (f '' 𝒳) (Finsupp.mapDomain f w) := by
  classical
  refine ⟨?_, fun y ↦ ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hy)
    exact ⟨x, hw.mem_of_mem_support hx, rfl⟩
  · rw [Finsupp.mapDomain, Finsupp.sum_apply]
    exact Finset.sum_nonneg fun x _ ↦ by
      dsimp only
      rw [Finsupp.single_apply]
      split_ifs <;> simp [hw.nonneg]
  · change (Finsupp.mapDomain f w).sum (fun _ a ↦ a) = 1
    rw [Finsupp.sum_mapDomain_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)]
    exact hw.sum_eq_one

variable [Fintype ι]

/-- Carathéodory's theorem for design matrices: every design matrix in `designSet 𝒳` is the
design matrix of a design distribution on `𝒳` supported on at most `card ι ^ 2 + 1` points. -/
lemma exists_isDesign_of_mem_designSet (hA : A ∈ designSet 𝒳) :
    ∃ w, IsDesign 𝒳 w ∧ designMatrix w = A ∧ w.support.card ≤ Fintype.card ι ^ 2 + 1 := by
  classical
  obtain ⟨κ, _, z, v, hz, hind, hv, hv1, rfl⟩ := eq_pos_convex_span_of_mem_convexHull hA
  choose x hx𝒳 hxz using fun i ↦ hz (Set.mem_range_self i)
  have hxinj : Function.Injective x := fun i j h ↦ hind.injective (by rw [← hxz, ← hxz, h])
  set v' : κ →₀ ℝ := Finsupp.equivFunOnFinite.symm v with hv'
  have hv'_apply : ∀ i, v' i = v i := fun i ↦ rfl
  have hsupp : (Finsupp.mapDomain x v').support = v'.support.image x :=
    Finsupp.mapDomain_support_of_injective hxinj _
  refine ⟨Finsupp.mapDomain x v', ⟨?_, fun y ↦ ?_, ?_⟩, ?_, ?_⟩
  · intro y hy
    rw [Finset.mem_coe, hsupp, Finset.mem_image] at hy
    obtain ⟨i, -, rfl⟩ := hy
    exact hx𝒳 i
  · by_cases hy : y ∈ Set.range x
    · obtain ⟨i, rfl⟩ := hy
      rw [Finsupp.mapDomain_apply hxinj, hv'_apply]
      exact (hv i).le
    · rw [Finsupp.mapDomain_of_notMem_range _ _ hy]
  · change (Finsupp.mapDomain x v').sum (fun _ a ↦ a) = 1
    rw [Finsupp.sum_mapDomain_index (fun _ ↦ rfl) (fun _ _ _ ↦ rfl), Finsupp.sum_fintype _ _
      fun _ ↦ rfl]
    exact hv1
  · rw [designMatrix, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
      Finsupp.sum_fintype _ _ fun _ ↦ by simp]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hv'_apply, Function.comp_apply, hxz]
  · rw [hsupp, Finset.card_image_of_injective _ hxinj]
    calc v'.support.card ≤ Fintype.card κ := Finset.card_le_univ _
      _ ≤ Module.finrank ℝ (Matrix ι ι ℝ) + 1 :=
        hind.card_le_finrank_succ.trans (by gcongr; exact Submodule.finrank_le _)
      _ = Fintype.card ι ^ 2 + 1 := by rw [Module.finrank_matrix, Module.finrank_self, sq]; ring

omit [Fintype ι] in
/-- The design set is the set of design matrices of design distributions. -/
lemma mem_designSet_iff [Finite ι] : A ∈ designSet 𝒳 ↔ ∃ w, IsDesign 𝒳 w ∧ designMatrix w = A := by
  have := Fintype.ofFinite ι
  exact ⟨fun hA ↦ (exists_isDesign_of_mem_designSet hA).imp fun _ h ↦ ⟨h.1, h.2.1⟩,
    fun ⟨_, hw, hA⟩ ↦ hA ▸ hw.designMatrix_mem_designSet⟩

variable [DecidableEq ι]

/-- The design matrix of the image of `w` by the linear map of matrix `M` is `M A(w) Mᵀ`. -/
lemma designMatrix_mapDomain_toEuclideanCLM (M : Matrix ι ι ℝ) (w : EuclideanSpace ℝ ι →₀ ℝ) :
    designMatrix (Finsupp.mapDomain (Matrix.toEuclideanCLM (𝕜 := ℝ) M) w) =
      M * designMatrix w * Mᵀ := by
  rw [designMatrix, Finsupp.linearCombination_mapDomain, Finsupp.linearCombination_apply,
    Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [Function.comp_apply, outerSelf_toEuclideanCLM, Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq ι] in
/-- For weights `w` with design matrix `A = ∑ₓ w x • x xᵀ` and any matrix `C`,
`∑ₓ w x * xᵀ C x = tr (C A)`. -/
lemma sum_mul_dotProduct_mulVec (C : Matrix ι ι ℝ) (w : EuclideanSpace ℝ ι →₀ ℝ) :
    ∑ x ∈ w.support, w x * (WithLp.ofLp x ⬝ᵥ C *ᵥ WithLp.ofLp x) = (C * designMatrix w).trace := by
  simp_rw [dotProduct_mulVec_eq_trace_mul_outerSelf]
  rw [designMatrix_apply, Matrix.mul_sum, Matrix.trace_sum]
  simp_rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- For weights `w` with invertible design matrix `A = ∑ₓ w x • x xᵀ`,
`∑ₓ w x * xᵀ A⁻¹ x = card ι`. -/
lemma sum_mul_dotProduct_inv_mulVec (hA : IsUnit (designMatrix w).det) :
    ∑ x ∈ w.support, w x * (WithLp.ofLp x ⬝ᵥ (designMatrix w)⁻¹ *ᵥ WithLp.ofLp x) =
      Fintype.card ι := by
  rw [sum_mul_dotProduct_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.trace_one]

section gValue

/-- The `G`-value of the matrix `A` on `𝒳`: `sup_{x ∈ 𝒳} xᵀ A⁻¹ x`. -/
noncomputable def gValue (𝒳 : Set (EuclideanSpace ℝ ι)) (A : Matrix ι ι ℝ) : ℝ :=
  ⨆ x : 𝒳, WithLp.ofLp (x : EuclideanSpace ℝ ι) ⬝ᵥ A⁻¹ *ᵥ WithLp.ofLp (x : EuclideanSpace ℝ ι)

lemma dotProduct_inv_mulVec_le_gValue (h𝒳 : IsCompact 𝒳) (hx : x ∈ 𝒳) :
    WithLp.ofLp x ⬝ᵥ A⁻¹ *ᵥ WithLp.ofLp x ≤ gValue 𝒳 A :=
  le_ciSup (Matrix.bddAbove_range_dotProduct_mulVec h𝒳 A⁻¹) ⟨x, hx⟩

lemma gValue_le (hne : 𝒳.Nonempty) {c : ℝ}
    (h : ∀ x ∈ 𝒳, WithLp.ofLp x ⬝ᵥ A⁻¹ *ᵥ WithLp.ofLp x ≤ c) : gValue 𝒳 A ≤ c := by
  have := hne.to_subtype
  exact ciSup_le fun x ↦ h x x.2

/-- The `G`-value of the design matrix of a design distribution is at least `card ι`. -/
lemma IsDesign.card_le_gValue (h𝒳 : IsCompact 𝒳) (hw : IsDesign 𝒳 w)
    (hA : IsUnit (designMatrix w).det) :
    (Fintype.card ι : ℝ) ≤ gValue 𝒳 (designMatrix w) := by
  rw [← sum_mul_dotProduct_inv_mulVec hA]
  calc ∑ x ∈ w.support, w x * (WithLp.ofLp x ⬝ᵥ (designMatrix w)⁻¹ *ᵥ WithLp.ofLp x)
      ≤ ∑ x ∈ w.support, w x * gValue 𝒳 (designMatrix w) :=
        Finset.sum_le_sum fun x hx ↦ mul_le_mul_of_nonneg_left
          (dotProduct_inv_mulVec_le_gValue h𝒳 (hw.mem_of_mem_support hx)) (hw.nonneg x)
    _ = gValue 𝒳 (designMatrix w) := by rw [← Finset.sum_mul, hw.sum_eq_one, one_mul]

/-- If the design matrix `A` of a design distribution `w` satisfies `xᵀ A⁻¹ x ≤ card ι` on `𝒳`,
then `xᵀ A⁻¹ x = card ι` for every `x` in the support of `w`. -/
lemma IsDesign.dotProduct_inv_mulVec_eq_card (hw : IsDesign 𝒳 w)
    (hA : IsUnit (designMatrix w).det)
    (h : ∀ x ∈ 𝒳, WithLp.ofLp x ⬝ᵥ (designMatrix w)⁻¹ *ᵥ WithLp.ofLp x ≤ Fintype.card ι)
    (hx : x ∈ w.support) :
    WithLp.ofLp x ⬝ᵥ (designMatrix w)⁻¹ *ᵥ WithLp.ofLp x = Fintype.card ι := by
  have hsum : ∑ y ∈ w.support,
      w y * (Fintype.card ι - WithLp.ofLp y ⬝ᵥ (designMatrix w)⁻¹ *ᵥ WithLp.ofLp y) = 0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, sum_mul_dotProduct_inv_mulVec hA, ← Finset.sum_mul,
      hw.sum_eq_one, one_mul, sub_self]
  rw [Finset.sum_eq_zero_iff_of_nonneg fun y hy ↦ mul_nonneg (hw.nonneg y)
    (sub_nonneg.2 (h y (hw.mem_of_mem_support hy)))] at hsum
  have := hsum x hx
  rw [mul_eq_zero, sub_eq_zero] at this
  exact (this.resolve_left (hw.pos_of_mem_support hx).ne').symm

end gValue

section dOptimal

/-- A `D`-optimal design matrix exists: the determinant is continuous on the compact set
`designSet 𝒳`. -/
lemma exists_isMaxOn_det_designSet (h𝒳 : IsCompact 𝒳) (hne : 𝒳.Nonempty) :
    ∃ A ∈ designSet 𝒳, IsMaxOn Matrix.det (designSet 𝒳) A := by
  obtain ⟨x, hx⟩ := hne
  exact (isCompact_designSet h𝒳).exists_isMaxOn ⟨_, outerSelf_mem_designSet hx⟩
    (continuous_id.matrix_det).continuousOn

/-- If `𝒳` spans the space, a `D`-optimal design matrix is positive definite. -/
lemma posDef_of_isMaxOn_det [Nonempty ι] (hspan : Submodule.span ℝ 𝒳 = ⊤) (hA : A ∈ designSet 𝒳)
    (hmax : IsMaxOn Matrix.det (designSet 𝒳) A) : A.PosDef := by
  obtain ⟨A', hA', hA'pd⟩ := exists_posDef_mem_designSet hspan
  have : 0 < A.det := hA'pd.det_pos.trans_le (hmax hA')
  exact (posSemidef_of_mem_designSet hA).posDef_iff_det_ne_zero.mpr this.ne'

end dOptimal

section gOptimal

/-- `w` is a `G`-optimal design on `𝒳`: a design distribution on `𝒳` whose design matrix `A` is
positive definite with `xᵀ A⁻¹ x ≤ card ι` for every `x ∈ 𝒳` (the smallest possible value of the
`G`-value of a design matrix, see `IsDesign.card_le_gValue`). -/
structure IsGOptimalDesign (𝒳 : Set (EuclideanSpace ℝ ι)) (w : EuclideanSpace ℝ ι →₀ ℝ) :
    Prop where
  isDesign : IsDesign 𝒳 w
  posDef : (designMatrix w).PosDef
  dotProduct_inv_mulVec_le :
    ∀ x ∈ 𝒳, WithLp.ofLp x ⬝ᵥ (designMatrix w)⁻¹ *ᵥ WithLp.ofLp x ≤ Fintype.card ι

/-- **Kiefer–Wolfowitz theorem** (existence of a `G`-optimal design): if `𝒳` is compact and
spans the space, there is a design distribution `w` on `𝒳` with positive definite design matrix
`A` such that `xᵀ A⁻¹ x ≤ card ι` for all `x ∈ 𝒳`. It is obtained as a `D`-optimal design, that
is a maximizer of the determinant over `designSet 𝒳`. -/
theorem exists_isGOptimalDesign [Nonempty ι] (h𝒳 : IsCompact 𝒳)
    (hspan : Submodule.span ℝ 𝒳 = ⊤) :
    ∃ w, IsGOptimalDesign 𝒳 w := by
  have hne : 𝒳.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    rw [Submodule.span_empty] at hspan
    exact bot_ne_top hspan
  obtain ⟨A, hA, hmax⟩ := exists_isMaxOn_det_designSet h𝒳 hne
  have hApd := posDef_of_isMaxOn_det hspan hA hmax
  have hAunit : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hApd.isUnit
  obtain ⟨w, hw, rfl, -⟩ := exists_isDesign_of_mem_designSet hA
  refine ⟨w, hw, hApd, fun x hx ↦ ?_⟩
  set d := Fintype.card ι
  set g := WithLp.ofLp x ⬝ᵥ (designMatrix w)⁻¹ *ᵥ WithLp.ofLp x
  -- the function `t ↦ det ((1 - t) A + t x xᵀ) / det A` is at most `1` on `(0, 1)`
  have hφ : ∀ t ∈ Set.Ioo (0 : ℝ) 1, (1 - t) ^ d * (1 + t / (1 - t) * g) ≤ 1 := by
    intro t ht
    have hmem : (1 - t) • designMatrix w + t • outerSelf x ∈ designSet 𝒳 :=
      convex_designSet hA (outerSelf_mem_designSet hx) (by linarith [ht.2]) ht.1.le (by ring)
    have h : ((1 - t) • designMatrix w + t • outerSelf x).det ≤ (designMatrix w).det := hmax hmem
    rw [det_smul_add_smul_outerSelf hAunit ht.2.ne x] at h
    have hdet := hApd.det_pos
    rw [mul_right_comm] at h
    exact le_of_mul_le_mul_right (by simpa using h) hdet
  -- its derivative at `0` is `g - d`, and it is at most `1 = φ 0` on the right of `0`
  have hderiv : HasDerivAt (fun t : ℝ ↦ (1 - t) ^ d * (1 + t / (1 - t) * g)) (g - d) 0 := by
    have h1 : HasDerivAt (fun t : ℝ ↦ (1 - t) ^ d) (d * (1 - 0) ^ (d - 1) * (-1)) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_sub 1).pow d
    have h2 : HasDerivAt (fun t : ℝ ↦ 1 + t / (1 - t) * g)
        (0 + (1 * (1 - 0) - 0 * (-1)) / (1 - 0) ^ 2 * g) 0 :=
      (hasDerivAt_const _ _).add
        (((hasDerivAt_id (0 : ℝ)).div ((hasDerivAt_id (0 : ℝ)).const_sub 1) (by simp)).mul_const g)
    exact (h1.mul h2).congr_deriv (by norm_num; ring)
  have h := hderiv.nonpos_of_eventually_le_nhdsGT (by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    simpa using hφ t ht)
  linarith

variable (hw : IsGOptimalDesign 𝒳 w)
include hw

/-- The `G`-value of a `G`-optimal design matrix is `card ι`. -/
lemma IsGOptimalDesign.gValue_eq (h𝒳 : IsCompact 𝒳) :
    gValue 𝒳 (designMatrix w) = Fintype.card ι := by
  have hne : 𝒳.Nonempty :=
    ⟨_, hw.isDesign.mem_of_mem_support hw.isDesign.support_nonempty.choose_spec⟩
  exact le_antisymm (gValue_le hne hw.dotProduct_inv_mulVec_le)
    (hw.isDesign.card_le_gValue h𝒳 ((Matrix.isUnit_iff_isUnit_det _).mp hw.posDef.isUnit))

/-- On the support of a `G`-optimal design, `xᵀ A⁻¹ x = card ι`. -/
lemma IsGOptimalDesign.dotProduct_inv_mulVec_eq_card (hx : x ∈ w.support) :
    WithLp.ofLp x ⬝ᵥ (designMatrix w)⁻¹ *ᵥ WithLp.ofLp x = Fintype.card ι :=
  hw.isDesign.dotProduct_inv_mulVec_eq_card ((Matrix.isUnit_iff_isUnit_det _).mp hw.posDef.isUnit)
    hw.dotProduct_inv_mulVec_le hx

/-- The whitened arms `√(A⁻¹) x`, `x ∈ 𝒳`, of a `G`-optimal design have norm at most
`√(card ι)`. -/
lemma IsGOptimalDesign.norm_sqrt_inv_le (hx : x ∈ 𝒳) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (designMatrix w)⁻¹) x‖ ≤ √(Fintype.card ι) := by
  rw [← Real.sqrt_sq (norm_nonneg _), Matrix.norm_toEuclideanCLM_sqrt_inv_sq hw.posDef]
  exact Real.sqrt_le_sqrt (hw.dotProduct_inv_mulVec_le x hx)

/-- The whitened arms `√(A⁻¹) x` of the support of a `G`-optimal design have norm `√(card ι)`. -/
lemma IsGOptimalDesign.norm_sqrt_inv_eq (hx : x ∈ w.support) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (designMatrix w)⁻¹) x‖ = √(Fintype.card ι) := by
  rw [← Real.sqrt_sq (norm_nonneg _), Matrix.norm_toEuclideanCLM_sqrt_inv_sq hw.posDef,
    hw.dotProduct_inv_mulVec_eq_card hx]

omit hw in
/-- The normalizing matrix `(card ι)^{-1/2} √(A⁻¹)` of a positive definite matrix `A`. For the
design matrix of a `G`-optimal design, it maps `𝒳` into the unit ball and the support of the
design onto unit vectors, and it maps the design matrix to `(card ι)⁻¹ • 1`. -/
noncomputable def normalizeMat (A : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  (√(Fintype.card ι))⁻¹ • CFC.sqrt A⁻¹

omit hw in
lemma toEuclideanCLM_normalizeMat_apply (A : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat A) x =
      (√(Fintype.card ι))⁻¹ • Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt A⁻¹) x := by
  rw [normalizeMat, map_smul]
  rfl

/-- The normalized `G`-optimal design is a design distribution on the normalized action set. -/
lemma IsGOptimalDesign.isDesign_mapDomain_normalizeMat :
    IsDesign (Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) '' 𝒳)
      (Finsupp.mapDomain (Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w))) w) :=
  hw.isDesign.mapDomain _

variable [Nonempty ι]

omit hw in
/-- The normalizing matrix of a positive definite matrix is invertible. -/
lemma isUnit_normalizeMat (hA : A.PosDef) : IsUnit (normalizeMat A) := by
  have hd : 0 < √(Fintype.card ι : ℝ) := Real.sqrt_pos.2 (by positivity)
  rw [Matrix.isUnit_iff_isUnit_det, normalizeMat, Matrix.det_smul]
  exact (isUnit_iff_ne_zero.2 (pow_ne_zero _ (inv_ne_zero hd.ne'))).mul
    ((Matrix.isUnit_iff_isUnit_det _).1 hA.inv.sqrt.isUnit)

/-- The normalized action set of a `G`-optimal design spans the space. -/
lemma IsGOptimalDesign.span_image_normalizeMat_eq_top (hspan : Submodule.span ℝ 𝒳 = ⊤) :
    Submodule.span ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) '' 𝒳) = ⊤ :=
  Matrix.span_image_toEuclideanCLM_eq_top (isUnit_normalizeMat hw.posDef) hspan

/-- The normalized arms `(card ι)^{-1/2} √(A⁻¹) x`, `x ∈ 𝒳`, of a `G`-optimal design have norm
at most `1`. -/
lemma IsGOptimalDesign.norm_normalizeMat_le (hx : x ∈ 𝒳) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) x‖ ≤ 1 := by
  have hd : 0 < √(Fintype.card ι : ℝ) := Real.sqrt_pos.2 (by positivity)
  rw [toEuclideanCLM_normalizeMat_apply, norm_smul, norm_inv, Real.norm_of_nonneg hd.le,
    inv_mul_le_iff₀ hd, mul_one]
  exact hw.norm_sqrt_inv_le hx

/-- The normalized arms `(card ι)^{-1/2} √(A⁻¹) x` of the support of a `G`-optimal design are
unit vectors. -/
lemma IsGOptimalDesign.norm_normalizeMat_eq_one (hx : x ∈ w.support) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)) x‖ = 1 := by
  have hd : 0 < √(Fintype.card ι : ℝ) := Real.sqrt_pos.2 (by positivity)
  rw [toEuclideanCLM_normalizeMat_apply, norm_smul, norm_inv, Real.norm_of_nonneg hd.le,
    hw.norm_sqrt_inv_eq hx, inv_mul_cancel₀ hd.ne']

/-- The design matrix of the normalized `G`-optimal design is `(card ι)⁻¹ • 1`. -/
lemma IsGOptimalDesign.designMatrix_mapDomain_normalizeMat :
    designMatrix (Finsupp.mapDomain (Matrix.toEuclideanCLM (𝕜 := ℝ) (normalizeMat (designMatrix w)))
      w) = (Fintype.card ι : ℝ)⁻¹ • 1 := by
  rw [designMatrix_mapDomain_toEuclideanCLM, normalizeMat, Matrix.transpose_smul,
    Matrix.transpose_sqrt, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    hw.posDef.sqrt_inv_mul_mul_sqrt_inv, ← mul_inv, Real.mul_self_sqrt (by positivity)]

end gOptimal

end COLT83
