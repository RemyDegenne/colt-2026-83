/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.Width
public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Topology.Instances.Matrix

/-!
# Basic properties of the design matrices of an action set

For an action set `𝒳 ⊆ EuclideanSpace ℝ ι`, the set of design matrices is
`designSet 𝒳 = conv {x xᵀ : x ∈ 𝒳}`. We prove its basic properties:

* every design matrix is positive semidefinite (`posSemidef_of_mem_designSet`) and has trace at
  most `R ^ 2` when `𝒳` is contained in the ball of radius `R` (`trace_le_of_mem_designSet`);
* `designSet 𝒳` is convex (`convex_designSet`) and compact when `𝒳` is compact
  (`isCompact_designSet`);
* empirical designs `T⁻¹ ∑ₜ xₜ xₜᵀ` are design matrices (`inv_smul_sum_outerSelf_mem_designSet`);
* if `𝒳` spans the space, there is a positive definite design matrix
  (`exists_posDef_mem_designSet`);
* the design set of the image of `𝒳` by a matrix `M` is the image of `designSet 𝒳` by
  `A ↦ M A Mᵀ` (`designSet_image_toEuclideanCLM`), and the image of a spanning set by an
  invertible matrix is spanning (`span_image_toEuclideanCLM_eq_top`).

We also prove along the way that the convex hull of a compact subset of a finite-dimensional
real topological vector space is compact (`isCompact_convexHull`, by Carathéodory's theorem).
-/

@[expose] public section

open Real

open scoped RealInnerProductSpace Matrix

/-- The convex hull of a compact subset of a finite-dimensional real topological vector space is
compact. By Carathéodory's theorem, it is the image of the compact set `stdSimplex × sⁿ` (with
`n = finrank + 1`) by the continuous map `(w, z) ↦ ∑ᵢ wᵢ zᵢ`. -/
lemma isCompact_convexHull {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [FiniteDimensional ℝ E] {s : Set E}
    (hs : IsCompact s) :
    IsCompact (convexHull ℝ s) := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  set n := Module.finrank ℝ E + 1 with hn
  let f : (Fin n → ℝ) × (Fin n → E) → E := fun p ↦ ∑ i, p.1 i • p.2 i
  have hf : Continuous f := by fun_prop
  have hK : IsCompact (stdSimplex ℝ (Fin n) ×ˢ Set.pi Set.univ fun _ : Fin n ↦ s) :=
    (isCompact_stdSimplex _ _).prod (isCompact_univ_pi fun _ ↦ hs)
  suffices convexHull ℝ s = f '' (stdSimplex ℝ (Fin n) ×ˢ Set.pi Set.univ fun _ : Fin n ↦ s) by
    rw [this]
    exact hK.image hf
  refine Set.Subset.antisymm ?_ ?_
  · intro x hx
    obtain ⟨κ, _, z, w, hz, hind, hw, hw1, rfl⟩ := eq_pos_convex_span_of_mem_convexHull hx
    have hcard : Fintype.card κ ≤ Fintype.card (Fin n) :=
      (AffineIndependent.card_le_finrank_succ hind).trans
        (by rw [Fintype.card_fin, hn]; gcongr; exact Submodule.finrank_le _)
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
    let w' : Fin n → ℝ := Function.extend e w 0
    let z' : Fin n → E := Function.extend e z fun _ ↦ x₀
    have hw'e : ∀ i, w' (e i) = w i := fun i ↦ e.injective.extend_apply _ _ i
    have hz'e : ∀ i, z' (e i) = z i := fun i ↦ e.injective.extend_apply _ _ i
    have hw'0 : ∀ j ∉ Set.range e, w' j = 0 := fun j hj ↦ Function.extend_apply' _ _ _ hj
    have hz'0 : ∀ j ∉ Set.range e, z' j = x₀ := fun j hj ↦ Function.extend_apply' _ _ _ hj
    refine ⟨(w', z'), ⟨⟨fun j ↦ ?_, ?_⟩, fun j _ ↦ ?_⟩, ?_⟩
    · change 0 ≤ w' j
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        rw [hw'e]
        exact (hw i).le
      · rw [hw'0 j hj]
    · change ∑ j, w' j = 1
      rw [← hw1]
      exact (Fintype.sum_of_injective e e.injective _ _ hw'0 fun i ↦ (hw'e i).symm).symm
    · change z' j ∈ s
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        rw [hz'e]
        exact hz (Set.mem_range_self i)
      · rw [hz'0 j hj]
        exact hx₀
    · change ∑ j, w' j • z' j = ∑ i, w i • z i
      exact (Fintype.sum_of_injective e e.injective _ _
        (fun j hj ↦ by rw [hw'0 j hj, zero_smul]) fun i ↦ by rw [hw'e, hz'e]).symm
  · rintro _ ⟨⟨w, z⟩, ⟨hw, hz⟩, rfl⟩
    exact (convex_convexHull ℝ s).sum_mem (fun i _ ↦ hw.1 i) hw.2
      fun i _ ↦ subset_convexHull ℝ s (hz i (Set.mem_univ _))

namespace COLT83

variable {ι : Type*} {𝒳 : Set (EuclideanSpace ℝ ι)} {x : EuclideanSpace ℝ ι} {A : Matrix ι ι ℝ}
  {R : ℝ}

/-- The design matrix `x xᵀ` of a point `x ∈ 𝒳` belongs to `designSet 𝒳`. -/
lemma outerSelf_mem_designSet (hx : x ∈ 𝒳) : outerSelf x ∈ designSet 𝒳 :=
  subset_convexHull ℝ _ (Set.mem_image_of_mem _ hx)

/-- `outerSelf` is continuous. -/
lemma continuous_outerSelf : Continuous (outerSelf (ι := ι)) :=
  Continuous.matrix_vecMulVec (PiLp.continuous_ofLp _ _) (PiLp.continuous_ofLp _ _)

/-- The cone of positive semidefinite matrices is convex. -/
lemma convex_posSemidef : Convex ℝ {A : Matrix ι ι ℝ | A.PosSemidef} := by
  intro A hA B hB a b ha hb _
  exact (hA.smul ha).add (hB.smul hb)

/-- The set of design matrices is convex. -/
lemma convex_designSet : Convex ℝ (designSet 𝒳) := convex_convexHull ℝ _

/-- The empirical design `T⁻¹ ∑ₜ xₜ xₜᵀ` of a sequence of `T ≥ 1` actions is a design matrix. -/
lemma inv_smul_sum_outerSelf_mem_designSet {T : ℕ} (hT : 0 < T) {x : Fin T → EuclideanSpace ℝ ι}
    (hx : ∀ t, x t ∈ 𝒳) :
    (T : ℝ)⁻¹ • ∑ t, outerSelf (x t) ∈ designSet 𝒳 := by
  rw [Finset.smul_sum]
  refine convex_designSet.sum_mem (fun _ _ ↦ by positivity) ?_
    fun t _ ↦ outerSelf_mem_designSet (hx t)
  simp [Finset.sum_const, hT.ne']

/-- The uniform average of the design matrices of a nonempty finite subset of `𝒳` is a design
matrix. -/
lemma inv_card_smul_sum_outerSelf_mem_designSet {t : Finset (EuclideanSpace ℝ ι)}
    (hne : t.Nonempty) (ht : ↑t ⊆ 𝒳) :
    (t.card : ℝ)⁻¹ • ∑ v ∈ t, outerSelf v ∈ designSet 𝒳 := by
  rw [Finset.smul_sum]
  refine convex_designSet.sum_mem (fun _ _ ↦ by positivity) ?_
    fun v hv ↦ outerSelf_mem_designSet (ht hv)
  simp [Finset.sum_const, hne.card_pos.ne']

variable [Fintype ι]

omit [Fintype ι] in
/-- The design matrix `x xᵀ` is positive semidefinite. -/
lemma outerSelf_posSemidef [Finite ι] (x : EuclideanSpace ℝ ι) : (outerSelf x).PosSemidef := by
  have := Fintype.ofFinite ι
  simpa [outerSelf] using Matrix.posSemidef_vecMulVec_self_star (WithLp.ofLp x)

/-- The trace of `x xᵀ` is `‖x‖ ^ 2`. -/
lemma trace_outerSelf (x : EuclideanSpace ℝ ι) : (outerSelf x).trace = ‖x‖ ^ 2 := by
  rw [outerSelf, Matrix.trace_vecMulVec, ← real_inner_self_eq_norm_sq,
    EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

omit [Fintype ι] in
/-- Every design matrix is positive semidefinite. -/
lemma posSemidef_of_mem_designSet [Finite ι] (hA : A ∈ designSet 𝒳) : A.PosSemidef :=
  convexHull_min (by rintro _ ⟨x, -, rfl⟩; exact outerSelf_posSemidef x) convex_posSemidef hA

/-- If `𝒳` is contained in the ball of radius `R`, every design matrix has trace at most
`R ^ 2`. -/
lemma trace_le_of_mem_designSet (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) (hA : A ∈ designSet 𝒳) :
    A.trace ≤ R ^ 2 := by
  refine convexHull_min ?_ (convex_halfSpace_le (Matrix.traceLinearMap ι ℝ ℝ).isLinear _) hA
  rintro _ ⟨x, hx, rfl⟩
  simp only [Set.mem_ofPred_eq, Matrix.traceLinearMap_apply, trace_outerSelf]
  exact pow_le_pow_left₀ (norm_nonneg _) (hR x hx) 2

omit [Fintype ι] in
/-- The set of design matrices of a compact action set is compact. -/
lemma isCompact_designSet [Finite ι] (h𝒳 : IsCompact 𝒳) : IsCompact (designSet 𝒳) := by
  have := Fintype.ofFinite ι
  exact isCompact_convexHull (h𝒳.image continuous_outerSelf)

omit [Fintype ι] in
/-- If `𝒳` spans the space, there is a positive definite design matrix: the uniform average of
the `v vᵀ` over a basis `b ⊆ 𝒳`. -/
lemma exists_posDef_mem_designSet [Finite ι] [Nonempty ι] (hspan : Submodule.span ℝ 𝒳 = ⊤) :
    ∃ A ∈ designSet 𝒳, A.PosDef := by
  have := Fintype.ofFinite ι
  obtain ⟨b, hb𝒳, hbspan, hbli⟩ := exists_linearIndependent ℝ 𝒳
  have hbfin : b.Finite := hbli.set_finite_of_isNoetherian
  have hbne : b.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    rw [Submodule.span_empty, hspan] at hbspan
    exact bot_ne_top hbspan
  set t := hbfin.toFinset with ht
  have htne : t.Nonempty := by simpa [ht] using hbne
  have ht𝒳 : ↑t ⊆ 𝒳 := by simpa [ht] using hb𝒳
  refine ⟨_, inv_card_smul_sum_outerSelf_mem_designSet htne ht𝒳, ?_⟩
  refine Matrix.posDef_iff_dotProduct_mulVec.2
    ⟨(posSemidef_of_mem_designSet (inv_card_smul_sum_outerSelf_mem_designSet htne ht𝒳)).1,
    fun y hy ↦ ?_⟩
  have h : star y ⬝ᵥ ((t.card : ℝ)⁻¹ • ∑ v ∈ t, outerSelf v) *ᵥ y =
      (t.card : ℝ)⁻¹ * ∑ v ∈ t, (WithLp.ofLp v ⬝ᵥ y) ^ 2 := by
    rw [star_trivial, Matrix.smul_mulVec, Matrix.sum_mulVec, dotProduct_smul, dotProduct_sum,
      smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [outerSelf, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMulVec, smul_dotProduct, smul_eq_mul,
      dotProduct_comm y, sq]
  rw [h]
  refine mul_pos (by positivity) (Finset.sum_pos' (fun _ _ ↦ sq_nonneg _) ?_)
  by_contra! hcontra
  have hzero : ∀ v ∈ b, ⟪v, WithLp.toLp 2 y⟫ = 0 := fun v hv ↦ by
    have := hcontra v (by simpa [ht] using hv)
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, WithLp.ofLp_toLp, dotProduct_comm]
    exact (pow_eq_zero_iff two_ne_zero).1 (le_antisymm this (sq_nonneg _))
  have horth : Submodule.span ℝ {WithLp.toLp 2 y} ⟂ Submodule.span ℝ b :=
    Submodule.isOrtho_span.2 fun u hu v hv ↦ by
      rw [Set.mem_singleton_iff] at hu
      rw [hu, real_inner_comm]
      exact hzero v hv
  rw [hbspan, hspan, Submodule.isOrtho_top_right, Submodule.span_singleton_eq_bot,
    WithLp.toLp_eq_zero] at horth
  exact hy horth

variable [DecidableEq ι]

/-- `(M x) (M x)ᵀ = M (x xᵀ) Mᵀ`. -/
lemma outerSelf_toEuclideanCLM (M : Matrix ι ι ℝ) (x : EuclideanSpace ℝ ι) :
    outerSelf (Matrix.toEuclideanCLM (𝕜 := ℝ) M x) = M * outerSelf x * Mᵀ := by
  rw [outerSelf, outerSelf, Matrix.ofLp_toEuclideanCLM, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

/-- The image of a spanning set by an invertible linear map is spanning. -/
lemma span_image_toEuclideanCLM_eq_top {M : Matrix ι ι ℝ} (hM : IsUnit M)
    (hspan : Submodule.span ℝ 𝒳 = ⊤) :
    Submodule.span ℝ (Matrix.toEuclideanCLM (𝕜 := ℝ) M '' 𝒳) = ⊤ := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).1 hM
  have h1 : Matrix.toEuclideanCLM (𝕜 := ℝ) M * Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹ = 1 := by
    rw [← map_mul, Matrix.mul_nonsing_inv _ hdet, map_one]
  have hsurj : Function.Surjective (Matrix.toEuclideanCLM (𝕜 := ℝ) M) := fun y ↦
    ⟨Matrix.toEuclideanCLM (𝕜 := ℝ) M⁻¹ y, by
      simpa using congr_fun (congrArg DFunLike.coe h1) y⟩
  rw [← ContinuousLinearMap.coe_coe, Submodule.span_image, hspan, Submodule.map_top,
    LinearMap.range_eq_top]
  exact hsurj

/-- The design set of the image of `𝒳` by the linear map of matrix `M` is the image of
`designSet 𝒳` by `A ↦ M A Mᵀ`. -/
lemma designSet_image_toEuclideanCLM (M : Matrix ι ι ℝ) :
    designSet (Matrix.toEuclideanCLM (𝕜 := ℝ) M '' 𝒳) =
      (fun A ↦ M * A * Mᵀ) '' designSet 𝒳 := by
  let L : Matrix ι ι ℝ →ₗ[ℝ] Matrix ι ι ℝ :=
    (LinearMap.mulRight ℝ Mᵀ).comp (LinearMap.mulLeft ℝ M)
  have hL : (fun A ↦ M * A * Mᵀ) = ⇑L := rfl
  rw [hL, designSet, designSet, L.image_convexHull, Set.image_image, Set.image_image]
  congr 2 with x
  rw [outerSelf_toEuclideanCLM]
  rfl

end COLT83
