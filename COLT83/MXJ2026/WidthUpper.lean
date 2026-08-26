/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.MXJ2026.OptimalDesign
public import COLT83.MXJ2026.Width
public import COLT83.Mathlib.Probability.SubgaussianMax

/-!
# Upper bounds on the width for a `G`-optimal design matrix, regionalized width

Let `w` be a `G`-optimal design on the action set `𝒳 ⊆ ℝ^d` (Kiefer–Wolfowitz) and `A_G` its
design matrix. The whitened arms `A_G^{-1/2} x`, `x ∈ 𝒳`, have norm at most `√d`, hence:

* `IsGOptimalDesign.gwMat_le_card`: `gwMat K A_G ≤ d` for every nonempty `K ⊆ 𝒳`
  (Cauchy–Schwarz and `E‖g‖ ≤ √d`);
* `IsGOptimalDesign.gwMat_le_sqrt_log_ncard`: `gwMat K A_G ≤ √(2 d log |K|)` for every finite
  nonempty `K ⊆ 𝒳` (expected maximum of `|K|` Gaussian variables of variance at most `d`).

The **regionalized width** `regionalizedGw A 𝓡 = max_i gwMat (𝓡 i) A` of a family of regions
`𝓡 i` (in the paper, a partition of `𝒳`) is introduced, with its basic properties and the bound
`regionalizedGw A_G 𝓡 ≤ √(2 d log p)` when every region has at most `p` elements
(`IsGOptimalDesign.regionalizedGw_le_sqrt_log`).

Blueprint: `prop:width_le_d`, `prop:width_finite`, `def:regionalized_width`,
`prop:width_partition`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped MatrixOrder

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒳 K : Set (EuclideanSpace ℝ ι)} {R : ℝ}
  {w : EuclideanSpace ℝ ι →₀ ℝ}

section gOptimal

variable (hw : IsGOptimalDesign 𝒳 w)
include hw

/-- The width of a subset `K` of `𝒳` for the `G`-optimal design matrix is at most `card ι`. -/
lemma IsGOptimalDesign.gwMat_le_card (hsub : K ⊆ 𝒳) (hne : K.Nonempty)
    (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) :
    gwMat K (designMatrix w) ≤ Fintype.card ι := by
  refine (gwMat_le_mul_sqrt_card hne (fun x hx ↦ hR x (hsub hx)) _
    fun x hx ↦ hw.norm_sqrt_inv_le (hsub hx)).trans ?_
  rw [Real.mul_self_sqrt (by positivity)]

/-- The width of a finite subset `K` of `𝒳` for the `G`-optimal design matrix is at most
`√(2 card ι log |K|)`. -/
lemma IsGOptimalDesign.gwMat_le_sqrt_log_ncard (hsub : K ⊆ 𝒳) (hfin : K.Finite)
    (hne : K.Nonempty) (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) :
    gwMat K (designMatrix w) ≤ √(2 * Fintype.card ι * log K.ncard) := by
  rw [gwMat_eq_gaussianWidth_stdGaussian hne (fun x hx ↦ hR x (hsub hx)) _]
  have hLn : ∀ x ∈ K, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (designMatrix w)⁻¹) x‖ ≤
      √(Fintype.card ι) := fun x hx ↦ hw.norm_sqrt_inv_le (hsub hx)
  generalize Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (designMatrix w)⁻¹) = L at hLn ⊢
  have h := gaussianWidth_stdGaussian_le_of_finite (hfin.image L) (hne.image L)
    (σ := √(Fintype.card ι)) (by
      rintro _ ⟨x, hx, rfl⟩
      exact hLn x hx)
  refine h.trans ?_
  have hcard : (0 : ℝ) < (L '' K).ncard := by
    exact_mod_cast (Set.ncard_pos (hfin.image L)).2 (hne.image L)
  have hle : ((L '' K).ncard : ℝ) ≤ K.ncard := by exact_mod_cast Set.ncard_image_le hfin
  calc √(Fintype.card ι) * √(2 * log (L '' K).ncard)
      = √(Fintype.card ι * (2 * log (L '' K).ncard)) := (Real.sqrt_mul (by positivity) _).symm
    _ ≤ √(2 * Fintype.card ι * log K.ncard) := by
      refine Real.sqrt_le_sqrt ?_
      rw [show (2 : ℝ) * Fintype.card ι * log K.ncard = Fintype.card ι * (2 * log K.ncard)
        by ring]
      gcongr

end gOptimal

section regionalized

variable {κ : Type*} [Finite κ] [Nonempty κ] {𝓡 : κ → Set (EuclideanSpace ℝ ι)}
  {A : Matrix ι ι ℝ}

/-- The regionalized Gaussian width of a family of regions `𝓡 i` (in the paper, a partition of
the action set) for the matrix `A`: the maximum over the regions of the width `gwMat (𝓡 i) A`. -/
noncomputable def regionalizedGw (A : Matrix ι ι ℝ) (𝓡 : κ → Set (EuclideanSpace ℝ ι)) : ℝ :=
  ⨆ i, gwMat (𝓡 i) A

omit [Nonempty κ] in
lemma gwMat_le_regionalizedGw (A : Matrix ι ι ℝ) (𝓡 : κ → Set (EuclideanSpace ℝ ι)) (i : κ) :
    gwMat (𝓡 i) A ≤ regionalizedGw A 𝓡 :=
  le_ciSup (Finite.bddAbove_range fun i ↦ gwMat (𝓡 i) A) i

omit [Finite κ] in
lemma regionalizedGw_le {c : ℝ} (h : ∀ i, gwMat (𝓡 i) A ≤ c) : regionalizedGw A 𝓡 ≤ c :=
  ciSup_le h

lemma regionalizedGw_nonneg (hne : ∀ i, (𝓡 i).Nonempty) (hR : ∀ i, ∀ x ∈ 𝓡 i, ‖x‖ ≤ R)
    (A : Matrix ι ι ℝ) :
    0 ≤ regionalizedGw A 𝓡 := by
  obtain ⟨i⟩ := ‹Nonempty κ›
  exact (gwMat_nonneg (hne i) (hR i) A).trans (gwMat_le_regionalizedGw A 𝓡 i)

omit [Finite κ] in
/-- The regionalized width of regions contained in `𝒳` is at most the width of `𝒳`. -/
lemma regionalizedGw_le_gwMat (hsub : ∀ i, 𝓡 i ⊆ 𝒳) (hne : ∀ i, (𝓡 i).Nonempty)
    (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) (A : Matrix ι ι ℝ) :
    regionalizedGw A 𝓡 ≤ gwMat 𝒳 A :=
  regionalizedGw_le fun i ↦ gwMat_mono (hne i) hR (hsub i) A

omit [Finite κ] in
/-- **Regionalized width of a finite set** for the `G`-optimal design matrix: if every region
is a finite nonempty subset of `𝒳` with at most `p` elements, then the regionalized width is at
most `√(2 card ι log p)`. -/
lemma IsGOptimalDesign.regionalizedGw_le_sqrt_log (hw : IsGOptimalDesign 𝒳 w)
    (hsub : ∀ i, 𝓡 i ⊆ 𝒳) (hfin : ∀ i, (𝓡 i).Finite) (hne : ∀ i, (𝓡 i).Nonempty) {p : ℕ}
    (hp : ∀ i, (𝓡 i).ncard ≤ p) (hR : ∀ x ∈ 𝒳, ‖x‖ ≤ R) :
    regionalizedGw (designMatrix w) 𝓡 ≤ √(2 * Fintype.card ι * log p) := by
  refine regionalizedGw_le fun i ↦
    (hw.gwMat_le_sqrt_log_ncard (hsub i) (hfin i) (hne i) hR).trans (Real.sqrt_le_sqrt ?_)
  have hcard : (0 : ℝ) < (𝓡 i).ncard := by exact_mod_cast (Set.ncard_pos (hfin i)).2 (hne i)
  gcongr
  exact hp i

end regionalized

end COLT83
