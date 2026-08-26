/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.LinearBandit
public import COLT83.MXJ2026.Multitask
public import COLT83.MXJ2026.WidthUpper
public import COLT83.MXJ2026.WidthLower
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Properties of the Gaussian width term (Proposition 4 and Theorem 5)

* `gw_le_card`: `w(𝒳) ≤ d` for every spanning action set `𝒳 ⊆ ℝ^d`;
* `gw_le_sqrt_log_ncard`: `w(𝒳) ≤ √(2 d log |𝒳|)` for a finite spanning action set;
* `sqrt_log_le_gw`: `w(𝒳) ≥ (1/8) √(d log ⌊d/2⌋)` for `d ≥ 4`;
* `width_separation`: a finite set `𝒳` (a multi-task set with `m - 1` blocks of size `2` and one
  block of size `m²`, in dimension `d = m² + 2m - 2`) whose span has dimension `r ∈ [d/2, d]`,
  whose intrinsic Gaussian width term is `≤ 3 √(d log d)`, while `√(d log |𝒳|) ≥ 0.49 d^{3/4}`.

Blueprint: `prop:width_le_d`, `prop:width_finite`, `prop:width_lower_sqrt_dlogd`,
`thm:width_separation`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real

namespace COLT83

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Proposition 4 (i)**: the Gaussian width term of a spanning compact action set in `ℝ^d` is at
most `d`. -/
theorem gw_le_card (𝒳 : Set (EuclideanSpace ℝ ι)) (h𝒳 : IsCompact 𝒳) (hne : 𝒳.Nonempty)
    (hspan : Submodule.span ℝ 𝒳 = ⊤) :
    gw 𝒳 ≤ Fintype.card ι := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [gw_of_isEmpty]
  obtain ⟨R, hR⟩ : ∃ R, ∀ x ∈ 𝒳, ‖x‖ ≤ R := by
    obtain ⟨r, hr⟩ := h𝒳.isBounded.subset_closedBall (0 : EuclideanSpace ℝ ι)
    exact ⟨r, fun x hx ↦ mem_closedBall_zero_iff.1 (hr hx)⟩
  obtain ⟨w, hw⟩ := exists_isGOptimalDesign h𝒳 hspan
  exact (gw_le_gwMat hne hR hw.isDesign.designMatrix_mem_designSet hw.posDef).trans
    (hw.gwMat_le_card subset_rfl hne hR)

/-- **Proposition 4 (ii)**: the Gaussian width term of a finite spanning action set `𝒳 ⊆ ℝ^d` is
at most `√(2 d log |𝒳|)`. -/
theorem gw_le_sqrt_log_ncard (𝒳 : Set (EuclideanSpace ℝ ι)) (hfin : 𝒳.Finite)
    (hne : 𝒳.Nonempty) (hspan : Submodule.span ℝ 𝒳 = ⊤) :
    gw 𝒳 ≤ √(2 * Fintype.card ι * log 𝒳.ncard) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [gw_of_isEmpty]
  obtain ⟨R, hR⟩ : ∃ R, ∀ x ∈ 𝒳, ‖x‖ ≤ R := by
    obtain ⟨r, hr⟩ := hfin.isCompact.isBounded.subset_closedBall (0 : EuclideanSpace ℝ ι)
    exact ⟨r, fun x hx ↦ mem_closedBall_zero_iff.1 (hr hx)⟩
  obtain ⟨w, hw⟩ := exists_isGOptimalDesign hfin.isCompact hspan
  exact (gw_le_gwMat hne hR hw.isDesign.designMatrix_mem_designSet hw.posDef).trans
    (hw.gwMat_le_sqrt_log_ncard subset_rfl hfin hne hR)

/-- **Proposition 4 (iii)**: the Gaussian width term of a spanning compact action set in `ℝ^d`,
`d ≥ 4`, is at least `(1/8) √(d log ⌊d/2⌋)`. -/
theorem sqrt_log_le_gw (𝒳 : Set (EuclideanSpace ℝ ι)) (h𝒳 : IsCompact 𝒳) (hne : 𝒳.Nonempty)
    (hspan : Submodule.span ℝ 𝒳 = ⊤) (hd : 4 ≤ Fintype.card ι) :
    √(Fintype.card ι * log (Fintype.card ι / 2 : ℕ)) / 8 ≤ gw 𝒳 := by
  have : Nonempty ι := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨R, hR⟩ : ∃ R, ∀ x ∈ 𝒳, ‖x‖ ≤ R := by
    obtain ⟨r, hr⟩ := h𝒳.isBounded.subset_closedBall (0 : EuclideanSpace ℝ ι)
    exact ⟨r, fun x hx ↦ mem_closedBall_zero_iff.1 (hr hx)⟩
  refine le_gw (exists_posDef_mem_designSet hspan) fun A hA hA' ↦ ?_
  obtain ⟨w, hw, rfl, -⟩ := exists_isDesign_of_mem_designSet hA
  exact sqrt_log_le_gwMat hw hA' hne hR hd

/-- Block sizes of the multi-task set of Theorem 5: `m - 1` blocks of size `2` and one block of
size `m ^ 2`. -/
def widthSepDims (m : ℕ) : Fin m → ℕ := fun j ↦ if (j : ℕ) + 1 < m then 2 else m ^ 2

/-- **Theorem 5** (Maiti, Xu, Jamieson 2026): for `m ≥ 2`, the multi-task set `𝒳` with `m - 1`
blocks of size `2` and one block of size `m²` lives in dimension `d = m² + 2m - 2`, has
`|𝒳| = 2^{m-1} m²` elements, spans a subspace of dimension `r = m² + m - 1 ∈ [d/2, d]`, and its
intrinsic Gaussian width term satisfies `w_int(𝒳) ≤ 3 √(d log d)`, whereas
`√(d log |𝒳|) ≥ 0.49 d^{3/4}` and `√(r log |𝒳|) ≥ 0.34 d^{3/4}`. -/
theorem width_separation (m : ℕ) (hm : 2 ≤ m) :
    Fintype.card (Σ j, Fin (widthSepDims m j)) = m ^ 2 + 2 * m - 2 ∧
    (multitaskSet (widthSepDims m)).ncard = 2 ^ (m - 1) * m ^ 2 ∧
    Module.finrank ℝ (Submodule.span ℝ (multitaskSet (widthSepDims m))) = m ^ 2 + m - 1 ∧
    ((m ^ 2 + 2 * m - 2 : ℕ) : ℝ) / 2 ≤ (m ^ 2 + m - 1 : ℕ) ∧
    intrinsicGw (multitaskSet (widthSepDims m)) ≤
      3 * √((m ^ 2 + 2 * m - 2 : ℕ) * log (m ^ 2 + 2 * m - 2 : ℕ)) ∧
    0.49 * ((m ^ 2 + 2 * m - 2 : ℕ) : ℝ) ^ (3 / 4 : ℝ) ≤
      √((m ^ 2 + 2 * m - 2 : ℕ) * log (2 ^ (m - 1) * m ^ 2 : ℕ)) ∧
    0.34 * ((m ^ 2 + 2 * m - 2 : ℕ) : ℝ) ^ (3 / 4 : ℝ) ≤
      √((m ^ 2 + m - 1 : ℕ) * log (2 ^ (m - 1) * m ^ 2 : ℕ)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  -- the block sizes
  have hdims : ∀ j : Fin (n + 1), 0 < widthSepDims (n + 1) j := fun j ↦ by
    unfold widthSepDims
    split_ifs <;> positivity
  have hcast : ∀ i : Fin n, widthSepDims (n + 1) i.castSucc = 2 := fun i ↦ by
    simp [widthSepDims, i.is_lt]
  have hlast : widthSepDims (n + 1) (Fin.last n) = (n + 1) ^ 2 := by
    simp [widthSepDims]
  -- the natural-number quantities
  have hD : (n + 1) ^ 2 + 2 * (n + 1) - 2 = n ^ 2 + 4 * n + 1 := by
    have : (n + 1) ^ 2 + 2 * (n + 1) = n ^ 2 + 4 * n + 1 + 2 := by ring
    omega
  have hRk : (n + 1) ^ 2 + (n + 1) - 1 = n ^ 2 + 3 * n + 1 := by
    have : (n + 1) ^ 2 + (n + 1) = n ^ 2 + 3 * n + 1 + 1 := by ring
    omega
  have hcard : Fintype.card (Σ j, Fin (widthSepDims (n + 1) j)) =
      (n + 1) ^ 2 + 2 * (n + 1) - 2 := by
    rw [Fintype.card_sigma, Fin.sum_univ_castSucc, hD]
    simp only [Fintype.card_fin, hcast, hlast, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  have hncard : (multitaskSet (widthSepDims (n + 1))).ncard = 2 ^ (n + 1 - 1) * (n + 1) ^ 2 := by
    rw [ncard_multitaskSet, Fin.prod_univ_castSucc]
    simp only [hcast, hlast, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Nat.add_sub_cancel]
  have hrank : Module.finrank ℝ (Submodule.span ℝ (multitaskSet (widthSepDims (n + 1)))) =
      (n + 1) ^ 2 + (n + 1) - 1 := by
    have h := finrank_span_multitaskSet_add hdims (by omega)
    rw [hcard, hD] at h
    rw [hRk]
    omega
  -- real casts
  set D : ℕ := (n + 1) ^ 2 + 2 * (n + 1) - 2 with hD_def
  set Rk : ℕ := (n + 1) ^ 2 + (n + 1) - 1 with hRk_def
  set N : ℕ := 2 ^ (n + 1 - 1) * (n + 1) ^ 2 with hN_def
  have hDR : (D : ℝ) = (n : ℝ) ^ 2 + 4 * n + 1 := by rw [hD]; push_cast; ring
  have hRkR : (Rk : ℝ) = (n : ℝ) ^ 2 + 3 * n + 1 := by rw [hRk]; push_cast; ring
  have hNR : (N : ℝ) = 2 ^ n * ((n : ℝ) + 1) ^ 2 := by
    rw [hN_def, Nat.add_sub_cancel]; push_cast; ring
  clear_value D Rk N
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hDpos : (0 : ℝ) < D := by rw [hDR]; positivity
  have hM2D : ((n : ℝ) + 1) ^ 2 ≤ D := by rw [hDR]; nlinarith
  have hDM : (D : ℝ) ≤ ((n : ℝ) + 2) ^ 2 := by rw [hDR]; nlinarith
  have hsqrtD : √(D : ℝ) ≤ (n : ℝ) + 2 :=
    Real.sqrt_le_iff.2 ⟨by positivity, hDM⟩
  -- logarithms
  have hlog2 : 0.6931471803 < log 2 := Real.log_two_gt_d9
  have hlogM : log 2 ≤ log ((n : ℝ) + 1) := Real.log_le_log two_pos (by linarith)
  have hL0 : 0 < log ((n : ℝ) + 1) := by linarith
  have hlogN : log (N : ℝ) = n * log 2 + 2 * log ((n : ℝ) + 1) := by
    rw [hNR, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
    push_cast
    ring
  have hlogD : log (((n : ℝ) + 1) ^ 2) ≤ log D :=
    Real.log_le_log (by positivity) hM2D
  -- (iii): `0.24 √D ≤ log N`
  have hkey : 0.2401 * √(D : ℝ) ≤ log N := by
    rw [hlogN]
    have : 0.6931471803 * (n : ℝ) ≤ n * log 2 := by nlinarith
    nlinarith
  -- the intrinsic width bound
  have hwidth : intrinsicGw (multitaskSet (widthSepDims (n + 1))) ≤
      4 * ((n : ℝ) + 1) * √(log ((n : ℝ) + 1)) := by
    refine (intrinsicGw_multitaskSet_le hdims).trans ?_
    rw [Fin.sum_univ_castSucc]
    simp only [hcast, hlast, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    have h1 : √(2 * 2 * log 2) ≤ 2 * √(log ((n : ℝ) + 1)) := by
      rw [show (2 : ℝ) * 2 * log 2 = 2 ^ 2 * log 2 by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by norm_num)]
      gcongr
    have h2 : √(2 * ((n : ℝ) + 1) ^ 2 * log (((n : ℝ) + 1) ^ 2)) =
        2 * ((n : ℝ) + 1) * √(log ((n : ℝ) + 1)) := by
      rw [Real.log_pow, show (2 : ℝ) * ((n : ℝ) + 1) ^ 2 * (((2 : ℕ) : ℝ) * log ((n : ℝ) + 1)) =
        (2 * ((n : ℝ) + 1)) ^ 2 * log ((n : ℝ) + 1) by push_cast; ring,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [h2]
    have h3 : (n : ℝ) * √(2 * 2 * log 2) ≤ n * (2 * √(log ((n : ℝ) + 1))) :=
      mul_le_mul_of_nonneg_left h1 hn0
    nlinarith [Real.sqrt_nonneg (log ((n : ℝ) + 1))]
  have hRHS : 4 * ((n : ℝ) + 1) * √(log ((n : ℝ) + 1)) ≤ 3 * √(D * log D) := by
    have hsq2 : (1.4142 : ℝ) ≤ √2 := by
      rw [Real.le_sqrt (by norm_num) (by norm_num)]
      norm_num
    have hlow : ((n : ℝ) + 1) ^ 2 * (2 * log ((n : ℝ) + 1)) ≤ D * log D := by
      have := Real.log_pow ((n : ℝ) + 1) 2
      push_cast at this
      rw [← this]
      exact mul_le_mul hM2D hlogD (by rw [this]; linarith) hDpos.le
    calc 4 * ((n : ℝ) + 1) * √(log ((n : ℝ) + 1))
        ≤ 3 * (((n : ℝ) + 1) * (√2 * √(log ((n : ℝ) + 1)))) := by
          nlinarith [Real.sqrt_nonneg (log ((n : ℝ) + 1)),
            mul_nonneg hn0 (Real.sqrt_nonneg (log ((n : ℝ) + 1)))]
      _ = 3 * √(((n : ℝ) + 1) ^ 2 * (2 * log ((n : ℝ) + 1))) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
            Real.sqrt_mul (by norm_num)]
      _ ≤ 3 * √(D * log D) := by gcongr
  -- the `3/4` powers
  have h34 : ((D : ℝ) ^ (3 / 4 : ℝ)) ^ 2 = D * √D := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hDpos.le, Real.sqrt_eq_rpow,
      show (3 / 4 : ℝ) * ((2 : ℕ) : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hDpos, Real.rpow_one]
  have hlogN0 : 0 ≤ log (N : ℝ) := by
    rw [hlogN]
    positivity
  have hRk0 : (0 : ℝ) ≤ Rk := by positivity
  refine ⟨hcard, hncard, hrank, ?_, hwidth.trans hRHS, ?_, ?_⟩
  · rw [hDR, hRkR]
    nlinarith
  · rw [Real.le_sqrt (by positivity) (mul_nonneg hDpos.le hlogN0), mul_pow, h34]
    have : (0.49 : ℝ) ^ 2 * (D * √D) = D * (0.2401 * √D) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hkey hDpos.le
  · rw [Real.le_sqrt (by positivity) (mul_nonneg hRk0 hlogN0), mul_pow, h34]
    have hRkD : (D : ℝ) / 2 ≤ Rk := by rw [hDR, hRkR]; nlinarith
    calc (0.34 : ℝ) ^ 2 * (D * √D) = (D / 2) * (0.2312 * √D) := by ring
      _ ≤ Rk * log N :=
          mul_le_mul hRkD (by linarith [Real.sqrt_nonneg (D : ℝ)]) (by positivity) hRk0

end COLT83
