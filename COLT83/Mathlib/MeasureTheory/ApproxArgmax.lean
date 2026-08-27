/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.Mathlib.Analysis.InnerProductSpace.SupportFn
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Measurable approximate argmax selectors

For a compact set `K` in a real inner product space `E` and `γ > 0`, we build a measurable map
`s : E → K` such that `⟪s v, v⟫ ≥ supportFn K v - γ` for every `v`: a measurable
`γ`-approximate argmax of `x ↦ ⟪x, v⟫` on `K`. For a finite set `K` the argmax itself can be
chosen measurably.

The construction is the same in both cases: pick a sequence `q : ℕ → K` (dense in `K`, or
enumerating `K` when it is finite), let `U n` be the (open, resp. closed) set of the `v` for
which `q n` is a good choice, check that the `U n` cover `E`, and send `v` to `q n` for the first
`n` with `v ∈ U n`. The first such index is a measurable function of `v` (`measurable_find`).

## Main results

* `exists_measurable_approx_argmax`: for `K` compact and `γ > 0`, there is a measurable
  `s : E → K` with `supportFn K v - γ ≤ ⟪s v, v⟫` for all `v`.
* `exists_measurable_argmax_of_finite`: for `K` finite, there is a measurable `s : E → K` with
  `⟪s v, v⟫ = supportFn K v` for all `v`.
-/

@[expose] public section

set_option autoImplicit false

open scoped RealInnerProductSpace

/-- Given a sequence `q : ℕ → β` and a family of measurable sets `U n ⊆ α` covering `α`, the
map sending `v` to `q n` for the first `n` with `v ∈ U n` is a measurable map `α → β` whose
value at `v` is `q n` for some `n` with `v ∈ U n`. -/
lemma exists_measurable_of_forall_exists_mem {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (q : ℕ → β) {U : ℕ → Set α} (hU : ∀ n, MeasurableSet (U n))
    (hcover : ∀ v, ∃ n, v ∈ U n) :
    ∃ s : α → β, Measurable s ∧ ∀ v, ∃ n, v ∈ U n ∧ s v = q n := by
  classical
  exact ⟨fun v ↦ q (Nat.find (hcover v)), measurable_from_nat.comp (measurable_find hcover hU),
    fun v ↦ ⟨Nat.find (hcover v), Nat.find_spec (hcover v), rfl⟩⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {K : Set E}

/-- **Measurable approximate argmax.** For a compact set `K` and `γ > 0`, there is a measurable
map `s : E → K` such that `s v` is a `γ`-approximate maximizer of `x ↦ ⟪x, v⟫` on `K` for every
`v`. -/
lemma exists_measurable_approx_argmax (hK : IsCompact K) (hne : K.Nonempty) {γ : ℝ}
    (hγ : 0 < γ) :
    ∃ s : E → K, Measurable s ∧ ∀ v : E, supportFn K v - γ ≤ ⟪(s v : E), v⟫ := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have : Nonempty K := hne.to_subtype
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq K
  have hM : Continuous (supportFn K) := continuous_supportFn hne hR
  -- `U n` is the set of `v` for which `q n` is a `γ`-approximate maximizer.
  have hU : ∀ n, MeasurableSet {v | supportFn K v - γ < ⟪(q n : E), v⟫} := fun n ↦
    (isOpen_lt (hM.sub continuous_const) (continuous_const.inner continuous_id)).measurableSet
  have hcover : ∀ v, ∃ n, v ∈ {v | supportFn K v - γ < ⟪(q n : E), v⟫} := by
    intro v
    obtain ⟨x, hx, hxv⟩ := exists_supportFn_eq_inner hK hne v
    have hpos : 0 < γ / (1 + ‖v‖) := by positivity
    obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 hq ⟨x, hx⟩ _ hpos
    rw [Subtype.dist_eq, dist_eq_norm] at hn
    refine ⟨n, ?_⟩
    change supportFn K v - γ < ⟪(q n : E), v⟫
    rw [hxv]
    have h1 : ⟪x - q n, v⟫ ≤ ‖x - (q n : E)‖ * ‖v‖ := real_inner_le_norm _ _
    have h2 : ‖x - (q n : E)‖ * ‖v‖ < γ :=
      calc ‖x - (q n : E)‖ * ‖v‖ ≤ ‖x - (q n : E)‖ * (1 + ‖v‖) :=
            mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ < γ / (1 + ‖v‖) * (1 + ‖v‖) := mul_lt_mul_of_pos_right hn (by positivity)
        _ = γ := div_mul_cancel₀ _ (by positivity)
    rw [inner_sub_left] at h1
    linarith
  obtain ⟨s, hs, hsv⟩ := exists_measurable_of_forall_exists_mem q hU hcover
  refine ⟨s, hs, fun v ↦ ?_⟩
  obtain ⟨n, hn, hsn⟩ := hsv v
  rw [hsn]
  exact hn.le

omit [SecondCountableTopology E] in
/-- **Measurable argmax on a finite set.** For a finite nonempty set `K`, there is a measurable
map `s : E → K` such that `s v` maximizes `x ↦ ⟪x, v⟫` on `K` for every `v`. -/
lemma exists_measurable_argmax_of_finite (hK : K.Finite) (hne : K.Nonempty) :
    ∃ s : E → K, Measurable s ∧ ∀ v : E, ⟪(s v : E), v⟫ = supportFn K v := by
  obtain ⟨R, hR⟩ := hK.isCompact.isBounded.exists_norm_le
  have : Nonempty K := hne.to_subtype
  have : Finite K := hK.to_subtype
  obtain ⟨q, hq⟩ := exists_surjective_nat K
  have hM : Continuous (supportFn K) := continuous_supportFn hne hR
  -- `U n` is the set of `v` for which `q n` is a maximizer.
  have hU : ∀ n, MeasurableSet {v | ⟪(q n : E), v⟫ = supportFn K v} := fun n ↦
    (isClosed_eq (continuous_const.inner continuous_id) hM).measurableSet
  have hcover : ∀ v, ∃ n, v ∈ {v | ⟪(q n : E), v⟫ = supportFn K v} := by
    intro v
    obtain ⟨x, hx, hxv⟩ := exists_supportFn_eq_inner hK.isCompact hne v
    obtain ⟨n, hn⟩ := hq ⟨x, hx⟩
    exact ⟨n, by simp [hn, hxv]⟩
  obtain ⟨s, hs, hsv⟩ := exists_measurable_of_forall_exists_mem q hU hcover
  refine ⟨s, hs, fun v ↦ ?_⟩
  obtain ⟨n, hn, hsn⟩ := hsv v
  rw [hsn]
  exact hn

end
