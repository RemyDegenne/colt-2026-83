/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Sign of the derivative at a one-sided local extremum

If `f : ℝ → ℝ` is differentiable at `a` and `f t ≤ f a` for all `t` in a right neighborhood of
`a`, then `f' a ≤ 0` (`HasDerivAt.nonpos_of_eventually_le_nhdsGT`); symmetrically for a one-sided
local minimum (`HasDerivAt.nonneg_of_eventually_ge_nhdsGT`). These are the one-dimensional,
one-sided versions of `IsLocalMaxOn.hasFDerivWithinAt_nonpos`, stated directly for the filter
`𝓝[>] a` of right neighborhoods.
-/

@[expose] public section

open Filter Set
open scoped Topology

variable {f : ℝ → ℝ} {a f' : ℝ}

/-- If `f` has derivative `f'` at `a` and `f t ≤ f a` for `t` in a right neighborhood of `a`,
then `f' ≤ 0`. -/
lemma HasDerivAt.nonpos_of_eventually_le_nhdsGT (hf : HasDerivAt f f' a)
    (h : ∀ᶠ t in 𝓝[>] a, f t ≤ f a) : f' ≤ 0 := by
  refine le_of_tendsto hf.tendsto_slope_zero_right ?_
  have h_tendsto : Tendsto (fun t ↦ a + t) (𝓝[>] (0 : ℝ)) (𝓝[>] a) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun t ↦ a + t) (𝓝 (0 : ℝ)) (𝓝 (a + 0)) :=
        (continuous_const.add continuous_id).tendsto 0
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact lt_add_of_pos_right a ht
  filter_upwards [self_mem_nhdsWithin, h_tendsto.eventually h] with t ht hft
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (le_of_lt ht)) (sub_nonpos.2 hft)

/-- If `f` has derivative `f'` at `a` and `f a ≤ f t` for `t` in a right neighborhood of `a`,
then `0 ≤ f'`. -/
lemma HasDerivAt.nonneg_of_eventually_ge_nhdsGT (hf : HasDerivAt f f' a)
    (h : ∀ᶠ t in 𝓝[>] a, f a ≤ f t) : 0 ≤ f' := by
  have := hf.neg.nonpos_of_eventually_le_nhdsGT (by filter_upwards [h] with t ht; simpa)
  linarith
