/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A product with the logarithm of a quotient

`Real.mul_log_div`: `a * log (a / b) = a * (log a - log b)` for `b ≠ 0`, with no assumption on
`a` thanks to `log 0 = 0`.
-/

public section

namespace Real

/-- `a * log (a / b) = a * (log a - log b)` for `b ≠ 0`, also when `a = 0` thanks to
`log 0 = 0`. -/
lemma mul_log_div {a b : ℝ} (hb : b ≠ 0) : a * log (a / b) = a * (log a - log b) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [log_div ha hb]

end Real
