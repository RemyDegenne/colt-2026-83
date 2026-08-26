/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Structured action sets

The action sets of Maiti, Xu, Jamieson (2026), as subsets of Euclidean spaces
`EuclideanSpace ℝ ι`:

* `unitBall ι`: the closed unit Euclidean ball;
* `hypercubePM ι = {-1, 1}^ι`, `hypercube01 ι = {0, 1}^ι`;
* `mSet ι m = {x ∈ {0, 1}^ι : ∑ᵢ xᵢ = m}`;
* `multitaskSet d`: for block sizes `d : Fin m → ℕ`, the vectors of `{0, 1}^(Σ j, Fin (d j))` with
  exactly one nonzero coordinate in each block (multi-task multi-armed bandit);
* `blockBallSet k d`: in `ℝ^(Fin k × Fin d)`, the union over the `k` blocks of the unit balls of
  the coordinate subspaces of the blocks.
-/

@[expose] public section

namespace COLT83

variable (ι : Type*) [Fintype ι]

/-- The closed unit Euclidean ball. -/
def unitBall : Set (EuclideanSpace ℝ ι) := Metric.closedBall 0 1

/-- The hypercube `{-1, 1}^ι`. -/
def hypercubePM : Set (EuclideanSpace ℝ ι) := {x | ∀ i, x i = 1 ∨ x i = -1}

/-- The hypercube `{0, 1}^ι`. -/
def hypercube01 : Set (EuclideanSpace ℝ ι) := {x | ∀ i, x i = 0 ∨ x i = 1}

/-- The `m`-sets: vectors of `{0, 1}^ι` with exactly `m` coordinates equal to `1`. -/
def mSet (m : ℕ) : Set (EuclideanSpace ℝ ι) := {x | (∀ i, x i = 0 ∨ x i = 1) ∧ ∑ i, x i = m}

variable {ι}

/-- The multi-task action set with block sizes `d : Fin m → ℕ`: vectors of
`{0, 1}^(Σ j, Fin (d j))` with exactly one coordinate equal to `1` in each block `j`. -/
def multitaskSet {m : ℕ} (d : Fin m → ℕ) : Set (EuclideanSpace ℝ (Σ j, Fin (d j))) :=
  {x | (∀ i, x i = 0 ∨ x i = 1) ∧ ∀ j, ∑ l, x ⟨j, l⟩ = 1}

/-- The block-ball set in `ℝ^(Fin k × Fin d)`: the union over the `k` blocks `i` of the unit balls
`{x : ‖x‖ ≤ 1, x supported on block i}`. -/
def blockBallSet (k d : ℕ) : Set (EuclideanSpace ℝ (Fin k × Fin d)) :=
  {x | ‖x‖ ≤ 1 ∧ ∃ i, ∀ j, j ≠ i → ∀ l, x (j, l) = 0}

end COLT83
