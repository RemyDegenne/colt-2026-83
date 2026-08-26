/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.AlgorithmPrefix

/-!
# Playing an algorithm, then repeating a recommended action

`Algorithm.thenRepeat alg n ρ` is the algorithm which plays `alg` for the first `n + 1` rounds,
then draws an action from the kernel `ρ` applied to the history of these rounds and repeats that
action forever. When `ρ` is the output rule of a fixed-budget identification algorithm `A` with
budget `n + 1` and actions as outputs, this is the *test algorithm* `IdentAlg.testAlg A n`: it
plays `A`, then repeatedly plays its recommendation. It is the sequential composition of `A` with
the "repeat the first action" algorithm used by the adaptive lower bound
(blueprint `lem:test_from_alg`).

## Main results

For an algorithm-environment sequence `(X, Y)` of `alg.thenRepeat n ρ`:
* `IsAlgEnvSeq.isAlgEnvSeqUntil_of_thenRepeat`: it is an algorithm-environment sequence for
  `alg` until time `n`;
* `IsAlgEnvSeq.hasCondDistrib_action_succ_of_thenRepeat`: the action at time `n + 1` has
  conditional law `ρ` given the history of the first `n + 1` rounds;
* `IsAlgEnvSeq.action_add_ae_eq_of_thenRepeat`: `X (n + 1 + s) = X (n + 1)` almost surely.

`IdentAlg.IsPAC.le_measureReal_action_succ_of_testAlg`: the PAC guarantee of `A` applies to the
action at time `n + 1` of the test algorithm.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

universe u v

namespace Learning

variable {𝓐 : Type u} {𝓨 : Type v} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}

namespace Algorithm

variable (alg : Algorithm 𝓐 𝓨) (n : ℕ) (ρ : Kernel (Fin (n + 1) → 𝓐 × 𝓨) 𝓐) [IsMarkovKernel ρ]

/-- The policy at time `t` of `Algorithm.thenRepeat alg n ρ`: the policy of `alg` for `t < n`,
the kernel `ρ` applied to the history of the first `n + 1` rounds for `t = n`, and the
deterministic choice of the action played at time `n + 1` for `t > n`. -/
noncomputable def thenRepeatPolicy (t : ℕ) : Kernel (Iic t → 𝓐 × 𝓨) 𝓐 :=
  if h : n < t then
    Kernel.deterministic (fun x ↦ (x ⟨n + 1, Finset.mem_Iic.2 h⟩).1) (by fun_prop)
  else if ht : t = n then
    ρ.comap (fun x (i : Fin (n + 1)) ↦ x ⟨i, Finset.mem_Iic.2 (by omega)⟩) (by fun_prop)
  else alg.policy t

instance (t : ℕ) : IsMarkovKernel (thenRepeatPolicy alg n ρ t) := by
  unfold thenRepeatPolicy
  split_ifs <;> infer_instance

/-- The algorithm which plays `alg` for the first `n + 1` rounds, then draws an action from `ρ`
applied to the history of these rounds and repeats that action forever. -/
noncomputable def thenRepeat : Algorithm 𝓐 𝓨 where
  policy := thenRepeatPolicy alg n ρ
  p0 := alg.p0

@[simp] lemma thenRepeat_p0 : (alg.thenRepeat n ρ).p0 = alg.p0 := rfl

lemma thenRepeat_policy_of_lt {t : ℕ} (ht : t < n) :
    (alg.thenRepeat n ρ).policy t = alg.policy t := by
  change thenRepeatPolicy alg n ρ t = _
  rw [thenRepeatPolicy, dite_eq_right_of_eq_false (by simpa using (by omega : ¬ n < t)),
    dite_eq_right_of_eq_false (by simpa using (by omega : t ≠ n))]

lemma thenRepeat_policy_self :
    (alg.thenRepeat n ρ).policy n = ρ.comap (toFinHistory n) (measurable_toFinHistory n) := by
  simp only [thenRepeat, thenRepeatPolicy, lt_self_iff_false, ↓reduceDIte]
  rfl

lemma thenRepeat_policy_of_gt {t : ℕ} (ht : n < t) :
    (alg.thenRepeat n ρ).policy t =
      Kernel.deterministic (fun x ↦ (x ⟨n + 1, Finset.mem_Iic.2 ht⟩).1) (by fun_prop) := by
  simp [thenRepeat, thenRepeatPolicy, ht]

/-- `thenRepeat alg n ρ` agrees with `alg` until time `n`. -/
lemma thenRepeat_agreeUntil : (alg.thenRepeat n ρ).AgreeUntil alg n :=
  ⟨rfl, fun _ ht ↦ thenRepeat_policy_of_lt alg n ρ ht⟩

end Algorithm

section run

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {alg : Algorithm 𝓐 𝓨} {env : Environment 𝓐 𝓨} {n : ℕ}
  {ρ : Kernel (Fin (n + 1) → 𝓐 × 𝓨) 𝓐} [IsMarkovKernel ρ]

/-- An algorithm-environment sequence of `alg.thenRepeat n ρ` is an algorithm-environment
sequence for `alg` until time `n`. -/
lemma IsAlgEnvSeq.isAlgEnvSeqUntil_of_thenRepeat
    (h : IsAlgEnvSeq X Y (alg.thenRepeat n ρ) env P) : IsAlgEnvSeqUntil X Y alg env P n :=
  h.isAlgEnvSeqUntil_of_agreeUntil (alg.thenRepeat_agreeUntil n ρ)

/-- Under `alg.thenRepeat n ρ`, the action at time `n + 1` has conditional law `ρ` given the
history of the first `n + 1` rounds. -/
lemma IsAlgEnvSeq.hasCondDistrib_action_succ_of_thenRepeat
    (h : IsAlgEnvSeq X Y (alg.thenRepeat n ρ) env P) :
    HasCondDistrib (X (n + 1)) (finHistory X Y (n + 1)) ρ P := by
  have h1 := h.hasCondDistrib_action n
  rw [Algorithm.thenRepeat_policy_self] at h1
  rw [finHistory_succ_eq_toFinHistory_comp]
  exact h1.comp_right

/-- Under `alg.thenRepeat n ρ`, the action at time `t + 1 > n + 1` is the one at time `n + 1`. -/
lemma IsAlgEnvSeq.action_ae_eq_of_thenRepeat [MeasurableEq 𝓐]
    (h : IsAlgEnvSeq X Y (alg.thenRepeat n ρ) env P) {t : ℕ} (ht : n < t) :
    X (t + 1) =ᵐ[P] X (n + 1) := by
  have h1 := h.hasCondDistrib_action t
  rw [Algorithm.thenRepeat_policy_of_gt alg n ρ ht] at h1
  exact ae_eq_of_hasCondDistrib_deterministic
    (f := fun x : Iic t → 𝓐 × 𝓨 ↦ (x ⟨n + 1, Finset.mem_Iic.2 ht⟩).1) (by fun_prop)
    (h.measurable_history t).aemeasurable (h.measurable_action (t + 1)).aemeasurable h1

/-- Under `alg.thenRepeat n ρ`, the action at time `n + 1 + s` is the one at time `n + 1`. -/
lemma IsAlgEnvSeq.action_add_ae_eq_of_thenRepeat [MeasurableEq 𝓐]
    (h : IsAlgEnvSeq X Y (alg.thenRepeat n ρ) env P) (s : ℕ) :
    X (n + 1 + s) =ᵐ[P] X (n + 1) := by
  cases s with
  | zero => rfl
  | succ s => exact h.action_ae_eq_of_thenRepeat (t := n + 1 + s) (by omega)

lemma IsAlgEnvSeq.ae_forall_action_add_eq_of_thenRepeat [MeasurableEq 𝓐]
    (h : IsAlgEnvSeq X Y (alg.thenRepeat n ρ) env P) :
    ∀ᵐ ω ∂P, ∀ s, X (n + 1 + s) ω = X (n + 1) ω :=
  ae_all_iff.2 fun s ↦ h.action_add_ae_eq_of_thenRepeat s

end run

namespace IdentAlg

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {n : ℕ}

/-- The test algorithm built from an identification algorithm `A` with budget `n + 1` whose
outputs are actions: play `A` for `n + 1` rounds, then repeat its recommendation forever. -/
noncomputable def testAlg (A : IdentAlg 𝓐 𝓨 𝓐) (n : ℕ) [IsMarkovKernel (A.output (n + 1))] :
    Algorithm 𝓐 𝓨 :=
  A.alg.thenRepeat n (A.output (n + 1))

/-- **The PAC guarantee of `A` applies to the recommendation played by the test algorithm.** -/
lemma IsPAC.le_measureReal_action_succ_of_testAlg {A : IdentAlg 𝓐 𝓨 𝓐}
    [IsMarkovKernel (A.output (n + 1))] {Θ : Type*} {env : Θ → Environment 𝓐 𝓨}
    {good : Θ → 𝓐 → Prop} {δ : ℝ} (hpac : A.IsPAC.{max u v} env good δ)
    (hA : A.IsFixedBudget (n + 1)) (θ : Θ) (h : IsAlgEnvSeq X Y (A.testAlg n) (env θ) P)
    (hgood : MeasurableSet {a | good θ a}) :
    1 - δ ≤ P.real {ω | good θ (X (n + 1) ω)} :=
  hpac.le_measureReal_of_isAlgEnvSeqUntil hA θ h.isAlgEnvSeqUntil_of_thenRepeat
    h.hasCondDistrib_action_succ_of_thenRepeat hgood

end IdentAlg

end Learning
