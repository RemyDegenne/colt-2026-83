/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import COLT83.LeanMachineLearning.FixedDesignRun
public import COLT83.LeanMachineLearning.FixedBudget

/-!
# Phased deterministic algorithms

A *phased algorithm* (`PhasedAlg 𝓐 𝓨 S`) runs in phases of deterministic lengths
`len 0, len 1, …` and keeps a state `s : S`. During phase `ℓ` it plays the fixed design
`act ℓ s : Fin (len ℓ) → 𝓐` determined by the state at the start of the phase, regardless of the
observations of the phase, and at the end of the phase it updates the state to `upd ℓ s y`, where
`y : Fin (len ℓ) → 𝓨` are the observations of the phase. Elimination algorithms (Median
Elimination), explore-then-commit strategies and the region algorithm of the log-gains theorem
are of this form.

The state at the start of phase `ℓ` is a function `PhasedAlg.state ℓ` of the observation
sequence which only depends on the observations before the phase (`PhasedAlg.state_congr`), and
the phased algorithm is the deterministic LML algorithm `PhasedAlg.toAlgorithm` which plays
`act ℓ (state ℓ y) j` at time `start ℓ + j`. With a budget of `L` phases and a measurable output
function of the final state, it is the fixed-budget identification algorithm
`PhasedAlg.toIdentAlg`.

## Analysis in a linear Gaussian bandit

The observations of phase `ℓ` are `⟪act ℓ s j, θ⟫ + η j` where the noise vector `η` of the phase
is i.i.d. `N(0, 1)` and independent of the past, in particular of the state `s` at the start of
the phase (`PhasedAlg.hasCondDistrib_phaseNoise`). Consequently a per-phase guarantee "if the
state at the start of phase `ℓ` is good then, with probability at least `1 - δ ℓ` over the noise
of the phase, the state at the end of the phase is good" gives
`P(state L good) ≥ 1 - ∑_{ℓ < L} δ ℓ` (`PhasedAlg.one_sub_sum_le_measureReal_stateProc_mem`) by
induction over the phases, and a PAC guarantee for the identification algorithm
(`PhasedAlg.isPAC_toIdentAlg`). This replaces the sequential composition of algorithms of the
blueprint (`lem:composition`) for this class of algorithms.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open scoped RealInnerProductSpace

namespace Learning

variable {𝓐 𝓨 S : Type*} {m𝓐 : MeasurableSpace 𝓐} {m𝓨 : MeasurableSpace 𝓨}
  {mS : MeasurableSpace S}

/-- A phased deterministic algorithm with actions in `𝓐`, observations in `𝓨` and states in `S`:
phase `ℓ` has length `len ℓ ≥ 1`, plays the design `act ℓ s` given by the state `s` at the start of
the phase and updates the state to `upd ℓ s y` from the observations `y` of the phase. -/
structure PhasedAlg (𝓐 𝓨 S : Type*) [MeasurableSpace 𝓐] [MeasurableSpace 𝓨]
    [MeasurableSpace S] where
  /-- The length of phase `ℓ`. -/
  len : ℕ → ℕ
  /-- Every phase has at least one round. -/
  len_pos : ∀ ℓ, 0 < len ℓ
  /-- The initial state. -/
  init : S
  /-- The design played during phase `ℓ` in state `s`. -/
  act : (ℓ : ℕ) → S → Fin (len ℓ) → 𝓐
  /-- The design is a measurable function of the state. -/
  measurable_act : ∀ ℓ j, Measurable fun s ↦ act ℓ s j
  /-- The state update at the end of phase `ℓ`, from the state and the observations of the phase. -/
  upd : (ℓ : ℕ) → S → (Fin (len ℓ) → 𝓨) → S
  /-- The state update is measurable. -/
  measurable_upd : ∀ ℓ, Measurable (Function.uncurry (upd ℓ))

/-- The observation sequence read from a history up to time `n`, extended beyond `n` by the
observation at time `n`. -/
def extendObs (n : ℕ) (h : Iic n → 𝓐 × 𝓨) : ℕ → 𝓨 :=
  fun t ↦ (h ⟨min t n, Finset.mem_Iic.2 (min_le_right t n)⟩).2

lemma measurable_extendObs (n : ℕ) : Measurable (extendObs (𝓐 := 𝓐) (𝓨 := 𝓨) n) :=
  measurable_pi_lambda _ fun _ ↦ (measurable_pi_apply _).snd

omit m𝓐 m𝓨 in
lemma extendObs_history {Ω : Type*} (X : ℕ → Ω → 𝓐) (Y : ℕ → Ω → 𝓨) (n : ℕ) (ω : Ω) {t : ℕ}
    (ht : t ≤ n) : extendObs n (history X Y n ω) t = Y t ω := by
  simp [extendObs, history, min_eq_left ht]

namespace PhasedAlg

variable (A : PhasedAlg 𝓐 𝓨 S)

section timing

/-- The start time of phase `ℓ`: `∑ k < ℓ, len k`. -/
def start (ℓ : ℕ) : ℕ := ∑ k ∈ range ℓ, A.len k

@[simp] lemma start_zero : A.start 0 = 0 := by simp [start]

lemma start_succ (ℓ : ℕ) : A.start (ℓ + 1) = A.start ℓ + A.len ℓ := sum_range_succ _ _

lemma start_lt_start_succ (ℓ : ℕ) : A.start ℓ < A.start (ℓ + 1) := by
  rw [start_succ]
  exact Nat.lt_add_of_pos_right (A.len_pos ℓ)

lemma start_strictMono : StrictMono A.start := strictMono_nat_of_lt_succ A.start_lt_start_succ

lemma start_mono : Monotone A.start := A.start_strictMono.monotone

lemma id_le_start (ℓ : ℕ) : ℓ ≤ A.start ℓ := A.start_strictMono.id_le ℓ

lemma start_pos_iff {ℓ : ℕ} : 0 < A.start ℓ ↔ 0 < ℓ := by
  rw [← A.start_zero]
  exact A.start_strictMono.lt_iff_lt

/-- The phase containing the time `t`. -/
def phaseOf (t : ℕ) : ℕ := Nat.findGreatest (fun ℓ ↦ A.start ℓ ≤ t) t

lemma start_phaseOf_le (t : ℕ) : A.start (A.phaseOf t) ≤ t :=
  Nat.findGreatest_spec (P := fun ℓ ↦ A.start ℓ ≤ t) (Nat.zero_le t) (by simp)

lemma lt_start_phaseOf_succ (t : ℕ) : t < A.start (A.phaseOf t + 1) := by
  by_contra! hcon
  have h1 : A.phaseOf t + 1 ≤ t := (A.id_le_start _).trans hcon
  have := Nat.le_findGreatest (P := fun ℓ ↦ A.start ℓ ≤ t) h1 hcon
  change A.phaseOf t + 1 ≤ A.phaseOf t at this
  omega

lemma phaseOf_eq_of_le_of_lt {t ℓ : ℕ} (h1 : A.start ℓ ≤ t) (h2 : t < A.start (ℓ + 1)) :
    A.phaseOf t = ℓ := by
  refine le_antisymm ?_ ?_
  · by_contra! h
    have h3 : A.start (ℓ + 1) ≤ A.start (A.phaseOf t) := A.start_mono h
    have := A.start_phaseOf_le t
    omega
  · by_contra! h
    have h3 : A.start (A.phaseOf t + 1) ≤ A.start ℓ := A.start_mono h
    have := A.lt_start_phaseOf_succ t
    omega

lemma phaseOf_start_add {ℓ j : ℕ} (hj : j < A.len ℓ) : A.phaseOf (A.start ℓ + j) = ℓ :=
  A.phaseOf_eq_of_le_of_lt (Nat.le_add_right _ _) (by rw [start_succ]; omega)

lemma sub_start_phaseOf_lt (t : ℕ) : t - A.start (A.phaseOf t) < A.len (A.phaseOf t) := by
  have h1 := A.lt_start_phaseOf_succ t
  rw [start_succ] at h1
  have h2 := A.start_phaseOf_le t
  omega

end timing

section state

/-- The action of phase `ℓ` in state `s` at the offset `j` (clipped to the phase). -/
def actAt (ℓ : ℕ) (s : S) (j : ℕ) : 𝓐 :=
  if h : j < A.len ℓ then A.act ℓ s ⟨j, h⟩ else A.act ℓ s ⟨0, A.len_pos ℓ⟩

lemma actAt_of_lt {ℓ j : ℕ} (hj : j < A.len ℓ) (s : S) : A.actAt ℓ s j = A.act ℓ s ⟨j, hj⟩ := by
  simp [actAt, hj]

lemma measurable_actAt (ℓ j : ℕ) : Measurable fun s ↦ A.actAt ℓ s j := by
  unfold actAt
  split_ifs
  · exact A.measurable_act ℓ _
  · exact A.measurable_act ℓ _

/-- The observations of phase `ℓ` in the observation sequence `y`. -/
def phaseObs (ℓ : ℕ) (y : ℕ → 𝓨) : Fin (A.len ℓ) → 𝓨 := fun j ↦ y (A.start ℓ + j)

lemma measurable_phaseObs (ℓ : ℕ) : Measurable (A.phaseObs ℓ) :=
  measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _

/-- The state at the start of phase `ℓ`, as a function of the observation sequence. -/
def state : ℕ → (ℕ → 𝓨) → S
  | 0, _ => A.init
  | ℓ + 1, y => A.upd ℓ (state ℓ y) (A.phaseObs ℓ y)

@[simp] lemma state_zero (y : ℕ → 𝓨) : A.state 0 y = A.init := rfl

lemma state_succ (ℓ : ℕ) (y : ℕ → 𝓨) :
    A.state (ℓ + 1) y = A.upd ℓ (A.state ℓ y) (A.phaseObs ℓ y) := rfl

lemma measurable_state (ℓ : ℕ) : Measurable (A.state ℓ) := by
  induction ℓ with
  | zero => exact measurable_const
  | succ ℓ ih =>
    have : A.state (ℓ + 1) =
        Function.uncurry (A.upd ℓ) ∘ fun y ↦ (A.state ℓ y, A.phaseObs ℓ y) := rfl
    rw [this]
    exact (A.measurable_upd ℓ).comp (ih.prodMk (A.measurable_phaseObs ℓ))

/-- The state at the start of phase `ℓ` only depends on the observations before the phase. -/
lemma state_congr {ℓ : ℕ} {y y' : ℕ → 𝓨} (h : ∀ t < A.start ℓ, y t = y' t) :
    A.state ℓ y = A.state ℓ y' := by
  induction ℓ with
  | zero => rfl
  | succ ℓ ih =>
    rw [state_succ, state_succ, ih fun t ht ↦ h t (ht.trans (A.start_lt_start_succ ℓ))]
    congr 1
    funext j
    exact h _ (by rw [start_succ]; omega)

/-- The action at time `t` for the observation sequence `y`. -/
def actionAt (t : ℕ) (y : ℕ → 𝓨) : 𝓐 :=
  A.actAt (A.phaseOf t) (A.state (A.phaseOf t) y) (t - A.start (A.phaseOf t))

lemma actionAt_start_add {ℓ : ℕ} (j : Fin (A.len ℓ)) (y : ℕ → 𝓨) :
    A.actionAt (A.start ℓ + j) y = A.act ℓ (A.state ℓ y) j := by
  rw [actionAt, A.phaseOf_start_add j.2, Nat.add_sub_cancel_left, A.actAt_of_lt j.2]

/-- The action at time `t` only depends on the observations before time `t`. -/
lemma actionAt_congr {t : ℕ} {y y' : ℕ → 𝓨} (h : ∀ s < t, y s = y' s) :
    A.actionAt t y = A.actionAt t y' := by
  unfold actionAt
  rw [A.state_congr fun s hs ↦ h s (hs.trans_le (A.start_phaseOf_le t))]

lemma measurable_actionAt (t : ℕ) : Measurable (A.actionAt t) :=
  (A.measurable_actAt _ _).comp (A.measurable_state _)

/-- The phased algorithm as a deterministic LML algorithm: at time `t` in phase `ℓ`, it plays the
action `act ℓ s j` where `s` is the state computed from the observations before the phase and
`j = t - start ℓ`. -/
noncomputable def toAlgorithm : Algorithm 𝓐 𝓨 :=
  detAlgorithm (fun n h ↦ A.actionAt (n + 1) (extendObs n h))
    (fun n ↦ (A.measurable_actionAt (n + 1)).comp (measurable_extendObs n))
    (A.act 0 A.init ⟨0, A.len_pos 0⟩)

/-- The state at the start of phase `ℓ` as a function of the history of the first `start ℓ`
rounds. -/
def stateOfFinHistory (ℓ : ℕ) (hist : Fin (A.start ℓ) → 𝓐 × 𝓨) : S :=
  if hℓ : 0 < A.start ℓ then
    A.state ℓ fun t ↦ (hist ⟨min t (A.start ℓ - 1), by omega⟩).2
  else A.init

lemma measurable_stateOfFinHistory (ℓ : ℕ) : Measurable (A.stateOfFinHistory ℓ) := by
  unfold stateOfFinHistory
  split_ifs
  · exact (A.measurable_state ℓ).comp
      (measurable_pi_lambda _ fun _ ↦ (measurable_pi_apply _).snd)
  · exact measurable_const

end state

section cons

variable {B : PhasedAlg 𝓐 𝓨 S} {n : ℕ} {hn : 0 < n} {d : Fin n → 𝓐} {f : (Fin n → 𝓨) → S}
  {hf : Measurable f}

/-- Prepend to `B` a first phase of length `n` playing the fixed design `d`, whose observations
`y` set the state to `f y`; the initial state of `B` is discarded. -/
def cons (B : PhasedAlg 𝓐 𝓨 S) (n : ℕ) (hn : 0 < n) (d : Fin n → 𝓐) (f : (Fin n → 𝓨) → S)
    (hf : Measurable f) : PhasedAlg 𝓐 𝓨 S where
  len
    | 0 => n
    | ℓ + 1 => B.len ℓ
  len_pos
    | 0 => hn
    | ℓ + 1 => B.len_pos ℓ
  init := B.init
  act
    | 0 => fun _ j ↦ d j
    | ℓ + 1 => B.act ℓ
  measurable_act
    | 0 => fun _ ↦ measurable_const
    | ℓ + 1 => B.measurable_act ℓ
  upd
    | 0 => fun _ y ↦ f y
    | ℓ + 1 => B.upd ℓ
  measurable_upd
    | 0 => hf.comp measurable_snd
    | ℓ + 1 => B.measurable_upd ℓ

@[simp] lemma cons_len_zero : (B.cons n hn d f hf).len 0 = n := rfl

@[simp] lemma cons_len_succ (ℓ : ℕ) : (B.cons n hn d f hf).len (ℓ + 1) = B.len ℓ := rfl

@[simp] lemma cons_init : (B.cons n hn d f hf).init = B.init := rfl

lemma cons_act_zero (s : S) (j : Fin n) : (B.cons n hn d f hf).act 0 s j = d j := rfl

lemma cons_act_succ (ℓ : ℕ) (s : S) (j : Fin (B.len ℓ)) :
    (B.cons n hn d f hf).act (ℓ + 1) s j = B.act ℓ s j := rfl

lemma cons_upd_zero (s : S) (y : Fin n → 𝓨) : (B.cons n hn d f hf).upd 0 s y = f y := rfl

lemma cons_upd_succ (ℓ : ℕ) (s : S) (y : Fin (B.len ℓ) → 𝓨) :
    (B.cons n hn d f hf).upd (ℓ + 1) s y = B.upd ℓ s y := rfl

lemma cons_start_succ (ℓ : ℕ) : (B.cons n hn d f hf).start (ℓ + 1) = n + B.start ℓ := by
  simp only [start, sum_range_succ', cons_len_succ, cons_len_zero, add_comm]

end cons

section run

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {env : Environment 𝓐 𝓨}

/-- The state process of `A` along the observation process `Y`: the state at the start of
phase `ℓ`. -/
def stateProc (Y : ℕ → Ω → 𝓨) (ℓ : ℕ) (ω : Ω) : S := A.state ℓ fun t ↦ Y t ω

@[simp] lemma stateProc_zero (Y : ℕ → Ω → 𝓨) (ω : Ω) : A.stateProc Y 0 ω = A.init := rfl

lemma measurable_stateProc (hY : ∀ t, Measurable (Y t)) (ℓ : ℕ) :
    Measurable (A.stateProc Y ℓ) :=
  (A.measurable_state ℓ).comp (measurable_pi_lambda _ hY)

lemma stateOfFinHistory_finHistory (ℓ : ℕ) (ω : Ω) :
    A.stateOfFinHistory ℓ (finHistory X Y (A.start ℓ) ω) = A.stateProc Y ℓ ω := by
  unfold stateOfFinHistory stateProc
  split_ifs with hℓ
  · exact A.state_congr fun t ht ↦ by
      simp [finHistory, min_eq_left (by omega : t ≤ A.start ℓ - 1)]
  · obtain rfl : ℓ = 0 := by
      by_contra hne
      exact hℓ (A.start_pos_iff.2 (Nat.pos_of_ne_zero hne))
    rfl

variable [MeasurableEq 𝓐] (h : IsAlgEnvSeq X Y A.toAlgorithm env P)
include h

/-- Along a run of the phased algorithm, the actions are given by `actionAt` applied to the
observation process. -/
lemma ae_action_eq : ∀ᵐ ω ∂P, ∀ t, X t ω = A.actionAt t fun s ↦ Y s ω := by
  have h' : IsAlgEnvSeq X Y (detAlgorithm (fun n h ↦ A.actionAt (n + 1) (extendObs n h))
      (fun n ↦ (A.measurable_actionAt (n + 1)).comp (measurable_extendObs n))
      (A.act 0 A.init ⟨0, A.len_pos 0⟩)) env P := h
  filter_upwards [h'.action_detAlgorithm_ae_all_eq] with ω hω t
  cases t with
  | zero =>
    rw [hω.1]
    have := A.actionAt_start_add (ℓ := 0) ⟨0, A.len_pos 0⟩ fun s ↦ Y s ω
    simpa using this.symm
  | succ t =>
    rw [hω.2 t]
    exact A.actionAt_congr fun s hs ↦ extendObs_history X Y t ω (by omega)

/-- Along a run of the phased algorithm, the action at time `start ℓ + j` is `act ℓ s j` where
`s` is the state at the start of phase `ℓ`. -/
lemma ae_action_start_add_eq :
    ∀ᵐ ω ∂P, ∀ ℓ (j : Fin (A.len ℓ)), X (A.start ℓ + j) ω = A.act ℓ (A.stateProc Y ℓ ω) j := by
  filter_upwards [A.ae_action_eq h] with ω hω ℓ j
  rw [hω, A.actionAt_start_add]
  rfl

end run

section identAlg

variable {𝓞 : Type*} {m𝓞 : MeasurableSpace 𝓞} {L : ℕ} {out : S → 𝓞} {hout : Measurable out}

/-- The fixed-budget identification algorithm which runs `A` for `L` phases (budget `start L`)
and outputs `out s` where `s` is the state at the end of the last phase. -/
noncomputable def toIdentAlg (L : ℕ) (out : S → 𝓞) (hout : Measurable out) : IdentAlg 𝓐 𝓨 𝓞 :=
  IdentAlg.fixedBudget A.toAlgorithm (A.start L)
    (Kernel.deterministic (fun hist ↦ out (A.stateOfFinHistory L hist))
      (hout.comp (A.measurable_stateOfFinHistory L)))

lemma isFixedBudget_toIdentAlg : (A.toIdentAlg L out hout).IsFixedBudget (A.start L) :=
  IdentAlg.isFixedBudget_fixedBudget _ _ _

lemma alg_toIdentAlg : (A.toIdentAlg L out hout).alg = A.toAlgorithm := rfl

lemma output_toIdentAlg :
    (A.toIdentAlg L out hout).output (A.start L) =
      Kernel.deterministic (fun hist ↦ out (A.stateOfFinHistory L hist))
        (hout.comp (A.measurable_stateOfFinHistory L)) :=
  IdentAlg.output_fixedBudget _ _ _

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {env : Environment 𝓐 𝓨} {o : Ω → 𝓞}

/-- Along a run of the identification algorithm, the output is `out` of the state at the end of
the last phase. -/
lemma output_ae_eq_of_isRun [MeasurableEq 𝓞]
    (hrun : (A.toIdentAlg L out hout).IsRun env X Y o P) :
    o =ᵐ[P] fun ω ↦ out (A.stateProc Y L ω) := by
  filter_upwards [hrun.output_ae_eq_of_output_eq_deterministic A.isFixedBudget_toIdentAlg _
    A.output_toIdentAlg] with ω hω
  rw [hω, A.stateOfFinHistory_finHistory]

end identAlg

end PhasedAlg

end Learning

namespace Learning.PhasedAlg

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {𝒳 : Set E} {θ : E} {S : Type*} {mS : MeasurableSpace S}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {X : ℕ → Ω → 𝒳} {Y : ℕ → Ω → ℝ} (A : PhasedAlg 𝒳 ℝ S)

/-- The noise of phase `ℓ` of a run in a linear Gaussian bandit. -/
noncomputable def phaseNoise (θ : E) (X : ℕ → Ω → 𝒳) (Y : ℕ → Ω → ℝ) (ℓ : ℕ) (ω : Ω) :
    Fin (A.len ℓ) → ℝ :=
  fun j ↦ LinearBandit.noise θ X Y (A.start ℓ + j) ω

/-- The state at the end of phase `ℓ` started in state `s` with noise `η`, in the linear Gaussian
bandit with reward vector `θ`: `upd ℓ s (⟪act ℓ s j, θ⟫ + η j)_j`. -/
def nextState (θ : E) (ℓ : ℕ) (s : S) (η : Fin (A.len ℓ) → ℝ) : S :=
  A.upd ℓ s fun j ↦ ⟪(A.act ℓ s j : E), θ⟫ + η j

omit [OpensMeasurableSpace E] in
lemma cons_nextState_zero {n : ℕ} {hn : 0 < n} {d : Fin n → 𝒳} {f : (Fin n → ℝ) → S}
    {hf : Measurable f} (θ : E) (s : S) (η : Fin n → ℝ) :
    (A.cons n hn d f hf).nextState θ 0 s η = f fun j ↦ ⟪(d j : E), θ⟫ + η j := rfl

omit [OpensMeasurableSpace E] in
lemma cons_nextState_succ {n : ℕ} {hn : 0 < n} {d : Fin n → 𝒳} {f : (Fin n → ℝ) → S}
    {hf : Measurable f} (θ : E) (ℓ : ℕ) (s : S) (η : Fin (A.len ℓ) → ℝ) :
    (A.cons n hn d f hf).nextState θ (ℓ + 1) s η = A.nextState θ ℓ s η := rfl

lemma measurable_nextState (θ : E) (ℓ : ℕ) :
    Measurable (Function.uncurry (A.nextState θ ℓ)) := by
  have : Function.uncurry (A.nextState θ ℓ) = Function.uncurry (A.upd ℓ) ∘
      fun p : S × (Fin (A.len ℓ) → ℝ) ↦ (p.1, fun j ↦ ⟪(A.act ℓ p.1 j : E), θ⟫ + p.2 j) := rfl
  rw [this]
  refine (A.measurable_upd ℓ).comp (measurable_fst.prodMk (measurable_pi_lambda _ fun j ↦ ?_))
  exact ((continuous_id.inner continuous_const).measurable.comp (measurable_subtype_coe.comp
    ((A.measurable_act ℓ j).comp measurable_fst))).add ((measurable_pi_apply j).comp measurable_snd)

variable (h : IsAlgEnvSeq X Y A.toAlgorithm (LinearBandit.linearGaussianEnv 𝒳 θ) P)
include h

/-- **The noise of a phase is independent of the state at the start of the phase**, with the
i.i.d. `N(0, 1)` law. -/
lemma hasCondDistrib_phaseNoise (ℓ : ℕ) :
    HasCondDistrib (A.phaseNoise θ X Y ℓ) (A.stateProc Y ℓ)
      (Kernel.const _ (Measure.pi fun _ ↦ gaussianReal 0 1)) P := by
  have h1 := (h.hasCondDistrib_noise_window (A.start ℓ) (A.len ℓ)).const_comp_right
    (A.measurable_stateOfFinHistory ℓ)
  have h2 : A.stateOfFinHistory ℓ ∘ finHistory X Y (A.start ℓ) = A.stateProc Y ℓ :=
    funext fun ω ↦ A.stateOfFinHistory_finHistory ℓ ω
  rwa [h2] at h1

variable [MeasurableEq 𝒳]

/-- The observations of phase `ℓ` are `⟪act ℓ s j, θ⟫ + η j` for the state `s` at the start of the
phase and the noise `η` of the phase. -/
lemma ae_phaseObs_eq : ∀ᵐ ω ∂P, ∀ ℓ, A.phaseObs ℓ (fun t ↦ Y t ω) =
    fun j ↦ ⟪(A.act ℓ (A.stateProc Y ℓ ω) j : E), θ⟫ + A.phaseNoise θ X Y ℓ ω j := by
  filter_upwards [A.ae_action_start_add_eq h] with ω hω ℓ
  funext j
  simp only [phaseObs, phaseNoise, LinearBandit.noise, hω ℓ j]
  ring

/-- The state at the end of phase `ℓ` is `nextState θ ℓ s η` for the state `s` at the start of the
phase and the noise `η` of the phase. -/
lemma ae_stateProc_succ_eq : ∀ᵐ ω ∂P, ∀ ℓ,
    A.stateProc Y (ℓ + 1) ω = A.nextState θ ℓ (A.stateProc Y ℓ ω) (A.phaseNoise θ X Y ℓ ω) := by
  filter_upwards [A.ae_phaseObs_eq h] with ω hω ℓ
  unfold nextState
  rw [← hω ℓ]
  rfl

/-- **One phase**: if from every good state `s` the next state is good with probability at least
`1 - δ` over the noise of the phase, then the probability that the state at the end of the phase
is good is at least the probability that the state at the start is good, minus `δ`. -/
lemma measureReal_stateProc_mem_sub_le {good good' : Set S} (hgood : MeasurableSet good)
    (hgood' : MeasurableSet good') {δ : ℝ} (hδ0 : 0 ≤ δ) (ℓ : ℕ)
    (hstep : ∀ s ∈ good, 1 - δ ≤ (Measure.pi fun _ : Fin (A.len ℓ) ↦ gaussianReal 0 1).real
      {η | A.nextState θ ℓ s η ∈ good'}) :
    P.real {ω | A.stateProc Y ℓ ω ∈ good} - δ ≤ P.real {ω | A.stateProc Y (ℓ + 1) ω ∈ good'} := by
  have h1 := (A.hasCondDistrib_phaseNoise h ℓ).measureReal_sub_le hgood
    (A.measurable_nextState θ ℓ hgood') hδ0 fun s hs ↦ by
      rw [Kernel.const_apply]
      exact hstep s hs
  refine h1.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_))
  change ∀ᵐ ω ∂P, ω ∈ (fun ω ↦ (A.stateProc Y ℓ ω, A.phaseNoise θ X Y ℓ ω)) ⁻¹'
    (Function.uncurry (A.nextState θ ℓ) ⁻¹' good') → ω ∈ {ω | A.stateProc Y (ℓ + 1) ω ∈ good'}
  filter_upwards [A.ae_stateProc_succ_eq h] with ω hω hmem
  rw [Set.mem_preimage, Set.mem_preimage, Function.uncurry_apply_pair] at hmem
  rw [hω ℓ]
  exact hmem

/-- **Union bound over the phases**: if the initial state is good and each phase `ℓ < L` fails
with probability at most `δ ℓ`, then the state at the end of phase `L - 1` is good with
probability at least `1 - ∑ ℓ < L, δ ℓ`. -/
lemma one_sub_sum_le_measureReal_stateProc_mem {good : ℕ → Set S}
    (hgood : ∀ ℓ, MeasurableSet (good ℓ)) {δ : ℕ → ℝ} (hδ0 : ∀ ℓ, 0 ≤ δ ℓ)
    (hinit : A.init ∈ good 0) (L : ℕ)
    (hstep : ∀ ℓ < L, ∀ s ∈ good ℓ,
      1 - δ ℓ ≤ (Measure.pi fun _ : Fin (A.len ℓ) ↦ gaussianReal 0 1).real
        {η | A.nextState θ ℓ s η ∈ good (ℓ + 1)}) :
    1 - ∑ ℓ ∈ range L, δ ℓ ≤ P.real {ω | A.stateProc Y L ω ∈ good L} := by
  induction L with
  | zero =>
    have : {ω | A.stateProc Y 0 ω ∈ good 0} = Set.univ := Set.eq_univ_of_forall fun _ ↦ hinit
    rw [this, probReal_univ]
    simp
  | succ L ih =>
    rw [sum_range_succ, sub_add_eq_sub_sub]
    have h1 := ih fun ℓ hℓ ↦ hstep ℓ (by omega)
    have h2 := A.measureReal_stateProc_mem_sub_le h (hgood L) (hgood (L + 1)) (hδ0 L) L
      (hstep L (by omega))
    linarith

end Learning.PhasedAlg

namespace Learning.PhasedAlg

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {𝒳 : Set E} {S : Type*} {mS : MeasurableSpace S}
  (A : PhasedAlg 𝒳 ℝ S) [MeasurableEq 𝒳]

/-- **PAC guarantee of a phased identification algorithm** in a linear Gaussian bandit: if for
every reward vector `θ` there are good sets of states `good ℓ` such that the initial state is
good, each phase `ℓ < L` fails with probability at most `δ ℓ` with `∑ ℓ < L, δ ℓ ≤ δ`, and every
good final state gives a good output, then the algorithm is `δ`-PAC. -/
lemma isPAC_toIdentAlg {𝓞 : Type*} {m𝓞 : MeasurableSpace 𝓞} [MeasurableEq 𝓞] {L : ℕ}
    {out : S → 𝓞} {hout : Measurable out} {gd : E → 𝓞 → Prop} {δ : ℝ}
    (hgood : ∀ θ : E, ∃ good : ℕ → Set S, (∀ ℓ, MeasurableSet (good ℓ)) ∧ A.init ∈ good 0 ∧
      (∃ δs : ℕ → ℝ, (∀ ℓ, 0 ≤ δs ℓ) ∧ ∑ ℓ ∈ range L, δs ℓ ≤ δ ∧ ∀ ℓ < L, ∀ s ∈ good ℓ,
        1 - δs ℓ ≤ (Measure.pi fun _ : Fin (A.len ℓ) ↦ gaussianReal 0 1).real
          {η | A.nextState θ ℓ s η ∈ good (ℓ + 1)}) ∧
      ∀ s ∈ good L, gd θ (out s)) :
    (A.toIdentAlg L out hout).IsPAC.{u} (LinearBandit.linearGaussianEnv 𝒳) gd δ := by
  intro θ Ω _ P _ X Y o hrun
  obtain ⟨good, hmeas, hinit, ⟨δs, hδs0, hδs, hstep⟩, hL⟩ := hgood θ
  have h1 := A.one_sub_sum_le_measureReal_stateProc_mem hrun.isAlgEnvSeq hmeas hδs0 hinit L hstep
  have h2 : P.real {ω | A.stateProc Y L ω ∈ good L} ≤ P.real {ω | gd θ (o ω)} := by
    refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae ?_)
    change ∀ᵐ ω ∂P, ω ∈ {ω | A.stateProc Y L ω ∈ good L} → ω ∈ {ω | gd θ (o ω)}
    filter_upwards [A.output_ae_eq_of_isRun hrun] with ω hω hmem
    rw [hω]
    exact hL _ hmem
  linarith

/-- **`(ε, δ)`-PAC guarantee of a phased identification algorithm** in a linear Gaussian bandit
(the case of `isPAC_toIdentAlg` where the output is a recommended arm and good means "simple
regret at most `ε`"). -/
lemma linearBandit_isPAC_toIdentAlg {L : ℕ} {out : S → 𝒳} {hout : Measurable out} {ε δ : ℝ}
    (hgood : ∀ θ : E, ∃ good : ℕ → Set S, (∀ ℓ, MeasurableSet (good ℓ)) ∧ A.init ∈ good 0 ∧
      (∃ δs : ℕ → ℝ, (∀ ℓ, 0 ≤ δs ℓ) ∧ ∑ ℓ ∈ range L, δs ℓ ≤ δ ∧ ∀ ℓ < L, ∀ s ∈ good ℓ,
        1 - δs ℓ ≤ (Measure.pi fun _ : Fin (A.len ℓ) ↦ gaussianReal 0 1).real
          {η | A.nextState θ ℓ s η ∈ good (ℓ + 1)}) ∧
      ∀ s ∈ good L, LinearBandit.simpleRegret 𝒳 θ (out s) ≤ ε) :
    LinearBandit.IsPAC 𝒳 (A.toIdentAlg L out hout) ε δ :=
  A.isPAC_toIdentAlg hgood

end Learning.PhasedAlg
