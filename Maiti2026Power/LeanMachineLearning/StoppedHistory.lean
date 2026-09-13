/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import LeanMachineLearning.SequentialLearning.StoppedHistory
public import Maiti2026Power.LeanMachineLearning.HistoryLaw

/-!
# Stopped histories: characterizations, truncation and laws

LML (`LeanMachineLearning.SequentialLearning.StoppedHistory`) introduces the process of
histories of variable length `sigmaHistory O X Y n = ⟨n, history O X Y n⟩`, the stopping time
`hittingAfter (sigmaHistory O X Y) S 0` of a *stopping rule* `S` (a measurable set of histories
of variable length: the interaction stops after `n` rounds if the history of these `n` rounds
belongs to `S`) and the *stopped history* `stoppedValue (sigmaHistory O X Y) τ` at a random time
`τ : Ω → WithTop ℕ`, together with their measurability and the law `stoppedHistMeasure` of the
history stopped by a stopping rule. This file develops the API used by the divergence
decomposition at a stopping time (`Maiti2026Power.LeanMachineLearning.DivergenceDecomposition`):

* characterizations of the stopping time of a stopping rule
  (`lt_hittingAfter_sigmaHistory_iff`, `hittingAfter_sigmaHistory_eq_coe_iff`) and
  `stoppedValue_sigmaHistory_of_eq`: the history stopped at a time equal to `n` is the history
  of the first `n` rounds;
* the history stopped at time `M`, Mathlib's `stoppedProcess (sigmaHistory O X Y) τ M` (the
  history of the first `min τ M` rounds): `measurable_stoppedProcess_sigmaHistory`,
  `stoppedProcess_sigmaHistory_zero` and its law `hasLaw_stoppedProcess_sigmaHistory_zero`,
  `fst_stoppedProcess_sigmaHistory_le`;
* `truncHist M`, `truncHist_stoppedValue_sigmaHistory`: truncating the history stopped at a
  finite time `τ` to its first `M` rounds gives the history stopped at time `M`, almost surely
  when `τ` is almost surely finite (`stoppedProcess_sigmaHistory_ae_eq_truncHist`), so that the
  history stopped at time `M` has law the image of the law of the history stopped at `τ` by the
  truncation (`HasLaw.stoppedProcess_sigmaHistory`), and `restrict_map_truncHist`: both laws
  agree on histories of length `< M`;
* `exists_measurableSet_preimage_lt_hittingAfter_sigmaHistory`: the event `{n < τ}` is
  determined by the first `n` rounds;
* `map_stoppedProcess_sigmaHistory_eq_add`, `map_stoppedProcess_sigmaHistory_succ_eq_add`: the
  laws of the histories stopped at times `M` and `M + 1` split according to whether `τ ≤ M`;
  `IsAlgEnvSeq.hasCondDistrib_step_restrict_lt_hittingAfter_sigmaHistory`,
  `IsAlgEnvSeq.hasCondDistrib_obs_restrict_lt_hittingAfter_sigmaHistory`,
  `IsAlgEnvSeq.hasCondDistrib_action_restrict_lt_hittingAfter_sigmaHistory`: on the event
  `{M < τ}`, which is determined by the first `M` rounds, the step, the observation and the
  action at round `M` keep their conditional laws.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace Learning

variable {𝓞 𝓐 𝓨 : Type*} {m𝓞 : MeasurableSpace 𝓞} {m𝓐 : MeasurableSpace 𝓐}
  {m𝓨 : MeasurableSpace 𝓨} {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {O : ℕ → Ω → 𝓞} {X : ℕ → Ω → 𝓐} {Y : ℕ → Ω → 𝓨} {S : Set (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)}
  {τ : Ω → WithTop ℕ} {ω : Ω} {n M : ℕ}

section stoppingTime

omit m𝓞 m𝓐 m𝓨

/-- The stopping rule `S` has not fired after `n` rounds iff none of the histories of the first
`j ≤ n` rounds belongs to `S`. -/
lemma lt_hittingAfter_sigmaHistory_iff :
    (n : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω ↔
      ∀ j ≤ n, sigmaHistory O X Y j ω ∉ S := by
  rw [← not_le]
  refine (not_congr (hittingAfter_le_iff (u := sigmaHistory O X Y) (s := S) (n := 0) (i := n)
    (ω := ω))).trans ?_
  simp

/-- The stopping rule `S` fires after exactly `n` rounds iff the history of the first `n` rounds
belongs to `S` and no history of fewer rounds does. -/
lemma hittingAfter_sigmaHistory_eq_coe_iff :
    hittingAfter (sigmaHistory O X Y) S 0 ω = n ↔
      sigmaHistory O X Y n ω ∈ S ∧ ∀ j < n, sigmaHistory O X Y j ω ∉ S :=
  (hittingAfter_eq_coe_iff (u := sigmaHistory O X Y) (s := S) (n := 0) (i := n)
    (ω := ω)).trans (by simp)

/-- The history stopped at a time equal to `n` is the history of the first `n` rounds. -/
lemma stoppedValue_sigmaHistory_of_eq (h : τ ω = n) :
    stoppedValue (sigmaHistory O X Y) τ ω = ⟨n, history O X Y n ω⟩ := by
  simp only [stoppedValue, h]
  rfl

/-- The history stopped at time `M` has length at most `M`. -/
lemma fst_stoppedProcess_sigmaHistory_le :
    (stoppedProcess (sigmaHistory O X Y) τ M ω).1 ≤ M := by
  rcases le_or_gt (τ ω) M with h | h
  · rw [stoppedProcess_eq_of_ge (i := M) h]
    exact WithTop.untopA_le h
  · rw [stoppedProcess_eq_of_le (i := M) h.le]
    exact le_rfl

/-- The history stopped at time `0` is the empty history. -/
lemma stoppedProcess_sigmaHistory_zero (τ : Ω → WithTop ℕ) :
    stoppedProcess (sigmaHistory O X Y) τ 0 = fun _ ↦ ⟨0, default⟩ := by
  funext ω
  rw [stoppedProcess_eq_of_le (i := 0) (by simp)]
  exact congrArg (Sigma.mk 0) (Subsingleton.elim _ _)

end stoppingTime

/-- The history stopped at time `0` has the Dirac law at the empty history. -/
lemma hasLaw_stoppedProcess_sigmaHistory_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : Ω → WithTop ℕ) :
    HasLaw (stoppedProcess (sigmaHistory O X Y) τ 0)
      (Measure.dirac (⟨0, default⟩ : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) P :=
  hasLaw_dirac_of_ae_eq
    (Filter.Eventually.of_forall (congrFun (stoppedProcess_sigmaHistory_zero τ)))

section truncation

/-- Truncation of a history of variable length to its first `M` rounds. -/
def truncHist (M : ℕ) (h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n) : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n :=
  if hM : h.1 ≤ M then h else ⟨M, fun i ↦ h.2 (Fin.castLE (not_le.1 hM).le i)⟩

lemma measurable_truncHist (M : ℕ) :
    Measurable (truncHist (𝓞 := 𝓞) (𝓐 := 𝓐) (𝓨 := 𝓨) M) := by
  refine measurable_sigma_of_measurable_comp_mk fun n ↦ ?_
  by_cases hn : n ≤ M
  · simp only [Function.comp_def, truncHist, hn, dite_true]
    exact measurable_sigma_mk n
  · simp only [Function.comp_def, truncHist, hn, dite_false]
    exact (measurable_sigma_mk M).comp
      (Measurable.of_eval fun i ↦ measurable_pi_apply (Fin.castLE (not_le.1 hn).le i))

omit m𝓞 m𝓐 m𝓨 in
lemma truncHist_of_fst_le {h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n} (hM : h.1 ≤ M) : truncHist M h = h :=
  dite_eq_left hM

omit m𝓞 m𝓐 m𝓨 in
/-- Truncating the history stopped at a finite time `τ` to its first `M` rounds gives the history
stopped at time `M`. -/
lemma truncHist_stoppedValue_sigmaHistory (h : τ ω ≠ ⊤) :
    truncHist M (stoppedValue (sigmaHistory O X Y) τ ω) =
      stoppedProcess (sigmaHistory O X Y) τ M ω := by
  rcases le_or_gt (τ ω) M with hτ | hτ
  · rw [stoppedProcess_eq_of_ge (i := M) hτ]
    exact truncHist_of_fst_le (WithTop.untopA_le hτ)
  · rw [stoppedProcess_eq_of_le (i := M) hτ.le, truncHist, dite_eq_right]
    · rfl
    · exact not_le.2 ((WithTop.lt_untopA_iff h).2 hτ)

omit m𝓞 m𝓐 m𝓨 in
lemma preimage_truncHist_fst_lt (M : ℕ) :
    truncHist M ⁻¹' {h : Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n | h.1 < M} = {h | h.1 < M} := by
  ext h
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, truncHist]
  split_ifs with hM
  · rfl
  · simp only [lt_self_iff_false, false_iff, not_lt]
    exact (not_le.1 hM).le

/-- The image of a measure by the truncation to the first `M` rounds agrees with the measure on
histories of length `< M`. -/
lemma restrict_map_truncHist (μ : Measure (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)) (M : ℕ) :
    (μ.map (truncHist M)).restrict {h | h.1 < M} = μ.restrict {h | h.1 < M} := by
  rw [Measure.restrict_map (measurable_truncHist M) (measurableSet_sigma_fst_lt M),
    preimage_truncHist_fst_lt]
  conv_rhs => rw [← Measure.map_id (μ := μ.restrict {h | h.1 < M})]
  refine Measure.map_congr ((ae_restrict_iff' (measurableSet_sigma_fst_lt M)).2
    (Filter.Eventually.of_forall fun h hh ↦ ?_))
  exact truncHist_of_fst_le hh.le

end truncation

section measurability

variable (hO : ∀ n, Measurable (O n)) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
include hO hX hY

lemma measurableSet_hittingAfter_sigmaHistory_le (hS : MeasurableSet S) (M : ℕ) :
    MeasurableSet {ω | hittingAfter (sigmaHistory O X Y) S 0 ω ≤ M} :=
  measurable_hittingAfter_sigmaHistory hO hX hY hS measurableSet_Iic

lemma measurableSet_lt_hittingAfter_sigmaHistory (hS : MeasurableSet S) (M : ℕ) :
    MeasurableSet {ω | (M : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω} :=
  measurable_hittingAfter_sigmaHistory hO hX hY hS measurableSet_Ioi

lemma measurable_stoppedProcess_sigmaHistory (hτ : Measurable τ) (M : ℕ) :
    Measurable (stoppedProcess (sigmaHistory O X Y) τ M) :=
  measurable_stoppedValue_sigmaHistory hO hX hY (by fun_prop)

omit hO hX hY in
/-- For an almost surely finite `τ`, the history stopped at time `M` is almost surely the
truncation to the first `M` rounds of the history stopped at `τ`. -/
lemma stoppedProcess_sigmaHistory_ae_eq_truncHist {P : Measure Ω} (hτ_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (M : ℕ) :
    stoppedProcess (sigmaHistory O X Y) τ M =ᵐ[P]
      truncHist M ∘ stoppedValue (sigmaHistory O X Y) τ := by
  filter_upwards [hτ_top] with ω hω
  exact (truncHist_stoppedValue_sigmaHistory hω).symm

omit hO hX hY in
/-- If the history stopped at an almost surely finite `τ` has law `μ`, the history stopped at
time `M` has law the image of `μ` by the truncation to the first `M` rounds. -/
lemma _root_.ProbabilityTheory.HasLaw.stoppedProcess_sigmaHistory {P : Measure Ω}
    {μ : Measure (Σ n : ℕ, Hist 𝓞 𝓐 𝓨 n)} (h : HasLaw (stoppedValue (sigmaHistory O X Y) τ) μ P)
    (hτ_top : ∀ᵐ ω ∂P, τ ω ≠ ⊤) (M : ℕ) :
    HasLaw (stoppedProcess (sigmaHistory O X Y) τ M) (μ.map (truncHist M)) P :=
  ((hasLaw_map (measurable_truncHist M).aemeasurable).comp h).congr
    (stoppedProcess_sigmaHistory_ae_eq_truncHist hτ_top M)

omit hO hX hY in
/-- The event `{n < τ}`, for the stopping time `τ` of a stopping rule, is determined by the
history of the first `n` rounds. -/
lemma exists_measurableSet_preimage_lt_hittingAfter_sigmaHistory (hS : MeasurableSet S) (n : ℕ) :
    ∃ B : Set (Hist 𝓞 𝓐 𝓨 n), MeasurableSet B ∧
      {ω | (n : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω} = history O X Y n ⁻¹' B := by
  refine ⟨⋂ j, ⋂ (hj : j ≤ n),
    {h | (⟨j, fun i ↦ h (Fin.castLE hj i)⟩ : Σ n, Hist 𝓞 𝓐 𝓨 n) ∉ S}, ?_, ?_⟩
  · refine MeasurableSet.iInter fun j ↦ MeasurableSet.iInter fun hj ↦ ?_
    exact ((measurable_sigma_mk j).comp (Measurable.of_eval fun _ ↦ measurable_pi_apply _))
      hS.compl
  · ext ω
    simp only [Set.mem_ofPred_eq, lt_hittingAfter_sigmaHistory_iff, Set.mem_preimage,
      Set.mem_iInter]
    exact ⟨fun h j hj ↦ h j hj, fun h j hj ↦ h j hj⟩

end measurability

section law

variable (hO : ∀ n, Measurable (O n)) (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
  {P : Measure Ω}
include hO hX hY

omit m𝓞 m𝓐 m𝓨 hO hX hY in
lemma compl_setOf_le_natCast (τ : Ω → WithTop ℕ) (M : ℕ) :
    {ω | τ ω ≤ M}ᶜ = {ω | (M : WithTop ℕ) < τ ω} := by
  ext ω
  simp

/-- The law of the history stopped at time `M` splits according to whether `τ ≤ M`: on
`{τ ≤ M}` it is the law of the history stopped at `τ`, on `{M < τ}` it is the law of the history
of the first `M` rounds. -/
lemma map_stoppedProcess_sigmaHistory_eq_add (hτ : Measurable τ) (M : ℕ) :
    P.map (stoppedProcess (sigmaHistory O X Y) τ M) =
      (P.restrict {ω | τ ω ≤ M}).map (stoppedProcess (sigmaHistory O X Y) τ M) +
        ((P.restrict {ω | (M : WithTop ℕ) < τ ω}).map (history O X Y M)).map (Sigma.mk M) := by
  have hZ := measurable_stoppedProcess_sigmaHistory hO hX hY hτ M
  have hle : MeasurableSet {ω | τ ω ≤ M} := hτ measurableSet_Iic
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := P) hle, Measure.map_add _ _ hZ,
    compl_setOf_le_natCast]
  congr 1
  rw [Measure.map_map (measurable_sigma_mk M) (measurable_history hO hX hY M)]
  refine Measure.map_congr ((ae_restrict_iff' (hle.compl.congr ?_)).2
    (Filter.Eventually.of_forall fun ω hω ↦ ?_))
  · exact compl_setOf_le_natCast τ M
  · exact stoppedProcess_eq_of_le (i := M) hω.le

/-- The law of the history stopped at time `M + 1` splits according to whether `τ ≤ M`: on
`{τ ≤ M}` it is the law of the history stopped at time `M`, on `{M < τ}` it is the law of the
history of the first `M + 1` rounds. -/
lemma map_stoppedProcess_sigmaHistory_succ_eq_add (hτ : Measurable τ) (M : ℕ) :
    P.map (stoppedProcess (sigmaHistory O X Y) τ (M + 1)) =
      (P.restrict {ω | τ ω ≤ M}).map (stoppedProcess (sigmaHistory O X Y) τ M) +
        ((P.restrict {ω | (M : WithTop ℕ) < τ ω}).map (history O X Y (M + 1))).map
          (Sigma.mk (M + 1)) := by
  have hZ := measurable_stoppedProcess_sigmaHistory hO hX hY hτ (M + 1)
  have hle : MeasurableSet {ω | τ ω ≤ M} := hτ measurableSet_Iic
  conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := P) hle, Measure.map_add _ _ hZ,
    compl_setOf_le_natCast]
  congr 1
  · refine Measure.map_congr ((ae_restrict_iff' hle).2
      (Filter.Eventually.of_forall fun ω hω ↦ ?_))
    rw [stoppedProcess_eq_of_ge (i := M) hω,
      stoppedProcess_eq_of_ge (i := M + 1) (hω.trans (WithTop.coe_le_coe.2 (Nat.le_add_right M 1)))]
  · rw [Measure.map_map (measurable_sigma_mk (M + 1)) (measurable_history hO hX hY (M + 1))]
    refine Measure.map_congr ((ae_restrict_iff' (hle.compl.congr (compl_setOf_le_natCast τ M))).2
      (Filter.Eventually.of_forall fun ω hω ↦ ?_))
    refine stoppedProcess_eq_of_le (i := M + 1) ?_
    push_cast
    exact Order.add_one_le_of_lt (α := ℕ∞) (show (M : WithTop ℕ) < τ ω from hω)

omit hO hX hY in
/-- The image of the restriction of `P` to `A` by `f` gives measure zero to a set avoided by `f`
on `A`. -/
lemma _root_.MeasureTheory.Measure.map_restrict_apply_of_forall_notMem {H : Type*}
    {mH : MeasurableSpace H} {f : Ω → H} (hf : Measurable f) {A : Set Ω} {T : Set H}
    (hT : MeasurableSet T) (h : ∀ ω ∈ A, f ω ∉ T) : ((P.restrict A).map f) T = 0 := by
  rw [Measure.map_apply hf hT, Measure.restrict_apply (hf hT)]
  exact measure_mono_null (fun ω hω ↦ (h ω hω.2 hω.1).elim) measure_empty

/-- On `{τ ≤ M}`, for the stopping time `τ` of the stopping rule `S`, the history stopped at
time `M` belongs to `S`. -/
lemma map_restrict_hittingAfter_sigmaHistory_le_stoppedProcess_apply_compl (hS : MeasurableSet S)
    (M : ℕ) :
    ((P.restrict {ω | hittingAfter (sigmaHistory O X Y) S 0 ω ≤ M}).map
      (stoppedProcess (sigmaHistory O X Y) (hittingAfter (sigmaHistory O X Y) S 0) M)) Sᶜ = 0 := by
  refine Measure.map_restrict_apply_of_forall_notMem
    (measurable_stoppedProcess_sigmaHistory hO hX hY
      (measurable_hittingAfter_sigmaHistory hO hX hY hS) M) hS.compl fun ω hω h ↦ h ?_
  rw [stoppedProcess_eq_of_ge (i := M) hω]
  exact hittingAfter_mem_set_of_ne_top (ne_top_of_le_ne_top (WithTop.natCast_ne_top M) hω)

/-- The history stopped at time `M` has length at most `M`. -/
lemma map_restrict_stoppedProcess_sigmaHistory_apply_compl_fst_le (hτ : Measurable τ) (A : Set Ω)
    (M : ℕ) :
    ((P.restrict A).map (stoppedProcess (sigmaHistory O X Y) τ M)) {h | h.1 ≤ M}ᶜ = 0 :=
  Measure.map_restrict_apply_of_forall_notMem
    (measurable_stoppedProcess_sigmaHistory hO hX hY hτ M)
    (measurableSet_sigma_fst_le M).compl fun _ _ h ↦ h fst_stoppedProcess_sigmaHistory_le

/-- On `{M < τ}`, for the stopping time `τ` of the stopping rule `S`, the history of the first
`M` rounds does not belong to `S`. -/
lemma map_restrict_lt_hittingAfter_sigmaHistory_map_sigmaMk_apply (hS : MeasurableSet S) (M : ℕ) :
    (((P.restrict {ω | (M : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω}).map
      (history O X Y M)).map (Sigma.mk M)) S = 0 := by
  rw [Measure.map_map (measurable_sigma_mk M) (measurable_history hO hX hY M)]
  exact Measure.map_restrict_apply_of_forall_notMem
    ((measurable_sigma_mk M).comp (measurable_history hO hX hY M)) hS
    fun ω hω ↦ notMem_of_lt_hittingAfter (k := M) hω (Nat.zero_le M)

end law

section filtration

variable {alg : Algorithm 𝓞 𝓐 𝓨} {env : Environment 𝓞 𝓐 𝓨} {P : Measure Ω} [IsFiniteMeasure P]

/-- On the event `{M < τ}`, for the stopping time `τ` of the stopping rule `S`, which is
determined by the first `M` rounds, the step at round `M` keeps its conditional law given the
first `M` rounds. -/
lemma IsAlgEnvSeq.hasCondDistrib_step_restrict_lt_hittingAfter_sigmaHistory
    (h : IsAlgEnvSeq O X Y alg env P) (hS : MeasurableSet S) (M : ℕ) :
    HasCondDistrib (step O X Y M) (history O X Y M) (stepKernel alg env M)
      (P.restrict {ω | (M : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω}) := by
  obtain ⟨B, hB, hB_eq⟩ :=
    exists_measurableSet_preimage_lt_hittingAfter_sigmaHistory (O := O) (X := X) (Y := Y) hS M
  rw [hB_eq]
  exact (h.hasCondDistrib_step M).restrict_preimage
    (h.measurable_history M) (h.measurable_step M) hB

/-- On the event `{M < τ}`, for the stopping time `τ` of the stopping rule `S`, which is
determined by the first `M` rounds, the observation at round `M` keeps its conditional law
given the first `M` rounds. -/
lemma IsAlgEnvSeq.hasCondDistrib_obs_restrict_lt_hittingAfter_sigmaHistory
    (h : IsAlgEnvSeq O X Y alg env P) (hS : MeasurableSet S) (M : ℕ) :
    HasCondDistrib (O M) (history O X Y M) (env.obs M)
      (P.restrict {ω | (M : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω}) := by
  obtain ⟨B, hB, hB_eq⟩ :=
    exists_measurableSet_preimage_lt_hittingAfter_sigmaHistory (O := O) (X := X) (Y := Y) hS M
  rw [hB_eq]
  exact (h.hasCondDistrib_obs M).restrict_preimage (h.measurable_history M) (h.measurable_obs M)
    hB

/-- On the event `{M < τ}`, for the stopping time `τ` of the stopping rule `S`, which is
determined by the first `M` rounds, the action at round `M` keeps its conditional law given the
first `M` rounds and the observation at round `M`. -/
lemma IsAlgEnvSeq.hasCondDistrib_action_restrict_lt_hittingAfter_sigmaHistory
    (h : IsAlgEnvSeq O X Y alg env P) (hS : MeasurableSet S) (M : ℕ) :
    HasCondDistrib (X M) (fun ω ↦ (history O X Y M ω, O M ω)) (alg.policy M)
      (P.restrict {ω | (M : WithTop ℕ) < hittingAfter (sigmaHistory O X Y) S 0 ω}) := by
  obtain ⟨B, hB, hB_eq⟩ :=
    exists_measurableSet_preimage_lt_hittingAfter_sigmaHistory (O := O) (X := X) (Y := Y) hS M
  have hB' : history O X Y M ⁻¹' B = (fun ω ↦ (history O X Y M ω, O M ω)) ⁻¹' (B ×ˢ Set.univ) := by
    ext ω
    simp
  rw [hB_eq, hB']
  exact (h.hasCondDistrib_action M).restrict_preimage
    ((h.measurable_history M).prodMk (h.measurable_obs M)) (h.measurable_action M)
    (hB.prod MeasurableSet.univ)

end filtration

end Learning
