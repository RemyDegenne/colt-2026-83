# Blueprint outline, Part II: prerequisite chapters (labels and proof routes)

Read `notes/blueprint-outline.md` first for the global conventions. This file fixes the labels
of the prerequisite chapters (`blueprint/src/chapters/prereq_*.tex`). Part I chapters reference
these labels; the prerequisite chapters may reference Part I labels only from `model.tex`
(def:env, def:bai_alg, lem:noise_representation, lem:composition, def:arm_set) and
`lem:loewner_*`/`lem:eigen_quadratic_bounds`/`lem:sqrt_props` from `design.tex`.

Each prerequisite chapter must start with a paragraph "What Mathlib/LML provides" naming the
relevant existing declarations (checked in the local Mathlib at
`.lake/packages/mathlib`, LML at `.lake/packages/LeanMachineLearning`), and a paragraph "What is
missing". Statements that are already in Mathlib are still stated (as lemmas with a one-line
proof "Mathlib: `name`") so that the dependency graph is complete; mark them with
`\mathlibok` after `\leanok`? No: leave them untagged but write "(Mathlib: ...)" in the proof.

---------------------------------------------------------------------------------------------

## prereq_gaussian.tex — `\chapter{Gaussian vectors and linear Gaussian processes}\label{chap:pre_gaussian}`

Mathlib: `ProbabilityTheory.stdGaussian`, `multivariateGaussian μ S` (= image of `stdGaussian`
by `μ + (CFC.sqrt S) ·`), `IsGaussian`, `HasGaussianLaw` (closed under continuous linear maps:
`HasGaussianLaw.map`), `stdGaussian_map` (invariance under linear isometry equivalences),
`map_pi_eq_stdGaussian`, `isGaussian_iff_charFun_eq`, `HasGaussianLaw.indepFun_of_covariance_*`
(`Mathlib/Probability/Distributions/Gaussian/HasGaussianLaw/Independence.lean`),
`gaussianReal`, `mgf_gaussianReal`, `variance_id_gaussianReal`, `covarianceBilin_multivariateGaussian`.

* lem:gauss_pi — if `η_0,…,η_{T−1}` are i.i.d. `\Normal(0,1)` then `η ∼ \Normal(0, I_T)` i.e.
  the law is `stdGaussian`; conversely coordinates of `stdGaussian` are i.i.d. (Mathlib `map_pi_eq_stdGaussian`).
* lem:gauss_linear_image — `g ∼ \Normal(0,I_n)`, `M ∈ \R^{m×n}`, `μ ∈ \R^m`: `μ + Mg ∼ \Normal(μ, MM^⊤)`.
  More generally a linear image of a Gaussian vector is Gaussian with the transformed mean and covariance.
* lem:gauss_law_of_cov — two Gaussian vectors with the same mean and covariance have the same law
  (characteristic function `\exp(i\ip{t}{μ} − ½t^⊤St)`). In particular `\Normal(0,S) = law(S^{1/2}g)`
  and `−G \eqd G` for centered `G`.
* lem:gauss_rotation — `(g, g')` i.i.d. standard in `\R^d`, `θ ∈ \R`: `(g\sinθ + g'\cosθ, g\cosθ − g'\sinθ)`
  has the same law as `(g,g')` (Mathlib `stdGaussian_map` with the linear isometry of `\R^{2d}`).
* lem:gauss_joint_linear — if `V ∼ \Normal(μ, S)` on `\R^n` and `L_1, L_2` are linear, then
  `(L_1V, L_2V)` is jointly Gaussian with the induced covariance; the covariance of `L_1V` and
  `L_2V` is `L_1 S L_2^⊤`.
* lem:gauss_uncorrelated_indep — jointly Gaussian `(V_1,V_2)` with `Cov(V_1,V_2) = 0` are independent
  (Mathlib `HasGaussianLaw.indepFun_of_covariance_eval` or `_inner`).
* lem:indep_integral_zero — `W` integrable centered, `V` any random variable, `W ⊥ V`, `f` bounded
  measurable with values in `\R^d`: `\E\ip{f(V)}{W} = 0`.
* lem:gauss_1d_moments — `Z∼\Normal(0,σ²)`: `\E Z² = σ²`, `\E Z⁴ = 3σ⁴`, `\E|Z| = σ\sqrt{2/π}`,
  `\E e^{λZ} = e^{λ²σ²/2}` (Mathlib `mgf_gaussianReal`; moments by differentiating or by direct integration).
* lem:gauss_norm_moments — `g ∼ \Normal(0,I_d)`, `S ∈ \PSD`, `Y := S^{1/2}g ∼ \Normal(0,S)`:
  `\E‖Y‖² = \tr S`, `\E‖Y‖⁴ = (\tr S)² + 2\tr(S²) ≤ 3(\tr S)²`, `\E‖Y‖ ≤ \sqrt{\tr S}`, and
  `\E‖Y‖ ≥ \sqrt{\tr S}/\sqrt3` (Hölder: `\E‖Y‖² ≤ (\E‖Y‖)^{2/3}(\E‖Y‖⁴)^{1/3}`). Proof of the
  fourth moment: diagonalize `S`, `‖Y‖² = Σ_i s_i g_i²` with i.i.d. `g_i`, expand using `\E g_i⁴ = 3`.
  Special case `S = I`: `\E‖g‖² = d`, `\E‖g‖ ≤ \sqrt d`.
* lem:gauss_tail — `Z ∼ \Normal(μ,σ²)`: `\Prob(Z − μ ≥ t) ≤ e^{−t²/(2σ²)}` for `t ≥ 0`
  (Mathlib: `HasSubgaussianMGF` for Gaussians via `mgf_gaussianReal` + `measure_ge_le`).
* lem:gauss_mean_concentration — `η_1..η_n` i.i.d. `\Normal(0,1)`: `\Prob(|\frac1nΣη_i| ≥ t) ≤ 2e^{−nt²/2}`;
  in particular `|\bar y − μ| ≤ ε/2` w.p. ≥ 1−δ when `n ≥ 8\log(2/δ)/ε²`.
* lem:sup_countable_dense — `\Xs ⊆ \R^d` compact, `D ⊆ \Xs` countable dense: for every `v`,
  `\sup_{x∈\Xs}\ip{x}{v} = \sup_{x∈D}\ip{x}{v}` (= max, attained), hence `v ↦ \sup_{x∈\Xs}\ip{x}{v}`
  is measurable (even continuous, convex, Lipschitz with constant `\sup_{x∈\Xs}‖x‖`).
* lem:gauss_max_upper — centered Gaussians `Z_1..Z_m` (any dependence) with `\Var Z_i ≤ σ²`:
  `\E\max_i Z_i ≤ σ\sqrt{2\log m}` (Jensen: `\E\max ≤ β^{-1}\log Σ\E e^{βZ_i}`, optimize `β`).
* lem:gauss_comparison — (covariance domination) `\Xs` compact, `S_X ⪯ S_Y` in `\PSD`,
  `G_X ∼ \Normal(0,S_X)`, `G_Y ∼ \Normal(0,S_Y)`: `\E\sup_{x∈\Xs}\ip{x}{G_X} ≤ \E\sup_{x∈\Xs}\ip{x}{G_Y}`.
  Proof: let `G_X` and `G_Z ∼ \Normal(0, S_Y − S_X)` be independent; `G_X + G_Z ∼ \Normal(0,S_Y)`
  (lem:gauss_joint_linear, lem:gauss_law_of_cov); conditionally on `G_X` (Fubini),
  `\E[\sup_x(\ip{x}{G_X} + \ip{x}{G_Z}) | G_X] ≥ \sup_x(\ip{x}{G_X} + \E\ip{x}{G_Z}) = \sup_x\ip{x}{G_X}`.
  Also state the finite-index version (a finite family of centered Gaussians whose covariance
  matrices are ordered).

---------------------------------------------------------------------------------------------

## prereq_concentration.tex — `\chapter{Gaussian concentration and the Borell--TIS inequality}\label{chap:pre_concentration}`

Constant `\cG := π²/4`. Mathlib: `HasSubgaussianMGF X c μ` (`Mathlib/Probability/Moments/SubGaussian.lean`)
with `measure_ge_le`, `measure_le_le` (LML), `cgf_le`; `ConvexOn.map_integral_le` (Jensen);
`integral_gaussian`; `HasFDerivAt`, FTC `intervalIntegral.integral_eq_sub_of_hasDerivAt`.
* lem:gauss_mgf_inner — `g' ∼ \Normal(0,I_d)`, `a ∈ \R^d`: `\E e^{\ip{a}{g'}} = e^{‖a‖²/2}`.
* lem:logsumexp_props — `x_1..x_m ∈ \R^d`, `β > 0`, `f_β(v) := β^{-1}\log Σ_i e^{β\ip{x_i}{v}}`:
  `f_β` is `C^∞`, `∇f_β(v) = Σ_i p_i(v)x_i` with `p(v)` in the simplex, so `‖∇f_β(v)‖ ≤ \max_i‖x_i‖`;
  `\max_i\ip{x_i}{v} ≤ f_β(v) ≤ \max_i\ip{x_i}{v} + (\log m)/β`.
* lem:maurey_pisier — `f : \R^d → \R` of class `C^1` with `‖∇f‖ ≤ L` everywhere (hence Lipschitz),
  `g ∼ \Normal(0,I_d)`: `f(g)` integrable and for all `λ∈\R`,
  `\E\exp(λ(f(g) − \E f(g))) ≤ \exp(π²λ²L²/8)`, i.e. `f(g) − \E f(g)` has sub-Gaussian MGF with
  constant `\cG L²`. Proof (the paper does not contain it; standard, e.g. Pisier 1986): independent
  copy `g'`; Jensen in `g'`: `\E e^{λ(f(g)−\E f)} ≤ \E e^{λ(f(g)−f(g'))}`;
  `g_θ := g\sinθ + g'\cosθ`, `g'_θ := g\cosθ − g'\sinθ`; `f(g) − f(g') = ∫_0^{π/2}\ip{∇f(g_θ)}{g'_θ}dθ`
  (chain rule + FTC); Jensen for the uniform probability on `[0,π/2]`:
  `\exp(λ∫_0^{π/2}h) ≤ \frac2π∫_0^{π/2}\exp(\frac{π}{2}λh(θ))dθ`; Fubini and lem:gauss_rotation:
  `\E\exp(\frac{πλ}{2}\ip{∇f(g_θ)}{g'_θ}) = \E\exp(\frac{πλ}{2}\ip{∇f(g)}{g'})`; condition on `g`
  (Fubini, independence) and lem:gauss_mgf_inner: `≤ \E\exp(π²λ²‖∇f(g)‖²/8) ≤ \exp(π²λ²L²/8)`.
* lem:finite_sup_subgaussian — `x_1..x_m ∈ \R^d`, `G ∼ \Normal(0,S)`, `S ∈ \PSD`,
  `M := \max_i\ip{x_i}{G}`, `σ² := \max_i x_i^⊤Sx_i`: `M − \E M` has sub-Gaussian MGF with constant `\cG σ²`.
  Proof: `G = S^{1/2}g`, apply lem:maurey_pisier to `f_β` with the vectors `S^{1/2}x_i`
  (`L = σ`), then `β → ∞` using lem:logsumexp_props (`|M − f_β(g)| ≤ (\log m)/β` a.s. and
  `|\E M − \E f_β| ≤ (\log m)/β`).
* lem:compact_sup_subgaussian — `\Xs ⊆ \R^d` compact, `G ∼ \Normal(0,S)`, `M := \sup_{x∈\Xs}\ip{x}{G}`,
  `σ² := \sup_{x∈\Xs}x^⊤Sx`: `M − \E M` has sub-Gaussian MGF with constant `\cG σ²`. Proof: countable
  dense `D = {q_n}` (lem:sup_countable_dense), `M_n := \max_{i≤n}\ip{q_i}{G} ↑ M`; MGF bound for each
  `n` from lem:finite_sup_subgaussian (`σ_n ≤ σ`); pass to the limit by dominated convergence
  (`|M_n| ≤ \sup_x‖x‖\,‖G‖`, `e^{λ M_n} ≤ e^{|λ|\sup‖x‖‖G‖}` integrable since Gaussian norms have all
  exponential moments — Mathlib Fernique or directly `\E e^{c‖g‖} ≤ Π\E e^{c|g_i|}`); `\E M_n → \E M`
  by monotone convergence.
* thm:borell_tis — (linear processes) same setting: for `u ≥ 0`,
  `\Prob(M − \E M ≥ u) ≤ \exp(−u²/(2\cG σ²))` and `\Prob(M − \E M ≤ −u) ≤ \exp(−u²/(2\cG σ²))`
  (Mathlib `HasSubgaussianMGF.measure_ge_le`/`measure_le_le`). Remark: the sharp constant is `\cG = 1`
  (Gaussian isoperimetry / log-Sobolev); not pursued.
* cor:sup_bound_whp — for `δ ∈ (0,1)`: `\Prob(M ≤ \E M + σ\sqrt{2\cG\log(1/δ)}) ≥ 1−δ`.
* cor:sup_bound_symmetric — for the index set `\Xs − \Xs := {x − x'}` (compact): `D := \sup_{x,x'}\ip{x−x'}{G}`,
  `\E D = 2\E\sup_x\ip{x}{G}` and `\Prob(D ≤ \E D + 2σ\sqrt{2\cG\log(1/δ)}) ≥ 1−δ`
  (`σ²_{\Xs−\Xs} ≤ 4σ²`).

---------------------------------------------------------------------------------------------

## prereq_subexp.tex — `\chapter{Sub-exponential random variables}\label{chap:pre_subexp}`

Definition mirrors the paper (Appendix D.1) and Mathlib's `HasSubgaussianMGF` design (a structure
with integrability + the MGF bound), kernel/measure versions not needed.
* def:subexp — `X` real random variable, `V ≥ 0`, `b > 0`: `HasSubexponentialMGF X V b` iff `X` is
  a.e.-measurable and for all `|λ| ≤ 1/b`, `e^{λX}` is integrable with `\E e^{λX} ≤ e^{λ²V/2}`.
  Remarks: implies `\E X = 0`? (No: only "`\E X ≤ 0` and `≥ 0`" via `λ → 0±`: yes it implies
  `\E X = 0` when `X` integrable; state and prove: `(\E e^{λX} − 1)/λ → \E X` and the bound gives ≤ 0
  from both sides.)
* lem:subexp_of_subgaussian — `HasSubgaussianMGF X c` ⟹ `HasSubexponentialMGF X c b` for every `b > 0`.
* lem:subexp_const_mul — `HasSubexponentialMGF X V b` ⟹ `HasSubexponentialMGF (aX) (a²V) (|a|b)` for `a ≠ 0`.
* lem:subexp_tail — `\Prob(X ≥ t) ≤ \exp(−\min(t²/(2V), t/(2b)))` for `t ≥ 0`, same for `\Prob(X ≤ −t)`
  (Chernoff with `λ = \min(t/V, 1/b)`; paper's Lemma 2 computation with `c = 1/2`).
* lem:subexp_sum — independent `X_1..X_K` with parameters `(V_i, b)`: `ΣX_i` has `(ΣV_i, b)`.
* cor:subexp_average_tail — same: `\Prob(|\frac1KΣX_i| > t) ≤ 2\exp(−K\min(t²/(2\bar V), t/(2b)))`,
  `\bar V := \frac1KΣV_i` (lem:subexp_const_mul with `a = 1/K` gives `(\bar V/K, b/K)`).
* lem:gaussian_square_mgf — `X ∼ \Normal(μ,σ²)`, `λ < 1/(2σ²)`:
  `\E e^{λX²} = (1−2σ²λ)^{-1/2}\exp(μ²λ/(1−2σ²λ))` (Mathlib `integral_cexp_quadratic` or direct
  completion of the square with `integral_gaussian`).
* lem:log_ineq_nu — for `|ν| ≤ 1/2`: `−½\log(1−ν) − ν/2 ≤ ν²` and `|1/(1−ν) − 1| ≤ 2|ν|`.
* lem:gaussian_square_subexp — `X ∼ \Normal(μ,σ²)`: `X² − (μ²+σ²)` has `(8(σ⁴+μ²σ²), 4σ²)`
  (paper's Lemma 1, proof there).
* lem:chi_square_subexp — `g ∼ \Normal(0,I_d)`: `‖g‖² − d` has `(8d, 4)` (lem:subexp_sum);
  lem:chi_square_tail — `\Prob(‖g‖² − d ≥ t) ≤ \exp(−\min(t²/(16d), t/8))`, and
  `\Prob(‖g‖² ≥ 2d + 12\log(1/δ)) ≤ δ` (take `t = \max(4\sqrt{dL}, 8L)`, `L = \log(1/δ)`, AM–GM).
* lem:gauss_quadratic_form_subexp — `S ∈ \PSD`, `g ∼ \Normal(0,I_d)`: `g^⊤Sg − \tr S` has
  `(8\tr(S²), 4‖S‖_{op})` (diagonalize with an orthogonal `U`; `U^⊤g ∼ \Normal(0,I)` by lem:gauss_rotation
  generalized to orthogonal maps; sum of `s_i(g_i² − 1)`, lem:subexp_const_mul, lem:subexp_sum).
* lem:rademacher_linear_subgaussian — `ε` i.i.d. uniform signs, `θ ∈ \R^d`: `\ip{ε}{θ}` has
  `HasSubgaussianMGF` with constant `‖θ‖²` (Mathlib Hoeffding lemma `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`
  per coordinate + `HasSubgaussianMGF.add` / `sum` for independent variables).
* lem:rademacher_fourth_moment — `\E\ip{ε}{θ}⁴ = 3‖θ‖⁴ − 2Σ_iθ_i⁴ ≤ 3‖θ‖⁴`, `\E\ip{ε}{θ}² = ‖θ‖²`.
* lem:subgaussian_square_mgf_pos — `Z` with `HasSubgaussianMGF Z K²`, `0 ≤ λ < 1/(2K²)`:
  `\E e^{λZ²} ≤ (1−2K²λ)^{-1/2}`. Proof: `e^{λz²} = \E_{g'}e^{\sqrt{2λ}zg'}` for `g' ∼ \Normal(0,1)`
  independent; Fubini; `\E_Z e^{sZ} ≤ e^{K²s²/2}` with `s = \sqrt{2λ}g'`; lem:gaussian_square_mgf with `μ = 0`.
* lem:rademacher_square_subexp — `Z := \ip{ε}{θ}`, `r := ‖θ‖ > 0`: `Z² − r²` has `(16r⁴, 4r²)`.
  Proof: for `0 ≤ λ ≤ 1/(4r²)`: lem:subgaussian_square_mgf_pos and lem:log_ineq_nu with `ν = 2r²λ`
  give `\E e^{λ(Z²−r²)} ≤ e^{ν²} = e^{4r⁴λ²} ≤ e^{λ²·16r⁴/2}`; for `−1/(4r²) ≤ λ < 0`:
  `e^{λz²} ≤ 1 + λz² + λ²z⁴/2` (for `λz² ≤ 0`), so `\E e^{λZ²} ≤ 1 + λr² + λ²·3r⁴/2 ≤ e^{λr² + 3r⁴λ²/2}`
  and `\E e^{λ(Z²−r²)} ≤ e^{3r⁴λ²/2} ≤ e^{λ²·16r⁴/2}`.

---------------------------------------------------------------------------------------------

## prereq_info.tex — `\chapter{Information-theoretic tools and the divergence decomposition}\label{chap:pre_info}`

Mathlib: `ProbabilityTheory.klDiv μ ν` (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`,
an `ℝ≥0∞`-valued `irreducible_def`), `klDiv_compProd_eq_add`, `klDiv_compProd_left`
(`ChainRule.lean`), `klDiv_map_le`, `klDiv_comp_right_le` (data processing, `DataProcessing.lean`),
`klFun`, `mul_log_le_klDiv`. LML: `Learning.trajMeasure`, `IsAlgEnvSeq`, `stationaryEnv`,
`Algorithm.density`/`hasLaw_history_withDensity` (`SequentialLearning/AlgorithmDensity.lean`, a
density for changing the *algorithm*; the environment analogue is what we need).
Check whether Mathlib has the KL of two real Gaussians and Pinsker; state them anyway.
* lem:kl_gaussian — `\KL(\Normal(μ_1,1)‖\Normal(μ_2,1)) = (μ_1−μ_2)²/2` (densities, `llr` explicit).
* lem:kl_bernoulli_pinsker — `p,q ∈ (0,1)`: `p\log(p/q) + (1−p)\log((1−p)/(1−q)) ≥ 2(p−q)²`.
* lem:pinsker — probability measures `μ,ν`, measurable `A`: `μ(A) − ν(A) ≤ \sqrt{\KL(μ‖ν)/2}`
  (data processing along `\indic_A` to the two-point space: `klDiv_map_le`, then lem:kl_bernoulli_pinsker;
  trivial if `\KL = ∞`).
* lem:bretagnolle_huber — `μ(A) + ν(A^c) ≥ ½\exp(−\KL(μ‖ν))`. Proof: with densities `p,q` w.r.t. `μ+ν`,
  `μ(A) + ν(A^c) ≥ ∫\min(p,q)`, `(∫\sqrt{pq})² ≤ ∫\min(p,q)·∫\max(p,q) ≤ 2∫\min(p,q)`, and
  `∫\sqrt{pq} = \E_μ e^{−½\log(p/q)} ≥ e^{−½\KL}` (Jensen). (Lattimore–Szepesvári Thm 14.2.)
* lem:kl_mixture_convex — `ν = Σ_j c_jν_j` finite mixture, `c` probability vector:
  `\KL(μ‖ν) ≤ Σ_jc_j\KL(μ‖ν_j)` (concavity of `\log` applied to `dν/dμ = Σc_j dν_j/dμ`).
* lem:kl_compProd_kernel — `\KL(μ⊗κ ‖ μ⊗η) = ∫\KL(κ_x‖η_x)dμ(x)` for Markov kernels `κ,η` (check
  Mathlib `ChainRule.lean`; if absent, prove from `rnDeriv_compProd`-type lemmas).
* def:env_pair — two stationary environments `ν, ν'` on the same action space with reward kernels
  `κ, κ' : \mathrm{Kernel}\ \Xs\ \R`; an algorithm `alg`; `\Prob^T`, `\Prob'^T` the laws of the
  history of length `T` (`Learning.trajMeasure` projected by `frestrictLe`).
* thm:divergence_decomposition — `\KL(\Prob^T ‖ \Prob'^T) = Σ_{t<T}\E_{\Prob}[\KL(κ(x_t)‖κ'(x_t))]`.
  Proof: induction on `T`; the history of length `T+1` is `(\hist_T) ⊗ (\text{policy}_T ⊗ \text{feedback})`
  (LML `history_succ`, `hasCondDistrib_step`); `klDiv_compProd_eq_add` splits off `\KL(\Prob^T‖\Prob'^T)`,
  `klDiv_compProd_left` kills the (common) policy kernel, lem:kl_compProd_kernel gives the expectation
  of the one-step KL. Include the measure-theoretic details (Markov kernels, `IsFiniteMeasure`).
* lem:kl_data_processing_recommendation — adding the recommendation `\rec ∼ ρ(\hist_T)` (same kernel
  under both environments) does not change the KL: `\KL(\Prob^T⊗ρ ‖ \Prob'^T⊗ρ) = \KL(\Prob^T‖\Prob'^T)`
  (`klDiv_compProd_left`); and for any event `E` of `(\hist_T,\rec)`, Pinsker/BH apply with this KL.
* cor:divergence_decomposition_gaussian — linear Gaussian environments `ν_θ, ν_{θ'}` (def:env):
  `\KL(\Prob_θ^T‖\Prob_{θ'}^T) = ½Σ_{t<T}\E_θ[\ip{x_t}{θ−θ'}²]` (lem:kl_gaussian).

---------------------------------------------------------------------------------------------

## prereq_sudakov.tex — `\chapter{The Sudakov--Fernique inequality}\label{chap:pre_sudakov}`

Secondary (only feeds prop:width_lower_sqrt_dlogd). Reference: Vershynin, HDP, Theorem 7.2.11
(Gaussian interpolation proof); Chatterjee's proof of Sudakov–Fernique.
* lem:gauss_ibp — (multivariate Stein) `X ∼ \Normal(0,S)` on `\R^m`, `F : \R^m→\R` `C^1` with `F, ∇F`
  of at most exponential growth: `\E[X_iF(X)] = Σ_jS_{ij}\E[∂_jF(X)]`.
* lem:interpolation_derivative — `X ∼ \Normal(0,S_X)`, `Y ∼ \Normal(0,S_Y)` independent, `F` `C^2`
  with bounded second derivatives, `Z_t := \sqrt t X + \sqrt{1−t}Y`:
  `\frac{d}{dt}\E F(Z_t) = ½Σ_{i,j}(S_X − S_Y)_{ij}\E[∂_{ij}F(Z_t)]`.
* lem:logsumexp_hessian — `F_β(z) = β^{-1}\log Σ_ie^{βz_i}`: `∂_{ij}F_β = β(δ_{ij}p_i − p_ip_j)`, and for
  any symmetric `Γ`, `Σ_{ij}Γ_{ij}∂_{ij}F_β = −\frac{β}{2}Σ_{i,j}p_ip_j(Γ_{ii} + Γ_{jj} − 2Γ_{ij})`.
* thm:sudakov_fernique — centered Gaussian vectors `X, Y` in `\R^m` with `\E(X_i−X_j)² ≤ \E(Y_i−Y_j)²`
  for all `i,j`: `\E\max_iX_i ≤ \E\max_iY_i`. Proof: `\E F_β(Z_t)` is nondecreasing in `t` from
  `Y` (`t=0`) to `X`?? Orient it: with `Z_t = \sqrt tX + \sqrt{1−t}Y`, derivative
  `= −\frac{β}{4}Σp_ip_j(\E(X_i−X_j)² − \E(Y_i−Y_j)²) ≥ 0`, so `\E F_β(X) ≥ \E F_β(Y)`?? Careful:
  we need `\E\max X ≤ \E\max Y` under `\E(X_i−X_j)² ≤ \E(Y_i−Y_j)²`, so the derivative should be ≤ 0:
  `Γ = S_X − S_Y`, `Γ_{ii}+Γ_{jj}−2Γ_{ij} = \E(X_i−X_j)² − \E(Y_i−Y_j)² ≤ 0`, giving
  `\frac{d}{dt}\E F_β(Z_t) = −\frac{β}{4}Σp_ip_j(…) ≥ 0`. Hmm: then `\E F_β(X) ≥ \E F_β(Y)`, wrong
  direction. Re-derive carefully (the standard statement: increments of `X` smaller ⟹ `\E\max X`
  smaller); the sign comes out right when done correctly (Vershynin 7.2.11 uses `Z_t = \sqrt tX + \sqrt{1−t}Y`
  and shows `\frac{d}{dt}\E F_β(Z_t) ≤ 0`). Write the correct derivation; then `β→∞`.
  Extension to compact index sets by density (lem:sup_countable_dense) is not needed.
* lem:gauss_tail_lower — `ξ ∼ \Normal(0,1)`, `t ≥ 1`: `\Prob(ξ ≥ t) ≥ \frac{t}{1+t²}\frac{e^{−t²/2}}{\sqrt{2π}}`.
* lem:gauss_max_lower — `ξ_1..ξ_m` i.i.d. standard, `m ≥ 2`: `\E\max_iξ_i ≥ c_{max}\sqrt{\log m}` with an
  explicit `c_{max}` (route: second-moment/Paley–Zygmund on `N_t := #\{i : ξ_i ≥ t\}` with
  `t = \sqrt{\log m}` (or `\sqrt{\log m}/2`), `\Prob(\max ≥ t) ≥ 1 − (1−p_t)^m ≥ 1 − e^{−mp_t}`,
  and `\E\max ≥ t\Prob(\max ≥ t) − \E|ξ_1|`). Give the constant you obtain and the range of `m`.

---------------------------------------------------------------------------------------------

## prereq_median.tex — `\chapter{Median Elimination}\label{chap:pre_median}`

Reference: Even-Dar, Mannor, Mansour (2002/2006) "Action elimination and stopping conditions for
the multi-armed bandit and reinforcement learning problems", Theorem 10. LML: `stationaryEnv`,
`pullCount`, `empMean`/`sumRewards` (`SequentialLearning/FiniteActions.lean`, `Online/Bandit/*`).
Setting: `K ≥ 1` arms, stationary environment with reward kernel `ν : \mathrm{Kernel}\ (\mathrm{Fin}\ K)\ \R`
such that each `ν a` has mean `μ_a` and `ν a − μ_a` has `HasSubgaussianMGF` with constant `1`
(Gaussian `\Normal(μ_a,1)` is the case used).
* def:me_schedule — `ε_1 := ε/4`, `δ_1 := δ/2`, `ε_{ℓ+1} := 3ε_ℓ/4`, `δ_{ℓ+1} := δ_ℓ/2`;
  `n_ℓ := ⌈8\log(3/δ_ℓ)/ε_ℓ²⌉`; lem:me_schedule_sums — `Σ_ℓε_ℓ ≤ ε`, `Σ_ℓδ_ℓ ≤ δ`.
* def:median_elimination — `S_1 := [K]`; round `ℓ`: pull each `a ∈ S_ℓ` `n_ℓ` times, `\hat μ_a` the
  empirical mean of these pulls, `S_{ℓ+1} :=` the `⌈|S_ℓ|/2⌉` arms of `S_ℓ` with the largest `\hat μ_a`
  (ties by index); stop when `|S_ℓ| = 1`, recommend its element. Deterministic budget: the number of
  rounds is `⌈\log_2K⌉` and the budget is `N_{ME}(K,ε,δ) := Σ_ℓ|S_ℓ|n_ℓ` (a deterministic function).
  Encode as an LML algorithm (deterministic next action = round-robin over `S_ℓ`, determined by the
  history) plus recommendation.
* lem:me_round — for each round `ℓ`, conditionally on `S_ℓ` (lem:composition or a direct
  filtration argument): `\Prob(\max_{a∈S_ℓ}μ_a ≤ \max_{a∈S_{ℓ+1}}μ_a + ε_ℓ) ≥ 1 − δ_ℓ`.
  Proof: `a_*` best in `S_ℓ`; `E_1 := \{\hat μ_{a_*} < μ_{a_*} − ε_ℓ/2\}`, `\Prob(E_1) ≤ δ_ℓ/3`
  (lem:gauss_tail / sub-Gaussian mean); an arm `a` is *bad* if `μ_a < μ_{a_*} − ε_ℓ` and
  `\hat μ_a ≥ \hat μ_{a_*}`; on `E_1^c`, bad ⟹ `\hat μ_a ≥ μ_a + ε_ℓ/2`, probability ≤ δ_ℓ/3 each;
  `\E[\#bad ; E_1^c] ≤ |S_ℓ|δ_ℓ/3`; Markov: `\Prob(\#bad ≥ |S_ℓ|/2) ≤ 2δ_ℓ/3`; if fewer than
  `|S_ℓ|/2` arms are bad-or-`a_*`-dominating then either `a_*` survives or a surviving arm is
  within `ε_ℓ` of `a_*` (median argument).
* lem:me_budget — `N_{ME}(K,ε,δ) ≤ C_{ME}K\log(1/δ)/ε²` hmm: give the exact bound
  `N_{ME} ≤ (128K/ε²)(9\log(3/δ) + 81\log 2) + 2K` and the form `≤ C_{ME}\,K\log(3/δ)/ε²` with explicit `C_{ME}`
  (use `ε ≤ 1`, `δ<1`).
* thm:median_elimination — Median Elimination with `(ε,δ)` on `K` sub-Gaussian arms returns `\hat a`
  with `\Prob(μ_{\hat a} ≥ \max_aμ_a − ε) ≥ 1 − δ`, with budget `N_{ME}(K,ε,δ)`.
* cor:median_elimination_linear — in the linear Gaussian environment (def:env), for candidates
  `x^{(1)},…,x^{(K)} ∈ \Xs` (possibly chosen from the past history), running Median Elimination on the
  induced `K`-armed bandit (arm `a` ↦ play `x^{(a)}`, mean `\ip{x^{(a)}}{θ}`) returns `\hat a` with
  `\ip{x^{(\hat a)}}{θ} ≥ \max_a\ip{x^{(a)}}{θ} − ε` w.p. ≥ 1−δ (the induced environment is a
  stationary `K`-armed Gaussian environment: `stationaryEnv` composed with the map `a ↦ x^{(a)}`).

---------------------------------------------------------------------------------------------

## prereq_bayes.tex — `\chapter{Gaussian posteriors for adaptively collected data and the unit-ball lower bound}\label{chap:pre_bayes}`

Replaces the citation of Chen et al. (2024) in Appendix H. Setting: `\Xs = \ball_d` (or any `\Xs ⊆ \ball_d`),
adaptive algorithm with budget `T` (def:bai_alg), prior `θ ∼ \Normal(0,σ²I_d)`, `σ² := d/(4T)`.
* lem:env_likelihood_ratio — for `θ ∈ \R^d`, the law `\Prob_θ^T` of the history of length `T` under
  `ν_θ` (def:env) is absolutely continuous w.r.t. `\Prob_0^T` with density
  `ℓ_θ(h) := \exp(Σ_{t<T}(y_t\ip{x_t}{θ} − ½\ip{x_t}{θ}²))`. Proof: induction on `T` using the step
  decomposition of LML (`history_succ`, `hasCondDistrib_step`), the Gaussian density ratio
  `d\Normal(m,1)/d\Normal(0,1)(y) = e^{ym − m²/2}`, and the fact that the policy kernel is common
  (this is the environment analogue of LML's `Algorithm.density`; state it for general stationary
  environments with kernels `κ_θ ≪ κ_0` having densities `ρ_θ(x,y)`, then specialize).
* def:bayes_joint — the joint law of `(θ, \hist_T, \rec)`: `\Normal(0,σ²I) ⊗ (θ ↦ \Prob_θ^T ⊗ ρ)`;
  `S_T := Σ_{t<T}x_tx_t^⊤`, `b_T := Σ_{t<T}y_tx_t`, `V_T := (σ^{-2}I + S_T)^{-1}`, `m_T := V_Tb_T`
  (functions of the history).
* lem:gaussian_complete_square — for `S ∈ \PSD`, `b ∈ \R^d`, `V := (σ^{-2}I + S)^{-1}`, `m := Vb`:
  `∫(θ − m)\exp(\ip{b}{θ} − ½θ^⊤Sθ)\,\Normal(0,σ²I)(dθ) = 0` and
  `∫‖θ − m‖²\exp(\ip{b}{θ} − ½θ^⊤Sθ)\,\Normal(0,σ²I)(dθ) = \tr(V)·∫\exp(\ip{b}{θ} − ½θ^⊤Sθ)\Normal(0,σ²I)(dθ)`
  (the integrand is a multiple of the `\Normal(m,V)` density: lem:gauss_linear_image, lem:gauss_norm_moments).
* lem:posterior_mean — for every bounded measurable `φ` of `(\hist_T,\rec)` with values in `\R^d`:
  `\E\ip{φ}{θ − m_T} = 0` (Fubini + lem:env_likelihood_ratio + lem:gaussian_complete_square).
* lem:posterior_second_moment — `\E‖θ − m_T‖² = \E\tr V_T` and `\E‖m_T‖² = σ²d − \E\tr V_T`.
* lem:trace_inv_lower — `‖x_t‖ ≤ 1`: `\tr V_T ≥ d²/(dσ^{-2} + T)` (lem:trace_inv_amhm, `\tr S_T ≤ T`).
* lem:bayes_regret_ball — `\E[r(\rec,θ)] = \E‖θ‖ − \E\ip{\rec}{θ} ≥ \E‖θ‖ − \E‖m_T‖` (lem:posterior_mean
  with `φ = \rec`, `‖\rec‖ ≤ 1`), and `\E‖θ‖ ≥ σd/\sqrt{d+2}` (lem:gauss_norm_moments),
  `\E‖m_T‖ ≤ \sqrt{σ²d − d²/(dσ^{-2}+T)}`.
* thm:ball_simple_regret_lower — `d ≥ 2`, `σ² = d/(4T)`: `\E[r(\rec,θ)] ≥ 0.13\,d/\sqrt T` under the
  prior; and there exists `θ` with `‖θ‖ ≤ 8d/\sqrt T` and `\E_θ[r(\rec,θ)] ≥ d/(15\sqrt T)`
  (truncation: `\E[2‖θ‖\indic\{‖θ‖ > 16σ\sqrt d\}] ≤ 2σ\sqrt d\sqrt{\Prob(‖g‖² > 256d)} ≤ 2σ\sqrt d/16`
  by Cauchy–Schwarz and Markov). Verify the arithmetic (`√(1/4)·√(1/2) − (1/4)/√(5/4) ≥ 0.13`).
* cor:ball_pac_lower — any `(ε,δ)`-PAC algorithm on `\ball_d` (`d ≥ 2`) with `δ ≤ 1/500` has
  `T ≥ d²/(1000ε²)`: lem:pac_expected_regret-style bound `\E_θ r ≤ ε + 2‖θ‖δ ≤ ε + 16dδ/\sqrt T`
  for the `θ` of the theorem, so `(1/15 − 16δ)d/\sqrt T ≤ ε`.
