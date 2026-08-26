# Blueprint outline (authoritative label list and proof routes)

This file is the contract between the chapter files of `blueprint/src/chapters/`. Every
label below is fixed: chapters may only `\uses{}` labels listed here (or labels they define
themselves). If a chapter needs a lemma that is not listed, define it locally with a new label
prefixed by the chapter's short name and do not reference it from other chapters.

## Global conventions (all chapters)

* Style reference: `blueprint/src/chapters/model.tex` (read it first). Each item is a
  `definition`/`lemma`/`proposition`/`theorem`/`corollary`/`remark` environment with a
  `\label{...}`, a `\uses{...}` line right after the label listing the labels of the
  definitions and lemmas the *statement* needs, and a `\begin{proof} ... \end{proof}` whose
  `\uses{...}` (first line inside the proof) lists what the *proof* needs. Proofs must be
  complete proof sketches at the level of detail of a careful paper, decomposed so that each
  lemma is a plausible single Lean declaration. Add `\textbf{Lean remark.}` paragraphs
  wherever the encoding is non-obvious (name Mathlib/LML declarations when known).
* `theorem` only for the paper's headline results and big classical theorems; everything else
  `lemma`/`proposition`/`corollary`.
* Paper source: `source/results.tex` (main text) and `source/appendix.tex` (proofs). Cite it
  by section, not by line. The deviations from the paper listed in
  `blueprint/src/content.tex` are decisions, not suggestions: follow them.
* Macros (see `blueprint/src/macros/common.tex`): `\R \N \E \Prob \Var \indic \ip{}{}
  \norm{} \abs{} \Xs \ball \sphere \simplex \designset \gw \gwidth{}{} \KL \TV \tr \supp
  \Span \conv \eps \Normal \hist \rec \cG \PD \PSD \Sym \eqd \argmax \argmin`. No other
  packages: plasTeX cannot parse `enumitem`; use `enumerate` with `\item[(i)]`. No `\ref` to
  equations defined with `\label` inside `align`? Fine in plasTeX, but prefer naming
  displayed equations sparingly. No `\newcommand` inside chapters. No tables (use itemize).
* Time is 0-indexed: rounds `t < T`, sums `\sum_{t<T}`. Probability space `(\Omega,\Prob)`.
  Reward-vector dependence: `\Prob_\theta`, `\E_\theta`. `\norm{x}_W^2 := x^\top W x`.
  `\cG := \pi^2/4` is the Gaussian concentration constant (Chapter pre_concentration).
* Constants: give explicit admissible constants where the outline gives them; where it says
  "explicit constant" derive one and state it. Never write `O(\cdot)` in a statement that is
  meant to be formalized; put the asymptotic form in a remark.
* Chapter/section labels: `chap:<name>`, `sec:<name>_<sub>`.
* Each chapter starts with `\chapter{...}\label{chap:...}` and an introductory paragraph
  stating what the chapter proves, what it uses from Mathlib/LML, and what is new.

## Labels defined in model.tex (already written)

def:arm_set, def:env, lem:noise_representation, def:bai_alg, def:regret, def:pac,
lem:pac_expected_regret, rem:stopping_times, def:fixed_design, lem:fixed_design_law,
def:design_matrix, lem:designset_basic, lem:exists_posdef_design, def:width_matrix,
lem:width_matrix_wd, def:width, lem:width_homog, lem:width_mono, lem:width_iso,
lem:width_empirical, lem:width_symm, lem:composition.

Notes: `def:pac` and lower bounds make sense for any compact `\Xs` (spanning is only used
for widths and upper bounds). `lem:composition` is the sequential composition of algorithms.
`Z(\theta) = \max_{x,y}\ip{x-y}{\theta}` is defined in def:regret.

---------------------------------------------------------------------------------------------

## design.tex — `\chapter{Optimal experimental design and rounding}\label{chap:design}`

Sections: `sec:design_loewner`, `sec:design_kw`, `sec:design_caratheodory`, `sec:rounding`.

### sec:design_loewner (linear algebra facts, Mathlib's Loewner order `Matrix.instPartialOrder`
scoped `MatrixOrder`, `CFC.sqrt`, `Matrix.PosDef`)
* lem:loewner_congruence — `A ⪯ B ⟹ M A M^⊤ ⪯ M B M^⊤` for any `M`.
* lem:loewner_quadratic — `A ⪯ B ⟹ x^⊤ A x ≤ x^⊤ B x`; and `A ⪯ B` iff this for all x.
* lem:loewner_inv — `0 ≺ A ⪯ B ⟹ B^{-1} ⪯ A^{-1}`. Proof: congruence by `A^{-1/2}` gives
  `I ⪯ A^{-1/2} B A^{-1/2}`, so all eigenvalues of `C := A^{-1/2}BA^{-1/2}` are ≥ 1, so
  `C^{-1} ⪯ I` (spectral theorem, `Matrix.IsHermitian.spectral_theorem`), congruence back.
* lem:loewner_scalar — `c A ⪯ B` with `c>0`, `A ≻ 0`: `B^{-1} ⪯ c^{-1} A^{-1}` (corollary).
* lem:eigen_quadratic_bounds — for `A ≻ 0`: `λ_min ‖x‖² ≤ x^⊤ A x ≤ λ_max ‖x‖²`,
  `‖A‖_op = λ_max`, `tr A = Σ λ_i`, `tr(A²) = Σ λ_i² ≤ d λ_max²`.
* lem:trace_inv_amhm — `A ≻ 0`: `tr(A^{-1}) ≥ d² / tr(A)` (AM–HM on eigenvalues).
* lem:sqrt_props — `A ≻ 0`: `A^{1/2} ≻ 0`, `A^{-1/2} = (A^{1/2})^{-1} = (A^{-1})^{1/2}`,
  `A^{-1/2} A A^{-1/2} = I`, `x^⊤A^{-1}x = ‖A^{-1/2}x‖²` (Mathlib `CFC.sqrt`, `inv_sqrt`).

### sec:design_kw (Kiefer–Wolfowitz; replaces John's theorem)
* def:g_value — for `A ∈ \PD`: `g_\Xs(A) := \max_{x∈\Xs} x^⊤ A^{-1} x` (compactness).
* lem:g_ge_d — for `λ ∈ \simplex_\Xs` with `A(λ) ≻ 0`: `Σ_x λ_x x^⊤A(λ)^{-1}x = tr(I_d) = d`,
  hence `g(A(λ)) ≥ d`, and if `g(A(λ)) = d` then every `x ∈ supp λ` has `x^⊤A(λ)^{-1}x = d`.
* def:d_optimal — `A_D ∈ \designset(\Xs)` maximizing `det` over `\designset(\Xs)`.
* lem:exists_d_optimal — exists (det continuous, set compact by lem:designset_basic); and
  `det A_D > 0`, i.e. `A_D ≻ 0` (lem:exists_posdef_design gives a competitor with det > 0;
  PSD with positive det is PD).
* lem:logdet_directional — `A ≻ 0`, `M` symmetric: `t ↦ (log det(A+tM) − log det A)/t → tr(A^{-1}M)`
  as `t → 0+`. Proof: `det(A+tM) = det A · det(I + t C)`, `C = A^{-1/2} M A^{-1/2}` symmetric
  with eigenvalues `μ_i`; `log det(I+tC) = Σ log(1+tμ_i)`; `log(1+tμ)/t → μ`; `Σ μ_i = tr C = tr(A^{-1}M)`.
* thm:kiefer_wolfowitz — there is `λ_G ∈ \simplex_\Xs` with `A_G := A(λ_G) ≻ 0` and
  `g(A_G) = d` (`G`-optimal design); moreover every `x ∈ supp λ_G` satisfies `x^⊤A_G^{-1}x = d`,
  and `|supp λ_G| ≤ d(d+1)/2 + 1`. Proof: take `A_D` (lem:exists_d_optimal) written as `A(λ)`
  (lem:caratheodory_design); for `x ∈ \Xs`, `B = xx^⊤ ∈ \designset`, `A_D + t(B − A_D) ∈ \designset`
  for `t∈[0,1]` (convexity), so by maximality and lem:logdet_directional
  `tr(A_D^{-1}(xx^⊤ − A_D)) ≤ 0`, i.e. `x^⊤A_D^{-1}x ≤ d`; with lem:g_ge_d, `= d` is attained.
* cor:g_optimal_norm_bound — for all `x ∈ \Xs`: `‖A_G^{-1/2} x‖² ≤ d`.
* cor:g_optimal_normalized — set `v_x := A_G^{-1/2} x / \sqrt d` for `x ∈ supp λ_G`: then
  `‖v_x‖ = 1`, `Σ_x λ_{G,x} v_x v_x^⊤ = I_d / d`, and the transformed action set
  `\Xs' := (1/\sqrt d) A_G^{-1/2}\Xs ⊆ \ball_d` contains all `v_x`. (Used by lower_adaptive.)

### sec:design_caratheodory
* lem:caratheodory_design — every `A ∈ \designset(\Xs)` equals `A(λ)` for some
  `λ ∈ \simplex_\Xs` with `|supp λ| ≤ d(d+1)/2 + 1` (Mathlib `convexHull_eq_union` /
  Carathéodory in the space of symmetric matrices, dimension `d(d+1)/2`).
* lem:width_matrix_continuous — `A ↦ \gwidth{\Xs}{A}` is continuous on `\PD` (dominated
  convergence; `A ↦ A^{-1/2}` continuous on `\PD`).
* lem:width_coercive — if `A_n ∈ \PD`, `A_n → A_∞` singular, then `\gwidth{\Xs}{A_n} → ∞`.
  Proof: `u` unit with `A_∞u = 0`, so `u^⊤A_nu → 0`. Since `\Span \Xs = \R^d` there are
  `x, x' ∈ \Xs` with `\ip{u}{x−x'} ≠ 0` (otherwise `\Xs ⊆ x_0 + u^⊥` with `\ip{u}{x_0}≠0`,
  and then `u^⊤A_nu = \ip{u}{x_0}^2` does not vanish — contradiction). Then
  `\gwidth{\Xs}{A} ≥ \E\max(\ip{A^{-1/2}x}{g}, \ip{A^{-1/2}x'}{g}) = \E|\ip{A^{-1/2}(x−x')}{g}|/2
  = ‖A^{-1/2}(x−x')‖/\sqrt{2π} ≥ |\ip{u}{x−x'}| / (\sqrt{2π}\,\sqrt{u^⊤A_nu}) → ∞`
  (Cauchy–Schwarz `\ip{u}{v} = \ip{A^{1/2}u}{A^{-1/2}v}`).
* lem:width_attained — there is `A_1 ∈ \designset(\Xs) ∩ \PD` with `\gwidth{\Xs}{A_1} = \gw(\Xs)`.
  Proof: minimizing sequence in the compact `\designset(\Xs)`; limit is PD by coercivity;
  continuity.

### sec:rounding (one-sided barrier, unit weights; replaces the cited rounding lemma)
Setting: `λ ∈ \simplex_\Xs` with `A := A(λ) ≻ 0`, support `{v_1,…,v_m}`, weights `p_i`.
Whitened vectors `u_i := A^{-1/2} v_i`, so `Σ p_i u_i u_i^⊤ = I`.
* def:barrier_potential — for symmetric `B` and `l < λ_min(B)`: `Φ_l(B) := tr((B − lI)^{-1})`.
* lem:sherman_morrison_trace — `M ≻ 0`, `u ∈ \R^d`: `(M + uu^⊤)^{-1} = M^{-1} − M^{-1}uu^⊤M^{-1}/(1+u^⊤M^{-1}u)`
  (Mathlib Woodbury `Matrix.add_mul_mul_inv_eq_sub` specialized) and
  `tr((M+uu^⊤)^{-1}) = tr(M^{-1}) − u^⊤M^{-2}u/(1+u^⊤M^{-1}u)`.
* lem:barrier_step — let `l < l' := l + 1/2`, `B` symmetric with `λ_min(B) > l'`,
  `M := B − l'I ≻ 0`, `Δ := Φ_{l'}(B) − Φ_l(B) > 0`, and
  `L_B(u) := u^⊤M^{-2}u/Δ − u^⊤M^{-1}u`. If `L_B(u) ≥ 1` then `Φ_{l'}(B + uu^⊤) ≤ Φ_l(B)` and
  `λ_min(B+uu^⊤) > l'`.
* lem:barrier_average — with `Σ p_i u_iu_i^⊤ = I`, `λ_min(B) > l`, `Φ_l(B) ≤ 1`: then
  `λ_min(B) ≥ l + 1 > l'` and `Σ_i p_i L_B(u_i) ≥ 2 − Φ_l(B) ≥ 1`; hence some `i` has
  `L_B(u_i) ≥ 1`. Proof (eigenvalues `λ_j` of `B`, `a_j = λ_j − l`, `b_j = a_j − 1/2`):
  `Σ p_i L(u_i) = P/(Δ) − Φ_{l'}` with `P = Σ 1/b_j²`, `Δ = Σ(1/b_j − 1/a_j) = ½ Q`,
  `Q = Σ 1/(a_j b_j)`. Need `P − Q ≥ Q²/4`: `P − Q = ½ Σ 1/(a_j b_j²)` and Cauchy–Schwarz
  `Q ≤ \sqrt{Σ 1/(a_jb_j²)}\sqrt{Σ 1/a_j} = \sqrt{2(P−Q)}\sqrt{Φ_l(B)}` so `Q² ≤ 2(P−Q)Φ_l ≤ 2(P−Q)`
  and `Q²/4 ≤ (P−Q)/2 ≤ P − Q`. Then `P/Δ − Φ_{l'} = 2P/Q − (Φ_l + Q/2) ≥ 2 − Φ_l` ⟺ `2P/Q − 2 ≥ Q/2`
  ⟺ `P − Q ≥ Q²/4`. Also `1/(λ_min − l) ≤ Φ_l ≤ 1`.
* thm:rounding — for every `T ≥ 4d` there are `x_0,…,x_{T−1} ∈ supp λ` (with repetitions) with
  `Σ_{t<T} x_tx_t^⊤ ⪰ (T/4) A(λ)`. Proof: greedy sequence `B_0 = 0`, `l_0 = −d`
  (`Φ_{−d}(0) = 1`), invariant `Φ_{l_t}(B_t) ≤ 1`, `λ_min(B_t) > l_t`, `l_t = −d + t/2`;
  step by lem:barrier_average + lem:barrier_step with `B_{t+1} = B_t + u_{i_t}u_{i_t}^⊤`;
  after `T` steps `λ_min(B_T) > −d + T/2 ≥ T/4`; un-whiten: `Σ v v^⊤ = A^{1/2} B_T A^{1/2} ⪰ (T/4)A`
  (lem:loewner_congruence).
* cor:fixed_design_from_distribution — same setting, `Σ_T := Σ_{t<T} x_tx_t^⊤`: `Σ_T ≻ 0`,
  `‖x‖²_{Σ_T^{-1}} ≤ (4/T)‖x‖²_{A^{-1}}` for all `x`, and `\gwidth{\Xs}{Σ_T} ≤ (2/\sqrt T)\gwidth{\Xs}{A}`
  (lem:loewner_scalar, lem:width_mono, lem:width_homog).
* lem:naive_rounding — (easy alternative) for `T ≥ 2m`, `κ_x := ⌈(T−m)λ_x⌉` gives a design of
  size ≤ T with `Σ ⪰ ((T−m)) A ⪰ (T/2) A`. State and prove; note it needs `T = Ω(d²)`.

---------------------------------------------------------------------------------------------

## upper.tex — `\chapter{The non-adaptive fixed-design algorithm}\label{chap:upper}`

Paper: Section 2.1, Appendix B.1. Target: Theorem 1 (thm:upper).
* def:mixed_design — `A_1` from lem:width_attained, `A_G` from thm:kiefer_wolfowitz,
  `A_0 := ½A_1 + ½A_G = A(λ_0)`, `λ_0 = ½λ_1 + ½λ_G ∈ \simplex_\Xs`.
* lem:mixed_design_bounds — `‖x‖²_{A_0^{-1}} ≤ 2d` for `x∈\Xs` and `\gwidth{\Xs}{A_0} ≤ \sqrt2\,\gw(\Xs)`
  (lem:loewner_scalar, cor:g_optimal_norm_bound, lem:width_mono, lem:width_homog).
* def:least_squares — for a fixed design with `Σ_T ≻ 0`: `\hat θ := Σ_T^{-1} X^⊤ y`.
* lem:least_squares_law — under `ν_θ`: `\hat θ − θ = Σ_T^{-1}X^⊤η ∼ \Normal(0, Σ_T^{-1})`
  (lem:fixed_design_law, lem:gauss_linear_image: covariance `Σ_T^{-1}X^⊤XΣ_T^{-1} = Σ_T^{-1}`).
* lem:approx_argmax_selector — for compact `\Xs` and `η > 0` there is a measurable
  `s_η : \R^d → \Xs` with `\ip{s_η(v)}{v} ≥ \max_{x∈\Xs}\ip{x}{v} − η` for all `v`.
  Proof: countable dense `(q_n)` in `\Xs`; `s_η(v) := q_{n(v)}`, `n(v) := \min\{n : \ip{q_n}{v} > M(v) − η\}`
  where `M(v) = \max_x \ip{x}{v}` is continuous; each `{v : \ip{q_n}{v} > M(v)−η}` is open.
  For finite `\Xs` an exact argmax selector exists (η = 0).
* lem:regret_le_difference_process — for any `\hat θ`, `\rec` with `\ip{\rec}{\hat θ} ≥ \max_x\ip{x}{\hat θ} − η`:
  `r(\rec,θ) ≤ D + η` where `D := \max_{x,x'∈\Xs}\ip{x − x'}{\hat θ − θ}`.
* lem:difference_process_concentration — `Δ ∼ \Normal(0,Σ_T^{-1})`, `D = \max_{x,x'}\ip{x−x'}{Δ}`,
  `σ_T^2 := \max_{x∈\Xs}‖x‖²_{Σ_T^{-1}}`: `\E D = 2\gwidth{\Xs}{Σ_T}` (lem:width_symm) and for
  `δ∈(0,1)`, `\Prob(D ≤ 2\gwidth{\Xs}{Σ_T} + 2σ_T\sqrt{2\cG\log(1/δ)}) ≥ 1−δ`
  (cor:sup_bound_whp applied to the index set `\Xs − \Xs` (compact), whose `σ²` is
  `\max_{x,x'}‖x−x'‖²_{Σ_T^{-1}} ≤ 4σ_T²`).
* def:fixed_design_algorithm — for `ε ∈ (0,1]`, `δ∈(0,1)`:
  `T := ⌈600 (\gw(\Xs)^2 + d\log(2/δ))/ε²⌉` (≥ 4d), design from thm:rounding applied to `λ_0`,
  recommendation `\rec := s_{ε/4}(\hat θ)`.
* thm:upper — (Theorem 1) the algorithm of def:fixed_design_algorithm is `(ε,δ)`-PAC.
  Proof chain: cor:fixed_design_from_distribution + lem:mixed_design_bounds give
  `σ_T² ≤ 8d/T`, `\gwidth{\Xs}{Σ_T} ≤ 2\sqrt2\gw(\Xs)/\sqrt T`; concentration gives w.p. ≥ 1−δ
  `D ≤ (4\sqrt2\,\gw(\Xs) + 8\sqrt{\cG d\log(1/δ)})/\sqrt T ≤ 3ε/4` (using `(a+b)² ≤ 2a²+2b²`,
  `128\cG < 320`, `(16/9)·320 < 600`); then `r ≤ D + ε/4 ≤ ε`.
  Remark: the paper's constant is 360; ours differs because of `\cG` and the approximate argmax;
  for finite `\Xs` the exact argmax gives `T = ⌈340(...)⌉`-ish (do not compute, just remark).
* lem:ball_identification — direct algorithm on `\Xs = \ball_d` (no width machinery): with
  `n := ⌈(8d + 48\log(1/δ))/ε²⌉` and `T = dn`, play each basis vector `e_i` `n` times;
  `\hat θ_i :=` empirical mean; `\rec := \hat θ/‖\hat θ‖` (any fixed point if `\hat θ = 0`).
  Then `(ε,δ)`-PAC. Proof: `\hat θ − θ ∼ \Normal(0, I/n)`; `‖\hat θ−θ‖² = ‖g‖²/n` with
  `\Prob(‖g‖² ≥ 2d + 12\log(1/δ)) ≤ δ` (lem:chi_square_tail); on the good event `‖Δ‖ ≤ ε/2` and
  `r(\rec,θ) = ‖θ‖ − \ip{\rec}{θ} ≤ 2‖Δ‖ ≤ ε`. (Uses lem:noise_representation, lem:gauss_pi.)
  Remark: it is also a special case of thm:upper since `\gw(\ball_d) ≤ d`.

---------------------------------------------------------------------------------------------

## lower_nonadaptive.tex — `\chapter{Lower bound for non-adaptive fixed designs}\label{chap:lower_nonadaptive}`

Paper: Section 2.2 (Bayesian argument), Appendices B.3 and B.4. Target: Theorem 3.
Setting: fixed design `x_0..x_{T−1}`, `X`, `Σ_T = X^⊤X ≻ 0`, recommendation kernel `ρ` on
`y ∈ \R^T` possibly using an independent seed `U` (a kernel is the same thing).
* def:bayes_prior — `τ > 0`; `θ ∼ \Normal(0, τ²Σ_T^{-1})` independent of `η ∼ \Normal(0,I_T)`;
  `y = Xθ + η`; `\rec ∼ ρ(y)`.
* lem:posterior_decomposition — `c := τ²/(1+τ²)`, `W := θ − c\,Σ_T^{-1}X^⊤y`. Then `(W, y)` is
  jointly Gaussian, `\E W = 0`, `Cov(W, y) = 0`, hence `W ⊥ y` (lem:gauss_joint_linear,
  lem:gauss_uncorrelated_indep); computation: `Cov(θ,y) = τ²Σ_T^{-1}X^⊤`,
  `Cov(y,y) = τ²XΣ_T^{-1}X^⊤ + I`, `Σ_T^{-1}X^⊤(τ²XΣ_T^{-1}X^⊤ + I) = (1+τ²)Σ_T^{-1}X^⊤`.
* lem:bayes_regret_identity — `\E\ip{\rec}{θ} = c\,\E\ip{\rec}{Σ_T^{-1}X^⊤y}` (lem:indep_integral_zero
  since `\rec` is a function of `(y, U)` and `W ⊥ (y,U)`).
* lem:bayes_regret_lower — `\E[r(\rec,θ)] ≥ \frac{τ(1−τ)}{1+τ²}\gwidth{\Xs}{Σ_T}`. Proof as in
  the paper: `Σ_T^{-1}X^⊤y = θ + Σ_T^{-1}X^⊤η`, `\ip{\rec}{v} ≤ \max_x\ip{x}{v}`, subadditivity
  of max, `θ \eqd τΣ_T^{-1/2}g` and `Σ_T^{-1}X^⊤η ∼ \Normal(0,Σ_T^{-1})` (lem:gauss_linear_image,
  lem:gauss_law_of_cov), lem:width_matrix_wd.
* lem:bayes_regret_lower_opt — with `τ = \sqrt2 − 1`: `\E[r] ≥ 0.207\,\gwidth{\Xs}{Σ_T}`
  (`τ(1−τ)/(1+τ²) = (\sqrt2−1)/2 ≥ 0.207`).
* thm:lower_nonadaptive — (Theorem 3) if a fixed-design algorithm with budget `T` is `(ε,δ)`-PAC
  with `δ ≤ 1/10`, then `T ≥ \gw(\Xs)²/(70 ε²)`. Proof: if `Σ_T` singular, lem:singular_design_fails
  contradicts `δ < 1/2`. Otherwise lem:pac_expected_regret with the prior of def:bayes_prior:
  `\E r ≤ ε + δ\E Z(θ) = ε + 2τδ\gwidth{\Xs}{Σ_T}` (lem:width_symm); combine with
  lem:bayes_regret_lower_opt: `(0.207 − 2τδ)\gwidth{\Xs}{Σ_T} ≤ ε`, `0.207 − 0.083 ≥ 0.12`;
  lem:width_empirical: `0.12\gw(\Xs)/\sqrt T ≤ ε`, so `T ≥ 0.0144\gw²/ε² ≥ \gw²/(70ε²)`.
* cor:lower_nonadaptive_H — paper's form: if the budget is `T = (H_1\log(1/δ)+H_2)/ε²` for all
  `δ` with `H_1 ≤ H_2`, then `H_2 ≥ \gw(\Xs)²/(70(\log 10 + 1))`.
* lem:singular_design_fails — if `Σ_T` is singular (including `T = 0`), then for every
  recommendation kernel there is `θ` with `\Prob_θ(r(\rec,θ) > ε) ≥ 1/2`. Proof from Appendix B.4:
  `v ≠ 0` with `Σ_Tv = 0` gives `\ip{x_t}{v} = 0` for all `t`, so `y` has the same law under
  `±αv`; `a := \max_x\ip{x}{v} > b := \min_x\ip{x}{v}` (else `\ip{x}{v}` constant `= 0` on `\Xs`
  when `T ≥ 1`, contradicting spanning; when `T = 0` use instead two points `x ≠ x'` of `\Xs`
  and `θ = ±α(x − x')`); `r(\rec, αv) + r(\rec,−αv) = α(a−b)`, choose `α = 4ε/(a−b)`.

---------------------------------------------------------------------------------------------

## lower_adaptive.tex — `\chapter{Lower bound for adaptive algorithms}\label{chap:lower_adaptive}`

Paper: Appendix B.2 (thm:main there). Target: Theorem 2 (thm:lower_adaptive). Assume `d ≥ 2`.
* lem:transform_preserves_pac — for invertible `M`, an identification algorithm on `\Xs` induces one
  on `M\Xs` (play `Mx` ↦ observe same `y`) which is `(ε,δ)`-PAC for `θ' = M^{-⊤}θ` iff the
  original is for `θ`, with the same budget; `\ip{Mx}{θ'} = \ip{x}{θ}`.
* def:normalized_instance — `M := d^{-1/2}A_G^{-1/2}` (thm:kiefer_wolfowitz); `\Xs' := M\Xs ⊆ \ball_d`
  (cor:g_optimal_norm_bound), `v_j := M x_j` for `x_j ∈ supp λ_G` (`m` points), `‖v_j‖ = 1`,
  `Σ_j λ_j v_jv_j^⊤ = I/d` (cor:g_optimal_normalized). Random index `J ∼ λ_G`.
  All of the chapter then works on `\Xs'` and drops primes.
* lem:separated_pair — `\E[\ip{v_1}{v_J}²] = 1/d`, so some `k` has `\ip{v_1}{v_k} ≤ 1/\sqrt d ≤ 1/\sqrt2`,
  and `ρ² := ‖v_1 − v_k‖² ≥ 2 − \sqrt2`.
* lem:two_point_test — `u := (v_1−v_k)/ρ`, `θ_± := ±(4ε/ρ)u`, `s := (\ip{v_1}{u} + \ip{v_k}{u})/2`.
  If `\rec` is `ε`-optimal for `θ_+` then `\ip{\rec}{u} ≥ s + ρ/4`; for `θ_-`: `≤ s − ρ/4`.
  Hence the test `\hat H := \indic\{\ip{\rec}{u} ≥ s\}` has error ≤ δ under each hypothesis.
* lem:kl_two_instances — for any algorithm with budget `n` on `\Xs ⊆ \ball_d`:
  `\KL(\Prob_{θ_+}‖\Prob_{θ_-}) ≤ 32nε²/ρ²` (cor:divergence_decomposition_gaussian,
  `|\ip{x_t}{u}| ≤ 1`).
* lem:baseline_lower — `(ε,δ)`-PAC with `δ < 1/16` implies `n ≥ \frac{2−\sqrt2}{32ε²}\log\frac{1}{4δ}`
  (lem:bretagnolle_huber: `2δ ≥ ½e^{−\KL}`).
* def:mixture_test — `θ^{(j)} := 3εv_j`; `H_0: θ = 0`; `H_1: θ = θ^{(J)}`, `J∼λ_G`;
  `\Prob_1 := Σ_j λ_j \Prob_{θ^{(j)}}` (mixture of trajectory laws, with recommendation).
* lem:mixture_kl — for any algorithm with budget `N`: `\KL(\Prob_0‖\Prob_1) ≤ Σ_jλ_j\KL(\Prob_0‖\Prob_{θ^{(j)}})
  = \frac{9ε²}{2}Σ_{t<N}\E_0[x_t^⊤(Σ_jλ_jv_jv_j^⊤)x_t] ≤ 9Nε²/(2d)` (lem:kl_mixture_convex,
  cor:divergence_decomposition_gaussian, `‖x_t‖ ≤ 1`).
* lem:test_lower — a test (an algorithm with budget `N` plus a `{0,1}`-valued recommendation) with
  `\Prob_0(\hat H = 1) ≤ 2δ` and `\Prob_1(\hat H = 0) ≤ 2δ` has `N ≥ \frac{2d}{9ε²}\log\frac{1}{8δ}`
  (lem:bretagnolle_huber; `4δ ≥ ½ e^{−9Nε²/(2d)}`).
* lem:test_from_alg — from an `(ε,δ)`-PAC `\mathsf{Alg}` with budget `n`, build (lem:composition)
  a test with budget `N = n + n_{est}`, `n_{est} := ⌈8\log(2/δ)/ε²⌉`: run `\mathsf{Alg}`, then play
  `\rec` `n_{est}` times, `\hat v :=` empirical mean, `\hat H := \indic\{\hat v > ε\}`. Errors ≤ 2δ
  under `H_0` and under each `θ^{(j)}` (hence under `\Prob_1`): lem:gauss_mean_concentration
  (`|\hat v − \ip{\rec}{θ}| ≤ ε/2` w.p. ≥ 1−δ), and under `θ^{(j)}`,
  `\max_x\ip{x}{θ^{(j)}} ≥ \ip{v_j}{θ^{(j)}} = 3ε` so `\ip{\rec}{θ^{(j)}} ≥ 2ε` w.p. ≥ 1−δ.
* thm:lower_adaptive — (Theorem 2) `d ≥ 2`, `δ < 1/16`: every `(ε,δ)`-PAC algorithm with budget
  `n` satisfies `n ≥ c_{ad}\, d\log(1/δ)/ε²` with an explicit `c_{ad}` (derive: from
  lem:baseline_lower `n_{est} ≤ (20/c_0)n + 1`... handle the ceiling; `c_0 = (2−\sqrt2)/32`;
  `\log(1/(8δ)) ≥ \log(1/δ)/4` for `δ < 1/16`). State the constant you obtain.

---------------------------------------------------------------------------------------------

## width.tex — `\chapter{Properties of the Gaussian width}\label{chap:width}`

Paper: Section 2.3, Appendices D and E. Targets: Proposition 4 (split), Theorem 5.
* prop:width_le_d — `\gw(\Xs) ≤ d` (cor:g_optimal_norm_bound, Cauchy–Schwarz, lem:gauss_norm_moments).
* prop:width_finite — `|\Xs| = m` finite: `\gw(\Xs) ≤ \sqrt{2d\log m}` (lem:gauss_max_upper with
  `σ² = d`; and `≤ d` trivially when `m = 1`).
* def:regionalized_width — for `A∈\PD` and a partition `\mathcal R = (R_1,…,R_K)` of `\Xs` into
  nonempty compact pieces: `\gw(A;\Xs,\mathcal R) := \max_i \E\max_{x∈R_i}\ip{x}{A^{-1/2}g}`.
* prop:width_partition — finite `\Xs`, pieces of size ≤ `p`: `\gw(A_G;\Xs,\mathcal R) ≤ \sqrt{2d\log p}`.
* prop:width_ball — `d/\sqrt3 ≤ \gw(\ball_d) ≤ d`. Lower bound: for `A ∈ \designset(\ball_d)`,
  `tr A ≤ 1`, `\gwidth{\ball_d}{A} = \E‖A^{-1/2}g‖ ≥ \sqrt{tr(A^{-1})}/\sqrt3 ≥ d/\sqrt3`
  (lem:gauss_norm_moments, lem:trace_inv_amhm).
* prop:width_lower_sqrt_dlogd — `\gw(\Xs) ≥ c\sqrt{d\log d}` (state with the constant coming from
  lem:gauss_max_lower; only for `d ≥ d_0`). Uses lem:whitened_separated_points (below) and
  thm:sudakov_fernique, lem:gauss_max_lower. Mark as secondary.
* lem:whitened_separated_points — `Σ := A(λ) ≻ 0`, `T := Σ^{-1/2}\Xs`, `m := ⌊d/2⌋`: there are
  `t_1..t_m ∈ T` with `‖t_i − t_j‖ ≥ \sqrt{d/2}` (greedy projection argument of Appendix D).
* prop:width_lower_from_pac — if every `(ε,δ_0)`-PAC algorithm with budget `T` on `\Xs` has
  `T ≥ L/ε²` (for all `ε ∈ (0,1]`), then `\gw(\Xs)^2 ≥ L/600 − d\log(2/δ_0) − 1` (thm:upper).
* cor:width_structured — from Chapter log_gains lower bounds: `\gw({−1,1}^d) ≥ c d`,
  `\gw({0,1}^d) ≥ c d`, `\gw(m\text{-sets}) ≥ c\sqrt{md}` for `d−m+1 ≥ 20m` (uses
  thm:lower_hypercube_pm, thm:lower_hypercube_01, thm:lower_msets via prop:width_lower_from_pac).
Section multi-task MAB (`sec:width_multitask`), Appendix E:
* def:width_subspace — for finite `\Xs ⊆ \R^d` spanning a subspace `V` of dimension `r`:
  `\gw(\Xs) := \gw(U^⊤\Xs)` for any `U ∈ \R^{d×r}` with orthonormal columns spanning `V`;
  well defined by lem:width_iso.
* def:multitask_set — blocks `B_j`, `d = Σd_j`, `d_j ≥ 2`, `\Xs = {x∈{0,1}^d : Σ_{i∈B_j}x_i = 1 ∀j}`.
* def:helmert — `H_n ∈ \R^{n×(n−1)}`; lem:helmert_props — `H_n^⊤H_n = I`, `H_n^⊤\mathbf 1 = 0`,
  `H_nH_n^⊤ = I − \frac1n\mathbf 1\mathbf 1^⊤`.
* lem:multitask_basis — `U := [u_0, Q_1, …, Q_m]` has orthonormal columns and `range U = \Span\Xs`,
  `\dim\Span\Xs = d − m + 1`.
* lem:multitask_design_cov — for the product-uniform design, `Σ_r = U^⊤ΣU = diag(S, d_1^{-1}I, …)`.
* lem:multitask_width_reduction — `\gw(\Xs) ≤ Σ_j\sqrt{d_j}\,\E\max_{k≤d_j}(H_{d_j}g^{(j)})_k`.
* lem:centered_gaussian_max — `\E\max_k (Z_k − \bar Z) = \E\max_k Z_k ≤ \sqrt{2\log n}` for iid `Z`.
* prop:width_multitask — `\gw(\Xs) ≤ Σ_j\sqrt{2d_j\log d_j}`.
* thm:width_separation — (Theorem 5) `d_i = 2` for `i<m`, `d_m = m²`: `\dim = Θ(d)`,
  `\gw(\Xs) ≤ C\sqrt{d\log d}` while `\sqrt{d\log|\Xs|} ≥ c d^{3/4}`; give explicit inequalities.

---------------------------------------------------------------------------------------------

## log_gains.tex — `\chapter{Structured sets with only logarithmic gains from adaptivity}\label{chap:log_gains}`

Paper: Section 2.4, Appendices C, G, F.
Section `sec:log_gains_algorithm` (Theorem 6):
* def:region_algorithm — partition `\mathcal R = (R_1..R_d)` of finite `\Xs`; phase 1: fixed design
  from thm:rounding applied to `λ_G` with `T_1 := ⌈C_1(\gw(A_G;\Xs,\mathcal R)^2 + d\log(4/δ))/ε²⌉`
  (explicit `C_1`, same computation as thm:upper with `ε/2` and `δ/2`), least squares `\hat θ`,
  candidates `x^{(i)} ∈ \argmax_{x∈R_i}\ip{x}{\hat θ}` (finite: exact); phase 2 (lem:composition):
  Median Elimination (thm:median_elimination) on the `d` candidates with parameters `(ε/2, δ/2)`;
  output its answer.
* lem:region_phase1 — w.p. ≥ 1−δ/2: `\ip{x^{(i_*)}}{θ} ≥ \max_x\ip{x}{θ} − ε/2` where `i_*` is
  the region of an optimal arm (concentration over `R_{i_*}` only: cor:sup_bound_whp on the index
  set `R_{i_*} − R_{i_*}`; `σ_T² ≤ 4d/T_1` since only `A_G` is used).
* thm:log_gains — (Theorem 6) for finite `\Xs` with `|\Xs| = m`, partition into `d` regions of size
  ≤ `⌈m/d⌉`: the algorithm is `(ε,δ)`-PAC with budget ≤ `C d\log((m/d)_+/δ)/ε²`, explicit `C`,
  `(u)_+ := \max(1,u)`. (prop:width_partition, thm:median_elimination sample bound.)
Section `sec:log_gains_lower` (adaptive lower bounds, randomized algorithms, no Yao):
* lem:two_point_pinsker — instances `θ, θ'`, any event `E` of `(\hist_T, \rec)`:
  `\Prob_{θ'}(E) ≤ \Prob_θ(E) + \sqrt{\KL/2}`, `\KL := ½Σ_{t<T}\E_θ\ip{x_t}{θ−θ'}²`
  (lem:pinsker, cor:divergence_decomposition_gaussian, lem:kl_data_processing_recommendation).
* lem:fail_prob_from_expected_value — if `\ip{x}{θ_I} ∈ [0, 10ε_*]` for all `x`,
  `\max_x\ip{x}{θ_I} = 10ε_*` for all instances `I` in a finite family, and
  `\E_{I∼Unif}\E_I\ip{\rec}{θ_I} ≤ aε_*` with `a < 9`, then some `I` has
  `\Prob_I(r > ε_*) ≥ (9−a)/9` (Markov/averaging).
* def:multitask_instances — `ε_j := ε\sqrt{d_j}/S`, `S := Σ_s\sqrt{d_s}`; for `\tilde x ∈ \tilde\Xs`
  (at most one 1 per block), `θ_{\tilde x}[i] := 10ε_j\tilde x[i]` for `i∈B_j`; `\Xs^{(j)}`, `x^{(i)}`.
* lem:multitask_block_average — fix `j`, `x ∈ \Xs^{(j)}`, `T`; with `p_i := \Prob_{θ_x}(\rec_{B_j} = e_i)`,
  `N_i := Σ_t x_t[i]` for `i ∈ B_j`: `Σ_i p_i = 1`, `Σ_i\E N_i = T`,
  `\KL(\Prob_{θ_x}‖\Prob_{θ_{x^{(i)}}}) = 50ε_j²\E_{θ_x}N_i`; hence
  `(1/d_j)Σ_i \E_{θ_{x^{(i)}}}[\ip{\rec}{θ_{x^{(i)}}}_{B_j}] ≤ (10ε_j/d_j)(1 + 5ε_j\sqrt{d_jT})`
  (Pinsker + Cauchy–Schwarz `Σ_i\sqrt{\E N_i} ≤ \sqrt{d_jT}`).
* thm:lower_multitask — `T ≤ S²/(20000ε²)`: `\E_{I∼Unif(\Xs)}\E_I\ip{\rec}{θ_I} ≤ 5.36ε`, so
  some instance has `\Prob(r > ε) ≥ 0.4`. (`ε_j\sqrt{d_jT} = d_j/\sqrt{20000}`, `d_j ≥ 2`.)
* thm:lower_hypercube_pm — `\Xs = {−1,1}^d`, `θ_s := (5ε/d)s`, `s∈{±1}^d`, alternative `θ_s^{(j)}`
  with coordinate `j` zeroed; `T ≤ d²/(100ε²)` ⟹ some `s` with `\Prob(r > ε) ≥ 1/6`.
  Route: gap `= Σ_j(10ε/d)\indic\{\rec_j ≠ s_j\}`; `\KL(θ^{(j)}_s‖θ_s) = (25ε²/(2d²))T`; average
  over the sign of `s_j` of `\Prob(\rec_j ≠ s_j) ≥ 1/2 − \sqrt{\KL/2}·...` (be precise); `\E gap ≥ 2.5ε`,
  `gap ≤ 10ε` ⟹ reverse Markov.
* thm:lower_hypercube_01 — `\Xs = {0,1}^d`, `θ_s := (10ε/d)s`, same route, `N_j := Σ_t x_t[j] ≤ T`.
* def:msets — `\Xs = {x∈{0,1}^d : ‖x‖_0 = m}`; lem:msets_equivalent_sampling (Appendix G.3);
  lem:msets_good_set (`G_B`, `|G_B| ≥ n/2`); lem:msets_pinsker_step; thm:lower_msets —
  `n := d−m+1 ≥ 20m`, `T ≤ mn/(2500ε²)` ⟹ some `θ^{(S)}` with `\Prob(r > ε) ≥ 2/9`.
* cor:lower_ball_adaptive — from cor:ball_pac_lower (Chapter pre_bayes): `(ε,δ)`-PAC on `\ball_d`
  with `δ ≤ 1/500` needs `T ≥ d²/(1000ε²)`.
* rem:table — restate Table 1 as an itemized list with pointers.

---------------------------------------------------------------------------------------------

## norm_estimation.tex — `\chapter{Estimation of the $\ell_2$-norm of the reward vector}\label{chap:norm}`

Paper: Section 3 and Appendix D (l2-norm estimation: D.1–D.4). Target: Theorem 8. `\Xs = \ball_d`,
`r := ‖θ‖`. Follow the paper's three-step structure but use the constants below.
* def:norm_estimator — an *estimation algorithm* with budget `T` is an LML algorithm plus a
  recommendation kernel with values in `[0,∞)`; it is `(ε,δ)`-accurate if `\Prob_θ(|\hat r − r| ≤ ε) ≥ 1−δ` ∀θ.
* def:rademacher_direction — `x = ε_{\pm}/\sqrt d ∈ \ball_d` (`ε_i` iid signs); lem:direction_second_moment
  (`\E\ip{x}{θ}² = r²/d`, `\E[xx^⊤] = I/d`).
* def:squared_statistic — directions `x^{(k)}`, `s` samples each, `\bar y_k`, `Z_k := d(\bar y_k² − 1/s)`,
  `\bar Z`; decomposition `\bar Z − r² = \frac1KΣ X_k + \frac1KΣ W_k`, `X_k := d\mu_k² − r²`,
  `W_k := Z_k − d\mu_k²`, `\mu_k := \ip{x^{(k)}}{θ}`.
* lem:statistic_structure — given the directions, `\bar y_k = \mu_k + ζ_k` with `ζ_k` iid `\Normal(0,1/s)`
  independent of the directions (lem:noise_representation, lem:gauss_pi).
* lem:term1_subexp — `X_k` iid, `(16r⁴, 4r²)`-sub-exponential (lem:rademacher_square_subexp with
  `d\mu_k² = \ip{ε^{(k)}}{θ}²`); lem:term1_bound —
  `\Prob(|\frac1KΣX_k| > t) ≤ 2\exp(−K\min(t²/(32r⁴), t/(8r²)))` (cor:subexp_average_tail).
* lem:term2_conditional — for fixed directions, `W_k` independent, `(V_k, b)`-sub-exponential with
  `V_k := 8(d²/s² + \mu_k²d²/s)`, `b := 4d/s` (lem:gaussian_square_subexp applied to `\sqrt d\bar y_k`).
* lem:term2_bound — `\bar V := \frac1KΣV_k`, any `τ`: `\Prob(|\frac1KΣW_k| > t) ≤ \Prob(\bar V > τ) + 2\exp(−K\min(t²/(2τ), t/(2b)))`
  (Fubini over the directions).
* lem:vbar_bound — `\Prob(\bar V > 8(d²/s² + 3dr²/(2s))) ≤ 2\exp(−K/128)` (lem:term1_bound with `t = r²/2`).
* thm:additive_estimation — (Algorithm 1) given `r_0` with `r/2 < r_0 ≤ 2r` and `ε ≤ r_0`,
  with `s := ⌈c_0 d/r_0²⌉`, `K := ⌈c_1 r_0²\log(4/δ)/ε²⌉`: `\Prob(|\hat r − r| ≤ ε) ≥ 1 − δ/2` and
  the budget `sK ≤ C d\log(4/δ)/ε²`. Derive explicit admissible `c_0, c_1, C` (e.g. `c_0 = 1`,
  `c_1` large enough that the four failure probabilities are ≤ δ/8 each; show the arithmetic).
  Also handle `r = 0` (then `X_k = 0`).
* def:scale_test — `Test(t, δ')` with `s = ⌈c_0d/t²⌉`, `K = ⌈c_1'\log(1/δ')⌉`, returns `H_1` iff `U ≥ 3t²/2`.
* lem:test_error_h0 — if `r ≤ t`: `\Prob(H_1) ≤ 3δ'/4`; lem:test_error_h1 — if `r ≥ 2t`: `\Prob(H_0) ≤ 3δ'/4`
  (with explicit `c_1'`; follow Appendix D.2 with the sub-exponential bounds above).
* def:multiscale_algorithm — `t_j = 2^jε`, `δ_j = δ/2^{j+2}`, loop while `t_j < 2\sqrt d`; output `r_0`.
* thm:multiscale_guarantee — the four cases of Appendix D.2, each w.p. ≥ 1 − 3δ/8: (1) `r ≤ ε` ⟹ `r_0 = ε`;
  (2) `ε < r < \sqrt d` ⟹ `r/2 < r_0 ≤ 2r` and `r_0 < 2\sqrt d`; (3) `\sqrt d ≤ r < 4\sqrt d` ⟹
  (`r/2 < r_0 ≤ 2r` or `r_0 ≥ 2\sqrt d`); (4) `r ≥ 4\sqrt d` ⟹ `r_0 ≥ 2\sqrt d`. Note the loop is
  adaptive: use lem:composition (each round is a fixed-length algorithm whose parameters depend on `j`).
* lem:multiscale_samples — total budget ≤ `C' d\log(1/δ)/ε²` (geometric sum with `Σ_j 4^{-j}(j+3) < ∞`).
* def:large_norm_algorithm — basis design: each `e_i` played `n := ⌈32\log(4/δ)/ε²⌉` times,
  `\hat θ_i` empirical means, `\hat R := ‖\hat θ‖² − d/n`, `\hat r := \sqrt{\max(\hat R, 0)}`.
  (Deviation from the paper: no random rows, no random-matrix bound.)
* lem:large_norm_decomposition — `\hat θ = θ + Δ`, `Δ ∼ \Normal(0, I/n)`, `\hat R − r² = L + Q`,
  `L := 2\ip{θ}{Δ} ∼ \Normal(0, 4r²/n)`, `Q := ‖Δ‖² − d/n = (‖g‖² − d)/n` `(8d/n², 4/n)`-sub-exponential
  (lem:chi_square_subexp).
* thm:large_norm_guarantee — if `r ≥ \sqrt d` and `ε ≤ 1`: `\Prob(|\hat R − r²| ≥ εr) ≤ δ/2`, hence
  `\Prob(|\hat r − r| ≤ ε) ≥ 1 − δ/2`; budget `dn ≤ 32d\log(4/δ)/ε² + d`. (Show the two tail computations.)
* def:meta_algorithm — Algorithm 4 with the three sub-algorithms, composed by lem:composition.
* thm:norm_estimation — (Theorem 8) the meta-algorithm is `(ε,δ)`-accurate with budget ≤ `C_{norm} d\log(4/δ)/ε²`
  (explicit `C_{norm}`); the four-case union bound of Appendix D.4.

---------------------------------------------------------------------------------------------

## separation.tex — `\chapter{A polynomial separation between adaptive and non-adaptive algorithms}\label{chap:separation}`

Paper: Section 2.5, Appendix I. Target: Theorem 7. `d ≤ k ≤ d²`.
* def:block_ball_set — `B_i := {(i−1)d+1..id}` (0-indexed in Lean), `\Xs_i := {x∈\R^{kd} : \supp x ⊆ B_i, ‖x‖ ≤ 1}`,
  `\Xs := ∪_i\Xs_i`; `θ^{(i)}` the block of `θ`.
* lem:block_ball_basic — `\Xs` compact, spans `\R^{kd}`, `\max_{x∈\Xs_i}\ip{x}{θ} = ‖θ^{(i)}‖`,
  `\max_{x∈\Xs}\ip{x}{θ} = \max_i‖θ^{(i)}‖`, `\Xs ⊆ \ball_{kd}`.
* lem:block_restriction — a fixed design on `\Xs` with `T_i` points in block `i`, and `θ` supported on
  block `i`: observations outside block `i` are pure noise independent of the rest; the induced
  procedure (design = block-`i` points as elements of `\ball_d`, recommendation = projection of `\rec`
  on block `i`, which is `0` if `\rec ∉ \Xs_i`) is a fixed-design algorithm on `\ball_d` with budget `T_i`
  and the same regret. (lem:fixed_design_law.)
* thm:separation_lower_nonadaptive — any fixed-design `(ε,δ)`-PAC algorithm on `\Xs` with `δ ≤ 1/10`
  has `T ≥ k d²/(210 ε²)` (pigeonhole `T_{i^*} ≤ T/k`, lem:block_restriction, thm:lower_nonadaptive,
  prop:width_ball: `\gw(\ball_d)² ≥ d²/3`), and with `δ < 1/16`, `T ≥ c_{ad} kd\log(1/δ)/ε²` (thm:lower_adaptive).
* def:block_algorithm — phase 1: for each `i ≤ k`, run the meta-algorithm (thm:norm_estimation) on
  `\Xs_i` (identified with `\ball_d`) with parameters `(ε/4, δ/(2k))`, get `\hat r_i`; `\hat i := \argmax_i\hat r_i`;
  phase 2: lem:ball_identification on `\Xs_{\hat i}` with `(ε/2, δ/2)`; composed by lem:composition.
* lem:block_selection — w.p. ≥ 1−δ/2, `‖θ^{(\hat i)}‖ ≥ \max_i‖θ^{(i)}‖ − ε/2` (union bound).
* thm:separation — (Theorem 7) the block algorithm is `(ε,δ)`-PAC with budget
  ≤ `C(kd\log(2k/δ) + d²)/ε² ≤ C'(kd\log(1/δ) + kd\log k)/ε²` (explicit), while every non-adaptive
  algorithm needs `Ω(kd\log(1/δ)/ε² + kd²/ε²)` (thm:separation_lower_nonadaptive). Regret bookkeeping:
  `r(\rec,θ) = \max_i‖θ^{(i)}‖ − \ip{\rec}{θ} ≤ (\max_i‖θ^{(i)}‖ − ‖θ^{(\hat i)}‖) + (‖θ^{(\hat i)}‖ − \ip{\rec}{θ})`.
