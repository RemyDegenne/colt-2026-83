# Upstreaming candidates

Assessment of the library layers `Maiti2026Power/Mathlib/` and `Maiti2026Power/LeanMachineLearning/` as
contributions to Mathlib and to LML (LeanMachineLearning), written on 2026-09-06 after phase 2
was completed (every headline result proved, comparator green), and updated on 2026-09-07 after
the LML bump to `21d7e67`, which removed the entries that have since been upstreamed to LML
(the sub-exponential file, the integrated chain rule for `klDiv`, `IndepFun.hasCondDistrib_const`,
`Kernel.compProd_prodMkLeft_apply`). Overlaps were checked against the Mathlib revision pinned in
`lake-manifest.json` (`cf65d43b4f5e1a79482e8c488d121853b9d7ca05`, toolchain `v4.34.0-rc2`): none of
the results listed below exist in Mathlib at that revision; the only near-miss is
`Set.Finite.isCompact_convexHull`, which covers finite sets only. Recheck before opening a PR,
since the probability library moves quickly.

## Strongest Mathlib candidates

Classical results, self-contained, already stated in Mathlib namespaces and Mathlib style.

| File | Result | Notes |
|---|---|---|
| `InformationTheory/Pinsker.lean`, `InformationTheory/BretagnolleHuber.lean` | Pinsker's inequality for one event (through the Bernoulli case), the Bretagnolle–Huber inequality | Absent from Mathlib although `klDiv` is there. Needs `Probability/Distributions/Bernoulli.lean` (Lebesgue integrals and densities of `bernoulliMeasure`), small and upstreamable. |
| `InformationTheory/KLMixture.lean` | Convexity of `klDiv` in its second argument | Extends the existing `klDiv` API. Needs `MeasureTheory/MixtureMeasure.lean` (Radon–Nikodym derivative of a finite mixture), small and upstreamable. |
| `Probability/SudakovFernique.lean` with `Probability/GaussianInterpolation.lean`, `Probability/SteinIdentity.lean`, `Probability/SteinReal.lean`, `Probability/SteinExpGrowth.lean`, `Analysis/SpecialFunctions/LogSumExp.lean`, `Analysis/InnerProductSpace/LogSumExp.lean` | Sudakov–Fernique inequality; Gaussian interpolation formula; Stein's identity (real and vector); log-sum-exp and softmax as a smoothing of the maximum | A coherent package. Log-sum-exp/softmax and Stein's identity are independently useful and can go first. |
| `Probability/MaureyPisier.lean`, `Probability/BorellTIS.lean`, `Analysis/Calculus/QuarterCircle.lean` | Gaussian concentration of smooth Lipschitz functions (Maurey–Pisier); Borell–TIS for finite maxima of linear forms and for compact sets | The compact-set version needs the support function (see below); the finite-max version is self-contained. |
| `Analysis/Convex/CompactHull.lean` | The convex hull of a compact set of a finite-dimensional real space is compact (Carathéodory) | Mathlib only has the finite-set case. |
| `Matrix/LoewnerInv.lean`, `Matrix/Loewner.lean`, `Matrix/HermitianCFC.lean`, `Matrix/TraceInv.lean`, `Analysis/InnerProductSpace/EuclideanMatrix.lean` | Inversion is antitone for the Loewner order over any `RCLike` field; quadratic-form characterizations of the Loewner order, congruence, square roots; traces and inverses through the continuous functional calculus; AM–HM for `tr A⁻¹`; `toEuclideanLin` lemmas | Mathlib proves the inverse result only for units of C⋆-algebras, which excludes real matrices. `HermitianCFC.lean` has a TODO: two trace identities are stated for real symmetric matrices only. |
| `Probability/GaussianSquareMGF.lean`, `Probability/SubgaussianSquare.lean` | `∫ exp (b x² + c x + d)`; MGF of the square of a Gaussian; chi-square variables are sub-exponential with explicit constants and their tail bounds; the Gaussian trick `E exp (a Z²) ≤ (1 - 2ca)^(-1/2)` for sub-Gaussian `Z`, fourth moment `≤ 14 c²`, `Z² - c` sub-exponential | Standard toolbox results with explicit constants. |
| `Probability/Rademacher.lean`, `Probability/GaussianSum.lean`, `Probability/GaussianAbsMoment.lean`, `Probability/SubgaussianMax.lean`, `Probability/GaussianMaxLower.lean`, `Probability/GaussianMGF.lean` | Rademacher vectors and Hoeffding's lemma coordinatewise; sums of independent Gaussians are Gaussian; `E|Z| = √(2v/π)`; expected maximum of finitely many sub-Gaussians; Mills-ratio lower bound and `E max ≥ √(log m)/4`; exponential moments under Gaussian measures (from Fernique) | Small, standard, low review cost. |
| `Probability/InfinitePiWindow.lean`, `Probability/IidOfCondDistrib.lean`, `Probability/CondDistribConst.lean`, `Probability/CondDistrib.lean` | Coordinates of an i.i.d. sequence along an injective family are i.i.d. (finite and infinite index sets); independence of a prefix and a later window; a constant conditional law implies i.i.d.; `Kernel.mapOfConst`; transport and composition lemmas for `HasCondDistrib` | Extend the recent `HasCondDistrib` and `infinitePi` APIs of Mathlib, which are actively growing. |
| `Analysis/Calculus/LocalExtr.lean`, `MeasureTheory/MeasurableSpace/Sigma.lean`, `Data/Fintype/PiSplitAt.lean`, `Algebra/Order/BigOperators/Covariance.lean`, `Analysis/InnerProductSpace/OrthonormalBasisSubmodule.lean` | One-sided Fermat's rule; measurability on sigma types from the fibers; sums over dependent products split at a coordinate; weighted covariance bound; expansion and Parseval identities for an orthonormal basis of a submodule, seen in the ambient space | Trivial to review. |

## Candidates needing a design decision first

* `Analysis/InnerProductSpace/SupportFn.lean`, `SupportFnDense.lean` and `Probability/GaussianWidth.lean`: the support function of a set and the Gaussian (mean) width are textbook notions, but the docstring TODO is right that Mathlib would probably want the support function of a set of a normed space as a function on the dual (or of a set of the dual as a function on the space). Worth a Zulip thread before a PR. The inner-product version used here would then be a special case.
* Files whose docstrings record a generalization gap that reviewers will ask about:
  `Analysis/Calculus/Gradient.lean` (real normed spaces only, holds over `RCLike`),
  `Order/CiSupFinite.lean` (`ℝ` only, and the exponential lemma is an instance of a general fact about monotone functions of a finite maximum),
  `Probability/StdGaussianProd.lean` (two covariance lemmas belong next to `covariance_fst_snd_prod`).
* `Probability/MultivariateGaussian.lean` (closure of `multivariateGaussian` under linear maps, convolution, scalar multiplication): check the current Mathlib file `Probability/Distributions/Gaussian/Multivariate.lean` first, since this area is being developed upstream.
* `MeasureTheory/ApproxArgmax.lean` (measurable approximate argmax selectors on compact sets, exact on finite sets) and `Data/Finset/TopBy.lean` (top-`m` selection by a score with a tie-breaking rule, and the median argument): generic and reusable, but the API shape should be discussed.

## LML candidates

Not Mathlib material (they are about learning algorithms), but generic in the environment and
the natural next layer of LML.

* `IdentAlg.lean`, `Run.lean`, `FixedBudget.lean`, `AlgorithmPrefix.lean`: identification algorithms with a stopping rule and an output rule, runs, transport and existence of runs, the PAC property, fixed budgets and fixed designs, the stopped history and data processing. This is the core abstraction of the project.
* `Seeded.lean` with `Probability/CondDistribConst.lean`: seeded algorithms (internal randomness as fresh seeds), noise environments, the seed representation of every run through the uniqueness of the law of the history, and the PAC transfer lemma for fixed-budget seeded algorithms with a deterministic output. This was the workhorse for both adaptive upper bounds (Theorems 7 and 8).
* `Phased.lean`, `MedianEliminationSchedule.lean`, `MedianEliminationRound.lean`, `MedianElimination.lean`: phased deterministic algorithms and a verified Median Elimination.
* `DivergenceDecomposition.lean` with `Mathlib/InformationTheory/KLCompProd.lean` (all that is left of that file: the one-step divergence of a policy/reward decomposition, on top of LML's integrated chain rule), `EnvDensity.lean`, `TwoPoint.lean`, `RepeatTest.lean`, `RepeatTestGaussian.lean`: the divergence decomposition, environment densities along a history, the two- and three-point methods, the repeated-action test. The standard lower-bound toolkit for bandits.
* `LinearBandit.lean`, `GaussianNoise.lean`, `FixedDesignRun.lean`, `FixedDesignLaw.lean`, `FixedDesignTransport.lean`, `CondSubgaussian.lean`: the linear Gaussian environment, its noise structure (i.i.d. noise for any algorithm, conditionally sub-Gaussian), the law of fixed-design runs and their transport through linear maps.

## Not worth upstreaming

Tailored to single proofs of the paper: `Analysis/BarrierSum.lean` (the barrier inequality of the
Batson–Spielman–Srivastava rounding), `Analysis/InnerProductSpace/IsotropicSeparated.lean`,
`Probability/Kernel/PriorAverage.lean`, `Data/Set/CoverSmall.lean`,
`Data/Finset/PowersetCardSum.lean`, `Probability/GaussianDensityRatio.lean`,
`Probability/KLGaussian.lean` (unless Mathlib still lacks the divergence between Gaussians with
the same variance), `Probability/IndepIntegral.lean`; and everything under `Maiti2026Power/MXJ2026/`,
which is the paper itself.

## Suggested order

A first PR with the best effort-to-value ratio: the two information-theory inequalities. Each is a
single file, classical, and plugs into an existing Mathlib API. Then the KL convexity file and the
Gaussian toolbox files (`GaussianSquareMGF`, `SubgaussianSquare`, `Rademacher`, `GaussianSum`).
The sub-exponential file left this repository for LML on 2026-09-07 and is the strongest Mathlib
candidate of all, but the PR now starts from
`LeanMachineLearning/ForMathlib/Probability/Moments/SubExponential.lean`. The Sudakov–Fernique
and Borell–TIS packages are the most valuable but also the largest, and the compact-set versions
wait on the support-function design decision.

Before any PR: remove the `Maiti2026Power.`-specific docstring references to the blueprint, check the
`## TODO` sections above, and note that the files use the `module` system with
`@[expose] public section`.
