# Formalization of "On the Power of Adaptivity for ε-Best Arm Identification in Linear Bandits" (Maiti, Xu, Jamieson, COLT 2026)

A Lean 4 formalization, built on Mathlib and the [Lean Machine Learning](https://github.com/LeanMachineLearning/LML) library (LML), of the minimax sample-complexity results of the paper: the non-adaptive fixed-design upper bound in terms of a Gaussian width of the action set, the matching lower bounds, the structured action sets on which adaptivity only gives logarithmic gains, the $\ell_2$-norm estimation procedure and the action set on which adaptivity gives a polynomial improvement.

The development is blueprint-driven: `blueprint/src/` contains a detailed proof document (a [leanblueprint](https://github.com/PatrickMassot/leanblueprint)) that decomposes the paper into lemmas whose proofs go from what Mathlib/LML already provide to the paper's results. Part II of the blueprint collects the prerequisites that are meant to be contributed upstream (Gaussian concentration, sub-exponential variables, divergence decompositions of algorithm-environment sequences, Median Elimination, ...).

* Paper source: `source/`
* Blueprint: `blueprint/src/` (build with `leanblueprint pdf` / `leanblueprint web` from `blueprint/`)
* Lean library: `COLT83/`
* Blueprint outline and design decisions: `notes/`
