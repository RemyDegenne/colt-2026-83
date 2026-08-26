# Comparator setup

Machine-checkable verification, with [leanprover/comparator](https://github.com/leanprover/comparator),
that this repository proves the headline results claimed in [`formalization.yaml`](../formalization.yaml)
— without having to read (or trust) the Lean development in `COLT83/`.

**Status (phase 1).** The headline statements are stated but not yet proved (their proofs are
`sorry`), so comparator currently reports the `sorryAx` axiom for every config. The challenge
files are the phase-1 deliverable: they fix the statements to be proved in phase 2.

Each challenge is **one self-contained file whose transitive imports resolve to Mathlib and Lean
core only**. That is the shape the [Palomar registry](https://palomar-registry.org/)'s mechanical
verification enforces: the challenge can import no LML, no project modules, and no sibling helper
modules.

## The trust story

For each headline theorem `COLT83.<name>` there is a challenge file
`Challenge_<name>.lean` and a config `<name>.json`; the list is `targets.txt`:

| paper result | challenge(s) |
|---|---|
| Theorem 1 (fixed-design upper bound) | `exists_isFixedDesign_isPAC` |
| Theorem 2 (adaptive lower bound) | `le_budget_of_isPAC` |
| Theorem 3 (non-adaptive lower bound) | `le_budget_of_isFixedDesign_of_isPAC` |
| Proposition 4 (width bounds) | `gw_le_card`, `gw_le_sqrt_log_ncard`, `sqrt_log_le_gw` |
| Theorem 5 (a set with small width) | `width_separation` |
| Theorem 6 (log gains on finite sets) | `exists_isPAC_of_finite` |
| Table 1 (adaptive lower bounds) | `multitaskSet_lt_budget_of_isPAC`, `hypercubePM_lt_budget_of_isPAC`, `hypercube01_lt_budget_of_isPAC`, `mSet_lt_budget_of_isPAC`, `unitBall_le_budget_of_isPAC` |
| Theorem 7 (polynomial separation) | `blockBallSet_le_budget_of_isFixedDesign_of_isPAC`, `blockBallSet_le_budget_of_isPAC`, `exists_isPAC_blockBallSet` |
| Theorem 8 (ℓ₂-norm estimation) | `exists_isAccurateNormEst` |

Each challenge states the theorem with `sorry`, with **every** definition the statement rests on
inlined verbatim: the project's definitions (identification algorithms — sampling, stopping and
output rules — and their laws, the PAC property, fixed budgets and fixed designs, the linear Gaussian environment, the simple regret, design matrices,
Gaussian widths, the structured action sets), and the handful of
[LML](https://github.com/LeanMachineLearning/LML) declarations they build on (`Algorithm`,
`Environment`, `history`, `IsAlgEnvSeq`, `obliviousEnv`, `stationaryEnv`, `detAlgorithm`), which
appear as clearly marked "vendored from LML" sections (`vendor/LML.lean.part`). The `sorry`s in
these files are the point: they are restatements to be verified, not part of the formalization,
and are excluded from `formalization.yaml`'s `sorry_count` (as the v0.4 spec prescribes).

When a definition in a statement's closure rests on a project *lemma* (for instance the
measurability lemma behind the output kernel on histories of variable length), referee leaves
that lemma's proof as `sorry` in the challenge too; comparator compares the proof terms of the
theorems in a closure, so such a lemma is listed in the config's `theorem_names` as an additional
target (comparator then verifies that the project proves it, with the challenged statement).
`scripts/make-challenges.py` does this automatically for every sorry'd lemma of a challenge.

`Solution.lean` is the other side: it just imports the project modules that state (phase 1) and
will prove (phase 2) the results.

A skeptical reader therefore only has to

1. read the one challenge file against the paper's statement, trusting only Mathlib for the
   imported notions, and
2. run comparator on the corresponding config.

If comparator succeeds, every theorem in the config's `theorem_names` is guaranteed to

1. be proved in this project **with exactly the challenged statement** (comparator checks that
   every constant in the statement's transitive closure — the inlined project definitions and the
   vendored LML declarations included, down to auxiliary `_proof_*` constants — is *identical*
   between the challenge and the project),
2. use no axioms beyond `propext`, `Classical.choice`, `Quot.sound`, and
3. be accepted by the Lean kernel, replayed from a `lean4export` dump inside a sandbox.

In particular the vendored LML sections cannot silently drift from upstream: comparator compares
them constant-for-constant against the LML package the project is built with.

## Regenerating the challenges

The challenge files are generated, not written by hand:

```bash
lake build                      # the project, so that referee can import it
scripts/make-challenges.py      # referee collect + extract, then vendoring; see its docstring
lake build Comparator           # every challenge must compile
```

`scripts/make-challenges.py` uses the `referee` tool of
[LeanMachineLearning/exposition](https://github.com/LeanMachineLearning/exposition) (a release
built for this project's toolchain; `gh release download <toolchain tag> -R
LeanMachineLearning/exposition --pattern 'referee-linux-x86_64-*.tar.gz'`), whose `extract`
subcommand produces one standalone file per declaration; the script then replaces the LML
imports by the vendored block. Rerun it whenever a headline statement or one of the definitions
it rests on changes.

## Running comparator

```bash
scripts/comparator-verify.sh                 # all configs
scripts/comparator-verify.sh gw_le_card      # one config
scripts/comparator-verify.sh --insecure ...  # without a landrun sandbox
```

The script clones and builds comparator and `lean4export` (pinned revision, project toolchain)
into `~/.cache/colt-2026-83/comparator-tools`, then runs each config from the repository root as

```bash
lake env path/to/comparator comparator/<name>.json
```

## Maintenance

The `Comparator` lake library (`lakefile.toml`) lists the challenge modules and `Solution` as
`globs`, with a stub root `Comparator.lean` that imports nothing: tools that import every library
root of the workspace (`checkdecls`, referee) must not load the challenges, which redeclare
project and LML names. Add any new challenge to the globs.

A module-system pitfall to keep in mind: comparator also compares the *values* of the theorems in
a statement's closure. A nested proof inside an `instance` (a theorem) of a `module` file is
abstracted into a module-private auxiliary constant, which a challenge file cannot reproduce;
nested proofs inside exposed `def`s become public auxiliaries and are fine. So the definitions a
headline statement rests on must not go through such an instance — `linearGaussianEnv` passes its
Markov-kernel proof inline for this reason. Statement identity can be checked before the proofs
exist by running comparator on a temporary copy of a config with `sorryAx` added to
`permitted_axioms`.
