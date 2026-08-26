/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import COLT83.MXJ2026.Upper
import COLT83.MXJ2026.LowerAdaptive
import COLT83.MXJ2026.LowerNonadaptive
import COLT83.MXJ2026.WidthBounds
import COLT83.MXJ2026.LogGains
import COLT83.MXJ2026.Separation
import COLT83.MXJ2026.NormEstimation

/-! # Comparator solution module

The solution side of the [comparator](https://github.com/leanprover/comparator) setup in
`comparator/`: this module imports the project files proving the headline results listed in
`formalization.yaml`, so its environment contains, at the exact names stated (with `sorry`) in
the `comparator/Challenge_*.lean` files, the headline theorems of the paper (see
`comparator/README.md`).

Nothing is restated here: comparator compares the challenge statements against this
environment's constants and replays the proofs through the kernel. -/
