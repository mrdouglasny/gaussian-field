/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Schwartz Space as a Nuclear Space

Provides the `NuclearSpace` instance for `SchwartzMap D ℝ` via the
sequence space isomorphism `SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq`.

The 5 axioms that were previously here (schwartzHermiteBasis, schwartzHermiteCoeff,
schwartz_hermite_expansion, schwartz_hermite_seminorm_growth,
schwartz_hermite_coefficient_decay) have been replaced by a single sorry
in `schwartzRapidDecayEquiv` (the topological isomorphism).

## References
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. 3-4
- Thangavelu, "Lectures on Hermite and Laguerre Expansions", Ch. 1
-/

import GaussianField.HermiteTensorProduct
