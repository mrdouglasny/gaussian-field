/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# SchwartzNuclear: Proof that Schwartz space is a nuclear Fréchet space

This is the root import file for the `SchwartzNuclear` library.
Importing this file provides all exported results, including:

* `schwartz_nuclearSpace`: the `NuclearSpace (SchwartzMap D ℝ)` instance
  for any finite-dimensional real normed space `D`.

The proof proceeds via the Hermite function basis for `𝓢(ℝ)` and the
sequence space isomorphism `SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq`.

## References
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. 3-4
- Thangavelu, "Lectures on Hermite and Laguerre Expansions", Ch. 1
-/

import SchwartzNuclear.HermiteFunctions
import SchwartzNuclear.SchwartzHermiteExpansion
import SchwartzNuclear.Basis1D
import SchwartzNuclear.SchwartzSlicing
import SchwartzNuclear.HermiteNuclear
