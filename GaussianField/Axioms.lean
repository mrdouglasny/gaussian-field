/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Schwartz Space as a Nuclear Space

Provides the `NuclearSpace` instance for `SchwartzMap D ℝ`.

The proof is developed in `SchwartzNuclear.HermiteTensorProduct`
via the sequence space isomorphism `SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq`.

## References
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. 3-4
- Thangavelu, "Lectures on Hermite and Laguerre Expansions", Ch. 1
-/

import GaussianField.NuclearSpace
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

open GaussianField

axiom schwartz_nuclearSpace
    (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [MeasurableSpace D] [BorelSpace D] [Nontrivial D] :
    NuclearSpace (SchwartzMap D ℝ)

noncomputable instance (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] [Nontrivial D] :
    NuclearSpace (SchwartzMap D ℝ) :=
  schwartz_nuclearSpace D
