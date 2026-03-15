/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Torus Test Function Space and Configuration Properties

Defines the 2D torus test function space as a tensor product of circle spaces.

## Main definitions

- `TorusTestFunction L` — smooth functions on the 2D torus T²_L

## References

- Gel'fand-Vilenkin, *Generalized Functions* Vol. 4 (Nuclear spaces)
- Glimm-Jaffe, *Quantum Physics*, §6.1
-/

import SmoothCircle.Restriction
import SmoothCircle.Nuclear
import Nuclear.NuclearTensorProduct
import GaussianField.Construction

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Torus test function space -/

/-- The test function space for the 2D torus T²_L.

This is the nuclear tensor product C∞(S¹_L) ⊗̂ C∞(S¹_L), which models
smooth L-periodic functions in two variables. It is a nuclear Fréchet
space, so the Bochner-Minlos theorem applies. -/
abbrev TorusTestFunction := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)

-- TorusTestFunction L inherits DyninMityaginSpace from NuclearTensorProduct
example : DyninMityaginSpace (TorusTestFunction L) := inferInstance

/-! ## Configuration space axioms

These are future proof targets. The Configuration space of the torus test functions
should be Polish and have the Borel σ-algebra coincide with the cylindrical σ-algebra.
See `future/configuration_torus.lean` for proof strategies. -/

-- Polish/Borel axioms moved to pphi2 (branch: cylinder) where they are used.
-- They are not needed by gaussian-field itself.

end GaussianField
