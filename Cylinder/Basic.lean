/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder Test Function Space

Defines the test function space for the cylinder S¹_L × ℝ as the nuclear
tensor product C∞(S¹_L) ⊗̂ 𝓢(ℝ).

## Main definitions

- `CylinderTestFunction L` — test functions on S¹_L × ℝ

## Mathematical background

The cylinder S¹_L × ℝ is the natural geometry for Osterwalder-Schrader
axioms: the spatial direction is compact (circle of circumference L) while
the temporal direction is the full real line, giving a clean positive-time
half-space {t > 0}.

The test function space C∞(S¹_L) ⊗̂ 𝓢(ℝ) is nuclear Fréchet (tensor
product of nuclear spaces), so the Bochner-Minlos theorem applies.

## References

- Gel'fand-Vilenkin, *Generalized Functions* Vol. 4 (Nuclear spaces)
- Glimm-Jaffe, *Quantum Physics*, §6.1
- Osterwalder-Schrader (1973, 1975)
-/

import SmoothCircle.Nuclear
import SchwartzNuclear.HermiteNuclear
import Nuclear.NuclearTensorProduct
import GaussianField.Construction

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Cylinder test function space -/

/-- The test function space for the cylinder S¹_L × ℝ.

This is the nuclear tensor product C∞(S¹_L) ⊗̂ 𝓢(ℝ), where
- `SmoothMap_Circle L ℝ` = C∞(S¹_L): smooth L-periodic functions (spatial)
- `SchwartzMap ℝ ℝ` = 𝓢(ℝ): Schwartz-class functions (temporal)

The first factor is spatial (compact, periodic) and the second is
temporal (non-compact, for OS time reflection). -/
abbrev CylinderTestFunction := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ ℝ)

-- CylinderTestFunction L inherits DyninMityaginSpace from NuclearTensorProduct
example : DyninMityaginSpace (CylinderTestFunction L) := inferInstance

/-! ## Configuration space axioms

These are future proof targets. The Configuration space of the cylinder test functions
should be Polish and have the Borel σ-algebra coincide with the cylindrical σ-algebra.
Both follow from nuclearity of the test function space (standard for duals of
nuclear Fréchet spaces). -/

/-- Configuration(CylinderTestFunction L) is a Polish space.
This follows from the nuclear Fréchet structure of CylinderTestFunction L,
whose weak-* dual is metrizable, complete, and separable. -/
axiom configuration_cylinder_polish (L : ℝ) [Fact (0 < L)] :
    PolishSpace (Configuration (CylinderTestFunction L))

/-- The cylindrical σ-algebra on Configuration(CylinderTestFunction L) equals
the Borel σ-algebra. This is standard for Polish duals of nuclear Fréchet spaces. -/
axiom configuration_cylinder_borelSpace (L : ℝ) [Fact (0 < L)] :
    BorelSpace (Configuration (CylinderTestFunction L))

end GaussianField
