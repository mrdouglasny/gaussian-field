/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Torus Test Function Space and Configuration Properties

Defines the 2D torus test function space as a tensor product of circle spaces,
and the Polish space instance for `Configuration(Torus L L)`.

## Main definitions

- `TorusTestFunction L` — smooth functions on the 2D torus T²_L
- `configuration_torus_polish` — Polish space instance for Configuration(TorusTestFunction L)

## Mathematical background

The 2D torus T²_L = (ℝ/Lℤ)² has test function space C∞(T²_L) ≅ C∞(S¹_L) ⊗̂ C∞(S¹_L),
the completed projective tensor product of periodic smooth functions in each variable.

As a nuclear Fréchet space, its configuration space (weak dual) is Polish,
which is the key property enabling Prokhorov's theorem.

## References

- Gel'fand-Vilenkin, *Generalized Functions* Vol. 4 (Nuclear spaces)
- Glimm-Jaffe, *Quantum Physics*, §6.1
-/

import SmoothCircle.Restriction
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

/-! ## Polish space instance for Configuration(Torus) -/

/-- **Configuration space of the torus is Polish.**

`Configuration(TorusTestFunction L)` = `WeakDual ℝ (TorusTestFunction L)` is a Polish space.

Mathematical justification:
- `TorusTestFunction L` is a nuclear Fréchet space (DyninMityagin).
- The weak-* dual of a nuclear Fréchet space is a countable union of compact
  metrizable sets, hence Polish.
- More precisely: nuclear Fréchet ⟹ Montel ⟹ semi-reflexive, and the
  strong dual of a nuclear Fréchet space is again nuclear Fréchet (hence Polish).

This lets us apply the **proved** `prokhorov_sequential` (which requires
Polish space) rather than the axiomatized `prokhorov_configuration_sequential`.

Reference: Schaefer, *Topological Vector Spaces* Ch. III §7, IV §9;
           Gel'fand-Vilenkin, *Generalized Functions* Vol. 4 Ch. IV. -/
axiom configuration_torus_polish :
    PolishSpace (Configuration (TorusTestFunction L))

/-- Borel space instance for Configuration(TorusTestFunction L).

The cylindrical σ-algebra on Configuration equals the Borel σ-algebra
of the weak-* topology for nuclear Fréchet spaces. -/
axiom configuration_torus_borelSpace :
    @BorelSpace (Configuration (TorusTestFunction L))
      (by exact inferInstance)
      instMeasurableSpaceConfiguration

end GaussianField
