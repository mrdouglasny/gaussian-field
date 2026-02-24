/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gaussian Fields on Schwartz Spaces

This is the root import file for the project. It exports two main results:

## Result 1: Schwartz space satisfies the Dynin-Mityagin characterization

`schwartz_dyninMityaginSpace : DyninMityaginSpace (SchwartzMap D ℝ)`

Proved via the Hermite function basis for 𝓢(ℝ) and the sequence space
isomorphism `SchwartzMap D ℝ ≃L[ℝ] RapidDecaySeq`. See `SchwartzNuclear/`.

## Result 2: Gaussian measure construction on the weak dual

`GaussianField.measure T : Measure (Configuration E)` — a centered Gaussian
probability measure on E' = WeakDual ℝ E with covariance C(f,g) = ⟨T(f), T(g)⟩_H.

`GaussianField.charFun T f` — the characteristic functional identity:
  E[exp(i⟨ω, f⟩)] = exp(-½ ‖T(f)‖²)

See `GaussianField/Construction.lean` and `GaussianField/Properties.lean`.

## Axiom fallback

To use the axiom version of `schwartz_dyninMityaginSpace` instead of the full proof,
replace `import SchwartzNuclear` below with `import Nuclear.DyninMityagin`
and uncomment the axiom block at the bottom of this file.

## References
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. 3-4
- Thangavelu, "Lectures on Hermite and Laguerre Expansions", Ch. 1
-/

import SchwartzNuclear
import Nuclear.NuclearTensorProduct
import Nuclear.NuclearSpace
import GaussianField.SpectralTheorem
import GaussianField.NuclearSVD
import GaussianField.NuclearFactorization
import GaussianField.TargetFactorization
import GaussianField.Construction
import GaussianField.Properties
import GaussianField.Wick

/-! ### Axiom fallback (inactive)

Uncomment the block below and replace `import SchwartzNuclear` with
`import Nuclear.DyninMityagin` to use the axiom version. This is
safe: the proven instance in `SchwartzNuclear.HermiteTensorProduct`
establishes the same result as a theorem.

```
open GaussianField

axiom schwartz_dyninMityaginSpace_axiom -- count_axioms:skip
    (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [MeasurableSpace D] [BorelSpace D] [Nontrivial D] :
    DyninMityaginSpace (SchwartzMap D ℝ)

noncomputable instance (D : Type*) [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ D] [MeasurableSpace D] [BorelSpace D] [Nontrivial D] :
    DyninMityaginSpace (SchwartzMap D ℝ) :=
  schwartz_dyninMityaginSpace_axiom D
```
-/
