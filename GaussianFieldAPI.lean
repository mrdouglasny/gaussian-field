/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# QFT Framework API

This file exports the functional analysis infrastructure that gaussian-field
provides for use by downstream QFT formalization projects. It re-exports
key definitions and restates proved theorems in a clean axiomatic form.

## Contents

1. **HasPointEval** — pointwise evaluation typeclass
2. **Configuration** — weak dual as configuration space
3. **Gaussian measure API** — measure, characteristic functional, moments
4. **Spectral CLM** — multiplier construction for covariance operators

## What stays out

- Schwinger functions, OS axioms, generating functionals → downstream repos
- Concrete space abbreviations → downstream repos
- SpacetimeData instances → downstream repos
-/

import GaussianField
import Nuclear.PointEval
import HeatKernel

/-! ## Section 1: HasPointEval -/

-- Re-exported from Nuclear.PointEval
-- `GaussianField.HasPointEval E M` — typeclass with `pointEval : E → M → ℝ`
-- Instances: SchwartzMap, SmoothMap_Circle, NuclearTensorProduct, Fin N → ℝ

/-! ## Section 2: Configuration Space -/

-- Re-exported from GaussianField.Construction:
-- `GaussianField.Configuration E := WeakDual ℝ E`
-- `GaussianField.instMeasurableSpaceConfiguration` — cylindrical σ-algebra

/-! ## Section 3: Gaussian Measure API

The following are **proved theorems** in `GaussianField.Construction` and
`GaussianField.Properties`. We list them here as the public API.

For any DyninMityaginSpace `E`, Hilbert space `H`, and CLM `T : E →L[ℝ] H`:

- `GaussianField.measure T : Measure (Configuration E)` — centered Gaussian
  probability measure with covariance C(f,g) = ⟨T(f), T(g)⟩_H.

- `GaussianField.charFun T f` — characteristic functional identity:
  `∫ ω, exp(i · ω f) ∂(measure T) = exp(-½ ‖T f‖²)`

- `GaussianField.measure_centered T f` — centering:
  `∫ ω, ω f ∂(measure T) = 0`

- `GaussianField.cross_moment_eq_covariance T f g` — covariance:
  `∫ ω, ω f * ω g ∂(measure T) = ⟨T f, T g⟩_H`

- `GaussianField.measure_isProbability T` — probability measure instance
-/

/-! ## Section 4: Spectral CLM

Re-exported from `HeatKernel.Axioms`:

- `GaussianField.IsBoundedSeq σ` — ∃ C, ∀ m, |σ m| ≤ C
- `GaussianField.spectralCLM σ hσ : E →L[ℝ] ell2'` — multiplier CLM
- `GaussianField.spectralCLM_coord` — coordinate specification
- `GaussianField.qftEigenvalue L mass m` — eigenvalue of -Δ + m² on S¹_L × ℝ
- `GaussianField.qftSingularValue L mass m` — σ_m = λ_m^{-1/2}
- `GaussianField.qft_singular_values_bounded` — boundedness for spectralCLM input
-/

/-! ## Re-exported definitions

All definitions and theorems listed above are available via their fully qualified
names (e.g. `GaussianField.measure`, `GaussianField.charFun`) after importing
this file. -/
