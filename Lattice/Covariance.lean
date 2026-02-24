/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Covariance and Gaussian Measure

Constructs the lattice Green's function / covariance as a `spectralCLM` into
ℓ², and the lattice Gaussian measure via `GaussianField.measure`.

## Main definitions

- `latticeSingularValue` — eigenvalue^{-1/2} for spectral CLM
- `lattice_singular_values_bounded` — bounded sequence condition
- `latticeCovariance` — the CLM `FinLatticeField d N →L[ℝ] ell2'`
- `latticeGaussianMeasure` — centered Gaussian measure on the lattice

## Mathematical background

For the finite lattice with periodic BC, the covariance matrix is
  `C = (-Δ_a + m²)⁻¹`

Eigenvalues of `-Δ_a + m²`: `λ_k = (4/a²) Σᵢ sin²(πkᵢ/N) + m²`
These are all strictly positive when m > 0.

Singular values: `σ_m = λ_m^{-1/2}`
These are bounded by `1/m` (mass > 0), enabling the spectralCLM construction.
-/

import Lattice.FiniteField
import Lattice.Laplacian
import HeatKernel.Axioms
import GaussianField.Construction
import GaussianField.Properties

noncomputable section

namespace GaussianField

open MeasureTheory

variable (d N : ℕ) [NeZero N]

/-! ## Singular values -/

/-- Singular value for the lattice covariance: `λ_m^{-1/2}`. -/
def latticeSingularValue (a mass : ℝ) (m : ℕ) : ℝ :=
  (latticeEigenvalue d N a mass m) ^ (-(1 : ℝ) / 2)

/-- Singular values are nonneg. -/
theorem latticeSingularValue_nonneg (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (m : ℕ) :
    0 ≤ latticeSingularValue d N a mass m :=
  Real.rpow_nonneg (le_of_lt (latticeEigenvalue_pos d N a mass ha hmass m)) _

/-- The lattice singular values form a bounded sequence.
All eigenvalues satisfy `λ_m ≥ mass² > 0`, so `σ_m ≤ 1/mass`. -/
theorem lattice_singular_values_bounded (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsBoundedSeq (fun m => latticeSingularValue d N a mass m) := by
  refine ⟨mass⁻¹, fun m => ?_⟩
  rw [abs_of_nonneg (latticeSingularValue_nonneg d N a mass ha hmass m)]
  unfold latticeSingularValue
  have hev_pos := latticeEigenvalue_pos d N a mass ha hmass m
  -- Eigenvalue ≥ mass²
  have hev_ge : mass ^ 2 ≤ latticeEigenvalue d N a mass m := by
    unfold latticeEigenvalue; split_ifs with h
    · have : 0 ≤ 4 / a ^ 2 * ∑ i : Fin d,
          Real.sin (Real.pi * ↑((Fintype.equivFin (FinLatticeSites d N)).symm ⟨m, h⟩ i) / ↑N) ^ 2 :=
        mul_nonneg (div_nonneg (by norm_num) (sq_nonneg a))
          (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      linarith
    · linarith
  -- σ_m ≤ (mass²)^{-1/2} = mass⁻¹
  have h1 : (latticeEigenvalue d N a mass m) ^ (-(1:ℝ)/2) ≤ (mass ^ 2) ^ (-(1:ℝ)/2) :=
    Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hmass) hev_ge (by norm_num)
  have h2 : (mass ^ 2) ^ (-(1:ℝ)/2) = mass⁻¹ := by
    rw [← Real.rpow_natCast mass 2, ← Real.rpow_mul (le_of_lt hmass)]
    norm_num
    exact Real.rpow_neg_one mass
  linarith

/-! ## Covariance CLM -/

/-- The lattice covariance as a CLM into ℓ².
Constructed via `spectralCLM` with the lattice singular values. -/
noncomputable def latticeCovariance (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    FinLatticeField d N →L[ℝ] ell2' :=
  spectralCLM
    (fun m => latticeSingularValue d N a mass m)
    (lattice_singular_values_bounded d N a mass ha hmass)

/-! ## Lattice Gaussian Measure -/

/-- The centered Gaussian measure on the finite lattice.
Constructed via `GaussianField.measure` from the covariance CLM.

This is the measure with characteristic functional:
  `E[exp(i⟨ω,f⟩)] = exp(-½ ‖T(f)‖²)`
where `T = latticeCovariance`.

The covariance is:
  `E[ω(f) · ω(g)] = ⟨T(f), T(g)⟩_ℓ² = ((-Δ_a + m²)⁻¹ f, g)` -/
noncomputable def latticeGaussianMeasure (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    @Measure (Configuration (FinLatticeField d N)) instMeasurableSpaceConfiguration :=
  GaussianField.measure (latticeCovariance d N a mass ha hmass)

/-- The lattice Gaussian measure is a probability measure. -/
instance latticeGaussianMeasure_isProbability (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    @IsProbabilityMeasure (Configuration (FinLatticeField d N))
      instMeasurableSpaceConfiguration
      (latticeGaussianMeasure d N a mass ha hmass) :=
  GaussianField.measure_isProbability _

/-! ## Covariance identity

The two-point function of the lattice Gaussian measure equals the Green's
function of the mass operator, following automatically from the general
GaussianField API:
  `E[ω(f)·ω(g)] = ⟨T(f), T(g)⟩_ℓ² = G_a(f,g) = ((-Δ_a + m²)⁻¹ f, g)` -/

theorem lattice_cross_moment (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeField d N) :
    ∫ ω : Configuration (FinLatticeField d N),
      (ω f) * (ω g) ∂(latticeGaussianMeasure d N a mass ha hmass) =
    GaussianField.covariance (latticeCovariance d N a mass ha hmass) f g :=
  GaussianField.cross_moment_eq_covariance _ f g

end GaussianField
