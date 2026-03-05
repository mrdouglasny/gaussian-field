/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Covariance and Gaussian Measure

Constructs the lattice covariance CLM into ℓ² via the spectral theorem for
the mass operator Q = -Δ + m², and the lattice Gaussian measure via
`GaussianField.measure`.

## Main definitions

- `latticeCovariance` — the CLM `T = Q^{-1/2} : FinLatticeField d N →L[ℝ] ell2'`
- `latticeGaussianMeasure` — centered Gaussian measure on the lattice

## Mathematical background

For the finite lattice with periodic BC, the covariance matrix is
  `C = (-Δ_a + m²)⁻¹`

The covariance CLM satisfies `⟨Tf, Tg⟩_ℓ² = ⟨f, Q⁻¹g⟩_L²` where Q is
the mass operator. This is constructed via the spectral decomposition
`T(f)(k) = λ_k^{-1/2} ⟪e_k, f⟫` where `{e_k}` are eigenvectors of Q.
-/

import Lattice.FiniteField
import Lattice.Laplacian
import Lattice.SpectralCovariance
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
    rw [latticeEigenvalue_eq]
    linarith [latticeLaplacianEigenvalue_nonneg d N a m]
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
Constructed via spectral decomposition of Q = -Δ + m²: maps
`f ↦ (k ↦ λ_k^{-1/2} ⟪e_k, f⟫)` where `{e_k, λ_k}` are the eigenvectors
and eigenvalues of the mass operator.

Satisfies `⟨Tf, Tg⟩_ℓ² = ⟨f, Q⁻¹g⟩_L²`. -/
noncomputable def latticeCovariance (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    FinLatticeField d N →L[ℝ] ell2' :=
  spectralLatticeCovariance d N a mass ha hmass

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
function of the mass operator:
  `E[ω(f)·ω(g)] = ⟨T(f), T(g)⟩_ℓ² = ⟨f, Q⁻¹g⟩_L²` -/

/-- The cross moment equals the abstract covariance. -/
theorem lattice_cross_moment (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeField d N) :
    ∫ ω : Configuration (FinLatticeField d N),
      (ω f) * (ω g) ∂(latticeGaussianMeasure d N a mass ha hmass) =
    GaussianField.covariance (latticeCovariance d N a mass ha hmass) f g :=
  GaussianField.cross_moment_eq_covariance _ f g

/-- The covariance equals the spectral expansion of Q⁻¹. -/
theorem lattice_covariance_eq_spectral (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeField d N) :
    GaussianField.covariance (latticeCovariance d N a mass ha hmass) f g =
    ∑ k : FinLatticeSites d N,
      (massEigenvalues d N a mass k)⁻¹ *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x) := by
  unfold covariance latticeCovariance
  exact spectralLatticeCovariance_inner d N a mass ha hmass f g

end GaussianField
