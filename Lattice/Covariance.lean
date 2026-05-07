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

/-! ## Covariance CLM (bare, counting inner product) -/

/-- The bare lattice covariance as a CLM into ℓ², in the **counting**
inner product on `FinLatticeField`.

Constructed via spectral decomposition of `Q = -Δ + m²`: maps
`f ↦ (k ↦ λ_k^{-1/2} ⟪e_k, f⟫)` where `{e_k, λ_k}` are the eigenvectors
and eigenvalues of the mass operator.

Satisfies `⟨Tf, Tg⟩_ℓ² = ⟨f, Q⁻¹g⟩_{counting}`.

This is the **operator-only** CLM — its spectral content reflects
`Q^{-1}` independently of any inner-product convention. The
**Glimm–Jaffe-aligned** CLM that determines the actual lattice GFF
covariance kernel is `latticeCovarianceGJ` below; it differs by a
scalar `(a^d)^{-1/2}` (i.e., the Riemann-sum vs counting inner-product
ratio). All existing spectral-identity lemmas about this CLM
(`spectralLatticeCovariance_inner`, `spectralLatticeCovariance_norm_sq`)
continue to hold without modification. -/
noncomputable def latticeCovariance (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    FinLatticeField d N →L[ℝ] ell2' :=
  spectralLatticeCovariance d N a mass ha hmass

/-- The Glimm–Jaffe-aligned lattice covariance CLM, used to construct
the lattice GFF measure with the textbook continuum-limit normalisation.

Defined as `(a^d)^{-1/2} • latticeCovariance` (scalar multiple of the
bare CLM). This implements the Riemann-sum inner product: instead of
Q^{-1} in counting, the kernel is `(a^d Q)^{-1} = a^{-d} Q^{-1}`,
so that the lattice 2-point function `(1/a^d)(Q^{-1})_{xy}` converges
to the textbook continuum Green's function on `T^d_L = (aℤ/N)^d` as
`a → 0` with `L = aN` fixed.

Reference: Glimm–Jaffe Eq. (6.1.6); Simon Ch. I. -/
noncomputable def latticeCovarianceGJ (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    FinLatticeField d N →L[ℝ] ell2' :=
  (Real.sqrt (a^d))⁻¹ • latticeCovariance d N a mass ha hmass

/-! ## Lattice Gaussian Measure -/

/-- The centered Gaussian measure on the finite lattice
(**Glimm–Jaffe-aligned normalisation**).

Constructed via `GaussianField.measure` from the GJ-aligned covariance
CLM `latticeCovarianceGJ`. Has covariance kernel `a^{-d} Q^{-1}`, so
the lattice 2-point function converges to the textbook continuum
Green's function on `T^d_L`.

Characteristic functional:
  `E[exp(i⟨ω,f⟩)] = exp(-½ ‖latticeCovarianceGJ(f)‖²) = exp(-(2 a^d)^{-1} ⟨f, Q⁻¹f⟩_counting)`. -/
noncomputable def latticeGaussianMeasure (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    @Measure (Configuration (FinLatticeField d N)) instMeasurableSpaceConfiguration :=
  GaussianField.measure (latticeCovarianceGJ d N a mass ha hmass)

/-- The lattice Gaussian measure is a probability measure. -/
instance latticeGaussianMeasure_isProbability (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    @IsProbabilityMeasure (Configuration (FinLatticeField d N))
      instMeasurableSpaceConfiguration
      (latticeGaussianMeasure d N a mass ha hmass) :=
  GaussianField.measure_isProbability _

/-! ## Covariance identity

The two-point function of the lattice Gaussian measure equals the
Glimm–Jaffe-aligned covariance:
  `E[ω(f)·ω(g)] = ⟨T_GJ(f), T_GJ(g)⟩_ℓ² = a^{-d} ⟨f, Q⁻¹g⟩_counting`

where `T_GJ = latticeCovarianceGJ`. The bare covariance CLM
`latticeCovariance` and its spectral identities are unchanged. -/

/-- The cross moment equals the GJ-aligned abstract covariance. -/
theorem lattice_cross_moment (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeField d N) :
    ∫ ω : Configuration (FinLatticeField d N),
      (ω f) * (ω g) ∂(latticeGaussianMeasure d N a mass ha hmass) =
    GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass) f g :=
  GaussianField.cross_moment_eq_covariance _ f g

/-- The bare covariance equals the (counting) spectral expansion of `Q⁻¹`. -/
theorem lattice_covariance_eq_spectral (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeField d N) :
    GaussianField.covariance (latticeCovariance d N a mass ha hmass) f g =
    ∑ k : FinLatticeSites d N,
      (massEigenvalues d N a mass k)⁻¹ *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x) := by
  unfold covariance latticeCovariance
  exact spectralLatticeCovariance_inner d N a mass ha hmass f g

/-- The GJ-aligned covariance equals `(a^d)⁻¹` times the bare covariance. -/
theorem latticeCovariance_GJ_eq_inv_smul_bare (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (f g : FinLatticeField d N) :
    GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass) f g =
    (a^d : ℝ)⁻¹ *
      GaussianField.covariance (latticeCovariance d N a mass ha hmass) f g := by
  have ha_d_pos : (0 : ℝ) < a^d := pow_pos ha d
  have hsqrt_sq : Real.sqrt (a^d) * Real.sqrt (a^d) = a^d :=
    Real.mul_self_sqrt (le_of_lt ha_d_pos)
  unfold latticeCovarianceGJ covariance
  simp only [ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
  -- Reduce conj-on-ℝ and combine the two scalar factors
  show (Real.sqrt (a^d))⁻¹ *
        ((Real.sqrt (a^d))⁻¹ *
          inner ℝ (latticeCovariance d N a mass ha hmass f)
            (latticeCovariance d N a mass ha hmass g)) =
      (a^d : ℝ)⁻¹ *
        inner ℝ (latticeCovariance d N a mass ha hmass f)
            (latticeCovariance d N a mass ha hmass g)
  rw [show (Real.sqrt (a^d))⁻¹ * ((Real.sqrt (a^d))⁻¹ *
        inner ℝ (latticeCovariance d N a mass ha hmass f)
          (latticeCovariance d N a mass ha hmass g)) =
      ((Real.sqrt (a^d))⁻¹ * (Real.sqrt (a^d))⁻¹) *
        inner ℝ (latticeCovariance d N a mass ha hmass f)
          (latticeCovariance d N a mass ha hmass g) from by ring]
  congr 1
  rw [show (Real.sqrt (a^d))⁻¹ * (Real.sqrt (a^d))⁻¹ =
      (Real.sqrt (a^d) * Real.sqrt (a^d))⁻¹ from by rw [mul_inv]]
  rw [hsqrt_sq]

/-- The GJ-aligned covariance equals the rescaled spectral expansion. -/
theorem lattice_covariance_GJ_eq_spectral (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (f g : FinLatticeField d N) :
    GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass) f g =
    (a^d : ℝ)⁻¹ *
    ∑ k : FinLatticeSites d N,
      (massEigenvalues d N a mass k)⁻¹ *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x) := by
  rw [latticeCovariance_GJ_eq_inv_smul_bare, lattice_covariance_eq_spectral]

end GaussianField
