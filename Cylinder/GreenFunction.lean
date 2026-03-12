/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Green's Function on the Cylinder S¹_L × ℝ

Axiomatizes the Green's function (covariance) for the massive free field
on the cylinder and its key properties needed for OS axioms.

## Main definitions

- `cylinderGreen L mass` — bilinear form G_L(f,g) on `CylinderTestFunction L`
- `cylinderMassOperator L mass` — CLM T : CylinderTestFunction L → ℓ² for Gaussian construction

## Mathematical background

The Green's function on S¹_L × ℝ for the operator (-Δ + m²) is:

  `G((x,t), (x',t')) = Σ_n φ_n(x) φ_n(x') · exp(-√(λ_n + m²) |t-t'|) / (2√(λ_n + m²))`

where φ_n are Fourier modes on S¹_L with eigenvalues λ_n = (2πn/L)².

Unlike the torus, the Laplacian on ℝ has continuous spectrum. The
Green's function uses the mixed representation: spectral in x, position
in t. The Hermite basis diagonalizes the DM structure but NOT the
Laplacian, so `HasLaplacianEigenvalues` does not apply to the ℝ factor.

For the Gaussian measure construction, the covariance is realized via
a CLM `T : CylinderTestFunction L → H` into a Hilbert space, with
`G(f,g) = ⟨Tf, Tg⟩_H`.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1, §19.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Cylinder.Symmetry
import GaussianField.Construction

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Cylinder Green's function -/

/-- The continuum Green's function on the cylinder S¹_L × ℝ.

  `G_L(f, g) = ⟨f, (-Δ_{S¹} - ∂²_t + m²)⁻¹ g⟩`

This is a continuous bilinear form on `CylinderTestFunction L`, defined
by the resolvent of the Laplacian on S¹_L × ℝ. In the mixed
spectral/position representation:

  `G_L(f,g) = Σ_n ∫∫ f̂_n(t) ĝ_n(t') · exp(-√(λ_n + m²)|t-t'|) / (2√(λ_n + m²)) dt dt'`

where f̂_n(t) = ∫₀ᴸ f(x,t) φ_n(x) dx is the n-th Fourier mode of f. -/
axiom cylinderGreen (mass : ℝ) (hmass : 0 < mass) :
    CylinderTestFunction L → CylinderTestFunction L → ℝ

/-- The cylinder Green's function is bilinear. -/
axiom cylinderGreen_bilinear (mass : ℝ) (hmass : 0 < mass) :
    ∀ (r : ℝ) (f g h : CylinderTestFunction L),
      cylinderGreen L mass hmass (r • f + g) h =
      r * cylinderGreen L mass hmass f h + cylinderGreen L mass hmass g h

/-- The cylinder Green's function is symmetric. -/
axiom cylinderGreen_symm (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    cylinderGreen L mass hmass f g = cylinderGreen L mass hmass g f

/-- The cylinder Green's function is nonneg on the diagonal.

  `G_L(f,f) ≥ 0` for all f.

This follows from (-Δ + m²)⁻¹ being a positive operator. -/
axiom cylinderGreen_nonneg (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L) :
    0 ≤ cylinderGreen L mass hmass f f

/-- The cylinder Green's function is strictly positive on nonzero functions.

  `G_L(f,f) > 0` for f ≠ 0.

This follows from (-Δ + m²)⁻¹ being strictly positive (injective). -/
axiom cylinderGreen_pos (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L) (hf : f ≠ 0) :
    0 < cylinderGreen L mass hmass f f

/-- The diagonal of the cylinder Green's function is continuous.

  `f ↦ G_L(f, f)` is continuous on `CylinderTestFunction L`.

This is needed for OS1 (regularity): the bound uses G(f,f) as the
continuous seminorm. -/
axiom cylinderGreen_continuous_diag (mass : ℝ) (hmass : 0 < mass) :
    Continuous (fun f : CylinderTestFunction L => cylinderGreen L mass hmass f f)

/-! ## Invariance properties -/

/-- The cylinder Green's function is invariant under spatial translation.

  `G_L(T_v f, T_v g) = G_L(f, g)` for all v ∈ S¹_L.

Spectral proof: translation by v multiplies the n-th Fourier mode by
`exp(2πinv/L)`, so the product f̂_n · ĝ_n is unchanged (phase cancels). -/
axiom cylinderGreen_spatialTranslation_invariant
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ)
    (f g : CylinderTestFunction L) :
    cylinderGreen L mass hmass (cylinderSpatialTranslation L v f)
      (cylinderSpatialTranslation L v g) =
    cylinderGreen L mass hmass f g

/-- The cylinder Green's function is invariant under time translation.

  `G_L(T_τ f, T_τ g) = G_L(f, g)` for all τ ∈ ℝ.

The Green's function kernel K(x, t-t') depends only on the time
difference, so translation invariance is immediate. -/
axiom cylinderGreen_timeTranslation_invariant
    (mass : ℝ) (hmass : 0 < mass) (τ : ℝ)
    (f g : CylinderTestFunction L) :
    cylinderGreen L mass hmass (cylinderTimeTranslation L τ f)
      (cylinderTimeTranslation L τ g) =
    cylinderGreen L mass hmass f g

/-- The cylinder Green's function is invariant under time reflection.

  `G_L(Θf, Θg) = G_L(f, g)`.

The Green's function kernel K(x, |t-t'|) depends on |t-t'|, which is
invariant under t ↦ -t. -/
axiom cylinderGreen_timeReflection_invariant
    (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    cylinderGreen L mass hmass (cylinderTimeReflection L f)
      (cylinderTimeReflection L g) =
    cylinderGreen L mass hmass f g

/-! ## Mass operator (for Gaussian measure construction) -/

/-- The mass operator T : CylinderTestFunction L → ℓ² for the cylinder.

This is the square root of the covariance: G(f,g) = ⟨Tf, Tg⟩_{ℓ²}.
It maps test functions to rapidly decaying sequences via the spectral
representation of (-Δ + m²)^{-1/2}.

Used by `GaussianField.measure T` to construct the Gaussian probability
measure on `Configuration (CylinderTestFunction L)`. -/
axiom cylinderMassOperator (mass : ℝ) (hmass : 0 < mass) :
    CylinderTestFunction L →L[ℝ] ell2'

/-- The mass operator realizes the Green's function as an inner product.

  `G_L(f, g) = ⟨T f, T g⟩`

This is the nuclear factorization needed for the Gaussian measure construction. -/
axiom cylinderMassOperator_inner (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    cylinderGreen L mass hmass f g =
    @inner ℝ ell2' _ (cylinderMassOperator L mass hmass f) (cylinderMassOperator L mass hmass g)

end GaussianField
