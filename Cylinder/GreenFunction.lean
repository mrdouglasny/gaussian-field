/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Green's Function on the Cylinder S¹_L × ℝ

Defines the Green's function (covariance) for the massive free field
on the cylinder from the axiomatized mass operator, and proves its
algebraic properties from inner product space theory.

## Main definitions

- `cylinderMassOperator L mass` — CLM T : CylinderTestFunction L → ℓ² (axiom)
- `cylinderGreen L mass` — bilinear form G_L(f,g) = ⟨Tf, Tg⟩ (defined)

## Main results

- `cylinderGreen_spatialTranslation_invariant` — G is translation-invariant (proved)
- `cylinderGreen_timeTranslation_invariant` — G is time-translation-invariant (proved)
- `cylinderGreen_timeReflection_invariant` — G is reflection-invariant (proved)

All three invariance theorems are derived from mass operator equivariance
axioms via the isometry property ⟨Ux, Uy⟩ = ⟨x, y⟩.

## Mathematical background

The Green's function on S¹_L × ℝ for the operator (-Δ + m²) is:

  `G((x,t), (x',t')) = Σ_n φ_n(x) φ_n(x') · exp(-√(λ_n + m²) |t-t'|) / (2√(λ_n + m²))`

where φ_n are Fourier modes on S¹_L with eigenvalues λ_n = (2πn/L)².

The covariance is realized via the mass operator T : CylinderTestFunction L → ℓ²
(the square root of (-Δ + m²)⁻¹), with G(f,g) = ⟨Tf, Tg⟩_{ℓ²}.
The algebraic properties (bilinearity, symmetry, nonnegativity, continuity)
then follow from inner product space axioms.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1, §19.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Cylinder.Symmetry
import GaussianField.Construction

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Mass operator (for Gaussian measure construction)

The mass operator is the fundamental axiom: it encodes the spectral
data of (-Δ + m²)^{-1/2} on the cylinder. All properties of the
Green's function are derived from it. -/

/-- The mass operator T : CylinderTestFunction L → ℓ² for the cylinder.

This is the square root of the covariance: G(f,g) = ⟨Tf, Tg⟩_{ℓ²}.
It maps test functions to rapidly decaying sequences via the spectral
representation of (-Δ + m²)^{-1/2}.

Used by `GaussianField.measure T` to construct the Gaussian probability
measure on `Configuration (CylinderTestFunction L)`. -/
axiom cylinderMassOperator (mass : ℝ) (hmass : 0 < mass) :
    CylinderTestFunction L →L[ℝ] ell2'

/-! ## Cylinder Green's function

Defined from the mass operator via the inner product on ℓ².
The algebraic properties follow from inner product space theory. -/

/-- The continuum Green's function on the cylinder S¹_L × ℝ.

  `G_L(f, g) = ⟨T f, T g⟩_{ℓ²}`

where T is the mass operator (square root of (-Δ + m²)⁻¹).

Equivalently, in the mixed spectral/position representation:

  `G_L(f,g) = Σ_n ∫∫ f̂_n(t) ĝ_n(t') · exp(-√(λ_n + m²)|t-t'|) / (2√(λ_n + m²)) dt dt'`

where f̂_n(t) = ∫₀ᴸ f(x,t) φ_n(x) dx is the n-th Fourier mode of f. -/
def cylinderGreen (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) : ℝ :=
  @inner ℝ ell2' _ (cylinderMassOperator L mass hmass f)
    (cylinderMassOperator L mass hmass g)

/-- The mass operator realizes the Green's function as an inner product.

  `G_L(f, g) = ⟨T f, T g⟩` -/
theorem cylinderMassOperator_inner (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    cylinderGreen L mass hmass f g =
    @inner ℝ ell2' _ (cylinderMassOperator L mass hmass f)
      (cylinderMassOperator L mass hmass g) := rfl

/-- The cylinder Green's function is bilinear. -/
theorem cylinderGreen_bilinear (mass : ℝ) (hmass : 0 < mass) :
    ∀ (r : ℝ) (f g h : CylinderTestFunction L),
      cylinderGreen L mass hmass (r • f + g) h =
      r * cylinderGreen L mass hmass f h + cylinderGreen L mass hmass g h := by
  intro r f g h
  simp only [cylinderGreen, map_add, map_smul]
  rw [inner_add_left, real_inner_smul_left]

/-- The cylinder Green's function is symmetric. -/
theorem cylinderGreen_symm (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    cylinderGreen L mass hmass f g = cylinderGreen L mass hmass g f := by
  simp only [cylinderGreen]
  exact real_inner_comm _ _

/-- The cylinder Green's function is nonneg on the diagonal.

  `G_L(f,f) ≥ 0` for all f. -/
theorem cylinderGreen_nonneg (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L) :
    0 ≤ cylinderGreen L mass hmass f f := by
  simp only [cylinderGreen]
  exact real_inner_self_nonneg

/-- The diagonal of the cylinder Green's function is continuous.

  `f ↦ G_L(f, f)` is continuous on `CylinderTestFunction L`.

Follows from continuity of the mass operator T and the inner product. -/
theorem cylinderGreen_continuous_diag (mass : ℝ) (hmass : 0 < mass) :
    Continuous (fun f : CylinderTestFunction L => cylinderGreen L mass hmass f f) := by
  simp only [cylinderGreen]
  exact (cylinderMassOperator L mass hmass).continuous.inner
    (cylinderMassOperator L mass hmass).continuous

/-- The cylinder Green's function is strictly positive on nonzero functions.

  `G_L(f,f) > 0` for f ≠ 0.

This requires injectivity of the mass operator T, which follows from
(-Δ + m²)⁻¹ being strictly positive (the operator has no kernel). -/
axiom cylinderGreen_pos (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L) (hf : f ≠ 0) :
    0 < cylinderGreen L mass hmass f f

/-! ## Mass operator equivariance

The mass operator intertwines with each symmetry via a linear isometry
on ℓ²: `T(Sf) = U(Tf)` for an isometry U. This is the fundamental
spectral property of the operator `(-Δ + m²)^{-1/2}`:

- Spatial translation: Fourier modes pick up phases that cancel in G
- Time translation: the resolvent kernel depends on time difference
- Time reflection: the resolvent kernel depends on |t - t'|

These equivariance axioms imply Green's function invariance via the
isometry property `⟨Ux, Uy⟩ = ⟨x, y⟩`. -/

/-- The mass operator intertwines spatial translation with an isometry on ℓ². -/
axiom cylinderMassOperator_spatialTranslation_equivariant
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ) :
    ∃ U : ell2' ≃ₗᵢ[ℝ] ell2',
    ∀ f, cylinderMassOperator L mass hmass (cylinderSpatialTranslation L v f) =
         U (cylinderMassOperator L mass hmass f)

/-- The mass operator intertwines time translation with an isometry on ℓ². -/
axiom cylinderMassOperator_timeTranslation_equivariant
    (mass : ℝ) (hmass : 0 < mass) (τ : ℝ) :
    ∃ U : ell2' ≃ₗᵢ[ℝ] ell2',
    ∀ f, cylinderMassOperator L mass hmass (cylinderTimeTranslation L τ f) =
         U (cylinderMassOperator L mass hmass f)

/-- The mass operator intertwines time reflection with an isometry on ℓ². -/
axiom cylinderMassOperator_timeReflection_equivariant
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ U : ell2' ≃ₗᵢ[ℝ] ell2',
    ∀ f, cylinderMassOperator L mass hmass (cylinderTimeReflection L f) =
         U (cylinderMassOperator L mass hmass f)

/-! ## Invariance properties

Derived from mass operator equivariance: `G(Sf, Sg) = ⟨T(Sf), T(Sg)⟩ =
⟨U(Tf), U(Tg)⟩ = ⟨Tf, Tg⟩ = G(f, g)`, using the isometry property. -/

/-- The cylinder Green's function is invariant under spatial translation.

  `G_L(T_v f, T_v g) = G_L(f, g)` for all v ∈ S¹_L. -/
theorem cylinderGreen_spatialTranslation_invariant
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ)
    (f g : CylinderTestFunction L) :
    cylinderGreen L mass hmass (cylinderSpatialTranslation L v f)
      (cylinderSpatialTranslation L v g) =
    cylinderGreen L mass hmass f g := by
  simp only [cylinderGreen]
  obtain ⟨U, hU⟩ := cylinderMassOperator_spatialTranslation_equivariant L mass hmass v
  rw [hU f, hU g]
  exact U.inner_map_map _ _

/-- The cylinder Green's function is invariant under time translation.

  `G_L(T_τ f, T_τ g) = G_L(f, g)` for all τ ∈ ℝ. -/
theorem cylinderGreen_timeTranslation_invariant
    (mass : ℝ) (hmass : 0 < mass) (τ : ℝ)
    (f g : CylinderTestFunction L) :
    cylinderGreen L mass hmass (cylinderTimeTranslation L τ f)
      (cylinderTimeTranslation L τ g) =
    cylinderGreen L mass hmass f g := by
  simp only [cylinderGreen]
  obtain ⟨U, hU⟩ := cylinderMassOperator_timeTranslation_equivariant L mass hmass τ
  rw [hU f, hU g]
  exact U.inner_map_map _ _

/-- The cylinder Green's function is invariant under time reflection.

  `G_L(Θf, Θg) = G_L(f, g)`. -/
theorem cylinderGreen_timeReflection_invariant
    (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    cylinderGreen L mass hmass (cylinderTimeReflection L f)
      (cylinderTimeReflection L g) =
    cylinderGreen L mass hmass f g := by
  simp only [cylinderGreen]
  obtain ⟨U, hU⟩ := cylinderMassOperator_timeReflection_equivariant L mass hmass
  rw [hU f, hU g]
  exact U.inner_map_map _ _

end GaussianField
