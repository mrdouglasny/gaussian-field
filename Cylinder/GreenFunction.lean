/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Green's Function on the Cylinder S¹_L × ℝ

Defines the Green's function (covariance) for the massive free field
on the cylinder via the **heat kernel integral representation**:

  `G(f, g) = ∫₀^∞ ⟨f, e^{-tA} g⟩_{L²} dt`

where `A = -Δ_{S¹} - ∂²/∂t² + m²` is the cylinder operator.

## Architecture

The proof chain uses two layers connecting to the heat semigroup:

1. **Mass operator** `T = A^{-1/2}` — a CLM to ℓ² satisfying `⟨Tf, Tg⟩ = G(f,g)`.
   Any symmetry that commutes with the heat semigroup `e^{-tA}` for all t ≥ 0
   also intertwines T with an isometry on ℓ². This follows because the
   covariance `C = ∫₀^∞ e^{-tA} dt` commutes with such symmetries (by linearity
   of the Bochner integral), and `T = C^{1/2}` inherits this equivariance.

2. **Green's function** `G(f,g) = ⟨Tf, Tg⟩` — algebraic properties (bilinearity,
   symmetry, nonnegativity) are free from the inner product structure.

## Main definitions

- `resolventFreq L mass n` — dispersion relation ω_n = √(λ_n + m²) (defined)
- `cylinderMassOperator L mass` — CLM T : CylinderTestFunction L → ℓ² (axiom)
- `cylinderGreen L mass` — bilinear form G_L(f,g) = ⟨Tf, Tg⟩ (defined)

## Main results

- `cylinderMassOperator_spatialTranslation_equivariant` — T equivariant (proved)
- `cylinderMassOperator_timeTranslation_equivariant` — T equivariant (proved)
- `cylinderMassOperator_timeReflection_equivariant` — T equivariant (proved)
- `cylinderGreen_spatialTranslation_invariant` — G invariant (proved)
- `cylinderGreen_timeTranslation_invariant` — G invariant (proved)
- `cylinderGreen_timeReflection_invariant` — G invariant (proved)

## Mathematical background

The Green's function on S¹_L × ℝ for the operator (-Δ_x - ∂²/∂t² + m²) is:

  `G((x,t), (x',t')) = Σ_n φ_n(x) φ_n(x') · exp(-ω_n |t-t'|) / (2ω_n)`

where φ_n are Fourier modes on S¹_L with eigenvalues λ_n = (2πn/L)²,
and ω_n = √(λ_n + m²) is the dispersion relation.

### Heat kernel integral representation

The covariance operator `C = A⁻¹` is the Bochner integral of the
cylinder heat semigroup:

  `C = ∫₀^∞ e^{-tA} dt = ∫₀^∞ e^{-m²t} · (e^{tΔ_{S¹}} ⊗ e^{tΔ_ℝ}) dt`

The integral converges because `e^{-m²t}` decays exponentially for m > 0.
The mass operator is `T = C^{1/2}` (or more precisely, the composition of
`A^{-1/2}` with the L² embedding into ℓ²).

### Why invariance follows from the heat kernel

If a symmetry S commutes with `e^{-tA}` for all t ≥ 0:

  `S ∘ e^{-tA} = e^{-tA} ∘ S`

then S commutes with the integral `C = ∫₀^∞ e^{-tA} dt` (linearity
of Bochner integral), and therefore with `T = C^{1/2}` as well.
The L² isometry condition (that S is unitary on L²(S¹×ℝ)) ensures
the ℓ² action is isometric: `T(Sf) = U(Tf)` for some isometry U.

### Temporal direction

**Important**: The temporal direction uses the free Laplacian `-d²/dt²`
(continuous spectrum on ℝ, diagonal in the Fourier basis), NOT the harmonic
oscillator `-d²/dt² + t²` (discrete spectrum, diagonal in Hermite basis).
The DMS basis for 𝓢(ℝ) is Hermite functions, but the resolvent
`(p² + ω²)^{-1/2}` is NOT diagonal in that basis.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1, §19.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
- Reed-Simon, *Methods of Modern Mathematical Physics* Vol. II, §X.12
-/

import Cylinder.FreeHeatSemigroup
import GaussianField.Construction

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Resolvent frequency (dispersion relation)

For each spatial Fourier mode n on S¹_L with eigenvalue λ_n = (2πk/L)²,
the dispersion relation gives the effective mass:

  `ω_n = √(λ_n + m²) = √((2πk/L)² + m²)`

This is the frequency that appears in the temporal resolvent kernel
`exp(-ω_n|t|)/(2ω_n)` and determines the mass gap of the theory. -/

/-- **Dispersion relation on the cylinder.**

  `ω_n = √((2πk/L)² + m²)`

where `k = fourierFreq(n)` is the spatial frequency of the n-th Fourier
mode on S¹_L. This is the resolvent frequency for the 1D operator
`-d²/dt² + ω_n²` acting on the temporal Schwartz functions. -/
def resolventFreq (mass : ℝ) (n : ℕ) : ℝ :=
  Real.sqrt ((2 * Real.pi * ↑(SmoothMap_Circle.fourierFreq n) / L) ^ 2 + mass ^ 2)

omit hL in
/-- The resolvent frequency is strictly positive when mass > 0. -/
theorem resolventFreq_pos (mass : ℝ) (hmass : 0 < mass) (n : ℕ) :
    0 < resolventFreq L mass n := by
  unfold resolventFreq
  apply Real.sqrt_pos_of_pos
  positivity

omit hL in
/-- The square of the resolvent frequency recovers the spatial eigenvalue + mass². -/
theorem resolventFreq_sq (mass : ℝ) (n : ℕ) :
    resolventFreq L mass n ^ 2 =
    (2 * Real.pi * ↑(SmoothMap_Circle.fourierFreq n) / L) ^ 2 + mass ^ 2 := by
  unfold resolventFreq
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

omit hL in
/-- The resolvent frequency is nonneg. -/
theorem resolventFreq_nonneg (mass : ℝ) (n : ℕ) :
    0 ≤ resolventFreq L mass n := by
  unfold resolventFreq
  exact Real.sqrt_nonneg _

omit hL in
/-- The resolvent frequency is at least the mass. -/
theorem resolventFreq_mass_le (mass : ℝ) (hmass : 0 ≤ mass) (n : ℕ) :
    mass ≤ resolventFreq L mass n := by
  unfold resolventFreq
  calc mass = Real.sqrt (mass ^ 2) := (Real.sqrt_sq hmass).symm
    _ ≤ Real.sqrt ((2 * Real.pi * ↑(SmoothMap_Circle.fourierFreq n) / L) ^ 2 + mass ^ 2) := by
        apply Real.sqrt_le_sqrt; linarith [sq_nonneg (2 * Real.pi * ↑(SmoothMap_Circle.fourierFreq n) / L)]

omit hL in
/-- The zero mode (n=0) has resolvent frequency equal to the mass. -/
theorem resolventFreq_zero_mode (mass : ℝ) (hmass : 0 ≤ mass) :
    resolventFreq L mass 0 = mass := by
  unfold resolventFreq
  simp [SmoothMap_Circle.fourierFreq, Real.sqrt_sq hmass]

/-! ## Mass operator (for Gaussian measure construction)

The mass operator `T = A^{-1/2} : CylinderTestFunction L → ℓ²` is the
square root of the covariance operator, composed with the L² embedding
into ℓ². It satisfies `⟨Tf, Tg⟩_{ℓ²} = G(f,g)` where G is the Green's
function (covariance bilinear form).

The mass operator is related to the covariance by `T*T = C` in the L² sense:

  `⟨Tf, Tg⟩_{ℓ²} = ⟨f, Cg⟩_{L²(S¹×ℝ)}`

This factorization is the content of the GNS construction applied to the
positive definite bilinear form `(f,g) ↦ ⟨f, Cg⟩_{L²}`. -/

/-- **The mass operator** `T = A^{-1/2} : CylinderTestFunction L → ℓ²`.

This is the GNS map for the covariance bilinear form: `⟨Tf, Tg⟩ = ⟨f, Cg⟩_{L²}`.
It decomposes by spatial Fourier mode: for mode n with dispersion relation
ω_n = `resolventFreq L mass n`, the temporal component undergoes the
Fourier multiplier `(p² + ω_n²)^{-1/2}` from `resolventMultiplierCLM`.

Used by `GaussianField.measure T` to construct the Gaussian probability
measure on `Configuration (CylinderTestFunction L)`. -/
axiom cylinderMassOperator (mass : ℝ) (hmass : 0 < mass) :
    CylinderTestFunction L →L[ℝ] ell2'

/-! ## Cylinder Green's function

Defined from the mass operator via the inner product on ℓ².
The algebraic properties follow from inner product space theory.

Equivalently, the Green's function is the L² pairing with the covariance operator:

  `G(f, g) = ⟨Tf, Tg⟩_{ℓ²} = ⟨f, Cg⟩_{L²(S¹×ℝ)} = ∫₀^∞ ⟨f, e^{-tA}g⟩_{L²} dt`

The heat kernel integral representation makes the physical content transparent:
the Green's function sums the heat kernel over all times. -/

/-- The continuum Green's function on the cylinder S¹_L × ℝ.

  `G_L(f, g) = ⟨T f, T g⟩_{ℓ²}`

where T is the mass operator. Equivalently, via the heat kernel integral:

  `G_L(f, g) = ∫₀^∞ ⟨f, e^{-tA} g⟩_{L²(S¹×ℝ)} dt`

In the mixed spectral/position representation:

  `G_L(f,g) = Σ_n ∫∫ f̂_n(t) ĝ_n(t') · exp(-ω_n|t-t'|) / (2ω_n) dt dt'`

where `f̂_n(t) = ∫₀ᴸ f(x,t) φ_n(x) dx` is the n-th Fourier mode,
and `ω_n = resolventFreq L mass n` is the dispersion relation. -/
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
the resolvent `(p² + ω_n²)^{-1/2}` being injective on 𝓢(ℝ) for each
mode n (since the Fourier multiplier vanishes nowhere). -/
axiom cylinderGreen_pos (mass : ℝ) (hmass : 0 < mass)
    (f : CylinderTestFunction L) (hf : f ≠ 0) :
    0 < cylinderGreen L mass hmass f f

/-! ## Heat kernel equivariance principle

If a CLM `S` commutes with the cylinder heat semigroup `e^{-tA}` for all
`t ≥ 0`, then the mass operator `T = A^{-1/2}` intertwines `S` with a
linear isometry `U` on ℓ²: `T(Sf) = U(Tf)`.

**Mathematical justification**: The proof goes through the covariance
operator `C = ∫₀^∞ e^{-tA} dt`. By linearity of the Bochner integral,
`[S, e^{-tA}] = 0` implies `[S, C] = 0`. Since `T*T = C` in the L²
sense, commutation with C implies `S` preserves the quadratic form
`⟨f, Cg⟩ = ⟨Tf, Tg⟩`, and any invertible map preserving a positive
definite form lifts to an isometry of the GNS Hilbert space. -/

/-- **Heat kernel equivariance principle for the mass operator.**

If a CLM `S` commutes with the cylinder heat semigroup `e^{-tA}` for
all `t ≥ 0`, then the mass operator `T` intertwines `S` with a linear
isometry `U` on ℓ²: `T(Sf) = U(Tf)`.

This single axiom replaces the previous three-step chain:
heat semigroup commutation → covariance commutation → mass operator
equivariance. -/
axiom cylinderMassOperator_equivariant_of_heat_comm
    (mass : ℝ) (hmass : 0 < mass)
    (S : CylinderTestFunction L →L[ℝ] CylinderTestFunction L)
    (h_heat : ∀ {t : ℝ} (ht : 0 ≤ t) (f : CylinderTestFunction L),
      cylinderHeatSemigroup L ht mass (S f) =
      S (cylinderHeatSemigroup L ht mass f)) :
    ∃ U : ell2' ≃ₗᵢ[ℝ] ell2',
    ∀ f, cylinderMassOperator L mass hmass (S f) =
         U (cylinderMassOperator L mass hmass f)

/-! ## Mass operator equivariance (proved from heat kernel principle)

Each equivariance theorem is proved by applying the heat kernel equivariance
principle to the corresponding cylinder heat semigroup equivariance theorem. -/

/-- The mass operator intertwines spatial translation with an isometry on ℓ².

Proved from `cylinderMassOperator_equivariant_of_heat_comm` using
`cylinderHeatSemigroup_spatialTranslation_comm`. -/
theorem cylinderMassOperator_spatialTranslation_equivariant
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ) :
    ∃ U : ell2' ≃ₗᵢ[ℝ] ell2',
    ∀ f, cylinderMassOperator L mass hmass (cylinderSpatialTranslation L v f) =
         U (cylinderMassOperator L mass hmass f) :=
  cylinderMassOperator_equivariant_of_heat_comm L mass hmass _ fun ht g =>
    cylinderHeatSemigroup_spatialTranslation_comm L ht mass v g

/-- The mass operator intertwines time translation with an isometry on ℓ².

Proved from `cylinderMassOperator_equivariant_of_heat_comm` using
`cylinderHeatSemigroup_timeTranslation_comm`. -/
theorem cylinderMassOperator_timeTranslation_equivariant
    (mass : ℝ) (hmass : 0 < mass) (τ : ℝ) :
    ∃ U : ell2' ≃ₗᵢ[ℝ] ell2',
    ∀ f, cylinderMassOperator L mass hmass (cylinderTimeTranslation L τ f) =
         U (cylinderMassOperator L mass hmass f) :=
  cylinderMassOperator_equivariant_of_heat_comm L mass hmass _ fun ht g =>
    cylinderHeatSemigroup_timeTranslation_comm L ht mass τ g

/-- The mass operator intertwines time reflection with an isometry on ℓ².

Proved from `cylinderMassOperator_equivariant_of_heat_comm` using
`cylinderHeatSemigroup_timeReflection_comm`. -/
theorem cylinderMassOperator_timeReflection_equivariant
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ U : ell2' ≃ₗᵢ[ℝ] ell2',
    ∀ f, cylinderMassOperator L mass hmass (cylinderTimeReflection L f) =
         U (cylinderMassOperator L mass hmass f) :=
  cylinderMassOperator_equivariant_of_heat_comm L mass hmass _ fun ht g =>
    cylinderHeatSemigroup_timeReflection_comm L ht mass g

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
