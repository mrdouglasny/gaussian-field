# Heat Kernel Toolkit

The `HeatKernel/` module provides the spectral multiplier CLM construction and
position-space heat kernels needed to build covariance operators for quantum
field theories on product spaces.

## Spectral CLM (`HeatKernel/Axioms.lean`)

The central construction is `spectralCLM`:

```
spectralCLM (σ : ℕ → ℝ) (hσ : IsBoundedSeq σ) : E →L[ℝ] ell2'
```

Given a bounded multiplier sequence σ and a DyninMityaginSpace E, this produces
a continuous linear map f ↦ (σ_m · coeff_m(f))_m from E to ℓ². The m-th
coordinate of the output is `σ_m * DyninMityaginSpace.coeff m f`.

**Why it works:** DyninMityaginSpace.coeff_decay guarantees |coeff_m(f)| decays
faster than any polynomial. Multiplying by bounded σ_m preserves the (1+m)^{-2}
decay needed for ℓ² membership. This is a consequence of the proved theorem
`nuclear_ell2_embedding_from_decay` in `TargetFactorization.lean`.

**Status:** `spectralCLM` and `spectralCLM_coord` are axioms. They will be
replaced by proofs once the full heat kernel library is complete.

### Additional axioms

- `spectralCLM_zero` — zero multiplier gives zero CLM
- `spectralCLM_smul` — scalar multiplication commutes

### Bounded sequence helpers

- `IsBoundedSeq σ` — ∃ C, ∀ m, |σ m| ≤ C
- `isBoundedSeq_const`, `IsBoundedSeq.mul`, `IsBoundedSeq.const_mul`

## QFT eigenvalues and singular values

For the free scalar on S¹_L × ℝ with mass m > 0, the eigenvalues of -Δ + m²
on the product basis are:

```
qftEigenvalue L mass m =
  (2πn/L)² + (2k+1) + mass²    where (n,k) = unpair(m)
```

The first term comes from the Fourier modes on S¹_L, the second from the
Hermite/harmonic oscillator modes on ℝ, and the third from the mass.

The singular values σ_m = λ_m^{-1/2} define the covariance CLM:

```
qftSingularValue L mass m = (qftEigenvalue L mass m) ^ (-1/2)
```

**Proved:** `qftEigenvalue_pos` (eigenvalues are strictly positive for m > 0),
`qftSingularValue_nonneg`.

**Axiom:** `qft_singular_values_bounded` (singular values are bounded, since
all eigenvalues ≥ mass² > 0).

### Heat-regularized singular values

For the regularized theory at scale s > 0:

```
heatSingularValue L mass s m = exp(-(s/2) · qftEigenvalue L mass m)
```

**Proved:** `heatSingularValue_pos`, `heatSingularValue_le_one` (for s ≥ 0),
`heatSingularValue_factors` (factorization into mass × circle × oscillator),
`heat_singular_values_bounded` (bounded by 1 for s ≥ 0).

## Position-space heat kernels (`HeatKernel/PositionKernel.lean`)

### Mehler kernel (harmonic oscillator)

The heat kernel for H = -d²/dx² + x² on ℝ:

```
mehlerKernel t x₁ x₂ = (2π sinh 2t)^{-1/2} ·
  exp(-(cosh(2t)(x₁² + x₂²) - 2x₁x₂) / (2 sinh 2t))
```

Properties (axiomatized):
- Eigenfunction expansion: `mehlerKernel_eq_series`
- Positivity: `mehlerKernel_pos`
- Semigroup property: `mehlerKernel_semigroup`
- Reproducing property: `mehlerKernel_reproduces_hermite`

Proved: `mehlerKernel_symmetric` (by `ring_nf`).

### Circle heat kernel

The heat kernel on S¹_L, defined as eigenfunction expansion:

```
circleHeatKernel L t θ₁ θ₂ = Σ_n exp(-t(2πn/L)²) · ψ_n(θ₁) · ψ_n(θ₂)
```

Properties (axiomatized): summability, symmetry, positivity, periodicity,
eigenfunction reproducing, semigroup property.

### Cylinder heat kernel

The full heat kernel on S¹_L × ℝ factors as:

```
cylinderHeatKernel L mass t θ₁ x₁ θ₂ x₂ =
  exp(-m²t) · circleHeatKernel L t θ₁ θ₂ · mehlerKernel t x₁ x₂
```

**Proved from factor properties:** `cylinderHeatKernel_symmetric`,
`cylinderHeatKernel_pos`, `cylinderHeatKernel_periodic₁/₂`.

### Bridge to spectral CLM

The key bridge theorem connects position-space integration to spectral-space
multiplication:

```
∫∫ cylinderHeatKernel L mass t (θ,x) (θ',x') · f(θ',x') dθ' dx'
  = Σ_m exp(-t·λ_m) · coeff_m(f) · ψ_n(θ) · φ_k(x)
```

This says: convolving with the heat kernel in position space is the same as
multiplying Fourier-Hermite coefficients by exp(-tλ_m) in spectral space.
The `cylinderEval` function provides pointwise evaluation of tensor product
test functions via their eigenfunction expansion.

## Usage in downstream projects

The [GFF](https://github.com/mrdouglasny/GFF) repo constructs covariance CLMs via:

```lean
def cylinderGFF_T L mass hL hmass : CylinderTestFun L →L[ℝ] ell2' :=
  spectralCLM (fun m => qftSingularValue L mass m)
    (qft_singular_values_bounded L mass hL hmass)
```

This is the covariance operator T = (-Δ + m²)^{-1/2} for the Gaussian free field.
