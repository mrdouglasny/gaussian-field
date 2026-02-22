# Point Evaluation and Downstream API

## HasPointEval typeclass (`Nuclear/PointEval.lean`)

`HasPointEval E M` is a typeclass associating a point type M with a test function
space E, together with pointwise evaluation:

```lean
class HasPointEval (E : Type*) (M : outParam Type*) where
  pointEval : E → M → ℝ
```

The `outParam` on M means Lean infers the domain type automatically from the
test function space.

### Instances

| Space E | Domain M | How evaluation works |
|---------|----------|---------------------|
| `SchwartzMap D ℝ` | `D` | Function application via `FunLike` |
| `SmoothMap_Circle L ℝ` | `ℝ` | Function application via `toFun` |
| `NuclearTensorProduct E₁ E₂` | `ℕ` | Coefficient access via `val` |
| `Fin N → ℝ` | `Fin N` | Function application |

The tensor product instance evaluates at coefficient index m (not at a
product-space point). For pointwise evaluation at (p₁, p₂) via eigenfunction
expansion, see `cylinderEval` in `HeatKernel/PositionKernel.lean`, which
computes:

```
f(θ, x) = Σ_m coeff_m(f) · ψ_n(θ) · φ_k(x)
```

A future `HasPointEval (NuclearTensorProduct E₁ E₂) (M₁ × M₂)` instance
using the factor-space bases is planned (see `docs/point-eval-plan.md`).

### Design rationale

We define our own lightweight typeclass rather than depending on Mathlib's
manifold infrastructure (`ContMDiffMap`) because:

- `ContMDiffMap` lacks Fréchet topology — cannot build `DyninMityaginSpace`
- `AddCircle L` has no manifold instance in Mathlib
- `SchwartzMap` requires a normed space domain, not a manifold

## GaussianFieldAPI.lean

This file collects imports and documents the public API that gaussian-field
exports for downstream QFT projects. After importing `GaussianFieldAPI`, the
following are available:

### Configuration space

```
GaussianField.Configuration E := WeakDual ℝ E
GaussianField.instMeasurableSpaceConfiguration  -- cylindrical σ-algebra
```

### Gaussian measure

For any `[DyninMityaginSpace E]`, Hilbert space H, and CLM `T : E →L[ℝ] H`:

| Name | Type signature | Description |
|------|---------------|-------------|
| `measure T` | `Measure (Configuration E)` | Centered Gaussian probability measure |
| `charFun T f` | integral identity | E[exp(iω(f))] = exp(-½‖Tf‖²) |
| `measure_centered T f` | `∫ ω f ∂μ = 0` | Zero mean |
| `cross_moment_eq_covariance T f g` | `∫ ω f · ω g ∂μ = ⟨Tf, Tg⟩` | Covariance identity |
| `measure_isProbability T` | instance | Probability measure |
| `pairing_integrable T f` | `Integrable` | Pairings are integrable |
| `pairing_memLp T f p` | `MemLp` | Pairings are in L^p for all finite p |

### Spectral CLM

| Name | Description |
|------|-------------|
| `spectralCLM σ hσ` | Multiplier CLM: f ↦ (σ_m · coeff_m(f))_m |
| `spectralCLM_coord` | Coordinate specification |
| `qftEigenvalue L mass m` | Eigenvalue of -Δ + m² on S¹_L × ℝ |
| `qftSingularValue L mass m` | σ_m = λ_m^{-1/2} |
| `qft_singular_values_bounded` | Boundedness (input for spectralCLM) |

### Point evaluation

| Name | Description |
|------|-------------|
| `HasPointEval E M` | Typeclass: E has evaluation at points of M |
| `HasPointEval.pointEval f x` | Evaluate f at x |

## Downstream consumers

- **[QFTFramework](https://github.com/mrdouglasny/QFTFramework)** uses the
  abstract structures (`Configuration`, `measure`) to fill `SpacetimeData.FieldConfig`
  and `QFTData.measure` slots.

- **[GFF](https://github.com/mrdouglasny/GFF)** imports `GaussianField`,
  `SmoothCircle`, and `HeatKernel` directly, plus `QFTFramework` for the
  abstract axiom framework.
