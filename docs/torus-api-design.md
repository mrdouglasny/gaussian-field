# Continuum Embedding API Design

## Overview

The API provides the mathematical infrastructure to embed lattice field theories
into continuum configuration spaces and take the continuum limit. The key
ingredients are:

1. **Test function spaces** (`DyninMityaginSpace E`): Nuclear Fréchet spaces
   with Schauder bases — e.g. smooth periodic functions `C∞(S¹_L)`, Schwartz
   functions `𝓢(ℝ)`, or their tensor products. These carry a countable
   orthonormal basis `{e_m}` and dual coefficient functionals `{coeff_m}`
   with rapid decay. The basis is orthonormal with respect to the L² inner
   product determined by the geometry (period L for the circle, etc.).

2. **Configurations / distributions** (`Configuration E = WeakDual ℝ E`):
   Continuous linear functionals on the test function space. A lattice field
   `φ : Sites → ℝ` becomes a distribution via the embedding
   `f ↦ Σ_x φ(x) · eval_x(f)`.

3. **Point evaluation** (`circleEvalAtSite`, `evalTorusAtSite`): Continuous
   linear functionals that sample a test function at a lattice site with the
   correct `√(L/N)` normalization. The 2D evaluations are tensor products
   of 1D evaluations via `evalCLM`.

4. **Tensor products** (`NuclearTensorProduct E₁ E₂`): The completed
   projective tensor product of nuclear spaces, realized as a Köthe sequence
   space via Cantor pairing. The universal property `evalCLM` maps pairs of
   functionals `(φ₁, φ₂)` to a functional on the tensor product satisfying
   `evalCLM φ₁ φ₂ (f₁ ⊗ f₂) = φ₁(f₁) · φ₂(f₂)`.

5. **Heat kernel** (`heatKernelBilinear`): The primary analytic object,
   defined spectrally as `K_t(f,g) = Σ_m e^{-tμ_m} coeff_m(f) coeff_m(g)`
   where `μ_m` are eigenvalues of the Laplacian `-Δ` on the space
   (which depend on the geometry, e.g. the period L for the circle).
   The heat kernel **factors** under tensor product:
   `K_t^{E₁⊗E₂}(f₁⊗f₂, g₁⊗g₂) = K_t^{E₁}(f₁,g₁) · K_t^{E₂}(f₂,g₂)`.
   This is the foundational property that makes the 1D → 2D construction work.
   As `t → 0⁺`, the heat kernel converges to the L² inner product (identity
   kernel): `K_t(f,g) → ⟨f,g⟩_{L²} = Σ_m coeff_m(f) coeff_m(g)`.

6. **Green's function** (`greenFunctionBilinear`): Derived universally from
   the heat kernel as a Laplace transform:
   `G_m(f,g) = ∫₀^∞ e^{-tm²} K_t(f,g) dt = Σ_m coeff_m(f) coeff_m(g) / (μ_m + m²)`.
   The mass `m²` enters only here, not in the heat kernel. Unlike the heat
   kernel, the Green's function does **not** factor under tensor product
   (the mass integral couples the factors).

## Architecture

```
Layer 0: NuclearTensorProduct.evalCLM    (tensor product of functionals)
Layer 1: HeatKernel — heatKernelBilinear, greenFunctionBilinear   (universal, any DMS)
Layer 2: SmoothCircle — circleEvalAtSite, circleEmbedCLM          (1D)
Layer 3: Torus — evalTorusAtSite, torusEmbedCLM                    (2D = 1D ⊗ 1D)
```

## Layer 0: Tensor product of functionals (Nuclear/NuclearTensorProduct.lean)

Already exists. The key definition:

```lean
-- Tensor product of functionals: φ₁ ⊗ φ₂ on E₁ ⊗̂ E₂
def NuclearTensorProduct.evalCLM
    (φ₁ : E₁ →L[ℝ] ℝ) (φ₂ : E₂ →L[ℝ] ℝ) :
    NuclearTensorProduct E₁ E₂ →L[ℝ] ℝ

theorem evalCLM_pure (φ₁ φ₂) (e₁ e₂) :
    evalCLM φ₁ φ₂ (pure e₁ e₂) = φ₁ e₁ * φ₂ e₂
```

## Layer 1: Heat kernel and Green's function (HeatKernel/)

### Laplacian eigenvalues (HeatKernel/Bilinear.lean — new file)

Each `DyninMityaginSpace` can be equipped with eigenvalues of the Laplacian
`-Δ` associated to its geometry. The eigenvalues are nonneg (not strictly
positive — the zero mode `n=0` on the circle has `μ₀ = 0`). The mass is
**not** included; it enters only through the Green's function.

```lean
class HasLaplacianEigenvalues (E : Type*) [...] where
  eigenvalue : ℕ → ℝ
  eigenvalue_nonneg : ∀ m, 0 ≤ eigenvalue m
```

The eigenvalues depend implicitly on the metric/geometry of the space through
the DMS structure: the basis `{e_m}` is orthonormal w.r.t. the L² inner
product on the Riemannian manifold, and the eigenvalues are determined by
`-Δ e_m = μ_m e_m`.

### Heat kernel bilinear form

The heat kernel on a `DyninMityaginSpace E` is:

```
K_t(f, g) = Σ_m e^{-t μ_m} · coeff_m(f) · coeff_m(g)
```

This is a continuous bilinear form on E for each t > 0. The sum converges
absolutely because `coeff_m(f)` and `coeff_m(g)` are rapidly decreasing and
`e^{-tμ_m} ≤ 1`.

```lean
def heatKernelBilinear [HasLaplacianEigenvalues E] (t : ℝ) (ht : 0 < t)
    (f g : E) : ℝ :=
  ∑' m, Real.exp (-t * HasLaplacianEigenvalues.eigenvalue m) *
    DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g
```

### Identity at t = 0

As `t → 0⁺`, the heat kernel converges to the L² inner product:

```
lim_{t→0⁺} K_t(f,g) = Σ_m coeff_m(f) · coeff_m(g) = ⟨f,g⟩_{L²}
```

This is the spectral formulation of "the heat semigroup `e^{-tΔ}` converges
strongly to the identity". The proof is by dominated convergence:
`|e^{-tμ_m} coeff_m(f) coeff_m(g)| ≤ |coeff_m(f) coeff_m(g)|`, and the
dominator is summable by the rapid decay of Schauder coefficients.

```lean
-- The L² inner product via Schauder coefficients
def l2InnerProduct (f g : E) : ℝ :=
  ∑' m, DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g

-- Heat kernel → identity as t → 0⁺
theorem heatKernelBilinear_tendsto_l2
    [HasLaplacianEigenvalues E] (f g : E) :
    Tendsto (fun t => heatKernelBilinear t (by linarith) f g)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (l2InnerProduct f g))
```

### Multiplicative under tensor product

For `E₁ ⊗̂ E₂` with Laplacian eigenvalues `μ₁(n₁) + μ₂(n₂)` (Cantor-paired),
the heat kernel factors:

```
K_t^{E₁⊗E₂}(f₁⊗f₂, g₁⊗g₂) = K_t^{E₁}(f₁,g₁) · K_t^{E₂}(f₂,g₂)
```

This follows from `e^{-t(μ₁+μ₂)} = e^{-tμ₁} · e^{-tμ₂}` and the factorization
of coefficients on pure tensors: `coeff(pair(n₁,n₂))(f₁⊗f₂) = coeff(n₁)(f₁) · coeff(n₂)(f₂)`.

```lean
-- Tensor product Laplacian eigenvalues are sums
instance tensorProductHasLaplacianEigenvalues
    [HasLaplacianEigenvalues E₁] [HasLaplacianEigenvalues E₂] :
    HasLaplacianEigenvalues (NuclearTensorProduct E₁ E₂) where
  eigenvalue m :=
    let (n₁, n₂) := Nat.unpair m
    HasLaplacianEigenvalues.eigenvalue (E := E₁) n₁ +
      HasLaplacianEigenvalues.eigenvalue (E := E₂) n₂
  eigenvalue_nonneg m := add_nonneg
    (HasLaplacianEigenvalues.eigenvalue_nonneg (Nat.unpair m).1)
    (HasLaplacianEigenvalues.eigenvalue_nonneg (Nat.unpair m).2)

-- THE KEY THEOREM: heat kernel is multiplicative under tensor product
theorem heatKernelBilinear_tensorProduct
    [HasLaplacianEigenvalues E₁] [HasLaplacianEigenvalues E₂]
    (t : ℝ) (ht : 0 < t) (f₁ g₁ : E₁) (f₂ g₂ : E₂) :
    heatKernelBilinear t ht (pure f₁ f₂) (pure g₁ g₂) =
    heatKernelBilinear t ht f₁ g₁ * heatKernelBilinear t ht f₂ g₂
```

### Green's function: universal definition via Laplace transform

The Green's function is defined from the heat kernel for **any** space.
The mass `m²` enters here as the Laplace transform parameter:

```
G_mass(f, g) = ∫₀^∞ e^{-t·mass²} K_t(f, g) dt
```

The integral converges when mass > 0, because `K_t(f,f) ≤ ‖f‖²_{L²}` and
the exponential `e^{-t·mass²}` is integrable on `[0,∞)`.

Exchanging sum and integral gives the spectral representation:
```
G_mass(f,g) = Σ_m coeff_m(f) coeff_m(g) / (μ_m + mass²)
```

```lean
-- Green's function: Laplace transform of heat kernel
def greenFunctionBilinear [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (f g : E) : ℝ :=
  ∫ t in Set.Ioi 0,
    Real.exp (-t * mass ^ 2) * heatKernelBilinear t (by linarith) f g

-- Green's function equals the spectral sum
theorem greenFunctionBilinear_eq_spectralSum [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (f g : E) :
    greenFunctionBilinear mass hmass f g =
    ∑' m, DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g /
      (HasLaplacianEigenvalues.eigenvalue m + mass ^ 2)

-- Green's function is positive definite
theorem greenFunctionBilinear_pos [HasLaplacianEigenvalues E]
    (mass : ℝ) (hmass : 0 < mass) (f : E) (hf : f ≠ 0) :
    0 < greenFunctionBilinear mass hmass f f
```

### Green's function does NOT factor

```
G_mass(f₁⊗f₂, g₁⊗g₂) = ∫₀^∞ e^{-t·mass²} K_t^{E₁}(f₁,g₁) · K_t^{E₂}(f₂,g₂) dt
                         ≠ G_mass^{E₁}(f₁,g₁) · G_mass^{E₂}(f₂,g₂)
```

The mass exponential couples the t-integral. But the spectral sum
representation is still explicit:
```
G_mass(f₁⊗f₂, g₁⊗g₂) = Σ_{n₁,n₂} ĉ₁(n₁)ĉ₂(n₂)ĝ₁(n₁)ĝ₂(n₂) / (μ₁(n₁)+μ₂(n₂)+mass²)
```

## Layer 2: 1D circle (SmoothCircle/)

### Laplacian eigenvalues on S¹_L

The eigenvalues of `-Δ` on the circle `S¹_L = ℝ/Lℤ` are `(2πn/L)²` for
`n ∈ ℤ` (or `n ∈ ℕ` after pairing ±n via the real Fourier basis). The
orthonormal basis is `{cos(2πnx/L)/√(L/2), sin(2πnx/L)/√(L/2)}` — the `L`
enters both the eigenvalues and the basis normalization.

```lean
instance circleHasLaplacianEigenvalues (L : ℝ) [Fact (0 < L)] :
    HasLaplacianEigenvalues (SmoothMap_Circle L ℝ) where
  eigenvalue n := (2 * Real.pi * n / L) ^ 2
  eigenvalue_nonneg n := sq_nonneg _
```

With this instance, `heatKernelBilinear` and `greenFunctionBilinear` on the
circle are automatically available — no separate definition needed.

The circle heat kernel is:
```
K_t^{S¹_L}(f,g) = Σ_n e^{-t(2πn/L)²} coeff_n(f) coeff_n(g)
```

And the circle Green's function:
```
G_mass^{S¹_L}(f,g) = Σ_n coeff_n(f) coeff_n(g) / ((2πn/L)² + mass²)
```

### Circle embedding (SmoothCircle/Embedding.lean — new file)

```lean
-- Point evaluation at lattice site k (1D)
def circleEvalAtSite (L : ℝ) (N : ℕ) [NeZero N]
    (k : ZMod N) : SmoothMap_Circle L ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj k).comp (circleRestriction L N)

-- 1D lattice embedding: φ : ZMod N → ℝ ↦ Configuration(SmoothMap_Circle L ℝ)
def circleEmbedCLM (L : ℝ) (N : ℕ) [NeZero N]
    (φ : ZMod N → ℝ) : Configuration (SmoothMap_Circle L ℝ) where
  toFun f := ∑ k : ZMod N, φ k * circleEvalAtSite L N k f
  ...

-- 1D embedded two-point function
def circleEmbeddedTwoPoint (L : ℝ) (N : ℕ) [NeZero N] (mass : ℝ) (hmass : 0 < mass)
    (f g : SmoothMap_Circle L ℝ) : ℝ :=
  ∫ ω, ω f * ω g ∂(circleContinuumMeasure L N mass hmass)

-- 1D propagator convergence
-- circleEmbeddedTwoPoint L N mass f g → greenFunctionBilinear mass f g  as N → ∞
axiom circle_propagator_convergence ...
```

## Layer 3: 2D torus = circle ⊗ circle (Torus/)

### Eigenvalues on T²_L

The torus inherits Laplacian eigenvalues automatically from the tensor product
instance:

```lean
-- Automatic from tensorProductHasLaplacianEigenvalues:
-- eigenvalue(pair(n₁,n₂)) = (2πn₁/L)² + (2πn₂/L)²
```

The torus heat kernel factors:
```
K_t^{T²_L}(f₁⊗f₂, g₁⊗g₂) = K_t^{S¹_L}(f₁,g₁) · K_t^{S¹_L}(f₂,g₂)
```

The torus Green's function (with mass):
```
G_mass^{T²_L}(f,g) = Σ_{n₁,n₂} coeff(n₁,n₂)(f) coeff(n₁,n₂)(g) / ((2πn₁/L)² + (2πn₂/L)² + mass²)
```

### Torus embedding (Torus/Evaluation.lean — exists)

All 2D definitions are compositions of 1D circle definitions with `evalCLM`:

```lean
-- Point evaluation at 2D lattice site x ∈ (ℤ/Nℤ)²
def evalTorusAtSite (L : ℝ) (N : ℕ) [NeZero N]
    (x : FinLatticeSites 2 N) : TorusTestFunction L →L[ℝ] ℝ :=
  NuclearTensorProduct.evalCLM
    (circleEvalAtSite L N (x 0))
    (circleEvalAtSite L N (x 1))

-- 2D lattice embedding = sum of tensor products of 1D evaluations
def torusEmbedCLM (L : ℝ) (N : ℕ) [NeZero N]
    (φ : FinLatticeField 2 N) : Configuration (TorusTestFunction L) where
  toFun f := ∑ x : FinLatticeSites 2 N, φ x * evalTorusAtSite L N x f
  ...
```

### Torus Green's function

The Green's function on the torus is just `greenFunctionBilinear` applied to
`TorusTestFunction L`. No separate definition needed:

```lean
def torusContinuumGreen (L : ℝ) (mass : ℝ) (hmass : 0 < mass) :=
  @greenFunctionBilinear (TorusTestFunction L) _ ... mass hmass
```

## Propagator convergence

The convergence argument reduces to 1D via the heat kernel factorization:

1. **1D lattice eigenvalues converge**: `(4N²/L²)sin²(πn/N) → (2πn/L)²` as N→∞
2. **1D heat kernel converges**: by dominated convergence (each term converges,
   dominated by `|coeff_n(f) coeff_n(g)|` which is summable)
3. **2D heat kernel converges**: by the tensor product factorization, the 2D
   convergence follows from the 1D convergence
4. **Green's function converges**: integrate the heat kernel convergence in t,
   using `e^{-t·mass²}` as the integrable dominator

## File plan

### gaussian-field (torus branch)

| File | Content | Status |
|------|---------|--------|
| `Nuclear/NuclearTensorProduct.lean` | `evalCLM`, `evalCLM_pure` | Modified (sorry) |
| `HeatKernel/Axioms.lean` | `spectralCLM`, `heatSingularValue_factors` | Existing |
| `HeatKernel/Bilinear.lean` | `HasLaplacianEigenvalues`, `heatKernelBilinear`, `greenFunctionBilinear` | **New** |
| `SmoothCircle/Restriction.lean` | `circleRestriction` (ZMod N indexing) | Existing |
| `SmoothCircle/Embedding.lean` | `circleEvalAtSite`, `circleEmbedCLM` | **New** |
| `Torus/Restriction.lean` | `TorusTestFunction`, Polish/Borel axioms | Existing |
| `Torus/Evaluation.lean` | `evalTorusAtSite`, `torusEmbedCLM` (via 1D ⊗ 1D) | Existing |

### pphi2

| File | Content | Changes |
|------|---------|---------|
| `TorusEmbedding.lean` | `torusEmbedLift`, measures, two-point | Use `greenFunctionBilinear` |
| `TorusPropagatorConvergence.lean` | Convergence axiom, bounds | Unchanged |
| `TorusTightness.lean` | Tightness axiom | Unchanged |
| `TorusConvergence.lean` | Prokhorov (proved!) | Unchanged |
| `TorusGaussianLimit.lean` | Gaussian identification | Unchanged |
| `TorusInteractingLimit.lean` | Interacting limit (proved!) | Unchanged |

## Axiom/sorry summary

### gaussian-field

| Item | Type | File |
|------|------|------|
| `evalCLM` | sorry | `NuclearTensorProduct.lean` |
| `evalCLM_pure` | sorry | `NuclearTensorProduct.lean` |
| `heatKernelBilinear_tensorProduct` | sorry or theorem | `HeatKernel/Bilinear.lean` |
| `heatKernelBilinear_tendsto_l2` | sorry or theorem | `HeatKernel/Bilinear.lean` |
| `greenFunctionBilinear_eq_spectralSum` | sorry | `HeatKernel/Bilinear.lean` |
| `greenFunctionBilinear_pos` | sorry | `HeatKernel/Bilinear.lean` |
| `configuration_torus_polish` | axiom | `Torus/Restriction.lean` |
| `configuration_torus_borelSpace` | axiom | `Torus/Restriction.lean` |

### pphi2

| Item | Type | File |
|------|------|------|
| `torusContinuumGreen` | defined via `greenFunctionBilinear` | `TorusEmbedding.lean` |
| `torusEmbeddedTwoPoint_uniform_bound` | sorry | `TorusPropagatorConvergence.lean` |
| `torus_propagator_convergence` | axiom | `TorusPropagatorConvergence.lean` |
| `torusContinuumMeasures_tight` | axiom | `TorusTightness.lean` |
| `torusGaussianLimit_isGaussian` | axiom | `TorusGaussianLimit.lean` |
| `torus_interacting_tightness` | axiom | `TorusInteractingLimit.lean` |

## Design rationale: separating mass from Laplacian eigenvalues

We use `HasLaplacianEigenvalues` (eigenvalues of `-Δ` alone, nonneg) rather
than baking the mass into a `HasEigenvalues` class because:

1. **Tensor product correctness**: Laplacian eigenvalues add under tensor product:
   `μ_{T²}(n₁,n₂) = μ_{S¹}(n₁) + μ_{S¹}(n₂)`. If mass were baked in, we'd get
   `2m²` instead of `m²` for the torus.

2. **Heat kernel factorization**: `K_t^{mass} = e^{-t·mass²} · K_t^Δ`, and
   `K_t^Δ` factors multiplicatively. The mass is a universal scalar prefactor.

3. **Generalization**: The same `greenFunctionBilinear` works for any space
   (circle, torus, Schwartz on ℝ^d, etc.) — just provide `HasLaplacianEigenvalues`.

4. **Identity at t=0**: The mass-free heat kernel `K_t^Δ(f,g) → ⟨f,g⟩_{L²}` as
   `t→0⁺`, which is the correct spectral statement that `e^{-tΔ} → Id`.
