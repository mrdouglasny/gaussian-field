# Position-Space Heat Kernel Plan

## Goal

Define the heat kernel K(x, y, t) as a function on (S¹_L × ℝ)² × ℝ₊ and
connect it to the spectral CLM already constructed in `HeatKernel/Axioms.lean`.

Currently we have the **spectral side**: the CLM `heatCovarianceCLM` acts on
basis coefficients by diagonal multiplication `e^{-tλ_m/2}`. We need the
**position side**: the kernel function whose integral against test functions
reproduces the spectral action.

## Mathematical content

### The eigenfunction expansion

The heat kernel on S¹_L × ℝ for the operator A = -∂²/∂θ² + H_x + m²
(where H_x = -∂²/∂x² + x² is the harmonic oscillator) is:

```
K((θ₁,x₁), (θ₂,x₂), t) = Σ_{n,k} e^{-tλ_{n,k}} ψ_n(θ₁)ψ_n(θ₂) φ_k(x₁)φ_k(x₂)
```

where:
- ψ_n = fourierBasisFun n : Fourier basis on S¹_L
- φ_k = hermiteFunction k : Hermite functions on ℝ
- λ_{n,k} = (2πn/L)² + (2k+1) + m² = qftEigenvalue L m (Nat.pair n k)

### Factorization

Since λ_{n,k} = λ^circle_n + λ^osc_k + m², the kernel factors:

```
K = e^{-m²t} · K_circle(θ₁, θ₂, t) · K_osc(x₁, x₂, t)
```

where:
- **K_circle(θ₁, θ₂, t)** = Σ_n e^{-t(2πn/L)²} ψ_n(θ₁)ψ_n(θ₂)
  = Jacobi theta function θ₃((θ₁-θ₂)/L, e^{-4π²t/L²}) / L

- **K_osc(x₁, x₂, t)** = Σ_k e^{-t(2k+1)} φ_k(x₁) φ_k(x₂)
  = Mehler kernel = (2π sinh 2t)^{-1/2} exp(-(cosh(2t)(x₁²+x₂²) - 2x₁x₂)/(2 sinh 2t))

### Connection to the spectral CLM

For test function f ∈ C^∞(S¹_L) ⊗̂ S(ℝ), the spectral action is:

```
(T_t f)_m = e^{-tλ_m/2} · coeff_m(f)
```

The position-space action is:

```
(T_t f)(θ, x) = ∫∫ K((θ,x), (θ',x'), t/2) f(θ', x') dθ' dx'
```

These are equal: substituting the eigenfunction expansion of K and f gives
the same series. The key identity is:

```
coeff_m(f) = ∫∫ f(θ', x') ψ_n(θ') φ_k(x') dθ' dx'   [where (n,k) = unpair m]
```

## What exists

### In our codebase

| Component | File | Status |
|-----------|------|--------|
| `fourierBasisFun n x` | `SmoothCircle/Basic.lean:289` | Defined: trig functions |
| `fourierBasis n` | `SmoothCircle/Basic.lean:336` | ∈ SmoothMap_Circle |
| `fourierCoeffReal n f` | `SmoothCircle/Basic.lean:372` | = ∫ f·ψ_n on [0,L] |
| `fourierCoeffCLM n` | `SmoothCircle/Basic.lean:431` | CLM version |
| `hermiteFunction n x` | `SchwartzNuclear/HermiteFunctions.lean:75` | = c_n H_n(x√2) e^{-x²/2} |
| `schwartzHermiteBasis1D n` | `SchwartzNuclear/SchwartzHermiteExpansion.lean:49` | ∈ SchwartzMap ℝ ℝ |
| `hermiteCoeff1D n f` | `SchwartzNuclear/SchwartzHermiteExpansion.lean:66` | = ∫ f·φ_n |
| `hermiteCoeff1DCLM n` | `SchwartzNuclear/Basis1D.lean:29` | CLM version |
| `spectralCLM σ hσ` | `HeatKernel/Axioms.lean:57` | Axiom: E →L[ℝ] ℓ² |
| `qftEigenvalue L mass m` | `HeatKernel/Axioms.lean` | = (2πn/L)² + (2k+1) + m² |
| `heatSingularValue L mass s m` | `HeatKernel/Axioms.lean` | = e^{-(s/2)λ_m} |
| `heatSingularValue_factors` | `HeatKernel/Axioms.lean` | Proved: mass × circle × osc |

### In Mathlib

| Component | Location | Relevance |
|-----------|----------|-----------|
| `gaussianPDFReal μ v x` | `Probability.Distributions.Gaussian.Real` | Heat kernel on ℝ for Laplacian (NOT harmonic oscillator) |
| `jacobiTheta τ` | `NumberTheory.ModularForms.JacobiTheta` | Heat kernel on S¹ (theta function) |
| `integral_gaussian b` | `Analysis.SpecialFunctions.Gaussian` | ∫ e^{-bx²} = √(π/b) |
| `fourierIntegral_gaussian` | `Analysis.SpecialFunctions.Gaussian.FourierTransform` | Fourier transform of Gaussian |
| `hasSum_fourier_series_of_summable` | `Analysis.Fourier.AddCircle` | Pointwise convergence on S¹ |
| `hermite n` | `RingTheory.Polynomial.HermitePolynomials` | Probabilist's Hermite polynomials |
| `Kernel` (Markov) | `Probability.Kernel.Defs` | Framework for measure-valued kernels |

### NOT in Mathlib

- Mehler kernel (harmonic oscillator heat kernel) — needs definition and proof
- Evaluation of NuclearTensorProduct elements at points — needs bridge
- L² orthogonality of Hermite functions (we have it implicitly via Schauder basis)

## Implementation plan

### File structure

```
HeatKernel/
  Axioms.lean          — existing: spectralCLM axioms
  Eval.lean            — pointwise evaluation for tensor products
  CircleKernel.lean    — heat kernel on S¹_L (theta function)
  MehlerKernel.lean    — Mehler kernel (harmonic oscillator)
  PositionKernel.lean  — full K(x,y,t) and connection to spectralCLM
```

### Step 1: Pointwise evaluation bridge (`Eval.lean`)

**Problem**: `NuclearTensorProduct E₁ E₂` is defined as `RapidDecaySeq`
(sequence space). Elements are ℕ-indexed coefficient sequences, not functions.
We need to evaluate them at points.

**Approach**: Define evaluation via the eigenfunction expansion.

```
/-- Evaluate a cylinder test function at a point (θ, x). -/
def Cylinder.eval (L : ℝ) (f : Cylinder L) (θ x : ℝ) : ℝ :=
  ∑' m, DyninMityaginSpace.coeff m f *
    fourierBasisFun (m.unpair).1 θ * hermiteFunction (m.unpair).2 x
```

**Required lemmas**:
- Convergence of the series (from rapid decay of coefficients × polynomial
  growth of eigenfunctions)
- `Cylinder.eval_basis`: evaluation of pure basis elements
- Consistency with the SmoothMap_Circle and SchwartzMap evaluations on
  pure tensors

**Dependencies**: `fourierBasisFun` from SmoothCircle, `hermiteFunction`
from SchwartzNuclear.

### Step 2: Circle heat kernel (`CircleKernel.lean`)

**Definition**:
```
/-- Heat kernel on S¹_L. -/
def circleHeatKernel (L t θ₁ θ₂ : ℝ) : ℝ :=
  ∑' n, exp(-t * (2*π*n/L)²) * fourierBasisFun n θ₁ * fourierBasisFun n θ₂
```

**Key results**:
- `circleHeatKernel_convergence`: series converges for t > 0
- `circleHeatKernel_eq_theta`: equals θ₃ expression for closed form
- `circleHeatKernel_symmetric`: K(θ₁,θ₂) = K(θ₂,θ₁)
- `circleHeatKernel_semigroup`: ∫ K(·,z,s) K(z,·,t) dz = K(·,·,s+t)
- `circleHeatKernel_reproduces_fourier`:
    ∫₀ᴸ K(θ₁,θ₂,t) ψ_n(θ₂) dθ₂ = e^{-t(2πn/L)²} ψ_n(θ₁)

**Mathlib support**: `jacobiTheta` gives the theta function; we need to
connect our Fourier basis indexing to the standard theta function form.

The closed form is:
```
circleHeatKernel L t θ₁ θ₂ =
  (1/L) * jacobiTheta₃((θ₁-θ₂)/(2L), exp(-4π²t/L²))
```

where θ₃(z, q) = 1 + 2 Σ_{n≥1} q^{n²} cos(2nπz). Alternatively, using
Poisson summation:

```
circleHeatKernel L t θ₁ θ₂ =
  (1/√(4πt)) Σ_{k∈ℤ} exp(-(θ₁ - θ₂ + kL)² / (4t))
```

This is a periodized Gaussian — may be easier to work with than theta
functions for some proofs.

### Step 3: Mehler kernel (`MehlerKernel.lean`)

**Definition**:
```
/-- Mehler kernel: heat kernel for the harmonic oscillator H = -d²/dx² + x². -/
def mehlerKernel (t x₁ x₂ : ℝ) : ℝ :=
  (2 * π * sinh(2*t))⁻¹ᐟ² *
  exp(-(cosh(2*t) * (x₁² + x₂²) - 2 * x₁ * x₂) / (2 * sinh(2*t)))
```

**Alternatively** (eigenfunction expansion):
```
def mehlerKernel' (t x₁ x₂ : ℝ) : ℝ :=
  ∑' k, exp(-t * (2*k + 1)) * hermiteFunction k x₁ * hermiteFunction k x₂
```

**Key results**:
- `mehlerKernel_eq_series`: closed form equals eigenfunction expansion
- `mehlerKernel_convergence`: series converges for t > 0
- `mehlerKernel_symmetric`: K(x₁,x₂) = K(x₂,x₁)
- `mehlerKernel_semigroup`: ∫ K(·,z,s) K(z,·,t) dz = K(·,·,s+t)
- `mehlerKernel_reproduces_hermite`:
    ∫ K(x₁,x₂,t) φ_k(x₂) dx₂ = e^{-t(2k+1)} φ_k(x₁)
- `mehlerKernel_t0_limit`: K(x₁,x₂,t) → δ(x₁-x₂) as t → 0

**Proof of closed form**: The Mehler formula follows from the generating
function for Hermite polynomials:

```
Σ_k (r^k / k!) H_k(x) H_k(y) = (1-r²)^{-1/2} exp((2xyr - (x²+y²)r²)/(1-r²))
```

Setting r = e^{-2t} and including the normalization/weight gives Mehler.

**Mathlib support**: `hermite n` (Hermite polynomials) exists. We need
`Real.sinh`, `Real.cosh` (exist in Mathlib), and the generating function
identity (likely not in Mathlib — needs proof or axiom).

### Step 4: Full position-space kernel (`PositionKernel.lean`)

**Definition**:
```
/-- Heat kernel on S¹_L × ℝ for the operator -∂²/∂θ² + H_x + m². -/
def cylinderHeatKernel (L mass t : ℝ) (θ₁ x₁ θ₂ x₂ : ℝ) : ℝ :=
  exp(-mass² * t) * circleHeatKernel L t θ₁ θ₂ * mehlerKernel t x₁ x₂
```

**Key results**:
- `cylinderHeatKernel_factored`: equals the product form
- `cylinderHeatKernel_eq_series`: equals the eigenfunction expansion
    Σ_{n,k} e^{-tλ_{n,k}} ψ_n(θ₁)φ_k(x₁) ψ_n(θ₂)φ_k(x₂)
- `cylinderHeatKernel_reproduces`:
    ∫∫ K(·,y,t) f(y) dy = spectralCLM (heatSingularValue t²) f evaluated at ·
- `cylinderHeatKernel_semigroup`: K(·,·,s) ∗ K(·,·,t) = K(·,·,s+t)
- `cylinderHeatKernel_symmetric`: K(x,y,t) = K(y,x,t)
- `cylinderHeatKernel_positive`: K(x,y,t) > 0 for t > 0

### Step 5: Bridge theorem

The central result connecting spectral and position:

```
/-- The spectral CLM equals integration against the position-space kernel.
    For f ∈ C^∞(S¹_L) ⊗̂ S(ℝ) and t > 0:
    (heatCovarianceCLM f)(θ, x) = ∫∫ K((θ,x), (θ',x'), t/2) f(θ', x') dθ' dx' -/
theorem heatCovarianceCLM_eq_integral ...
```

This requires:
1. Evaluating `spectralCLM` at a point (via `Cylinder.eval`)
2. Writing the integral as a series (Fubini)
3. Matching term-by-term with the spectral expansion

## Dependency graph

```
                    Eval
                   ↗    ↘
CircleKernel ──→ PositionKernel
                   ↗
MehlerKernel ──→
```

All import `HeatKernel/Axioms.lean` for eigenvalue definitions.

## Difficulty assessment

| Component | Difficulty | Notes |
|-----------|-----------|-------|
| Eval.lean | Medium | Convergence of eigenfunction expansion; needs growth/decay interplay |
| CircleKernel.lean | Medium | Connecting to Mathlib's jacobiTheta or periodized Gaussian |
| MehlerKernel.lean | Hard | Mehler formula proof from Hermite generating function; not in Mathlib |
| PositionKernel.lean | Medium | Mostly assembling pieces; Fubini for eigenfunction series |
| Bridge theorem | Hard | Integral identity requires careful convergence arguments |

## Axiom budget

If building fully is too slow, axiomatize:
- `mehlerKernel_eq_series` (closed form = eigenfunction series)
- `cylinderHeatKernel_reproduces` (bridge to spectral CLM)
- Convergence of eigenfunction series

The circle kernel can likely be proved from Mathlib's theta function API.
The Mehler kernel closed form is the hardest piece.

## Existing infrastructure across projects

### auto1: Hermite polynomials (algebraic)

The `auto1` project has a variance-parametrized Hermite polynomial `probHermite n c`
with the following proved results:

| Result | Theorem | File |
|--------|---------|------|
| Definition + special values H₀–H₅ | `probHermite_zero`, ..., `probHermite_five` | Hermite/Basic.lean |
| Three-term recurrence | `probHermite_recurrence` | Hermite/Basic.lean |
| Derivative formula d/dx H_{n+1} = (n+1)H_n | `probHermite_derivative` | Hermite/Basic.lean |
| Monic, degree properties | `probHermite_monic`, `probHermite_degree` | Hermite/Basic.lean |
| Connection to Mathlib hermite | `probHermite_one_eq_hermite_map` | Hermite/Basic.lean |
| **Addition formula** H_n(x+a;c) = Σ C(n,k)a^k H_{n-k}(x;c) | `probHermite_addition` | Hermite/Shift.lean |

**Missing from auto1** (identified in `conjectures/hermite.md`):
- Generating function: exp(tx - ct²/2) = Σ (t^n/n!) H_n(x;c) — listed as H01, status ⬜
- Orthogonality: E[H_n H_m] = n! c^n δ_{nm} — listed as H20–H22, status ⬜
- Mehler formula — not in scope

### aqft2: Hermite functions (axiomatized)

The `aqft2` project axiomatizes the analytic Hermite function infrastructure:

| Axiom | Content |
|-------|---------|
| `hermiteFunction_orthonormal` | ∫ φ_n φ_m = δ_{nm} |
| `hermiteFunction_complete` | Completeness in L² |
| `hermiteFunction_seminorm_bound` | Polynomial growth control |
| `schwartzHermiteBasis` | Schwartz space Schauder basis |
| `schwartz_hermite_coefficient_decay` | Coefficient decay rates |

These are the axioms already imported into gaussian-field via
`SchwartzNuclear/HermiteFunctions.lean`.

### aqft2: Heat kernel results (proved)

| Result | File |
|--------|------|
| `heatKernel_bilinear_fourier_form` | OS3_MixedRep.lean:207 |
| `bilinear_schwinger_eq_heatKernel` | OS3_MixedRep.lean:1269 |

These connect Schwinger parameter representations to heat kernels for
reflection positivity proofs. The heat kernel there is for the Laplacian
on ℝ⁴, not the harmonic oscillator.

### auto1: Bessel / Schwinger integrals (proved)

| Result | Content |
|--------|---------|
| `schwingerIntegral_eq_besselK0` | ∫₀^∞ e^{-m²t-r²/4t}/t dt = 2K₀(mr) |
| Bessel function library | 228 proved theorems (K₀, K₁, I, J) |

These handle Schwinger-parameter representations of Euclidean propagators,
potentially useful for the bridge theorem (Step 5) via Schwinger integrals.

## Roadmap: from existing work to Mehler kernel

The Mehler formula is the main missing piece. Here is a concrete development
path, building on the auto1 Hermite infrastructure.

### Phase A: Hermite generating function (auto1 or gaussian-field)

**Goal**: Prove the formal identity
```
exp(tx - ct²/2) = Σ_{n≥0} (t^n / n!) H_n(x; c)
```

**Approach**: This follows from the recurrence `probHermite_recurrence` by
comparing Taylor coefficients. Specifically:
1. Define `G(t,x) := exp(tx - ct²/2)` and `S(t,x) := Σ (t^n/n!) H_n(x;c)`
2. Both satisfy ∂G/∂t = (x - ct) G with G(0,x) = 1
3. The ODE + initial condition has a unique solution (Picard-Lindelöf on ℝ)

**Alternative**: Direct proof by induction using `probHermite_derivative` to
show the n-th Taylor coefficient of G at t=0 is H_n(x;c)/n!.

**Difficulty**: Medium. The algebraic content is straightforward; the analytic
content (convergence of the series, term-by-term differentiation) needs
Mathlib's `HasFPowerSeriesOnBall` or direct estimates.

**Prerequisites**: `probHermite_recurrence`, `probHermite_derivative` (both proved)

### Phase B: Hermite orthogonality (auto1 or gaussian-field)

**Goal**: Prove
```
∫ H_n(x; c) · H_m(x; c) · gaussian(x; c) dx = n! · c^n · δ_{nm}
```
where `gaussian(x; c) = (2πc)^{-1/2} exp(-x²/(2c))`.

**Approach 1** (via generating function): Multiply two generating functions:
```
∫ G(s,x) G(t,x) gaussian(x;c) dx = ∫ exp((s+t)x - c(s²+t²)/2) gaussian(x;c) dx
```
Complete the square to get `exp(cst)`. Comparing coefficients of s^n t^m
gives the orthogonality.

**Approach 2** (direct): Integration by parts using `probHermite_derivative`
and the fact that `gaussian'(x;c) = -(x/c) · gaussian(x;c)`.

**Difficulty**: Medium. Approach 1 requires Phase A. Approach 2 is independent
but needs careful handling of boundary terms (they vanish because Gaussian
decays faster than any polynomial).

**Mathlib support**: `integral_gaussian` from `Analysis.SpecialFunctions.Gaussian`
gives ∫ e^{-bx²} = √(π/b). Completing the square reduces to this.

### Phase C: Hermite function orthogonality (gaussian-field)

**Goal**: Prove (or derive from Phase B) that
```
∫ φ_n(x) φ_m(x) dx = δ_{nm}
```
where `φ_n(x) = c_n · H_n(x√2) · e^{-x²/2}` is our `hermiteFunction n x`.

This would replace the axiom `hermiteFunction_orthonormal` currently in the
project. The connection is:
```
φ_n(x) = (2^n n! √π)^{-1/2} · He_n(x) · e^{-x²/2}
```
where `He_n` is the physicist's Hermite polynomial. The orthogonality follows
from Phase B with the substitution `x → x√2` and `c = 1/2`.

**Difficulty**: Medium (given Phase B). Mostly bookkeeping with normalization
constants.

### Phase D: Mehler formula (gaussian-field)

**Goal**: Prove
```
Σ_k r^k φ_k(x) φ_k(y) = (π(1-r²))^{-1/2} exp(-(1+r²)(x²+y²)/(2(1-r²)) + 2rxy/(1-r²))
```
for |r| < 1.

**Approach** (via generating function): This is the classical proof.
1. Write φ_k(x) φ_k(y) using Hermite polynomials and Gaussian weights
2. Use the generating function from Phase A to sum the series
3. The sum becomes a Gaussian integral (or algebraic manipulation)

Specifically, from the generating function:
```
Σ_k (r^k/k!) H_k(x) H_k(y) = ... (use G(s,x)·G(t,y) with s=r, t=r after orthogonality)
```

Actually the standard proof multiplies two generating functions evaluated at
different points and uses the Gaussian integral:
```
Σ_{n,m} (s^n t^m)/(n! m!) ∫ H_n(x;c) H_m(x;c) gaussian(x;c) dx = exp(cst)
```
Then setting appropriate values and doing algebra gives Mehler.

**Alternative shortcut**: State and prove the bilinear generating function
```
Σ_k (r^k / k!) H_k(x) H_k(y) = (1-r²)^{-1/2} exp((2xyr - r²(x²+y²))/(1-r²))
```
directly by completing the square in the product G(r,x) · w(y) and integrating
over an auxiliary variable. This is the classical Mehler identity for polynomials;
the function version follows by including the Gaussian weights.

**Difficulty**: Hard. The algebraic manipulations are intricate (completing the
square in 2 variables). Convergence of the Hermite series needs estimates.

**Dependencies**: Phases A + B (or Phase C directly if working with functions)

### Phase E: Mehler → mehlerKernel (gaussian-field)

**Goal**: Setting r = e^{-2t} in Phase D gives
```
mehlerKernel t x y = Σ_k e^{-t(2k+1)} φ_k(x) φ_k(y)
                   = (2π sinh 2t)^{-1/2} exp(-(cosh(2t)(x²+y²) - 2xy)/(2 sinh 2t))
```

This is straightforward algebra: substitute r = e^{-2t}, use
`sinh 2t = (e^{2t} - e^{-2t})/2`, `cosh 2t = (e^{2t} + e^{-2t})/2`,
and simplify.

**Difficulty**: Easy (given Phase D). Just algebraic substitution.

### Summary of phases

```
Phase A: Generating function  ←── probHermite_recurrence, derivative (auto1, proved)
    ↓
Phase B: Orthogonality         ←── integral_gaussian (Mathlib, proved)
    ↓
Phase C: Function orthogonality ← hermiteFunction definition (gaussian-field)
    ↓
Phase D: Mehler formula         ← Phases A + B
    ↓
Phase E: mehlerKernel           ← Phase D + sinh/cosh algebra
```

**Estimated effort**: Phases A+B are ~500 lines each. Phase C is ~200 lines.
Phase D is ~800 lines (the hard part). Phase E is ~100 lines.

**Axiom-first strategy**: Start by axiomatizing Phase D (the Mehler formula)
and Phase C (function orthogonality), then build the position-space kernel
(Steps 2–5 from the implementation plan above). Fill in the proofs of
Phases A–D later. This lets us develop the kernel infrastructure in parallel
with the Hermite analysis.

## Alternative: Laplacian on ℝ instead of harmonic oscillator

If we used the **Laplacian** -d²/dx² instead of the harmonic oscillator
-d²/dx² + x², the heat kernel on ℝ would be the standard Gaussian
`(4πt)^{-1/2} exp(-(x-y)²/(4t))`, which is `gaussianPDFReal` from Mathlib.

However, this would require a different test function space (not Schwartz
with Hermite basis) since plane waves are not Schwartz functions. The Hermite
basis naturally pairs with the harmonic oscillator.

A possible compromise: work with the Laplacian and use Hermite functions
as a convenient basis, accepting that the eigenfunction expansion of the
standard heat kernel in the Hermite basis involves cross terms (the
Hermite functions are not eigenfunctions of -d²/dx²). This would be
more complex spectrally but simpler in position space.
