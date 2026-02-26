# Lattice Module — Public API

This module provides Gaussian field theory on lattices, both finite (periodic
torus) and infinite (ℤ^d with rapid decay). All definitions live in the
`GaussianField` namespace.

## File Structure

```
Lattice/
  Sites.lean              -- Lattice site types and geometry
  RapidDecayLattice.lean  -- Infinite lattice: rapidly decaying functions on ℤ^d
  FiniteField.lean        -- Finite lattice: functions on (Fin N)^d
  Laplacian.lean          -- Discrete Laplacian with spacing parameter a
  Covariance.lean         -- Green's function as spectralCLM
  FKG.lean                -- FKG inequality for log-concave lattice measures
Lattice.lean              -- Root import file
```

Import dependency graph:
```
Sites ← RapidDecayLattice   (uses latticeNorm, InfLatticeSites)
Sites ← FiniteField          (uses FinLatticeSites)
Sites ← Laplacian            (uses neighbors, both site types)
FiniteField + Laplacian ← Covariance  (eigenvalues, spectralCLM)
Covariance ← FKG             (lattice Gaussian measure)
```

## 1. Lattice Sites (`Lattice/Sites.lean`)

| Definition | Type | Meaning |
|---|---|---|
| `FinLatticeSites d N` | `Type` | `Fin d → Fin N` — sites of (ℤ/Nℤ)^d |
| `InfLatticeSites d` | `Type` | `Fin d → ℤ` — sites of ℤ^d |
| `latticeNorm x` | `ℝ` | ℓ¹ norm: `∑ i, \|x i\|` |
| `neighbors d x` | `Finset (Fin d → ℤ)` | 2d nearest neighbors of x on ℤ^d |
| `neighborsFinite d N x` | `Finset (Fin d → Fin N)` | neighbors with periodic BC |

The lattice spacing `a : ℝ` is a parameter in the Laplacian/covariance,
not in the site type. Physical position of site x is `a • x`.

## 2. Infinite Lattice Test Space (`Lattice/RapidDecayLattice.lean`)

| Definition | Type | Meaning |
|---|---|---|
| `RapidDecayLattice d` | `Type` | Rapidly decaying functions on ℤ^d |
| `.val` | `(Fin d → ℤ) → ℝ` | Underlying function |
| `.rapid_decay` | `∀ k, Summable (...)` | `∑_x \|f(x)\| (1+\|x\|)^k < ∞` for all k |

**Instances:**
- `AddCommGroup`, `Module ℝ`, `TopologicalSpace`, `IsTopologicalAddGroup`, `ContinuousSMul ℝ`
- `DyninMityaginSpace (RapidDecayLattice d)` — via CLE to `RapidDecaySeq`
- `HasPointEval (RapidDecayLattice d) (Fin d → ℤ)`

| Definition | Type | Meaning |
|---|---|---|
| `latticeRapidDecaySeminorm d k` | `Seminorm ℝ (RapidDecayLattice d)` | `∑_x \|f(x)\| (1+\|x\|)^k` |
| `latticeEnum d` | `(Fin d → ℤ) ≃ ℕ` | Shell enumeration of ℤ^d |
| `latticeRapidDecayEquiv d` | `RapidDecayLattice d ≃L[ℝ] RapidDecaySeq` | CLE via enumeration |

**Key difficulty:** The CLE proof needs `latticeNorm (latticeEnum.symm m) ≤ C · m^{1/d}`,
which follows from the shell enumeration: the m-th point in ℤ^d (ordered by ℓ¹ norm)
has norm ~m^{1/d}.

## 3. Finite Lattice Field Space (`Lattice/FiniteField.lean`)

| Definition | Type | Meaning |
|---|---|---|
| `FinLatticeField d N` | `Type` | `FinLatticeSites d N → ℝ` |

**Instances:**
- `DyninMityaginSpace (FinLatticeField d N)` — finite-dimensional (delta basis)
- `HasPointEval (FinLatticeField d N) (FinLatticeSites d N)`

The finite-dim case: `basis_growth` and `coeff_decay` hold with any polynomial
because there are only finitely many basis vectors.

## 4. Discrete Laplacian (`Lattice/Laplacian.lean`)

All operators parametrized by lattice spacing `a : ℝ`.

| Definition | Type | Meaning |
|---|---|---|
| `finiteLaplacian d N a` | `FinLatticeField d N →L[ℝ] FinLatticeField d N` | `(Δ_a f)(x) = a⁻² Σ_i [f(x+eᵢ)+f(x-eᵢ)-2f(x)]` |
| `infiniteLaplacian d a` | `RapidDecayLattice d →L[ℝ] RapidDecayLattice d` | Same on ℤ^d |
| `massOperator d N a m` | `FinLatticeField d N →L[ℝ] FinLatticeField d N` | `-Δ_a + m²` |

**Properties:**
- `finiteLaplacian_selfAdjoint` — symmetric
- `finiteLaplacian_neg_semidefinite` — ⟨f, Δf⟩ ≤ 0
- `massOperator_pos_def` — positive definite when m > 0

**Eigenvalues (finite, periodic BC):**

| Definition | Type | Meaning |
|---|---|---|
| `latticeEigenvalue d N a mass m` | `ℝ` | `(4/a²) Σᵢ sin²(πkᵢ/N) + mass²` |
| `latticeEigenvalue_pos` | `0 < latticeEigenvalue ...` | when mass > 0 |

## 5. Covariance and Gaussian Measure (`Lattice/Covariance.lean`)

| Definition | Type | Meaning |
|---|---|---|
| `latticeSingularValue d N a mass m` | `ℝ` | `latticeEigenvalue(...)^{-1/2}` |
| `lattice_singular_values_bounded` | `IsBoundedSeq (latticeSingularValue ...)` | enables spectralCLM |
| `latticeCovariance d N a mass` | `FinLatticeField d N →L[ℝ] ell2'` | `spectralCLM` with lattice singular values |
| `latticeGaussianMeasure d N a mass` | `Measure (Configuration (FinLatticeField d N))` | `GaussianField.measure (latticeCovariance ...)` |

**Derived (automatic from GaussianField API):**
- `charFun (latticeCovariance ...) f` — characteristic functional
- `cross_moment_eq_covariance (latticeCovariance ...) f g` — `E[φ(f)φ(g)] = ⟨Tf, Tg⟩ = G_a(f,g)`
- `wick_recursive`, `wick_bound` — Wick's theorem on the lattice

For infinite lattice: same pattern with `RapidDecayLattice d` replacing `FinLatticeField d N`.

## 6. FKG Inequality (`Lattice/FKG.lean`)

| Definition | Type | Meaning |
|---|---|---|
| `fkg_lattice_gaussian` | axiom | `E[F·G] ≥ E[F]·E[G]` for monotone F, G under lattice Gaussian |
| `fkg_perturbed` | axiom | Same for `(1/Z) exp(-V) dμ₀` when V is convex |

The monotonicity uses `Pi.instLE` on `FinLatticeField d N` (pointwise ≤).

**Development path toward proof:**
1. Prove the FKG lattice condition for product measures (generalize Harris-Kleitman)
2. Verify the lattice condition for Gaussian measures (log-concave density)
3. Verify preservation under convex perturbation

## Usage Example (downstream in pphi2)

```lean
import Lattice

-- Set up a 2D lattice with spacing a, mass m, on N×N torus
variable (N : ℕ) (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)

-- The Gaussian measure is automatic:
#check latticeGaussianMeasure 2 N a mass ha hmass
  -- : Measure (Configuration (FinLatticeField 2 N))

-- Two-point function:
example (x y : FinLatticeSites 2 N) :
    ∫ ω, ω (deltaFun x) * ω (deltaFun y)
      ∂(latticeGaussianMeasure 2 N a mass ha hmass) =
    GaussianField.covariance (latticeCovariance 2 N a mass ha hmass)
      (deltaFun x) (deltaFun y) :=
  GaussianField.cross_moment_eq_covariance _ _ _

-- Wick's theorem applies:
#check GaussianField.wick_recursive (latticeCovariance 2 N a mass ha hmass)

-- FKG for the interacting measure:
-- Define V(φ) = a² Σ_x P(φ(x)) where P is even and bounded below
-- Then fkg_perturbed gives E_μ[F·G] ≥ E_μ[F]·E_μ[G]
```
