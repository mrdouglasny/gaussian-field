# Constructing Covariance Operators on Product Spaces

## The problem

The Gaussian measure library takes a CLM `T : E →L[ℝ] H` and produces a
measure. But how do you *build* $T$ for a specific physical model, especially
on a product space $M_1 \times M_2$?

The naive hope — that $T$ factors as $T_1 \otimes T_2$ — fails. The Laplacian
factors *additively*:

$$-\Delta_{M_1 \times M_2} = (-\Delta_{M_1}) \otimes I + I \otimes (-\Delta_{M_2})$$

but the covariance operator $T = (-\Delta + m^2)^{-1/2}$ is a nonlinear function
of this sum and does not factor as a tensor product.

## The heat kernel solution

The heat kernel $e^{-sA}$ (where $A = -\Delta + m^2$) is the right building
block because it **factors multiplicatively** over products:

$$e^{-s(A_1 \otimes I + I \otimes A_2)} = e^{-sA_1} \otimes e^{-sA_2}$$

This identity holds because $A_1 \otimes I$ and $I \otimes A_2$ commute, and
the exponential of a sum of commuting operators is the product of exponentials.

### Why the heat kernel is better than fractional powers

| Property | $e^{-sA}$ | $A^{-1/2}$ |
|---|---|---|
| Bounded | Yes, always | Only if $A$ is bounded |
| Factors over products | Yes, multiplicatively | No |
| Mathlib support | `Matrix.exp` + `exp_add_of_commute` | `CFC.rpow` (single operator only) |
| Extends to continuum | Yes, no unbounded operator theory | Requires spectral theory for unbounded ops |
| Physical meaning | Heat propagator at time $s$ | Green's function square root |

### Using $e^{-sA/2}$ as the covariance operator

Set $T_s = e^{-sA/2}$ for $s > 0$. The covariance is:

$$C_s(f,g) = \langle T_s f, T_s g \rangle_H = \langle f, e^{-sA} g \rangle$$

This is a valid covariance for each $s > 0$ — a "heat-regularized" Gaussian.
The library produces `measure T_s` with all properties (probability measure,
characteristic functional identity, moments, $L^p$ integrability).

### Recovering the GFF covariance

The standard GFF covariance $C(f,g) = \langle f, A^{-1} g \rangle$ is the
integral of heat-regularized covariances:

$$\langle f, A^{-1} g \rangle = \int_0^\infty \langle f, e^{-sA} g \rangle \, ds$$

More generally, fractional powers are recovered via the Mellin transform:

$$A^{-\alpha} = \frac{1}{\Gamma(\alpha)} \int_0^\infty s^{\alpha-1} e^{-sA}\, ds$$

For $\alpha = 1/2$: $T = A^{-1/2} = \frac{1}{\sqrt{\pi}} \int_0^\infty s^{-1/2} e^{-sA}\, ds$.

This can serve as a *definition* of $A^{-\alpha}$ that avoids spectral theory
for unbounded operators, building instead on the well-defined bounded operator
$e^{-sA}$.

### The mass term factors out

For the massive operator $A = -\Delta + m^2$:

$$e^{-s(-\Delta + m^2)} = e^{-m^2 s} \cdot e^{s\Delta}$$

since $-\Delta$ and $m^2 I$ commute. On a product space:

$$e^{-s(-\Delta_{M_1 \times M_2} + m^2)} = e^{-m^2 s} \cdot e^{s\Delta_{M_1}} \otimes e^{s\Delta_{M_2}}$$

## Mathlib support

### What exists

**Operator exponential:**
- `NormedSpace.exp` / `Matrix.exp` — power series definition in any Banach algebra
- `exp_add_of_commute : Commute A B → exp (A + B) = exp A * exp B`
- `Matrix.IsHermitian.exp` — exponential of Hermitian is Hermitian

**Continuous functional calculus (CFC):**
- `cfc f a` — applies continuous $f : \mathbb{R} \to \mathbb{R}$ to self-adjoint $a$ in a C\*-algebra
- `CFC.rpow a y` — fractional power $a^y$ for positive $a$
- `Matrix.IsHermitian.cfc` — specializes to matrices via spectral decomposition:
  $f(A) = U \cdot \text{diag}(f(\lambda_1), \ldots, f(\lambda_n)) \cdot U^*$

**Matrix spectral theorem:**
- `Matrix.IsHermitian.eigenvalues` — real eigenvalues
- `Matrix.IsHermitian.eigenvectorBasis` — orthonormal eigenbasis
- `Matrix.IsHermitian.spectral_theorem` — $A = U D U^*$ decomposition

**Kronecker product:**
- `Matrix.kroneckerMap` — generalized Kronecker product
- Index type: `Matrix (l × n) (m × p)`

**CFC algebra:**
- Composition: `cfc (g ∘ f) a = cfc g (cfc f a)`
- Commutativity: `IsSelfAdjoint.commute_cfc` — if $b$ commutes with $a$,
  then $b$ commutes with $f(a)$
- Powers: `nnrpow_add`, `nnrpow_nnrpow`

### What needs to be developed

**Kronecker product algebra.** The mixed-product identity:

$$(A \otimes B)(C \otimes D) = (AC) \otimes (BD)$$

Mathlib has `kroneckerMap` but the multiplication identity for the standard
Kronecker product may need to be proved or assembled from existing pieces.

**Commutativity of Kronecker factors.** The identity:

$$\text{Commute}(A_1 \otimes I,\, I \otimes A_2)$$

Follows from the mixed-product identity: $(A_1 \otimes I)(I \otimes A_2) =
A_1 \otimes A_2 = (I \otimes A_2)(A_1 \otimes I)$.

**Heat kernel factorization theorem.** Combining the above:

$$\text{exp}(-s(A_1 \otimes I + I \otimes A_2)) = \text{exp}(-sA_1) \otimes \text{exp}(-sA_2)$$

This is `exp_add_of_commute` applied to `(-s) • (A_1 ⊗ I)` and `(-s) • (I ⊗ A_2)`,
followed by the Kronecker mixed-product identity.

**CLM wrapper.** Packaging a matrix as a CLM `(Fin N → ℝ) →L[ℝ] (Fin N → ℝ)`
for use with the Gaussian measure API.

## Lean design

### Core definitions

```lean
namespace GaussianField

/-- Heat kernel on a finite lattice: e^{-s·A} for real symmetric A.
    This is a bounded operator for all s, even when interpreted as
    the lattice discretization of an unbounded generator. -/
def heatKernel {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (s : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  Matrix.exp ℝ ((-s) • A)

/-- Heat kernel is symmetric when A is. -/
theorem heatKernel_isHermitian {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (hA : A.IsHermitian) (s : ℝ) :
    (heatKernel A s).IsHermitian :=
  (hA.smul (-s)).exp

/-- Heat kernel at s=0 is the identity. -/
theorem heatKernel_zero {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    heatKernel A 0 = 1 := by
  simp [heatKernel, zero_smul, Matrix.exp_zero]

/-- Semigroup property: e^{-sA} · e^{-tA} = e^{-(s+t)A}. -/
theorem heatKernel_add {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (s t : ℝ) :
    heatKernel A s * heatKernel A t = heatKernel A (s + t) := by
  simp [heatKernel, ← exp_add_of_commute (Commute.smul_smul _ _ _)]
  ring_nf

end GaussianField
```

### Factorization over products

```lean
namespace GaussianField

open Matrix in
/-- Kronecker product: A ⊗_K B as a matrix on (Fin N₁ × Fin N₂). -/
def kron {N₁ N₂ : ℕ}
    (A : Matrix (Fin N₁) (Fin N₁) ℝ) (B : Matrix (Fin N₂) (Fin N₂) ℝ) :
    Matrix (Fin N₁ × Fin N₂) (Fin N₁ × Fin N₂) ℝ :=
  Matrix.kroneckerMap (· * ·) A B

/-- Mixed-product identity: (A ⊗ B)(C ⊗ D) = (AC) ⊗ (BD). -/
theorem kron_mul {N₁ N₂ : ℕ}
    (A C : Matrix (Fin N₁) (Fin N₁) ℝ) (B D : Matrix (Fin N₂) (Fin N₂) ℝ) :
    kron A B * kron C D = kron (A * C) (B * D) := by
  sorry  -- From kroneckerMap properties

/-- Kronecker factors commute: (A ⊗ I) and (I ⊗ B) commute. -/
theorem kron_commute {N₁ N₂ : ℕ}
    (A : Matrix (Fin N₁) (Fin N₁) ℝ) (B : Matrix (Fin N₂) (Fin N₂) ℝ) :
    Commute (kron A 1) (kron 1 B) := by
  -- (A ⊗ I)(I ⊗ B) = A ⊗ B = (I ⊗ B)(A ⊗ I)
  simp [Commute, SemiconjBy, kron_mul, mul_one, one_mul]

/-- **Heat kernel factorization on product lattices.**

    e^{-s(A₁ ⊗ I + I ⊗ A₂)} = e^{-sA₁} ⊗ e^{-sA₂}

    Proof: A₁ ⊗ I and I ⊗ A₂ commute, so exp of sum = product of exps.
    Then (e^{-sA₁} ⊗ I)(I ⊗ e^{-sA₂}) = e^{-sA₁} ⊗ e^{-sA₂} by
    the Kronecker mixed-product identity. -/
theorem heatKernel_product {N₁ N₂ : ℕ}
    (A₁ : Matrix (Fin N₁) (Fin N₁) ℝ)
    (A₂ : Matrix (Fin N₂) (Fin N₂) ℝ) (s : ℝ) :
    heatKernel (kron A₁ 1 + kron 1 A₂) s =
      kron (heatKernel A₁ s) (heatKernel A₂ s) := by
  -- Step 1: exp(-s(A₁⊗I + I⊗A₂)) = exp(-s(A₁⊗I)) · exp(-s(I⊗A₂))
  -- by exp_add_of_commute and kron_commute
  -- Step 2: exp(-s(A₁⊗I)) = exp(-sA₁) ⊗ I
  -- Step 3: exp(-s(I⊗A₂)) = I ⊗ exp(-sA₂)
  -- Step 4: (exp(-sA₁) ⊗ I)(I ⊗ exp(-sA₂)) = exp(-sA₁) ⊗ exp(-sA₂)
  sorry

/-- Mass factors out as a scalar. -/
theorem heatKernel_add_scalar {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (c s : ℝ) :
    heatKernel (A + c • 1) s = Real.exp (-c * s) • heatKernel A s := by
  -- A and c·I commute; exp(-s(A + cI)) = exp(-csI) · exp(-sA)
  -- exp(-csI) = e^{-cs} · I
  sorry

end GaussianField
```

### Building the covariance operator T

```lean
namespace GaussianField

/-- Package a matrix as a CLM on Fin N → ℝ. -/
def matrixToCLM {N : ℕ} (M : Matrix (Fin N) (Fin N) ℝ) :
    (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  M.toLin'.toContinuousLinearMap  -- finite-dim, automatically continuous

/-- The heat-regularized covariance operator: T_s = e^{-sA/2}.

    The Gaussian measure with this T has covariance:
      C_s(f,g) = ⟨T_s f, T_s g⟩ = ⟨f, e^{-sA} g⟩  -/
def heatCovarianceOp {N : ℕ}
    (A : Matrix (Fin N) (Fin N) ℝ) (s : ℝ) :
    (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) :=
  matrixToCLM (heatKernel A (s / 2))

/-- On a product lattice, the covariance operator factors.

    T_s(A₁ ⊗ I + I ⊗ A₂) = T_s(A₁) ⊗ T_s(A₂)

    This is the key compositional property: build covariance operators
    on factors, tensor them to get the product covariance operator. -/
theorem heatCovarianceOp_product {N₁ N₂ : ℕ}
    (A₁ : Matrix (Fin N₁) (Fin N₁) ℝ)
    (A₂ : Matrix (Fin N₂) (Fin N₂) ℝ) (s : ℝ) :
    heatCovarianceOp (kron A₁ 1 + kron 1 A₂) s =
      sorry -- kron (heatCovarianceOp A₁ s) (heatCovarianceOp A₂ s) as CLM
  := sorry

end GaussianField
```

### The discrete Laplacian

```lean
namespace GaussianField

/-- Discrete Laplacian on N sites with spacing a and Dirichlet BC.
    (Δ_a f)(k) = (f(k+1) - 2f(k) + f(k-1)) / a² -/
def discreteLaplacian (a : ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  sorry  -- tridiagonal matrix with -2/a² on diagonal, 1/a² off-diagonal

/-- Discrete periodic Laplacian on N sites with spacing a = L/N.
    (Δ f)(k) = (f(k+1 mod N) - 2f(k) + f(k-1 mod N)) / a²

    This is the lattice approximation to d²/dx² on S¹_L. -/
def discretePeriodicLaplacian (L : ℝ) (N : ℕ) :
    Matrix (Fin N) (Fin N) ℝ :=
  sorry  -- circulant matrix

/-- The discrete periodic Laplacian is symmetric. -/
theorem discretePeriodicLaplacian_isHermitian (L : ℝ) (N : ℕ) :
    (discretePeriodicLaplacian L N).IsHermitian :=
  sorry

/-- The discrete periodic Laplacian is positive semidefinite. -/
theorem discretePeriodicLaplacian_posSemidef (L : ℝ) (N : ℕ) :
    (discretePeriodicLaplacian L N).PosSemidef :=
  sorry

/-- Eigenvalues of the periodic discrete Laplacian.
    λ_k = (2N/L)² · sin²(πk/N) for k = 0, …, N-1. -/
theorem discretePeriodicLaplacian_eigenvalues (L : ℝ) (N : ℕ) (k : Fin N) :
    sorry -- eigenvalue k equals 4 * (N/L)^2 * sin(π * k / N)^2
  := sorry

end GaussianField
```

## Putting it all together

### Example: lattice GFF on a periodic square lattice

```lean
variable (L₁ L₂ : ℝ) [Fact (0 < L₁)] [Fact (0 < L₂)]
variable (N₁ N₂ : ℕ) [NeZero N₁] [NeZero N₂]
variable (mass : ℝ) (hmass : 0 < mass)
variable (s : ℝ) (hs : 0 < s)

-- Factor Laplacians
def Δ₁ := discretePeriodicLaplacian L₁ N₁  -- on Fin N₁
def Δ₂ := discretePeriodicLaplacian L₂ N₂  -- on Fin N₂

-- Product operator: -Δ₁ ⊗ I + I ⊗ (-Δ₂) + m²
def A_product :=
  kron (Δ₁ L₁ N₁) (1 : Matrix (Fin N₂) (Fin N₂) ℝ) +
  kron (1 : Matrix (Fin N₁) (Fin N₁) ℝ) (Δ₂ L₂ N₂) +
  mass ^ 2 • (1 : Matrix (Fin N₁ × Fin N₂) (Fin N₁ × Fin N₂) ℝ)

-- Covariance operator: T = e^{-sA/2}
def T_product := heatCovarianceOp (A_product L₁ L₂ N₁ N₂ mass) s

-- The Gaussian measure on the product lattice
-- (needs DyninMityaginSpace instance for Fin N₁ × Fin N₂ → ℝ)
#check GaussianField.measure (T_product L₁ L₂ N₁ N₂ mass s)
```

### The factorization in action

The heat kernel factorization theorem lets us compute the product operator
from the factor operators:

```lean
-- By heatKernel_product and heatKernel_add_scalar:
-- T_product ≃ e^{-m²s/2} · (T₁ ⊗ T₂)
-- where T₁ = e^{-s·Δ₁/2} and T₂ = e^{-s·Δ₂/2}

-- The covariance on the product is:
-- C_s(f₁⊗f₂, g₁⊗g₂) = e^{-m²s} · ⟨f₁, e^{-sΔ₁} g₁⟩ · ⟨f₂, e^{-sΔ₂} g₂⟩

-- On pure tensors, this factors as a product of 1D covariances.
-- On general functions, it doesn't — but the operator still factors.
```

## Relationship to other approaches

### CFC.rpow (alternative for single operators)

For a single lattice (not a product), Mathlib's `CFC.rpow` gives $A^{-1/2}$
directly via the continuous functional calculus:

```lean
-- For a single positive definite Hermitian matrix A:
def gffOperator {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.PosDef) : Matrix (Fin N) (Fin N) ℝ :=
  cfc (fun x : ℝ => x ^ (-1/2 : ℝ)) A
```

This is simpler when you don't need to compose over products. But it doesn't
factor: `cfc f (A₁ ⊗ I + I ⊗ A₂) ≠ kron (cfc f A₁) (cfc f A₂)` in general.

### Integral representation (connecting the two)

The heat kernel and CFC approaches are connected by:

$$A^{-\alpha} = \frac{1}{\Gamma(\alpha)} \int_0^\infty s^{\alpha-1} e^{-sA}\, ds$$

For the lattice case (finite-dim), both sides are well-defined and equal.
This identity could be proved using the spectral decomposition: both sides
act on eigenspace $\lambda_k$ by $\lambda_k^{-\alpha}$.

For the continuum case, the left side requires unbounded operator spectral
theory, while the right side only uses the bounded operator $e^{-sA}$. The
integral representation is therefore the more general definition.

## Continuum extension

The heat kernel approach extends directly to continuum spaces:

**On $C^\infty(S^1_L)$:** The heat kernel $e^{s\Delta}$ acts on Fourier
modes by $e^{-s(2\pi n/L)^2}$. This is a bounded operator on $L^2(S^1_L)$
and a CLM from $C^\infty(S^1_L)$ to $L^2(S^1_L)$ (or to itself). No
unbounded operator theory needed.

**On $\mathcal{S}(\mathbb{R}^d)$:** The heat kernel acts on Hermite functions
by $e^{-s\lambda_n}$ where $\lambda_n$ are Hermite eigenvalues. Again bounded.

**On products:** The factorization theorem holds in the same form:
$e^{-s(A_1 \otimes I + I \otimes A_2)} = e^{-sA_1} \otimes e^{-sA_2}$.
The proof uses the same ingredients (commutativity of Kronecker factors,
exponential of commuting sum).

The heat kernel is the natural building block for covariance operators
across all scales — from finite lattices to continuum spaces — and
its tensor product factorization is the compositional principle that
makes product space constructions tractable.
