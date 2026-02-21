# Tensor Products and Product Spaces

## Goal

Given `DyninMityaginSpace` instances for $E_1$ and $E_2$ (e.g., $C^\infty(S^1)$
and $\mathcal{S}(\mathbb{R})$), construct a `DyninMityaginSpace` instance for
the product space $E_1 \hat{\otimes} E_2 \cong C^\infty(S^1 \times \mathbb{R})$.

This lets us build Gaussian measures on distributions on product manifolds
(cylinders, tori, etc.) from measures on the factors.

## Mathematical picture

### The isomorphism

For nuclear Fréchet spaces, the completed projective tensor product
satisfies a kernel theorem:

$$C^\infty(M_1 \times M_2) \cong C^\infty(M_1) \hat{\otimes} C^\infty(M_2)$$

The dual side gives the corresponding statement for distributions:

$$\mathcal{D}'(M_1 \times M_2) \cong \mathcal{D}'(M_1) \hat{\otimes} \mathcal{D}'(M_2)$$

### Tensor product basis

If $E_1$ has basis $\{\psi_i\}$ and $E_2$ has basis $\{\varphi_j\}$, then
$E_1 \hat{\otimes} E_2$ has basis $\{\psi_i \otimes \varphi_j\}_{(i,j) \in \mathbb{N}^2}$.

Use a bijection $\sigma : \mathbb{N} \to \mathbb{N} \times \mathbb{N}$ (e.g., Cantor
pairing) to index by $\mathbb{N}$ as required by the typeclass.

### Seminorms

If $E_1$ has seminorms $\{p_\alpha\}_{\alpha \in \iota_1}$ and $E_2$ has
$\{q_\beta\}_{\beta \in \iota_2}$, the tensor product seminorms are
indexed by $\iota_1 \times \iota_2$:

$$r_{(\alpha,\beta)}(\psi_i \otimes \varphi_j) = p_\alpha(\psi_i) \cdot q_\beta(\varphi_j)$$

### Growth and decay

**Growth** (polynomial): If $p_\alpha(\psi_i) \le C_1 (1+i)^{s_1}$ and
$q_\beta(\varphi_j) \le C_2 (1+j)^{s_2}$, then under the Cantor pairing
$\sigma(m) = (i,j)$ we have $i, j \le m$, so:

$$r_{(\alpha,\beta)}(\psi_i \otimes \varphi_j) \le C_1 C_2 (1+m)^{s_1 + s_2}$$

Still polynomial growth.

**Decay** (super-polynomial): If $|c^1_i(f_1)| (1+i)^k \le C_1 p_{\alpha}(f_1)$
and $|c^2_j(f_2)| (1+j)^k \le C_2 q_{\beta}(f_2)$, the tensor product
coefficients satisfy the product decay bound, which is still
super-polynomial.

## Example: cylinder $S^1 \times \mathbb{R}$

### Components

- $E_1 = C^\infty(S^1)$ with Fourier basis $\{e^{inx}\}_{n \in \mathbb{Z}}$
  and Sobolev seminorms $\|f\|_k$
- $E_2 = \mathcal{S}(\mathbb{R})$ with Hermite basis $\{h_m(y)\}_{m \in \mathbb{N}}$
  and Schwartz seminorms $p_{k,l}$

### Tensor product

- Test functions: $C^\infty(S^1 \times \mathbb{R})$ with appropriate decay in $y$
- Basis: $\{e^{inx} h_m(y)\}_{(n,m)}$ — Fourier in $x$, Hermite in $y$
- Seminorm index: $(\mathbb{N}) \times (\mathbb{N} \times \mathbb{N})$
- Product seminorms: $r_{(k, (k', l'))}(f) = \|f\|_{k, k', l'}$

### Covariance operator

For a massive free field on the cylinder:

$$T = (-\partial_x^2 - \partial_y^2 + m^2)^{-1/2}$$

On the tensor product basis:

$$\|T(e^{inx} h_m(y))\|^2 = \frac{1}{n^2 + \lambda_m + m^2}$$

where $\lambda_m$ are the Hermite eigenvalues. The measure `measure T`
is a Gaussian on distributions on the cylinder.

## Lean approach

### Option A: Köthe sequence space (avoids abstract tensor products)

Instead of formalizing the completed projective tensor product $\hat{\otimes}$
in full generality, define the product space directly at the sequence level.

```lean
/-- The nuclear tensor product, defined as a Köthe sequence space
    on ℕ × ℕ with product weights. -/
def NuclearTensorProduct (E₁ E₂ : Type*)
    [AddCommGroup E₁] [Module ℝ E₁] ... [DyninMityaginSpace E₁]
    [AddCommGroup E₂] [Module ℝ E₂] ... [DyninMityaginSpace E₂] :=
  -- Concretely: sequences a : ℕ × ℕ → ℝ such that
  -- ∀ (α, β), ∑_{i,j} |a_{i,j}|² · p_α(ψ_i)² · q_β(φ_j)² < ∞
  sorry

instance : DyninMityaginSpace (NuclearTensorProduct E₁ E₂) where
  ι := DyninMityaginSpace.ι (E := E₁) × DyninMityaginSpace.ι (E := E₂)
  p := fun (α, β) => ...  -- product seminorm
  basis := fun m =>
    let (i, j) := Nat.pair_inv m  -- Cantor unpairing
    basis_E₁ i ⊗ basis_E₂ j
  coeff := fun m =>
    let (i, j) := Nat.pair_inv m
    coeff_E₁ i ⊗ coeff_E₂ j      -- product coefficient
  expansion := ...   -- from factor expansions
  basis_growth := ... -- product of factor growth bounds
  coeff_decay := ...  -- product of factor decay bounds
```

The key advantage: everything stays in the Dynin-Mityagin / Schauder basis
framework. No need for Grothendieck's abstract tensor product theory.

### Option B: Direct instance for specific product spaces

For a specific case like $C^\infty(S^1 \times \mathbb{R})$, provide the
`DyninMityaginSpace` instance directly using the product basis, without going
through abstract tensor products:

```lean
instance : DyninMityaginSpace (SmoothCylinder) where
  ι := ℕ × (ℕ × ℕ)   -- Sobolev index × Schwartz index
  basis := fun m =>
    let (n, k) := Nat.pair_inv m
    fourierMode n * hermiteFunction k   -- e^{inx} · h_k(y)
  ...
```

This is less general but avoids any tensor product formalization overhead.

## Composability

Once tensor products work, spaces compose freely:

| Target space | Construction |
|---|---|
| $T^2 = S^1 \times S^1$ | `NuclearTensorProduct C∞(S¹) C∞(S¹)` |
| Cylinder $S^1 \times \mathbb{R}$ | `NuclearTensorProduct C∞(S¹) S(ℝ)` |
| $\mathbb{R}^n$ | $n$-fold tensor of $\mathcal{S}(\mathbb{R})$ |
| $T^d$ | $d$-fold tensor of $C^\infty(S^1)$ |
| Cylinder $T^d \times \mathbb{R}^k$ | Tensor of torus and Euclidean factors |

Each gets a Gaussian measure for any CLM $T$ into a Hilbert space —
automatically, from the `DyninMityaginSpace` instance.

## Relation to the lattice limit

For the lattice-continuum limit on product spaces, the tensor product
structure gives a natural factorization of the restriction maps:

$$r_n = r_n^{(1)} \otimes r_n^{(2)} : E_1 \hat{\otimes} E_2 \to E_{1,n} \otimes E_{2,n}$$

The quadratic form convergence condition then factors as well, potentially
simplifying the analysis.
