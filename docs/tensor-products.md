# Tensor Products of Nuclear Spaces

## Overview

`NuclearTensorProduct E₁ E₂` is the completed nuclear tensor product of two
`DyninMityaginSpace` spaces. It carries its own `DyninMityaginSpace` instance
and satisfies the universal property of tensor products. The construction is
concrete: `NuclearTensorProduct` is defined as `RapidDecaySeq` (the Köthe
sequence space $s(\mathbb{N})$), with Cantor pairing encoding two basis indices
into one.

The high-level API — associativity, Schwartz isomorphisms, and the universal
property — is described in the [README](../README.md). This document covers the
concrete construction and internal machinery.

**Status: Complete (1 sorry in `schwartzPointwiseProduct_apply`).**

## Mathematical picture

### Nuclear tensor products via sequence spaces

For nuclear Fréchet spaces with Schauder bases, the Dynin-Mityagin theorem
gives topological isomorphisms $E_1 \cong s(\mathbb{N})$ and
$E_2 \cong s(\mathbb{N})$. The completed projective tensor product is then:

$$E_1 \hat{\otimes} E_2 \cong s(\mathbb{N}) \hat{\otimes} s(\mathbb{N}) \cong s(\mathbb{N}^2) \cong s(\mathbb{N})$$

where the last step uses the Cantor pairing bijection
$\mathbb{N}^2 \to \mathbb{N}$. This justifies defining `NuclearTensorProduct`
concretely as `RapidDecaySeq`.

### The kernel theorem

For nuclear Fréchet spaces of smooth functions, the tensor product isomorphism
is the Schwartz kernel theorem:

$$C^\infty(M_1 \times M_2) \cong C^\infty(M_1) \hat{\otimes} C^\infty(M_2)$$

In our formalization, this is realized for Schwartz spaces by `schwartzTensorEquiv`:

$$\mathcal{S}(\mathbb{R}^{m+1}) \hat{\otimes} \mathcal{S}(\mathbb{R}^{n+1}) \cong \mathcal{S}(\mathbb{R}^{m+n+2})$$

### Tensor product basis and seminorms

If $E_1$ has basis $\{\psi_i\}$ and $E_2$ has basis $\{\varphi_j\}$, then
$E_1 \hat{\otimes} E_2$ has basis $\{\psi_i \otimes \varphi_j\}_{(i,j) \in \mathbb{N}^2}$,
indexed by $\mathbb{N}$ via the Cantor pairing.

Seminorms are indexed by $\iota_1 \times \iota_2$:
$$r_{(\alpha,\beta)}(\psi_i \otimes \varphi_j) = p_\alpha(\psi_i) \cdot q_\beta(\varphi_j)$$

**Growth** remains polynomial: if $p_\alpha(\psi_i) \le C_1 (1+i)^{s_1}$ and
$q_\beta(\varphi_j) \le C_2 (1+j)^{s_2}$, then under Cantor pairing $\sigma(m) = (i,j)$
we have $i, j \le m$, giving $r_{(\alpha,\beta)} \le C_1 C_2 (1+m)^{s_1 + s_2}$.

**Decay** remains super-polynomial: the product of coefficient sequences decays
faster than any polynomial.

## File structure

| File | Lines | Contents |
|------|------:|----------|
| [`Nuclear/NuclearTensorProduct.lean`](../Nuclear/NuclearTensorProduct.lean) | 1,125 | `RapidDecaySeq`, `NuclearTensorProduct`, `pure`, `lift`, `lift_pure` |
| [`SchwartzNuclear/SchwartzTensorProduct.lean`](../SchwartzNuclear/SchwartzTensorProduct.lean) | 363 | `reindex`, `assoc`, `schwartzPeelOff`, `schwartzTensorEquiv` |

## Concrete construction: `RapidDecaySeq` and `NuclearTensorProduct`

### `RapidDecaySeq` (in `Nuclear/NuclearTensorProduct.lean`)

The Köthe sequence space $s(\mathbb{N})$: real sequences $(a_m)$ with
$\sum_m |a_m| (1+m)^k < \infty$ for every $k$. Equipped with:

- **Seminorms**: `rapidDecaySeminorm k : a ↦ ∑_m |a_m| (1+m)^k`
- **Topology**: locally convex, via `WithSeminorms`
- **Standard basis**: `basisVec m` and `coeffCLM m` (coordinate projection)
- **`DyninMityaginSpace` instance**: `rapidDecay_dyninMityaginSpace`

The key convergence result is `hasSum_basisVec`: partial sums
$\sum_{m \in s} a_m e_m$ converge to $a$ in the seminorm topology.

### `NuclearTensorProduct` (in `Nuclear/NuclearTensorProduct.lean`)

```lean
def NuclearTensorProduct (_E₁ _E₂ : Type*) := RapidDecaySeq
```

The type parameters are phantom — every tensor product is concretely `RapidDecaySeq`.
The `DyninMityaginSpace` instance is inherited.

### Pure tensor embedding

`pure e₁ e₂` embeds $E_1 \times E_2$ into $E_1 \hat{\otimes} E_2$ by:
$$(\text{pure}\ e_1\ e_2)_m = c_{\pi_1(m)}(e_1) \cdot c_{\pi_2(m)}(e_2)$$
where $\pi_1, \pi_2$ are the Cantor unpairing projections.

| Definition / Theorem | Description |
|---|---|
| `pure e₁ e₂` | Pure tensor: product of coefficients via Cantor pairing |
| `pure_val` | `(pure e₁ e₂).val m = coeff (unpair m).1 e₁ * coeff (unpair m).2 e₂` |
| `pure_seminorm_bound k` | Bilinear seminorm estimate for rapid decay |
| `pureLin` | `E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] NuclearTensorProduct E₁ E₂` |
| `pureCLM_right e₁` | Continuous in second argument for fixed first |
| `pure_continuous` | Joint continuity via `continuous_of_continuousAt_zero₂` |

The seminorm bound is the key estimate: it bounds $(1+\text{pair}(i,j))^k$
by $4^k(1+i)^{2k}(1+j)^{2k}$ (via `one_add_pair_le_sq`), then factors
into individual coefficient decay at exponent $2k+2$.

### Universal property: `lift` and `lift_pure`

Every seminorm-bounded bilinear map $B : E_1 \times E_2 \to G$ (into a complete
normed space $G$) factors through `pure` via a continuous linear map:

| Definition / Theorem | Description |
|---|---|
| `lift B` | `NuclearTensorProduct E₁ E₂ →L[ℝ] G` — the factoring CLM |
| `lift_pure` | `lift B (pure e₁ e₂) = B e₁ e₂` — the universal property identity |
| `lift_summable` | The defining series converges absolutely |

The proof of `lift_pure` uses the double Schauder expansion (`hasSum_basis`)
mapped through $B$ and recombined via Cantor pairing. Specifically, `lift` is
defined as:
$$\text{lift}\ B\ a = \sum_m a_m \cdot B(\psi_{\pi_1(m)}, \varphi_{\pi_2(m)})$$

## Reindexing and associativity (in `SchwartzNuclear/SchwartzTensorProduct.lean`)

### `RapidDecaySeq.reindex`

A general reindexing automorphism for `RapidDecaySeq`: given a permutation
$\sigma : \mathbb{N} \equiv \mathbb{N}$ with both $\sigma$ and $\sigma^{-1}$
polynomially bounded, produces a CLE:

```lean
def reindex (σ : ℕ ≃ ℕ)
    (hσ : IsPolyBounded σ) (hσ_inv : IsPolyBounded σ.symm) :
    RapidDecaySeq ≃L[ℝ] RapidDecaySeq
```

The forward map is $a \mapsto a \circ \sigma$, and rapid decay is preserved
by the change of variables $n = \sigma(m)$ with the polynomial bound on
$\sigma^{-1}$ controlling the weight shift.

### `NuclearTensorProduct.assoc`

Associativity $(E_1 \hat{\otimes} E_2) \hat{\otimes} E_3 \cong E_1 \hat{\otimes} (E_2 \hat{\otimes} E_3)$
is realized as `reindex assocPerm`, where `assocPerm` is the Cantor pairing
reassociation permutation:
$$\text{pair}(\text{pair}(i,j), k) \mapsto \text{pair}(i, \text{pair}(j,k))$$

The polynomial bounds use the Cantor pairing growth estimate
$1 + \text{pair}(i,j) \le (2(1+i)(1+j))^2$ iterated twice, giving
degree-10 bounds with constant 64.

## Schwartz tensor product isomorphisms

### `schwartzPeelOff` — dimension peeling

```lean
def schwartzPeelOff (d : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ ≃L[ℝ]
    NuclearTensorProduct
      (SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ)
      (SchwartzMap ℝ ℝ)
```

This is literally `schwartzRapidDecayEquivNd (d + 1)` — the existing isomorphism
$\mathcal{S}(\mathbb{R}^{d+2}) \cong s(\mathbb{N})$, reinterpreted as landing
in `NuclearTensorProduct` (which is definitionally `RapidDecaySeq`).

The key insight: `multiIndexEquiv (d+1)` peels off the last coordinate via
`Fin.succFunEquiv` then Cantor-pairs, which matches exactly how
`NuclearTensorProduct` pairs two sequence spaces.

### `schwartzPeelOff_pure` — canonicity

The inverse of `schwartzPeelOff` sends a pure tensor $f \otimes g$ to the
pointwise product function $(x, t) \mapsto f(x) \cdot g(t)$:

```lean
theorem schwartzPeelOff_pure (d : ℕ) (f g) :
    (schwartzPeelOff d).symm (pure f g) = schwartzPointwiseProduct d f g
```

This is `rfl` by definition: `schwartzPointwiseProduct` is defined as the
inverse image of `pure f g` under `schwartzPeelOff`.

### `schwartzTensorEquiv` — general isomorphism

```lean
def schwartzTensorEquiv (m n : ℕ) :
    NuclearTensorProduct
      (SchwartzMap (EuclideanSpace ℝ (Fin (m + 1))) ℝ)
      (SchwartzMap (EuclideanSpace ℝ (Fin (n + 1))) ℝ) ≃L[ℝ]
    SchwartzMap (EuclideanSpace ℝ (Fin (m + n + 2))) ℝ
```

Since `NuclearTensorProduct` is always `RapidDecaySeq`, this is simply
`(schwartzRapidDecayEquivNd (m + n + 1)).symm` after Fin arithmetic.

## Composability

Once `DyninMityaginSpace` instances exist for factor spaces, tensor products
compose freely:

| Target space | Construction |
|---|---|
| $T^2 = S^1 \times S^1$ | `NuclearTensorProduct C∞(S¹) C∞(S¹)` |
| Cylinder $S^1 \times \mathbb{R}$ | `NuclearTensorProduct C∞(S¹) S(ℝ)` |
| $\mathbb{R}^n$ | $n$-fold tensor of $\mathcal{S}(\mathbb{R})$ |
| $T^d$ | $d$-fold tensor of $C^\infty(S^1)$ |
| Cylinder $T^d \times \mathbb{R}^k$ | Tensor of torus and Euclidean factors |

Each gets a Gaussian measure for any CLM $T$ into a Hilbert space —
automatically, from the `DyninMityaginSpace` instance.

## Relation to Mathlib's `TensorProduct`

The current construction is concrete (Path B): `NuclearTensorProduct` is
`RapidDecaySeq` with the universal property proved directly. A future
direction (Path A) would build completed projective tensor products on
Mathlib's algebraic `TensorProduct R M N` and prove the isomorphism with
`RapidDecaySeq` for DM spaces. See
[abstract-tensor-product-plan.md](abstract-tensor-product-plan.md) for details.

## Relation to the lattice-continuum limit

For the lattice-continuum limit on product spaces, the tensor product
structure gives a natural factorization of the restriction maps:

$$r_n = r_n^{(1)} \otimes r_n^{(2)} : E_1 \hat{\otimes} E_2 \to E_{1,n} \otimes E_{2,n}$$

The quadratic form convergence condition then factors as well, potentially
simplifying the analysis.
