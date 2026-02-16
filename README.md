# gaussian-measure

A Lean 4 / Mathlib library for constructing **centered Gaussian probability measures on duals of Schwartz spaces**.

Given a continuous linear map (CLM) $T : \mathcal{S}(D, F) \to H$ from a Schwartz space to a separable real Hilbert space $H$ (finite- or infinite-dimensional), the library constructs a probability measure $\mu$ on the weak dual $\mathcal{S}'(D, F) = \text{WeakDual}\ \mathbb{R}\ (\text{SchwartzMap}\ D\ F)$ satisfying the characteristic functional identity:

$$\mathbb{E}\left[e^{i\langle\omega, f\rangle}\right] = e^{-\frac{1}{2}\|T(f)\|_H^2} \qquad \forall f \in \mathcal{S}(D, F)$$

The covariance is $C(f,g) = \langle T(f), T(g) \rangle_H$.

## Motivation

This construction is the standard path to Gaussian measures in quantum field theory, stochastic PDEs, and infinite-dimensional probability. The library is **application-agnostic** — it works for any CLM into any separable Hilbert space, not just specific physical models.

### Example: Gaussian Free Field

For the free scalar field in $d$ dimensions, take:
- $D = \mathbb{R}^d$, $F = \mathbb{R}$
- $H = L^2(\mathbb{R}^d)$
- $T = (-\Delta + m^2)^{-1/2}$ (inverse half-Laplacian on Schwartz space)

The resulting measure is the Gaussian free field with mass $m$, and the covariance is:
$$C(f,g) = \int \frac{\hat{f}(p)\,\overline{\hat{g}(p)}}{|p|^2 + m^2}\,dp$$

### Gel'fand Triple Structure

The construction realizes a **rigged Hilbert space** (Gel'fand triple):

$$\mathcal{S}(D, F) \hookrightarrow H_T \hookrightarrow \mathcal{S}'(D, F)$$

where $H_T$ is the **Cameron-Martin space** — the completion of $\mathcal{S}(D, F)$ under the inner product $\langle f, g \rangle_T = \langle T(f), T(g) \rangle_H = C(f,g)$. The measure $\mu$ is supported on $\mathcal{S}'(D, F)$ but concentrated (in the sense of regularity) on distributions with specific Sobolev/Besov regularity determined by $T$.

This triple is the functional-analytic core of:
- **Constructive QFT**: the Osterwalder-Schrader and Wightman frameworks, where $\mu$ is the Euclidean path integral measure
- **Stochastic PDEs**: where $\mu$ provides the law of Gaussian driving noise
- **Infinite-dimensional probability**: where $\mu$ generalizes finite-dimensional Gaussian distributions

## API

### Input: `T : SchwartzMap D F →L[ℝ] H`

The user provides:
- Finite-dimensional domain `D` and coefficient space `F`
- A separable real Hilbert space `H` (with instances)
- A CLM `T : SchwartzMap D F →L[ℝ] H`

### Output

| Definition / Theorem | Type | Description |
|---|---|---|
| `measure T` | `Measure (Configuration D F)` | The Gaussian measure (with `IsProbabilityMeasure` instance) |
| `covariance T f g` | `ℝ` | $C(f,g) = \langle T(f), T(g) \rangle_H$ |
| `charFun T f` | integral identity | $\mathbb{E}[e^{i\omega(f)}] = e^{-\frac{1}{2}\|Tf\|^2}$ |
| `pairing_is_gaussian` | measure equality | Pushforward by $\omega \mapsto \omega(f)$ is $N(0, \|Tf\|^2)$ |
| `measure_centered` | integral = 0 | $\mathbb{E}[\omega(f)] = 0$ |
| `second_moment_eq_covariance` | integral identity | $\mathbb{E}[\omega(f)^2] = \|Tf\|^2$ |
| `cross_moment_eq_covariance` | integral identity | $\mathbb{E}[\omega(f)\omega(g)] = \langle Tf, Tg \rangle$ |
| `pairing_integrable` | `Integrable` | $\omega(f)$ is integrable |
| `pairing_memLp` | `MemLp` | $\omega(f) \in L^p$ for all finite $p$ (Fernique-type) |
| `pairing_product_integrable` | `Integrable` | $\omega(f)\omega(g)$ is integrable |

### Design note

The API takes only `T` as an explicit argument — no proof of infinite-dimensionality
is required. When `H` is finite-dimensional, the construction embeds `H` isometrically
into $\ell^2$ and builds the measure there, yielding a degenerate (finite-rank) Gaussian.
This allows testing with toy cases like $H = \mathbb{R}^n$.

## Module structure

```
GaussianMeasure/
  Axioms.lean                -- 5 axioms (Hermite basis)
  SpectralTheorem.lean       -- Compact self-adjoint spectral theorem
  NuclearSVD.lean            -- SVD for nuclear operators
  NuclearFactorization.lean  -- Source-indexed nuclear representation
  TargetFactorization.lean   -- Target-indexed factorization with ONB
  SeriesConvergence.lean     -- Gaussian series convergence (Tonelli)
  Construction.lean          -- Main construction + characteristic functional
  Properties.lean            -- Gaussianity, moments, Lp integrability
```

### Dependency chain

```
Axioms → SpectralTheorem → NuclearSVD → NuclearFactorization
                                            → TargetFactorization
                                                → SeriesConvergence
                                                    → Construction
                                                        → Properties
```

## Axiom budget

The library assumes **5 axioms**, all concerning the Hermite basis for Schwartz space. The spectral theorem for compact self-adjoint operators is **fully proved** in `SpectralTheorem.lean` with no custom axioms.

### Hermite basis (5 axioms)
1. **`schwartzHermiteBasis`** — countable basis for $\mathcal{S}(D, F)$
2. **`schwartzHermiteCoeff`** — coefficient CLMs
3. **`schwartz_hermite_expansion`** — expansion identity for CLMs
4. **`schwartz_hermite_seminorm_growth`** — polynomial growth of basis seminorms
5. **`schwartz_hermite_coefficient_decay`** — super-polynomial decay of coefficients

All 5 are provable from existing mathematics — they are axioms here only because their proofs require Mathlib infrastructure not yet available (e.g., multi-dimensional Hermite functions).

## Future work

- **Support theorems / Besov regularity**: The `pairing_memLp` result (Fernique-type $L^p$ bounds) is the first step toward showing $\mu$-a.s. $\omega \in B^s_{p,q}$ for appropriate $s, p, q$. Besov and Sobolev spaces enter as **measure support characterizations**, not as replacements for the Schwartz base space.
- **$\sigma$-algebra coincidence**: For separable nuclear Fréchet spaces, the cylindrical and Borel $\sigma$-algebras on the dual coincide. This would connect `instMeasurableSpaceConfiguration` to the Borel $\sigma$-algebra.

## Building

```bash
lake update
lake build
```

Requires Lean 4 v4.28.0-rc1 and Mathlib (fetched automatically by Lake).

## License

Apache 2.0

## References

- I.M. Gel'fand and N.Ya. Vilenkin, *Generalized Functions*, Vol. 4 (1964)
- B. Simon, *The P(φ)₂ Euclidean (Quantum) Field Theory* (1974)
- J. Glimm and A. Jaffe, *Quantum Physics: A Functional Integral Point of View* (1987)
- S. Thangavelu, *Lectures on Hermite and Laguerre Expansions* (1993)
