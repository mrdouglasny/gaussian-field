# gaussian-measure

A Lean 4 / Mathlib library for constructing **centered Gaussian probability measures on duals of Schwartz spaces**.

Given a continuous linear map (CLM) $T : \mathcal{S}(D, F) \to H$ from a Schwartz space to a separable infinite-dimensional Hilbert space $H$, the library constructs a probability measure $\mu$ on the weak dual $\mathcal{S}'(D, F) = \text{WeakDual}\ \mathbb{R}\ (\text{SchwartzMap}\ D\ F)$ satisfying the characteristic functional identity:

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

## API

### Input: `T : SchwartzMap D F →L[ℝ] H`

The user provides:
- Finite-dimensional domain `D` and coefficient space `F`
- A separable infinite-dimensional real Hilbert space `H` (with instances)
- A CLM `T : SchwartzMap D F →L[ℝ] H`
- A proof `h_inf : ¬ FiniteDimensional ℝ H`

### Output

| Definition / Theorem | Type | Description |
|---|---|---|
| `measure T h_inf` | `ProbabilityMeasure (Configuration D F)` | The Gaussian measure |
| `covariance T f g` | `ℝ` | $C(f,g) = \langle T(f), T(g) \rangle_H$ |
| `charFun T h_inf f` | integral identity | $\mathbb{E}[e^{i\omega(f)}] = e^{-\frac{1}{2}\|Tf\|^2}$ |
| `measure_centered` | integral = 0 | $\mathbb{E}[\omega(f)] = 0$ |
| `second_moment_eq_covariance` | integral identity | $\mathbb{E}[\omega(f)^2] = \|Tf\|^2$ |
| `cross_moment_eq_covariance` | integral identity | $\mathbb{E}[\omega(f)\omega(g)] = \langle Tf, Tg \rangle$ |
| `pairing_integrable` | `Integrable` | $\omega(f)$ is integrable |

### Design note

The current API uses explicit `T` and `h_inf` arguments. An alternative bundled
`GaussianMeasureData` structure (carrying `H` with its instances) would give cleaner
dot-notation but requires careful handling of Lean's instance resolution for bundled
type class fields. See the comment in `Construction.lean` for details.

## Module structure

```
GaussianMeasure/
  Axioms.lean                -- 7 axioms (2 spectral + 5 Hermite)
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

The library assumes **7 axioms**, all standard functional analysis results:

### Spectral theory (2 axioms)
1. **`compact_operator_eigenspace_finiteDimensional`** — eigenspaces of compact operators for nonzero eigenvalues are finite-dimensional
2. **`compact_selfAdjoint_eigenvalues_finite_above_eps`** — compact self-adjoint operators have finitely many eigenvalues above any threshold

### Hermite basis (5 axioms)
3. **`schwartzHermiteBasis`** — countable basis for $\mathcal{S}(D, F)$
4. **`schwartzHermiteCoeff`** — coefficient CLMs
5. **`schwartz_hermite_expansion`** — expansion identity for CLMs
6. **`schwartz_hermite_seminorm_growth`** — polynomial growth of basis seminorms
7. **`schwartz_hermite_coefficient_decay`** — super-polynomial decay of coefficients

All 7 are provable from existing mathematics — they are axioms here only because their proofs require Mathlib infrastructure not yet available (e.g., multi-dimensional Hermite functions, spectral theorem for compact operators).

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
