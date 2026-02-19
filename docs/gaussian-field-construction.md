# Gaussian Field Construction — Proof Overview

This directory contains ~2,960 lines of Lean 4 constructing a centered Gaussian
probability measure on the weak dual of a nuclear Fréchet space, i.e., building
[`GaussianField.measure`](../GaussianField/Construction.lean#L489) from a CLM `T : E →L[ℝ] H`.

**Status: Complete (0 sorrys, 0 axioms).**

## Overall Strategy

Given a nuclear Fréchet space $E$ and a CLM $T : E \to H$ into a separable
Hilbert space, we construct a probability measure $\mu$ on
[`Configuration E`](../GaussianField/Construction.lean#L61) $= \text{WeakDual}(\mathbb{R}, E)$
satisfying the characteristic functional identity
([`charFun`](../GaussianField/Construction.lean#L687)):

$$\int_{E'} e^{i\langle \omega, f \rangle}\, d\mu(\omega) = e^{-\frac{1}{2}\|T(f)\|^2}$$

The construction proceeds by:
1. **Nuclear factorization**: Decompose $T$ through an intermediate Hilbert space
   $K = \ell^2$ with an adapted ONB $\{e_n\}$ and vectors $v_n \in K$ with
   $\sum \|v_n\| < \infty$ such that $\langle e_n, T(f)\rangle = \langle v_n, j(f)\rangle_K$.
2. **Gaussian series**: Sample iid $\xi_n \sim N(0,1)$ and form
   $\omega(f) = \sum_n \xi_n \langle e_n, T(f)\rangle$, which converges a.s. by
   nuclear summability.
3. **Pushforward**: Define $\mu$ as the pushforward of the product Gaussian measure
   through the series limit map.

## Shared Infrastructure (`Nuclear/`)

These files define the `NuclearSpace` typeclass and Köthe sequence spaces, shared by both
`SchwartzNuclear/` and `GaussianField/`:

| File | Lines | Description |
|------|------:|-------------|
| [`NuclearSpace.lean`](../Nuclear/NuclearSpace.lean) | 76 | [`NuclearSpace`](../Nuclear/NuclearSpace.lean#L41) typeclass |
| [`NuclearTensorProduct.lean`](../Nuclear/NuclearTensorProduct.lean) | 355 | [`RapidDecaySeq`](../Nuclear/NuclearTensorProduct.lean#L43), [`rapidDecaySeminorm`](../Nuclear/NuclearTensorProduct.lean#L118), tensor product instance |

## File Structure

| File | Lines | Description |
|------|------:|-------------|
| [`SpectralTheorem.lean`](../GaussianField/SpectralTheorem.lean) | 468 | [`compact_selfAdjoint_spectral`](../GaussianField/SpectralTheorem.lean#L451) |
| [`NuclearSVD.lean`](../GaussianField/NuclearSVD.lean) | 640 | [`nuclear_sequence_svd`](../GaussianField/NuclearSVD.lean#L515), [`ell2'`](../GaussianField/NuclearSVD.lean#L50) |
| [`NuclearFactorization.lean`](../GaussianField/NuclearFactorization.lean) | 190 | [`nuclear_clm_representation`](../GaussianField/NuclearFactorization.lean#L134) |
| [`TargetFactorization.lean`](../GaussianField/TargetFactorization.lean) | 324 | [`nuclear_clm_target_factorization`](../GaussianField/TargetFactorization.lean#L196) |
| [`Construction.lean`](../GaussianField/Construction.lean) | 715 | [`measure`](../GaussianField/Construction.lean#L489), [`charFun`](../GaussianField/Construction.lean#L687) |
| [`Properties.lean`](../GaussianField/Properties.lean) | 193 | [`pairing_is_gaussian`](../GaussianField/Properties.lean#L50), [`cross_moment_eq_covariance`](../GaussianField/Properties.lean#L153) |
| **Total** | **2,961** | |

## Dependency Graph

```
NuclearSpace (Nuclear/)
├── NuclearTensorProduct (Nuclear/, Kothe sequence space, used by SchwartzNuclear/)
├── NuclearFactorization (source-indexed decomposition)
│   └── TargetFactorization (target-indexed, uses NuclearSVD)
│       └── Construction (Gaussian measure)
│           └── Properties (moments, covariance)
└── SpectralTheorem
    └── NuclearSVD (compact operator SVD)
```

## What Is Proved

### Nuclear Space Typeclass ([`NuclearSpace.lean`](../Nuclear/NuclearSpace.lean))

[`NuclearSpace E`](../Nuclear/NuclearSpace.lean#L41) requires a Schauder-like basis `{ψ_m}` with:
- **Expansion**: every CLF $\varphi$ satisfies $\varphi(f) = \sum_m c_m(f)\,\varphi(\psi_m)$
- **Basis growth**: $p_i(\psi_m) \le C(1+m)^s$ for each seminorm $p_i$
- **Coefficient decay**: $|c_m(f)|(1+m)^k \le C\,p_S(f)$ for each $k$

### Spectral Theorem ([`SpectralTheorem.lean`](../GaussianField/SpectralTheorem.lean))

[`compact_selfAdjoint_spectral`](../GaussianField/SpectralTheorem.lean#L451):
full spectral theorem for compact self-adjoint operators on separable Hilbert spaces —
eigenvector ONB with eigenvalues converging to zero. Proved via iterated
Rayleigh quotient maximization and orthogonal complement descent.

### Nuclear SVD ([`NuclearSVD.lean`](../GaussianField/NuclearSVD.lean))

[`nuclear_sequence_svd`](../GaussianField/NuclearSVD.lean#L515):
given a sequence $\{y_m\}$ in $H$ with $\sum \|y_m\| < \infty$, constructs:
- An adapted ONB $\{e_n\}$ of $H$
- Singular values $\sigma_n \ge 0$ with $\sum \sigma_n < \infty$
- Rotation matrix $W_{nm}$ with $\langle e_n, y_m\rangle = \sigma_n W_{nm}$

Uses the spectral theorem applied to $A^*A$ where $A :$ [`ell2'`](../GaussianField/NuclearSVD.lean#L50) $\to H$ is the
nuclear map $x \mapsto \sum x_m y_m$.

### Nuclear Factorization ([`NuclearFactorization.lean`](../GaussianField/NuclearFactorization.lean) + [`TargetFactorization.lean`](../GaussianField/TargetFactorization.lean))

Two-stage factorization of any CLM $T : E \to H$:

1. **Source-indexed** ([`nuclear_clm_representation`](../GaussianField/NuclearFactorization.lean#L134)):
   $T(f) = \sum_m \varphi_m(f)\, y_m$ with $\sum \|y_m\| < \infty$ and equicontinuous $\varphi_m$.

2. **Target-indexed** ([`nuclear_clm_target_factorization`](../GaussianField/TargetFactorization.lean#L196)):
   Combines with nuclear SVD to produce an adapted ONB $\{e_n\}$, an $\ell^2$ embedding
   $j : E \to \ell^2$, and vectors $v_n \in \ell^2$ with $\sum \|v_n\| < \infty$ and
   $\langle e_n, T(f)\rangle = \langle v_n, j(f)\rangle_{\ell^2}$.

### Gaussian Measure ([`Construction.lean`](../GaussianField/Construction.lean))

- **Noise measure**: $\mu_{\text{noise}} = \bigotimes_n N(0,1)$ on $\mathbb{R}^\mathbb{N}$
- **Series convergence**: $\sum_n \xi_n v_n$ converges a.s. (Tonelli argument)
- **Series limit map**: $\omega(f) = \sum_n \xi_n \langle e_n, T(f)\rangle$ defines $\omega \in E'$ a.s.
- **Pushforward measure**: [`measure T`](../GaussianField/Construction.lean#L489) $= (\text{seriesLimit})_* \mu_{\text{noise}}$
- **Characteristic functional** ([`charFun`](../GaussianField/Construction.lean#L687)): $\hat\mu(f) = e^{-\frac{1}{2}\|T(f)\|^2}$
- Handles both infinite- and finite-dimensional $H$ (via $\ell^2$ embedding)

### Properties ([`Properties.lean`](../GaussianField/Properties.lean))

- [`pairing_is_gaussian`](../GaussianField/Properties.lean#L50): each pairing $\omega \mapsto \omega(f)$ is Gaussian with variance $\|T(f)\|^2$
- [`pairing_memLp`](../GaussianField/Properties.lean#L86): pairings are $L^p$ for all $p < \infty$ (Fernique-type)
- [`measure_centered`](../GaussianField/Properties.lean#L104): $\mathbb{E}[\omega(f)] = 0$
- [`second_moment_eq_covariance`](../GaussianField/Properties.lean#L117): $\mathbb{E}[\omega(f)^2] = \|T(f)\|^2$
- [`cross_moment_eq_covariance`](../GaussianField/Properties.lean#L153): $\mathbb{E}[\omega(f)\,\omega(g)] = \langle T(f), T(g)\rangle_H$

## References

- Gel'fand, Vilenkin, *Generalized Functions* Vol. 4, Ch. 3-4
- Fernique, "Processus lineaires, processus generalises", Ann. Inst. Fourier 1967
- Durrett, *Probability: Theory and Examples*, Ch. 2
