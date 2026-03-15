# `Tightness.lean` — Informal Summary

> **Source**: [`GaussianField/Tightness.lean`](../../GaussianField/Tightness.lean)
> **Generated**: 2026-03-15

## Overview

Proves the **Mitoma-Chebyshev tightness criterion** for probability measures on
nuclear Fréchet duals: if a family of probability measures $\{\mu_i\}$ on
$\mathrm{Configuration}(E) = E'$ (weak dual) has uniformly bounded second moments
$\sup_i \int (\omega f)^2\, d\mu_i \le C(f)$ for each test function $f \in E$,
then the family is tight.

This is the key technical input for extracting convergent subsequences of lattice
measures in the continuum limit, used in both the Gaussian and interacting cases.

## Status

**Main result**: `configuration_tight_of_uniform_second_moments`

**2 sorry declarations**:
- `uniform_bound_from_pointwise` — Baire category theorem: a pointwise-finite
  lower semicontinuous seminorm on a Fréchet space is continuous.
  This requires infrastructure not available in Mathlib.
- `h_basis_int` — Integrability of $(\omega(\psi_m))^2$ from its finite integral bound.
  Routine Mathlib API, to be filled.

**Length**: 458 lines

---

## Proof Architecture

### Step 1: Baire Category (sorry)

The pointwise supremum $q(f) = \sup_i (\int (\omega f)^2\, d\mu_i)^{1/2}$ is a
lower semicontinuous seminorm on the Fréchet space $E$. By the Baire category
theorem (Fréchet spaces are barreled), $q$ is continuous, hence bounded by one of
the defining seminorms: $q(f) \le M \cdot p_j(f)$.

### Step 2: Polynomial Growth

From `basis_growth`: $p_j(\psi_m) \le C_B \cdot (1+m)^s$, giving
$\int (\omega \psi_m)^2 \le B \cdot (1+m)^{2s}$ uniformly in $i$.

### Step 3: Compact Set Construction

Define $K = \{\omega : |\omega(\psi_m)| \le D \cdot (1+m)^{s+1}\ \forall m\}$
(coordinate box) with $D = \sqrt{2BS/\varepsilon}$ where $S = \sum 1/(1+m)^2$.

### Step 4: Compactness (`coordBox_isCompact`)

Proved via sequential compactness:
1. Map to $\mathbb{R}^\mathbb{N}$ via `configBasisEval`
2. Product $\prod_m [-R_m, R_m]$ compact by **Tychonoff** (`isCompact_univ_pi`)
3. Extract convergent subsequence (`IsCompact.tendsto_subseq`)
4. DM expansion + **Tannery's theorem** (`tendsto_tsum_of_dominated_convergence`)
   gives pointwise convergence of evaluations
5. Construct limit CLM, prove continuity from `coeff_decay` bound
6. Weak-* convergence via `tendsto_iff_forall_eval_tendsto_topDualPairing`

### Step 5: Mass Bound (`coordBox_compl_mass_le`)

Fully proved:
1. $K^c \subseteq \bigcup_m \{|\omega(\psi_m)| > R_m\}$ (complement of intersection)
2. **Chebyshev**: $\mu_i(\{|\omega(\psi_m)| > R_m\}) \le B/(D^2(1+m)^2)$ via Markov inequality
3. **Countable subadditivity**: $\mu_i(K^c) \le \sum_m B/(D^2(1+m)^2) = BS/D^2 \le \varepsilon$

## Key Lemmas

| Name | Statement |
|------|-----------|
| `summable_coeff_mul_pow` | $\sum_m |c_m(f)| \cdot (1+m)^r < \infty$ from `coeff_decay` |
| `coordBox_closed` | Coordinate box is closed in weak-* topology |
| `coordBox_measurable` | Coordinate box is cylindrically measurable |
| `coordBox_isCompact` | Coordinate box is compact (seq. compactness) |
| `coordBox_compl_mass_le` | Complement has measure $\le B/D^2 \cdot S$ |
| `basis_moment_poly_bound` | Basis moments grow polynomially |

## References

- Mitoma (1983), "Tightness of probabilities on $C([0,1]; \mathcal{S}')$ and $D([0,1]; \mathcal{S}')$"
- Simon, *The $P(\varphi)_2$ Euclidean QFT*, §V.1
- Gel'fand-Vilenkin, *Generalized Functions* Vol. 4, Ch. IV
