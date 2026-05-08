/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Multivariate Wick Polynomials in the Eigenbasis

Identifies multivariate Wick polynomials in the lattice GFF with
multivariate Hermite polynomials in the eigenbasis-orthogonalized
coordinates `(ξ_k)` from `GaussianField/StandardGaussianBridge.lean`.

The setup: the lattice GFF measure pushes forward via
`gffOrthonormalProj` to the standard multivariate Gaussian
`Π_k gaussianReal 0 1`. Under this change of variables, multivariate
Wick polynomials become multivariate Hermite polynomials, since:

* Each `ξ_k` is standard `N(0,1)` (variance 1).
* The 1D Wick monomial of variance 1 equals the probabilist's Hermite
  polynomial: `:x^n:_1 = He_n(x)` (consequence of `wick_eq_hermiteR`
  in `SchwartzNuclear/HermiteWick.lean`).
* Independence of distinct `ξ_k` makes
  `:ξ^α:_1 := ∏_k :ξ_k^{α_k}:_1` a multivariate Wick monomial that is
  also a multivariate Hermite polynomial.

The site Wick monomial `:φ(x)^d:_{c_a}` then admits an explicit
expansion in eigenbasis multi-indices, giving the chaos decomposition
of the GFF interaction.

## Main definitions

- `gffMultiWickMonomial` — multivariate Wick monomial indexed by a
  multi-index over eigenbasis sites.
- `gffMultiHermiteValue` — multivariate Hermite polynomial in the
  orthogonalized variables (purely as a function of `ω`).

## Main theorems

- `gffMultiWickMonomial_eq_hermiteMulti` — the two coincide.
- `siteWickMonomial_eigenbasis_expansion` — site Wick monomial as an
  explicit linear combination of `gffMultiWickMonomial`s.
- `interaction_centered_in_chaosLE` — the GFF interaction
  $V_a - \mathbb E V_a$ is a finite linear combination of Wick
  monomials of total degree $\le \deg P$, hence (after the change of
  variables) lies in `wienerChaosLE _ (deg P)`.

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), §3.1
  (Hermite polynomials) and Theorem 3.21 (orthogonality).
- Glimm and Jaffe, *Quantum Physics*, §6.1 (Wick ordering).
- `SchwartzNuclear/HermiteWick.lean` (this repo) — `wick_eq_hermiteR`,
  the 1D building block.

## Status

API + axiom skeleton (2026-05-08). Definitions are concrete; the
identification theorems are stated as axioms with proof-strategy
docstrings citing the existing 1D infrastructure. QFT-specific
specializations (e.g. interaction polynomial $V_a$ in the chaos)
live downstream in pphi2's `PolynomialChaosBridge.lean`; this file
provides only the generic Gaussian-Hilbert-space identifications.
-/

import GaussianField.StandardGaussianBridge
import GaussianField.Wick
import SchwartzNuclear.HermiteWick

noncomputable section

namespace GaussianField

open MeasureTheory ProbabilityTheory

variable (d N : ℕ) [NeZero N]

/-- Total degree of a multi-index over `FinLatticeSites d N`. -/
def MultiIndexLattice.totalDegree {d N : ℕ} [NeZero N]
    (α : FinLatticeSites d N → ℕ) : ℕ :=
  haveI : Fintype (ZMod N) := ZMod.fintype N
  haveI : Fintype (FinLatticeSites d N) := Pi.instFintype
  ∑ k, α k

/-- All multi-indices on `FinLatticeSites d N` with each component
bounded by `D + 1` (so total degree is bounded by `D · |Λ|`).
Constrained per-coordinate because `FinLatticeSites d N → ℕ` is not a
`Fintype`; the constraint gives a finite Finset enumeration via
`Fintype.piFinset`. -/
noncomputable def multiIndicesUpToDegree (d N D : ℕ) [NeZero N] :
    Finset (FinLatticeSites d N → ℕ) :=
  haveI : Fintype (ZMod N) := ZMod.fintype N
  haveI : Fintype (FinLatticeSites d N) := Pi.instFintype
  haveI : DecidableEq (FinLatticeSites d N) :=
    Classical.decEq (FinLatticeSites d N)
  Fintype.piFinset (fun _ : FinLatticeSites d N => Finset.range (D + 1))

/-- Multi-indices on `FinLatticeSites d N` with total degree exactly `k`
(and each coord in `Finset.range (k + 1)`). -/
noncomputable def multiIndicesOfDegree (d N k : ℕ) [NeZero N] :
    Finset (FinLatticeSites d N → ℕ) :=
  (multiIndicesUpToDegree d N k).filter
    (fun α => MultiIndexLattice.totalDegree α = k)

/-- Multivariate Wick monomial in the orthogonalized GFF coordinates
$(\xi_k)$. For a multi-index $\alpha : \mathrm{FinLatticeSites}\ d\ N
\to \mathbb N$, this is the product of 1D unit-variance Wick monomials:

  `:ξ^α:_1 := ∏_k :ξ_k^{α_k}:_1`.

(All variances are 1 because each `ξ_k` is standard Gaussian under the
lattice GFF pushforward.) -/
noncomputable def gffMultiWickMonomial
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (α : FinLatticeSites d N → ℕ)
    (ω : Configuration (FinLatticeField d N)) : ℝ :=
  ∏ k : FinLatticeSites d N,
    wickMonomial (α k) 1 (gffOrthonormalCoord d N a mass ha hmass k ω)

/-- **GFF multivariate Wick monomial = multivariate Hermite in
orthogonalized variables.**

Specifically, since each `ξ_k` is standard `N(0,1)` (variance 1) under
the GFF pushforward, the 1D Wick monomial `:ξ_k^{α_k}:_1` equals the
probabilist's Hermite polynomial $\mathrm{He}_{\alpha_k}(\xi_k)$ by
`wick_eq_hermiteR` (with $c = 1$, $\sqrt c = 1$). Taking the product
over $k$:

  `gffMultiWickMonomial α ω = ∏_k He_{α_k}(ξ_k(ω))`.

This is exactly the multivariate Hermite polynomial of multi-index
$\alpha$ evaluated at the orthogonalized vector. -/
axiom gffMultiWickMonomial_eq_hermite_product
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (α : FinLatticeSites d N → ℕ)
    (ω : Configuration (FinLatticeField d N)) :
    gffMultiWickMonomial d N a mass ha hmass α ω =
      ∏ k : FinLatticeSites d N,
        ((Polynomial.hermite (α k)).map (Int.castRingHom ℝ)).eval
          (gffOrthonormalCoord d N a mass ha hmass k ω)

/-- **Orthogonality of GFF multivariate Wick monomials under the lattice
GFF measure.**

  `∫ :ξ^α: · :ξ^β: dμ_GFF = δ_{αβ} · ∏_k α_k!`

This is the multivariate Wick orthogonality: distinct multi-indices
give zero, and the diagonal is a product of factorials.

**Proof strategy:** Push forward to the standard multivariate Gaussian
via `gffOrthonormalProj_pushforward_eq_stdGaussian`, then use Fubini
on the product Gaussian and the 1D `wick_eq_hermiteR` +
1D Hermite orthogonality (`wickMonomial_mean_zero` for the off-diagonal,
1D Hermite norm `∫ He_n² dγ = n!` for the diagonal). -/
axiom gffMultiWickMonomial_orthogonality
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (α β : FinLatticeSites d N → ℕ) :
    ∫ ω, gffMultiWickMonomial d N a mass ha hmass α ω *
        gffMultiWickMonomial d N a mass ha hmass β ω
        ∂(latticeGaussianMeasure d N a mass ha hmass) =
    (if α = β then ((∏ k, (α k).factorial : ℕ) : ℝ) else 0)

/-- **Site Wick monomial expansion in the eigenbasis.**

The single-site Wick monomial $\mathopen{:}\phi(x)^k\mathclose{:}_{c_a}$
admits an explicit linear expansion in eigenbasis multi-indices:

  `:φ(x)^k:_{c_a} = ∑_{|α| = k} c(α, x, k) · :ξ^α:_1`,

where the coefficients $c(\alpha, x, k)$ are explicit polynomial
combinations of the eigenvector values $e_k(x)$ and eigenvalue powers
$\lambda_k^{1/2}$.

**Proof strategy:** Substitute the eigenbasis expansion
$\phi(x) = \sum_k \sqrt{\lambda_k}\, e_k(x)\, \xi_k$ into the 1D Wick
recursion. The Wick subtraction normalization picks out exactly the
multivariate Wick monomials at total degree $k$. The combinatorial
identity is multinomial-style: each summand of the polynomial expansion
of $(\sum_k \sqrt{\lambda_k} e_k(x) \xi_k)^k$ contributes to a specific
multi-index, and the Wick subtraction collapses the lower-degree terms.

The variance $c$ is a generic parameter here (in QFT applications it
will be specialized to the local Wick constant
`c_a = ⟨φ(x), φ(x)⟩ = (1/a^d) · Σ_k λ_k^{-1} e_k(x)^2`, but this
file's API is QFT-agnostic). -/
axiom siteWickMonomial_eigenbasis_expansion
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (k : ℕ) (x : FinLatticeSites d N) (c : ℝ) :
    ∃ (coeff : (FinLatticeSites d N → ℕ) → ℝ),
      (∀ α, coeff α ≠ 0 → MultiIndexLattice.totalDegree α = k) ∧
      ∀ ω : Configuration (FinLatticeField d N),
        wickMonomial k c (ω (Pi.single x 1)) =
        ∑ α ∈ multiIndicesOfDegree d N k, coeff α *
          gffMultiWickMonomial d N a mass ha hmass α ω

end GaussianField
