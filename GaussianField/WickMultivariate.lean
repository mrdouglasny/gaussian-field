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
theorem gffMultiWickMonomial_eq_hermite_product
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (α : FinLatticeSites d N → ℕ)
    (ω : Configuration (FinLatticeField d N)) :
    gffMultiWickMonomial d N a mass ha hmass α ω =
      ∏ k : FinLatticeSites d N,
        ((Polynomial.hermite (α k)).map (Int.castRingHom ℝ)).eval
          (gffOrthonormalCoord d N a mass ha hmass k ω) := by
  unfold gffMultiWickMonomial
  refine Finset.prod_congr rfl ?_
  intro k _
  rw [wick_eq_hermiteR (α k) 1 (by norm_num : (0:ℝ) < 1)]
  unfold scaledHermite
  rw [Real.sqrt_one, one_pow, one_mul, div_one]

/-- **Orthogonality of GFF multivariate Wick monomials under the lattice
GFF measure.**

  `∫ :ξ^α: · :ξ^β: dμ_GFF = δ_{αβ} · ∏_k α_k!`

This is the multivariate Wick orthogonality: distinct multi-indices
give zero, and the diagonal is a product of factorials.

**Proof strategy** (deferred):
1. Push forward to the standard multivariate Gaussian via
   `gffOrthonormalProj_pushforward_eq_stdGaussian` (now a theorem).
2. Decompose into a product over `k` via Fubini
   (`integral_fintype_prod_eq_prod`).
3. Each factor reduces to the 1D Wick inner product
   `∫ wickMonomial m 1 · wickMonomial n 1 ∂(gaussianReal 0 1) =
     if m = n then (m! : ℝ) else 0`.

**Blocking dependency:** the 1D Wick orthogonality identity above is
not yet in this repo or Mathlib. The existing
`SchwartzNuclear/WickOrthogonality.lean` only proves the n ≥ 1 mean
(`wickMonomial_mean_zero`); the cross-product / norm pair would
follow from analogous Stein-induction proofs but is a substantive
addition. -/
axiom gffMultiWickMonomial_orthogonality
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (α β : FinLatticeSites d N → ℕ) :
    ∫ ω, gffMultiWickMonomial d N a mass ha hmass α ω *
        gffMultiWickMonomial d N a mass ha hmass β ω
        ∂(latticeGaussianMeasure d N a mass ha hmass) =
    (if α = β then ((∏ k, (α k).factorial : ℕ) : ℝ) else 0)

/-- The GFF site (auto-)variance at site `x`:
`c_a(x) = ⟨φ(x), φ(x)⟩ = (a^d)⁻¹ · Σ_k λ_k⁻¹ · e_k(x)²`.

This is the diagonal of the lattice GFF covariance, i.e. the variance
that the local Wick subtraction must subtract for `:φ(x)^k:_{c_a}` to
be the QFT-correct Wick monomial. The site-Wick-expansion axiom below
is true only for this specific value of `c`; for any other `c`, the
expansion picks up lower-degree terms. -/
noncomputable def gffSiteVariance
    (a mass : ℝ) (_ha : 0 < a) (_hmass : 0 < mass)
    (x : FinLatticeSites d N) : ℝ :=
  haveI : Fintype (ZMod N) := ZMod.fintype N
  haveI : Fintype (FinLatticeSites d N) := Pi.instFintype
  (a ^ d)⁻¹ *
    ∑ k : FinLatticeSites d N,
      (massEigenvalues d N a mass k)⁻¹ *
        ((massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) ^ 2

/-- **Site Wick monomial expansion in the eigenbasis.**

The single-site Wick monomial $\mathopen{:}\phi(x)^k\mathclose{:}_{c_a(x)}$
(with the local Wick constant `c_a(x) = gffSiteVariance d N a mass ha hmass x
= (a^d)⁻¹ Σ_k λ_k⁻¹ e_k(x)²`) admits an explicit linear expansion in
eigenbasis multi-indices:

  `:φ(x)^k:_{c_a(x)} = ∑_{|α| = k} coeff(α, x, k) · :ξ^α:_1`,

where the coefficients are explicit polynomial combinations of the
eigenvector values $e_k(x)$ and eigenvalue powers $\lambda_k^{1/2}$.
The `totalDegree α = k` constraint is the key content: only multi-indices
of *exact* total degree `k` appear, because the local Wick subtraction
with the matched site variance `c_a(x)` cancels exactly the lower-degree
contractions.

**Proof strategy** (deferred): Substitute the eigenbasis expansion
$\phi(x) = \sum_k \lambda_k^{-1/2}\, e_k(x)\, \xi_k$ into the 1D Wick
recursion (note the `λ_k^{-1/2}` factor in the GJ-aligned normalisation
where `ξ_k` has unit variance and `Var(ω(e_k)) = (a^d λ_k)⁻¹`). The
Wick subtraction with constant `c_a(x) = Var(φ(x))` matches the
multinomial diagonal contractions exactly, killing all lower-degree
terms. The explicit coefficient is
`coeff α x k = (k! / ∏_j α_j!) · ∏_j (e_j(x) / √(a^d · λ_j))^{α_j}`
for `|α| = k`, otherwise 0.

**Blocking dependency:** a multivariate Wick algebra theorem of the
form "for independent `ξ_j ∼ N(0,1)` and `Y = ∑_j γ_j ξ_j`, one has
`:Y^k:_{Var Y} = ∑_{|α|=k} (k! / ∏ α_j!) · (∏ γ_j^{α_j}) · :ξ^α:_1`"
is not yet in this repo. -/
axiom siteWickMonomial_eigenbasis_expansion
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (k : ℕ) (x : FinLatticeSites d N) :
    ∃ (coeff : (FinLatticeSites d N → ℕ) → ℝ),
      (∀ α, coeff α ≠ 0 → MultiIndexLattice.totalDegree α = k) ∧
      ∀ ω : Configuration (FinLatticeField d N),
        wickMonomial k (gffSiteVariance d N a mass ha hmass x)
            (ω (Pi.single x 1)) =
        ∑ α ∈ multiIndicesOfDegree d N k, coeff α *
          gffMultiWickMonomial d N a mass ha hmass α ω

end GaussianField
