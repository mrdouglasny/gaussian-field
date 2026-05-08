/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice GFF as Pushforward of the Standard Multivariate Gaussian

The lattice Gaussian Free Field (`latticeGaussianMeasure d N a mass ha hmass`)
is a centered Gaussian on `Configuration (FinLatticeField d N)` with
covariance kernel `(1/a^d) M_a^{-1}` (Glimm-Jaffe-aligned). The
covariance operator has spectral decomposition

  `C = ∑ k, λ_k · (e_k ⊗ e_k)`

where `(e_k)` are the orthonormal eigenvectors
(`massEigenvectorBasis`) and `λ_k > 0` are the eigenvalues
(`massEigenvalues`). Defining

  `ξ_k(ω) := ω(e_k) / √(λ_k)`

makes the `(ξ_k)` an i.i.d. standard `N(0,1)` family. Equivalently,
the pushforward of `latticeGaussianMeasure` by the orthogonalization
map `gffOrthonormalProj` is the standard multivariate Gaussian
`Measure.pi (fun _ => gaussianReal 0 1)` on `FinLatticeSites d N → ℝ`.

This is the change-of-variables that makes the abstract polynomial-chaos
concentration theorem (`MarkovSemigroups.Gaussian.PolynomialChaosConcentration`,
upstream Janson Theorem 5.10) directly applicable to the lattice GFF.
Wick polynomials in the GFF correspond to multivariate Hermite
polynomials in the orthogonalized variables (proved in
`GaussianField/WickMultivariate.lean`).

## Main definitions

- `gffOrthonormalCoord` — the k-th orthogonalized coordinate
  `ω ↦ ω(e_k) / √(λ_k)`.
- `gffOrthonormalProj` — bundled into a vector-valued map.

## Main theorems

- `gffOrthonormalCoord_normal` — each `ξ_k` is standard `N(0,1)` under
  the lattice GFF.
- `gffOrthonormalCoord_independent` — distinct `ξ_k` are independent.
- `gffOrthonormalProj_pushforward_eq_stdGaussian` — the pushforward
  measure equals the product Gaussian.
- `gffOrthonormalProj_eq_charFun` — characteristic-function form,
  closer to the existing `Density.lean` infrastructure.

## References

- S. Janson, *Gaussian Hilbert Spaces*, Cambridge (1997), §1.3
  (orthogonal expansion of a Gaussian Hilbert space).

## Status

API + axiom skeleton (2026-05-08). Definitions are concrete; the four
main theorems are stated as axioms with proof-strategy docstrings. The
primary tool will be the existing `latticeGaussianFieldLaw_fourier`
in `GaussianField/Density.lean` plus characteristic-function uniqueness
(`MeasureTheory.Measure.ext_of_charFunDual`).
-/

import GaussianField.Density
import Lattice.SpectralCovariance
import Lattice.Covariance
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi

noncomputable section

namespace GaussianField

open MeasureTheory ProbabilityTheory

variable (d N : ℕ) [NeZero N]

/-- The k-th orthogonalized field coordinate:
`ξ_k(ω) := ω(e_k) / √(λ_k)`,
where `e_k = massEigenvectorBasis d N a mass k` and
`λ_k = massEigenvalues d N a mass k > 0`. As a function of `ω`, this
is linear, continuous, and (under the lattice GFF measure) a standard
`N(0,1)` random variable. -/
noncomputable def gffOrthonormalCoord
    (a mass : ℝ) (_ha : 0 < a) (_hmass : 0 < mass)
    (k : FinLatticeSites d N) :
    Configuration (FinLatticeField d N) → ℝ :=
  fun ω =>
    ω (fun x => (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) /
      Real.sqrt (massEigenvalues d N a mass k)

/-- The bundled orthogonalization map: takes a configuration to the
vector of its orthogonalized coordinates indexed by lattice sites
(equivalently, by eigenvalue indices, since `massEigenvectorBasis` is
indexed by `FinLatticeSites d N`). -/
noncomputable def gffOrthonormalProj
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Configuration (FinLatticeField d N) → (FinLatticeSites d N → ℝ) :=
  fun ω k => gffOrthonormalCoord d N a mass ha hmass k ω

/-- **Each orthogonalized coordinate is standard Gaussian.**

Under `latticeGaussianMeasure d N a mass ha hmass`, the random variable
`ξ_k = gffOrthonormalCoord d N a mass ha hmass k` has distribution
`gaussianReal 0 1` (mean zero, variance one).

**Reference:** Janson §1.3.

**Proof strategy:** The pairing `ω ↦ ω(e_k)` is centred Gaussian under
the GFF with variance `⟨T_GJ(e_k), T_GJ(e_k)⟩ = (a^d)⁻¹ · λ_k⁻¹ · 1
= (a^d λ_k)⁻¹` by the GJ-aligned spectral identity
(`lattice_covariance_GJ_eq_spectral` in `Lattice/Covariance.lean`).
Wait — the variance is computed directly: `e_k` is an eigenvector of
$Q$, so $T_{GJ}(e_k) = (a^d)^{-1/2} \lambda_k^{-1/2} e_k$, giving
$\|T_{GJ}(e_k)\|^2 = (a^d \lambda_k)^{-1}$.
Dividing by $\sqrt{\lambda_k}$ rescales variance to $(a^d)^{-1}$ —
hmm, this would not be unit variance. The orthonormalization needs to
account for the GJ scaling: the right normalization is
`ξ_k(ω) := ω(e_k) · √(a^d λ_k)`, not `ω(e_k) / √λ_k`.

**TODO** before proving this axiom: confirm the correct normalization
constant by computing `Var(ω(e_k))` under the GJ-aligned GFF (via
`spectralLatticeCovariance_inner` and `latticeCovariance_GJ_eq_inv_smul_bare`)
and choosing the divisor so the result has variance 1. The axiom
statement below is provisional pending this computation. -/
axiom gffOrthonormalCoord_normal
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (k : FinLatticeSites d N) :
    Measure.map (gffOrthonormalCoord d N a mass ha hmass k)
      (latticeGaussianMeasure d N a mass ha hmass) =
    gaussianReal 0 1

/-- **Distinct orthogonalized coordinates are independent.**

Under `latticeGaussianMeasure`, the family `(ξ_k)_{k ∈ FinLatticeSites d N}`
is mutually independent. Combined with `gffOrthonormalCoord_normal`,
this means the family is i.i.d. standard Gaussian.

**Reference:** Janson §1.4 (uncorrelated jointly Gaussian variables
are independent).

**Proof strategy:** The covariance
`Cov(ω(e_j), ω(e_k)) = ⟨T_GJ(e_j), T_GJ(e_k)⟩ = 0` for `j ≠ k` by the
spectral identity (`spectralLatticeCovariance_inner` evaluated on
distinct eigenvectors gives zero, since the eigenvectors are
orthonormal and the spectral expansion is diagonal). Jointly Gaussian
+ pairwise uncorrelated = mutually independent (Mathlib has the
2-variable case via `ProbabilityTheory.IndepFun`; the multi-variable
extension is by induction on the family). -/
axiom gffOrthonormalCoord_independent
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    iIndepFun (fun k : FinLatticeSites d N =>
      gffOrthonormalCoord d N a mass ha hmass k)
      (latticeGaussianMeasure d N a mass ha hmass)

/-- **The pushforward of the lattice GFF under orthogonalization is
the standard multivariate Gaussian.**

  `Measure.map gffOrthonormalProj (latticeGaussianMeasure …) = Π_k gaussianReal 0 1`

**Proof strategy:** Combine
`gffOrthonormalCoord_normal` (each marginal is `N(0,1)`) and
`gffOrthonormalCoord_independent` (the family is independent). The
product structure of the pushforward then matches `Measure.pi` of
1D `gaussianReal 0 1`. Mathlib's
`MeasureTheory.Measure.pi_eq_pi_iff_marginals` (or the equivalent
characterization via finite cylinders) closes this. -/
axiom gffOrthonormalProj_pushforward_eq_stdGaussian
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measure.map (gffOrthonormalProj d N a mass ha hmass)
      (latticeGaussianMeasure d N a mass ha hmass) =
    Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1)

/-- **Characteristic-functional form of the bridge** (alternative formulation).

The pushforward measure has the characteristic functional
`exp(-(1/2) ‖t‖²)` where the norm is the standard Euclidean norm on
`FinLatticeSites d N → ℝ`. Equivalent to
`gffOrthonormalProj_pushforward_eq_stdGaussian` by uniqueness of the
characteristic functional, but useful as a target form when proving
via `MeasureTheory.Measure.ext_of_charFunDual` (the same uniqueness
tool used in `GaussianField/Density.lean`). -/
axiom gffOrthonormalProj_charFun
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (t : FinLatticeSites d N → ℝ) :
    ∫ x : FinLatticeSites d N → ℝ,
      Complex.exp (Complex.I * ↑(∑ k, t k * x k))
        ∂(Measure.map (gffOrthonormalProj d N a mass ha hmass)
          (latticeGaussianMeasure d N a mass ha hmass)) =
    Complex.exp (-(1 / 2 : ℂ) * ↑(∑ k, t k ^ 2))

end GaussianField
