# Wick-Polynomial / Wiener-Chaos Bridge: Roadmap

*Drafted 2026-05-08. Companion to
[`pphi2/docs/polynomial-chaos-concentration.md`](https://github.com/mrdouglasny/pphi2/blob/main/docs/polynomial-chaos-concentration.md)
(math writeup) and
[`markov-semigroups/docs/polynomial-chaos-roadmap.md`](https://github.com/mrdouglasny/markov-semigroups/blob/main/docs/polynomial-chaos-roadmap.md)
(upstream Janson 5.10 implementation plan). This file is the
gaussian-field-side roadmap: the orthogonal change-of-variables that
identifies the lattice GFF with a standard multivariate Gaussian,
under which Wick polynomials become multivariate Hermite polynomials
and the markov-semigroups polynomial-chaos concentration theorem
becomes directly applicable.*

## Goal

Provide the bridge that makes
`MarkovSemigroups.Gaussian.PolynomialChaosConcentration`
(Janson Theorem 5.10) usable on the lattice GFF
(`Lattice.Covariance.latticeGaussianMeasure`):

> The lattice GFF measure $\mu_{\rm GFF}$ on `FinLatticeField d N`
> with covariance kernel $C = (1/a^d) M_a^{-1}$ is the pushforward
> of the standard multivariate Gaussian $\gamma_n$ on
> $\mathrm{Fin}\ n \to \mathbb R$ ($n = |\Lambda| = N^d$) under the
> linear isometry $\sqrt{C} \colon \ell^2(\Lambda) \to \ell^2(\Lambda)$.
> Wick polynomials in the GFF correspond to multivariate Hermite
> polynomials in the orthogonalized variables.

With this bridge, polynomial-chaos concentration of the GFF Wick
polynomial $V_a - \mathbb E V_a \in \mathcal H^{\le 2k}$ follows
mechanically from the upstream theorem.

## Strategy: identify Hermite-in-eigenbasis with Wick-in-GFF

The covariance operator $C$ has spectral decomposition
$C = \sum_k \lambda_k \, e_k e_k^*$ with eigenvalues $\lambda_k > 0$
and orthonormal eigenvectors $e_k$ (these are
`Lattice.SpectralCovariance.massEigenvectorBasis`).

Set $\xi_k(\omega) = \omega(e_k) / \sqrt{\lambda_k}$. The
`(\xi_k)` are i.i.d. standard $\mathcal N(0,1)$ under $\mu_{\rm GFF}$
(the orthogonal change of variables). Then for a Wick monomial
$:\phi(x)^d:_{c_a}$ (with $c_a = \mathbb E[\phi(x)^2]$, the
local Wick constant), expand via the eigenbasis
$\phi(x) = \sum_k \sqrt{\lambda_k} \, e_k(x) \, \xi_k$ and use
multilinearity of Wick ordering. The result is an explicit
multivariate Hermite polynomial in the $(\xi_k)$.

This bypasses any analytic infinite-dim machinery: the change of
variables is a finite-dim linear isometry, and the Hermite/Wick
identification is the same algebraic identity as in 1D
(`SchwartzNuclear/HermiteWick.lean`'s `wick_eq_hermiteR`),
extended via tensor products.

## Existing gaussian-field infrastructure

A surprising amount is already in place:

| Already exists | File | Content |
|---|---|---|
| 1D Wick monomial | `GaussianField/Wick.lean` | `wickMonomial`, `wick_recursive`, `wick_bound` |
| 1D Wick = scaled Hermite | `SchwartzNuclear/HermiteWick.lean` | `wick_eq_hermiteR` (`:x^n:_c = c^{n/2} · He_n(x/√c)`) |
| 1D Wick zero mean | `SchwartzNuclear/WickOrthogonality.lean` | `wickMonomial_mean_zero` |
| Hermite Hilbert basis | `SchwartzNuclear/HermiteHilbertBasis.lean` | `hermiteHilbertBasis` of $L^2(\mathbb R, \mathrm{Lebesgue})$ |
| Hermite tensor products | `SchwartzNuclear/HermiteTensorProduct.lean` | multivariate building blocks |
| Spectral decomposition of GFF covariance | `Lattice/SpectralCovariance.lean` | `massEigenvalues`, `massEigenvectorBasis` |
| GJ-aligned covariance bridge | `Lattice/Covariance.lean` | `latticeCovarianceGJ`, `lattice_covariance_GJ_eq_spectral` |
| Density bridge | `GaussianField/Density.lean` | `latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure` (the GFF measure is the normalized density measure) |

What's MISSING for the markov-semigroups bridge:

| Needed | Where to add | Rough size |
|---|---|---|
| Standard-Gaussian-via-eigenbasis identification of GFF | new: `GaussianField/StandardGaussianBridge.lean` | ~150-250 lines |
| Multivariate Wick = multivariate Hermite (in eigenbasis) | new: `GaussianField/WickMultivariate.lean` | ~150-250 lines |
| Wick-polynomial chaos degree | new (above file or separate) | ~50-100 lines |

## File layout

### `GaussianField/StandardGaussianBridge.lean`

The core change-of-variables. Identifies the lattice GFF with a standard
multivariate Gaussian under $\sqrt C$.

```lean
/-- The eigenbasis-orthogonalized field coordinates:
`ξ_k(ω) = ω(e_k) / √(λ_k)`. -/
noncomputable def gffOrthonormalCoord (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (k : FinLatticeSites d N) :
    Configuration (FinLatticeField d N) → ℝ

/-- The eigenbasis projection map: bundles all coordinates into a vector. -/
noncomputable def gffOrthonormalProj (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Configuration (FinLatticeField d N) → (FinLatticeSites d N → ℝ)

/-- **The orthogonal coordinates are i.i.d. standard Gaussian.**
Under the lattice GFF measure, `(ξ_k)` are i.i.d. `N(0,1)`. Equivalently,
the pushforward of `latticeGaussianMeasure` by `gffOrthonormalProj` is
the standard multivariate Gaussian on `FinLatticeSites d N → ℝ`.

**Reference:** Janson, *Gaussian Hilbert Spaces*, §1.3 (orthogonal
expansion of a Gaussian Hilbert space). -/
theorem gffOrthonormalProj_pushforward_eq_stdGaussian
    (d N : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measure.map (gffOrthonormalProj d N a mass ha hmass)
      (latticeGaussianMeasure d N a mass ha hmass) =
    MeasureTheory.Measure.pi
      (fun _ : FinLatticeSites d N => ProbabilityTheory.gaussianReal 0 1)

/-- **The inverse map: standard Gaussian -> lattice GFF.** Pushing the
standard Gaussian through `√C ∘ embed` recovers the lattice GFF. -/
theorem stdGaussian_map_sqrtC_eq_gff
    (d N : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measure.map (sqrtCovarianceEmbedding d N a mass ha hmass)
      (MeasureTheory.Measure.pi
        (fun _ : FinLatticeSites d N => ProbabilityTheory.gaussianReal 0 1)) =
    latticeGaussianMeasure d N a mass ha hmass
```

Key proof ingredients:
- The `(ξ_k)` are uncorrelated by spectral decomposition + the GFF
  covariance identity
  (`spectralLatticeCovariance_inner` from `Lattice/SpectralCovariance.lean`).
- Uncorrelated jointly Gaussian variables are independent (Janson §1.4
  / `Mathlib.Probability.Independence.Basic`).
- Standard Gaussian on $\mathrm{Fin}\ n \to \mathbb R$ is the product
  measure of $n$ copies of `gaussianReal 0 1`.

### `GaussianField/WickMultivariate.lean`

Identification of multivariate Wick polynomials in the GFF with
multivariate Hermite polynomials in the orthogonalized coordinates.

```lean
/-- Multivariate Wick monomial in the GFF: for a multi-index
`α : Fin (#sites) → ℕ` over the eigenbasis,
`:ξ^α: := ∏_k :ξ_k^{α_k}:_1` (each factor is a 1D Wick monomial of
unit variance, since the `ξ_k` are standard Gaussian). -/
noncomputable def gffWickMonomial (d N : ℕ) [NeZero N]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (α : FinLatticeSites d N → ℕ)
    (ω : Configuration (FinLatticeField d N)) : ℝ

/-- **Identification: GFF Wick monomial = multivariate Hermite
in orthogonalized coordinates.**

  `gffWickMonomial α ω = hermiteMultiEval α (gffOrthonormalProj ω)`

Immediate from the 1D `wick_eq_hermiteR` applied per coordinate, plus
the product structure of multivariate Hermite. -/
theorem gffWickMonomial_eq_hermiteMulti
    (d N : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (α : FinLatticeSites d N → ℕ)
    (ω : Configuration (FinLatticeField d N)) :
    gffWickMonomial d N a mass ha hmass α ω =
    hermiteMultiEval α (gffOrthonormalProj d N a mass ha hmass ω)

/-- **Site Wick monomial as a sum over eigenbasis multi-indices.**

The Wick monomial `:φ(x)^d:_{c_a}` expressed in eigenbasis coordinates
expands as `∑_α (combinatorial coefficient) · gffWickMonomial α ω`.
This is the explicit form needed to identify the Wick polynomial as a
finite linear combination of Hermite multi-indices, hence in
`wienerChaosLE _ d`. -/
theorem siteWickMonomial_eigenbasis_expansion
    (d N : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (k : ℕ) (x : FinLatticeSites d N) :
    ∃ (c : (FinLatticeSites d N → ℕ) → ℝ),
      ∀ ω : Configuration (FinLatticeField d N),
      wickMonomial k (siteWickConstant d N a mass x) (ω (Pi.single x 1)) =
      ∑ α ∈ multiIndicesOfDegree k, c α * gffWickMonomial d N a mass ha hmass α ω
```

### Optional: `GaussianField/WickChaos.lean`

If we want a clean "chaos degree of a Wick polynomial" statement
factored from the bridge:

```lean
/-- **The interaction `V_a - E V_a` lies in `H^{≤ deg P}`** in the
markov-semigroups Wiener-chaos sense, transported via the orthogonal
change of variables. -/
theorem interaction_centered_mem_wienerChaosLE
    (d N : ℕ) [NeZero N] (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (P : InteractionPolynomial) :
    (interactionFunctional d N P a mass - (∫ ω, interactionFunctional d N P a mass ω
      ∂(latticeGaussianMeasure d N a mass ha hmass))) ∈
    -- via gffOrthonormalProj pushforward to the standard-Gaussian
    -- chaos space
    SOMETHING
```

(This bridges to `MarkovSemigroups.Gaussian.WienerChaos.wienerChaosLE`
once we depend on markov-semigroups; for now it is the natural
formulation that pphi2's `polynomial_chaos_exp_moment_bridge` will
unfold.)

## Order of work

1. **`StandardGaussianBridge.lean`** (~150-250 lines, ~3-5 days). The
   core change-of-variables theorem. Hard parts: showing the
   pushforward measure equals the product Gaussian (joint independence
   + per-coordinate standard normal), and identifying the inverse map.
   Mathlib's `MeasureTheory.Measure.map`, `Measure.pi`,
   `ProbabilityTheory.gaussianReal`, and `Probability.Independence.Basic`
   are the relevant pieces.
2. **`WickMultivariate.lean`** (~150-250 lines, ~3-5 days). The
   identification of multivariate Wick with multivariate Hermite.
   Hard part: the `siteWickMonomial_eigenbasis_expansion` combinatorial
   identity (Wick monomial as a sum over multi-indices). The 1D
   `wick_eq_hermiteR` from `HermiteWick.lean` does most of the work
   per coordinate; the multi-index combinatorics is mechanical.
3. **`WickChaos.lean`** (~50-100 lines, ~2-3 days). Optional, only
   needed if we want a clean chaos-membership statement that doesn't
   require pphi2 to depend on markov-semigroups. Can be deferred until
   the lakefile-level dependency lands.

Total in gaussian-field: ~1-2 weeks.

This is the prerequisite for using
`MarkovSemigroups.Gaussian.PolynomialChaosConcentration` in pphi2.

## Risks and exit ramps

- **Pushforward equality** (step 1) is fiddly because Mathlib's
  `Measure.map` and `Measure.pi` need careful handling of measurability
  hypotheses. If `gffOrthonormalProj` measurability is hard to set up,
  state it as a single equality of pushforward measures and prove via
  characteristic-function uniqueness using
  `MeasureTheory.Measure.ext_of_charFun` (which gaussian-field already
  uses extensively in `Density.lean`).
- **Per-site Wick expansion** (step 2's hardest piece) involves
  combinatorics over multi-indices. If this fights us, an alternative is
  to bypass it by expressing the entire Wick polynomial $V_a$ directly
  in the eigenbasis (instead of summing per-site Wick monomials), which
  avoids the per-site expansion entirely.
- **Mathlib Hermite multivariate gap**: Mathlib has `Polynomial.hermite`
  (1D) but no multivariate version; the multivariate case is currently
  axiomatized in markov-semigroups. The bridge here can be stated
  abstractly enough to not depend on the multivariate Hermite
  *definition* upstream — it just needs the existence/uniqueness of an
  orthonormal Hermite-like basis.

## Coordination across the project family

```
gaussian-field    [needs new]   StandardGaussianBridge + WickMultivariate
        ↑
markov-semigroups [API form]    Janson 5.10 (Wiener chaos + OU + Bonami-Nelson)
        ↑
pphi2             [API form]    polynomial_chaos_exp_moment_bridge axiom
                                + dynamical-cutoff wiring
```

Once the bridge in gaussian-field lands, pphi2 can replace the
`polynomial_chaos_exp_moment_bridge` axiom with a derivation that
invokes the markov-semigroups Janson 5.10 statement (still axiomatic
upstream in markov-semigroups, but pphi2's axiom is gone). When
markov-semigroups also discharges, the chain becomes axiom-free except
for the residual smooth-side / dynamical-cutoff scaffolding in
pphi2/NelsonEstimate/.

## Time budget (revised total for Cluster A)

* gaussian-field: StandardGaussianBridge + WickMultivariate
  (this roadmap): **1-2 weeks**.
* markov-semigroups: prove the API axioms (per
  `markov-semigroups/docs/polynomial-chaos-roadmap.md`):
  **2-3 weeks**.
* pphi2: discharge `polynomial_chaos_exp_moment_bridge`,
  rewire dynamical cutoff in `NelsonEstimate.lean`, replace
  `RoughErrorBound.lean` `True`-stubs:
  **2-3 weeks**.
* **Total: 5-8 weeks**, matching the original Gemini estimate.

## What this unlocks beyond the polynomial-chaos goal

* **Standalone**: a clean change-of-variables theorem for the
  lattice GFF is reusable by anyone working with Wick moments,
  cluster expansions, or hypercontractivity in finite-volume.
* **Mathlib contribution**: the identification of multivariate
  Wick polynomials with multivariate Hermite (under the natural
  Gaussian-Hilbert-space orthogonalization) is a clean algebraic
  result with no QFT-specific assumptions, suitable for upstreaming.
* **pphi2N**: the same change of variables makes the polynomial-chaos
  concentration apply to the O(N) sigma-model fields.
* **Future Mathlib probability**: pairing this with the abstract
  Wiener chaos in markov-semigroups gives a clean concrete
  polynomial-concentration toolkit for the lattice setting.
