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
`ξ_k(ω) := ω(e_k) · √(a^d · λ_k)`,
where `e_k = massEigenvectorBasis d N a mass k` and
`λ_k = massEigenvalues d N a mass k > 0`. As a function of `ω`, this
is linear, continuous, and (under the lattice GFF measure) a standard
`N(0,1)` random variable.

The GJ-aligned variance is `Var(ω(e_k)) = (a^d λ_k)⁻¹` (since
`T_GJ(e_k) = (a^d λ_k)^{-1/2} e_k`, see
`lattice_covariance_GJ_eq_spectral` in `Lattice/Covariance.lean`),
so the multiplier `√(a^d λ_k)` rescales to unit variance. -/
noncomputable def gffOrthonormalCoord
    (a mass : ℝ) (_ha : 0 < a) (_hmass : 0 < mass)
    (k : FinLatticeSites d N) :
    Configuration (FinLatticeField d N) → ℝ :=
  fun ω =>
    ω (fun x => (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
      Real.sqrt (a ^ d * massEigenvalues d N a mass k)

/-- The bundled orthogonalization map: takes a configuration to the
vector of its orthogonalized coordinates indexed by lattice sites
(equivalently, by eigenvalue indices, since `massEigenvectorBasis` is
indexed by `FinLatticeSites d N`). -/
noncomputable def gffOrthonormalProj
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Configuration (FinLatticeField d N) → (FinLatticeSites d N → ℝ) :=
  fun ω k => gffOrthonormalCoord d N a mass ha hmass k ω

/-! ## Variance computation

The k-th eigenvector `e_k` has GJ-covariance
`⟨T_GJ(e_k), T_GJ(e_k)⟩ = (a^d λ_k)⁻¹`. Combined with `pairing_is_gaussian`
this gives `Var(ω(e_k)) = (a^d λ_k)⁻¹`, so multiplying by `√(a^d λ_k)`
rescales to unit variance. -/

/-- The GJ-covariance of the k-th eigenvector with itself is `(a^d λ_k)⁻¹`. -/
theorem latticeCovarianceGJ_eigenvector_inner_self
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (k : FinLatticeSites d N) :
    let e_k : FinLatticeField d N :=
      fun x => (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x
    @inner ℝ ell2' _
        (latticeCovarianceGJ d N a mass ha hmass e_k)
        (latticeCovarianceGJ d N a mass ha hmass e_k) =
      (a^d * massEigenvalues d N a mass k)⁻¹ := by
  intro e_k
  -- This is `covariance(latticeCovarianceGJ) e_k e_k`.
  show GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass) e_k e_k =
    (a^d * massEigenvalues d N a mass k)⁻¹
  rw [lattice_covariance_GJ_eq_spectral d N a mass ha hmass e_k e_k]
  -- Goal: (a^d)⁻¹ * Σ_j λ_j⁻¹ · c_j(e_k)² = (a^d λ_k)⁻¹
  -- where c_j(e_k) = Σ_x v_j(x) · v_k(x) = ⟨v_j, v_k⟩ = δ_{jk}.
  have h_inner : ∀ j : FinLatticeSites d N,
      (∑ x, (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x * e_k x) =
      if j = k then (1 : ℝ) else 0 := by
    intro j
    -- This sum is `inner ℝ v_j v_k` in EuclideanSpace, which orthonormality
    -- gives as the indicator. Convert via dotProduct (mirroring the pattern
    -- in `massEigenbasis_sum_mul_sum_eq_site_inner`).
    have h_orth :
        @inner ℝ (EuclideanSpace ℝ (FinLatticeSites d N)) _
          (massEigenvectorBasis d N a mass j)
          (massEigenvectorBasis d N a mass k) =
        if j = k then (1 : ℝ) else 0 :=
      orthonormal_iff_ite.mp (massEigenvectorBasis d N a mass).orthonormal j k
    have h_eq :
        (∑ x, (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x * e_k x) =
        @inner ℝ (EuclideanSpace ℝ (FinLatticeSites d N)) _
          (massEigenvectorBasis d N a mass j)
          (massEigenvectorBasis d N a mass k) := by
      change _ =
        ((massEigenvectorBasis d N a mass k).ofLp ⬝ᵥ
          star (massEigenvectorBasis d N a mass j).ofLp)
      simp [dotProduct, star_trivial, e_k, mul_comm]
    rw [h_eq]; exact h_orth
  rw [show (∑ j : FinLatticeSites d N,
        (massEigenvalues d N a mass j)⁻¹ *
          (∑ x, (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x * e_k x) *
          (∑ x, (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x * e_k x)) =
      (massEigenvalues d N a mass k)⁻¹ from by
    rw [Finset.sum_eq_single k]
    · rw [h_inner k, if_pos rfl]; ring
    · intro j _ hjk
      rw [h_inner j, if_neg hjk]; ring
    · intro h; exact (h (Finset.mem_univ _)).elim]
  ring

/-- **Each orthogonalized coordinate is standard Gaussian.**

Under `latticeGaussianMeasure d N a mass ha hmass`, the random variable
`ξ_k = gffOrthonormalCoord d N a mass ha hmass k` has distribution
`gaussianReal 0 1` (mean zero, variance one).

**Reference:** Janson §1.3.

**Proof:** Combine `pairing_is_gaussian` (the pushforward of `ω ↦ ω(e_k)`
is `gaussianReal 0 ⟨T(e_k), T(e_k)⟩.toNNReal`) with the variance helper
`latticeCovarianceGJ_eigenvector_inner_self` (which computes the variance
to be `(a^d λ_k)⁻¹`). The scaling by `√(a^d λ_k)` rescales the variance
to 1 via `gaussianReal_map_const_mul`. -/
theorem gffOrthonormalCoord_normal
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (k : FinLatticeSites d N) :
    Measure.map (gffOrthonormalCoord d N a mass ha hmass k)
      (latticeGaussianMeasure d N a mass ha hmass) =
    gaussianReal 0 1 := by
  -- Setup
  let e_k : FinLatticeField d N :=
    fun x => (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x
  let c : ℝ := Real.sqrt (a^d * massEigenvalues d N a mass k)
  have hev_pos : 0 < massEigenvalues d N a mass k :=
    massOperatorMatrix_eigenvalues_pos d N a mass ha hmass k
  have ha_d_pos : 0 < a^d := pow_pos ha d
  have h_prod_pos : 0 < a^d * massEigenvalues d N a mass k := mul_pos ha_d_pos hev_pos
  have hc_nn : 0 ≤ c := Real.sqrt_nonneg _
  have hc_sq : c^2 = a^d * massEigenvalues d N a mass k := by
    show (Real.sqrt (a^d * massEigenvalues d N a mass k))^2 = _
    rw [sq, Real.mul_self_sqrt h_prod_pos.le]
  -- Step 1: gffOrthonormalCoord k = (c * ·) ∘ (· e_k) (by commutativity)
  have h_fun_eq : (gffOrthonormalCoord d N a mass ha hmass k :
        Configuration (FinLatticeField d N) → ℝ) =
      (c * ·) ∘ (fun ω : Configuration (FinLatticeField d N) => ω e_k) := by
    funext ω
    show ω e_k * c = c * ω e_k
    ring
  -- Step 2: Measure.map composition
  have h_meas_mul : Measurable (fun x : ℝ => c * x) :=
    (continuous_const.mul continuous_id).measurable
  have h_meas_eval : Measurable (fun ω : Configuration (FinLatticeField d N) => ω e_k) :=
    configuration_eval_measurable e_k
  rw [h_fun_eq, ← Measure.map_map h_meas_mul h_meas_eval]
  -- Step 3: Apply pairing_is_gaussian
  unfold latticeGaussianMeasure
  rw [pairing_is_gaussian (latticeCovarianceGJ d N a mass ha hmass) e_k]
  -- Goal: Measure.map (c * ·) (gaussianReal 0 ⟨Te_k, Te_k⟩.toNNReal) = gaussianReal 0 1
  rw [latticeCovarianceGJ_eigenvector_inner_self d N a mass ha hmass k]
  -- Goal: Measure.map (c * ·) (gaussianReal 0 ((a^d λ_k)⁻¹).toNNReal) = gaussianReal 0 1
  rw [gaussianReal_map_const_mul]
  -- Goal: gaussianReal (c * 0) (⟨c², _⟩ * ((a^d λ_k)⁻¹).toNNReal) = gaussianReal 0 1
  congr 1
  · ring
  · -- ⟨c², _⟩ * (a^d λ_k)⁻¹.toNNReal = 1 in ℝ≥0
    apply NNReal.eq
    push_cast
    rw [hc_sq, Real.coe_toNNReal _ (inv_nonneg.mpr h_prod_pos.le)]
    rw [mul_inv_cancel₀ h_prod_pos.ne']

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
