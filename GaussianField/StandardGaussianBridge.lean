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
import GaussianField.IsGaussian
import Lattice.SpectralCovariance
import Lattice.Covariance
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
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

/-! ## Off-diagonal eigenvector covariance and the joint-Gaussianness CLM

The pieces needed to discharge `gffOrthonormalCoord_independent`:
* The off-diagonal companion of `latticeCovarianceGJ_eigenvector_inner_self`,
  giving `⟨T_GJ(e_i), T_GJ(e_j)⟩ = 0` for `i ≠ j` by orthonormality of
  the eigenvector basis.
* A continuous-linear bundling `gffOrthonormalProjCLM` of the projection
  `gffOrthonormalProj`, used to upgrade `IsGaussian (latticeGaussianMeasure)`
  to `IsGaussian (latticeGaussianMeasure.map gffOrthonormalProj)` via
  `isGaussian_map_of_measurable`. -/

/-- The GJ-covariance of two distinct eigenvectors is zero. -/
theorem latticeCovarianceGJ_eigenvector_inner_off
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (i j : FinLatticeSites d N) (hij : i ≠ j) :
    let e_i : FinLatticeField d N :=
      fun x => (massEigenvectorBasis d N a mass i : EuclideanSpace ℝ _) x
    let e_j : FinLatticeField d N :=
      fun x => (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x
    @inner ℝ ell2' _
        (latticeCovarianceGJ d N a mass ha hmass e_i)
        (latticeCovarianceGJ d N a mass ha hmass e_j) =
      0 := by
  intro e_i e_j
  show GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass) e_i e_j = 0
  rw [lattice_covariance_GJ_eq_spectral d N a mass ha hmass e_i e_j]
  -- Goal: (a^d)⁻¹ * Σ_k λ_k⁻¹ · c_k(e_i) · c_k(e_j) = 0
  -- where c_k(e_i) = δ_{ki}, c_k(e_j) = δ_{kj}; product is 0 since i ≠ j.
  have h_inner : ∀ k l : FinLatticeSites d N,
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
        (massEigenvectorBasis d N a mass l : EuclideanSpace ℝ _) x) =
      if k = l then (1 : ℝ) else 0 := by
    intro k l
    have h_orth :
        @inner ℝ (EuclideanSpace ℝ (FinLatticeSites d N)) _
          (massEigenvectorBasis d N a mass k)
          (massEigenvectorBasis d N a mass l) =
        if k = l then (1 : ℝ) else 0 :=
      orthonormal_iff_ite.mp (massEigenvectorBasis d N a mass).orthonormal k l
    have h_eq :
        (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
          (massEigenvectorBasis d N a mass l : EuclideanSpace ℝ _) x) =
        @inner ℝ (EuclideanSpace ℝ (FinLatticeSites d N)) _
          (massEigenvectorBasis d N a mass k)
          (massEigenvectorBasis d N a mass l) := by
      change _ =
        ((massEigenvectorBasis d N a mass l).ofLp ⬝ᵥ
          star (massEigenvectorBasis d N a mass k).ofLp)
      simp [dotProduct, star_trivial, mul_comm]
    rw [h_eq]; exact h_orth
  -- Each summand has factor c_k(e_i) · c_k(e_j) = δ_{ki} · δ_{kj}.
  -- Since i ≠ j, this is 0 for every k (k = i forces δ_{kj} = 0; k ≠ i forces δ_{ki} = 0).
  rw [show (∑ k : FinLatticeSites d N,
        (massEigenvalues d N a mass k)⁻¹ *
          (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * e_i x) *
          (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * e_j x)) =
      (0 : ℝ) from ?_]
  · ring
  apply Finset.sum_eq_zero
  intro k _
  rw [h_inner k i, h_inner k j]
  by_cases hki : k = i
  · -- k = i, so by i ≠ j, k ≠ j, second indicator is 0
    rw [if_neg (hki ▸ hij : k ≠ j)]; ring
  · rw [if_neg hki]; ring

/-- Evaluation of a configuration at a fixed test function, packaged as
a continuous linear map `Configuration E →L[ℝ] ℝ`. Continuity is
`WeakDual.eval_continuous`; linearity is the topological-dual pairing. -/
private noncomputable def gffEvalCLM (f : FinLatticeField d N) :
    Configuration (FinLatticeField d N) →L[ℝ] ℝ :=
  ⟨(topDualPairing ℝ (FinLatticeField d N)).flip f, WeakDual.eval_continuous f⟩

omit [NeZero N] in
@[simp] private lemma gffEvalCLM_apply (f : FinLatticeField d N)
    (ω : Configuration (FinLatticeField d N)) :
    gffEvalCLM d N f ω = ω f := rfl

/-- The orthogonalization map `ω ↦ (k ↦ ω(e_k) · √(a^d λ_k))` packaged
as a continuous linear map. Used to discharge joint Gaussianness in
`gffOrthonormalCoord_independent`. -/
private noncomputable def gffOrthonormalProjCLM
    (a mass : ℝ) (_ha : 0 < a) (_hmass : 0 < mass) :
    Configuration (FinLatticeField d N) →L[ℝ] (FinLatticeSites d N → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    Real.sqrt (a^d * massEigenvalues d N a mass k) •
      gffEvalCLM d N
        (fun x => (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x)

private lemma gffOrthonormalProjCLM_eq
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    ((gffOrthonormalProjCLM d N a mass ha hmass) :
        Configuration (FinLatticeField d N) → FinLatticeSites d N → ℝ) =
      gffOrthonormalProj d N a mass ha hmass := by
  funext ω k
  show Real.sqrt (a^d * massEigenvalues d N a mass k) *
      ω (fun x => (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) =
    ω (fun x => (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) *
      Real.sqrt (a^d * massEigenvalues d N a mass k)
  ring

private lemma gffOrthonormalProj_measurable
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measurable (gffOrthonormalProj d N a mass ha hmass) := by
  apply measurable_pi_iff.mpr
  intro k
  exact (configuration_eval_measurable _).mul_const _

/-- The lattice GFF (in GJ normalization) is Gaussian on `Configuration`
in Mathlib's sense. Bridges the `latticeGaussianMeasure` definition to
`GaussianField.measure_isGaussian`. -/
instance latticeGaussianMeasure_isGaussian
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    IsGaussian (latticeGaussianMeasure d N a mass ha hmass) :=
  GaussianField.measure_isGaussian _

private theorem gffOrthonormalProj_isGaussian
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    IsGaussian ((latticeGaussianMeasure d N a mass ha hmass).map
      (gffOrthonormalProj d N a mass ha hmass)) := by
  rw [show gffOrthonormalProj d N a mass ha hmass =
      ((gffOrthonormalProjCLM d N a mass ha hmass) :
        Configuration (FinLatticeField d N) → FinLatticeSites d N → ℝ) from
      (gffOrthonormalProjCLM_eq d N a mass ha hmass).symm]
  exact isGaussian_map_of_measurable
    ((gffOrthonormalProjCLM_eq d N a mass ha hmass).symm ▸
      gffOrthonormalProj_measurable d N a mass ha hmass)

/-- **Distinct orthogonalized coordinates are independent.**

Under `latticeGaussianMeasure`, the family `(ξ_k)_{k ∈ FinLatticeSites d N}`
is mutually independent. Combined with `gffOrthonormalCoord_normal`,
this means the family is i.i.d. standard Gaussian.

**Reference:** Janson §1.4 (uncorrelated jointly Gaussian variables
are independent).

**Proof:** Joint Gaussianness comes from packaging the orthogonalization
map as a CLM (`gffOrthonormalProjCLM`) and pushing forward the lattice
GFF (which is Gaussian on `Configuration` via `measure_isGaussian`).
Pairwise covariances vanish on the eigenbasis by orthonormality
(`latticeCovarianceGJ_eigenvector_inner_off`). Mathlib's
`HasGaussianLaw.iIndepFun_of_covariance_eq_zero` then closes the goal. -/
theorem gffOrthonormalCoord_independent
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    iIndepFun (fun k : FinLatticeSites d N =>
      gffOrthonormalCoord d N a mass ha hmass k)
      (latticeGaussianMeasure d N a mass ha hmass) := by
  set μ := latticeGaussianMeasure d N a mass ha hmass with hμ
  -- Joint Gaussianness of the coordinate family.
  haveI hGauss : IsGaussian (μ.map (gffOrthonormalProj d N a mass ha hmass)) :=
    gffOrthonormalProj_isGaussian d N a mass ha hmass
  have hX : HasGaussianLaw
      (fun ω : Configuration (FinLatticeField d N) =>
        fun k => gffOrthonormalCoord d N a mass ha hmass k ω) μ := ⟨hGauss⟩
  -- Pairwise covariances vanish for distinct indices.
  refine hX.iIndepFun_of_covariance_eq_zero ?_
  intro i j hij
  -- Notation
  set e_i : FinLatticeField d N :=
    fun x => (massEigenvectorBasis d N a mass i : EuclideanSpace ℝ _) x with he_i
  set e_j : FinLatticeField d N :=
    fun x => (massEigenvectorBasis d N a mass j : EuclideanSpace ℝ _) x with he_j
  set c_i : ℝ := Real.sqrt (a^d * massEigenvalues d N a mass i) with hc_i
  set c_j : ℝ := Real.sqrt (a^d * massEigenvalues d N a mass j) with hc_j
  -- Both eigenvector pairings are centered (mean zero) under μ.
  have h_centered_i : μ[fun ω : Configuration (FinLatticeField d N) => ω e_i] = 0 := by
    show ∫ ω : Configuration (FinLatticeField d N), ω e_i ∂μ = 0
    exact measure_centered (latticeCovarianceGJ d N a mass ha hmass) e_i
  have h_centered_j : μ[fun ω : Configuration (FinLatticeField d N) => ω e_j] = 0 := by
    show ∫ ω : Configuration (FinLatticeField d N), ω e_j ∂μ = 0
    exact measure_centered (latticeCovarianceGJ d N a mass ha hmass) e_j
  -- L² integrability of each pairing.
  have hLp_i : MemLp (fun ω : Configuration (FinLatticeField d N) => ω e_i) 2 μ := by
    exact_mod_cast pairing_memLp (latticeCovarianceGJ d N a mass ha hmass) e_i 2
  have hLp_j : MemLp (fun ω : Configuration (FinLatticeField d N) => ω e_j) 2 μ := by
    exact_mod_cast pairing_memLp (latticeCovarianceGJ d N a mass ha hmass) e_j 2
  -- ξ_i = (· e_i) * c_i, ξ_j = (· e_j) * c_j, so cov is c_i * c_j * cov of evaluations.
  have h_cov_eval :
      cov[fun ω : Configuration (FinLatticeField d N) => ω e_i,
          fun ω : Configuration (FinLatticeField d N) => ω e_j; μ] =
        ∫ ω, (ω e_i) * (ω e_j) ∂μ := by
    rw [covariance_eq_sub hLp_i hLp_j, h_centered_i, h_centered_j, mul_zero, sub_zero]
    rfl
  have h_cross :
      ∫ ω : Configuration (FinLatticeField d N), (ω e_i) * (ω e_j) ∂μ = 0 := by
    rw [show μ = GaussianField.measure (latticeCovarianceGJ d N a mass ha hmass) from rfl]
    rw [cross_moment_eq_covariance (latticeCovarianceGJ d N a mass ha hmass) e_i e_j]
    have := latticeCovarianceGJ_eigenvector_inner_off d N a mass ha hmass i j hij
    show GaussianField.covariance (latticeCovarianceGJ d N a mass ha hmass) e_i e_j = 0
    exact this
  -- Pull out the constants.
  have h_cov_zero :
      cov[fun ω : Configuration (FinLatticeField d N) => ω e_i,
          fun ω : Configuration (FinLatticeField d N) => ω e_j; μ] = 0 := by
    rw [h_cov_eval, h_cross]
  -- Combine with the c_i, c_j multiplications.
  show cov[fun ω => ω e_i * c_i, fun ω => ω e_j * c_j; μ] = 0
  rw [covariance_mul_const_left, covariance_mul_const_right, h_cov_zero,
    zero_mul, zero_mul]

/-- **The pushforward of the lattice GFF under orthogonalization is
the standard multivariate Gaussian.**

  `Measure.map gffOrthonormalProj (latticeGaussianMeasure …) = Π_k gaussianReal 0 1`

**Proof:** Each marginal is `N(0,1)` (`gffOrthonormalCoord_normal`)
and the family is mutually independent (`gffOrthonormalCoord_independent`).
Mathlib's `iIndepFun_iff_map_fun_eq_pi_map` then identifies the
joint pushforward with the product of marginals. -/
theorem gffOrthonormalProj_pushforward_eq_stdGaussian
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measure.map (gffOrthonormalProj d N a mass ha hmass)
      (latticeGaussianMeasure d N a mass ha hmass) =
    Measure.pi (fun _ : FinLatticeSites d N => gaussianReal 0 1) := by
  set μ := latticeGaussianMeasure d N a mass ha hmass with hμ
  have h_indep := gffOrthonormalCoord_independent d N a mass ha hmass
  have h_AE : ∀ i : FinLatticeSites d N,
      AEMeasurable (gffOrthonormalCoord d N a mass ha hmass i) μ := by
    intro i
    exact ((configuration_eval_measurable _).mul_const _).aemeasurable
  have h_eq :=
    (iIndepFun_iff_map_fun_eq_pi_map (μ := μ)
      (f := fun i => gffOrthonormalCoord d N a mass ha hmass i) h_AE).mp h_indep
  -- gffOrthonormalProj is `fun ω i ↦ gffOrthonormalCoord ... i ω` by definition.
  rw [show gffOrthonormalProj d N a mass ha hmass =
      fun ω i => gffOrthonormalCoord d N a mass ha hmass i ω from rfl, h_eq]
  congr 1
  funext i
  exact gffOrthonormalCoord_normal d N a mass ha hmass i

/-- **Characteristic-functional form of the bridge** (alternative formulation).

The pushforward measure has the characteristic functional
`exp(-(1/2) ‖t‖²)` where the norm is the standard Euclidean norm on
`FinLatticeSites d N → ℝ`. Equivalent to
`gffOrthonormalProj_pushforward_eq_stdGaussian` by uniqueness of the
characteristic functional, but useful as a target form when proving
via `MeasureTheory.Measure.ext_of_charFunDual` (the same uniqueness
tool used in `GaussianField/Density.lean`). -/
theorem gffOrthonormalProj_charFun
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (t : FinLatticeSites d N → ℝ) :
    ∫ x : FinLatticeSites d N → ℝ,
      Complex.exp (Complex.I * ↑(∑ k, t k * x k))
        ∂(Measure.map (gffOrthonormalProj d N a mass ha hmass)
          (latticeGaussianMeasure d N a mass ha hmass)) =
    Complex.exp (-(1 / 2 : ℂ) * ↑(∑ k, t k ^ 2)) := by
  rw [gffOrthonormalProj_pushforward_eq_stdGaussian d N a mass ha hmass]
  -- Decompose the exponential of the sum into a product of exponentials.
  have h_decomp : ∀ x : FinLatticeSites d N → ℝ,
      Complex.exp (Complex.I * ↑(∑ k, t k * x k)) =
        ∏ k, Complex.exp (Complex.I * ↑(t k * x k)) := by
    intro x
    rw [show (↑(∑ k, t k * x k) : ℂ) = ∑ k, ((t k * x k : ℝ) : ℂ) from by push_cast; rfl]
    rw [Finset.mul_sum, Complex.exp_sum]
  simp_rw [h_decomp]
  rw [show
      ∫ x : FinLatticeSites d N → ℝ, ∏ k, Complex.exp (Complex.I * ↑(t k * x k))
        ∂(Measure.pi fun _ : FinLatticeSites d N => gaussianReal 0 1) =
      ∏ k : FinLatticeSites d N,
        ∫ x : ℝ, Complex.exp (Complex.I * ↑(t k * x)) ∂(gaussianReal 0 1) from
    integral_fintype_prod_eq_prod
      (f := fun k (x : ℝ) => Complex.exp (Complex.I * ↑(t k * x)))]
  -- Each factor is the characteristic function of N(0,1) at t k.
  have h_each : ∀ k : FinLatticeSites d N,
      ∫ x : ℝ, Complex.exp (Complex.I * ↑(t k * x)) ∂(gaussianReal 0 1) =
        Complex.exp (-((t k : ℂ) ^ 2) / 2) := by
    intro k
    have h_rewrite : ∀ x : ℝ,
        Complex.exp (Complex.I * ↑(t k * x)) =
          Complex.exp (↑(t k) * ↑x * Complex.I) := by
      intro x
      push_cast
      ring_nf
    simp_rw [h_rewrite]
    rw [← charFun_apply_real, charFun_gaussianReal]
    push_cast
    ring_nf
  simp_rw [h_each]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k _
  ring

end GaussianField
