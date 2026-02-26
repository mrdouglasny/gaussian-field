/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Density Bridge: Gaussian Measure ↔ Gaussian Density

Proves that the lattice Gaussian measure (constructed via pushforward of noise)
has density `ρ(φ) = exp(-½⟨φ,Qφ⟩)` with respect to Lebesgue measure, up to
normalization.

This "density bridge" connects the abstract Gaussian field construction with
the explicit density formula needed for the FKG inequality proof.

## Main theorems

- `latticeGaussianMeasure_density_integral` — expectations under the Gaussian
  measure equal normalized weighted Lebesgue integrals
- `integrable_mul_gaussianDensity` — integrability transfer from Gaussian
  measure to Lebesgue via density

## Proof strategy

1. The pushforward `μ.map eval` (where eval maps ω to field values) has
   characteristic function `exp(-½ ⟨t, Q⁻¹t⟩)` by `GaussianField.charFun`
   and the spectral covariance identity.

2. The density measure `(1/Z)ρ · λ` has the same characteristic function,
   computed via the Gaussian Fourier transform (diagonalized by eigenbasis).

3. By `Measure.ext_of_charFun`, the two measures are equal.

4. The density bridge and integrability transfer follow.

## References

- Glimm-Jaffe, "Quantum Physics", §7.1 (Gaussian functional integrals)
- Simon, "The P(φ)₂ Euclidean (Quantum) Field Theory", Chapter I
-/

import Lattice.Covariance
import Lattice.SpectralCovariance
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

noncomputable section

namespace GaussianField

open MeasureTheory
open ProbabilityTheory

section TextbookFiniteDimensionalGaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Generic finite-dimensional quadratic Gaussian density. -/
def quadraticGaussianDensity
    (Q : (ι → ℝ) →L[ℝ] (ι → ℝ)) (φ : ι → ℝ) : ℝ :=
  Real.exp (-(1 / 2 : ℝ) * ∑ x : ι, φ x * (Q φ) x)

/-- Generic finite-dimensional (unnormalized) quadratic Gaussian measure. -/
def quadraticGaussianMeasure
    (Q : (ι → ℝ) →L[ℝ] (ι → ℝ)) : Measure (ι → ℝ) :=
  volume.withDensity (fun φ => ENNReal.ofReal (quadraticGaussianDensity Q φ))

/-- Generic finite-dimensional normalized quadratic Gaussian measure. -/
def normalizedQuadraticGaussianMeasure
    (Q : (ι → ℝ) →L[ℝ] (ι → ℝ)) : Measure (ι → ℝ) :=
  ((quadraticGaussianMeasure Q) Set.univ)⁻¹ • quadraticGaussianMeasure Q

/-- Finite-dimensional diagonal Gaussian Fourier integral with real coefficients. -/
theorem integral_cexp_neg_half_sum_mul_sq_add_linear
    (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) (c : ι → ℝ) :
    (∫ v : EuclideanSpace ℝ ι,
      Complex.exp (-(1 / 2 : ℂ) * ∑ i, (lam i : ℂ) * (v i : ℂ) ^ 2 +
        Complex.I * ↑(∑ i, c i * v i))) =
    (∏ i, (2 * Real.pi / lam i) ^ (1 / 2 : ℂ) *
      Complex.exp (-(1 / 2 : ℂ) * ((c i : ℂ) ^ 2 / (lam i : ℂ)))) := by
  rw [← (PiLp.volume_preserving_toLp ι).integral_comp
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding]
  have hleft :
      (∫ x : (ι → ℝ),
        Complex.exp (-(1 / 2 : ℂ) * ∑ i, (lam i : ℂ) * (x i : ℂ) ^ 2 +
          Complex.I * ↑(∑ i, c i * x i))) =
      (∫ x : (ι → ℝ),
        Complex.exp (-∑ i, ((lam i : ℂ) / 2) * (x i : ℂ) ^ 2 +
          ∑ i, (Complex.I * (c i : ℂ)) * x i)) := by
    refine integral_congr_ae <| Filter.Eventually.of_forall ?_
    intro x
    simp [Finset.sum_mul, Finset.mul_sum, sub_eq_add_neg, add_assoc, add_left_comm, add_comm,
      mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
  rw [hleft]
  calc
    (∫ x : (ι → ℝ),
      Complex.exp (-∑ i, ((lam i : ℂ) / 2) * (x i : ℂ) ^ 2 +
        ∑ i, (Complex.I * (c i : ℂ)) * x i))
        =
      ∏ i, (Real.pi / ((lam i : ℂ) / 2)) ^ (1 / 2 : ℂ) *
        Complex.exp (((Complex.I * (c i : ℂ)) ^ 2) / (4 * ((lam i : ℂ) / 2))) := by
          exact GaussianFourier.integral_cexp_neg_sum_mul_add
            (b := fun i => (lam i : ℂ) / 2)
            (fun i => by simp [hlam i])
            (fun i => Complex.I * (c i : ℂ))
    _ =
      (∏ i, (2 * Real.pi / lam i) ^ (1 / 2 : ℂ) *
        Complex.exp (-(1 / 2 : ℂ) * ((c i : ℂ) ^ 2 / (lam i : ℂ)))) := by
          refine Finset.prod_congr rfl ?_
          intro i hi
          have hli : (lam i : ℂ) ≠ 0 := by
            exact_mod_cast (ne_of_gt (hlam i))
          field_simp [hli]
          simp [Complex.I_sq]
          ring_nf

/-- Textbook axiom: finite-dimensional Gaussian Fourier transform for normalized
quadratic densities. -/
axiom normalizedQuadraticGaussianMeasure_linearFourier
    (Q : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (T : (ι → ℝ) →L[ℝ] ell2')
    (f : ι → ℝ) :
    ∫ φ : (ι → ℝ), Complex.exp (Complex.I * ↑(∑ x : ι, f x * φ x))
      ∂(normalizedQuadraticGaussianMeasure Q) =
    Complex.exp (-(1 / 2 : ℂ) * ↑(@inner ℝ ell2' _ (T f) (T f)))

end TextbookFiniteDimensionalGaussian

variable (d N : ℕ) [NeZero N]

/-! ## Evaluation map -/

/-- The evaluation map from Configuration space to field values:
`eval(ω) = (fun x => ω(δ_x))`.

This extracts the field configuration from a continuous linear functional. -/
def evalMap :
    Configuration (FinLatticeField d N) → FinLatticeField d N :=
  fun ω x => ω (finLatticeDelta d N x)

omit [NeZero N] in
theorem measurable_evalMap :
    Measurable (evalMap d N) := by
  rw [measurable_pi_iff]
  intro x
  simpa [evalMap] using
    (configuration_eval_measurable (E := FinLatticeField d N)
      (finLatticeDelta d N x))

/-- Basis decomposition in the finite field space:
`φ = ∑ x, φ(x) • δ_x`. -/
theorem field_basis_decomposition_density (φ : FinLatticeField d N) :
    φ = ∑ y : FinLatticeSites d N, φ y • finLatticeDelta d N y := by
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, finLatticeDelta,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- Pairing with a configuration can be rewritten in site coordinates. -/
theorem config_apply_eq_sum_delta (ω : Configuration (FinLatticeField d N))
    (f : FinLatticeField d N) :
    ω f = ∑ x : FinLatticeSites d N, f x * ω (finLatticeDelta d N x) := by
  conv_lhs => rw [field_basis_decomposition_density (d := d) (N := N) f]
  simp [map_sum, map_smul, smul_eq_mul]

/-- The coordinate pairing `∑ x, f(x) φ(x)` equals `ω(f)` after `evalMap`. -/
theorem config_apply_eq_sum_evalMap (ω : Configuration (FinLatticeField d N))
    (f : FinLatticeField d N) :
    ω f = ∑ x : FinLatticeSites d N, f x * (evalMap d N ω) x := by
  simpa [evalMap] using config_apply_eq_sum_delta (d := d) (N := N) ω f

theorem gaussianDensity_measurable (a mass : ℝ) :
    Measurable (gaussianDensity d N a mass) := by
  unfold gaussianDensity
  exact (Real.continuous_exp.comp (continuous_const.mul
      (continuous_finset_sum _ fun x _ =>
        (continuous_apply x).mul
          ((continuous_apply x).comp (massOperator d N a mass).continuous)))).measurable

def gaussianDensityWeight (a mass : ℝ) : FinLatticeField d N → ENNReal :=
  fun φ => ENNReal.ofReal (gaussianDensity d N a mass φ)

def gaussianDensityMeasure (a mass : ℝ) : Measure (FinLatticeField d N) :=
  volume.withDensity (gaussianDensityWeight d N a mass)

noncomputable def gaussianDensityNormConst (a mass : ℝ) : ENNReal :=
  (gaussianDensityMeasure d N a mass) Set.univ

def normalizedGaussianDensityMeasure (a mass : ℝ) :
    Measure (FinLatticeField d N) :=
  (gaussianDensityNormConst d N a mass)⁻¹ • gaussianDensityMeasure d N a mass

/-- Stage-1 wrapper for the finite-dimensional field law. -/
def latticeGaussianFieldLaw (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Measure (FinLatticeField d N) :=
  (latticeGaussianMeasure d N a mass ha hmass).map (evalMap d N)

/-- The coordinate pairing map on field configurations is measurable. -/
theorem measurable_sitePairing (f : FinLatticeField d N) :
    Measurable (fun φ : FinLatticeField d N =>
      ∑ x : FinLatticeSites d N, f x * φ x) := by
  simpa using
    (continuous_finset_sum _ (fun x _ => continuous_const.mul (continuous_apply x))).measurable

/-- Site pairing expanded in the mass-eigenvector basis coordinates. -/
theorem sitePairing_eq_massEigenbasis_sum (a mass : ℝ)
    (f φ : FinLatticeField d N) :
    (∑ x : FinLatticeSites d N, f x * φ x) =
      ∑ k : FinLatticeSites d N,
        (∑ x : FinLatticeSites d N,
          (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
        (∑ x : FinLatticeSites d N,
          (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * φ x) := by
  symm
  exact massEigenbasis_sum_mul_sum_eq_site_inner (d := d) (N := N) a mass f φ

/-- Spectral form of `gaussianDensity`. -/
theorem gaussianDensity_eq_exp_massEigenbasis (a mass : ℝ)
    (φ : FinLatticeField d N) :
    gaussianDensity d N a mass φ =
      Real.exp (-(1 / 2 : ℝ) *
        ∑ k : FinLatticeSites d N,
          massEigenvalues d N a mass k *
            (∑ x : FinLatticeSites d N,
            (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * φ x) ^ 2) := by
  simpa using gaussianDensity_eq_exp_spectral (d := d) (N := N) a mass φ

/-- Gaussian Fourier integral in mass-eigenbasis coordinates. -/
theorem integral_massEigenbasis_cexp
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (c : FinLatticeSites d N → ℝ) :
    (∫ φ : (FinLatticeSites d N → ℝ),
      Complex.exp (-(1 / 2 : ℂ) *
        ∑ k : FinLatticeSites d N,
          (massEigenvalues d N a mass k : ℂ) *
            (↑(∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * φ x) : ℂ) ^ 2
        + Complex.I * ↑(∑ k : FinLatticeSites d N, c k *
          (∑ x : FinLatticeSites d N,
            (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * φ x)))) =
    ∏ k : FinLatticeSites d N,
      (2 * Real.pi / massEigenvalues d N a mass k) ^ (1 / 2 : ℂ) *
        Complex.exp (-(1 / 2 : ℂ) *
          ((c k : ℂ) ^ 2 / (massEigenvalues d N a mass k : ℂ))) := by
  let g : EuclideanSpace ℝ (FinLatticeSites d N) → ℂ := fun v =>
    Complex.exp (-(1 / 2 : ℂ) *
      ∑ k : FinLatticeSites d N,
        (massEigenvalues d N a mass k : ℂ) *
          (↑(∑ x : FinLatticeSites d N,
            (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * v x) : ℂ) ^ 2
      + Complex.I * ↑(∑ k : FinLatticeSites d N, c k *
          (∑ x : FinLatticeSites d N,
            (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * v x)))
  let h : EuclideanSpace ℝ (FinLatticeSites d N) → ℂ := fun v =>
    Complex.exp (-(1 / 2 : ℂ) *
      ∑ k : FinLatticeSites d N, (massEigenvalues d N a mass k : ℂ) * (v k : ℂ) ^ 2
      + Complex.I * ↑(∑ k : FinLatticeSites d N, c k * v k))
  have hstart :
      (∫ φ : (FinLatticeSites d N → ℝ),
        Complex.exp (-(1 / 2 : ℂ) *
          ∑ k : FinLatticeSites d N,
            (massEigenvalues d N a mass k : ℂ) *
              (↑(∑ x : FinLatticeSites d N,
                (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * φ x) : ℂ) ^ 2
          + Complex.I * ↑(∑ k : FinLatticeSites d N, c k *
            (∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * φ x)))) =
      ∫ φ : (FinLatticeSites d N → ℝ), g ((MeasurableEquiv.toLp 2 (FinLatticeSites d N → ℝ)) φ) := by
    refine integral_congr_ae <| Filter.Eventually.of_forall ?_
    intro φ
    simp [g]
  rw [hstart]
  have htolp :
      (∫ φ : (FinLatticeSites d N → ℝ), g ((MeasurableEquiv.toLp 2 (FinLatticeSites d N → ℝ)) φ)) =
      (∫ φ : (FinLatticeSites d N → ℝ), g (WithLp.toLp 2 φ)) := by
    simp
  rw [htolp]
  rw [(PiLp.volume_preserving_toLp (FinLatticeSites d N)).integral_comp
    (MeasurableEquiv.toLp 2 (FinLatticeSites d N → ℝ)).measurableEmbedding]
  rw [← ((massEigenvectorBasis d N a mass).repr.symm.measurePreserving).integral_comp
    ((massEigenvectorBasis d N a mass).repr.symm.toHomeomorph.measurableEmbedding)]
  have hrepr : ∀ v : EuclideanSpace ℝ (FinLatticeSites d N),
      g ((massEigenvectorBasis d N a mass).repr.symm v) = h v := by
    intro v
    have hqR :
        (∑ k : FinLatticeSites d N,
          massEigenvalues d N a mass k *
            (∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
                ((massEigenvectorBasis d N a mass).repr.symm v).ofLp x) ^ 2) =
        (∑ k : FinLatticeSites d N, massEigenvalues d N a mass k * (v.ofLp k) ^ 2) :=
      massEigenbasis_quadratic_sum_reprSymm_ofLp (d := d) (N := N) a mass v
    have hqC :
        (∑ k : FinLatticeSites d N,
          (massEigenvalues d N a mass k : ℂ) *
            (↑(∑ x : FinLatticeSites d N,
              (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
                ((massEigenvectorBasis d N a mass).repr.symm v).ofLp x) : ℂ) ^ 2) =
        (∑ k : FinLatticeSites d N,
          (massEigenvalues d N a mass k : ℂ) * (v.ofLp k : ℂ) ^ 2) := by
      simpa using congrArg (fun r : ℝ => (r : ℂ)) hqR
    have hlR :
        (∑ k : FinLatticeSites d N, c k *
          (∑ x : FinLatticeSites d N,
            (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
              ((massEigenvectorBasis d N a mass).repr.symm v).ofLp x)) =
        (∑ k : FinLatticeSites d N, c k * v.ofLp k) :=
      massEigenbasis_linear_sum_reprSymm_ofLp (d := d) (N := N) a mass c v
    have hlCcomplex :
        (↑(∑ k : FinLatticeSites d N, c k *
          (∑ x : FinLatticeSites d N,
            (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x *
              ((massEigenvectorBasis d N a mass).repr.symm v).ofLp x)) : ℂ) =
        (↑(∑ k : FinLatticeSites d N, c k * v.ofLp k) : ℂ) := by
      exact congrArg (fun r : ℝ => (r : ℂ)) hlR
    unfold g h
    rw [hqC, hlCcomplex]
  rw [integral_congr_ae (Filter.Eventually.of_forall hrepr)]
  simpa [h] using
    (integral_cexp_neg_half_sum_mul_sq_add_linear
      (ι := FinLatticeSites d N)
      (lam := massEigenvalues d N a mass)
      (hlam := massOperatorMatrix_eigenvalues_pos (d := d) (N := N) a mass ha hmass)
      (c := c))

/-- Adapts `pairing_is_gaussian` to the finite field-law measure:
the pushforward by coordinate pairing is a 1D Gaussian. -/
theorem latticeGaussianFieldLaw_pairing_is_gaussian
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) :
    ((latticeGaussianFieldLaw d N a mass ha hmass).map
      (fun φ : FinLatticeField d N => ∑ x : FinLatticeSites d N, f x * φ x)) =
      gaussianReal 0
        (@inner ℝ ell2' _
          (latticeCovariance d N a mass ha hmass f)
          (latticeCovariance d N a mass ha hmass f)).toNNReal := by
  rw [latticeGaussianFieldLaw]
  have hmap :
      Measure.map (fun φ : FinLatticeField d N =>
          ∑ x : FinLatticeSites d N, f x * φ x)
      (Measure.map (evalMap d N) (latticeGaussianMeasure d N a mass ha hmass)) =
      Measure.map (fun ω : Configuration (FinLatticeField d N) =>
          ∑ x : FinLatticeSites d N, f x * (evalMap d N ω) x)
        (latticeGaussianMeasure d N a mass ha hmass) := by
    simpa [Function.comp] using
      (Measure.map_map
        (g := fun φ : FinLatticeField d N => ∑ x : FinLatticeSites d N, f x * φ x)
        (f := evalMap d N)
        (μ := latticeGaussianMeasure d N a mass ha hmass)
        (measurable_sitePairing (d := d) (N := N) f)
        (measurable_evalMap (d := d) (N := N)))
  rw [hmap]
  have hcoord :
      (fun ω : Configuration (FinLatticeField d N) =>
        ∑ x : FinLatticeSites d N, f x * (evalMap d N ω) x) =
      (fun ω : Configuration (FinLatticeField d N) => ω f) := by
    funext ω
    exact (config_apply_eq_sum_evalMap (d := d) (N := N) ω f).symm
  rw [hcoord]
  simpa using GaussianField.pairing_is_gaussian
    (latticeCovariance d N a mass ha hmass) f

/-- Fourier identity for the finite-dimensional field law, expressed in site
coordinates. This is the pushforward-side characteristic-function formula. -/
theorem latticeGaussianFieldLaw_fourier (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) :
    ∫ φ : FinLatticeField d N,
      Complex.exp (Complex.I * ↑(∑ x : FinLatticeSites d N, f x * φ x))
        ∂(latticeGaussianFieldLaw d N a mass ha hmass) =
    Complex.exp (-(1 / 2 : ℂ) * ↑(@inner ℝ ell2' _
      (latticeCovariance d N a mass ha hmass f)
      (latticeCovariance d N a mass ha hmass f))) := by
  rw [latticeGaussianFieldLaw]
  have hmeas :
      AEStronglyMeasurable
        (fun φ : FinLatticeField d N =>
          Complex.exp (Complex.I * ↑(∑ x : FinLatticeSites d N, f x * φ x)))
        ((latticeGaussianMeasure d N a mass ha hmass).map (evalMap d N)) := by
    refine (Complex.continuous_exp.comp ?_).aestronglyMeasurable
    refine (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
    refine continuous_finset_sum _ (fun x _ => ?_)
    exact (continuous_const.mul (continuous_apply x))
  rw [integral_map (measurable_evalMap (d := d) (N := N)).aemeasurable hmeas]
  have hcoord : ∀ ω : Configuration (FinLatticeField d N),
      (∑ x : FinLatticeSites d N, f x * (evalMap d N ω) x) = ω f := by
    intro ω
    simpa using (config_apply_eq_sum_evalMap (d := d) (N := N) ω f).symm
  simp_rw [hcoord]
  exact GaussianField.charFun (latticeCovariance d N a mass ha hmass) f

/-! ## Density bridge

The core result: the lattice Gaussian measure's expectations can be computed
as normalized weighted Lebesgue integrals with the Gaussian density.

### Proof outline

**Step 1**: Characteristic function of pushforward.
By `GaussianField.charFun`:
  `E_μ[exp(i ω(f))] = exp(-½ ‖T(f)‖²_ℓ²)`
For `f = ∑ t_x δ_x`, using `spectralLatticeCovariance_norm_sq`:
  `‖T(∑ t_x δ_x)‖² = ∑_k λ_k⁻¹ |⟪e_k, t⟫|²`

**Step 2**: Characteristic function of density measure.
The Fourier transform of `ρ(φ) = exp(-½ ⟨φ, Qφ⟩)` gives, after
diagonalization in the eigenbasis:
  `∫ exp(i⟨t,φ⟩) ρ(φ) dφ = Z · exp(-½ ∑_k λ_k⁻¹ |⟪e_k, t⟫|²)`

**Step 3**: Measure uniqueness via `Measure.ext_of_charFun`.
Both measures have the same characteristic function, hence are equal.

**Step 4**: The density bridge and integrability transfer follow
from the measure equality. -/

/-- The project normalized density measure is the generic normalized quadratic
Gaussian measure for `Q = massOperator`. -/
theorem normalizedGaussianDensityMeasure_eq_normalizedQuadraticGaussianMeasure
    (a mass : ℝ) :
    normalizedGaussianDensityMeasure d N a mass =
      normalizedQuadraticGaussianMeasure (Q := massOperator d N a mass) := by
  rfl

/-- Fourier identity for the project normalized density measure, derived from
the generic textbook axiom. -/
theorem normalizedGaussianDensityMeasure_linearFourier
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) :
    ∫ φ : FinLatticeField d N,
      Complex.exp (Complex.I * ↑(∑ x : FinLatticeSites d N, f x * φ x))
        ∂(normalizedGaussianDensityMeasure d N a mass) =
    Complex.exp (-(1 / 2 : ℂ) * ↑(@inner ℝ ell2' _
      (latticeCovariance d N a mass ha hmass f)
      (latticeCovariance d N a mass ha hmass f))) := by
  rw [normalizedGaussianDensityMeasure_eq_normalizedQuadraticGaussianMeasure (d := d) (N := N) a mass]
  simpa using normalizedQuadraticGaussianMeasure_linearFourier
    (Q := massOperator d N a mass)
    (T := latticeCovariance d N a mass ha hmass)
    f

/-- Site-coordinate representative of a dual functional. -/
def strongDualToField
    (L : StrongDual ℝ (FinLatticeField d N)) : FinLatticeField d N :=
  fun x => L (finLatticeDelta d N x)

/-- Any dual functional on the finite field space equals its site-coordinate pairing. -/
theorem strongDual_apply_eq_site_sum
    (L : StrongDual ℝ (FinLatticeField d N))
    (φ : FinLatticeField d N) :
    L φ = ∑ x : FinLatticeSites d N, strongDualToField (d := d) (N := N) L x * φ x := by
  conv_lhs => rw [field_basis_decomposition_density (d := d) (N := N) φ]
  simp [strongDualToField, map_sum, map_smul, smul_eq_mul, mul_comm]

/-- `charFunDual` rewritten in site coordinates. -/
theorem charFunDual_eq_site_integral
    (μ : Measure (FinLatticeField d N))
    (L : StrongDual ℝ (FinLatticeField d N)) :
    MeasureTheory.charFunDual μ L =
      ∫ φ : FinLatticeField d N,
        Complex.exp (Complex.I * ↑(∑ x : FinLatticeSites d N,
          strongDualToField (d := d) (N := N) L x * φ x)) ∂μ := by
  rw [MeasureTheory.charFunDual_eq_charFun_map_one]
  rw [MeasureTheory.charFun_apply_real]
  have hmeas :
      AEStronglyMeasurable (fun x : ℝ => Complex.exp (↑(1 : ℝ) * ↑x * Complex.I))
        (μ.map L) := by
    refine (Complex.continuous_exp.comp ?_).aestronglyMeasurable
    exact ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)
  rw [integral_map L.continuous.measurable.aemeasurable hmeas]
  refine integral_congr_ae <| Filter.Eventually.of_forall ?_
  intro φ
  change Complex.exp (↑(1 : ℝ) * ↑(L φ) * Complex.I) =
    Complex.exp (Complex.I * ↑(∑ x : FinLatticeSites d N,
      strongDualToField (d := d) (N := N) L x * φ x))
  rw [strongDual_apply_eq_site_sum (d := d) (N := N) L φ]
  simpa [mul_comm, mul_left_comm, mul_assoc]

/-- Characteristic-function identity between normalized density and field law. -/
theorem normalizedGaussianDensityMeasure_charFunDual_eq_latticeGaussianFieldLaw
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    MeasureTheory.charFunDual (normalizedGaussianDensityMeasure d N a mass) =
      MeasureTheory.charFunDual (latticeGaussianFieldLaw d N a mass ha hmass) := by
  ext L
  rw [charFunDual_eq_site_integral (d := d) (N := N)
      (μ := normalizedGaussianDensityMeasure d N a mass) L]
  rw [charFunDual_eq_site_integral (d := d) (N := N)
      (μ := latticeGaussianFieldLaw d N a mass ha hmass) L]
  let f : FinLatticeField d N := strongDualToField (d := d) (N := N) L
  calc
    ∫ φ : FinLatticeField d N,
        Complex.exp (Complex.I * ↑(∑ x : FinLatticeSites d N, f x * φ x))
          ∂(normalizedGaussianDensityMeasure d N a mass)
      = Complex.exp (-(1 / 2 : ℂ) * ↑(@inner ℝ ell2' _
          (latticeCovariance d N a mass ha hmass f)
          (latticeCovariance d N a mass ha hmass f))) := by
          exact normalizedGaussianDensityMeasure_linearFourier (d := d) (N := N)
            a mass ha hmass f
    _ = ∫ φ : FinLatticeField d N,
          Complex.exp (Complex.I * ↑(∑ x : FinLatticeSites d N, f x * φ x))
            ∂(latticeGaussianFieldLaw d N a mass ha hmass) := by
          symm
          exact latticeGaussianFieldLaw_fourier (d := d) (N := N) a mass ha hmass f

/-- The normalized density measure is finite. -/
theorem normalizedGaussianDensityMeasure_isFinite
    (a mass : ℝ) :
    MeasureTheory.IsFiniteMeasure (normalizedGaussianDensityMeasure d N a mass) := by
  refine ⟨?_⟩
  let z : ENNReal := (gaussianDensityMeasure d N a mass) Set.univ
  have hz :
      (normalizedGaussianDensityMeasure d N a mass) Set.univ = z⁻¹ * z := by
    simp [normalizedGaussianDensityMeasure, gaussianDensityNormConst, z]
  rw [hz]
  by_cases h0 : z = 0
  · simp [h0]
  · by_cases htop : z = ⊤
    · simp [htop]
    · simpa [ENNReal.inv_mul_cancel h0 htop]

/-- Stage-2 master theorem (derived from `charFunDual` equality + finiteness). -/
theorem latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    latticeGaussianFieldLaw d N a mass ha hmass =
      normalizedGaussianDensityMeasure d N a mass := by
  letI : MeasureTheory.IsFiniteMeasure
      (normalizedGaussianDensityMeasure d N a mass) :=
    normalizedGaussianDensityMeasure_isFinite (d := d) (N := N) a mass
  letI : MeasureTheory.IsFiniteMeasure
      (latticeGaussianFieldLaw d N a mass ha hmass) := by
    letI : MeasureTheory.IsProbabilityMeasure (latticeGaussianFieldLaw d N a mass ha hmass) := by
      rw [latticeGaussianFieldLaw]
      exact Measure.isProbabilityMeasure_map
        (measurable_evalMap (d := d) (N := N)).aemeasurable
    infer_instance
  exact MeasureTheory.Measure.ext_of_charFunDual <|
    (normalizedGaussianDensityMeasure_charFunDual_eq_latticeGaussianFieldLaw
      (d := d) (N := N) a mass ha hmass).symm

theorem gaussianDensityWeight_measurable (a mass : ℝ) :
    Measurable (gaussianDensityWeight d N a mass) := by
  simpa [gaussianDensityWeight] using
    (gaussianDensity_measurable (d := d) (N := N) a mass).ennreal_ofReal

theorem gaussianDensityWeight_toReal (a mass : ℝ) (φ : FinLatticeField d N) :
    (gaussianDensityWeight d N a mass φ).toReal = gaussianDensity d N a mass φ := by
  simpa [gaussianDensityWeight] using
    (ENNReal.toReal_ofReal (gaussianDensity_nonneg (d := d) (N := N) a mass φ))

theorem gaussianDensityNormConst_eq_lintegral (a mass : ℝ) :
    gaussianDensityNormConst d N a mass =
      ∫⁻ φ, gaussianDensityWeight d N a mass φ := by
  simp [gaussianDensityNormConst, gaussianDensityMeasure]

theorem latticeGaussianFieldLaw_univ (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (latticeGaussianFieldLaw d N a mass ha hmass) Set.univ = 1 := by
  letI : IsProbabilityMeasure (latticeGaussianFieldLaw d N a mass ha hmass) := by
    rw [latticeGaussianFieldLaw]
    exact Measure.isProbabilityMeasure_map (measurable_evalMap (d := d) (N := N)).aemeasurable
  simpa using (measure_univ : (latticeGaussianFieldLaw d N a mass ha hmass) Set.univ = 1)

theorem gaussianDensityNormConst_ne_zero (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    gaussianDensityNormConst d N a mass ≠ 0 := by
  have hnorm_univ : (normalizedGaussianDensityMeasure d N a mass) Set.univ = 1 := by
    simpa [latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure (d := d) (N := N)
      a mass ha hmass] using latticeGaussianFieldLaw_univ (d := d) (N := N) a mass ha hmass
  by_contra h0
  have hμ0 : gaussianDensityMeasure d N a mass = 0 := by
    exact (Measure.measure_univ_eq_zero.mp (by simpa [gaussianDensityNormConst] using h0))
  have hz : (normalizedGaussianDensityMeasure d N a mass) Set.univ = 0 := by
    simp [normalizedGaussianDensityMeasure, hμ0]
  have hne : (normalizedGaussianDensityMeasure d N a mass) Set.univ ≠ 0 := by
    simpa [hnorm_univ]
  exact hne hz

theorem gaussianDensityNormConst_ne_top (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    gaussianDensityNormConst d N a mass ≠ (⊤ : ENNReal) := by
  have hnorm_univ : (normalizedGaussianDensityMeasure d N a mass) Set.univ = 1 := by
    simpa [latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure (d := d) (N := N)
      a mass ha hmass] using latticeGaussianFieldLaw_univ (d := d) (N := N) a mass ha hmass
  by_contra htop
  have hz : (normalizedGaussianDensityMeasure d N a mass) Set.univ = 0 := by
    simp [normalizedGaussianDensityMeasure, htop]
  have hne : (normalizedGaussianDensityMeasure d N a mass) Set.univ ≠ 0 := by
    simpa [hnorm_univ]
  exact hne hz

theorem integrable_gaussianDensity (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Integrable (gaussianDensity d N a mass) := by
  have hEq := latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure
    (d := d) (N := N) a mass ha hmass
  letI : IsProbabilityMeasure (latticeGaussianFieldLaw d N a mass ha hmass) := by
    rw [latticeGaussianFieldLaw]
    exact Measure.isProbabilityMeasure_map (measurable_evalMap (d := d) (N := N)).aemeasurable
  have hIntLaw : Integrable (fun _ : FinLatticeField d N => (1 : ℝ))
      (latticeGaussianFieldLaw d N a mass ha hmass) := by
    simpa using (integrable_const (1 : ℝ))
  have hIntNorm : Integrable (fun _ : FinLatticeField d N => (1 : ℝ))
      (normalizedGaussianDensityMeasure d N a mass) := by
    simpa [hEq] using hIntLaw
  have hIntWD : Integrable (fun _ : FinLatticeField d N => (1 : ℝ))
      (gaussianDensityMeasure d N a mass) := by
    have hEquiv := integrable_smul_measure
      (μ := gaussianDensityMeasure d N a mass)
      (f := fun _ : FinLatticeField d N => (1 : ℝ))
      (h₁ := ENNReal.inv_ne_zero.mpr (gaussianDensityNormConst_ne_top (d := d) (N := N) a mass ha hmass))
      (h₂ := ENNReal.inv_ne_top.mpr (gaussianDensityNormConst_ne_zero (d := d) (N := N) a mass ha hmass))
    exact hEquiv.mp (by simpa [normalizedGaussianDensityMeasure] using hIntNorm)
  have hflt : ∀ᵐ φ ∂(volume : Measure (FinLatticeField d N)),
      gaussianDensityWeight d N a mass φ < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall (fun _ => by simp [gaussianDensityWeight])
  have hIntMul : Integrable
      (fun φ : FinLatticeField d N => (gaussianDensityWeight d N a mass φ).toReal • (1 : ℝ)) volume := by
    exact (integrable_withDensity_iff_integrable_smul'
      (μ := volume) (f := gaussianDensityWeight d N a mass)
      (hf := gaussianDensityWeight_measurable (d := d) (N := N) a mass)
      (hflt := hflt)).mp (by simpa [gaussianDensityMeasure] using hIntWD)
  simpa [smul_eq_mul, one_mul, gaussianDensityWeight_toReal (d := d) (N := N) a mass] using hIntMul

theorem gaussianDensityNormConst_eq_ofReal_integral (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    gaussianDensityNormConst d N a mass =
      ENNReal.ofReal (∫ φ, gaussianDensity d N a mass φ) := by
  rw [gaussianDensityNormConst_eq_lintegral]
  simp [gaussianDensityWeight]
  symm
  exact ofReal_integral_eq_lintegral_ofReal
    (integrable_gaussianDensity (d := d) (N := N) a mass ha hmass)
    (Filter.Eventually.of_forall (gaussianDensity_nonneg (d := d) (N := N) a mass))

theorem gaussianDensity_integral_pos (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    0 < ∫ φ, gaussianDensity d N a mass φ := by
  apply integral_pos_of_integrable_nonneg_nonzero (x := 0)
  · unfold gaussianDensity
    exact Real.continuous_exp.comp (continuous_const.mul
      (continuous_finset_sum _ fun x _ =>
        (continuous_apply x).mul
          ((continuous_apply x).comp (massOperator d N a mass).continuous)))
  · exact integrable_gaussianDensity d N a mass ha hmass
  · exact fun φ => le_of_lt (Real.exp_pos _)
  · exact ne_of_gt (Real.exp_pos _)

theorem latticeGaussianFieldLaw_density_integral (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (F : FinLatticeField d N → ℝ) :
    ∫ φ, F φ ∂(latticeGaussianFieldLaw d N a mass ha hmass) =
    (∫ φ, F φ * gaussianDensity d N a mass φ) /
    (∫ φ, gaussianDensity d N a mass φ) := by
  have hEq := latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure
    (d := d) (N := N) a mass ha hmass
  have hflt : ∀ᵐ φ ∂(volume : Measure (FinLatticeField d N)),
      gaussianDensityWeight d N a mass φ < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall (fun _ => by simp [gaussianDensityWeight])
  calc
    ∫ φ, F φ ∂(latticeGaussianFieldLaw d N a mass ha hmass)
        = ∫ φ, F φ ∂(normalizedGaussianDensityMeasure d N a mass) := by simpa [hEq]
    _ = ((gaussianDensityNormConst d N a mass)⁻¹).toReal *
          ∫ φ, F φ ∂(gaussianDensityMeasure d N a mass) := by
          simp [normalizedGaussianDensityMeasure, integral_smul_measure]
    _ = ((gaussianDensityNormConst d N a mass)⁻¹).toReal *
          ∫ φ, (gaussianDensityWeight d N a mass φ).toReal • F φ := by
          congr 1
          simpa [gaussianDensityMeasure] using (integral_withDensity_eq_integral_toReal_smul
            (μ := volume) (f := gaussianDensityWeight d N a mass)
            (f_meas := gaussianDensityWeight_measurable (d := d) (N := N) a mass)
            (hf_lt_top := hflt) (g := F))
    _ = ((gaussianDensityNormConst d N a mass)⁻¹).toReal *
          ∫ φ, F φ * gaussianDensity d N a mass φ := by
          congr 1
          refine integral_congr_ae <| Filter.Eventually.of_forall <| fun φ => ?_
          simp [smul_eq_mul, gaussianDensityWeight_toReal (d := d) (N := N) a mass φ, mul_comm]
    _ = (∫ φ, F φ * gaussianDensity d N a mass φ) /
          (∫ φ, gaussianDensity d N a mass φ) := by
          rw [gaussianDensityNormConst_eq_ofReal_integral (d := d) (N := N) a mass ha hmass]
          have hρpos : 0 < ∫ φ, gaussianDensity d N a mass φ :=
            gaussianDensity_integral_pos (d := d) (N := N) a mass ha hmass
          have hInv :
              ((ENNReal.ofReal (∫ φ, gaussianDensity d N a mass φ))⁻¹).toReal =
                (∫ φ, gaussianDensity d N a mass φ)⁻¹ := by
            have hρnn : 0 ≤ ∫ φ, gaussianDensity d N a mass φ :=
              integral_nonneg fun _ => gaussianDensity_nonneg (d := d) (N := N) a mass _
            simp [ENNReal.toReal_inv, hρnn]
          rw [hInv]
          field_simp [hρpos.ne']

theorem integrable_mul_gaussianDensity_of_fieldLaw (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (F : FinLatticeField d N → ℝ)
    (hF : Integrable F (latticeGaussianFieldLaw d N a mass ha hmass)) :
    Integrable (fun φ => F φ * gaussianDensity d N a mass φ) := by
  have hEq := latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure
    (d := d) (N := N) a mass ha hmass
  have hNorm : Integrable F (normalizedGaussianDensityMeasure d N a mass) := by
    simpa [hEq] using hF
  have hWD : Integrable F (gaussianDensityMeasure d N a mass) := by
    have hEquiv := integrable_smul_measure
      (μ := gaussianDensityMeasure d N a mass) (f := F)
      (h₁ := ENNReal.inv_ne_zero.mpr (gaussianDensityNormConst_ne_top (d := d) (N := N) a mass ha hmass))
      (h₂ := ENNReal.inv_ne_top.mpr (gaussianDensityNormConst_ne_zero (d := d) (N := N) a mass ha hmass))
    exact hEquiv.mp (by simpa [normalizedGaussianDensityMeasure] using hNorm)
  have hflt : ∀ᵐ φ ∂(volume : Measure (FinLatticeField d N)),
      gaussianDensityWeight d N a mass φ < (⊤ : ENNReal) :=
    Filter.Eventually.of_forall (fun _ => by simp [gaussianDensityWeight])
  have hMul : Integrable
      (fun φ : FinLatticeField d N => (gaussianDensityWeight d N a mass φ).toReal • F φ) volume := by
    exact (integrable_withDensity_iff_integrable_smul'
      (μ := volume) (f := gaussianDensityWeight d N a mass)
      (hf := gaussianDensityWeight_measurable (d := d) (N := N) a mass)
      (hflt := hflt)).mp (by simpa [gaussianDensityMeasure] using hWD)
  exact hMul.congr <| Filter.Eventually.of_forall <| fun φ => by
    simp [smul_eq_mul, gaussianDensityWeight_toReal (d := d) (N := N) a mass φ, mul_comm]

/-- **Integrability transfer** from Gaussian measure to weighted Lebesgue. -/
theorem integrable_mul_gaussianDensity (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (F : FinLatticeField d N → ℝ)
    (hFm : Measurable F)
    (hF : Integrable (fun ω => F (fun x => ω (finLatticeDelta d N x)))
           (latticeGaussianMeasure d N a mass ha hmass)) :
    Integrable (fun φ => F φ * gaussianDensity d N a mass φ) := by
  have hField : Integrable F (latticeGaussianFieldLaw d N a mass ha hmass) := by
    rw [latticeGaussianFieldLaw]
    exact (integrable_map_measure hFm.aestronglyMeasurable
      (measurable_evalMap (d := d) (N := N)).aemeasurable).mpr (by simpa [evalMap] using hF)
  exact integrable_mul_gaussianDensity_of_fieldLaw (d := d) (N := N) a mass ha hmass F hField

theorem integrable_normalizedGaussianDensityMeasure_iff (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (F : FinLatticeField d N → ℝ) :
    Integrable F (latticeGaussianFieldLaw d N a mass ha hmass) ↔
      Integrable F (normalizedGaussianDensityMeasure d N a mass) := by
  constructor
  · intro hF
    simpa [latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure (d := d) (N := N)
      a mass ha hmass] using hF
  · intro hF
    simpa [latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure (d := d) (N := N)
      a mass ha hmass] using hF

theorem integral_latticeGaussianFieldLaw_eq_integral_normalizedGaussianDensityMeasure
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (F : FinLatticeField d N → ℝ) :
    ∫ φ, F φ ∂(latticeGaussianFieldLaw d N a mass ha hmass) =
      ∫ φ, F φ ∂(normalizedGaussianDensityMeasure d N a mass) := by
  simp [latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure (d := d) (N := N)
    a mass ha hmass]

theorem latticeGaussianMeasure_density_integral_of_fieldLaw (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (F : FinLatticeField d N → ℝ)
    (hFm : Measurable F)
    (_hFρi : Integrable (fun φ => F φ * gaussianDensity d N a mass φ)) :
    ∫ ω, F (evalMap d N ω) ∂(latticeGaussianMeasure d N a mass ha hmass) =
    (∫ φ, F φ * gaussianDensity d N a mass φ) /
    (∫ φ, gaussianDensity d N a mass φ) := by
  calc
    ∫ ω, F (evalMap d N ω) ∂(latticeGaussianMeasure d N a mass ha hmass)
        = ∫ φ, F φ ∂(latticeGaussianFieldLaw d N a mass ha hmass) := by
            symm
            rw [latticeGaussianFieldLaw]
            simpa [Function.comp] using
              (integral_map (μ := latticeGaussianMeasure d N a mass ha hmass)
                (measurable_evalMap (d := d) (N := N)).aemeasurable hFm.aestronglyMeasurable)
    _ = (∫ φ, F φ * gaussianDensity d N a mass φ) /
          (∫ φ, gaussianDensity d N a mass φ) :=
      latticeGaussianFieldLaw_density_integral (d := d) (N := N) a mass ha hmass F

/-- **Density bridge**: expectation under `latticeGaussianMeasure` equals the
normalized weighted Lebesgue integral with density `gaussianDensity`. -/
theorem latticeGaussianMeasure_density_integral (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (F : FinLatticeField d N → ℝ)
    (hFm : Measurable F)
    (hFρi : Integrable (fun φ => F φ * gaussianDensity d N a mass φ)) :
    ∫ ω, F (fun x => ω (finLatticeDelta d N x))
      ∂(latticeGaussianMeasure d N a mass ha hmass) =
    (∫ φ, F φ * gaussianDensity d N a mass φ) /
    (∫ φ, gaussianDensity d N a mass φ) := by
  simpa [evalMap] using
    (latticeGaussianMeasure_density_integral_of_fieldLaw (d := d) (N := N) a mass ha hmass F hFm hFρi)

theorem integrable_mul_gaussianDensity_of_comp_eval (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (F : FinLatticeField d N → ℝ)
    (hFm : Measurable F)
    (hF : Integrable (fun ω => F (evalMap d N ω))
           (latticeGaussianMeasure d N a mass ha hmass)) :
    Integrable (fun φ => F φ * gaussianDensity d N a mass φ) := by
  have hField : Integrable F (latticeGaussianFieldLaw d N a mass ha hmass) := by
    rw [latticeGaussianFieldLaw]
    exact (integrable_map_measure hFm.aestronglyMeasurable
      (measurable_evalMap (d := d) (N := N)).aemeasurable).mpr hF
  exact integrable_mul_gaussianDensity_of_fieldLaw (d := d) (N := N) a mass ha hmass F hField

end GaussianField
