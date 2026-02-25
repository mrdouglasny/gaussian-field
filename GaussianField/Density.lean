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

noncomputable section

namespace GaussianField

open MeasureTheory

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

/-- Stage-2 master theorem target: identify the finite-dimensional field law with
the normalized Gaussian density measure. Existing density theorems will be
rewired to derive from this statement in subsequent stages. -/
axiom latticeGaussianFieldLaw_eq_normalizedGaussianDensityMeasure
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    latticeGaussianFieldLaw d N a mass ha hmass =
      normalizedGaussianDensityMeasure d N a mass

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
