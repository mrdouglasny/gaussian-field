/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniqueness of Gaussian Measures from Covariance

Proves that two centered Gaussian probability measures on `Configuration E`
with the same covariance must be equal. This is a general result for any
DyninMityaginSpace.

## Main results

- `gaussian_measure_unique_of_covariance`: If μ₁ and μ₂ are centered Gaussian
  probability measures on `Configuration E` with the same covariance, then μ₁ = μ₂.

## Proof strategy

From the hypotheses, one derives that for all f : E,
  ∫ exp(ω f) dμ₁ = exp(½ ∫(ω f)² dμ₁) = exp(½ ∫(ω f)² dμ₂) = ∫ exp(ω f) dμ₂.

Applying this to `t • f` yields that the moment generating function `t ↦ exp(t² σ²/2)`
of the 1D marginal `(eval_f)_* μ` agrees for both measures, for every test function f.
Since the MGF of a centered Gaussian N(0, σ²) is `exp(t² σ²/2)`, and MGFs determine
distributions, both 1D marginals equal `gaussianReal 0 σ²` for the same σ².

This extends to finite-dimensional marginals by linearity: the joint distribution of
(ω f₁, ..., ω f_k) is determined by its characteristic function, which at (t₁,...,t_k)
equals the 1D characteristic function of ω(∑ tⱼ fⱼ), hence agrees for both measures.

By Dynkin's pi-lambda theorem, measures agreeing on all finite-dimensional cylinder
sets agree on the cylindrical σ-algebra.

## Proved results (all sorry-free)

- `mgf_eq_of_covariance`: Same covariance implies same MGF for all test functions.
- `mgf_at_scaled`: The Gaussian MGF identity applied to `t • f` gives
  `∫ exp(t ωf) = exp(t²σ²/2)`.
- `eval_map_eq_of_covariance`: 1D marginals agree for all test functions. Uses
  analytic continuation from real to complex MGF (via Mathlib's
  `eqOn_complexMGF_of_mgf` + `integrableExpSet_id_gaussianReal`) and
  `ext_of_complexMGF_eq`.
- `pushforward_eq_of_eval_eq`: Equal 1D marginals for all `f : E` imply equal
  pushforward measures on `ℝ^ℕ` via `configBasisEval`. Uses Cramér-Wold
  (`ext_of_charFunDual`) for finite-dimensional marginals and projective limit
  uniqueness (`IsProjectiveLimit.unique`) for the product σ-algebra.
- `gaussian_measure_unique_of_covariance`: The main theorem. The pullback from
  `ℝ^ℕ` uses `instMeasurableSpaceConfiguration_eq_comap`.
-/

import GaussianField.ConfigurationEmbedding
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

noncomputable section

namespace GaussianField

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [hDM : DyninMityaginSpace E]

/-! ## Step 1: MGF equality from hypotheses -/

omit hDM in
/-- If two centered Gaussian measures have the same covariance, their moment
    generating functions agree on all test functions. -/
theorem mgf_eq_of_covariance
    (μ₁ μ₂ : @Measure (Configuration E) instMeasurableSpaceConfiguration)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁_gauss : ∀ (f : E),
      ∫ ω : Configuration E, Real.exp (ω f) ∂μ₁ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ₁))
    (hμ₂_gauss : ∀ (f : E),
      ∫ ω : Configuration E, Real.exp (ω f) ∂μ₂ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ₂))
    (hcov : ∀ (f : E),
      ∫ ω : Configuration E, (ω f) ^ 2 ∂μ₁ =
      ∫ ω : Configuration E, (ω f) ^ 2 ∂μ₂)
    (f : E) :
    ∫ ω : Configuration E, Real.exp (ω f) ∂μ₁ =
    ∫ ω : Configuration E, Real.exp (ω f) ∂μ₂ := by
  rw [hμ₁_gauss f, hμ₂_gauss f, hcov f]

/-! ## Step 2: Scaled MGF identity -/

omit hDM in
/-- For a centered Gaussian measure satisfying the MGF identity, the MGF
    at `t • f` gives `exp(t² σ²(f) / 2)` where `σ²(f) = ∫ (ω f)² dμ`.
    This follows from linearity of ω and the hypothesis. -/
theorem mgf_at_scaled
    (μ : @Measure (Configuration E) instMeasurableSpaceConfiguration)
    [IsProbabilityMeasure μ]
    (hμ_gauss : ∀ (f : E),
      ∫ ω : Configuration E, Real.exp (ω f) ∂μ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ))
    (f : E) (t : ℝ) :
    ∫ ω : Configuration E, Real.exp (t * ω f) ∂μ =
    Real.exp (t ^ 2 / 2 * ∫ ω, (ω f) ^ 2 ∂μ) := by
  have h := hμ_gauss (t • f)
  -- ω(t • f) = t * ω(f) by linearity
  simp_rw [show ∀ ω : Configuration E, ω (t • f) = t * ω f from
    fun ω => map_smul ω t f] at h
  -- (t * ω f) ^ 2 = t ^ 2 * (ω f) ^ 2
  simp_rw [show ∀ ω : Configuration E, (t * ω f) ^ 2 = t ^ 2 * (ω f) ^ 2 from
    fun ω => by ring] at h
  rw [h, integral_const_mul]
  congr 1; ring

/-! ## Step 3: Equal 1D marginals for all test functions -/

omit hDM in
/-- Two centered Gaussian measures with the same covariance have the same
    1D marginal for every test function f.

    Both 1D marginals are `gaussianReal 0 σ²` where `σ² = ∫(ω f)²dμ`.
    The proof requires showing that the real MGF `t ↦ exp(t²σ²/2)` uniquely
    determines the distribution. This follows from analytic continuation to
    the complex MGF `z ↦ exp(z²σ²/2)` and `Measure.ext_of_complexMGF_eq`. -/
theorem eval_map_eq_of_covariance
    (μ₁ μ₂ : @Measure (Configuration E) instMeasurableSpaceConfiguration)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁_gauss : ∀ (f : E),
      ∫ ω : Configuration E, Real.exp (ω f) ∂μ₁ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ₁))
    (hμ₂_gauss : ∀ (f : E),
      ∫ ω : Configuration E, Real.exp (ω f) ∂μ₂ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ₂))
    (hcov : ∀ (f : E),
      ∫ ω : Configuration E, (ω f) ^ 2 ∂μ₁ =
      ∫ ω : Configuration E, (ω f) ^ 2 ∂μ₂)
    (f : E) :
    μ₁.map (fun ω : Configuration E => ω f) =
    μ₂.map (fun ω : Configuration E => ω f) := by
  set σ := (∫ ω : Configuration E, (ω f) ^ 2 ∂μ₁).toNNReal with hσ_def
  have h_meas : @Measurable _ _ instMeasurableSpaceConfiguration _
      (fun ω : Configuration E => ω f) := configuration_eval_measurable f
  -- Show both measures have the same real MGF as gaussianReal 0 σ
  have hmgf₁ : ProbabilityTheory.mgf (fun ω : Configuration E => ω f) μ₁ =
      ProbabilityTheory.mgf id (gaussianReal 0 σ) := by
    ext t
    simp only [ProbabilityTheory.mgf, id]
    rw [mgf_at_scaled μ₁ hμ₁_gauss f t]
    rw [show ∫ x, Real.exp (t * x) ∂gaussianReal 0 σ =
        Real.exp (0 * t + ↑σ * t ^ 2 / 2) from
      ProbabilityTheory.mgf_gaussianReal (by simp) t]
    congr 1
    simp only [zero_mul, zero_add, hσ_def, Real.coe_toNNReal _ (integral_nonneg (fun _ => sq_nonneg _))]
    ring
  have hmgf₂ : ProbabilityTheory.mgf (fun ω : Configuration E => ω f) μ₂ =
      ProbabilityTheory.mgf id (gaussianReal 0 σ) := by
    -- Reuse hmgf₁ and the fact that the real MGF of μ₂ matches μ₁ (via hcov)
    have hmgf₂_eq_₁ : ProbabilityTheory.mgf (fun ω : Configuration E => ω f) μ₂ =
        ProbabilityTheory.mgf (fun ω : Configuration E => ω f) μ₁ := by
      ext t
      simp only [ProbabilityTheory.mgf]
      rw [mgf_at_scaled μ₁ hμ₁_gauss f t, mgf_at_scaled μ₂ hμ₂_gauss f t, hcov f]
    rw [hmgf₂_eq_₁, hmgf₁]
  -- From equal real MGFs, derive equal complexMGFs via analytic continuation.
  -- The integrableExpSet for gaussianReal is all of ℝ, so the strip is all of ℂ.
  have h_eqOn₁ := ProbabilityTheory.eqOn_complexMGF_of_mgf hmgf₁
  have h_eqOn₂ := ProbabilityTheory.eqOn_complexMGF_of_mgf hmgf₂
  -- The strip = ℂ because integrableExpSet = univ for our X
  have h_strip : ProbabilityTheory.integrableExpSet (fun ω : Configuration E => ω f) μ₁ = Set.univ := by
    rw [ProbabilityTheory.integrableExpSet_eq_of_mgf hmgf₁,
        ProbabilityTheory.integrableExpSet_id_gaussianReal]
  rw [h_strip, interior_univ] at h_eqOn₁
  have h_strip₂ : ProbabilityTheory.integrableExpSet (fun ω : Configuration E => ω f) μ₂ = Set.univ := by
    rw [ProbabilityTheory.integrableExpSet_eq_of_mgf hmgf₂,
        ProbabilityTheory.integrableExpSet_id_gaussianReal]
  rw [h_strip₂, interior_univ] at h_eqOn₂
  -- Now h_eqOn₁ : EqOn (complexMGF eval_f μ₁) (complexMGF id gaussianReal) univ
  -- and h_eqOn₂ : EqOn (complexMGF eval_f μ₂) (complexMGF id gaussianReal) univ
  have h_cmgf₁ : ProbabilityTheory.complexMGF (fun ω : Configuration E => ω f) μ₁ =
      ProbabilityTheory.complexMGF id (gaussianReal 0 σ) :=
    funext (fun z => h_eqOn₁ (Set.mem_univ z))
  have h_cmgf₂ : ProbabilityTheory.complexMGF (fun ω : Configuration E => ω f) μ₂ =
      ProbabilityTheory.complexMGF id (gaussianReal 0 σ) :=
    funext (fun z => h_eqOn₂ (Set.mem_univ z))
  -- Equal complexMGFs → equal distributions
  have h₁ := Measure.ext_of_complexMGF_eq h_meas.aemeasurable aemeasurable_id h_cmgf₁
  have h₂ := Measure.ext_of_complexMGF_eq h_meas.aemeasurable aemeasurable_id h_cmgf₂
  -- h₁ : μ₁.map eval_f = gaussianReal 0 σ (via map id = id)
  simp only [Measure.map_id] at h₁ h₂
  rw [h₁, h₂]

/-! ## Step 4: Pushforward equality on ℝ^ℕ -/

/-- If two probability measures on `Configuration E` have the same 1D marginal
    for every test function f : E, then their pushforwards to ℝ^ℕ via
    `configBasisEval` agree.

    This is the combination of the Cramér-Wold theorem (equal 1D marginals on
    all linear combinations determine finite-dimensional joint distributions)
    and Kolmogorov's extension uniqueness (equal finite-dimensional marginals
    determine measures on the product σ-algebra of a Polish space). -/
theorem pushforward_eq_of_eval_eq
    (μ₁ μ₂ : @Measure (Configuration E) instMeasurableSpaceConfiguration)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (h_eval : ∀ f : E,
      μ₁.map (fun ω : Configuration E => ω f) =
      μ₂.map (fun ω : Configuration E => ω f)) :
    @Measure.map _ _ instMeasurableSpaceConfiguration _
      (configBasisEval (E := E)) μ₁ =
    @Measure.map _ _ instMeasurableSpaceConfiguration _
      (configBasisEval (E := E)) μ₂ := by
  -- Use projective limit uniqueness for measures on ℕ → ℝ
  set ν₁ := @Measure.map _ _ instMeasurableSpaceConfiguration _
    (configBasisEval (E := E)) μ₁
  set ν₂ := @Measure.map _ _ instMeasurableSpaceConfiguration _
    (configBasisEval (E := E)) μ₂
  haveI : IsProbabilityMeasure ν₁ :=
    Measure.isProbabilityMeasure_map configBasisEval_measurable.aemeasurable
  haveI : IsProbabilityMeasure ν₂ :=
    Measure.isProbabilityMeasure_map configBasisEval_measurable.aemeasurable
  -- Apply projective limit uniqueness: both are projective limits of ν₁'s marginals
  refine IsProjectiveLimit.unique (P := fun J => ν₁.map (Finset.restrict J))
    (fun J => rfl) (fun J => ?_)
  -- Need: ν₂.map (Finset.restrict J) = ν₁.map (Finset.restrict J)
  simp only [ν₁, ν₂]
  rw [Measure.map_map (Finset.measurable_restrict J) configBasisEval_measurable,
      Measure.map_map (Finset.measurable_restrict J) configBasisEval_measurable]
  -- Apply Cramér-Wold: equal characteristic functions ⟹ equal measures
  set F : Configuration E → ((j : ↥J) → ℝ) :=
    Finset.restrict J ∘ configBasisEval (E := E)
  have hF : @Measurable _ _ instMeasurableSpaceConfiguration MeasurableSpace.pi F :=
    (Finset.measurable_restrict J).comp configBasisEval_measurable
  apply Measure.ext_of_charFunDual
  funext L
  simp only [charFunDual_apply]
  -- Change of variables: ∫ v, exp(↑(L v) * I) d(μᵢ.map F) = ∫ ω, exp(↑(L(F ω)) * I) dμᵢ
  have hg : ∀ (ν : Measure ((j : ↥J) → ℝ)),
      AEStronglyMeasurable (fun v => Complex.exp (↑(L v) * Complex.I)) ν :=
    fun _ => (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp L.continuous).mul continuous_const)).aestronglyMeasurable
  rw [integral_map hF.aemeasurable (hg _), integral_map hF.aemeasurable (hg _)]
  -- Key linearity: L(F ω) = ω(f_L) where f_L = ∑ L(eⱼ) • basis j
  set f_L : E := ∑ j : ↥J,
    L (Pi.single j 1) • DyninMityaginSpace.basis (↑j : ℕ)
  suffices hkey : ∀ ω : Configuration E, L (F ω) = ω f_L by
    simp_rw [hkey]
    -- From h_eval f_L: the 1D marginals agree, so integrals agree
    have h_meas : @Measurable _ _ instMeasurableSpaceConfiguration _
        (fun ω : Configuration E => ω f_L) := configuration_eval_measurable f_L
    have hg' : ∀ (ν : Measure ℝ),
        AEStronglyMeasurable (fun x : ℝ => Complex.exp (↑x * Complex.I)) ν :=
      fun _ => (Complex.continuous_exp.comp
        (Complex.continuous_ofReal.mul continuous_const)).aestronglyMeasurable
    rw [show ∫ ω, Complex.exp (↑(ω f_L) * Complex.I) ∂μ₂ =
        ∫ x, Complex.exp (↑x * Complex.I) ∂(μ₂.map (fun ω : Configuration E => ω f_L)) from
        (integral_map h_meas.aemeasurable (hg' _)).symm,
      show ∫ ω, Complex.exp (↑(ω f_L) * Complex.I) ∂μ₁ =
        ∫ x, Complex.exp (↑x * Complex.I) ∂(μ₁.map (fun ω : Configuration E => ω f_L)) from
        (integral_map h_meas.aemeasurable (hg' _)).symm,
      (h_eval f_L).symm]
  -- Prove the key linearity: L(F ω) = ω(f_L)
  intro ω
  -- L v = ∑ j, v j * L(Pi.single j 1) for any v, by decomposition
  have hL_decomp : ∀ v : (j : ↥J) → ℝ,
      L v = ∑ j : ↥J, v j * L (Pi.single j 1) := by
    intro v
    have hv : v = ∑ j : ↥J, v j • Pi.single (M := fun _ : ↥J => ℝ) j 1 := by
      ext k
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul,
                  mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    conv_lhs => rw [hv]
    rw [map_sum]; congr 1; ext j; rw [map_smul, smul_eq_mul]
  -- Apply hL_decomp to F ω
  change L (F ω) = ω f_L
  rw [show F ω = (fun j : ↥J => ω (DyninMityaginSpace.basis ↑j)) from by
    funext j; rfl]
  rw [hL_decomp]
  -- RHS: ω(f_L) = ∑ j, L(eⱼ) * ω(basis j) by linearity of ω
  simp only [f_L, map_sum ω, map_smul ω, smul_eq_mul]
  -- Both sides: ∑ ω(basis j) * L(eⱼ) = ∑ L(eⱼ) * ω(basis j)
  congr 1; ext j; ring

/-! ## Main theorem -/

/-- **Uniqueness of Gaussian measures from covariance.**

Two centered Gaussian probability measures on `Configuration E` with the same
covariance (second moment structure) must be equal.

The proof combines three ingredients:
1. **MGF matching**: From the hypotheses, for all `f : E`,
   `∫ exp(ω f) dμ₁ = ∫ exp(ω f) dμ₂` (via same covariance).
2. **1D marginals agree**: The MGF equality for all `t • f` shows the 1D marginal
   `(eval_f)_* μ` is `gaussianReal 0 σ²` with `σ² = ∫(ω f)²dμ`, the same for both.
3. **Measure extension**: Equal 1D marginals for all f implies equal finite-dim
   marginals (Cramer-Wold), which determines the pushforward to ℝ^ℕ (Kolmogorov
   uniqueness on Polish space), which pulls back to Configuration E via the
   σ-algebra identity `instMeasurableSpaceConfiguration_eq_comap`. -/
theorem gaussian_measure_unique_of_covariance
    (μ₁ μ₂ : @Measure (Configuration E) instMeasurableSpaceConfiguration)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂]
    (hμ₁_gauss : ∀ (f : E),
      ∫ ω : Configuration E, Real.exp (ω f) ∂μ₁ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ₁))
    (hμ₂_gauss : ∀ (f : E),
      ∫ ω : Configuration E, Real.exp (ω f) ∂μ₂ =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂μ₂))
    (hcov : ∀ (f : E),
      ∫ ω : Configuration E, (ω f) ^ 2 ∂μ₁ =
      ∫ ω : Configuration E, (ω f) ^ 2 ∂μ₂) :
    μ₁ = μ₂ := by
  -- Step 1: All 1D marginals agree
  have h_eval : ∀ f : E,
      μ₁.map (fun ω : Configuration E => ω f) =
      μ₂.map (fun ω : Configuration E => ω f) :=
    eval_map_eq_of_covariance μ₁ μ₂ hμ₁_gauss hμ₂_gauss hcov
  -- Step 2: Pushforward measures to ℝ^ℕ agree
  set ν₁ := @Measure.map _ _ instMeasurableSpaceConfiguration _
    (configBasisEval (E := E)) μ₁ with hν₁_def
  set ν₂ := @Measure.map _ _ instMeasurableSpaceConfiguration _
    (configBasisEval (E := E)) μ₂ with hν₂_def
  have h_push_eq : ν₁ = ν₂ := pushforward_eq_of_eval_eq μ₁ μ₂ h_eval
  -- Step 3: Pull back from ℝ^ℕ to Configuration E
  ext s hs
  rw [instMeasurableSpaceConfiguration_eq_comap] at hs
  obtain ⟨T, hT, hpre⟩ := hs
  have h₁ : μ₁ s = ν₁ T := by
    rw [hν₁_def, Measure.map_apply configBasisEval_measurable hT, ← hpre]
  have h₂ : μ₂ s = ν₂ T := by
    rw [hν₂_def, Measure.map_apply configBasisEval_measurable hT, ← hpre]
  rw [h₁, h₂, h_push_eq]

end GaussianField

end
