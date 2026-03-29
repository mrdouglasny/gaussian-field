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

## Axiom

One axiom:
- `cramerWold`: The Cramér-Wold theorem — two probability measures on `ι → ℝ`
  agreeing on all 1D marginals under linear projections are equal. This is a
  standard result following from injectivity of the characteristic function.

## Proved results

- `mgf_eq_of_covariance`: Same covariance implies same MGF for all test functions.
- `mgf_at_scaled`: The Gaussian MGF identity applied to `t • f` gives
  `∫ exp(t ωf) = exp(t²σ²/2)`.
- `eval_map_eq_of_covariance`: 1D marginals agree for all test functions. Uses
  analytic continuation from real to complex MGF (via Mathlib's
  `eqOn_complexMGF_of_mgf` + `integrableExpSet_id_gaussianReal`) and
  `ext_of_complexMGF_eq`.
- `pushforward_eq_of_eval_eq`: Equal 1D marginals for all `f : E` imply equal
  pushforwards to `ℝ^ℕ`. Uses `cramerWold` + `IsProjectiveLimit.unique`.
- `gaussian_measure_unique_of_covariance`: The main theorem. Pullback from `ℝ^ℕ`
  uses `instMeasurableSpaceConfiguration_eq_comap`.
-/

import GaussianField.ConfigurationEmbedding
import Mathlib.Probability.Distributions.Gaussian.Real

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators

/-- **Cramér-Wold theorem**: Two probability measures on a finite product `ι → ℝ` are equal
    if they assign the same distribution to every linear functional `x ↦ ∑ i, c i * x i`.

    Proof sketch: The characteristic function `φ_ν(t) = E[exp(i⟨t,X⟩)]` at point `c` equals
    the 1D characteristic function of `⟨c,X⟩` at 1, via `charFun_map_eq_charFunDual_smul`.
    Equal 1D distributions for all `c` imply equal characteristic functions, hence equal measures
    (by `Measure.ext_of_charFun`). -/
axiom cramerWold {ι : Type*} [Fintype ι]
    (ν₁ ν₂ : Measure (ι → ℝ))
    [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h : ∀ c : ι → ℝ,
      ν₁.map (fun x => ∑ i : ι, c i * x i) =
      ν₂.map (fun x => ∑ i : ι, c i * x i)) :
    ν₁ = ν₂

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

/-- Composing restriction to `I` and a linear functional with `configBasisEval` gives
    evaluation at a linear combination of basis vectors. -/
private lemma map_restrict_lin_eq
    (μ : @Measure (Configuration E) instMeasurableSpaceConfiguration)
    (I : Finset ℕ) (c : ↥I → ℝ) :
    ((μ.map (configBasisEval (E := E))).map I.restrict).map
      (fun x : ↥I → ℝ => ∑ i, c i * x i) =
    μ.map (fun ω : Configuration E =>
      ω (∑ i : ↥I, c i • DyninMityaginSpace.basis (↑i : ℕ))) := by
  have h_restrict_meas : Measurable (I.restrict (π := fun _ : ℕ => ℝ)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  have h_lin_meas : Measurable (fun x : ↥I → ℝ => ∑ i, c i * x i) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i))
  rw [Measure.map_map h_lin_meas h_restrict_meas,
      Measure.map_map (h_lin_meas.comp h_restrict_meas) configBasisEval_measurable]
  congr 1; ext ω
  simp only [Function.comp, configBasisEval, Finset.restrict_def]
  rw [map_sum]; congr 1; ext i; rw [map_smul, smul_eq_mul]

/-- If two probability measures on `Configuration E` have the same 1D marginal
    for every test function f : E, then their pushforwards to ℝ^ℕ via
    `configBasisEval` agree.

    Uses `cramerWold` (equal 1D marginals of all linear combinations determine
    finite-dimensional joint distributions) and `IsProjectiveLimit.unique`
    (equal finite-dimensional marginals determine measures on `ℕ → ℝ`). -/
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
  set ν₁ := @Measure.map _ _ instMeasurableSpaceConfiguration _
    (configBasisEval (E := E)) μ₁
  set ν₂ := @Measure.map _ _ instMeasurableSpaceConfiguration _
    (configBasisEval (E := E)) μ₂
  haveI : IsProbabilityMeasure ν₁ :=
    Measure.isProbabilityMeasure_map configBasisEval_measurable.aemeasurable
  haveI : IsProbabilityMeasure ν₂ :=
    Measure.isProbabilityMeasure_map configBasisEval_measurable.aemeasurable
  -- Projective family from ν₁'s finite-dimensional marginals
  set P : ∀ I : Finset ℕ, Measure (∀ j : ↥I, ℝ) := fun I => ν₁.map I.restrict
  have h_restrict_meas : ∀ I : Finset ℕ,
      Measurable (I.restrict (π := fun _ : ℕ => ℝ)) :=
    fun I => measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  haveI : ∀ I : Finset ℕ, IsFiniteMeasure (P I) := by
    intro I
    haveI : IsProbabilityMeasure (P I) :=
      Measure.isProbabilityMeasure_map (h_restrict_meas I).aemeasurable
    infer_instance
  -- ν₁ is a projective limit (by definition of P)
  have hν₁_proj : IsProjectiveLimit ν₁ P := fun I => rfl
  -- ν₂ is a projective limit (via Cramér-Wold on each finite-dim marginal)
  have hν₂_proj : IsProjectiveLimit ν₂ P := by
    intro I
    show ν₂.map I.restrict = ν₁.map I.restrict
    symm
    haveI : IsProbabilityMeasure (Measure.map I.restrict ν₁) :=
      Measure.isProbabilityMeasure_map (h_restrict_meas I).aemeasurable
    haveI : IsProbabilityMeasure (Measure.map I.restrict ν₂) :=
      Measure.isProbabilityMeasure_map (h_restrict_meas I).aemeasurable
    apply cramerWold
    intro c
    rw [map_restrict_lin_eq μ₁ I c, map_restrict_lin_eq μ₂ I c]
    exact h_eval _
  exact IsProjectiveLimit.unique hν₁_proj hν₂_proj

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
