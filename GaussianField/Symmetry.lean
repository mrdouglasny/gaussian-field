/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Measure-Level Symmetries of Gaussian Fields

For a centered Gaussian measure `μ = GaussianField.measure T`, any continuous
linear self-map `g : E →L[ℝ] E` whose induced action preserves the covariance
form `⟨T·, T·⟩` produces an invariance of `μ`:

  `μ.map (configurationPullback g) = μ`.

This subsumes every covariance-preserving symmetry: negation, lattice
translations and reflections, O(N) rotations of vector fields, Euclidean
group action on the continuum GFF, etc. Each becomes a one-line
specialization of `measure_invariant_of_covariance_preserved`.

## Main results

- `configurationPullback g : Configuration E → Configuration E` — the dual
  action `ω ↦ ω ∘ g`.
- `integral_exp_pairing T f` — the real Gaussian MGF identity for
  `measure T`, derived from `pairing_is_gaussian` + `mgf_gaussianReal`.
- `measure_invariant_of_covariance_preserved` — the workhorse theorem.
- `measure_neg_invariant` — every centered Gaussian on Configuration is
  invariant under the dual negation action (g = -id).
- `latticeGaussianFieldLaw_isNegInvariant` — instance lifting the
  Configuration-side negation invariance through `evalMap` to the
  field-law side.
-/

import GaussianField.MeasureUniqueness
import GaussianField.Properties
import Lattice.Covariance
import GaussianField.Density
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.MetricSpace.Basic

noncomputable section

namespace GaussianField

open MeasureTheory ProbabilityTheory TopologicalSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]

/-! ## Configuration pullback by a linear self-map of E -/

/-- Pullback of a configuration `ω : Configuration E` by a continuous linear
self-map `g : E →L[ℝ] E`. Sends `ω : E →L[ℝ] ℝ` to its precomposition with
`g`, evaluated as `f ↦ ω (g f)`. -/
def configurationPullback (g : E →L[ℝ] E) :
    Configuration E → Configuration E :=
  fun ω => (ω : E →L[ℝ] ℝ).comp g

@[simp]
theorem configurationPullback_apply (g : E →L[ℝ] E)
    (ω : Configuration E) (f : E) :
    (configurationPullback g ω) f = ω (g f) := rfl

/-- Pullback by a linear map is measurable w.r.t. the cylindrical σ-algebra. -/
theorem measurable_configurationPullback (g : E →L[ℝ] E) :
    @Measurable (Configuration E) (Configuration E)
      instMeasurableSpaceConfiguration instMeasurableSpaceConfiguration
      (configurationPullback g) := by
  apply configuration_measurable_of_eval_measurable
  intro f
  exact configuration_eval_measurable (g f)

/-! ## Real Gaussian MGF identity for `measure T`

The integral `∫ exp(ω f) d(measure T) = exp((1/2) · ⟨T f, T f⟩)`. Follows from
`pairing_is_gaussian` plus the standard MGF identity for `gaussianReal`. -/

section MGFIdentity

variable (T : E →L[ℝ] H)

/-- The MGF identity for the Gaussian measure: `∫ exp(ω f) d(measure T) =
exp((1/2) · ⟨T f, T f⟩)`. Pushforward of `eval f` is `gaussianReal 0 σ²`;
`mgf_gaussianReal` at `t = 1` gives the result. -/
theorem integral_exp_pairing (f : E) :
    ∫ ω : Configuration E, Real.exp (ω f) ∂(measure T) =
      Real.exp ((1 / 2) * @inner ℝ H _ (T f) (T f)) := by
  have h_pair := pairing_is_gaussian T f
  have h_mgf := mgf_gaussianReal h_pair 1
  have h_unfold : mgf (fun ω : Configuration E => ω f) (measure T) 1 =
      ∫ ω : Configuration E, Real.exp (ω f) ∂(measure T) := by
    simp [mgf, one_mul]
  rw [← h_unfold, h_mgf]
  congr 1
  have h_nn_ge : (0 : ℝ) ≤ @inner ℝ H _ (T f) (T f) := real_inner_self_nonneg
  have h_nn : ((@inner ℝ H _ (T f) (T f)).toNNReal : ℝ) = @inner ℝ H _ (T f) (T f) :=
    Real.coe_toNNReal _ h_nn_ge
  push_cast [h_nn]
  ring

/-- The Gaussian MGF identity in the variance form needed by
`gaussian_measure_unique_of_covariance`. -/
theorem integral_exp_pairing_eq_exp_variance (f : E) :
    ∫ ω : Configuration E, Real.exp (ω f) ∂(measure T) =
      Real.exp ((1 / 2) * ∫ ω, (ω f) ^ 2 ∂(measure T)) := by
  rw [integral_exp_pairing T f, second_moment_eq_covariance T f]

end MGFIdentity

/-! ## The workhorse: covariance-preserved invariance -/

/-- **Covariance-preserved invariance.** If `g : E →L[ℝ] E` preserves the
covariance form `⟨T·, T·⟩`, then the Gaussian measure `measure T` is invariant
under the dual action `configurationPullback g`. -/
theorem measure_invariant_of_covariance_preserved
    (T : E →L[ℝ] H) (g : E →L[ℝ] E)
    (h_cov : ∀ f, @inner ℝ H _ (T (g f)) (T (g f)) = @inner ℝ H _ (T f) (T f)) :
    (measure T).map (configurationPullback g) = measure T := by
  haveI : IsProbabilityMeasure ((measure T).map (configurationPullback g)) :=
    Measure.isProbabilityMeasure_map (measurable_configurationPullback g).aemeasurable
  -- Helper: pushforward integrals reduce to integrals against (measure T).
  -- Apply integral_map then the simp lemma configurationPullback_apply.
  have h_pull_exp : ∀ f : E,
      ∫ ω, Real.exp (ω f) ∂((measure T).map (configurationPullback g)) =
      ∫ ω, Real.exp (ω (g f)) ∂(measure T) := by
    intro f
    have h : ∫ ω, Real.exp (ω f) ∂((measure T).map (configurationPullback g)) =
        ∫ x, Real.exp ((configurationPullback g x) f) ∂(measure T) :=
      MeasureTheory.integral_map (measurable_configurationPullback g).aemeasurable
        (Real.measurable_exp.comp (configuration_eval_measurable f)).aestronglyMeasurable
    simp only [configurationPullback_apply] at h
    exact h
  have h_pull_sq : ∀ f : E,
      ∫ ω, (ω f) ^ 2 ∂((measure T).map (configurationPullback g)) =
      ∫ ω, (ω (g f)) ^ 2 ∂(measure T) := by
    intro f
    have h : ∫ ω, (ω f) ^ 2 ∂((measure T).map (configurationPullback g)) =
        ∫ x, ((configurationPullback g x) f) ^ 2 ∂(measure T) :=
      MeasureTheory.integral_map (measurable_configurationPullback g).aemeasurable
        ((configuration_eval_measurable f).pow_const 2).aestronglyMeasurable
    simp only [configurationPullback_apply] at h
    exact h
  apply gaussian_measure_unique_of_covariance
  · -- MGF identity for the pushforward
    intro f
    rw [h_pull_exp f, h_pull_sq f]
    exact integral_exp_pairing_eq_exp_variance T (g f)
  · -- MGF identity for measure T
    exact integral_exp_pairing_eq_exp_variance T
  · -- Same second moment
    intro f
    rw [h_pull_sq f, second_moment_eq_covariance T (g f), second_moment_eq_covariance T f]
    exact h_cov f

/-! ## Specialization: negation invariance -/

/-- The negation map `-id : E →L[ℝ] E` as a continuous linear map. -/
def negCLM : E →L[ℝ] E := -ContinuousLinearMap.id ℝ E

@[simp]
theorem negCLM_apply (f : E) : (negCLM : E →L[ℝ] E) f = -f := rfl

/-- **Centered Gaussian measures are negation-invariant on Configuration space.**
The covariance form `⟨T·, T·⟩` is bilinear, so `⟨T(-f), T(-f)⟩ = ⟨T f, T f⟩`. -/
theorem measure_neg_invariant (T : E →L[ℝ] H) :
    (measure T).map (configurationPullback negCLM) = measure T := by
  apply measure_invariant_of_covariance_preserved T negCLM
  intro f
  simp only [negCLM_apply, map_neg]
  rw [inner_neg_left, inner_neg_right, neg_neg]

end GaussianField

/-! ## Lattice GFF: negation invariance via evalMap pushforward -/

namespace GaussianField

variable (d N : ℕ) [NeZero N]

/-- The lattice Gaussian field law is a probability measure. -/
instance latticeGaussianFieldLaw_isProbability
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    MeasureTheory.IsProbabilityMeasure
      (latticeGaussianFieldLaw d N a mass ha hmass) := by
  unfold latticeGaussianFieldLaw
  exact MeasureTheory.Measure.isProbabilityMeasure_map
    (measurable_evalMap d N).aemeasurable

/-- The evaluation map intertwines `Neg` on `Configuration` with pointwise
`Neg` on `FinLatticeField`. Concretely:
`(-(evalMap ω)) = evalMap (configurationPullback negCLM ω)`. -/
private theorem neg_evalMap_eq_evalMap_configurationPullback
    (ω : Configuration (FinLatticeField d N)) :
    (fun x => -(evalMap d N ω) x) =
      evalMap d N (configurationPullback negCLM ω) := by
  funext x
  simp only [evalMap, configurationPullback_apply, negCLM_apply]
  exact (map_neg ω _).symm

/-- **Negation invariance of the lattice Gaussian field law.**
The measure on `FinLatticeField d N` is invariant under pointwise field
negation `φ ↦ -φ`. -/
theorem latticeGaussianFieldLaw_map_neg
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (latticeGaussianFieldLaw d N a mass ha hmass).map (fun φ => -φ) =
      latticeGaussianFieldLaw d N a mass ha hmass := by
  -- Rewrite using latticeGaussianFieldLaw = (latticeGaussianMeasure).map evalMap
  unfold latticeGaussianFieldLaw
  -- Compose maps: ((μ.map evalMap).map Neg) = μ.map (Neg ∘ evalMap)
  rw [MeasureTheory.Measure.map_map (by fun_prop : Measurable (fun φ : FinLatticeField d N => -φ))
    (measurable_evalMap d N)]
  -- Show Neg ∘ evalMap = evalMap ∘ configurationPullback negCLM
  have h_intertwine : (fun φ : FinLatticeField d N => -φ) ∘ evalMap d N =
      evalMap d N ∘ configurationPullback negCLM := by
    funext ω
    exact (neg_evalMap_eq_evalMap_configurationPullback d N ω)
  rw [h_intertwine]
  -- Now: (latticeGaussianMeasure).map (evalMap ∘ cfgPB negCLM)
  --    = ((latticeGaussianMeasure).map (cfgPB negCLM)).map evalMap
  --    = (latticeGaussianMeasure).map evalMap  [by measure_neg_invariant]
  rw [← MeasureTheory.Measure.map_map (measurable_evalMap d N)
    (measurable_configurationPullback negCLM)]
  unfold latticeGaussianMeasure
  rw [measure_neg_invariant (latticeCovariance d N a mass ha hmass)]

/-- `IsNegInvariant` instance for the lattice Gaussian field law.
This is the property required by `oneDim_hasCorrelationDecay` and the
mass-gap chain. -/
instance latticeGaussianFieldLaw_isNegInvariant
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    (latticeGaussianFieldLaw d N a mass ha hmass).IsNegInvariant where
  neg_eq_self := by
    show (latticeGaussianFieldLaw d N a mass ha hmass).map Neg.neg =
         latticeGaussianFieldLaw d N a mass ha hmass
    exact latticeGaussianFieldLaw_map_neg d N a mass ha hmass

end GaussianField

end
