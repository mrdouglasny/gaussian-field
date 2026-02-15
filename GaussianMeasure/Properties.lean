/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Properties of the Constructed Gaussian Measure

Downstream consequences of the characteristic functional identity.

## Main results

### Key intermediate result
- `pairing_is_gaussian`: pushforward by evaluation is a 1D Gaussian

### Moments
- `measure_centered`: E[w(f)] = 0 for all f
- `second_moment_eq_covariance`: E[w(f)^2] = <T(f), T(f)>_H = C(f,f)
- `pairing_product_integrable`: w(f)*w(g) is integrable
- `cross_moment_eq_covariance`: E[w(f)*w(g)] = <T(f), T(g)>_H = C(f,g)

### Integrability
- `pairing_integrable`: w(f) is integrable for all f
- `pairing_memLp`: w(f) is in Lᵖ for all finite p (Fernique-type)
-/

import GaussianMeasure.Construction
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

namespace GaussianMeasure

open MeasureTheory ProbabilityTheory TopologicalSpace Complex
open scoped BigOperators NNReal
open Classical

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
variable (T : SchwartzMap D F →L[ℝ] H) (h_inf : ¬ FiniteDimensional ℝ H)

/-- The pushforward of the Gaussian measure by evaluation at f is a 1D Gaussian
    with mean 0 and variance ‖T(f)‖² = ⟨T(f), T(f)⟩_H.

    Proof: By Lévy's uniqueness theorem, it suffices to match characteristic functions.
    The charFun of the pushforward at t equals charFun applied to t•f, which by
    our main theorem equals exp(-½ t² ‖T(f)‖²) — exactly the charFun of N(0, ‖T(f)‖²). -/
theorem pairing_is_gaussian (f : SchwartzMap D F) :
    (measure T h_inf).map (fun ω : Configuration D F => ω f) =
      gaussianReal 0 (@inner ℝ H _ (T f) (T f) : ℝ).toNNReal := by
  haveI : IsProbabilityMeasure ((measure T h_inf).map
      (fun ω : Configuration D F => ω f)) :=
    Measure.isProbabilityMeasure_map (configuration_eval_measurable f).aemeasurable
  apply Measure.ext_of_charFun
  funext t
  -- LHS: charFun of the pushforward
  rw [charFun_apply_real]
  -- ∫ x, exp(t*x*I) ∂(map (fun ω => ω f) μ)
  have hmeas_integrand : AEStronglyMeasurable (fun x : ℝ => Complex.exp (↑t * ↑x * I))
      ((measure T h_inf).map (fun ω : Configuration D F => ω f)) :=
    (Complex.continuous_exp.comp
      ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)).aestronglyMeasurable
  rw [integral_map (configuration_eval_measurable f).aemeasurable hmeas_integrand]
  -- Now: ∫ ω, exp(t * (ω f) * I) d(measure T h_inf)
  -- Use charFun T h_inf (t • f)
  have h_char := charFun T h_inf (t • f)
  -- Rewrite T(t•f) = t • T(f) and ω(t•f) = t * ω(f)
  simp only [map_smul, smul_eq_mul] at h_char
  -- Match integrands: t * (ω f) * I = I * ↑(t * ω f)
  simp_rw [show ∀ (ω : Configuration D F),
      cexp (↑t * ↑(ω f) * I) = cexp (I * ↑(t * ω f))
    from fun ω => by congr 1; push_cast; ring]
  rw [h_char]
  -- RHS: charFun of gaussianReal 0 σ
  rw [charFun_gaussianReal]
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_sub]
  rw [real_inner_smul_left, real_inner_smul_right]
  rw [Real.coe_toNNReal _ real_inner_self_nonneg]
  push_cast; ring

/-- Pairings are in Lᵖ for all finite p (Fernique-type bound).
    Follows from `pairing_is_gaussian` + Mathlib's `memLp_id_gaussianReal`. -/
theorem pairing_memLp (f : SchwartzMap D F) (p : ℝ≥0) :
    MemLp (fun ω : Configuration D F => ω f) p (measure T h_inf) := by
  have h_gauss := pairing_is_gaussian T h_inf f
  have h_memLp : MemLp id p
      (gaussianReal 0 (@inner ℝ H _ (T f) (T f) : ℝ).toNNReal) :=
    memLp_id_gaussianReal p
  rw [← h_gauss] at h_memLp
  rwa [memLp_map_measure_iff h_memLp.aestronglyMeasurable
    (configuration_eval_measurable f).aemeasurable] at h_memLp

/-- Pairings are integrable (special case of Fernique-type bound). -/
theorem pairing_integrable (f : SchwartzMap D F) :
    Integrable (fun ω : Configuration D F => ω f)
      (measure T h_inf) :=
  memLp_one_iff_integrable.mp (pairing_memLp T h_inf f 1)

/-- The measure is centered: E[w(f)] = 0 for all test functions f.
    Proof: pushforward by evaluation is N(0, σ²), whose mean is 0. -/
theorem measure_centered (f : SchwartzMap D F) :
    ∫ ω : Configuration D F, ω f ∂(measure T h_inf) = 0 := by
  have h_gauss := pairing_is_gaussian T h_inf f
  -- Relate to integral on pushforward measure
  have h_map := integral_map (configuration_eval_measurable f).aemeasurable
    (measurable_id.aestronglyMeasurable
      (μ := (measure T h_inf).map (fun ω : Configuration D F => ω f)))
  -- h_map : ∫ x, id x ∂(map ...) = ∫ ω, id (ω f) ∂μ = ∫ ω, ω f ∂μ
  simp only [id] at h_map
  rw [h_map.symm, h_gauss, integral_id_gaussianReal]

/-- Second moment equals covariance: E[w(f)²] = ‖T(f)‖²_H.
    Proof: pushforward is N(0, σ²), variance of N(0,σ²) is σ². -/
theorem second_moment_eq_covariance (f : SchwartzMap D F) :
    ∫ ω : Configuration D F, (ω f) ^ 2 ∂(measure T h_inf) =
      @inner ℝ H _ (T f) (T f) := by
  have h_gauss := pairing_is_gaussian T h_inf f
  set σ := (@inner ℝ H _ (T f) (T f) : ℝ).toNNReal with hσ_def
  -- variance = second moment since mean = 0
  have h_var : Var[fun ω : Configuration D F => ω f; measure T h_inf] =
      ∫ ω, (ω f) ^ 2 ∂(measure T h_inf) :=
    variance_of_integral_eq_zero
      (configuration_eval_measurable f).aemeasurable
      (measure_centered T h_inf f)
  -- Compute variance via pushforward
  have h_var2 : Var[fun ω : Configuration D F => ω f; measure T h_inf] = σ := by
    have h : Var[fun x : ℝ => x;
        (measure T h_inf).map (fun ω : Configuration D F => ω f)] =
        Var[fun ω : Configuration D F => ω f; measure T h_inf] :=
      variance_map aemeasurable_id (configuration_eval_measurable f).aemeasurable
    rw [← h, h_gauss, variance_fun_id_gaussianReal]
  rw [← h_var, h_var2, hσ_def]
  exact Real.coe_toNNReal _ real_inner_self_nonneg

/-- Products of pairings are integrable (by Cauchy-Schwarz in L²). -/
theorem pairing_product_integrable (f g : SchwartzMap D F) :
    Integrable (fun ω : Configuration D F => ω f * ω g)
      (measure T h_inf) := by
  have hf : MemLp (fun ω : Configuration D F => ω f) 2 (measure T h_inf) := by
    exact_mod_cast pairing_memLp T h_inf f 2
  have hg : MemLp (fun ω : Configuration D F => ω g) 2 (measure T h_inf) := by
    exact_mod_cast pairing_memLp T h_inf g 2
  exact hf.integrable_mul hg

/-- Cross moment equals inner product: E[w(f)*w(g)] = <T(f), T(g)>_H.
    Proof by polarization from the second moment identity:
    ⟨Tf, Tg⟩ = ¼(‖T(f+g)‖² - ‖T(f-g)‖²)
             = ¼(E[(ω(f+g))²] - E[(ω(f-g))²])
             = E[ω(f) * ω(g)] -/
theorem cross_moment_eq_covariance (f g : SchwartzMap D F) :
    ∫ ω : Configuration D F, (ω f) * (ω g) ∂(measure T h_inf) =
      @inner ℝ H _ (T f) (T g) := by
  -- Polarization: 4⟨Tf, Tg⟩ = ‖T(f+g)‖² - ‖T(f-g)‖²
  have h_polar : @inner ℝ H _ (T f) (T g) =
      (1/4) * (@inner ℝ H _ (T (f + g)) (T (f + g)) -
               @inner ℝ H _ (T (f - g)) (T (f - g))) := by
    simp only [map_add, map_sub]
    rw [show @inner ℝ H _ (T f + T g) (T f + T g) =
        @inner ℝ H _ (T f) (T f) + 2 * @inner ℝ H _ (T f) (T g) +
        @inner ℝ H _ (T g) (T g) from by
      rw [inner_add_left, inner_add_right, inner_add_right,
          real_inner_comm (T g) (T f)]; ring]
    rw [show @inner ℝ H _ (T f - T g) (T f - T g) =
        @inner ℝ H _ (T f) (T f) - 2 * @inner ℝ H _ (T f) (T g) +
        @inner ℝ H _ (T g) (T g) from by
      rw [inner_sub_left, inner_sub_right, inner_sub_right,
          real_inner_comm (T g) (T f)]; ring]
    ring
  -- Polarization for integral via difference of squares
  have h_int_polar : ∫ ω : Configuration D F, ω f * ω g ∂measure T h_inf =
      (1/4) * (∫ ω, (ω (f + g)) ^ 2 ∂measure T h_inf -
               ∫ ω, (ω (f - g)) ^ 2 ∂measure T h_inf) := by
    have hfg_int := pairing_product_integrable T h_inf f g
    -- Difference of squares identity
    have hp : ∀ ω : Configuration D F,
        (ω (f + g)) ^ 2 - (ω (f - g)) ^ 2 = 4 * (ω f * ω g) := fun ω => by
      rw [show ω (f + g) = ω f + ω g from ω.map_add f g,
          show ω (f - g) = ω f - ω g from ω.map_sub f g]; ring
    have hfg_sq := (pairing_memLp T h_inf (f + g) 2).integrable_sq
    have hfmg_sq := (pairing_memLp T h_inf (f - g) 2).integrable_sq
    rw [← integral_sub hfg_sq hfmg_sq]
    simp_rw [hp]
    rw [integral_const_mul]
    ring
  rw [h_int_polar, h_polar]
  congr 1
  rw [second_moment_eq_covariance T h_inf (f + g),
      second_moment_eq_covariance T h_inf (f - g)]

end GaussianMeasure
