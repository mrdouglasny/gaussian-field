/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Properties of the Constructed Gaussian Measure

Downstream consequences of the characteristic functional identity.

## Main results

### Moments
- `measure_centered`: E[w(f)] = 0 for all f
- `second_moment_eq_covariance`: E[w(f)^2] = <T(f), T(f)>_H = C(f,f)
- `pairing_product_integrable`: w(f)*w(g) is integrable
- `cross_moment_eq_covariance`: E[w(f)*w(g)] = <T(f), T(g)>_H = C(f,g)

### Integrability
- `pairing_integrable`: w(f) is integrable for all f
-/

import GaussianMeasure.Construction

noncomputable section

namespace GaussianMeasure

open MeasureTheory ProbabilityTheory TopologicalSpace

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
variable (T : SchwartzMap D F →L[ℝ] H) (h_inf : ¬ FiniteDimensional ℝ H)

/-- The measure is centered: E[w(f)] = 0 for all test functions f. -/
theorem measure_centered (f : SchwartzMap D F) :
    ∫ ω : Configuration D F, ω f ∂(measure T h_inf).toMeasure = 0 := by
  sorry

/-- Second moment equals covariance: E[w(f)²] = ‖T(f)‖²_H. -/
theorem second_moment_eq_covariance (f : SchwartzMap D F) :
    ∫ ω : Configuration D F, (ω f) ^ 2 ∂(measure T h_inf).toMeasure =
      @inner ℝ H _ (T f) (T f) := by
  sorry

/-- Products of pairings are integrable. -/
theorem pairing_product_integrable (f g : SchwartzMap D F) :
    Integrable (fun ω : Configuration D F => ω f * ω g)
      (measure T h_inf).toMeasure := by
  sorry

/-- Cross moment equals inner product: E[w(f)*w(g)] = <T(f), T(g)>_H. -/
theorem cross_moment_eq_covariance (f g : SchwartzMap D F) :
    ∫ ω : Configuration D F, (ω f) * (ω g) ∂(measure T h_inf).toMeasure =
      @inner ℝ H _ (T f) (T g) := by
  sorry

/-- Pairings are integrable (special case of Fernique-type bound). -/
theorem pairing_integrable (f : SchwartzMap D F) :
    Integrable (fun ω : Configuration D F => ω f)
      (measure T h_inf).toMeasure := by
  sorry

end GaussianMeasure
