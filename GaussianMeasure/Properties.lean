/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Properties of the Constructed Gaussian Measure

Downstream consequences of the characteristic functional identity.

## Main results

### Gaussianity
- `pairing_is_gaussian`: For every f ∈ S(D,F), the pushforward of μ
  under ω ↦ ω(f) is a 1D Gaussian N(0, ‖T(f)‖²).

### Moments
- `measure_centered`: E[ω(f)] = 0 for all f
- `second_moment_eq_covariance`: E[ω(f)²] = ⟨T(f), T(f)⟩_H = C(f,f)
- `pairing_product_integrable`: ω(f)·ω(g) is integrable
- `cross_moment_eq_covariance`: E[ω(f)·ω(g)] = ⟨T(f), T(g)⟩_H = C(f,g)

### Integrability
- `pairing_memLp`: ω(f) ∈ Lᵖ(μ) for all 1 ≤ p < ∞ (Fernique)
- `exponential_integrability`: exp(t·ω(f)) is integrable for |t| < 1/(√2 ‖T(f)‖)
-/

import GaussianMeasure.Construction

noncomputable section

namespace GaussianMeasure

open MeasureTheory ProbabilityTheory

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## Gaussianity -/

/-- Every test-function pairing produces a 1D Gaussian random variable.
    The pushforward of μ under ω ↦ ω(f) is N(0, ‖T(f)‖²).

    Proof: The characteristic function of the pushforward is
    t ↦ E[exp(it·ω(f))] = exp(-½ t² ‖T(f)‖²)
    which matches the CF of N(0, ‖T(f)‖²). By Lévy uniqueness, done. -/
theorem pairing_is_gaussian (data : GaussianMeasureData D F)
    (f : SchwartzMap D F) :
    Measure.map (fun ω : Configuration D F => ω f) data.measure.toMeasure =
      gaussianReal 0 (@inner ℝ data.H data.instIPS (data.T f) (data.T f)) := by
  sorry

/-! ## Moments -/

/-- The measure is centered: E[ω(f)] = 0 for all test functions f. -/
theorem measure_centered (data : GaussianMeasureData D F)
    (f : SchwartzMap D F) :
    ∫ ω : Configuration D F, ω f ∂data.measure.toMeasure = 0 := by
  sorry

/-- Second moment equals covariance: E[ω(f)²] = ‖T(f)‖²_H. -/
theorem second_moment_eq_covariance (data : GaussianMeasureData D F)
    (f : SchwartzMap D F) :
    ∫ ω : Configuration D F, (ω f) ^ 2 ∂data.measure.toMeasure =
      @inner ℝ data.H data.instIPS (data.T f) (data.T f) := by
  sorry

/-- Products of pairings are integrable. -/
theorem pairing_product_integrable (data : GaussianMeasureData D F)
    (f g : SchwartzMap D F) :
    Integrable (fun ω : Configuration D F => ω f * ω g)
      data.measure.toMeasure := by
  sorry

/-- Cross moment equals inner product: E[ω(f)·ω(g)] = ⟨T(f), T(g)⟩_H. -/
theorem cross_moment_eq_covariance (data : GaussianMeasureData D F)
    (f g : SchwartzMap D F) :
    ∫ ω : Configuration D F, (ω f) * (ω g) ∂data.measure.toMeasure =
      @inner ℝ data.H data.instIPS (data.T f) (data.T g) := by
  sorry

/-! ## Integrability -/

/-- Pairings are in Lᵖ for all finite p (Fernique-type bound). -/
theorem pairing_memLp (data : GaussianMeasureData D F)
    (f : SchwartzMap D F) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    Memℒp (fun ω : Configuration D F => ω f) p data.measure.toMeasure := by
  sorry

end GaussianMeasure
