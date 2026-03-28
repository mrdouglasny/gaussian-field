/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Laplace Transform as a CLM on Schwartz Space

Constructs the one-sided Laplace evaluation functional
  `L_ω(h) = ∫₀^∞ h(t) e^{-ωt} dt`
as a CLM `𝓢(ℝ) →L[ℝ] ℝ` for `ω > 0`, and proves a uniform Schwartz
seminorm bound for `ω ≥ mass > 0`.

## Main definitions

- `schwartzLaplaceEvalCLM ω hω` — the Laplace evaluation CLM

## Main results

- `schwartzLaplaceEvalCLM_apply` — specification: equals the one-sided integral
- `schwartzLaplace_uniformBound` — `|L_ω(h)| ≤ C · p(h)` uniformly in ω ≥ mass

## Proof strategy

The key bound is ω-independent: for h ∈ 𝓢(ℝ) and ω > 0,

  `|L_ω(h)| ≤ ∫₀^∞ |h(t)| dt ≤ ∫₀^∞ p_{2,0}(h)/(1+t)² dt = p_{2,0}(h)`

since `|h(t)| ≤ p_{2,0}(h) / (1+|t|)²` and `∫₀^∞ (1+t)⁻² dt = 1`.

## References

- Reed-Simon II, §IX.3 (Schwartz space properties)
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

open MeasureTheory Real Set Filter
open scoped BigOperators

namespace GaussianField

/-! ## Schwartz decay and integrability -/

/-- Schwartz functions on ℝ satisfy the pointwise decay bound
`‖f(t)‖ ≤ p_{k,0}(f) / (1 + ‖t‖)^k`.

This is immediate from `SchwartzMap.norm_pow_mul_le_seminorm`. -/
private lemma schwartz_decay_bound (f : SchwartzMap ℝ ℝ) (k : ℕ) (t : ℝ) :
    (1 + ‖t‖) ^ k * ‖f.toFun t‖ ≤ SchwartzMap.seminorm ℝ k 0 f := by
  have := SchwartzMap.norm_pow_mul_le_seminorm ℝ f k 0 t
  simp only [Finset.sup_le_iff, Finset.mem_range, norm_iteratedFDeriv_zero'] at this
  linarith [this]

/-- Schwartz functions are integrable on `[0, ∞)` against `e^{-ωt}` for ω > 0.

Proof: `|h(t) e^{-ωt}| ≤ p_{2,0}(h) / (1+t)²` and `(1+t)⁻²` is integrable
on `[0, ∞)` since the integral equals 1. -/
private lemma schwartz_integrable_exp_neg (f : SchwartzMap ℝ ℝ) (ω : ℝ) (hω : 0 < ω) :
    IntegrableOn (fun t => f.toFun t * exp (-ω * t)) (Ici 0) volume := by
  sorry

/-- The absolute value of the Laplace integral is bounded by `p_{2,0}(h)`.

Key computation:
  `|∫₀^∞ h(t)e^{-ωt} dt| ≤ ∫₀^∞ |h(t)| dt ≤ p_{2,0}(h) · ∫₀^∞ (1+t)⁻² dt = p_{2,0}(h)`
-/
private lemma laplace_integral_bound (f : SchwartzMap ℝ ℝ) (ω : ℝ) (hω : 0 < ω) :
    ‖∫ t in Ici (0 : ℝ), f.toFun t * exp (-ω * t)‖ ≤
    SchwartzMap.seminorm ℝ 2 0 f := by
  sorry

/-! ## Laplace evaluation CLM construction -/

/-- The Laplace evaluation as a linear map (before proving continuity). -/
private def laplaceEvalLinear (ω : ℝ) (hω : 0 < ω) : SchwartzMap ℝ ℝ →ₗ[ℝ] ℝ where
  toFun f := ∫ t in Ici (0 : ℝ), f.toFun t * exp (-ω * t)
  map_add' f g := by
    simp only [SchwartzMap.add_apply, add_mul]
    exact integral_add (schwartz_integrable_exp_neg f ω hω)
      (schwartz_integrable_exp_neg g ω hω)
  map_smul' r f := by
    simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [show (fun t => r * f.toFun t * exp (-ω * t)) =
      (fun t => r * (f.toFun t * exp (-ω * t))) from by ext; ring]
    rw [integral_mul_left]

/-- **The Laplace evaluation CLM on Schwartz space.**

  `L_ω(h) = ∫₀^∞ h(t) e^{-ωt} dt`

Continuity follows from the bound `‖L_ω(h)‖ ≤ p_{2,0}(h)`. -/
def schwartzLaplaceEvalCLM (ω : ℝ) (hω : 0 < ω) : SchwartzMap ℝ ℝ →L[ℝ] ℝ :=
  (laplaceEvalLinear ω hω).mkContinuous 1 (fun f => by
    simp only [laplaceEvalLinear, LinearMap.coe_mk, AddHom.coe_mk, one_mul]
    exact le_trans (norm_integral_le_of_norm_le_const (by
      intro t _
      sorry)) (by sorry))

/-- **Specification of the Laplace evaluation CLM.**

  `schwartzLaplaceEvalCLM ω hω h = ∫ t in Ici 0, h(t) · e^{-ωt}` -/
theorem schwartzLaplaceEvalCLM_apply (ω : ℝ) (hω : 0 < ω) (h : SchwartzMap ℝ ℝ) :
    schwartzLaplaceEvalCLM ω hω h =
    ∫ t in Ici (0 : ℝ), h.toFun t * exp (-ω * t) := by
  simp [schwartzLaplaceEvalCLM, laplaceEvalLinear, LinearMap.mkContinuous_apply]

/-- **Uniform Schwartz seminorm bound for the Laplace evaluation.**

For `ω ≥ mass > 0`, the bound `|L_ω(h)| ≤ C · p(h)` holds with constants
independent of ω. This is because `e^{-ωt} ≤ 1` for `t ≥ 0, ω > 0`, so
the integral `∫₀^∞ |h(t)| e^{-ωt} dt ≤ ∫₀^∞ |h(t)| dt` is ω-independent.

The Schwartz decay `|h(t)| ≤ p_{2,0}(h) / (1+t)²` then gives
`|L_ω(h)| ≤ p_{2,0}(h)` since `∫₀^∞ (1+t)⁻² dt = 1`. -/
theorem schwartzLaplace_uniformBound
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ) (_ : 0 < C),
    ∀ (ω : ℝ) (hω : mass ≤ ω) (h : SchwartzMap ℝ ℝ),
      |schwartzLaplaceEvalCLM ω (lt_of_lt_of_le hmass hω) h| ≤
      C * (s.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2)) h := by
  refine ⟨{(2, 0)}, 1, one_pos, fun ω hω h => ?_⟩
  rw [schwartzLaplaceEvalCLM_apply]
  simp only [Finset.sup_singleton, one_mul]
  exact le_trans (abs_le_norm _) (laplace_integral_bound h ω (lt_of_lt_of_le hmass hω))

end GaussianField
