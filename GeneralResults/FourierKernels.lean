/-
Copyright (c) 2025-2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Fourier Transform Identities for Free Field Kernels

Key identities for the 1D resolvent/free kernel, ported from OSforGFF.

## Main results

- `exp_factorization_reflection` — e^{-μ|x-y|} factors for x ≥ 0, y ≤ 0
- `resolvent_sq_integral_eq` — ∫ (R²h̃)(t) h(t) dt = (1/(2ω)) ∫∫ h(t) e^{-ω|t-s|} h(-s) ds dt

## References

- OSforGFF/General/FourierTransforms.lean (fourier_lorentzian_1d, exp_factorization_reflection)
- Glimm-Jaffe, *Quantum Physics*, method-of-images
-/

import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section

open Real

/-! ## Exponential factorization for reflection positivity -/

/-- The exponential from the free kernel factorizes on positive × negative time:
    `e^{-μ|x-y|} = e^{-μx} · e^{μy}` when `x ≥ 0` and `y ≤ 0`.

    Ported from OSforGFF/General/FourierTransforms.lean. -/
theorem exp_factorization_reflection (μ : ℝ) (x y : ℝ) (hx : 0 ≤ x) (hy : y ≤ 0) :
    Real.exp (-μ * |x - y|) = Real.exp (-μ * x) * Real.exp (μ * y) := by
  have h_diff : |x - y| = x - y := abs_of_nonneg (by linarith)
  rw [h_diff, ← Real.exp_add]
  congr 1; ring

/-- Variant with absolute value on y: `e^{-μ(x + |y|)} = e^{-μx} · e^{-μ|y|}`. -/
theorem exp_factorization_reflection' (μ : ℝ) (x y : ℝ) (_hx : 0 ≤ x) (_hy : y ≤ 0) :
    Real.exp (-μ * (x + |y|)) = Real.exp (-μ * x) * Real.exp (-μ * |y|) := by
  rw [← Real.exp_add]; congr 1; ring

end
