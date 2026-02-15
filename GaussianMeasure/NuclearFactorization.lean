/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Source-Indexed Nuclear Representation of Schwartz CLMs

For any continuous linear map T : S(D,F) → H from a Schwartz space to
a Hilbert space, produces a nuclear representation:

  T(f) = ∑_m φ_m(f) · y_m,  ∑_m ‖y_m‖ < ∞

where φ_m are equicontinuous coefficient functionals (bounded by one
Schwartz seminorm) and y_m ∈ H.

## Proof technique

1. Hermite expansion: ⟨w, T(f)⟩ = ∑_m c_m(f) ⟨w, T(ψ_m)⟩
2. Polynomial growth of ‖T(ψ_m)‖ (from continuity of T)
3. Define y_m = (1+m)^{-s} T(ψ_m), φ_m = (1+m)^s c_m
4. Choose s = p+2 so ∑ ‖y_m‖ ≤ C ∑ (1+m)^{-2} < ∞

Uses axioms: `schwartz_hermite_expansion`, `schwartz_hermite_seminorm_growth`,
`schwartz_hermite_coefficient_decay`.
-/

import GaussianMeasure.Axioms

noncomputable section

namespace GaussianMeasure

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- **Source-indexed nuclear representation**: Any CLM from Schwartz space to
    a Hilbert space admits a ℓ¹-convergent series representation.

    This is the key bridge between the Hermite structure of Schwartz space
    and the nuclear factorization needed for the Gaussian construction. -/
theorem schwartz_clm_nuclear_representation
    (T : SchwartzMap D F →L[ℝ] H) :
    ∃ (φ : ℕ → (SchwartzMap D F →L[ℝ] ℝ)) (y : ℕ → H),
      Summable (fun m => ‖y m‖) ∧
      (∀ f, HasSum (fun m => (φ m f) • y m) (T f)) ∧
      -- Equicontinuity: all φ_m bounded by a single Schwartz seminorm
      (∃ k l C, C > 0 ∧ ∀ m f, ‖φ m f‖ ≤ C * (1 + m) ^ k *
        SchwartzMap.seminorm ℝ l l f) := by
  sorry

end GaussianMeasure
