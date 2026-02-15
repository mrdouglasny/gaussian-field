/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nuclear SVD from Spectral Theorem

Given a sequence {y_m} in a separable Hilbert space H with ∑ ‖y_m‖ < ∞,
constructs the singular value decomposition of the associated nuclear
operator A : ℓ² → H, A(e_m) = y_m.

## Main result

`nuclear_sequence_svd`: Produces an adapted ONB {e_n} of H (extending the
right singular vectors), singular values σ_n with ∑ σ_n < ∞, and an
orthogonal matrix W such that y_m = ∑_n σ_n W_{nm} e_n.
-/

import GaussianMeasure.SpectralTheorem

noncomputable section

namespace GaussianMeasure

open TopologicalSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]

/-- ℕ-indexed corollary of the spectral theorem. Converts the generic-ι
    output to ℕ-indexed via separability → Countable, infinite-dim → Infinite. -/
theorem compact_selfAdjoint_spectral_nat
    (h_inf : ¬ FiniteDimensional ℝ H)
    (T : H →L[ℝ] H)
    (hT_sa : IsSelfAdjoint T) (hT_compact : IsCompactOperator T) :
    ∃ (u : ℕ → H) (eigenval : ℕ → ℝ),
      Orthonormal ℝ u ∧
      (⊤ ≤ (Submodule.span ℝ (Set.range u)).topologicalClosure) ∧
      (∀ n, (T : H →ₗ[ℝ] H) (u n) = eigenval n • u n) ∧
      (∀ x, HasSum (fun n => (eigenval n * @inner ℝ _ _ (u n) x) • u n) (T x)) := by
  sorry

/-- **Nuclear Sequence SVD**: Given {y_m} with ∑ ‖y_m‖ < ∞ in a separable
    Hilbert space H, the nuclear operator A(e_m) = y_m admits an SVD with
    an adapted ONB of H.

    Outputs:
    - {e_n} : ℕ → H, an ONB of H
    - σ_n ≥ 0 with ∑ σ_n ≤ ∑ ‖y_m‖
    - W : ℕ → ℕ → ℝ (orthogonal mixing matrix)
    - y_m = ∑_n σ_n W_{nm} e_n -/
theorem nuclear_sequence_svd
    (h_inf : ¬ FiniteDimensional ℝ H)
    (y : ℕ → H) (hy : Summable (fun m => ‖y m‖)) :
    ∃ (e : ℕ → H) (σ : ℕ → ℝ) (W : ℕ → ℕ → ℝ),
      Orthonormal ℝ e ∧
      (⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) ∧
      (∀ n, σ n ≥ 0) ∧
      Summable σ ∧
      (∑' n, σ n ≤ ∑' m, ‖y m‖) ∧
      (∀ m, HasSum (fun n => (σ n * W n m) • e n) (y m)) := by
  sorry

end GaussianMeasure
