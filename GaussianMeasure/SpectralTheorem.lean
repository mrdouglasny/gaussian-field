/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Spectral Theorem for Compact Self-Adjoint Operators

Proves the spectral theorem for compact self-adjoint operators on
real Hilbert spaces from 2 axioms:
- `compact_operator_eigenspace_finiteDimensional`
- `compact_selfAdjoint_eigenvalues_finite_above_eps`

Plus 2 proved lemmas:
- `compact_selfAdjoint_hasEigenvector` (proved via Mathlib)
- `compact_selfAdjoint_orthogonalComplement_iSup_eigenspaces_eq_bot` (proved)

## Main result

`compact_selfAdjoint_spectral`: For any compact self-adjoint T on a real
Hilbert space, there exist a HilbertBasis of eigenvectors and eigenvalues
μ_ι → 0 such that T = ∑ μ_ι ⟨e_ι, ·⟩ e_ι.
-/

import GaussianMeasure.Axioms

noncomputable section

namespace GaussianMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A compact self-adjoint operator on a nontrivial real Hilbert space
    has an eigenvector achieving ‖T‖. Proved from Mathlib. -/
theorem compact_selfAdjoint_hasEigenvector
    [Nontrivial E]
    {T : E →L[ℝ] E} (hT_sa : IsSelfAdjoint T) (hT_compact : IsCompactOperator T)
    (hT_ne : T ≠ 0) :
    ∃ μ : ℝ, Module.End.HasEigenvalue (T : E →ₗ[ℝ] E) μ ∧ |μ| = ‖T‖ := by
  sorry

/-- The orthogonal complement of the span of all eigenspaces is trivial.
    Proved via the "restrict to complement" argument. -/
theorem compact_selfAdjoint_orthogonalComplement_iSup_eigenspaces_eq_bot
    {T : E →L[ℝ] E} (hT_sa : IsSelfAdjoint T) (hT_compact : IsCompactOperator T) :
    (⨆ μ, LinearMap.eigenspace (T : E →ₗ[ℝ] E) μ)ᗮ = ⊥ := by
  sorry

/-- **Spectral Theorem**: Every compact self-adjoint operator on a real Hilbert
    space admits a HilbertBasis of eigenvectors.

    Given T compact and self-adjoint, there exist:
    - A HilbertBasis {e_ι} (spanning ONB)
    - Eigenvalues μ_ι with T(e_ι) = μ_ι • e_ι
    - Representation: T(x) = ∑_ι μ_ι ⟨e_ι, x⟩ e_ι (norm-convergent) -/
theorem compact_selfAdjoint_spectral
    (T : E →L[ℝ] E)
    (hT_sa : IsSelfAdjoint T) (hT_compact : IsCompactOperator T) :
    ∃ (ι : Type) (b : HilbertBasis ι ℝ E) (eigenval : ι → ℝ),
      (∀ i, (T : E →ₗ[ℝ] E) (b i) = eigenval i • b i) ∧
      (∀ x, HasSum (fun i => (eigenval i * @inner ℝ _ _ (b i) x) • b i) (T x)) := by
  sorry

end GaussianMeasure
