/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Target-Indexed Nuclear Factorization

Combines the source-indexed nuclear representation with the nuclear SVD
to produce a target-indexed factorization of any Schwartz-to-Hilbert CLM.

## Main result

`schwartz_clm_target_factorization`: For any CLM T : S(D,F) → H with H
separable and infinite-dimensional, there exist:
- An adapted ONB {eₙ} of H
- An intermediate Hilbert space K (= ℓ²)
- A CLM j : S(D,F) → K
- Vectors vₙ ∈ K with ∑ ‖vₙ‖ < ∞
- Such that ⟨eₙ, T(f)⟩ = ⟨vₙ, j(f)⟩_K

This is the factorization theorem that drives the Gaussian construction.
The key point is that the ONB is *output* (adapted to T's nuclear structure),
not input — the construction fails for arbitrary ONBs.
-/

import GaussianMeasure.NuclearFactorization
import GaussianMeasure.NuclearSVD

noncomputable section

namespace GaussianMeasure

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Target-indexed nuclear factorization for Schwartz CLMs.**

    Any CLM T : S(D,F) → H into a separable infinite-dimensional Hilbert space
    admits a factorization through an intermediate Hilbert space K with an
    adapted ONB. -/
theorem schwartz_clm_target_factorization
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [SeparableSpace H] (h_inf : ¬ FiniteDimensional ℝ H)
    (T : (SchwartzMap D F) →L[ℝ] H) :
    ∃ (e : ℕ → H)
      (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K)
      (j : (SchwartzMap D F) →L[ℝ] K) (v : ℕ → K),
      Orthonormal ℝ e ∧
      (⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) ∧
      Summable (fun n => ‖v n‖) ∧
      ∀ (f : SchwartzMap D F) (n : ℕ),
        @inner ℝ H _ (e n) (T f) = @inner ℝ K _ (v n) (j f) := by
  sorry

end GaussianMeasure
