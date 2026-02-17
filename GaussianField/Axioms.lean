/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Schwartz Space as a Nuclear Space

Provides the `NuclearSpace` instance for `SchwartzMap D F` using 5 axioms
about the Hermite basis. The axioms encode standard results about
multi-dimensional Hermite functions that are not yet in Mathlib.

## Axioms

- `schwartzHermiteBasis` — countable Schwartz basis (Hermite functions)
- `schwartzHermiteCoeff` — coefficient CLMs extracting coordinates
- `schwartz_hermite_expansion` — expansion recovers any scalar CLF
- `schwartz_hermite_seminorm_growth` — polynomial growth of seminorms
- `schwartz_hermite_coefficient_decay` — super-polynomial decay of coefficients

## References
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. 3-4
- Thangavelu, "Lectures on Hermite and Laguerre Expansions", Ch. 1
-/

import GaussianField.NuclearSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

noncomputable section

namespace GaussianField

/-! ## Hermite Basis Axioms for Schwartz Space

The Schwartz space S(D,F) for finite-dimensional D admits a countable basis
of Schwartz functions (tensor products of Hermite functions) with associated
coefficient CLMs. These satisfy expansion, growth, and decay properties
making S(D,F) a nuclear Fréchet space. -/

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Countable Schwartz basis indexed by ℕ (multi-dimensional Hermite functions). -/
axiom schwartzHermiteBasis (D : Type*) (F : Type*)
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ℕ → SchwartzMap D F

/-- Coefficient CLMs: continuous linear functionals extracting coordinates. -/
axiom schwartzHermiteCoeff (D : Type*) (F : Type*)
    [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F] :
    ℕ → (SchwartzMap D F →L[ℝ] ℝ)

/-- The Hermite expansion recovers any continuous linear functional on S(D,F).

    For any scalar CLF φ : S(D,F) →L[ℝ] ℝ and f ∈ S(D,F):
      φ(f) = ∑_m c_m(f) · φ(ψ_m) -/
axiom schwartz_hermite_expansion
    (φ : SchwartzMap D F →L[ℝ] ℝ) (f : SchwartzMap D F) :
    φ f = ∑' m, (schwartzHermiteCoeff D F m f) * φ (schwartzHermiteBasis D F m)

/-- Schwartz seminorm growth: basis elements grow polynomially in the index.

    For each Schwartz seminorm p_{k,l}, there exist C > 0 and s : ℕ such that
      p_{k,l}(ψ_m) ≤ C · (1 + m)^s -/
axiom schwartz_hermite_seminorm_growth
    (k l : ℕ) : ∃ C > 0, ∃ (s : ℕ),
    ∀ m : ℕ, SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis D F m) ≤ C * (1 + (m : ℝ)) ^ s

/-- Coefficient decay: coefficients decay faster than any polynomial,
    uniformly controlled by a single Schwartz seminorm.

    For every k : ℕ there exist C > 0 and a Schwartz seminorm index q
    such that for all f ∈ S(D,F) and m ∈ ℕ:
      |c_m(f)| · (1 + m)^k ≤ C · p_q(f) -/
axiom schwartz_hermite_coefficient_decay
    (k : ℕ) : ∃ C > 0, ∃ (q : ℕ × ℕ),
    ∀ (f : SchwartzMap D F) (m : ℕ),
      |schwartzHermiteCoeff D F m f| * (1 + (m : ℝ)) ^ k ≤
        C * SchwartzMap.seminorm ℝ q.1 q.2 f

/-- **Schwartz space is a nuclear Fréchet space.**

The instance uses the Schwartz seminorm family `(k, l) ↦ p_{k,l}` and the
Hermite basis {ψ_m} with coefficient CLMs {c_m}. The 5 axioms above
provide the proof obligations. -/
noncomputable instance schwartz_nuclearSpace :
    NuclearSpace (SchwartzMap D F) where
  ι := ℕ × ℕ
  p := fun ⟨k, l⟩ => SchwartzMap.seminorm ℝ k l
  h_with := schwartz_withSeminorms ℝ D F
  basis := schwartzHermiteBasis D F
  coeff := schwartzHermiteCoeff D F
  expansion := schwartz_hermite_expansion
  basis_growth := fun ⟨k, l⟩ => schwartz_hermite_seminorm_growth k l
  coeff_decay := fun k => schwartz_hermite_coefficient_decay k

end GaussianField
