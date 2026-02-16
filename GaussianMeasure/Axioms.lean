/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Axioms for Gaussian Measure Construction

This file declares the 5 axioms needed for the Gaussian measure construction.
All axioms are standard functional analysis results, independent of any
specific application (QFT, stochastic PDEs, etc.).

## Axiom groups

### Hermite basis for Schwartz space (5 axioms)
The multi-dimensional Schwartz space S(D,F) admits a countable basis
{ψ_m} with coefficient CLMs {c_m} satisfying expansion, decay, and growth.
- `schwartzHermiteBasis`
- `schwartzHermiteCoeff`
- `schwartz_hermite_expansion`
- `schwartz_hermite_seminorm_growth`
- `schwartz_hermite_coefficient_decay`

## References
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. 3-4
- Thangavelu, "Lectures on Hermite and Laguerre Expansions", Ch. 1
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv

noncomputable section

namespace GaussianMeasure

/-! ## Hermite Basis for Schwartz Space

The Schwartz space S(D,F) for finite-dimensional D admits a countable basis
of Schwartz functions (tensor products of Hermite functions) with associated
coefficient CLMs. These satisfy:
1. **Expansion**: Any CLM out of S(D,F) can be recovered from coefficients
2. **Growth**: Basis elements have polynomial Schwartz seminorm growth
3. **Decay**: Coefficients decay super-polynomially

These are polymorphic in (D, F) — they work for any S(ℝᵈ, F). -/

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

    For any CLM w ∈ (S(D,F))* (represented via inner product on a Hilbert space H)
    and any f ∈ S(D,F):
      ⟨w, T(f)⟩ = ∑_m c_m(f) · ⟨w, T(ψ_m)⟩

    where ψ_m = schwartzHermiteBasis and c_m = schwartzHermiteCoeff.
    The sum converges because c_m(f) decays super-polynomially and
    ⟨w, T(ψ_m)⟩ grows at most polynomially. -/
axiom schwartz_hermite_expansion
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : SchwartzMap D F →L[ℝ] H) (w : H) (f : SchwartzMap D F) :
    @inner ℝ H _ w (T f) =
    ∑' m, (schwartzHermiteCoeff D F m f) * @inner ℝ H _ w (T (schwartzHermiteBasis D F m))

/-- Schwartz seminorm growth: basis elements grow polynomially in the index.

    For each Schwartz seminorm p_{k,l}, there exist C > 0 and s ≥ 0 such that
      p_{k,l}(ψ_m) ≤ C · (1 + m)^s

    This follows from the eigenvalue structure of the harmonic oscillator:
    Hermite functions are eigenfunctions of H = -Δ + |x|², and seminorms
    are controlled by powers of H. -/
axiom schwartz_hermite_seminorm_growth
    (k l : ℕ) : ∃ (C : ℝ) (s : ℝ), C > 0 ∧ s ≥ 0 ∧
    ∀ m : ℕ, SchwartzMap.seminorm ℝ k l (schwartzHermiteBasis D F m) ≤ C * (1 + (m : ℝ)) ^ s

/-- Coefficient decay: coefficients decay faster than any polynomial,
    uniformly controlled by a single Schwartz seminorm.

    For every k ≥ 0 there exist C > 0 and a Schwartz seminorm index q
    such that for all f ∈ S(D,F) and m ∈ ℕ:
      |c_m(f)| · (1 + m)^k ≤ C · p_q(f)

    This is the Schwartz-space analogue of "smooth functions have rapidly
    decaying Fourier coefficients" — the equicontinuity version needed for
    the nuclear representation theorem. -/
axiom schwartz_hermite_coefficient_decay
    (k : ℝ) : ∃ (C : ℝ) (q : ℕ × ℕ), C > 0 ∧
    ∀ (f : SchwartzMap D F) (m : ℕ),
      |schwartzHermiteCoeff D F m f| * (1 + (m : ℝ)) ^ k ≤
        C * SchwartzMap.seminorm ℝ q.1 q.2 f

end GaussianMeasure
