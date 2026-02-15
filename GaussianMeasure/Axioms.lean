/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Axioms for Gaussian Measure Construction

This file declares the axioms needed for the Gaussian measure construction.
All axioms are standard functional analysis results, independent of any
specific application (QFT, stochastic PDEs, etc.).

## Axiom groups

### Group 1: Spectral theory (2 axioms)
Standard facts about compact operators on Hilbert spaces.
- `compact_operator_eigenspace_finiteDimensional`
- `compact_selfAdjoint_eigenvalues_finite_above_eps`

### Group 2: Hermite basis for Schwartz space (5 axioms)
The multi-dimensional Schwartz space S(D,F) admits a countable basis
{ψ_m} with coefficient CLMs {c_m} satisfying expansion, decay, and growth.
- `schwartzHermiteBasis`
- `schwartzHermiteCoeff`
- `schwartz_hermite_expansion`
- `schwartz_hermite_seminorm_growth`
- `schwartz_hermite_coefficient_decay`

## References
- Conway, "A Course in Functional Analysis", Ch. II, VI
- Reed-Simon, "Methods of Mathematical Physics" Vol. I, §VI
- Gel'fand-Vilenkin, "Generalized Functions" Vol. 4, Ch. 3-4
- Thangavelu, "Lectures on Hermite and Laguerre Expansions", Ch. 1
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

namespace GaussianMeasure

/-! ## Group 1: Spectral Theory Axioms

These are standard facts about compact operators on real Hilbert spaces.
Together with the proved results `compact_selfAdjoint_hasEigenvector` and
`compact_selfAdjoint_orthogonalComplement_iSup_eigenspaces_eq_bot`,
they yield the full spectral theorem for compact self-adjoint operators. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Eigenspaces of compact operators for nonzero eigenvalues are finite-dimensional.

    **Reference**: Conway, Theorem VI.15; Reed-Simon Vol. I, Theorem VI.15.
    **Proof sketch**: The unit ball of the eigenspace is the preimage of a compact
    set under scaling by μ. If the eigenspace were infinite-dimensional, its unit
    ball would not be compact, contradicting compactness of T. -/
axiom compact_operator_eigenspace_finiteDimensional
    {T : E →L[ℝ] E} (hT : IsCompactOperator T) {μ : ℝ} (hμ : μ ≠ 0) :
    FiniteDimensional ℝ (Module.End.eigenspace (T : E →ₗ[ℝ] E) μ)

/-- A compact self-adjoint operator has at most finitely many eigenvalues
    with absolute value exceeding any ε > 0.

    **Reference**: Conway, Corollary VI.16; Reed-Simon Vol. I, Theorem VI.16.
    **Proof sketch**: Eigenvectors for distinct eigenvalues are orthogonal.
    If infinitely many eigenvalues had |μₙ| > ε, the corresponding unit
    eigenvectors would form a bounded sequence with no convergent subsequence
    (being ε-separated), contradicting compactness of T. -/
axiom compact_selfAdjoint_eigenvalues_finite_above_eps
    {T : E →L[ℝ] E} (hT_sa : IsSelfAdjoint T) (hT_compact : IsCompactOperator T)
    {ε : ℝ} (hε : ε > 0) :
    Set.Finite {μ : ℝ | Module.End.HasEigenvalue (T : E →ₗ[ℝ] E) μ ∧ |μ| > ε}

/-! ## Group 2: Hermite Basis for Schwartz Space

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
