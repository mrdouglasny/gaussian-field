/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Heat Kernel

Defines the heat kernel on the finite lattice as the matrix exponential
of the negative Laplacian: `K_t = exp(-t · (-Δ_a))`.

## Main definitions

- `negLaplacianMatrix` — the matrix `-Δ_a` (mass-free)
- `latticeHeatKernelMatrix` — `K_t = exp(-t · (-Δ_a))`

## Main theorems

- `latticeHeatKernelMatrix_semigroup` — `K_{s+t} = K_s · K_t`
- `latticeHeatKernelMatrix_zero` — `K_0 = I`
- `latticeHeatKernelMatrix_isHermitian` — `K_tᵀ = K_t` (symmetry)
- `latticeHeatKernelMatrix_commute` — commutation with symmetries

## Design notes

The heat kernel uses eigenvalues of `-Δ_a` alone (no mass). Mass enters
only through the Green's function / propagator:
  `G_m = ∫₀^∞ e^{-tm²} K_t dt = (-Δ + m²)⁻¹`

This follows the mass-separation convention from `HeatKernel/Bilinear.lean`,
ensuring tensor product factorization: `K_t^{2D} = K_t^{1D} ⊗ K_t^{1D}`.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1, §19
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Lattice.SpectralCovariance
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

noncomputable section

namespace GaussianField

open Matrix

-- `NormedSpace.exp` applied to matrices gives the matrix exponential
-- (not `Real.exp` which is ℝ → ℝ)

variable (d N : ℕ) [NeZero N]

/-! ## Negative Laplacian matrix -/

/-- The matrix of `-Δ_a` (the negative Laplacian, without mass).
Defined as `massOperatorMatrix` at mass = 0, which gives
`(-Δ_a)(x,y) = ⟨δ_x, (-Δ_a)(δ_y)⟩`. -/
def negLaplacianMatrix (a : ℝ) :
    Matrix (FinLatticeSites d N) (FinLatticeSites d N) ℝ :=
  massOperatorMatrix d N a 0

/-- `-Δ_a` is symmetric (Hermitian). -/
theorem negLaplacianMatrix_isHermitian (a : ℝ) :
    (negLaplacianMatrix d N a).IsHermitian :=
  massOperatorMatrix_isHermitian d N a 0

/-! ## Heat kernel matrix -/

/-- **Lattice heat kernel matrix.**

`K_t = exp(-t · (-Δ_a))` where `-Δ_a` is the negative Laplacian matrix
(without mass). This is a positive semidefinite symmetric matrix for `t ≥ 0`.

The matrix exponential is `exp(A) = Σ_{n=0}^∞ A^n / n!`, convergent for
any matrix (finite-dimensional normed algebra). -/
def latticeHeatKernelMatrix (a t : ℝ) :
    Matrix (FinLatticeSites d N) (FinLatticeSites d N) ℝ :=
  NormedSpace.exp (-t • negLaplacianMatrix d N a)

/-! ## Semigroup and identity -/

/-- **Heat kernel semigroup property:** `K_{s+t} = K_s · K_t`.

Proof: `exp(-(s+t)A) = exp(-sA + -tA) = exp(-sA) · exp(-tA)` since
`-sA` and `-tA` commute (both are scalar multiples of `A`). -/
theorem latticeHeatKernelMatrix_semigroup (a s t : ℝ) :
    latticeHeatKernelMatrix d N a (s + t) =
    latticeHeatKernelMatrix d N a s * latticeHeatKernelMatrix d N a t := by
  simp only [latticeHeatKernelMatrix, neg_add, add_smul]
  exact Matrix.exp_add_of_commute _ _
    ((Commute.refl (negLaplacianMatrix d N a)).smul_right (-t) |>.smul_left (-s))

/-- **Heat kernel at t = 0 is the identity:** `K_0 = I`. -/
theorem latticeHeatKernelMatrix_zero (a : ℝ) :
    latticeHeatKernelMatrix d N a 0 = 1 := by
  simp only [latticeHeatKernelMatrix, neg_zero, zero_smul, NormedSpace.exp_zero]

/-! ## Symmetry -/

/-- **Heat kernel is symmetric:** `K_tᵀ = K_t`.

Since `-Δ_a` is symmetric, so is `-t • (-Δ_a)`, and therefore
so is `exp(-t · (-Δ_a))`. -/
theorem latticeHeatKernelMatrix_isHermitian (a t : ℝ) :
    (latticeHeatKernelMatrix d N a t).IsHermitian := by
  simp only [latticeHeatKernelMatrix]
  apply Matrix.IsHermitian.exp
  rw [Matrix.IsHermitian, conjTranspose_smul, star_trivial,
    (negLaplacianMatrix_isHermitian d N a).eq]

/-! ## Commutation with symmetries -/

/-- Any matrix commuting with `-Δ_a` also commutes with the heat kernel `K_t`.

This is the key structural result: proving `[U, Δ] = 0` gives heat kernel
invariance for free, via Mathlib's `Commute.exp_right`. -/
theorem latticeHeatKernelMatrix_commute (a t : ℝ)
    (U : Matrix (FinLatticeSites d N) (FinLatticeSites d N) ℝ)
    (hU : Commute U (negLaplacianMatrix d N a)) :
    Commute U (latticeHeatKernelMatrix d N a t) := by
  simp only [latticeHeatKernelMatrix]
  exact (hU.smul_right (-t)).exp_right

end GaussianField
