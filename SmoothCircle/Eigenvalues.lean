/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Laplacian Eigenvalues on the Circle

Provides the `HasLaplacianEigenvalues` instance for `SmoothMap_Circle L ℝ`,
giving eigenvalues `(2π·fourierFreq(n)/L)²` for the Laplacian `-d²/dx²`
on the circle `S¹_L = ℝ/Lℤ`.

## Main results

- `circleHasLaplacianEigenvalues` — eigenvalues of -Δ on S¹_L

## Mathematical background

The real Fourier basis on S¹_L is indexed by ℕ via `fourierFreq`:
- n = 0: constant mode, eigenvalue 0
- n = 2k-1: cos(2πkx/L), eigenvalue (2πk/L)²
- n = 2k: sin(2πkx/L), eigenvalue (2πk/L)²

The eigenvalue at index n is `(2π·fourierFreq(n)/L)²`.
-/

import SmoothCircle.Nuclear
import HeatKernel.Bilinear

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

/-- **Laplacian eigenvalues on the circle S¹_L.**

The eigenvalue of `-d²/dx²` for the n-th real Fourier mode is
`(2π · fourierFreq(n) / L)²`. The `fourierFreq` map sends:
- 0 ↦ 0 (constant mode)
- 2k-1 ↦ k (cosine modes)
- 2k ↦ k (sine modes)

So the eigenvalue is 0 for the constant mode and `(2πk/L)²` for the
k-th cosine/sine pair. -/
instance circleHasLaplacianEigenvalues :
    HasLaplacianEigenvalues (SmoothMap_Circle L ℝ) where
  eigenvalue n :=
    (2 * Real.pi * (SmoothMap_Circle.fourierFreq n : ℝ) / L) ^ 2
  eigenvalue_nonneg _ := sq_nonneg _

end GaussianField
