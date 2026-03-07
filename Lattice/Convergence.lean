/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice-to-Continuum Green's Function Convergence

States the convergence of the lattice covariance bilinear form (for restricted
torus test functions) to the continuum Green's function as the lattice spacing
goes to zero.

## Main results

- `lattice_green_tendsto_continuum` — (axiom) lattice covariance → continuum Green's function

## Mathematical background

On the periodic lattice (ℤ/Nℤ)^d with spacing a = L/N, the mass matrix
Q = -Δ_a + m² is circulant, hence diagonalized by the DFT basis with
eigenvalues:

  `λ_k = (4/a²) Σ_i sin²(πk_i/N) + m²`

The lattice covariance of restricted test functions is:

  `Σ_k λ_k⁻¹ · c_k(r_N f) · c_k(r_N g)`

As N → ∞ (a = L/N → 0), each eigenvalue converges to the continuum eigenvalue:

  `(4N²/L²) sin²(πn/N) → (2πn/L)²`

by the asymptotic `sin(x)/x → 1`. The DFT coefficients of the restricted
test function converge to the continuum Fourier coefficients by Riemann sum
convergence. Dominated convergence (with bound `|c_m(f)| |c_m(g)| / m²`)
yields convergence of the full spectral sum.

## Proof strategy

1. Express the lattice covariance using DFT diagonalization of the circulant
   mass matrix (Plancherel identity for circulant matrices)
2. Show mode-by-mode convergence using `sin(πn/N)/(πn/N) → 1`
   (`Real.isEquivalent_sin` in Mathlib)
3. Bound each term by `|coeff_n(f)| · |coeff_n(g)| / mass²` (summable
   by rapid decay of Schwartz/DMS coefficients)
4. Apply `tendsto_tsum_of_dominated_convergence`

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Lattice.Covariance
import Torus.Evaluation
import HeatKernel.Bilinear
import SmoothCircle.Eigenvalues

noncomputable section

namespace GaussianField

open Filter MeasureTheory

variable (L : ℝ) [hL : Fact (0 < L)]

/-- **Lattice covariance converges to the continuum Green's function.**

For smooth torus test functions `f, g ∈ C∞(T²_L)`:

  `covariance(T_N)(ι*f, ι*g) → G_L(f, g)`

where `T_N = latticeCovariance` is the lattice covariance CLM,
`ι*f = evalTorusAtSite(·)(f)` restricts f to lattice sites, and
`G_L = greenFunctionBilinear` is the continuum Green's function.

The key ingredients are:
1. **DFT diagonalization**: The mass matrix on `(ℤ/Nℤ)²` is circulant,
   so the abstract `massEigenvalues` equal the explicit
   `(4/a²) sin²(πk/N) + m²` (up to ordering).
2. **Eigenvalue convergence**: `(4N²/L²) sin²(πn/N) → (2πn/L)²` for
   each fixed mode n, by `sin(x)/x → 1`.
3. **Coefficient convergence**: DFT coefficients of restricted test
   functions converge to continuum Fourier coefficients (Riemann sums).
4. **Domination**: Each term is bounded by `|c_n(f)|·|c_n(g)|/mass²`,
   which is summable by rapid decay of DMS coefficients.
5. **DCT**: Apply `tendsto_tsum_of_dominated_convergence`.

Reference: Glimm-Jaffe §6.1, Simon Ch. I. -/
axiom lattice_green_tendsto_continuum
    (mass : ℝ) (hmass : 0 < mass)
    (f g : TorusTestFunction L) :
    Tendsto
      (fun N : ℕ =>
        covariance
          (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
            (circleSpacing_pos L (N + 1)) hmass)
          (fun x => evalTorusAtSite L (N + 1) x f)
          (fun x => evalTorusAtSite L (N + 1) x g))
      atTop
      (nhds (greenFunctionBilinear mass hmass f g))

end GaussianField

end
