/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Isotropic covariance and lattice→continuum convergence on the rectangular lattice

Manifestly-correct discretization of the rectangular torus `T = S¹(Lt) × S¹(Ls)`:
a **single isotropic spacing `a`** on the heterogeneous lattice
`AsymLatticeSites Nt Ns = ZMod Nt × ZMod Ns` with `a = Lt/Nt = Ls/Ns`. The lattice
Laplacian `−Δ_a` is isotropic (same `1/a²` in both directions); the rectangle is
carried entirely by `Nt ≠ Ns` (the boundary condition). This replaces the
metric-inconsistent `N×N` + geometric-mean-spacing construction.

## Main definitions

- `spectralLatticeCovarianceAsym` — `Q^{-1/2}` CLM on `AsymLatticeField Nt Ns`,
  separable eigendecomposition `λ = latticeEigenvalue1d Nt a · + latticeEigenvalue1d Ns a ·`
- `latticeCovarianceAsymGJ`, `latticeGaussianMeasureAsym` — GJ-normalised covariance/measure

## Main results (to prove)

- `lattice_green_tendsto_continuum_asym` — the lattice covariance converges to
  `greenFunctionBilinear` on `AsymTorusTestFunction Lt Ls` (the rectangular-torus Green's
  function, dispersion `(2πp/Lt)² + (2πq/Ls)²`); now mathematically TRUE and `Lt`-uniform,
  the honest version of the cylinder-OS0 "delta".

Implementation plan: pphi2 `docs/cylinder-isotropic-lattice-implementation.md`.

STATUS: Phase-1a scaffold (definitions + headline statements). Proofs are `sorry`,
to be filled per the implementation plan (separable spectral covariance from the 1D
DFT pieces; Tannery convergence reusing `latticeDFTCoeff1d_quadratic_bound`).
-/

import Lattice.Covariance
import Lattice.Convergence
import Torus.AsymmetricTorus
import HeatKernel.Bilinear

noncomputable section

namespace GaussianField

open MeasureTheory Filter Topology

variable (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]

/-! ## Isotropic covariance on the heterogeneous lattice -/

/-- The isotropic spectral lattice covariance `T = Q^{-1/2}` on the rectangular lattice
`ZMod Nt × ZMod Ns` with single spacing `a`. To be built separably from the 1D DFT
eigendecomposition (eigenvalues `latticeEigenvalue1d Nt a · + latticeEigenvalue1d Ns a ·`,
eigenvectors = products of 1D DFT modes), mirroring `spectralLatticeCovariance`. -/
noncomputable def spectralLatticeCovarianceAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (_ha : 0 < a) (_hmass : 0 < mass) :
    AsymLatticeField Nt Ns →L[ℝ] ell2' := sorry

/-- Glimm–Jaffe-aligned isotropic covariance: `(a²)^{-1/2} • spectralLatticeCovarianceAsym`
(the `d = 2` Riemann-sum normalisation; cell area `a²`, volume `Nt·Ns·a² = Lt·Ls`). -/
noncomputable def latticeCovarianceAsymGJ (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    AsymLatticeField Nt Ns →L[ℝ] ell2' :=
  (Real.sqrt (a ^ 2))⁻¹ • spectralLatticeCovarianceAsym Nt Ns a mass ha hmass

/-! ## The lattice→continuum convergence (the cylinder-OS0 delta, now true) -/

/-- **Isotropic rectangular lattice → continuum Green's function.**

For a sequence of isotropic lattices `ZMod (Nt k) × ZMod (Ns k)` with spacing `a k`
satisfying `(Nt k)·(a k) = Lt` and `(Ns k)·(a k) = Ls` (so the discretization is exactly
isotropic and lands on the rectangle), the lattice two-point function converges to the
continuum rectangular-torus Green's function. The `Lt ≠ Ls` obstruction of the
geometric-mean construction is gone, and the bounds are `Lt`-uniform.

Proof route (port of `lattice_green_tendsto_continuum`): Tannery over `ℕ × ℕ` with
per-direction 1D eigenvalue convergence `latticeEigenvalue1d (Nt k) (a k) p → (2πp/Lt)²`
(and `Ls`) and the reused domination `latticeDFTCoeff1d_quadratic_bound Lt` / `… Ls`. -/
theorem lattice_green_tendsto_continuum_asym
    (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hLt : ∀ k, (Nt k : ℝ) * a k = Lt) (hLs : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Tendsto a atTop (nhds 0))
    (f g : AsymTorusTestFunction Lt Ls) :
    Tendsto
      (fun k =>
        haveI := hNt k; haveI := hNs k
        covariance (spectralLatticeCovarianceAsym (Nt k) (Ns k) (a k) mass (ha k) hmass)
          (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x f)
          (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x g))
      atTop
      (nhds (greenFunctionBilinear mass hmass f g)) := sorry

end GaussianField

end
