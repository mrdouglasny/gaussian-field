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

- `finiteLaplacianAsym` — isotropic nearest-neighbour Laplacian on `ZMod Nt × ZMod Ns`
- `massOperatorAsym` / `massOperatorMatrixAsym` — the massive operator `Q = -Δ_a + m²`
- `massEigenvaluesAsym` / `massEigenvectorBasisAsym` — Hermitian spectral data of `Q`
- `spectralLatticeCovarianceAsym` — `Q^{-1/2}` as a CLM `AsymLatticeField Nt Ns →L[ℝ] ell2'`

## Main results (to prove)

- `lattice_green_tendsto_continuum_asym` — the lattice covariance converges to
  `greenFunctionBilinear` on `AsymTorusTestFunction Lt Ls` (the rectangular-torus Green's
  function, dispersion `(2πp/Lt)² + (2πq/Ls)²`); now mathematically TRUE and `Lt`-uniform,
  the honest version of the cylinder-OS0 "delta".

Implementation plan: pphi2 `docs/cylinder-isotropic-lattice-implementation.md`.
-/

import Lattice.Covariance
import Lattice.Convergence
import Torus.AsymmetricTorus
import HeatKernel.Bilinear
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace GaussianField

open MeasureTheory Filter Topology Matrix

variable (Lt Ls : ℝ) [Fact (0 < Lt)] [Fact (0 < Ls)]

/-! ## Isotropic covariance on the heterogeneous lattice -/

/-- Delta function at an asymmetric lattice site. -/
def asymLatticeDelta (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (y : AsymLatticeSites Nt Ns) : AsymLatticeField Nt Ns :=
  fun x => if x = y then 1 else 0

/-- Raw isotropic nearest-neighbour Laplacian on `ZMod Nt × ZMod Ns` with a single spacing `a`.

`(Δφ)(i,j) = (φ(i+1,j) + φ(i-1,j) + φ(i,j+1) + φ(i,j-1) - 4φ(i,j)) / a²`. -/
def finiteLaplacianAsymFun (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (f : AsymLatticeField Nt Ns) (x : AsymLatticeSites Nt Ns) : ℝ :=
  a⁻¹ ^ 2 *
    (f (x.1 + 1, x.2) +
     f (x.1 - 1, x.2) +
     f (x.1, x.2 + 1) +
     f (x.1, x.2 - 1) -
     4 * f x)

/-- The isotropic nearest-neighbour Laplacian as a linear map. -/
def finiteLaplacianAsymLM (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) :
    AsymLatticeField Nt Ns →ₗ[ℝ] AsymLatticeField Nt Ns where
  toFun := finiteLaplacianAsymFun Nt Ns a
  map_add' := by
    intro f g
    funext x
    simp only [finiteLaplacianAsymFun, Pi.add_apply]
    ring
  map_smul' := by
    intro r f
    funext x
    simp only [finiteLaplacianAsymFun, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The isotropic nearest-neighbour Laplacian as a CLM on the asymmetric lattice. -/
noncomputable def finiteLaplacianAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ) :
    AsymLatticeField Nt Ns →L[ℝ] AsymLatticeField Nt Ns :=
  { finiteLaplacianAsymLM Nt Ns a with
    cont := (finiteLaplacianAsymLM Nt Ns a).continuous_of_finiteDimensional }

/-- Translation reindexing (forward) on the heterogeneous lattice: shifting the
second factor by `+v` is the same as shifting the first by `-v`. Periodicity is
automatic since `AsymLatticeSites Nt Ns` is a finite additive group. -/
private lemma asym_sum_mul_translate {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]
    (h k : AsymLatticeField Nt Ns) (v : AsymLatticeSites Nt Ns) :
    ∑ x, h x * k (x + v) = ∑ x, h (x - v) * k x := by
  symm
  exact Fintype.sum_equiv (Equiv.addRight (-v))
    (fun x => h (x - v) * k x) (fun x => h x * k (x + v))
    (fun x => by simp [sub_eq_add_neg])

/-- Translation reindexing (backward) on the heterogeneous lattice. -/
private lemma asym_sum_mul_translate' {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]
    (h k : AsymLatticeField Nt Ns) (v : AsymLatticeSites Nt Ns) :
    ∑ x, h x * k (x - v) = ∑ x, h (x + v) * k x := by
  symm
  exact Fintype.sum_equiv (Equiv.addRight v)
    (fun x => h (x + v) * k x) (fun x => h x * k (x - v))
    (fun x => by simp [add_sub_cancel_right])

/-- The asymmetric isotropic Laplacian is self-adjoint in the counting inner product.

This is the heterogeneous analogue of `finiteLaplacian_selfAdjoint`: the same periodic
reindexing argument on the product lattice `ZMod Nt × ZMod Ns`, shifting in the two
factors `e₁ = (1,0)` and `e₂ = (0,1)` separately. -/
theorem finiteLaplacianAsym_selfAdjoint (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a : ℝ)
    (f g : AsymLatticeField Nt Ns) :
    ∑ x, f x * (finiteLaplacianAsym Nt Ns a g) x =
    ∑ x, (finiteLaplacianAsym Nt Ns a f) x * g x := by
  change ∑ x, f x * finiteLaplacianAsymFun Nt Ns a g x =
    ∑ x, finiteLaplacianAsymFun Nt Ns a f x * g x
  simp only [finiteLaplacianAsymFun]
  -- Express the four nearest-neighbour shifts as group translations by `e₁`, `e₂`.
  have e1p : ∀ x : AsymLatticeSites Nt Ns,
      ((x.1 + 1, x.2) : AsymLatticeSites Nt Ns) = x + ((1 : ZMod Nt), (0 : ZMod Ns)) := by
    intro x; simp [Prod.ext_iff]
  have e1m : ∀ x : AsymLatticeSites Nt Ns,
      ((x.1 - 1, x.2) : AsymLatticeSites Nt Ns) = x - ((1 : ZMod Nt), (0 : ZMod Ns)) := by
    intro x; simp [Prod.ext_iff]
  have e2p : ∀ x : AsymLatticeSites Nt Ns,
      ((x.1, x.2 + 1) : AsymLatticeSites Nt Ns) = x + ((0 : ZMod Nt), (1 : ZMod Ns)) := by
    intro x; simp [Prod.ext_iff]
  have e2m : ∀ x : AsymLatticeSites Nt Ns,
      ((x.1, x.2 - 1) : AsymLatticeSites Nt Ns) = x - ((0 : ZMod Nt), (1 : ZMod Ns)) := by
    intro x; simp [Prod.ext_iff]
  simp_rw [e1p, e1m, e2p, e2m]
  set e1 : AsymLatticeSites Nt Ns := ((1 : ZMod Nt), (0 : ZMod Ns))
  set e2 : AsymLatticeSites Nt Ns := ((0 : ZMod Nt), (1 : ZMod Ns))
  -- Expand both sides into four shift terms plus the diagonal.
  have lhs_exp : ∀ x : AsymLatticeSites Nt Ns,
      f x * (a⁻¹ ^ 2 * (g (x + e1) + g (x - e1) + g (x + e2) + g (x - e2) - 4 * g x)) =
      a⁻¹ ^ 2 * (f x * g (x + e1)) + a⁻¹ ^ 2 * (f x * g (x - e1)) +
      a⁻¹ ^ 2 * (f x * g (x + e2)) + a⁻¹ ^ 2 * (f x * g (x - e2)) +
      a⁻¹ ^ 2 * (-4 * (f x * g x)) := fun x => by ring
  have rhs_exp : ∀ x : AsymLatticeSites Nt Ns,
      a⁻¹ ^ 2 * (f (x + e1) + f (x - e1) + f (x + e2) + f (x - e2) - 4 * f x) * g x =
      a⁻¹ ^ 2 * (f (x + e1) * g x) + a⁻¹ ^ 2 * (f (x - e1) * g x) +
      a⁻¹ ^ 2 * (f (x + e2) * g x) + a⁻¹ ^ 2 * (f (x - e2) * g x) +
      a⁻¹ ^ 2 * (-4 * (f x * g x)) := fun x => by ring
  simp_rw [lhs_exp, rhs_exp, Finset.sum_add_distrib, ← Finset.mul_sum]
  -- Reindex the four shift sums on the left to match the right; diagonal is shared.
  rw [asym_sum_mul_translate f g e1, asym_sum_mul_translate' f g e1,
    asym_sum_mul_translate f g e2, asym_sum_mul_translate' f g e2]
  ring

/-- Massive operator on the asymmetric lattice: `Q = -Δ_a + m²`. -/
def massOperatorAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ) :
    AsymLatticeField Nt Ns →L[ℝ] AsymLatticeField Nt Ns :=
  -finiteLaplacianAsym Nt Ns a + mass ^ 2 • ContinuousLinearMap.id ℝ _

/-- The mass operator is self-adjoint on the asymmetric lattice. -/
theorem massOperatorAsym_selfAdjoint (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (f g : AsymLatticeField Nt Ns) :
    ∑ x, f x * (massOperatorAsym Nt Ns a mass g) x =
    ∑ x, (massOperatorAsym Nt Ns a mass f) x * g x := by
  simp only [massOperatorAsym, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul]
  have split_l :
      ∀ x, f x * (-(finiteLaplacianAsym Nt Ns a g) x + mass ^ 2 * g x) =
        -(f x * (finiteLaplacianAsym Nt Ns a g) x) + mass ^ 2 * (f x * g x) := by
    intro x
    ring
  have split_r :
      ∀ x, (-(finiteLaplacianAsym Nt Ns a f) x + mass ^ 2 * f x) * g x =
        -((finiteLaplacianAsym Nt Ns a f) x * g x) + mass ^ 2 * (f x * g x) := by
    intro x
    ring
  simp_rw [split_l, split_r, Finset.sum_add_distrib, Finset.sum_neg_distrib, ← Finset.mul_sum]
  congr 1
  rw [finiteLaplacianAsym_selfAdjoint Nt Ns a f g]

/-- Matrix entries of the asymmetric massive operator. -/
def massOperatorEntryAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (x y : AsymLatticeSites Nt Ns) : ℝ :=
  (massOperatorAsym Nt Ns a mass (asymLatticeDelta Nt Ns y)) x

/-- The mass operator `Q = -Δ_a + m²` as a matrix indexed by asymmetric lattice sites. -/
def massOperatorMatrixAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ) :
    Matrix (AsymLatticeSites Nt Ns) (AsymLatticeSites Nt Ns) ℝ :=
  fun x y => massOperatorEntryAsym Nt Ns a mass x y

/-- The asymmetric mass operator matrix is Hermitian (symmetric over `ℝ`). -/
theorem massOperatorMatrixAsym_isHermitian (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ) :
    (massOperatorMatrixAsym Nt Ns a mass).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  have h := massOperatorAsym_selfAdjoint Nt Ns a mass
    (asymLatticeDelta Nt Ns j) (asymLatticeDelta Nt Ns i)
  simpa [Matrix.conjTranspose, massOperatorMatrixAsym, massOperatorEntryAsym, asymLatticeDelta]
    using h

/-- Abbreviation for the Hermiticity proof on the asymmetric lattice. -/
abbrev massMatrixAsymHerm (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ) :=
  massOperatorMatrixAsym_isHermitian Nt Ns a mass

/-- Eigenvalues of the asymmetric mass operator matrix. -/
def massEigenvaluesAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ) :
    AsymLatticeSites Nt Ns → ℝ :=
  (massMatrixAsymHerm Nt Ns a mass).eigenvalues

/-- Orthonormal eigenbasis of the asymmetric mass operator matrix. -/
def massEigenvectorBasisAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ) :
    OrthonormalBasis (AsymLatticeSites Nt Ns) ℝ
      (EuclideanSpace ℝ (AsymLatticeSites Nt Ns)) :=
  (massMatrixAsymHerm Nt Ns a mass).eigenvectorBasis

/-- The isotropic spectral lattice covariance `T = Q^{-1/2}` on the rectangular lattice
`ZMod Nt × ZMod Ns` with single spacing `a`.

This is the heterogeneous-lattice verbatim port of `spectralLatticeCovariance`, using the
Hermitian spectral data of `massOperatorMatrixAsym`. -/
noncomputable def spectralLatticeCovarianceAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (_ha : 0 < a) (_hmass : 0 < mass) :
    AsymLatticeField Nt Ns →L[ℝ] ell2' := by
  set eigvecs := massEigenvectorBasisAsym Nt Ns a mass
  set eigvals := massEigenvaluesAsym Nt Ns a mass
  set enum := Fintype.equivFin (AsymLatticeSites Nt Ns)
  set L : AsymLatticeField Nt Ns →ₗ[ℝ] ell2' :=
    { toFun := fun f => ∑ k : AsymLatticeSites Nt Ns,
        ((Real.sqrt (eigvals k))⁻¹ *
         ∑ x : AsymLatticeSites Nt Ns, (eigvecs k : EuclideanSpace ℝ _) x * f x) •
        lp.single 2 (enum k).val (1 : ℝ)
      map_add' := by
        intro f g
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, add_smul]
      map_smul' := by
        intro r f
        simp only [Pi.smul_apply, RingHom.id_apply]
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [smul_smul]
        congr 1
        calc
          (Real.sqrt (eigvals k))⁻¹ *
              (∑ x : AsymLatticeSites Nt Ns, (eigvecs k : EuclideanSpace ℝ _) x * (r * f x))
              = (Real.sqrt (eigvals k))⁻¹ *
                  (r * ∑ x : AsymLatticeSites Nt Ns, (eigvecs k : EuclideanSpace ℝ _) x * f x) := by
                    congr 1
                    calc
                      (∑ x : AsymLatticeSites Nt Ns,
                          (eigvecs k : EuclideanSpace ℝ _) x * (r * f x))
                          = ∑ x : AsymLatticeSites Nt Ns,
                              r * ((eigvecs k : EuclideanSpace ℝ _) x * f x) := by
                                apply Finset.sum_congr rfl
                                intro x hx
                                ring
                      _ = r * ∑ x : AsymLatticeSites Nt Ns,
                            (eigvecs k : EuclideanSpace ℝ _) x * f x := by
                              rw [Finset.mul_sum]
          _ = r * ((Real.sqrt (eigvals k))⁻¹ *
                  ∑ x : AsymLatticeSites Nt Ns, (eigvecs k : EuclideanSpace ℝ _) x * f x) := by
                    ring }
  exact { L with cont := L.continuous_of_finiteDimensional }

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
      (nhds (greenFunctionBilinear mass hmass f g)) := by
  -- TODO: port the convergence proof from the square lattice using the heterogeneous
  -- spectral decomposition and the rectangular continuum dispersion relation.
  sorry

end GaussianField

end
