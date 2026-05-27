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
import Mathlib.Analysis.Matrix.PosDef
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

/-! ## Abstract spectral foundation (positivity, eigencoefficients)

Heterogeneous-lattice analogues of the square `Laplacian`/`SpectralCovariance` results. These
are generic Hermitian-eigendecomposition facts (the eigenbasis `massEigenvectorBasisAsym` is
defined exactly as in the square case) plus the lattice-specific positivity. They feed the
abstract = DFT spectral bridge. -/

/-- Basis decomposition: any lattice field is a linear combination of site deltas. -/
private lemma asym_field_basis_decomp {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]
    (φ : AsymLatticeField Nt Ns) :
    φ = ∑ y : AsymLatticeSites Nt Ns, φ y • asymLatticeDelta Nt Ns y := by
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, asymLatticeDelta,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- For a single direction, `∑ₓ f(x)·(f(x+v)+f(x-v)-2f(x)) = -∑ₓ (f(x+v)-f(x))²`. Summation by
parts on the finite additive group; periodicity is automatic. -/
private lemma asym_direction_sum_eq_neg_sq {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]
    (f : AsymLatticeField Nt Ns) (v : AsymLatticeSites Nt Ns) :
    ∑ x, f x * (f (x + v) + f (x - v) - 2 * f x) =
    -(∑ x, (f (x + v) - f x) ^ 2) := by
  have reindex_sq : ∑ x, f (x + v) ^ 2 = ∑ x, f x ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight v) (fun x => f (x + v) ^ 2) (fun x => f x ^ 2)
      (fun x => by simp)
  have shift_bwd : ∑ x, f x * f (x - v) = ∑ x, f (x + v) * f x :=
    asym_sum_mul_translate' f f v
  have comm_sum : ∑ x, f (x + v) * f x = ∑ x, f x * f (x + v) :=
    Finset.sum_congr rfl (fun x _ => mul_comm _ _)
  have lhs_eq : ∑ x, f x * (f (x + v) + f (x - v) - 2 * f x) =
      (∑ x, f x * f (x + v)) + (∑ x, f x * f (x - v)) + (-2) * (∑ x, f x ^ 2) := by
    have h1 : ∀ x, f x * (f (x + v) + f (x - v) - 2 * f x) =
        f x * f (x + v) + f x * f (x - v) + (-2) * (f x ^ 2) := fun x => by ring
    simp_rw [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [lhs_eq, shift_bwd, comm_sum]
  have rhs_eq : -(∑ x, (f (x + v) - f x) ^ 2) =
      -(∑ x, f (x + v) ^ 2) + 2 * (∑ x, f x * f (x + v)) + (-1) * (∑ x, f x ^ 2) := by
    have h2 : ∀ x, (f (x + v) - f x) ^ 2 =
        f (x + v) ^ 2 + (-2) * (f x * f (x + v)) + f x ^ 2 := fun x => by ring
    simp_rw [h2, Finset.sum_add_distrib, ← Finset.mul_sum]; ring
  rw [rhs_eq, reindex_sq]; ring

/-- The asymmetric isotropic Laplacian is negative semidefinite. -/
theorem finiteLaplacianAsym_neg_semidefinite (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a : ℝ) (ha : 0 < a) (f : AsymLatticeField Nt Ns) :
    ∑ x, f x * (finiteLaplacianAsym Nt Ns a f) x ≤ 0 := by
  let _ha := ha
  change ∑ x, f x * finiteLaplacianAsymFun Nt Ns a f x ≤ 0
  simp only [finiteLaplacianAsymFun]
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
  have expand : ∀ x : AsymLatticeSites Nt Ns,
      f x * (a⁻¹ ^ 2 * (f (x + e1) + f (x - e1) + f (x + e2) + f (x - e2) - 4 * f x)) =
      a⁻¹ ^ 2 * (f x * (f (x + e1) + f (x - e1) - 2 * f x)) +
      a⁻¹ ^ 2 * (f x * (f (x + e2) + f (x - e2) - 2 * f x)) := fun x => by ring
  simp_rw [expand, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [asym_direction_sum_eq_neg_sq f e1, asym_direction_sum_eq_neg_sq f e2]
  have hS1 : 0 ≤ ∑ x, (f (x + e1) - f x) ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have hS2 : 0 ≤ ∑ x, (f (x + e2) - f x) ^ 2 := Finset.sum_nonneg fun x _ => sq_nonneg _
  have ha2 : 0 ≤ a⁻¹ ^ 2 := sq_nonneg _
  nlinarith [mul_nonneg ha2 hS1, mul_nonneg ha2 hS2]

/-- The mass operator on the asymmetric lattice is positive definite when `mass > 0`. -/
theorem massOperatorAsym_pos_def (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) (f : AsymLatticeField Nt Ns) (hf : f ≠ 0) :
    0 < ∑ x, f x * (massOperatorAsym Nt Ns a mass f) x := by
  simp only [massOperatorAsym, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul]
  have split : ∀ x : AsymLatticeSites Nt Ns,
      f x * (-(finiteLaplacianAsym Nt Ns a f) x + mass ^ 2 * f x) =
      -(f x * (finiteLaplacianAsym Nt Ns a f) x) + mass ^ 2 * f x ^ 2 := by
    intro x; ring
  simp_rw [split, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_neg_distrib]
  have h_neg : 0 ≤ -(∑ x, f x * (finiteLaplacianAsym Nt Ns a f) x) :=
    neg_nonneg.mpr (finiteLaplacianAsym_neg_semidefinite Nt Ns a ha f)
  have h_sq_pos : 0 < ∑ x, f x ^ 2 := by
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h; push Not at h; exact hf (funext h)
    exact Finset.sum_pos' (fun x _ => sq_nonneg (f x))
      ⟨x, Finset.mem_univ _, by positivity⟩
  linarith [mul_pos (sq_pos_of_pos hmass) h_sq_pos]

/-- The mass operator applied to `f` equals the matrix-vector product `M *ᵥ f`. -/
theorem massOperatorAsym_eq_matrix_mulVec (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (f : AsymLatticeField Nt Ns) (x : AsymLatticeSites Nt Ns) :
    (massOperatorAsym Nt Ns a mass f) x =
    (massOperatorMatrixAsym Nt Ns a mass).mulVec f x := by
  simp only [Matrix.mulVec, massOperatorMatrixAsym]
  conv_lhs => rw [asym_field_basis_decomp f]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1; ext y
  unfold massOperatorEntryAsym
  ring

/-- In eigenbasis coefficients, the mass operator acts by scalar multiplication by its
eigenvalue. -/
theorem massOperatorAsym_eigenCoeff_eq_eigenvalues_mul_eigenCoeff (Nt Ns : ℕ)
    [NeZero Nt] [NeZero Ns] (a mass : ℝ) (f : AsymLatticeField Nt Ns)
    (k : AsymLatticeSites Nt Ns) :
    (∑ x : AsymLatticeSites Nt Ns,
        (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x *
          (massOperatorAsym Nt Ns a mass f) x) =
      massEigenvaluesAsym Nt Ns a mass k *
        (∑ x : AsymLatticeSites Nt Ns,
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * f x) := by
  have hswap := massOperatorAsym_selfAdjoint Nt Ns a mass
    (massEigenvectorBasisAsym Nt Ns a mass k) f
  have hright :
      ∑ x : AsymLatticeSites Nt Ns,
          (massOperatorAsym Nt Ns a mass (massEigenvectorBasisAsym Nt Ns a mass k)) x * f x =
        massEigenvaluesAsym Nt Ns a mass k *
          (∑ x : AsymLatticeSites Nt Ns,
            (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * f x) := by
    have hmul :
        massOperatorAsym Nt Ns a mass (massEigenvectorBasisAsym Nt Ns a mass k) =
          massEigenvaluesAsym Nt Ns a mass k • (massEigenvectorBasisAsym Nt Ns a mass k) := by
      ext x
      rw [massOperatorAsym_eq_matrix_mulVec Nt Ns a mass
        (massEigenvectorBasisAsym Nt Ns a mass k) x]
      simpa [massEigenvaluesAsym, massEigenvectorBasisAsym] using
        congrFun (Matrix.IsHermitian.mulVec_eigenvectorBasis
          (hA := massOperatorMatrixAsym_isHermitian Nt Ns a mass) k) x
    rw [hmul]
    calc
      ∑ x : AsymLatticeSites Nt Ns,
          (massEigenvaluesAsym Nt Ns a mass k *
            (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x) * f x
          = ∑ x : AsymLatticeSites Nt Ns,
              massEigenvaluesAsym Nt Ns a mass k *
                ((massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * f x) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
      _ = massEigenvaluesAsym Nt Ns a mass k *
            (∑ x : AsymLatticeSites Nt Ns,
              (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * f x) := by
            rw [Finset.mul_sum]
  rw [hright] at hswap
  exact hswap

/-- Parseval identity in the mass-operator eigenbasis, in site coordinates. -/
theorem massEigenbasisAsym_sum_mul_sum_eq_site_inner (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (f g : AsymLatticeField Nt Ns) :
    (∑ k : AsymLatticeSites Nt Ns,
      (∑ x : AsymLatticeSites Nt Ns,
        (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * f x) *
      (∑ x : AsymLatticeSites Nt Ns,
        (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * g x)) =
      ∑ x : AsymLatticeSites Nt Ns, f x * g x := by
  let uf : EuclideanSpace ℝ (AsymLatticeSites Nt Ns) :=
    (EuclideanSpace.equiv (AsymLatticeSites Nt Ns) ℝ).symm f
  let ug : EuclideanSpace ℝ (AsymLatticeSites Nt Ns) :=
    (EuclideanSpace.equiv (AsymLatticeSites Nt Ns) ℝ).symm g
  have hparseval :=
    OrthonormalBasis.sum_inner_mul_inner (massEigenvectorBasisAsym Nt Ns a mass) uf ug
  have hcoeff_left : ∀ k : AsymLatticeSites Nt Ns,
      inner ℝ uf (massEigenvectorBasisAsym Nt Ns a mass k) =
        ∑ x : AsymLatticeSites Nt Ns,
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * f x := by
    intro k
    change (massEigenvectorBasisAsym Nt Ns a mass k).ofLp ⬝ᵥ star uf.ofLp = _
    simp [dotProduct, star_trivial, uf, WithLp.ofLp_toLp]
  have hcoeff_right : ∀ k : AsymLatticeSites Nt Ns,
      inner ℝ (massEigenvectorBasisAsym Nt Ns a mass k) ug =
        ∑ x : AsymLatticeSites Nt Ns,
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * g x := by
    intro k
    change ug.ofLp ⬝ᵥ star (massEigenvectorBasisAsym Nt Ns a mass k).ofLp = _
    simp [dotProduct, star_trivial, ug, WithLp.ofLp_toLp, mul_comm]
  have hinner :
      inner ℝ uf ug = ∑ x : AsymLatticeSites Nt Ns, f x * g x := by
    change ug.ofLp ⬝ᵥ star uf.ofLp = _
    simp [dotProduct, star_trivial, uf, ug, WithLp.ofLp_toLp, mul_comm]
  calc
    (∑ k : AsymLatticeSites Nt Ns,
        (∑ x : AsymLatticeSites Nt Ns,
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * f x) *
        (∑ x : AsymLatticeSites Nt Ns,
          (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * g x))
        = ∑ k : AsymLatticeSites Nt Ns,
            inner ℝ uf (massEigenvectorBasisAsym Nt Ns a mass k) *
              inner ℝ (massEigenvectorBasisAsym Nt Ns a mass k) ug := by
              refine Finset.sum_congr rfl ?_
              intro k hk
              rw [hcoeff_left, hcoeff_right]
    _ = inner ℝ uf ug := hparseval
    _ = ∑ x : AsymLatticeSites Nt Ns, f x * g x := hinner

/-- Eigenvalues of the asymmetric mass operator are strictly positive (`Q` is pos. def.). -/
theorem massOperatorMatrixAsym_eigenvalues_pos (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (k : AsymLatticeSites Nt Ns) :
    0 < massEigenvaluesAsym Nt Ns a mass k := by
  let M : Matrix (AsymLatticeSites Nt Ns) (AsymLatticeSites Nt Ns) ℝ :=
    massOperatorMatrixAsym Nt Ns a mass
  have hPosDef : M.PosDef := by
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ?_
    refine ⟨massOperatorMatrixAsym_isHermitian Nt Ns a mass, ?_⟩
    intro x hx
    have hpos := massOperatorAsym_pos_def Nt Ns a mass ha hmass x hx
    have hmul : M.mulVec x = massOperatorAsym Nt Ns a mass x := by
      ext i
      symm
      exact massOperatorAsym_eq_matrix_mulVec Nt Ns a mass x i
    simpa [M, dotProduct, hmul] using hpos
  have hEigPos : ∀ i : AsymLatticeSites Nt Ns,
      0 < (massMatrixAsymHerm Nt Ns a mass).eigenvalues i :=
    (Matrix.IsHermitian.posDef_iff_eigenvalues_pos
      (hA := massMatrixAsymHerm Nt Ns a mass)).mp hPosDef
  simpa [massEigenvaluesAsym] using hEigPos k

/-- Key identity: `⟨Tf, Tg⟩_ℓ² = Σ_k λ_k⁻¹ c_k(f) c_k(g)` with `c_k(·) = ⟪e_k, ·⟫`. -/
theorem spectralLatticeCovarianceAsym_inner (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (f g : AsymLatticeField Nt Ns) :
    @inner ℝ ell2' _
      (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass f)
      (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass g) =
    ∑ k : AsymLatticeSites Nt Ns,
      (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
      (∑ x, (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * f x) *
      (∑ x, (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * g x) := by
  let enum : AsymLatticeSites Nt Ns ≃ Fin (Fintype.card (AsymLatticeSites Nt Ns)) :=
    Fintype.equivFin (AsymLatticeSites Nt Ns)
  let lam : AsymLatticeSites Nt Ns → ℝ := massEigenvaluesAsym Nt Ns a mass
  let s : AsymLatticeSites Nt Ns → ℝ := fun k =>
    ∑ x : AsymLatticeSites Nt Ns,
      (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * f x
  let t : AsymLatticeSites Nt Ns → ℝ := fun k =>
    ∑ x : AsymLatticeSites Nt Ns,
      (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * g x
  have hlam : ∀ k : AsymLatticeSites Nt Ns, 0 < lam k := by
    intro k
    simpa [lam] using massOperatorMatrixAsym_eigenvalues_pos Nt Ns a mass ha hmass k
  have hf :
      spectralLatticeCovarianceAsym Nt Ns a mass ha hmass f =
      ∑ k : AsymLatticeSites Nt Ns,
        ((Real.sqrt (lam k))⁻¹ * s k) • lp.single 2 (enum k).val (1 : ℝ) := by
    unfold spectralLatticeCovarianceAsym
    simp [enum, lam, s]
  have hg :
      spectralLatticeCovarianceAsym Nt Ns a mass ha hmass g =
      ∑ k : AsymLatticeSites Nt Ns,
        ((Real.sqrt (lam k))⁻¹ * t k) • lp.single 2 (enum k).val (1 : ℝ) := by
    unfold spectralLatticeCovarianceAsym
    simp [enum, lam, t]
  rw [hf, hg]
  simp [inner_sum, sum_inner, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hleft :
      ∑ i,
        inner ℝ (((Real.sqrt (lam i))⁻¹ * s i) •
          lp.single (E := fun _ : ℕ => ℝ) 2 (enum i).val (1 : ℝ))
          (((Real.sqrt (lam k))⁻¹ * t k) •
            lp.single (E := fun _ : ℕ => ℝ) 2 (enum k).val (1 : ℝ)) =
      ((Real.sqrt (lam k))⁻¹ * s k) * ((Real.sqrt (lam k))⁻¹ * t k) := by
    classical
    simpa using (show ∑ i : AsymLatticeSites Nt Ns,
      inner ℝ (((Real.sqrt (lam i))⁻¹ * s i) • lp.single (E := fun _ : ℕ => ℝ) 2 (enum i).val (1 : ℝ))
        (((Real.sqrt (lam k))⁻¹ * t k) • lp.single (E := fun _ : ℕ => ℝ) 2 (enum k).val (1 : ℝ))
      = ((Real.sqrt (lam k))⁻¹ * s k) * ((Real.sqrt (lam k))⁻¹ * t k) from by
        classical
        rw [Finset.sum_eq_single k]
        · have hsingle : inner ℝ (lp.single (E := fun _ : ℕ => ℝ) 2 (enum k).val (1 : ℝ))
              (lp.single (E := fun _ : ℕ => ℝ) 2 (enum k).val (1 : ℝ)) = 1 := by
              simp
          simp [inner_smul_left, inner_smul_right, mul_assoc, mul_left_comm, mul_comm]
        · intro i hi hik
          have hne : enum i ≠ enum k := by
            intro h; exact hik (enum.injective h)
          have : inner ℝ (((Real.sqrt (lam i))⁻¹ * s i) • lp.single (E := fun _ : ℕ => ℝ) 2 (enum i).val (1 : ℝ))
              (((Real.sqrt (lam k))⁻¹ * t k) • lp.single (E := fun _ : ℕ => ℝ) 2 (enum k).val (1 : ℝ)) = 0 := by
                have hne_val : (enum i).val ≠ (enum k).val := by
                  intro h
                  apply hne
                  exact Fin.ext h
                have hsingle0 :
                    inner ℝ (lp.single (E := fun _ : ℕ => ℝ) 2 (enum i).val (1 : ℝ))
                      (lp.single (E := fun _ : ℕ => ℝ) 2 (enum k).val (1 : ℝ)) = 0 := by
                  rw [lp.inner_single_left]
                  simp [lp.single_apply, hne_val]
                simp [inner_smul_left, inner_smul_right, hsingle0, mul_comm]
          exact this
        · intro hknot
          exact (hknot (Finset.mem_univ k)).elim)
  have hrhs :
      (∑ x, ∑ i,
        (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
          ((massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) i * f i) *
          ((massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * g x)) =
      (lam k)⁻¹ * s k * t k := by
    calc
      (∑ x, ∑ i,
        (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
          ((massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) i * f i) *
          ((massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * g x))
          = ∑ i, ∑ x,
              (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
                ((massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) i * f i) *
                ((massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * g x) := by
              rw [Finset.sum_comm]
      _ = (lam k)⁻¹ *
            (∑ i, (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) i * f i) *
            (∑ x, (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * g x) := by
              simp [lam, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
      _ = (lam k)⁻¹ * s k * t k := by simp [s, t]
  rw [hleft, hrhs]
  have hsq : Real.sqrt (lam k) * Real.sqrt (lam k) = lam k := by
    nlinarith [Real.sq_sqrt (le_of_lt (hlam k))]
  calc
    ((Real.sqrt (lam k))⁻¹ * s k) * ((Real.sqrt (lam k))⁻¹ * t k)
        = (((Real.sqrt (lam k))⁻¹ * (Real.sqrt (lam k))⁻¹) * s k) * t k := by ring
    _ = (((Real.sqrt (lam k) * Real.sqrt (lam k))⁻¹) * s k) * t k := by ring
    _ = (lam k)⁻¹ * s k * t k := by simp [hsq]

/-! ## Rectangular 2D DFT spectral identities

Heterogeneous-lattice analogues of the square `CirculantDFT2d` results, assembled from the
per-direction 1D pieces (`dft_parseval_1d`, `dft_1d_eigenvalue_pointwise`) instantiated at the
two sizes `Nt`, `Ns`. These are the spectral foundation for the lattice→continuum convergence. -/

/-- Factor a sum over the product lattice `ZMod Nt × ZMod Ns` as an iterated sum. -/
lemma sum_factor_asym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (F : AsymLatticeSites Nt Ns → ℝ) :
    ∑ x : AsymLatticeSites Nt Ns, F x = ∑ a : ZMod Nt, ∑ b : ZMod Ns, F (a, b) :=
  Fintype.sum_prod_type F

/-- The 2D DFT Parseval identity on the rectangular lattice: the counting inner product equals
the spectral sum over the product DFT basis `φ^{Nt}_{m₁} ⊗ φ^{Ns}_{m₂}`. Tensor of the 1D
Parseval identities of sizes `Nt`, `Ns`. -/
theorem dft_parseval_2d_asym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (f g : AsymLatticeField Nt Ns) :
    ∑ x : AsymLatticeSites Nt Ns, f x * g x =
    ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
      (∑ x : AsymLatticeSites Nt Ns,
        f x * (latticeFourierBasisFun Nt m₁ x.1 * latticeFourierBasisFun Ns m₂ x.2)) *
      (∑ x : AsymLatticeSites Nt Ns,
        g x * (latticeFourierBasisFun Nt m₁ x.1 * latticeFourierBasisFun Ns m₂ x.2)) /
      (latticeFourierNormSq Nt m₁ * latticeFourierNormSq Ns m₂) := by
  have coeff_factor : ∀ (h : AsymLatticeField Nt Ns) (m₁ : Fin Nt) (m₂ : Fin Ns),
      ∑ x : AsymLatticeSites Nt Ns,
        h x * (latticeFourierBasisFun Nt m₁ x.1 * latticeFourierBasisFun Ns m₂ x.2) =
      ∑ a : ZMod Nt, (∑ b : ZMod Ns, h (a, b) * latticeFourierBasisFun Ns ↑m₂ b) *
        latticeFourierBasisFun Nt ↑m₁ a := by
    intro h m₁ m₂
    rw [sum_factor_asym]
    congr 1; ext a
    rw [Finset.sum_mul]
    congr 1; ext b
    ring
  rw [sum_factor_asym]
  simp_rw [dft_parseval_1d Ns (fun b => f (_, b)) (fun b => g (_, b))]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext m₂; rw [← Finset.sum_div,
    dft_parseval_1d Nt
      (fun a => ∑ b, f (a, b) * latticeFourierBasisFun Ns ↑m₂ b)
      (fun a => ∑ b, g (a, b) * latticeFourierBasisFun Ns ↑m₂ b),
    Finset.sum_div]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => ?_
  rw [← coeff_factor f m₁ m₂, ← coeff_factor g m₁ m₂]
  ring

/-- The rectangular mass operator applied to a product of 1D DFT eigenvectors
`φ^{Nt}_{m₁} ⊗ φ^{Ns}_{m₂}` yields `(λ^{Nt}_{m₁} + λ^{Ns}_{m₂} + mass²)` times it: it is an
eigenvector with the additive rectangular dispersion. -/
theorem massOperator_product_eigenvector_asym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : a ≠ 0) (m₁ m₂ : ℕ) (hm₁ : m₁ < Nt) (hm₂ : m₂ < Ns)
    (x : AsymLatticeSites Nt Ns) :
    (massOperatorAsym Nt Ns a mass
      (fun y : AsymLatticeSites Nt Ns =>
        latticeFourierBasisFun Nt m₁ y.1 * latticeFourierBasisFun Ns m₂ y.2)) x =
    (latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂ + mass ^ 2) *
      (latticeFourierBasisFun Nt m₁ x.1 * latticeFourierBasisFun Ns m₂ x.2) := by
  simp only [massOperatorAsym, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [finiteLaplacianAsym, ContinuousLinearMap.coe_mk',
    finiteLaplacianAsymLM, LinearMap.coe_mk, AddHom.coe_mk,
    finiteLaplacianAsymFun]
  have h1d₁ := dft_1d_eigenvalue_pointwise Nt a ha m₁ hm₁ x.1
  have h1d₂ := dft_1d_eigenvalue_pointwise Ns a ha m₂ hm₂ x.2
  linear_combination
    latticeFourierBasisFun Ns m₂ x.2 * h1d₁ +
    latticeFourierBasisFun Nt m₁ x.1 * h1d₂

/-- The asymmetric mass operator is surjective (positive definite on a finite-dim space). -/
theorem massOperatorAsym_surjective (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) :
    Function.Surjective (massOperatorAsym Nt Ns a mass) := by
  have hinj : Function.Injective (massOperatorAsym Nt Ns a mass) := by
    intro f g hfg
    by_contra hne
    have hne' : f - g ≠ 0 := sub_ne_zero.mpr hne
    have hpos := massOperatorAsym_pos_def Nt Ns a mass ha hmass (f - g) hne'
    have hzero : ∑ x, (f - g) x * (massOperatorAsym Nt Ns a mass (f - g)) x = 0 := by
      have hzero' : massOperatorAsym Nt Ns a mass (f - g) = 0 := by
        ext x; simp [map_sub, hfg, sub_self]
      simp [hzero']
    linarith
  exact (massOperatorAsym Nt Ns a mass).toLinearMap.surjective_of_injective hinj

/-- The covariance bilinear form of the asymmetric spectral CLM, in eigencoordinates. -/
theorem covariance_spectralLatticeCovarianceAsym_eq (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (f g : AsymLatticeField Nt Ns) :
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) f g =
    ∑ k : AsymLatticeSites Nt Ns,
      (massEigenvaluesAsym Nt Ns a mass k)⁻¹ *
      (∑ x, (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * f x) *
      (∑ x, (massEigenvectorBasisAsym Nt Ns a mass k : EuclideanSpace ℝ _) x * g x) := by
  unfold covariance
  exact spectralLatticeCovarianceAsym_inner Nt Ns a mass ha hmass f g

/-- The DFT eigencoefficient identity: pairing a product DFT eigenvector with `Q·h` equals the
eigenvalue times the pairing with `h`. From `Q` self-adjoint + the product-eigenvector property. -/
theorem dft_eigencoeff_massOperatorAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : a ≠ 0) (m₁ m₂ : ℕ) (hm₁ : m₁ < Nt) (hm₂ : m₂ < Ns)
    (h : AsymLatticeField Nt Ns) :
    (∑ x : AsymLatticeSites Nt Ns,
      (latticeFourierBasisFun Nt m₁ x.1 * latticeFourierBasisFun Ns m₂ x.2) *
      (massOperatorAsym Nt Ns a mass h) x) =
    (latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂ + mass ^ 2) *
      (∑ x : AsymLatticeSites Nt Ns,
        (latticeFourierBasisFun Nt m₁ x.1 * latticeFourierBasisFun Ns m₂ x.2) * h x) := by
  rw [massOperatorAsym_selfAdjoint Nt Ns a mass
    (fun y => latticeFourierBasisFun Nt m₁ y.1 * latticeFourierBasisFun Ns m₂ y.2) h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [massOperator_product_eigenvector_asym Nt Ns a mass ha m₁ m₂ hm₁ hm₂ x]
  ring

/-- **The abstract spectral covariance equals the rectangular 2D DFT spectral sum.** The
heterogeneous analogue of `abstract_spectral_eq_dft_spectral_2d`: both compute `⟨f, Q⁻¹g⟩`,
one via Mathlib's eigenbasis, one via the product DFT eigenbasis. -/
theorem abstract_spectral_eq_dft_spectral_2d_asym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (f g : AsymLatticeField Nt Ns) :
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass) f g =
    ∑ m₁ : Fin Nt, ∑ m₂ : Fin Ns,
      (∑ x, f x * (latticeFourierBasisFun Nt m₁ x.1 * latticeFourierBasisFun Ns m₂ x.2)) *
      (∑ x, g x * (latticeFourierBasisFun Nt m₁ x.1 * latticeFourierBasisFun Ns m₂ x.2)) /
      ((latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂ + mass ^ 2) *
       latticeFourierNormSq Nt m₁ * latticeFourierNormSq Ns m₂) := by
  obtain ⟨h, rfl⟩ := massOperatorAsym_surjective Nt Ns a mass ha hmass g
  have ha' : a ≠ 0 := ne_of_gt ha
  trans (∑ x : AsymLatticeSites Nt Ns, f x * h x)
  · rw [covariance_spectralLatticeCovarianceAsym_eq]
    simp_rw [massOperatorAsym_eigenCoeff_eq_eigenvalues_mul_eigenCoeff Nt Ns a mass h]
    refine Eq.trans ?_
      (massEigenbasisAsym_sum_mul_sum_eq_site_inner Nt Ns a mass f h)
    refine Finset.sum_congr rfl fun k _ => ?_
    have hne : massEigenvaluesAsym Nt Ns a mass k ≠ 0 :=
      ne_of_gt (massOperatorMatrixAsym_eigenvalues_pos Nt Ns a mass ha hmass k)
    field_simp
  · rw [dft_parseval_2d_asym]
    refine Finset.sum_congr rfl fun m₁ _ => Finset.sum_congr rfl fun m₂ _ => ?_
    have heig := dft_eigencoeff_massOperatorAsym Nt Ns a mass ha' m₁ m₂ m₁.isLt m₂.isLt h
    have heig' : ∑ x : AsymLatticeSites Nt Ns,
        (massOperatorAsym Nt Ns a mass h) x *
        (latticeFourierBasisFun Nt m₁ x.1 * latticeFourierBasisFun Ns m₂ x.2) =
      (latticeEigenvalue1d Nt a ↑m₁ + latticeEigenvalue1d Ns a ↑m₂ + mass ^ 2) *
        (∑ x, h x * (latticeFourierBasisFun Nt m₁ x.1 * latticeFourierBasisFun Ns m₂ x.2)) := by
      rw [show ∑ x, (massOperatorAsym Nt Ns a mass h) x *
          (latticeFourierBasisFun Nt m₁ x.1 * latticeFourierBasisFun Ns m₂ x.2) =
        ∑ x, (latticeFourierBasisFun Nt m₁ x.1 * latticeFourierBasisFun Ns m₂ x.2) *
          (massOperatorAsym Nt Ns a mass h) x from
        Finset.sum_congr rfl fun x _ => mul_comm _ _]
      rw [heig]
      congr 1
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    rw [heig']
    have hμ : 0 < latticeEigenvalue1d Nt a ↑m₁ + latticeEigenvalue1d Ns a ↑m₂ + mass ^ 2 := by
      have h1 := latticeEigenvalue1d_nonneg Nt a m₁
      have h2 := latticeEigenvalue1d_nonneg Ns a m₂
      positivity
    field_simp

/-! ## The lattice→continuum convergence (the cylinder-OS0 delta, now true) -/

/-- The `(m₁, m₂)`-th term of the rectangular lattice Green's function spectral sum: time
direction on `S¹(Lt)` with `Nt` sites, space on `S¹(Ls)` with `Ns` sites, shared spacing `a`. -/
private def latticeGreenTerm2dAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (f₁ g₁ : SmoothMap_Circle Lt ℝ) (f₂ g₂ : SmoothMap_Circle Ls ℝ) (p : ℕ × ℕ) : ℝ :=
  latticeDFTCoeff1d Lt Nt f₁ p.1 * latticeDFTCoeff1d Lt Nt g₁ p.1 *
  latticeDFTCoeff1d Ls Ns f₂ p.2 * latticeDFTCoeff1d Ls Ns g₂ p.2 /
  ((latticeEigenvalue1d Nt a p.1 + latticeEigenvalue1d Ns a p.2 + mass ^ 2) *
   latticeFourierNormSq Nt p.1 * latticeFourierNormSq Ns p.2)

/-- The `(n₁, n₂)`-th term of the continuum rectangular 2D Green's function spectral sum. -/
private def continuumGreenTerm2dAsym (mass : ℝ)
    (f₁ g₁ : SmoothMap_Circle Lt ℝ) (f₂ g₂ : SmoothMap_Circle Ls ℝ) (p : ℕ × ℕ) : ℝ :=
  DyninMityaginSpace.coeff p.1 f₁ * DyninMityaginSpace.coeff p.1 g₁ *
  DyninMityaginSpace.coeff p.2 f₂ * DyninMityaginSpace.coeff p.2 g₂ /
  (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) p.1 +
   HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) p.2 + mass ^ 2)

/-- The rectangular lattice Green's term vanishes when either index is out of range. -/
private theorem latticeGreenTerm2dAsym_zero_of_ge (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (f₁ g₁ : SmoothMap_Circle Lt ℝ) (f₂ g₂ : SmoothMap_Circle Ls ℝ) (p : ℕ × ℕ)
    (h : Nt ≤ p.1 ∨ Ns ≤ p.2) :
    latticeGreenTerm2dAsym Lt Ls Nt Ns a mass f₁ g₁ f₂ g₂ p = 0 := by
  unfold latticeGreenTerm2dAsym
  rcases h with h1 | h2
  · rw [latticeDFTCoeff1d_zero_of_ge Lt Nt f₁ p.1 h1]; ring
  · rw [latticeDFTCoeff1d_zero_of_ge Ls Ns f₂ p.2 h2]; ring

/-- Norm bound on each rectangular lattice Green's term, from per-direction DFT quadratic decay.
Gives `C / (mass² (1+p₁)⁴ (1+p₂)⁴)`, summable over `ℕ × ℕ` and uniform in `Nt, Ns, a`. -/
private theorem latticeGreenTerm2dAsym_norm_le (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] (a mass : ℝ)
    (hmass : 0 < mass)
    (f₁ g₁ : SmoothMap_Circle Lt ℝ) (f₂ g₂ : SmoothMap_Circle Ls ℝ)
    {Cf₁ Cg₁ Cf₂ Cg₂ : ℝ}
    (hCf₁ : 0 ≤ Cf₁) (hCg₁ : 0 ≤ Cg₁) (hCf₂ : 0 ≤ Cf₂) (hCg₂ : 0 ≤ Cg₂)
    (hf₁ : ∀ m, |latticeDFTCoeff1d Lt Nt f₁ m| ≤ Cf₁ / (1 + (m : ℝ)) ^ 2)
    (hg₁ : ∀ m, |latticeDFTCoeff1d Lt Nt g₁ m| ≤ Cg₁ / (1 + (m : ℝ)) ^ 2)
    (hf₂ : ∀ m, |latticeDFTCoeff1d Ls Ns f₂ m| ≤ Cf₂ / (1 + (m : ℝ)) ^ 2)
    (hg₂ : ∀ m, |latticeDFTCoeff1d Ls Ns g₂ m| ≤ Cg₂ / (1 + (m : ℝ)) ^ 2)
    (p : ℕ × ℕ) :
    ‖latticeGreenTerm2dAsym Lt Ls Nt Ns a mass f₁ g₁ f₂ g₂ p‖ ≤
      Cf₁ * Cg₁ * Cf₂ * Cg₂ /
      (mass ^ 2 * (1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4) := by
  by_cases h_range : p.1 < Nt ∧ p.2 < Ns
  · obtain ⟨hp1_lt, hp2_lt⟩ := h_range
    unfold latticeGreenTerm2dAsym
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_mul]
    have hden_pos : 0 < (latticeEigenvalue1d Nt a p.1 + latticeEigenvalue1d Ns a p.2 + mass ^ 2) *
        latticeFourierNormSq Nt p.1 * latticeFourierNormSq Ns p.2 := by
      apply mul_pos (mul_pos _ _) _
      · linarith [latticeEigenvalue1d_nonneg Nt a p.1,
                   latticeEigenvalue1d_nonneg Ns a p.2, sq_pos_of_pos hmass]
      · exact latticeFourierNormSq_pos Nt p.1 hp1_lt
      · exact latticeFourierNormSq_pos Ns p.2 hp2_lt
    rw [abs_of_pos hden_pos]
    have hden_ge : mass ^ 2 ≤ (latticeEigenvalue1d Nt a p.1 + latticeEigenvalue1d Ns a p.2 +
        mass ^ 2) * latticeFourierNormSq Nt p.1 * latticeFourierNormSq Ns p.2 := by
      have h_eig_sum_nn : 0 ≤ latticeEigenvalue1d Nt a p.1 + latticeEigenvalue1d Ns a p.2 +
          mass ^ 2 :=
        le_of_lt (by linarith [latticeEigenvalue1d_nonneg Nt a p.1,
                               latticeEigenvalue1d_nonneg Ns a p.2, sq_pos_of_pos hmass])
      calc mass ^ 2
          ≤ latticeEigenvalue1d Nt a p.1 + latticeEigenvalue1d Ns a p.2 + mass ^ 2 :=
            by linarith [latticeEigenvalue1d_nonneg Nt a p.1, latticeEigenvalue1d_nonneg Ns a p.2]
        _ ≤ _ * latticeFourierNormSq Nt p.1 :=
            le_mul_of_one_le_right h_eig_sum_nn (latticeFourierNormSq_ge_one Nt p.1 hp1_lt)
        _ ≤ _ * latticeFourierNormSq Ns p.2 :=
            le_mul_of_one_le_right (mul_nonneg h_eig_sum_nn
              (le_of_lt (latticeFourierNormSq_pos Nt p.1 hp1_lt)))
              (latticeFourierNormSq_ge_one Ns p.2 hp2_lt)
    have hmass_sq := sq_pos_of_pos hmass
    have hp1 : (0 : ℝ) < (1 + (p.1 : ℝ)) ^ 2 := by positivity
    have hp2 : (0 : ℝ) < (1 + (p.2 : ℝ)) ^ 2 := by positivity
    have h1 : |latticeDFTCoeff1d Lt Nt f₁ p.1| * |latticeDFTCoeff1d Lt Nt g₁ p.1| ≤
        Cf₁ * Cg₁ / (1 + (p.1 : ℝ)) ^ 4 :=
      calc |latticeDFTCoeff1d Lt Nt f₁ p.1| * |latticeDFTCoeff1d Lt Nt g₁ p.1|
          ≤ (Cf₁ / (1 + (p.1 : ℝ)) ^ 2) * (Cg₁ / (1 + (p.1 : ℝ)) ^ 2) :=
            mul_le_mul (hf₁ p.1) (hg₁ p.1) (abs_nonneg _) (div_nonneg hCf₁ hp1.le)
        _ = Cf₁ * Cg₁ / (1 + (p.1 : ℝ)) ^ 4 := by rw [div_mul_div_comm]; congr 1; ring
    have h2 : |latticeDFTCoeff1d Ls Ns f₂ p.2| * |latticeDFTCoeff1d Ls Ns g₂ p.2| ≤
        Cf₂ * Cg₂ / (1 + (p.2 : ℝ)) ^ 4 :=
      calc |latticeDFTCoeff1d Ls Ns f₂ p.2| * |latticeDFTCoeff1d Ls Ns g₂ p.2|
          ≤ (Cf₂ / (1 + (p.2 : ℝ)) ^ 2) * (Cg₂ / (1 + (p.2 : ℝ)) ^ 2) :=
            mul_le_mul (hf₂ p.2) (hg₂ p.2) (abs_nonneg _) (div_nonneg hCf₂ hp2.le)
        _ = Cf₂ * Cg₂ / (1 + (p.2 : ℝ)) ^ 4 := by rw [div_mul_div_comm]; congr 1; ring
    have hnum : |latticeDFTCoeff1d Lt Nt f₁ p.1| * |latticeDFTCoeff1d Lt Nt g₁ p.1| *
        |latticeDFTCoeff1d Ls Ns f₂ p.2| * |latticeDFTCoeff1d Ls Ns g₂ p.2| ≤
        Cf₁ * Cg₁ * Cf₂ * Cg₂ / ((1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4) := by
      have hmul := mul_le_mul h1 h2 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        (div_nonneg (mul_nonneg hCf₁ hCg₁) (by positivity))
      calc |latticeDFTCoeff1d Lt Nt f₁ p.1| * |latticeDFTCoeff1d Lt Nt g₁ p.1| *
            |latticeDFTCoeff1d Ls Ns f₂ p.2| * |latticeDFTCoeff1d Ls Ns g₂ p.2|
          = (|latticeDFTCoeff1d Lt Nt f₁ p.1| * |latticeDFTCoeff1d Lt Nt g₁ p.1|) *
            (|latticeDFTCoeff1d Ls Ns f₂ p.2| * |latticeDFTCoeff1d Ls Ns g₂ p.2|) := by ring
        _ ≤ (Cf₁ * Cg₁ / (1 + (p.1 : ℝ)) ^ 4) * (Cf₂ * Cg₂ / (1 + (p.2 : ℝ)) ^ 4) := hmul
        _ = Cf₁ * Cg₁ * Cf₂ * Cg₂ / ((1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4) := by
            rw [div_mul_div_comm]; congr 1; ring
    set den := (latticeEigenvalue1d Nt a p.1 + latticeEigenvalue1d Ns a p.2 + mass ^ 2) *
        latticeFourierNormSq Nt p.1 * latticeFourierNormSq Ns p.2
    calc |latticeDFTCoeff1d Lt Nt f₁ p.1| * |latticeDFTCoeff1d Lt Nt g₁ p.1| *
          |latticeDFTCoeff1d Ls Ns f₂ p.2| * |latticeDFTCoeff1d Ls Ns g₂ p.2| / den
        ≤ Cf₁ * Cg₁ * Cf₂ * Cg₂ / ((1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4) / den :=
          div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
      _ ≤ Cf₁ * Cg₁ * Cf₂ * Cg₂ / ((1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4) / mass ^ 2 :=
          div_le_div_of_nonneg_left (div_nonneg (by positivity) (by positivity)) hmass_sq hden_ge
      _ = Cf₁ * Cg₁ * Cf₂ * Cg₂ /
          (mass ^ 2 * (1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4) := by
          rw [div_div]; congr 1; ring
  · rw [not_and_or, not_lt, not_lt] at h_range
    have h0 : latticeGreenTerm2dAsym Lt Ls Nt Ns a mass f₁ g₁ f₂ g₂ p = 0 :=
      latticeGreenTerm2dAsym_zero_of_ge Lt Ls Nt Ns a mass f₁ g₁ f₂ g₂ p h_range
    rw [h0, norm_zero]; positivity

/-- Summability of the dominating function `C / (mass² (1+p₁)⁴ (1+p₂)⁴)` over `ℕ × ℕ`. -/
private theorem summable_bound_asym (mass : ℝ) (hmass : 0 < mass) (C : ℝ) :
    Summable (fun p : ℕ × ℕ =>
      C / (mass ^ 2 * (1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4)) := by
  have h1d : Summable (fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 4) := by
    have hps := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4)).comp_injective
      Nat.succ_injective
    exact hps.congr fun n => by simp only [Function.comp, Nat.cast_succ, add_comm]
  have h2d := h1d.mul_of_nonneg h1d (fun _ => by positivity) (fun _ => by positivity)
  exact (h2d.mul_left (C / mass ^ 2)).congr fun p => by
    have : mass ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hmass)
    have : (1 + (p.1 : ℝ)) ^ 4 ≠ 0 := ne_of_gt (by positivity)
    have : (1 + (p.2 : ℝ)) ^ 4 ≠ 0 := ne_of_gt (by positivity)
    field_simp

/-- Each rectangular lattice Green's term converges to the continuum term, along any
isotropic sequence `(Nt k, Ns k, a k)` with `Nt k · a k = Lt`, `Ns k · a k = Ls`, `a k → 0`. -/
private theorem latticeGreenTerm2dAsym_tendsto
    (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hLt : ∀ k, (Nt k : ℝ) * a k = Lt) (hLs : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Tendsto a atTop (nhds 0))
    (f₁ g₁ : SmoothMap_Circle Lt ℝ) (f₂ g₂ : SmoothMap_Circle Ls ℝ) (p : ℕ × ℕ) :
    Tendsto (fun k => haveI := hNt k; haveI := hNs k
        latticeGreenTerm2dAsym Lt Ls (Nt k) (Ns k) (a k) mass f₁ g₁ f₂ g₂ p)
      atTop (nhds (continuumGreenTerm2dAsym Lt Ls mass f₁ g₁ f₂ g₂ p)) := by
  -- a → 𝓝[>] 0  ⟹  (a)⁻¹ → atTop  ⟹  Nt, Ns → atTop
  have ha0' : Tendsto a atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within a ha0
      (Filter.Eventually.of_forall fun k => ha k)
  have hinv : Tendsto (fun k => (a k)⁻¹) atTop atTop := tendsto_inv_nhdsGT_zero.comp ha0'
  have hNt_top : Tendsto Nt atTop atTop := by
    rw [← tendsto_natCast_atTop_iff (R := ℝ)]
    refine (hinv.const_mul_atTop (Fact.out : (0:ℝ) < Lt)).congr fun k => ?_
    rw [← div_eq_mul_inv, div_eq_iff (ne_of_gt (ha k))]; exact (hLt k).symm
  have hNs_top : Tendsto Ns atTop atTop := by
    rw [← tendsto_natCast_atTop_iff (R := ℝ)]
    refine (hinv.const_mul_atTop (Fact.out : (0:ℝ) < Ls)).congr fun k => ?_
    rw [← div_eq_mul_inv, div_eq_iff (ne_of_gt (ha k))]; exact (hLs k).symm
  have hNt1 : Tendsto (fun k => Nt k - 1) atTop atTop := by
    rw [tendsto_atTop_atTop]; intro b
    obtain ⟨K, hK⟩ := tendsto_atTop_atTop.mp hNt_top (b + 1)
    exact ⟨K, fun k hk => by have := hK k hk; omega⟩
  have hNs1 : Tendsto (fun k => Ns k - 1) atTop atTop := by
    rw [tendsto_atTop_atTop]; intro b
    obtain ⟨K, hK⟩ := tendsto_atTop_atTop.mp hNs_top (b + 1)
    exact ⟨K, fun k hk => by have := hK k hk; omega⟩
  have hNtk : ∀ k, (Nt k - 1) + 1 = Nt k := fun k =>
    Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (hNt k).out)
  have hNsk : ∀ k, (Ns k - 1) + 1 = Ns k := fun k =>
    Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (hNs k).out)
  -- per-direction reindexed convergences
  have eig1 : Tendsto (fun k => latticeEigenvalue1d (Nt k) (a k) p.1) atTop
      (nhds (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) p.1)) := by
    refine ((latticeEigenvalue1d_tendsto_continuum Lt p.1).comp hNt1).congr fun k => ?_
    haveI := hNt k
    simp only [Function.comp, hNtk k]
    congr 1
    rw [circleSpacing, div_eq_iff (by exact_mod_cast (hNt k).out : (Nt k : ℝ) ≠ 0), mul_comm]
    exact (hLt k).symm
  have eig2 : Tendsto (fun k => latticeEigenvalue1d (Ns k) (a k) p.2) atTop
      (nhds (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) p.2)) := by
    refine ((latticeEigenvalue1d_tendsto_continuum Ls p.2).comp hNs1).congr fun k => ?_
    haveI := hNs k
    simp only [Function.comp, hNsk k]
    congr 1
    rw [circleSpacing, div_eq_iff (by exact_mod_cast (hNs k).out : (Ns k : ℝ) ≠ 0), mul_comm]
    exact (hLs k).symm
  have dft_f1 : Tendsto (fun k => haveI := hNt k; latticeDFTCoeff1d Lt (Nt k) f₁ p.1) atTop
      (nhds (DyninMityaginSpace.coeff p.1 f₁)) := by
    refine ((latticeDFTCoeff1d_tendsto Lt f₁ p.1).comp hNt1).congr fun k => ?_
    haveI := hNt k; simp only [Function.comp, hNtk k]
  have dft_g1 : Tendsto (fun k => haveI := hNt k; latticeDFTCoeff1d Lt (Nt k) g₁ p.1) atTop
      (nhds (DyninMityaginSpace.coeff p.1 g₁)) := by
    refine ((latticeDFTCoeff1d_tendsto Lt g₁ p.1).comp hNt1).congr fun k => ?_
    haveI := hNt k; simp only [Function.comp, hNtk k]
  have dft_f2 : Tendsto (fun k => haveI := hNs k; latticeDFTCoeff1d Ls (Ns k) f₂ p.2) atTop
      (nhds (DyninMityaginSpace.coeff p.2 f₂)) := by
    refine ((latticeDFTCoeff1d_tendsto Ls f₂ p.2).comp hNs1).congr fun k => ?_
    haveI := hNs k; simp only [Function.comp, hNsk k]
  have dft_g2 : Tendsto (fun k => haveI := hNs k; latticeDFTCoeff1d Ls (Ns k) g₂ p.2) atTop
      (nhds (DyninMityaginSpace.coeff p.2 g₂)) := by
    refine ((latticeDFTCoeff1d_tendsto Ls g₂ p.2).comp hNs1).congr fun k => ?_
    haveI := hNs k; simp only [Function.comp, hNsk k]
  have ns1 : Tendsto (fun k => haveI := hNt k; latticeFourierNormSq (Nt k) p.1) atTop (nhds 1) := by
    refine tendsto_const_nhds.congr' (Filter.EventuallyEq.symm ?_)
    filter_upwards [hNt1.eventually (latticeFourierNormSq_eventually_one p.1)] with k hk
    haveI := hNt k; simpa only [hNtk k] using hk
  have ns2 : Tendsto (fun k => haveI := hNs k; latticeFourierNormSq (Ns k) p.2) atTop (nhds 1) := by
    refine tendsto_const_nhds.congr' (Filter.EventuallyEq.symm ?_)
    filter_upwards [hNs1.eventually (latticeFourierNormSq_eventually_one p.2)] with k hk
    haveI := hNs k; simpa only [hNsk k] using hk
  -- denominator convergence: (eig₁ + eig₂ + mass²)·normSq₁·normSq₂ → (c₁ + c₂ + mass²)
  have h_denom : Tendsto (fun k => haveI := hNt k; haveI := hNs k
      (latticeEigenvalue1d (Nt k) (a k) p.1 + latticeEigenvalue1d (Ns k) (a k) p.2 + mass ^ 2) *
        latticeFourierNormSq (Nt k) p.1 * latticeFourierNormSq (Ns k) p.2) atTop
      (nhds (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) p.1 +
             HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) p.2 + mass ^ 2)) := by
    have h := (((eig1.add eig2).add (tendsto_const_nhds (x := mass ^ 2))).mul ns1).mul ns2
    simpa only [mul_one] using h
  unfold latticeGreenTerm2dAsym continuumGreenTerm2dAsym
  apply Filter.Tendsto.div (((dft_f1.mul dft_g1).mul dft_f2).mul dft_g2) h_denom
  have h1 := HasLaplacianEigenvalues.eigenvalue_nonneg (E := SmoothMap_Circle Lt ℝ) p.1
  have h2 := HasLaplacianEigenvalues.eigenvalue_nonneg (E := SmoothMap_Circle Ls ℝ) p.2
  nlinarith [sq_pos_of_pos hmass]

/-- The rectangular lattice covariance for pure tensors equals the explicit 2D DFT spectral
sum (range form). From `abstract_spectral_eq_dft_spectral_2d_asym` + the pure-tensor DFT
coefficient factorization. -/
private theorem lattice_covariance_pure_eq_2d_spectral_asym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f₁ g₁ : SmoothMap_Circle Lt ℝ) (f₂ g₂ : SmoothMap_Circle Ls ℝ) :
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
      (fun x => evalAsymTorusAtSite Lt Ls Nt Ns x (NuclearTensorProduct.pure f₁ f₂))
      (fun x => evalAsymTorusAtSite Lt Ls Nt Ns x (NuclearTensorProduct.pure g₁ g₂)) =
    ∑ m₁ ∈ Finset.range Nt, ∑ m₂ ∈ Finset.range Ns,
      latticeDFTCoeff1d Lt Nt f₁ m₁ * latticeDFTCoeff1d Lt Nt g₁ m₁ *
      latticeDFTCoeff1d Ls Ns f₂ m₂ * latticeDFTCoeff1d Ls Ns g₂ m₂ /
      ((latticeEigenvalue1d Nt a m₁ + latticeEigenvalue1d Ns a m₂ + mass ^ 2) *
       latticeFourierNormSq Nt m₁ * latticeFourierNormSq Ns m₂) := by
  rw [abstract_spectral_eq_dft_spectral_2d_asym]
  have hpure : ∀ (h₁ : SmoothMap_Circle Lt ℝ) (h₂ : SmoothMap_Circle Ls ℝ)
      (x : AsymLatticeSites Nt Ns),
      evalAsymTorusAtSite Lt Ls Nt Ns x (NuclearTensorProduct.pure h₁ h₂) =
      circleRestriction Lt Nt h₁ x.1 * circleRestriction Ls Ns h₂ x.2 := by
    intro h₁ h₂ x
    unfold evalAsymTorusAtSite
    rw [NuclearTensorProduct.evalCLM_pure]
    simp [ContinuousLinearMap.comp_apply]
  have hcoeff : ∀ (h₁ : SmoothMap_Circle Lt ℝ) (h₂ : SmoothMap_Circle Ls ℝ)
      (m₁ : Fin Nt) (m₂ : Fin Ns),
      ∑ x : AsymLatticeSites Nt Ns,
        evalAsymTorusAtSite Lt Ls Nt Ns x (NuclearTensorProduct.pure h₁ h₂) *
        (latticeFourierBasisFun Nt ↑m₁ x.1 * latticeFourierBasisFun Ns ↑m₂ x.2) =
      latticeDFTCoeff1d Lt Nt h₁ ↑m₁ * latticeDFTCoeff1d Ls Ns h₂ ↑m₂ := by
    intro h₁ h₂ m₁ m₂
    simp_rw [hpure]
    simp_rw [show ∀ x : AsymLatticeSites Nt Ns,
        (circleRestriction Lt Nt h₁ x.1 * circleRestriction Ls Ns h₂ x.2) *
        (latticeFourierBasisFun Nt ↑m₁ x.1 * latticeFourierBasisFun Ns ↑m₂ x.2) =
        (circleRestriction Lt Nt h₁ x.1 * latticeFourierBasisFun Nt ↑m₁ x.1) *
        (circleRestriction Ls Ns h₂ x.2 * latticeFourierBasisFun Ns ↑m₂ x.2) from
      fun x => by ring]
    rw [sum_factor_asym]
    dsimp only
    rw [← Fintype.sum_mul_sum]
    congr 1
    · rw [latticeDFTCoeff1d, if_pos m₁.isLt]
    · rw [latticeDFTCoeff1d, if_pos m₂.isLt]
  simp_rw [hcoeff]
  symm
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  ring

/-- The rectangular lattice covariance for pure tensors as a `tsum` over `ℕ × ℕ`. -/
private theorem lattice_covariance_eq_tsum_pure_asym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f₁ g₁ : SmoothMap_Circle Lt ℝ) (f₂ g₂ : SmoothMap_Circle Ls ℝ) :
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
      (fun x => evalAsymTorusAtSite Lt Ls Nt Ns x (NuclearTensorProduct.pure f₁ f₂))
      (fun x => evalAsymTorusAtSite Lt Ls Nt Ns x (NuclearTensorProduct.pure g₁ g₂)) =
    ∑' p : ℕ × ℕ, latticeGreenTerm2dAsym Lt Ls Nt Ns a mass f₁ g₁ f₂ g₂ p := by
  rw [lattice_covariance_pure_eq_2d_spectral_asym]
  symm
  rw [tsum_eq_sum (s := Finset.range Nt ×ˢ Finset.range Ns)]
  · rw [Finset.sum_product]; rfl
  · intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range, not_and_or, not_lt, not_lt] at hp
    exact latticeGreenTerm2dAsym_zero_of_ge Lt Ls Nt Ns a mass f₁ g₁ f₂ g₂ p hp

/-- The continuum rectangular Green's function for pure tensors as a `tsum` over `ℕ × ℕ`. -/
private theorem greenFunctionBilinear_pure_eq_tsum_asym (mass : ℝ) (hmass : 0 < mass)
    (f₁ g₁ : SmoothMap_Circle Lt ℝ) (f₂ g₂ : SmoothMap_Circle Ls ℝ) :
    greenFunctionBilinear (E := AsymTorusTestFunction Lt Ls) mass hmass
      (NuclearTensorProduct.pure f₁ f₂) (NuclearTensorProduct.pure g₁ g₂) =
    ∑' p : ℕ × ℕ, continuumGreenTerm2dAsym Lt Ls mass f₁ g₁ f₂ g₂ p := by
  show ∑' m, DyninMityaginSpace.coeff m (NuclearTensorProduct.pure f₁ f₂) *
        DyninMityaginSpace.coeff m (NuclearTensorProduct.pure g₁ g₂) /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle Lt ℝ) (SmoothMap_Circle Ls ℝ)) m +
          mass ^ 2) =
      ∑' p : ℕ × ℕ, continuumGreenTerm2dAsym Lt Ls mass f₁ g₁ f₂ g₂ p
  have h_term : ∀ m : ℕ,
      DyninMityaginSpace.coeff m (NuclearTensorProduct.pure f₁ f₂) *
        DyninMityaginSpace.coeff m (NuclearTensorProduct.pure g₁ g₂) /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle Lt ℝ) (SmoothMap_Circle Ls ℝ)) m +
          mass ^ 2) =
      continuumGreenTerm2dAsym Lt Ls mass f₁ g₁ f₂ g₂ (Nat.unpair m) := by
    intro m
    show (NuclearTensorProduct.pure f₁ f₂).val m * (NuclearTensorProduct.pure g₁ g₂).val m /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle Lt ℝ) (SmoothMap_Circle Ls ℝ)) m +
          mass ^ 2) =
      continuumGreenTerm2dAsym Lt Ls mass f₁ g₁ f₂ g₂ (Nat.unpair m)
    have ev_ntp := fun (n : ℕ) =>
      show HasLaplacianEigenvalues.eigenvalue
        (E := NuclearTensorProduct (SmoothMap_Circle Lt ℝ) (SmoothMap_Circle Ls ℝ)) n =
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Lt ℝ) (Nat.unpair n).1 +
        HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle Ls ℝ) (Nat.unpair n).2 from rfl
    simp only [continuumGreenTerm2dAsym, ev_ntp, NuclearTensorProduct.pure_val]
    ring
  simp_rw [h_term, ← Nat.pairEquiv_symm_apply]
  exact Nat.pairEquiv.symm.tsum_eq _

/-- **Isotropic rectangular lattice → continuum Green's function (pure tensors).** -/
private theorem lattice_green_tendsto_continuum_asym_pure
    (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k)
    (hLt : ∀ k, (Nt k : ℝ) * a k = Lt) (hLs : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Tendsto a atTop (nhds 0))
    (f₁ g₁ : SmoothMap_Circle Lt ℝ) (f₂ g₂ : SmoothMap_Circle Ls ℝ) :
    Tendsto (fun k => haveI := hNt k; haveI := hNs k
        covariance (spectralLatticeCovarianceAsym (Nt k) (Ns k) (a k) mass (ha k) hmass)
          (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x (NuclearTensorProduct.pure f₁ f₂))
          (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x (NuclearTensorProduct.pure g₁ g₂)))
      atTop
      (nhds (greenFunctionBilinear (E := AsymTorusTestFunction Lt Ls) mass hmass
        (NuclearTensorProduct.pure f₁ f₂) (NuclearTensorProduct.pure g₁ g₂))) := by
  simp_rw [lattice_covariance_eq_tsum_pure_asym]
  rw [greenFunctionBilinear_pure_eq_tsum_asym]
  obtain ⟨Cf₁, hCf₁_nn, hCf₁⟩ := latticeDFTCoeff1d_quadratic_bound Lt f₁
  obtain ⟨Cg₁, hCg₁_nn, hCg₁⟩ := latticeDFTCoeff1d_quadratic_bound Lt g₁
  obtain ⟨Cf₂, hCf₂_nn, hCf₂⟩ := latticeDFTCoeff1d_quadratic_bound Ls f₂
  obtain ⟨Cg₂, hCg₂_nn, hCg₂⟩ := latticeDFTCoeff1d_quadratic_bound Ls g₂
  apply tendsto_tsum_of_dominated_convergence
    (bound := fun p : ℕ × ℕ => Cf₁ * Cg₁ * Cf₂ * Cg₂ /
      (mass ^ 2 * (1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4))
  · exact summable_bound_asym mass hmass _
  · intro p
    exact latticeGreenTerm2dAsym_tendsto Lt Ls mass hmass Nt Ns a hNt hNs ha hLt hLs ha0
      f₁ g₁ f₂ g₂ p
  · apply Filter.Eventually.of_forall
    intro k p
    haveI := hNt k; haveI := hNs k
    have hNtk : (Nt k - 1) + 1 = Nt k := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (hNt k).out)
    have hNsk : (Ns k - 1) + 1 = Ns k := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (hNs k).out)
    have bf₁ : ∀ m, |latticeDFTCoeff1d Lt (Nt k) f₁ m| ≤ Cf₁ / (1 + (m : ℝ)) ^ 2 := fun m => by
      have := hCf₁ (Nt k - 1) m; simpa only [hNtk] using this
    have bg₁ : ∀ m, |latticeDFTCoeff1d Lt (Nt k) g₁ m| ≤ Cg₁ / (1 + (m : ℝ)) ^ 2 := fun m => by
      have := hCg₁ (Nt k - 1) m; simpa only [hNtk] using this
    have bf₂ : ∀ m, |latticeDFTCoeff1d Ls (Ns k) f₂ m| ≤ Cf₂ / (1 + (m : ℝ)) ^ 2 := fun m => by
      have := hCf₂ (Ns k - 1) m; simpa only [hNsk] using this
    have bg₂ : ∀ m, |latticeDFTCoeff1d Ls (Ns k) g₂ m| ≤ Cg₂ / (1 + (m : ℝ)) ^ 2 := fun m => by
      have := hCg₂ (Ns k - 1) m; simpa only [hNsk] using this
    exact latticeGreenTerm2dAsym_norm_le Lt Ls (Nt k) (Ns k) (a k) mass hmass f₁ g₁ f₂ g₂
      hCf₁_nn hCg₁_nn hCf₂_nn hCg₂_nn bf₁ bg₁ bf₂ bg₂ p

/-! ### DM-expansion infrastructure (general elements) -/

/-- NTP basis elements of the rectangular torus are pure tensors. -/
private theorem ntp_basis_eq_pure_asym (m : ℕ) :
    DyninMityaginSpace.basis (E := AsymTorusTestFunction Lt Ls) m =
    NuclearTensorProduct.pure
      (DyninMityaginSpace.basis (E := SmoothMap_Circle Lt ℝ) (Nat.unpair m).1)
      (DyninMityaginSpace.basis (E := SmoothMap_Circle Ls ℝ) (Nat.unpair m).2) := by
  ext k
  show (RapidDecaySeq.basisVec m).val k =
    (NuclearTensorProduct.pure
      (DyninMityaginSpace.basis (E := SmoothMap_Circle Lt ℝ) (Nat.unpair m).1)
      (DyninMityaginSpace.basis (E := SmoothMap_Circle Ls ℝ) (Nat.unpair m).2)).val k
  rw [NuclearTensorProduct.pure_val, smoothCircle_coeff_basis, smoothCircle_coeff_basis]
  simp only [RapidDecaySeq.basisVec]
  by_cases hk : k = m
  · subst hk; simp
  · simp only [hk, ite_false]
    by_cases h1 : (Nat.unpair k).1 = (Nat.unpair m).1
    · have h2 : (Nat.unpair k).2 ≠ (Nat.unpair m).2 := by
        intro h2; exact hk (by rw [← Nat.pair_unpair k, h1, h2, Nat.pair_unpair])
      simp [h2]
    · simp [h1]

/-- Continuity of `f ↦ G(f, h)` on the rectangular torus, via polarization. -/
private theorem greenFunctionBilinear_continuous_left_asym
    (mass : ℝ) (hmass : 0 < mass) (h : AsymTorusTestFunction Lt Ls) :
    Continuous (fun f => greenFunctionBilinear
      (E := AsymTorusTestFunction Lt Ls) mass hmass f h) := by
  have hcdiag := greenFunctionBilinear_continuous_diag mass hmass
    (E := AsymTorusTestFunction Lt Ls)
  have hpol : ∀ f, greenFunctionBilinear mass hmass f h =
      (greenFunctionBilinear mass hmass (f + h) (f + h) -
       greenFunctionBilinear mass hmass f f -
       greenFunctionBilinear mass hmass h h) / 2 := by
    intro f
    have : greenFunctionBilinear mass hmass (f + h) (f + h) =
        greenFunctionBilinear mass hmass f f +
        2 * greenFunctionBilinear mass hmass f h +
        greenFunctionBilinear mass hmass h h := by
      rw [greenFunctionBilinear_add_left, greenFunctionBilinear_add_right,
          greenFunctionBilinear_add_right, greenFunctionBilinear_symm mass hmass h f]
      ring
    linarith
  exact (((hcdiag.comp (continuous_id.add continuous_const)).sub hcdiag).sub
    continuous_const).div_const 2 |>.congr (fun f => (hpol f).symm)

/-- Green function on the rectangular torus as a CLM in the first argument. -/
private noncomputable def greenCLM_left_asym
    (mass : ℝ) (hmass : 0 < mass) (h : AsymTorusTestFunction Lt Ls) :
    AsymTorusTestFunction Lt Ls →L[ℝ] ℝ :=
  ⟨{ toFun := fun f => greenFunctionBilinear (E := AsymTorusTestFunction Lt Ls) mass hmass f h
     map_add' := fun f₁ f₂ => greenFunctionBilinear_add_left mass hmass f₁ f₂ h
     map_smul' := fun c f => by
       rw [greenFunctionBilinear_smul_left, RingHom.id_apply, smul_eq_mul] },
   greenFunctionBilinear_continuous_left_asym Lt Ls mass hmass h⟩

@[simp] private theorem greenCLM_left_apply_asym
    (mass : ℝ) (hmass : 0 < mass) (h f : AsymTorusTestFunction Lt Ls) :
    greenCLM_left_asym Lt Ls mass hmass h f =
    greenFunctionBilinear (E := AsymTorusTestFunction Lt Ls) mass hmass f h := rfl

/-- The restriction map `f ↦ (x ↦ evalAsymTorusAtSite x f)` as a CLM. -/
private def evalLatticeMapAsym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] :
    AsymTorusTestFunction Lt Ls →L[ℝ] AsymLatticeField Nt Ns where
  toFun f := fun x => evalAsymTorusAtSite Lt Ls Nt Ns x f
  map_add' f₁ f₂ := funext fun x => map_add (evalAsymTorusAtSite Lt Ls Nt Ns x) f₁ f₂
  map_smul' c f := funext fun x => map_smul (evalAsymTorusAtSite Lt Ls Nt Ns x) c f
  cont := continuous_pi fun x => (evalAsymTorusAtSite Lt Ls Nt Ns x).continuous

@[simp] private theorem evalLatticeMapAsym_apply (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (f : AsymTorusTestFunction Lt Ls) (x : AsymLatticeSites Nt Ns) :
    evalLatticeMapAsym Lt Ls Nt Ns f x = evalAsymTorusAtSite Lt Ls Nt Ns x f := rfl

/-- Lattice covariance CLM in the first argument (for fixed `Nt, Ns, a` and second argument). -/
private noncomputable def latticeCovCLM_left_asym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (g : AsymTorusTestFunction Lt Ls) :
    AsymTorusTestFunction Lt Ls →L[ℝ] ℝ :=
  let T := (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass).comp (evalLatticeMapAsym Lt Ls Nt Ns)
  (innerSL ℝ (T g)).comp T

private theorem latticeCovCLM_left_apply_asym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (f g : AsymTorusTestFunction Lt Ls) :
    latticeCovCLM_left_asym Lt Ls Nt Ns a mass ha hmass g f =
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
      (fun x => evalAsymTorusAtSite Lt Ls Nt Ns x f)
      (fun x => evalAsymTorusAtSite Lt Ls Nt Ns x g) := by
  simp only [latticeCovCLM_left_asym, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    covariance, evalLatticeMapAsym]
  exact real_inner_comm _ _

/-- DM expansion of the lattice covariance in the first argument. -/
private theorem covariance_dm_expansion_left_asym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass) (f g : AsymTorusTestFunction Lt Ls) :
    covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
      (fun x => evalAsymTorusAtSite Lt Ls Nt Ns x f)
      (fun x => evalAsymTorusAtSite Lt Ls Nt Ns x g) =
    ∑' m, DyninMityaginSpace.coeff m f *
      covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
        (fun x => evalAsymTorusAtSite Lt Ls Nt Ns x (DyninMityaginSpace.basis m))
        (fun x => evalAsymTorusAtSite Lt Ls Nt Ns x g) := by
  rw [← latticeCovCLM_left_apply_asym]
  rw [DyninMityaginSpace.expansion (latticeCovCLM_left_asym Lt Ls Nt Ns a mass ha hmass g) f]
  congr 1; ext m
  rw [latticeCovCLM_left_apply_asym]

/-- Summability of `1 / ((1+p₁)²·(1+p₂)²)` over `ℕ × ℕ`. -/
private theorem summable_inv_sq_sq_asym :
    Summable (fun p : ℕ × ℕ =>
      1 / ((1 + (p.1 : ℝ)) ^ 2 * (1 + (p.2 : ℝ)) ^ 2)) := by
  have h1d : Summable (fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 2) := by
    have hps := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      Nat.succ_injective
    exact hps.congr fun n => by simp only [Function.comp, Nat.cast_succ, add_comm]
  exact (h1d.mul_of_nonneg h1d (fun _ => by positivity) (fun _ => by positivity)).congr
    fun p => by simp [mul_comm]

/-- Uniform bound on `|B(pure(f₁,f₂), pure(g₁,g₂))|` using flat bounds for `f` and quadratic
bounds for `g`. -/
private theorem lattice_covariance_pure_abs_le_asym (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns]
    (a mass : ℝ) (ha : 0 < a) (hmass : 0 < mass)
    (f₁ g₁ : SmoothMap_Circle Lt ℝ) (f₂ g₂ : SmoothMap_Circle Ls ℝ)
    {Af₁ Af₂ Cg₁ Cg₂ : ℝ}
    (hAf₁ : 0 ≤ Af₁) (hAf₂ : 0 ≤ Af₂) (hCg₁ : 0 ≤ Cg₁) (hCg₂ : 0 ≤ Cg₂)
    (hf₁ : ∀ m, |latticeDFTCoeff1d Lt Nt f₁ m| ≤ Af₁)
    (hg₁ : ∀ m, |latticeDFTCoeff1d Lt Nt g₁ m| ≤ Cg₁ / (1 + (m : ℝ)) ^ 2)
    (hf₂ : ∀ m, |latticeDFTCoeff1d Ls Ns f₂ m| ≤ Af₂)
    (hg₂ : ∀ m, |latticeDFTCoeff1d Ls Ns g₂ m| ≤ Cg₂ / (1 + (m : ℝ)) ^ 2) :
    |covariance (spectralLatticeCovarianceAsym Nt Ns a mass ha hmass)
      (fun x => evalAsymTorusAtSite Lt Ls Nt Ns x (NuclearTensorProduct.pure f₁ f₂))
      (fun x => evalAsymTorusAtSite Lt Ls Nt Ns x (NuclearTensorProduct.pure g₁ g₂))| ≤
    Af₁ * Cg₁ * Af₂ * Cg₂ / mass ^ 2 *
      ∑' p : ℕ × ℕ, 1 / ((1 + (p.1 : ℝ)) ^ 2 * (1 + (p.2 : ℝ)) ^ 2) := by
  rw [lattice_covariance_eq_tsum_pure_asym]
  have hmass_sq := sq_pos_of_pos hmass
  have hNtk : (Nt - 1) + 1 = Nt := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne Nt))
  have hNsk : (Ns - 1) + 1 = Ns := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne Ns))
  have h_summable : Summable (latticeGreenTerm2dAsym Lt Ls Nt Ns a mass f₁ g₁ f₂ g₂) := by
    obtain ⟨Cf₁, hCf₁_nn, hCf₁⟩ := latticeDFTCoeff1d_quadratic_bound Lt f₁
    obtain ⟨Cg₁', hCg₁'_nn, hCg₁'⟩ := latticeDFTCoeff1d_quadratic_bound Lt g₁
    obtain ⟨Cf₂, hCf₂_nn, hCf₂⟩ := latticeDFTCoeff1d_quadratic_bound Ls f₂
    obtain ⟨Cg₂', hCg₂'_nn, hCg₂'⟩ := latticeDFTCoeff1d_quadratic_bound Ls g₂
    refine Summable.of_norm_bounded (summable_bound_asym mass hmass _) fun p =>
      latticeGreenTerm2dAsym_norm_le Lt Ls Nt Ns a mass hmass f₁ g₁ f₂ g₂
        hCf₁_nn hCg₁'_nn hCf₂_nn hCg₂'_nn
        (fun m => by have := hCf₁ (Nt - 1) m; simpa only [hNtk] using this)
        (fun m => by have := hCg₁' (Nt - 1) m; simpa only [hNtk] using this)
        (fun m => by have := hCf₂ (Ns - 1) m; simpa only [hNsk] using this)
        (fun m => by have := hCg₂' (Ns - 1) m; simpa only [hNsk] using this) p
  calc |∑' p, latticeGreenTerm2dAsym Lt Ls Nt Ns a mass f₁ g₁ f₂ g₂ p|
      ≤ ∑' p, |latticeGreenTerm2dAsym Lt Ls Nt Ns a mass f₁ g₁ f₂ g₂ p| := by
        have h := norm_tsum_le_tsum_norm h_summable.norm
        simp only [Real.norm_eq_abs] at h; exact h
    _ ≤ ∑' p : ℕ × ℕ, Af₁ * Cg₁ * Af₂ * Cg₂ /
        (mass ^ 2 * (1 + (p.1 : ℝ)) ^ 2 * (1 + (p.2 : ℝ)) ^ 2) := by
        have hg_sum : Summable (fun p : ℕ × ℕ => Af₁ * Cg₁ * Af₂ * Cg₂ /
            (mass ^ 2 * (1 + (p.1 : ℝ)) ^ 2 * (1 + (p.2 : ℝ)) ^ 2)) :=
          (summable_inv_sq_sq_asym.mul_left (Af₁ * Cg₁ * Af₂ * Cg₂ / mass ^ 2)).congr
            fun p => by field_simp
        apply h_summable.abs.tsum_le_tsum _ hg_sum
        intro p
        by_cases h_range : p.1 < Nt ∧ p.2 < Ns
        · obtain ⟨hp1_lt, hp2_lt⟩ := h_range
          unfold latticeGreenTerm2dAsym
          rw [abs_div, abs_mul, abs_mul, abs_mul]
          have hden_pos : 0 < (latticeEigenvalue1d Nt a p.1 + latticeEigenvalue1d Ns a p.2 +
              mass ^ 2) * latticeFourierNormSq Nt p.1 * latticeFourierNormSq Ns p.2 := by
            apply mul_pos (mul_pos _ _) _
            · linarith [latticeEigenvalue1d_nonneg Nt a p.1,
                         latticeEigenvalue1d_nonneg Ns a p.2, sq_pos_of_pos hmass]
            · exact latticeFourierNormSq_pos Nt p.1 hp1_lt
            · exact latticeFourierNormSq_pos Ns p.2 hp2_lt
          rw [abs_of_pos hden_pos]
          have hnum : |latticeDFTCoeff1d Lt Nt f₁ p.1| * |latticeDFTCoeff1d Lt Nt g₁ p.1| *
              |latticeDFTCoeff1d Ls Ns f₂ p.2| * |latticeDFTCoeff1d Ls Ns g₂ p.2| ≤
              Af₁ * (Cg₁ / (1 + (p.1 : ℝ)) ^ 2) * Af₂ * (Cg₂ / (1 + (p.2 : ℝ)) ^ 2) := by
            apply mul_le_mul
            · apply mul_le_mul
              · exact mul_le_mul (hf₁ p.1) (hg₁ p.1) (abs_nonneg _) hAf₁
              · exact hf₂ p.2
              · exact abs_nonneg _
              · exact mul_nonneg hAf₁ (div_nonneg hCg₁ (by positivity))
            · exact hg₂ p.2
            · exact abs_nonneg _
            · positivity
          set den := (latticeEigenvalue1d Nt a p.1 + latticeEigenvalue1d Ns a p.2 + mass ^ 2) *
              latticeFourierNormSq Nt p.1 * latticeFourierNormSq Ns p.2
          have hden_ge : mass ^ 2 ≤ den := by
            have h_ns1 := latticeFourierNormSq_ge_one Nt p.1 hp1_lt
            have h_ns2 := latticeFourierNormSq_ge_one Ns p.2 hp2_lt
            have h_eig_sum_pos : 0 < latticeEigenvalue1d Nt a p.1 + latticeEigenvalue1d Ns a p.2 +
                mass ^ 2 := by
              linarith [latticeEigenvalue1d_nonneg Nt a p.1,
                         latticeEigenvalue1d_nonneg Ns a p.2, sq_pos_of_pos hmass]
            calc mass ^ 2
                ≤ latticeEigenvalue1d Nt a p.1 + latticeEigenvalue1d Ns a p.2 + mass ^ 2 :=
                  by linarith [latticeEigenvalue1d_nonneg Nt a p.1,
                               latticeEigenvalue1d_nonneg Ns a p.2]
              _ ≤ (latticeEigenvalue1d Nt a p.1 + latticeEigenvalue1d Ns a p.2 + mass ^ 2) *
                  latticeFourierNormSq Nt p.1 := le_mul_of_one_le_right h_eig_sum_pos.le h_ns1
              _ ≤ den := le_mul_of_one_le_right
                  (mul_nonneg h_eig_sum_pos.le (le_of_lt (latticeFourierNormSq_pos Nt p.1 hp1_lt)))
                  h_ns2
          calc |latticeDFTCoeff1d Lt Nt f₁ p.1| * |latticeDFTCoeff1d Lt Nt g₁ p.1| *
                |latticeDFTCoeff1d Ls Ns f₂ p.2| * |latticeDFTCoeff1d Ls Ns g₂ p.2| / den
              ≤ Af₁ * (Cg₁ / (1 + (p.1:ℝ)) ^ 2) * Af₂ * (Cg₂ / (1 + (p.2:ℝ)) ^ 2) / den :=
                  div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
            _ ≤ Af₁ * (Cg₁ / (1 + (p.1:ℝ)) ^ 2) * Af₂ * (Cg₂ / (1 + (p.2:ℝ)) ^ 2) / mass ^ 2 := by
                  apply div_le_div_of_nonneg_left
                  · positivity
                  · exact hmass_sq
                  · exact hden_ge
            _ = Af₁ * Cg₁ * Af₂ * Cg₂ /
                (mass ^ 2 * (1 + (p.1:ℝ)) ^ 2 * (1 + (p.2:ℝ)) ^ 2) := by field_simp
        · rw [not_and_or, not_lt, not_lt] at h_range
          rw [show |latticeGreenTerm2dAsym Lt Ls Nt Ns a mass f₁ g₁ f₂ g₂ p| = 0 from by
            rw [latticeGreenTerm2dAsym_zero_of_ge Lt Ls Nt Ns a mass f₁ g₁ f₂ g₂ p h_range,
              abs_zero]]
          positivity
    _ = Af₁ * Cg₁ * Af₂ * Cg₂ / mass ^ 2 *
        ∑' p : ℕ × ℕ, 1 / ((1 + (p.1 : ℝ)) ^ 2 * (1 + (p.2 : ℝ)) ^ 2) := by
        rw [← tsum_mul_left]; congr 1; ext p
        have : mass ^ 2 ≠ 0 := ne_of_gt hmass_sq
        have : (1 + (p.1 : ℝ)) ^ 2 ≠ 0 := ne_of_gt (by positivity)
        have : (1 + (p.2 : ℝ)) ^ 2 ≠ 0 := ne_of_gt (by positivity)
        field_simp

/-- Explicit quadratic DFT bound with Sobolev-seminorm constant (general circle size `L`).
Allows polynomial-in-`k` bounds for `basis k`. -/
private theorem latticeDFTCoeff1d_seminorm_quadratic_gen (L : ℝ) [hL : Fact (0 < L)]
    (f : SmoothMap_Circle L ℝ) (N m : ℕ) :
    |latticeDFTCoeff1d L (N + 1) f m| ≤
      (Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 0 f +
       Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 2 f * L ^ 2) /
      (1 + (m : ℝ)) ^ 2 := by
  set C₀ := Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 0 f
  set C₂ := Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 2 f
  set Cd := C₂ * L ^ 2
  set C := C₀ + Cd
  have hC₀_nn : 0 ≤ C₀ := by positivity
  have hC₂_nn : 0 ≤ C₂ := by positivity
  have hC_nn : 0 ≤ C := by positivity
  by_cases hm_lt : m < N + 1
  · by_cases hm0 : m = 0
    · subst hm0; simp only [Nat.cast_zero, add_zero, one_pow, div_one]
      exact (latticeDFTCoeff1d_flat_bound L f N 0).trans (le_add_of_nonneg_right (by positivity))
    · have hm_pos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      haveI hN1 : NeZero (N + 1) := ⟨by omega⟩
      have h_transfer := eigenvector_transfer L (N + 1) f m hm_lt
      have h_lap := laplacianDFT_flat_bound L (N + 1) f m
      have h_eig := latticeEigenvalue1d_ge_quadratic L (N + 1) m hm_pos hm_lt
      have h_eig_pos : 0 < latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m :=
        lt_of_lt_of_le (by have := hL.out; positivity) h_eig
      rw [← h_transfer] at h_lap
      have h_abs : |latticeDFTCoeff1d L (N + 1) f m| ≤
          C₂ / latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m := by
        rw [abs_mul, abs_of_pos h_eig_pos] at h_lap
        rw [le_div_iff₀ h_eig_pos, mul_comm]
        exact h_lap
      have hL_pos := hL.out
      have h_denom_pos : (0 : ℝ) < (1 + ↑m) ^ 2 / L ^ 2 := by positivity
      calc |latticeDFTCoeff1d L (N + 1) f m|
          ≤ C₂ / latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m := h_abs
        _ ≤ C₂ / ((1 + ↑m) ^ 2 / L ^ 2) := div_le_div_of_nonneg_left hC₂_nn h_denom_pos h_eig
        _ = Cd / (1 + ↑m) ^ 2 := by simp only [Cd]; field_simp
        _ ≤ C / (1 + ↑m) ^ 2 := div_le_div_of_nonneg_right (by linarith) (by positivity)
  · rw [latticeDFTCoeff1d_zero_of_ge L (N + 1) f m (by omega), abs_zero]
    exact div_nonneg hC_nn (by positivity)

/-- **Convergence for general `f`, pure `g`** (Phase A), via DM expansion of `f`. -/
private theorem lattice_green_tendsto_pure_right_asym
    (mass : ℝ) (hmass : 0 < mass)
    (Nt Ns : ℕ → ℕ) (a : ℕ → ℝ)
    (hNt : ∀ k, NeZero (Nt k)) (hNs : ∀ k, NeZero (Ns k))
    (ha : ∀ k, 0 < a k) (hLt : ∀ k, (Nt k : ℝ) * a k = Lt) (hLs : ∀ k, (Ns k : ℝ) * a k = Ls)
    (ha0 : Tendsto a atTop (nhds 0))
    (f : AsymTorusTestFunction Lt Ls)
    (g₁ : SmoothMap_Circle Lt ℝ) (g₂ : SmoothMap_Circle Ls ℝ) :
    Tendsto (fun k => haveI := hNt k; haveI := hNs k
        covariance (spectralLatticeCovarianceAsym (Nt k) (Ns k) (a k) mass (ha k) hmass)
          (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x f)
          (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x (NuclearTensorProduct.pure g₁ g₂)))
      atTop
      (nhds (greenFunctionBilinear (E := AsymTorusTestFunction Lt Ls) mass hmass
        f (NuclearTensorProduct.pure g₁ g₂))) := by
  have h_expand : ∀ k, (haveI := hNt k; haveI := hNs k
      covariance (spectralLatticeCovarianceAsym (Nt k) (Ns k) (a k) mass (ha k) hmass)
        (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x f)
        (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x (NuclearTensorProduct.pure g₁ g₂))) =
      ∑' m, DyninMityaginSpace.coeff m f *
        (haveI := hNt k; haveI := hNs k
        covariance (spectralLatticeCovarianceAsym (Nt k) (Ns k) (a k) mass (ha k) hmass)
          (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x (DyninMityaginSpace.basis m))
          (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x (NuclearTensorProduct.pure g₁ g₂))) :=
    fun k => by
      haveI := hNt k; haveI := hNs k
      exact covariance_dm_expansion_left_asym Lt Ls (Nt k) (Ns k) (a k) mass (ha k) hmass f
        (NuclearTensorProduct.pure g₁ g₂)
  simp_rw [h_expand]
  have h_G_expand : greenFunctionBilinear (E := AsymTorusTestFunction Lt Ls) mass hmass f
      (NuclearTensorProduct.pure g₁ g₂) =
      ∑' m, DyninMityaginSpace.coeff m f *
        greenFunctionBilinear (E := AsymTorusTestFunction Lt Ls) mass hmass
          (DyninMityaginSpace.basis m) (NuclearTensorProduct.pure g₁ g₂) := by
    have := DyninMityaginSpace.expansion (greenCLM_left_asym Lt Ls mass hmass
      (NuclearTensorProduct.pure g₁ g₂)) f
    simp only [greenCLM_left_apply_asym] at this
    exact this
  rw [h_G_expand]
  obtain ⟨Cg₁, hCg₁_nn, hCg₁⟩ := latticeDFTCoeff1d_quadratic_bound Lt g₁
  obtain ⟨Cg₂, hCg₂_nn, hCg₂⟩ := latticeDFTCoeff1d_quadratic_bound Ls g₂
  obtain ⟨A₁, hA₁_pos, r₁, hA₁⟩ :=
    DyninMityaginSpace.basis_growth (E := SmoothMap_Circle Lt ℝ) (0 : ℕ)
  obtain ⟨A₂, hA₂_pos, r₂, hA₂⟩ :=
    DyninMityaginSpace.basis_growth (E := SmoothMap_Circle Ls ℝ) (0 : ℕ)
  set Sb₁ := Real.sqrt (2 * Lt) * A₁
  set Sb₂ := Real.sqrt (2 * Ls) * A₂
  set S₂ := ∑' p : ℕ × ℕ, 1 / ((1 + (p.1 : ℝ)) ^ 2 * (1 + (p.2 : ℝ)) ^ 2)
  have hS₂_nn : 0 ≤ S₂ := tsum_nonneg fun p => by positivity
  set K := Sb₁ * Cg₁ * Sb₂ * Cg₂ / mass ^ 2 * S₂ with hK_def
  have hK_nn : 0 ≤ K := by
    rw [hK_def]
    exact mul_nonneg (div_nonneg (by positivity) (by positivity)) hS₂_nn
  have h_BN_bound : ∀ m k, (haveI := hNt k; haveI := hNs k
      |covariance (spectralLatticeCovarianceAsym (Nt k) (Ns k) (a k) mass (ha k) hmass)
        (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x (DyninMityaginSpace.basis m))
        (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
          (NuclearTensorProduct.pure g₁ g₂))|) ≤
      K * (1 + ((Nat.unpair m).1 : ℝ)) ^ r₁ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₂ := by
    intro m k
    haveI := hNt k; haveI := hNs k
    have hk1 : (Nt k - 1) + 1 = Nt k :=
      Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne (Nt k)))
    have hk2 : (Ns k - 1) + 1 = Ns k :=
      Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne (Ns k)))
    rw [ntp_basis_eq_pure_asym Lt Ls m]
    have hf₁ : ∀ j, |latticeDFTCoeff1d Lt (Nt k)
        (DyninMityaginSpace.basis (Nat.unpair m).1) j| ≤
        Sb₁ * (1 + ((Nat.unpair m).1 : ℝ)) ^ r₁ := fun j => by
      have hflat := latticeDFTCoeff1d_flat_bound Lt
        (DyninMityaginSpace.basis (Nat.unpair m).1) (Nt k - 1) j
      simp only [hk1] at hflat
      calc |latticeDFTCoeff1d Lt (Nt k) (DyninMityaginSpace.basis (Nat.unpair m).1) j|
          ≤ Real.sqrt (2 * Lt) *
            SmoothMap_Circle.sobolevSeminorm 0 (DyninMityaginSpace.basis (Nat.unpair m).1) := hflat
        _ ≤ Real.sqrt (2 * Lt) * (A₁ * (1 + ((Nat.unpair m).1 : ℝ)) ^ r₁) :=
            mul_le_mul_of_nonneg_left (hA₁ _) (Real.sqrt_nonneg _)
        _ = Sb₁ * (1 + ((Nat.unpair m).1 : ℝ)) ^ r₁ := by ring
    have hf₂ : ∀ j, |latticeDFTCoeff1d Ls (Ns k)
        (DyninMityaginSpace.basis (Nat.unpair m).2) j| ≤
        Sb₂ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₂ := fun j => by
      have hflat := latticeDFTCoeff1d_flat_bound Ls
        (DyninMityaginSpace.basis (Nat.unpair m).2) (Ns k - 1) j
      simp only [hk2] at hflat
      calc |latticeDFTCoeff1d Ls (Ns k) (DyninMityaginSpace.basis (Nat.unpair m).2) j|
          ≤ Real.sqrt (2 * Ls) *
            SmoothMap_Circle.sobolevSeminorm 0 (DyninMityaginSpace.basis (Nat.unpair m).2) := hflat
        _ ≤ Real.sqrt (2 * Ls) * (A₂ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₂) :=
            mul_le_mul_of_nonneg_left (hA₂ _) (Real.sqrt_nonneg _)
        _ = Sb₂ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₂ := by ring
    have hgg₁ : ∀ j, |latticeDFTCoeff1d Lt (Nt k) g₁ j| ≤ Cg₁ / (1 + (j : ℝ)) ^ 2 := fun j => by
      have := hCg₁ (Nt k - 1) j; simpa only [hk1] using this
    have hgg₂ : ∀ j, |latticeDFTCoeff1d Ls (Ns k) g₂ j| ≤ Cg₂ / (1 + (j : ℝ)) ^ 2 := fun j => by
      have := hCg₂ (Ns k - 1) j; simpa only [hk2] using this
    calc |covariance (spectralLatticeCovarianceAsym (Nt k) (Ns k) (a k) mass (ha k) hmass)
            (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
              (NuclearTensorProduct.pure (DyninMityaginSpace.basis (Nat.unpair m).1)
                (DyninMityaginSpace.basis (Nat.unpair m).2)))
            (fun x => evalAsymTorusAtSite Lt Ls (Nt k) (Ns k) x
              (NuclearTensorProduct.pure g₁ g₂))|
        ≤ (Sb₁ * (1 + ((Nat.unpair m).1 : ℝ)) ^ r₁) * Cg₁ *
          (Sb₂ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₂) * Cg₂ / mass ^ 2 * S₂ :=
            lattice_covariance_pure_abs_le_asym Lt Ls (Nt k) (Ns k) (a k) mass (ha k) hmass
              _ g₁ _ g₂ (by positivity) (by positivity) hCg₁_nn hCg₂_nn hf₁ hgg₁ hf₂ hgg₂
      _ = K * (1 + ((Nat.unpair m).1 : ℝ)) ^ r₁ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₂ := by
          rw [hK_def]; ring
  set rr := r₁ + r₂
  obtain ⟨D, hD_pos, sD, hD⟩ :=
    DyninMityaginSpace.coeff_decay (E := AsymTorusTestFunction Lt Ls) (rr + 2)
  have h_dom_summable : Summable (fun m : ℕ => |DyninMityaginSpace.coeff m f| * K *
      (1 + ((Nat.unpair m).1 : ℝ)) ^ r₁ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₂) := by
    have h_bound : ∀ m, |DyninMityaginSpace.coeff m f| * K *
        (1 + ((Nat.unpair m).1 : ℝ)) ^ r₁ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₂ ≤
        D * (sD.sup (DyninMityaginSpace.p (E := AsymTorusTestFunction Lt Ls))) f * K /
        (1 + (m : ℝ)) ^ 2 := by
      intro m
      have h_unpair_le : (1 + ((Nat.unpair m).1 : ℝ)) ^ r₁ *
          (1 + ((Nat.unpair m).2 : ℝ)) ^ r₂ ≤ (1 + (m : ℝ)) ^ rr := by
        calc (1 + ((Nat.unpair m).1 : ℝ)) ^ r₁ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₂
            ≤ (1 + (m : ℝ)) ^ r₁ * (1 + (m : ℝ)) ^ r₂ := by
              apply mul_le_mul
              · gcongr; exact_mod_cast Nat.unpair_left_le m
              · gcongr; exact_mod_cast Nat.unpair_right_le m
              · positivity
              · positivity
          _ = (1 + (m : ℝ)) ^ rr := by rw [← pow_add]
      have hD_bound := hD f m
      calc |DyninMityaginSpace.coeff m f| * K *
            (1 + ((Nat.unpair m).1 : ℝ)) ^ r₁ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₂
          = |DyninMityaginSpace.coeff m f| *
            ((1 + ((Nat.unpair m).1 : ℝ)) ^ r₁ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₂) * K := by
              ring
        _ ≤ |DyninMityaginSpace.coeff m f| * (1 + (m : ℝ)) ^ rr * K := by
              apply mul_le_mul_of_nonneg_right _ hK_nn
              exact mul_le_mul_of_nonneg_left h_unpair_le (abs_nonneg _)
        _ = (|DyninMityaginSpace.coeff m f| * (1 + (m : ℝ)) ^ (rr + 2)) *
            (K / (1 + (m : ℝ)) ^ 2) := by
              have : (1 + (m : ℝ)) ^ 2 ≠ 0 := ne_of_gt (by positivity)
              field_simp; ring
        _ ≤ (D * (sD.sup (DyninMityaginSpace.p (E := AsymTorusTestFunction Lt Ls))) f) *
            (K / (1 + (m : ℝ)) ^ 2) :=
            mul_le_mul_of_nonneg_right hD_bound (div_nonneg hK_nn (by positivity))
        _ = D * (sD.sup (DyninMityaginSpace.p (E := AsymTorusTestFunction Lt Ls))) f * K /
            (1 + (m : ℝ)) ^ 2 := by ring
    apply Summable.of_nonneg_of_le (fun m => by positivity) h_bound
    have hps := (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2)).comp_injective
      Nat.succ_injective
    have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) :=
      hps.congr fun n => by simp only [Function.comp, Nat.cast_succ]
    exact (h1.mul_left
      (D * (sD.sup (DyninMityaginSpace.p (E := AsymTorusTestFunction Lt Ls))) f * K)).congr
      fun n => by ring
  apply tendsto_tsum_of_dominated_convergence
    (bound := fun m => |DyninMityaginSpace.coeff m f| * K *
      (1 + ((Nat.unpair m).1 : ℝ)) ^ r₁ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₂)
  · exact h_dom_summable
  · intro m
    apply Filter.Tendsto.const_mul
    rw [ntp_basis_eq_pure_asym Lt Ls m]
    exact lattice_green_tendsto_continuum_asym_pure Lt Ls mass hmass Nt Ns a hNt hNs ha hLt hLs ha0
      _ g₁ _ g₂
  · apply Filter.Eventually.of_forall
    intro k m
    haveI := hNt k; haveI := hNs k
    rw [Real.norm_eq_abs, abs_mul]
    have hrhs : |DyninMityaginSpace.coeff m f| * K *
        (1 + ((Nat.unpair m).1 : ℝ)) ^ r₁ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₂ =
        |DyninMityaginSpace.coeff m f| * (K *
        (1 + ((Nat.unpair m).1 : ℝ)) ^ r₁ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₂) := by ring
    rw [hrhs]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [abs_le]
    refine ⟨?_, le_trans (le_abs_self _) (h_BN_bound m k)⟩
    have := (abs_le.mp (h_BN_bound m k)).1; linarith

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
