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
