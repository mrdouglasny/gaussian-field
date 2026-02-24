/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Spectral Covariance Construction

Constructs the lattice covariance CLM `T : FinLatticeField → ℓ²` via the
spectral theorem for the mass operator matrix Q = -Δ + m².

The key property is `⟨Tf, Tg⟩_ℓ² = ⟨f, Q⁻¹g⟩_L²`, which is needed for the
density bridge (showing the Gaussian measure has density exp(-½⟨φ,Qφ⟩)).

## Main definitions

- `massOperatorMatrix` — the mass operator as a real symmetric matrix
- `spectralLatticeCovariance` — the CLM `T = Q^{-1/2}` into ℓ²

## Main theorems

- `massOperatorMatrix_isHermitian` — Q is symmetric
- `massOperatorMatrix_eigenvalues_pos` — eigenvalues of Q are positive
- `spectralLatticeCovariance_inner` — `⟨Tf, Tg⟩ = Σ_x f(x)(Q⁻¹g)(x)`
- `spectralLatticeCovariance_norm_sq_eq` — `‖Tf‖² = Σ_x f(x)(Q⁻¹f)(x)`

## References

- Reed-Simon, Vol. 1, §VI (Spectral theorem)
- Glimm-Jaffe, §19 (Gaussian measures and covariance operators)
-/

import Lattice.Laplacian
import Lattice.FiniteField
import HeatKernel.Axioms
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace GaussianField

open MeasureTheory Matrix

variable (d N : ℕ) [NeZero N]

/-! ## Mass operator as a matrix -/

/-- The "matrix entries" of the mass operator: the bilinear form evaluated
on delta functions. `Q(x,y) = ⟨δ_x, (-Δ+m²)(δ_y)⟩ = (Q δ_y)(x)`. -/
def massOperatorEntry (a mass : ℝ)
    (x y : FinLatticeSites d N) : ℝ :=
  (massOperator d N a mass (finLatticeDelta d N y)) x

/-- The mass operator `Q = -Δ + m²` as a matrix indexed by lattice sites.
Entry `(x, y)` is `⟨δ_x, Q(δ_y)⟩ = (Q δ_y)(x)`. -/
def massOperatorMatrix (a mass : ℝ) :
    Matrix (FinLatticeSites d N) (FinLatticeSites d N) ℝ :=
  fun x y => massOperatorEntry d N a mass x y

/-! ## Self-adjointness -/

/-- The mass operator is self-adjoint: `⟨f, Qg⟩ = ⟨Qf, g⟩`. -/
theorem massOperator_selfAdjoint (a mass : ℝ)
    (f g : FinLatticeField d N) :
    ∑ x, f x * (massOperator d N a mass g) x =
    ∑ x, (massOperator d N a mass f) x * g x := by
  simp only [massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul]
  -- Split into Laplacian and mass terms
  have split_l : ∀ x, f x * (-(finiteLaplacian d N a g) x + mass ^ 2 * g x) =
      -(f x * (finiteLaplacian d N a g) x) + mass ^ 2 * (f x * g x) := by
    intro x; ring
  have split_r : ∀ x, (-(finiteLaplacian d N a f) x + mass ^ 2 * f x) * g x =
      -((finiteLaplacian d N a f) x * g x) + mass ^ 2 * (f x * g x) := by
    intro x; ring
  simp_rw [split_l, split_r, Finset.sum_add_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum]
  congr 1
  -- The Laplacian part follows from finiteLaplacian_selfAdjoint
  rw [finiteLaplacian_selfAdjoint d N a f g]

/-- The mass operator matrix is Hermitian (symmetric over ℝ).

Proof: Self-adjointness of Q applied to delta functions gives
`Q(x,y) = (Qδ_y)(x) = ⟨δ_x, Qδ_y⟩ = ⟨Qδ_x, δ_y⟩ = (Qδ_x)(y) = Q(y,x)`. -/
theorem massOperatorMatrix_isHermitian (a mass : ℝ) :
    (massOperatorMatrix d N a mass).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp only [conjTranspose_apply, star_trivial]
  -- Need: massOperatorEntry j i = massOperatorEntry i j
  -- Use self-adjointness with f = δ_j, g = δ_i
  have h := massOperator_selfAdjoint d N a mass
    (finLatticeDelta d N j) (finLatticeDelta d N i)
  -- LHS: ∑ x, δ_j(x) * (Q δ_i)(x) = (Q δ_i)(j) = massOperatorEntry j i
  have lhs_eq : ∑ x, (finLatticeDelta d N j) x * (massOperator d N a mass (finLatticeDelta d N i)) x =
      massOperatorEntry d N a mass j i := by
    simp only [finLatticeDelta, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, massOperatorEntry]
  -- RHS: ∑ x, (Q δ_j)(x) * δ_i(x) = (Q δ_j)(i) = massOperatorEntry i j
  have rhs_eq : ∑ x, (massOperator d N a mass (finLatticeDelta d N j)) x * (finLatticeDelta d N i) x =
      massOperatorEntry d N a mass i j := by
    simp only [finLatticeDelta, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true, massOperatorEntry]
  rw [lhs_eq, rhs_eq] at h
  -- h : massOperatorEntry j i = massOperatorEntry i j
  -- goal : massOperatorMatrix j i = massOperatorMatrix i j
  show massOperatorMatrix d N a mass j i = massOperatorMatrix d N a mass i j
  simp only [massOperatorMatrix]
  exact h

/-! ## Eigenvectors and eigenvalues -/

/-- Abbreviation for the Hermiticity proof. -/
abbrev massMatrixHerm (a mass : ℝ) :=
  massOperatorMatrix_isHermitian d N a mass

/-- Eigenvalues of the mass operator matrix. -/
def massEigenvalues (a mass : ℝ) : FinLatticeSites d N → ℝ :=
  (massMatrixHerm d N a mass).eigenvalues

/-- Eigenvector orthonormal basis of the mass operator matrix. -/
def massEigenvectorBasis (a mass : ℝ) :
    OrthonormalBasis (FinLatticeSites d N) ℝ (EuclideanSpace ℝ (FinLatticeSites d N)) :=
  (massMatrixHerm d N a mass).eigenvectorBasis

/-- Basis decomposition: any lattice field is a linear combination of deltas. -/
private lemma field_basis_decomp (φ : FinLatticeField d N) :
    φ = ∑ y : FinLatticeSites d N, φ y • finLatticeDelta d N y := by
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, finLatticeDelta,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- The mass operator applied to f equals the matrix-vector product.

This bridges the CLM `massOperator` with the matrix `massOperatorMatrix`:
`(Q f)(x) = Σ_y Q(x,y) · f(y) = (M *ᵥ f)(x)`. -/
theorem massOperator_eq_matrix_mulVec (a mass : ℝ)
    (f : FinLatticeField d N) (x : FinLatticeSites d N) :
    (massOperator d N a mass f) x =
    (massOperatorMatrix d N a mass).mulVec f x := by
  -- (Q f)(x) = Σ_y Q(x,y) f(y) = (M *ᵥ f)(x) by linearity + basis expansion
  simp only [Matrix.mulVec, massOperatorMatrix]
  conv_lhs => rw [field_basis_decomp d N f]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1; ext y
  -- f y * (Q δ_y)(x) = massOperatorEntry x y * f y
  unfold massOperatorEntry
  ring

/-- Eigenvalues of the mass operator are strictly positive.

Proof: Q is positive definite. For eigenvector e_k with eigenvalue λ_k:
`0 < ⟨e_k, Q e_k⟩ = λ_k ⟨e_k, e_k⟩ = λ_k`. -/
theorem massOperatorMatrix_eigenvalues_pos (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (k : FinLatticeSites d N) :
    0 < massEigenvalues d N a mass k := by
  unfold massEigenvalues
  -- The mass operator Q = -Δ + m² is positive definite (massOperator_pos_def).
  -- For eigenvector e_k with eigenvalue λ_k:
  --   0 < ⟨e_k, Q e_k⟩ = λ_k ⟨e_k, e_k⟩ = λ_k
  -- since e_k is a unit vector from the orthonormal eigenbasis.
  sorry

/-! ## Spectral covariance CLM -/

/-- The spectral lattice covariance: `T = Q^{-1/2}` as a CLM into ℓ².

For `f : FinLatticeField d N`, defines:
  `(Tf)(m) = λ_m^{-1/2} · ⟪e_m, f⟫_L²`   for `m < N^d`
  `(Tf)(m) = 0`                              otherwise

where `{e_m}` is the eigenvector ONB of Q and `λ_m` its eigenvalues.
Maps into `ell2'` via the Fintype enumeration of lattice sites. -/
noncomputable def spectralLatticeCovariance (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    FinLatticeField d N →L[ℝ] ell2' := by
  -- Build as a CLM via finite-dimensionality (any linear map is continuous)
  -- The linear map sends f to ∑_k λ_k^{-1/2} ⟪e_k, f⟫ · ℓ²_k
  set eigvecs := massEigenvectorBasis d N a mass
  set eigvals := massEigenvalues d N a mass
  set enum := Fintype.equivFin (FinLatticeSites d N)
  -- Define the underlying linear map
  set L : FinLatticeField d N →ₗ[ℝ] ell2' :=
    { toFun := fun f => ∑ k : FinLatticeSites d N,
        ((Real.sqrt (eigvals k))⁻¹ *
         ∑ x : FinLatticeSites d N, (eigvecs k : EuclideanSpace ℝ _) x * f x) •
        lp.single 2 (enum k).val (1 : ℝ)
      map_add' := by intro f g; sorry
      map_smul' := by intro r f; sorry }
  -- Any linear map from a finite-dimensional space to a normed space is continuous
  exact L.mkContinuousOfExistsBound (by sorry)

/-- Key identity: `⟨Tf, Tg⟩_ℓ² = ∑ x, f(x) · (Q⁻¹g)(x)` where `Q⁻¹g`
is the inverse mass operator applied to g.

Equivalently: `⟨Tf, Tg⟩ = Σ_k λ_k⁻¹ · c_k(f) · c_k(g)`
where `c_k(f) = ⟪e_k, f⟫_L²` and `λ_k` are eigenvalues of Q. -/
theorem spectralLatticeCovariance_inner (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeField d N) :
    @inner ℝ ell2' _
      (spectralLatticeCovariance d N a mass ha hmass f)
      (spectralLatticeCovariance d N a mass ha hmass g) =
    ∑ k : FinLatticeSites d N,
      (massEigenvalues d N a mass k)⁻¹ *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x) := by
  sorry

/-- The ℓ² norm squared of `Tf` equals the quadratic form `⟨f, Q⁻¹f⟩_L²`.
This is `spectralLatticeCovariance_inner` with `g = f`. -/
theorem spectralLatticeCovariance_norm_sq (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f : FinLatticeField d N) :
    @inner ℝ ell2' _
      (spectralLatticeCovariance d N a mass ha hmass f)
      (spectralLatticeCovariance d N a mass ha hmass f) =
    ∑ k : FinLatticeSites d N,
      (massEigenvalues d N a mass k)⁻¹ *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) ^ 2 := by
  rw [spectralLatticeCovariance_inner]
  congr 1; ext k; ring

/-- Bridge between spectral form and site-basis bilinear form:
`Σ_k λ_k⁻¹ c_k(f) c_k(g) = Σ_x f(x) (Q⁻¹ g)(x)`.

The LHS is the spectral decomposition of `⟨f, Q⁻¹g⟩`; the RHS is its
site-basis expansion. These are equal by the completeness of the eigenbasis. -/
theorem spectral_eq_site_bilinear (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass)
    (f g : FinLatticeField d N) :
    ∑ k : FinLatticeSites d N,
      (massEigenvalues d N a mass k)⁻¹ *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * f x) *
      (∑ x, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x * g x) =
    ∑ x, f x *
      (∑ k : FinLatticeSites d N,
        (massEigenvalues d N a mass k)⁻¹ *
        (∑ y, (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) y * g y) *
        (massEigenvectorBasis d N a mass k : EuclideanSpace ℝ _) x) := by
  sorry

/-- The bounded sequence condition for the spectral singular values.
Needed to show the CLM maps into ℓ². -/
theorem spectral_singular_values_bounded (a mass : ℝ)
    (ha : 0 < a) (hmass : 0 < mass) :
    IsBoundedSeq (fun m =>
      if h : m < Fintype.card (FinLatticeSites d N) then
        Real.sqrt ((massEigenvalues d N a mass
          ((Fintype.equivFin _).symm ⟨m, h⟩))⁻¹)
      else 0) := by
  sorry

/-! ## Gaussian density

Defined here (rather than in FKG.lean) so that Density.lean can access it
without circular imports. -/

/-- The Gaussian density on `FinLatticeField d N` (unnormalized):
`ρ(φ) = exp(-½ ⟨φ, Qφ⟩)` where Q = -Δ_a + m² is the mass operator. -/
def gaussianDensity (a mass : ℝ)
    (φ : FinLatticeField d N) : ℝ :=
  Real.exp (-(1/2) * ∑ x : FinLatticeSites d N,
    φ x * (massOperator d N a mass φ) x)

/-- The Gaussian density is non-negative. -/
theorem gaussianDensity_nonneg (a mass : ℝ) (φ : FinLatticeField d N) :
    0 ≤ gaussianDensity d N a mass φ :=
  le_of_lt (Real.exp_pos _)

end GaussianField
