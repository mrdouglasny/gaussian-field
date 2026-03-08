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

/-! ## Spectral expansion of the matrix exponential

For a Hermitian matrix M with eigenvector basis ψ_k and eigenvalues μ_k,
the matrix exponential satisfies:
  `exp(-t · M) ψ_j = exp(-t · μ_j) · ψ_j`
and hence the bilinear form:
  `∑ x, f x · (exp(-tM) g) x = ∑ k, exp(-tμ_k) · c_k(f) · c_k(g)`

These results use Mathlib's abstract eigenvector basis from the spectral theorem
for Hermitian (real symmetric) matrices. -/

section MatrixExpSpectral

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Eigenvectors of a Hermitian matrix are eigenvectors of its matrix exponential.

If `M ψ_j = μ_j · ψ_j`, then `exp(-t·M) ψ_j = exp(-t·μ_j) · ψ_j`.

The proof uses:
- Spectral theorem: `M = U · diagonal(μ) · U*`
- `exp_units_conj`: `exp(U A U⁻¹) = U exp(A) U⁻¹`
- `exp_diagonal`: `exp(diagonal v) = diagonal(exp v)` -/
theorem Matrix.IsHermitian.mulVec_exp_neg_smul
    {M : Matrix n n ℝ} (hM : M.IsHermitian) (t : ℝ) (j : n) :
    (NormedSpace.exp ((-t) • M)) *ᵥ ⇑(hM.eigenvectorBasis j) =
    Real.exp (-t * hM.eigenvalues j) • ⇑(hM.eigenvectorBasis j) := by
  set U := hM.eigenvectorUnitary
  have hspec := hM.spectral_theorem
  simp only [RCLike.ofReal_real_eq_id] at hspec
  -- -t • M = conjStarAlgAut U (-t • diagonal eigenvalues)
  have hsmul : (-t) • M =
      Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) U ((-t) • diagonal (id ∘ hM.eigenvalues)) := by
    rw [map_smul, ← hspec]
  -- Key: eigenvector equation M *ᵥ ψ_j = λ_j • ψ_j
  -- implies (-t•M) *ᵥ ψ_j = (-t*λ_j) • ψ_j
  -- implies exp(-t•M) *ᵥ ψ_j = exp(-t*λ_j) • ψ_j
  -- We prove this via spectral decomposition: M = U * diag(λ) * U*
  set D := diagonal (id ∘ hM.eigenvalues)
  set y := Unitary.toUnits U
  -- exp(-t • diag(λ)) = diag(exp(-t * λ))
  have hexp_diag : NormedSpace.exp ((-t) • D) =
      diagonal (fun i => NormedSpace.exp ((-t) * hM.eigenvalues i)) := by
    rw [← Matrix.diagonal_smul, Matrix.exp_diagonal]; congr 1; ext i; simp
  -- Connect star U with (y⁻¹).val
  have hinv_star : (y⁻¹ : (Matrix n n ℝ)ˣ).val = star (U : Matrix n n ℝ) := by
    simp [y, Unitary.toUnits]
  have hval_U : y.val = (U : Matrix n n ℝ) := rfl
  -- -t • M = y.val * (-t • D) * (y⁻¹).val
  have hsmul' : (-t) • M = y.val * ((-t) • D) * (y⁻¹ : (Matrix n n ℝ)ˣ).val := by
    rw [hsmul, Unitary.conjStarAlgAut_apply, hinv_star, hval_U]
  -- exp(-t•M) = y.val * exp(-t • D) * (y⁻¹).val
  have hexp : NormedSpace.exp ((-t) • M) =
      y.val * NormedSpace.exp ((-t) • D) * (y⁻¹ : (Matrix n n ℝ)ˣ).val := by
    rw [hsmul']; exact Matrix.exp_units_conj y _
  -- Apply mulVec to eigenvector ψ_j
  rw [hexp, hexp_diag, hinv_star]
  -- (↑y * diag * star ↑U) *ᵥ ψ_j  =  ↑y *ᵥ (diag *ᵥ (star ↑U *ᵥ ψ_j))
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hM.star_eigenvectorUnitary_mulVec j]
  -- Keep as mulVec_mulVec; don't apply diagonal_mulVec_single
  -- Goal before simp: ↑y *ᵥ (diag *ᵥ Pi.single j 1) = exp(-t*λ_j) • ψ_j
  -- Instead: rewrite diag as scalar * I applied to Pi.single j
  -- Simpler: use mulVec_smul after converting Pi.single j c to c • Pi.single j 1
  rw [Matrix.diagonal_mulVec_single, show (fun i => NormedSpace.exp ((-t) * hM.eigenvalues i)) j * (1 : ℝ) =
      NormedSpace.exp ((-t) * hM.eigenvalues j) from by simp]
  rw [show (Pi.single j (NormedSpace.exp ((-t) * hM.eigenvalues j)) : n → ℝ) =
      NormedSpace.exp ((-t) * hM.eigenvalues j) • (Pi.single j (1 : ℝ) : n → ℝ) from by
    funext i; simp [Pi.single_apply, smul_eq_mul]]
  rw [Matrix.mulVec_smul, hval_U, hM.eigenvectorUnitary_mulVec j]
  congr 1; exact congr_fun Real.exp_eq_exp_ℝ.symm _

/-- Inner product of eigenvector with exp(-tM)g extracts the eigenvalue factor. -/
theorem Matrix.IsHermitian.eigenCoeff_exp_neg_smul
    {M : Matrix n n ℝ} (hM : M.IsHermitian) (t : ℝ)
    (g : n → ℝ) (k : n) :
    (∑ x : n,
      (hM.eigenvectorBasis k : EuclideanSpace ℝ n) x *
        ((NormedSpace.exp ((-t) • M)) *ᵥ g) x) =
    Real.exp (-t * hM.eigenvalues k) *
      (∑ x : n, (hM.eigenvectorBasis k : EuclideanSpace ℝ n) x * g x) := by
  -- exp(-tM) is symmetric, so ψ_k^T exp(-tM) g = (exp(-tM) ψ_k)^T g
  have hHerm : (NormedSpace.exp ((-t) • M)).IsHermitian := by
    apply Matrix.IsHermitian.exp
    rw [Matrix.IsHermitian, conjTranspose_smul, star_trivial, hM.eq]
  -- Rewrite as dotProduct and use symmetry of exp(-tM) to swap
  change dotProduct (⇑(hM.eigenvectorBasis k)) ((NormedSpace.exp ((-t) • M)) *ᵥ g) = _
  rw [Matrix.dotProduct_mulVec]
  -- ψ_k ᵥ* exp(-t•M) = exp(-t•M) *ᵥ ψ_k  (using symmetry)
  rw [show (NormedSpace.exp ((-t) • M)) = (NormedSpace.exp ((-t) • M))ᵀ from by
        rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hHerm.eq.symm,
      Matrix.vecMul_transpose]
  -- dotProduct (exp(-t•M) *ᵥ ψ_k) g = exp(-t*λ_k) * dotProduct ψ_k g
  rw [Matrix.IsHermitian.mulVec_exp_neg_smul hM t k]
  simp [dotProduct, smul_eq_mul, Finset.mul_sum, mul_comm, mul_left_comm]

/-- **Spectral expansion of the matrix exponential bilinear form.**

For a Hermitian matrix M:
  `∑ x, f x * (exp(-tM) g) x = ∑ k, exp(-tμ_k) * c_k(f) * c_k(g)`
where `c_k(f) = ∑ x, ψ_k(x) * f(x)` are the eigenvector coefficients. -/
theorem Matrix.IsHermitian.bilinear_exp_eq_spectral
    {M : Matrix n n ℝ} (hM : M.IsHermitian) (t : ℝ)
    (f g : n → ℝ) :
    (∑ x : n, f x * ((NormedSpace.exp ((-t) • M)) *ᵥ g) x) =
    ∑ k : n,
      Real.exp (-t * hM.eigenvalues k) *
      (∑ x : n, (hM.eigenvectorBasis k : EuclideanSpace ℝ n) x * f x) *
      (∑ x : n, (hM.eigenvectorBasis k : EuclideanSpace ℝ n) x * g x) := by
  set h := (NormedSpace.exp ((-t) • M)) *ᵥ g
  let uf : EuclideanSpace ℝ n := (EuclideanSpace.equiv n ℝ).symm f
  let uh : EuclideanSpace ℝ n := (EuclideanSpace.equiv n ℝ).symm h
  have hparseval := OrthonormalBasis.sum_inner_mul_inner
    (hM.eigenvectorBasis) uf uh
  have hinner_fh : @inner ℝ _ _ uf uh = ∑ x : n, f x * h x := by
    simp [uf, uh, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  have hcoeff_f : ∀ k,
      @inner ℝ _ _ uf (hM.eigenvectorBasis k) =
      ∑ x, (hM.eigenvectorBasis k : EuclideanSpace ℝ n) x * f x := by
    intro k; simp [uf, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
  have hcoeff_h : ∀ k,
      @inner ℝ _ _ (hM.eigenvectorBasis k) uh =
      ∑ x, (hM.eigenvectorBasis k : EuclideanSpace ℝ n) x * h x := by
    intro k; simp [uh, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
  have heigen : ∀ k,
      ∑ x, (hM.eigenvectorBasis k : EuclideanSpace ℝ n) x * h x =
      Real.exp (-t * hM.eigenvalues k) *
        ∑ x, (hM.eigenvectorBasis k : EuclideanSpace ℝ n) x * g x :=
    fun k => Matrix.IsHermitian.eigenCoeff_exp_neg_smul hM t g k
  calc ∑ x, f x * h x
      = @inner ℝ _ _ uf uh := hinner_fh.symm
    _ = ∑ k, @inner ℝ _ _ uf (hM.eigenvectorBasis k) *
          @inner ℝ _ _ (hM.eigenvectorBasis k) uh := hparseval.symm
    _ = ∑ k, (∑ x, (hM.eigenvectorBasis k : EuclideanSpace ℝ n) x * f x) *
          (∑ x, (hM.eigenvectorBasis k : EuclideanSpace ℝ n) x * h x) := by
        refine Finset.sum_congr rfl ?_; intro k _; rw [hcoeff_f, hcoeff_h]
    _ = ∑ k, (∑ x, (hM.eigenvectorBasis k : EuclideanSpace ℝ n) x * f x) *
          (Real.exp (-t * hM.eigenvalues k) *
            ∑ x, (hM.eigenvectorBasis k : EuclideanSpace ℝ n) x * g x) := by
        refine Finset.sum_congr rfl ?_; intro k _; rw [heigen]
    _ = ∑ k, Real.exp (-t * hM.eigenvalues k) *
          (∑ x, (hM.eigenvectorBasis k : EuclideanSpace ℝ n) x * f x) *
          (∑ x, (hM.eigenvectorBasis k : EuclideanSpace ℝ n) x * g x) := by
        refine Finset.sum_congr rfl ?_; intro k _; ring

/-- **Symmetry of Hermitian matrix bilinear form.**

For a real symmetric (Hermitian) matrix M: `(M *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (M *ᵥ w)`. -/
set_option linter.unusedSectionVars false in
theorem Matrix.IsHermitian.dotProduct_mulVec_comm
    {M : Matrix n n ℝ} (hM : M.IsHermitian) (u w : n → ℝ) :
    dotProduct (M.mulVec u) w = dotProduct u (M.mulVec w) := by
  rw [Matrix.dotProduct_mulVec]
  congr 1
  have hMT : M = Mᵀ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]; exact hM.eq.symm
  symm; conv_lhs => rw [hMT]
  exact Matrix.vecMul_transpose M u

/-- **Eigenspace orthogonality for Hermitian matrices.**

If M is Hermitian with eigenvectors v (eigenvalue μ) and w (eigenvalue λ ≠ μ),
then `v ⬝ᵥ w = 0`. -/
theorem Matrix.IsHermitian.dotProduct_eigenvectors_eq_zero
    {M : Matrix n n ℝ} (hM : M.IsHermitian)
    {v w : n → ℝ} {μ ν : ℝ}
    (hv : M.mulVec v = μ • v) (hw : M.mulVec w = ν • w) (hne : μ ≠ ν) :
    dotProduct v w = 0 := by
  -- μ ⟨v, w⟩ = ⟨Mv, w⟩ = ⟨v, Mw⟩ = ν ⟨v, w⟩
  have lhs : μ * dotProduct v w = dotProduct (M.mulVec v) w := by
    rw [hv]; simp [dotProduct, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  have rhs : dotProduct (M.mulVec v) w = ν * dotProduct v w := by
    rw [Matrix.IsHermitian.dotProduct_mulVec_comm hM, hw]
    simp [dotProduct, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_; ring
  have : (μ - ν) * dotProduct v w = 0 := by linarith [lhs, rhs]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hne)

/-- **Matrix exponential maps any eigenvector of a Hermitian matrix.**

If `M v = μ • v` and M is Hermitian, then `exp(-t·M) v = exp(-t·μ) • v`.

The proof uses `bilinear_exp_eq_spectral` to compute `w ⬝ᵥ (exp(-tM) v)` for all w,
and eigenspace orthogonality to identify all Mathlib eigenvector coefficients. -/
theorem Matrix.IsHermitian.mulVec_exp_of_eigenvector
    {M : Matrix n n ℝ} (hM : M.IsHermitian) (t : ℝ)
    {v : n → ℝ} {μ : ℝ} (hv : M.mulVec v = μ • v) :
    (NormedSpace.exp ((-t) • M)).mulVec v = Real.exp (-t * μ) • v := by
  set ψ := hM.eigenvectorBasis
  -- Strategy: show ∑_x w(x) · (exp(-tM) v)(x) = ∑_x w(x) · (exp(-tμ) · v)(x)
  -- for all w, then extract each component.
  suffices h_all : ∀ w : n → ℝ,
      (∑ x, w x * ((NormedSpace.exp ((-t) • M)).mulVec v) x) =
      (∑ x, w x * (Real.exp (-t * μ) * v x)) by
    ext i
    have := h_all (Pi.single i 1)
    simp only [Pi.single_apply, boole_mul] at this
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq', if_pos (Finset.mem_univ i),
         if_pos (Finset.mem_univ i)] at this
    simp only [Pi.smul_apply, smul_eq_mul]
    exact this
  intro w
  -- LHS: use bilinear_exp_eq_spectral
  rw [Matrix.IsHermitian.bilinear_exp_eq_spectral hM t w v]
  -- Transform RHS: ∑ x, w x * (exp * v x) → exp * ∑ x, w x * v x → spectral
  simp_rw [show ∀ x, w x * (Real.exp (-t * μ) * v x) =
      Real.exp (-t * μ) * (w x * v x) from fun x => by ring]
  rw [← Finset.mul_sum]
  -- Use Parseval on ⟨w, v⟩ (obtained from bilinear_exp_eq_spectral at t = 0)
  have hparseval : (∑ x, w x * v x) =
      ∑ k, (∑ x, (ψ k : EuclideanSpace ℝ n) x * w x) *
           (∑ x, (ψ k : EuclideanSpace ℝ n) x * v x) := by
    have := Matrix.IsHermitian.bilinear_exp_eq_spectral hM 0 w v
    simp only [neg_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec,
      zero_mul, Real.exp_zero, one_mul] at this
    exact this
  rw [hparseval, Finset.mul_sum]
  -- Goal: ∑ k, exp(-tμ_k) (ψ_k·w)(ψ_k·v) = ∑ k, exp(-tμ) ((ψ_k·w)(ψ_k·v))
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : hM.eigenvalues k = μ
  · rw [hk]; ring
  · -- ψ_k·v = 0 by eigenspace orthogonality
    have h_ortho : dotProduct (⇑(ψ k)) v = 0 :=
      Matrix.IsHermitian.dotProduct_eigenvectors_eq_zero hM
        (hM.mulVec_eigenvectorBasis k) hv hk
    rw [show (∑ x, (ψ k : EuclideanSpace ℝ n) x * v x) = dotProduct (⇑(ψ k)) v from rfl,
      h_ortho, mul_zero, mul_zero, mul_zero]

end MatrixExpSpectral

end GaussianField
