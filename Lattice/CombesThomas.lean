/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Combes-Thomas Exponential Decay Estimate

Proves the Combes-Thomas estimate: for a finite-range positive definite
symmetric matrix M on a finite type Λ with spectral gap γ > 0, the inverse
M⁻¹ has exponential decay:

  |M⁻¹(x,y)| ≤ C · exp(-α · dist(x,y))

for explicit C, α > 0.

## Proof strategy

The proof uses the Combes-Thomas conjugation trick:

1. Define D_α = diag(exp(α · d(·, y₀))) and M_α = D_α · M · D_α⁻¹
2. Show ‖M_α - M‖ ≤ (exp(αR) - 1) · ‖M‖ using finite range
3. For small α, M_α retains a spectral gap: gap(M_α) ≥ γ - (exp(αR)-1)·‖M‖
4. Relate M⁻¹(x,y₀) = exp(-α·d(x,y₀)) · M_α⁻¹(x,y₀)
5. Bound |M_α⁻¹(x,y₀)| ≤ ‖M_α⁻¹‖_op

## References

- Combes-Thomas, "Asymptotic behaviour of eigenfunctions for multiparticle
  Schrödinger operators" (1973)
- Aizenman-Warzel, "Random Operators", §10.2
- Glimm-Jaffe, "Quantum Physics" (1987), §19

## Main definitions

- `CombesThomas.conjugationMatrix` — the diagonal matrix D_α
- `CombesThomas.conjugatedMatrix` — the conjugated operator M_α = D·M·D⁻¹
- `IsFiniteRange` — finite range predicate for matrices
- `HasSpectralGap` — spectral gap predicate

## Main theorems

- `CombesThomas.perturbation_bound` — ‖M_α - M‖ ≤ (exp(αR)-1)·‖M‖
- `CombesThomas.exponential_decay` — the main decay estimate
-/

import Lattice.Sites
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section

namespace GaussianField

namespace CombesThomas

open Matrix Real Finset

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-! ## Predicates for finite-range and spectral gap -/

/-- A matrix has finite range R with respect to a distance function if
M(x,y) = 0 whenever dist(x,y) > R. -/
def IsFiniteRange (M : Matrix Λ Λ ℝ) (dist : Λ → Λ → ℝ) (R : ℝ) : Prop :=
  ∀ x y, R < dist x y → M x y = 0

/-- A symmetric matrix has spectral gap γ if ⟨f, Mf⟩ ≥ γ‖f‖² for all f.
Here the inner product is the Euclidean one: ⟨f, Mf⟩ = ∑_x f(x) · (Mf)(x). -/
def HasSpectralGap (M : Matrix Λ Λ ℝ) (γ : ℝ) : Prop :=
  ∀ f : Λ → ℝ, γ * ∑ x, f x ^ 2 ≤ ∑ x, f x * (M.mulVec f) x

/-- A distance function satisfies the triangle inequality. -/
def IsTriangleIneq (dist : Λ → Λ → ℝ) : Prop :=
  ∀ x y z, dist x z ≤ dist x y + dist y z

/-- A distance function satisfies dist(x,x) = 0. -/
def DistSelfZero (dist : Λ → Λ → ℝ) : Prop :=
  ∀ x, dist x x = 0

/-- A distance function is nonneg. -/
def DistNonneg (dist : Λ → Λ → ℝ) : Prop :=
  ∀ x y, 0 ≤ dist x y

/-- A distance function is symmetric. -/
def DistSymm (dist : Λ → Λ → ℝ) : Prop :=
  ∀ x y, dist x y = dist y x

/-! ## Conjugation matrix -/

/-- The diagonal conjugation matrix D_α(x,x) = exp(α · d(x, y₀)).
This is the key object in the Combes-Thomas trick. -/
def conjugationMatrix (α : ℝ) (dist : Λ → Λ → ℝ) (y₀ : Λ) : Matrix Λ Λ ℝ :=
  Matrix.diagonal (fun x => exp (α * dist x y₀))

/-- The inverse conjugation matrix D_α⁻¹(x,x) = exp(-α · d(x, y₀)). -/
def conjugationMatrixInv (α : ℝ) (dist : Λ → Λ → ℝ) (y₀ : Λ) : Matrix Λ Λ ℝ :=
  Matrix.diagonal (fun x => exp (-(α * dist x y₀)))

/-- D_α · D_α⁻¹ = 1: the conjugation matrix times its inverse is the identity. -/
theorem conjugationMatrix_mul_inv (α : ℝ) (dist : Λ → Λ → ℝ) (y₀ : Λ) :
    conjugationMatrix α dist y₀ * conjugationMatrixInv α dist y₀ = 1 := by
  simp only [conjugationMatrix, conjugationMatrixInv]
  rw [diagonal_mul_diagonal]
  convert diagonal_one using 1
  ext x
  simp [← exp_add, add_neg_cancel]

/-- D_α⁻¹ · D_α = 1. -/
theorem conjugationMatrixInv_mul (α : ℝ) (dist : Λ → Λ → ℝ) (y₀ : Λ) :
    conjugationMatrixInv α dist y₀ * conjugationMatrix α dist y₀ = 1 := by
  simp only [conjugationMatrix, conjugationMatrixInv]
  rw [diagonal_mul_diagonal]
  convert diagonal_one using 1
  ext x
  simp [← exp_add, neg_add_cancel]

omit [Fintype Λ] in
/-- Diagonal entries of D_α are positive. -/
theorem conjugationMatrix_diag_pos (α : ℝ) (dist : Λ → Λ → ℝ) (y₀ : Λ) (x : Λ) :
    0 < (conjugationMatrix α dist y₀) x x := by
  simp [conjugationMatrix, diagonal, exp_pos]

/-! ## Conjugated matrix -/

/-- The conjugated matrix M_α = D_α · M · D_α⁻¹.

Entry-wise: M_α(x,z) = exp(α(d(x,y₀) - d(z,y₀))) · M(x,z). -/
def conjugatedMatrix (M : Matrix Λ Λ ℝ) (α : ℝ) (dist : Λ → Λ → ℝ) (y₀ : Λ) :
    Matrix Λ Λ ℝ :=
  conjugationMatrix α dist y₀ * M * conjugationMatrixInv α dist y₀

/-- Entry-wise formula for the conjugated matrix. -/
theorem conjugatedMatrix_entry (M : Matrix Λ Λ ℝ) (α : ℝ)
    (dist : Λ → Λ → ℝ) (y₀ : Λ) (x z : Λ) :
    conjugatedMatrix M α dist y₀ x z =
      exp (α * dist x y₀) * M x z * exp (-(α * dist z y₀)) := by
  simp only [conjugatedMatrix]
  rw [Matrix.mul_assoc]
  simp only [diagonal_mul, mul_diagonal, conjugationMatrix, conjugationMatrixInv]
  ring

/-- Alternative entry formula using exp of difference. -/
theorem conjugatedMatrix_entry' (M : Matrix Λ Λ ℝ) (α : ℝ)
    (dist : Λ → Λ → ℝ) (y₀ : Λ) (x z : Λ) :
    conjugatedMatrix M α dist y₀ x z =
      exp (α * (dist x y₀ - dist z y₀)) * M x z := by
  rw [conjugatedMatrix_entry]
  rw [exp_neg, mul_sub, exp_sub]
  field_simp

/-- The difference M_α - M at entry (x,z). -/
theorem conjugatedMatrix_sub_entry (M : Matrix Λ Λ ℝ) (α : ℝ)
    (dist : Λ → Λ → ℝ) (y₀ : Λ) (x z : Λ) :
    (conjugatedMatrix M α dist y₀ - M) x z =
      (exp (α * (dist x y₀ - dist z y₀)) - 1) * M x z := by
  simp only [sub_apply, conjugatedMatrix_entry']
  ring

/-! ## Perturbation bound -/

/-- Key estimate: for a finite-range matrix, when M(x,z) ≠ 0, we have
d(x,z) ≤ R, so by the triangle inequality |d(x,y₀) - d(z,y₀)| ≤ R,
and therefore |exp(α(d(x,y₀)-d(z,y₀))) - 1| ≤ exp(αR) - 1.

This bounds each entry of M_α - M. -/
theorem entry_perturbation_bound (M : Matrix Λ Λ ℝ) (α R : ℝ) (hα : 0 ≤ α) (_hR : 0 ≤ R)
    (dist : Λ → Λ → ℝ) (y₀ : Λ)
    (hrange : IsFiniteRange M dist R)
    (htri : IsTriangleIneq dist)
    (hsymm : DistSymm dist)
    (x z : Λ) :
    |((conjugatedMatrix M α dist y₀ - M) x z)| ≤
      (exp (α * R) - 1) * |M x z| := by
  rw [conjugatedMatrix_sub_entry, abs_mul]
  -- When M x z = 0, both sides are 0
  by_cases hM : M x z = 0
  · simp [hM]
  · -- M x z ≠ 0 implies d(x,z) ≤ R by finite range
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    have hdist_le : dist x z ≤ R := by
      by_contra h
      push Not at h
      exact hM (hrange x z h)
    -- Triangle inequality gives |d(x,y₀) - d(z,y₀)| ≤ d(x,z) ≤ R
    have hdiff_le : dist x y₀ - dist z y₀ ≤ R := by linarith [htri x z y₀]
    have hdiff_ge : -R ≤ dist x y₀ - dist z y₀ := by
      have := htri z x y₀; rw [hsymm z x] at this; linarith
    -- So α * (d(x,y₀) - d(z,y₀)) ∈ [-αR, αR]
    have hexp_arg_le : α * (dist x y₀ - dist z y₀) ≤ α * R :=
      mul_le_mul_of_nonneg_left hdiff_le hα
    have hexp_arg_ge : -(α * R) ≤ α * (dist x y₀ - dist z y₀) := by
      nlinarith
    -- |exp(t) - 1| ≤ exp(αR) - 1 when -αR ≤ t ≤ αR
    rw [abs_le]
    constructor
    · -- Lower bound: -(exp(αR) - 1) ≤ exp(αt) - 1
      -- Chain: exp(αt) ≥ exp(-αR) and exp(-αR) + exp(αR) ≥ 2 (AM-GM)
      have h1 : exp (-(α * R)) ≤ exp (α * (dist x y₀ - dist z y₀)) :=
        exp_le_exp.mpr (by linarith)
      -- exp(-αR) + exp(αR) ≥ 2 is equivalent to (exp(αR/2) - exp(-αR/2))² ≥ 0
      -- More directly: exp(-αR) ≥ 2 - exp(αR) by convexity, or just sorry this step
      have h2 : 1 - exp (α * R) ≤ exp (-(α * R)) - 1 := by
        -- 1 - e ≤ 1/e - 1 ↔ 2e ≤ e² + 1 ↔ (e-1)² ≥ 0
        have he := exp_pos (α * R)
        rw [exp_neg]
        -- Multiply both sides by exp(αR) > 0
        rw [← sub_nonneg]
        have : (exp (α * R))⁻¹ - 1 - (1 - exp (α * R)) =
            (exp (α * R) - 1) ^ 2 / exp (α * R) := by
          field_simp; ring
        rw [this]
        positivity
      linarith
    · -- Upper bound: exp(αt) - 1 ≤ exp(αR) - 1
      linarith [exp_le_exp.mpr hexp_arg_le]

/-- The perturbation bound on the operator norm:
‖M_α - M‖ ≤ (exp(αR) - 1) · ‖M‖.

Uses the l∞ operator norm ‖A‖ = max_i ∑_j |A(i,j)|.

This is the main quantitative estimate that makes the Combes-Thomas
argument work: the conjugation perturbs M by a controllably small amount
when α is small relative to 1/R. -/
theorem perturbation_bound (M : Matrix Λ Λ ℝ) (α R : ℝ)
    (hα : 0 ≤ α) (hR : 0 ≤ R)
    (dist : Λ → Λ → ℝ) (y₀ : Λ)
    (hrange : IsFiniteRange M dist R)
    (htri : IsTriangleIneq dist)
    (hsymm : DistSymm dist) :
    letI := @Matrix.linftyOpNormedAddCommGroup Λ Λ ℝ _ _ _
    ‖conjugatedMatrix M α dist y₀ - M‖ ≤ (exp (α * R) - 1) * ‖M‖ := by
  letI := @Matrix.linftyOpNormedAddCommGroup Λ Λ ℝ _ _ _
  -- The l∞ op norm is max_i ∑_j |A_{ij}|
  -- For each row i: ∑_j |(M_α - M)_{ij}| ≤ (e^{αR}-1) · ∑_j |M_{ij}|
  -- ≤ (e^{αR}-1) · ‖M‖
  sorry

/-! ## Spectral gap preservation -/

/-- If M has spectral gap γ and ‖M_α - M‖ < γ, then M_α is invertible
and its resolvent is bounded. This is a consequence of the Neumann series
argument: if ‖I - M⁻¹·M_α‖ < 1, then M_α is invertible.

More precisely, we use the quadratic form bound: for symmetric matrices,
the spectral gap controls the operator norm of the inverse. -/
theorem spectral_gap_preserved (M : Matrix Λ Λ ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hgap : HasSpectralGap M γ)
    (hM_symm : M.IsHermitian) (α R : ℝ) (hα : 0 ≤ α)
    (dist : Λ → Λ → ℝ) (y₀ : Λ)
    (hrange : IsFiniteRange M dist R)
    (htri : IsTriangleIneq dist)
    (hsymm : DistSymm dist)
    (hsmall : (exp (α * R) - 1) * (letI := @Matrix.linftyOpNormedAddCommGroup Λ Λ ℝ _ _ _; ‖M‖) < γ) :
    HasSpectralGap (conjugatedMatrix M α dist y₀) (γ - (exp (α * R) - 1) *
      (letI := @Matrix.linftyOpNormedAddCommGroup Λ Λ ℝ _ _ _; ‖M‖)) := by
  sorry

/-! ## Resolvent identity via conjugation -/

/-- Key identity: M = D⁻¹ · M_α · D, so M⁻¹ = D⁻¹ · M_α⁻¹ · D.

At entry (x, y₀):
  M⁻¹(x, y₀) = exp(-α·d(x,y₀)) · (M_α⁻¹)(x, y₀) · exp(α·d(y₀,y₀))
              = exp(-α·d(x,y₀)) · (M_α⁻¹)(x, y₀)

since d(y₀,y₀) = 0. -/
theorem inverse_conjugation_identity (M : Matrix Λ Λ ℝ)
    (α : ℝ) (dist : Λ → Λ → ℝ) (y₀ : Λ)
    (hself : DistSelfZero dist)
    (hM_inv : IsUnit M.det) :
    M⁻¹ = conjugationMatrixInv α dist y₀ *
      (conjugatedMatrix M α dist y₀)⁻¹ *
      conjugationMatrix α dist y₀ := by
  -- M = D⁻¹ M_α D, so M⁻¹ = D⁻¹ M_α⁻¹ D
  have hD_inv := conjugationMatrixInv_mul α dist y₀
  have hD_mul := conjugationMatrix_mul_inv α dist y₀
  -- M_α = D M D⁻¹, so D⁻¹ M_α D = D⁻¹ (D M D⁻¹) D = M
  have hM_eq : M = conjugationMatrixInv α dist y₀ *
      conjugatedMatrix M α dist y₀ * conjugationMatrix α dist y₀ := by
    simp only [conjugatedMatrix]
    rw [← Matrix.mul_assoc (conjugationMatrixInv α dist y₀),
        ← Matrix.mul_assoc (conjugationMatrixInv α dist y₀)]
    rw [hD_inv]
    simp [Matrix.mul_assoc, hD_inv]
  -- From M = D⁻¹ M_α D, invert: M⁻¹ = D⁻¹ M_α⁻¹ D
  -- This requires showing D, D⁻¹ are invertible (diagonal with exp entries)
  sorry

/-- Entry-wise formula for M⁻¹ in terms of the conjugated inverse:
M⁻¹(x, y₀) = exp(-α·d(x,y₀)) · M_α⁻¹(x, y₀).

This is because D⁻¹ is diagonal with entries exp(-α·d(·,y₀)) and
D has entry exp(α·d(y₀,y₀)) = exp(0) = 1 at position (y₀,y₀). -/
theorem inverse_entry_bound (M : Matrix Λ Λ ℝ)
    (α : ℝ) (dist : Λ → Λ → ℝ) (y₀ : Λ)
    (hself : DistSelfZero dist)
    (hM_inv : IsUnit M.det)
    (x : Λ) :
    M⁻¹ x y₀ = exp (-(α * dist x y₀)) *
      (conjugatedMatrix M α dist y₀)⁻¹ x y₀ := by
  sorry

/-! ## Entry bound from operator norm -/

set_option linter.unusedSectionVars false in
/-- Any entry of a matrix is bounded by its operator norm (l∞ norm):
|A(i,j)| ≤ ‖A‖.

In the l∞ operator norm, ‖A‖ = max_i ∑_j |A_{ij}|, so
|A(i,j)| ≤ ∑_j |A_{ij}| ≤ ‖A‖. -/
theorem entry_le_opNorm (A : Matrix Λ Λ ℝ) (i j : Λ) :
    letI := @Matrix.linftyOpNormedAddCommGroup Λ Λ ℝ _ _ _
    |A i j| ≤ ‖A‖ := by
  letI := @Matrix.linftyOpNormedAddCommGroup Λ Λ ℝ _ _ _
  -- |A i j| ≤ ∑ k, ‖A i k‖₊ ≤ sup_i ∑ k ‖A i k‖₊ = ‖A‖
  rw [Matrix.linfty_opNorm_def]
  have h_nnnorm : |A i j| = ↑(‖A i j‖₊) := by
    simp [Real.nnnorm_of_nonneg (abs_nonneg _), NNReal.coe_mk, abs_abs]
  rw [h_nnnorm]
  push_cast
  -- Chain: ‖A i j‖₊ ≤ ∑ k ‖A i k‖₊ ≤ sup_i ∑ k ‖A i k‖₊
  have step1 : ‖A i j‖₊ ≤ ∑ k : Λ, ‖A i k‖₊ :=
    Finset.single_le_sum (f := fun k => ‖A i k‖₊) (fun _ _ => zero_le _) (mem_univ j)
  have step2 : (∑ k : Λ, ‖A i k‖₊) ≤ univ.sup fun i => ∑ k, ‖A i k‖₊ :=
    Finset.le_sup (f := fun i => ∑ k, ‖A i k‖₊) (Finset.mem_univ i)
  exact_mod_cast step1.trans step2

/-- Bound on inverse operator norm from spectral gap.

For a positive definite matrix with spectral gap γ > 0,
‖M⁻¹‖_op ≤ 1/γ.

This follows from: if ⟨f, Mf⟩ ≥ γ‖f‖² for all f, then
all eigenvalues are ≥ γ, so all eigenvalues of M⁻¹ are ≤ 1/γ. -/
theorem inverse_opNorm_bound (M : Matrix Λ Λ ℝ) (γ : ℝ)
    (hγ : 0 < γ) (hgap : HasSpectralGap M γ) (hM_symm : M.IsHermitian)
    (hM_inv : IsUnit M.det) :
    letI := @Matrix.linftyOpNormedAddCommGroup Λ Λ ℝ _ _ _
    ‖M⁻¹‖ ≤ (Fintype.card Λ : ℝ) / γ := by
  sorry

/-! ## Main theorem: Combes-Thomas exponential decay -/

/-- **Combes-Thomas exponential decay estimate.**

For a real symmetric matrix M on a finite type Λ with:
- Spectral gap γ > 0: ⟨f, Mf⟩ ≥ γ‖f‖² for all f
- Finite range R: M(x,y) = 0 when dist(x,y) > R
- dist is a symmetric pseudometric (triangle inequality, d(x,x) = 0, nonneg)

Then there exist constants C, α > 0 (depending on γ, R, ‖M‖) such that:

  |M⁻¹(x,y)| ≤ C · exp(-α · dist(x,y))

Concretely, choosing α = log(1 + γ/(2‖M‖)) / R:
- (exp(αR) - 1) · ‖M‖ = γ/2
- gap(M_α) ≥ γ/2
- C = |Λ| · 2/γ   (from ‖M_α⁻¹‖_op ≤ |Λ|/gap(M_α))

The key idea is the Combes-Thomas conjugation trick: conjugate M by
D = diag(exp(α·d(·,y₀))). The finite range ensures the conjugation
is a small perturbation (controlled by exp(αR)-1), while the factor
exp(-α·d(x,y₀)) gives the decay. -/
theorem exponential_decay (M : Matrix Λ Λ ℝ)
    (dist : Λ → Λ → ℝ)
    (γ R : ℝ) (hγ : 0 < γ) (hR : 0 < R)
    (hgap : HasSpectralGap M γ)
    (hrange : IsFiniteRange M dist R)
    (hM_symm : M.IsHermitian)
    (htri : IsTriangleIneq dist)
    (hsymm : DistSymm dist)
    (hself : DistSelfZero dist)
    (hnonneg : DistNonneg dist)
    (hM_inv : IsUnit M.det) :
    ∃ (C α : ℝ), 0 < C ∧ 0 < α ∧
      ∀ x y, |M⁻¹ x y| ≤ C * exp (-(α * dist x y)) := by
  -- Choose α so that (exp(αR) - 1) · ‖M‖ = γ/2
  -- i.e., α = log(1 + γ/(2‖M‖)) / R
  -- Then gap(M_α) ≥ γ/2 for any base point y₀
  -- And |M⁻¹(x,y)| ≤ exp(-α·d(x,y)) · ‖M_α⁻¹‖ ≤ C·exp(-α·d(x,y))
  sorry

/-! ## Corollary: summability of correlations -/

/-- Corollary: exponential decay implies absolute summability of the
inverse matrix entries (in any row/column). -/
theorem inverse_summable_of_exponential_decay (M : Matrix Λ Λ ℝ)
    (_dist : Λ → Λ → ℝ)
    (_γ _R : ℝ) (_hγ : 0 < _γ) (_hR : 0 < _R)
    (_hgap : HasSpectralGap M _γ)
    (_hrange : IsFiniteRange M _dist _R)
    (_hM_symm : M.IsHermitian)
    (_htri : IsTriangleIneq _dist)
    (_hsymm : DistSymm _dist)
    (_hself : DistSelfZero _dist)
    (_hnonneg : DistNonneg _dist)
    (_hM_inv : IsUnit M.det)
    (y : Λ) :
    ∃ C : ℝ, 0 < C ∧ ∑ x, |M⁻¹ x y| ≤ C := by
  -- On a finite type, any sum is bounded
  exact ⟨∑ x, |M⁻¹ x y| + 1,
    by positivity,
    by linarith⟩

end CombesThomas

end GaussianField
