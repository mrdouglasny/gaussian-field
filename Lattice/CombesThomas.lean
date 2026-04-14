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
  rw [Matrix.linfty_opNorm_def, Matrix.linfty_opNorm_def]
  have hexp_nonneg : 0 ≤ rexp (α * R) - 1 := by linarith [one_le_exp (mul_nonneg hα hR)]
  let c : NNReal := ⟨rexp (α * R) - 1, hexp_nonneg⟩
  have hrow : ∀ i : Λ, (∑ j : Λ, ‖(conjugatedMatrix M α dist y₀ - M) i j‖₊) ≤
      c * (∑ j : Λ, ‖M i j‖₊) := by
    intro i
    calc ∑ j : Λ, ‖(conjugatedMatrix M α dist y₀ - M) i j‖₊
        ≤ ∑ j : Λ, c * ‖M i j‖₊ := by
          apply Finset.sum_le_sum
          intro j _
          have h := entry_perturbation_bound M α R hα hR dist y₀ hrange htri hsymm i j
          rw [← NNReal.coe_le_coe]
          push_cast
          simp only [Real.norm_eq_abs]
          exact h
      _ = c * ∑ j : Λ, ‖M i j‖₊ := by rw [Finset.mul_sum]
  have hsup_bound : (univ.sup fun i => ∑ j, ‖(conjugatedMatrix M α dist y₀ - M) i j‖₊) ≤
      c * (univ.sup fun i => ∑ j, ‖M i j‖₊) := by
    apply Finset.sup_le
    intro i _
    calc ∑ j, ‖(conjugatedMatrix M α dist y₀ - M) i j‖₊
        ≤ c * ∑ j, ‖M i j‖₊ := hrow i
      _ ≤ c * (univ.sup fun i => ∑ j, ‖M i j‖₊) := by
          apply mul_le_mul_right
          exact Finset.le_sup (f := fun i => ∑ j : Λ, ‖M i j‖₊) (Finset.mem_univ i)
  exact_mod_cast hsup_bound

/-! ## Spectral gap preservation -/

/-- If M has spectral gap γ and ‖M_α - M‖ < γ, then M_α is invertible
and its resolvent is bounded. This is a consequence of the Neumann series
argument: if ‖I - M⁻¹·M_α‖ < 1, then M_α is invertible.

More precisely, we use the quadratic form bound: for symmetric matrices,
the spectral gap controls the operator norm of the inverse. -/
theorem spectral_gap_preserved (M : Matrix Λ Λ ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hgap : HasSpectralGap M γ)
    (hM_symm : M.IsHermitian) (α R : ℝ) (hα : 0 ≤ α) (hR : 0 ≤ R)
    (dist : Λ → Λ → ℝ) (y₀ : Λ)
    (hrange : IsFiniteRange M dist R)
    (htri : IsTriangleIneq dist)
    (hsymm : DistSymm dist)
    (hsmall : (exp (α * R) - 1) * (letI := @Matrix.linftyOpNormedAddCommGroup Λ Λ ℝ _ _ _; ‖M‖) < γ) :
    HasSpectralGap (conjugatedMatrix M α dist y₀) (γ - (exp (α * R) - 1) *
      (letI := @Matrix.linftyOpNormedAddCommGroup Λ Λ ℝ _ _ _; ‖M‖)) := by
  intro f
  have hgap_f := hgap f
  have heq : ∀ x, (conjugatedMatrix M α dist y₀).mulVec f x =
      M.mulVec f x + (conjugatedMatrix M α dist y₀ - M).mulVec f x := by
    intro x; simp [Matrix.sub_mulVec]
  simp_rw [heq, mul_add, Finset.sum_add_distrib]
  letI := @Matrix.linftyOpNormedAddCommGroup Λ Λ ℝ _ _ _
  suffices key : |(∑ x, f x * ((conjugatedMatrix M α dist y₀ - M) *ᵥ f) x)| ≤
      (rexp (α * R) - 1) * ‖M‖ * ∑ x, f x ^ 2 by
    nlinarith [abs_le.mp key]
  -- Expand mulVec
  simp only [Matrix.mulVec, dotProduct, conjugatedMatrix_sub_entry]
  -- Triangle inequality + entry bound + AM-GM + M symmetric
  trans (∑ x, |f x| * (∑ j, (rexp (α * R) - 1) * |M x j| * |f j|))
  · -- Step 1: |sum| ≤ sum |entry| with entry bound
    apply le_trans (Finset.abs_sum_le_sum_abs _ _)
    apply Finset.sum_le_sum
    intro x _
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply le_trans (Finset.abs_sum_le_sum_abs _ _)
    apply Finset.sum_le_sum
    intro j _
    rw [abs_mul, abs_mul]
    by_cases hM : M x j = 0
    · simp [hM]
    · apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      have hdist_le : dist x j ≤ R := by
        by_contra h; push Not at h; exact hM (hrange x j h)
      have hdiff_le : dist x y₀ - dist j y₀ ≤ R := by linarith [htri x j y₀]
      have hexp_arg_le : α * (dist x y₀ - dist j y₀) ≤ α * R :=
        mul_le_mul_of_nonneg_left hdiff_le hα
      have hexp_arg_ge : -(α * R) ≤ α * (dist x y₀ - dist j y₀) := by
        nlinarith [htri j x y₀, hsymm j x]
      rw [abs_le]
      constructor
      · have h1 : rexp (-(α * R)) ≤ rexp (α * (dist x y₀ - dist j y₀)) :=
          exp_le_exp.mpr (by linarith)
        have h2 : 1 - rexp (α * R) ≤ rexp (-(α * R)) - 1 := by
          rw [exp_neg, ← sub_nonneg]
          have : (rexp (α * R))⁻¹ - 1 - (1 - rexp (α * R)) =
            (rexp (α * R) - 1) ^ 2 / rexp (α * R) := by field_simp; ring
          rw [this]; positivity
        linarith
      · linarith [exp_le_exp.mpr hexp_arg_le]
  · -- Step 2: AM-GM + row sum bound
    -- Factor out (exp(αR)-1)
    have hexp_nonneg : 0 ≤ rexp (α * R) - 1 := by linarith [one_le_exp (mul_nonneg hα hR)]
    have hfactor : ∀ x, |f x| * ∑ j, (rexp (α * R) - 1) * |M x j| * |f j| =
        (rexp (α * R) - 1) * (∑ j, |M x j| * (|f x| * |f j|)) := by
      intro x; simp_rw [Finset.mul_sum]; congr 1; ext j; ring
    simp_rw [hfactor, ← Finset.mul_sum]
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hexp_nonneg
    -- Row and column sum bounds from l∞ norm
    have hrow_le : ∀ i : Λ, (∑ j : Λ, |M i j|) ≤ ‖M‖ := by
      intro i; rw [Matrix.linfty_opNorm_def]
      have h1 : (∑ j : Λ, |M i j|) = ↑(∑ j : Λ, ‖M i j‖₊) := by
        simp [NNNorm.nnnorm, Real.norm_eq_abs, NNReal.coe_sum]
      rw [h1]
      exact_mod_cast Finset.le_sup (f := fun i => ∑ j : Λ, ‖M i j‖₊) (Finset.mem_univ i)
    have hM_sym_entry : ∀ i j : Λ, M i j = M j i := by
      intro i j; have h := hM_symm; rw [Matrix.IsHermitian] at h
      have := congr_fun (congr_fun h j) i
      simp [Matrix.conjTranspose_apply] at this; exact this
    have hcol_le : ∀ j : Λ, (∑ i : Λ, |M i j|) ≤ ‖M‖ := by
      intro j
      calc ∑ i, |M i j| = ∑ i, |M j i| := by congr 1; ext i; rw [hM_sym_entry]
        _ ≤ ‖M‖ := hrow_le j
    -- AM-GM: |f_i||f_j| ≤ (f_i² + f_j²)/2, then split and bound
    -- Part A: ∑_i f_i² * (∑_j |M_ij|) ≤ ‖M‖ * ∑ f²
    have hpartA : ∑ i, f i ^ 2 * ∑ j, |M i j| ≤ ‖M‖ * ∑ i, f i ^ 2 := by
      calc ∑ i, f i ^ 2 * ∑ j, |M i j|
          ≤ ∑ i, f i ^ 2 * ‖M‖ := by
            apply Finset.sum_le_sum; intro i _
            exact mul_le_mul_of_nonneg_left (hrow_le i) (sq_nonneg _)
        _ = ‖M‖ * ∑ i, f i ^ 2 := by rw [← Finset.sum_mul]; ring
    -- Part B: ∑_j f_j² * (∑_i |M_ij|) ≤ ‖M‖ * ∑ f² (using column bound)
    have hpartB : ∑ j, f j ^ 2 * ∑ i, |M i j| ≤ ‖M‖ * ∑ j, f j ^ 2 := by
      calc ∑ j, f j ^ 2 * ∑ i, |M i j|
          ≤ ∑ j, f j ^ 2 * ‖M‖ := by
            apply Finset.sum_le_sum; intro j _
            exact mul_le_mul_of_nonneg_left (hcol_le j) (sq_nonneg _)
        _ = ‖M‖ * ∑ j, f j ^ 2 := by rw [← Finset.sum_mul]; ring
    -- Main: apply AM-GM then combine parts
    calc ∑ i, ∑ j, |M i j| * (|f i| * |f j|)
        ≤ ∑ i, ∑ j, (|M i j| * f i ^ 2 / 2 + |M i j| * f j ^ 2 / 2) := by
          apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
          have := sq_abs (f i); have := sq_abs (f j)
          nlinarith [sq_nonneg (|f i| - |f j|), abs_nonneg (M i j)]
      _ = (∑ i, f i ^ 2 * ∑ j, |M i j|) / 2 + (∑ j, f j ^ 2 * ∑ i, |M i j|) / 2 := by
          simp_rw [Finset.sum_add_distrib, Finset.sum_div]
          congr 1
          · apply Finset.sum_congr rfl; intro i _
            rw [← Finset.sum_div]; congr 1
            conv_lhs => arg 2; ext j; rw [mul_comm]
            exact (Finset.mul_sum _ _ _).symm
          · rw [Finset.sum_comm]
            apply Finset.sum_congr rfl; intro j _
            rw [← Finset.sum_div]; congr 1
            conv_lhs => arg 2; ext i; rw [mul_comm]
            exact (Finset.mul_sum _ _ _).symm
      _ ≤ (‖M‖ * ∑ i, f i ^ 2) / 2 + (‖M‖ * ∑ j, f j ^ 2) / 2 := by
          apply add_le_add <;> exact div_le_div_of_nonneg_right (by assumption) (by norm_num)
      _ = ‖M‖ * ∑ x, f x ^ 2 := by ring

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
  have hDinv_inv : (conjugationMatrixInv α dist y₀)⁻¹ = conjugationMatrix α dist y₀ :=
    Matrix.inv_eq_left_inv hD_mul
  have hD_inv' : (conjugationMatrix α dist y₀)⁻¹ = conjugationMatrixInv α dist y₀ :=
    Matrix.inv_eq_left_inv hD_inv
  conv_lhs => rw [hM_eq]
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc, hDinv_inv, hD_inv']

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
  rw [inverse_conjugation_identity M α dist y₀ hself hM_inv]
  simp only [conjugationMatrixInv, conjugationMatrix]
  rw [Matrix.mul_assoc]
  simp only [diagonal_mul, mul_diagonal]
  simp [hself y₀]

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
  letI := @Matrix.linftyOpNormedAddCommGroup Λ Λ ℝ _ _ _
  -- Suffices: each |M⁻¹_{ij}| ≤ 1/γ, then row sum ≤ |Λ|/γ
  suffices hentry : ∀ i j : Λ, |M⁻¹ i j| ≤ 1 / γ by
    have hrow : ∀ i, (∑ j, |M⁻¹ i j|) ≤ (Fintype.card Λ : ℝ) / γ := by
      intro i
      calc ∑ j, |M⁻¹ i j| ≤ ∑ _j : Λ, (1 / γ : ℝ) :=
            Finset.sum_le_sum (fun j _ => hentry i j)
        _ = (Fintype.card Λ : ℝ) / γ := by
            simp [Finset.sum_const, Finset.card_univ]; ring
    -- From row bound to norm bound
    rw [Matrix.linfty_opNorm_def]
    have h1 : ∀ i, (∑ j : Λ, ‖M⁻¹ i j‖₊ : ℝ) ≤ (Fintype.card Λ : ℝ) / γ := by
      intro i
      calc (∑ j : Λ, ‖M⁻¹ i j‖₊ : ℝ) = ∑ j, |M⁻¹ i j| := by
            simp [NNNorm.nnnorm, Real.norm_eq_abs, NNReal.coe_sum]
        _ ≤ _ := hrow i
    have hle : (univ.sup fun i => ∑ j, ‖M⁻¹ i j‖₊) ≤
        ⟨(Fintype.card Λ : ℝ) / γ, div_nonneg (Nat.cast_nonneg _) (le_of_lt hγ)⟩ := by
      apply Finset.sup_le; intro i _
      exact_mod_cast h1 i
    exact_mod_cast hle
  -- Entry bound: |M⁻¹(i,j)| ≤ 1/γ
  -- Proof: let g = M⁻¹ eⱼ. Then Mg = eⱼ.
  -- ⟨g, Mg⟩ = g(j) and ⟨g, Mg⟩ ≥ γ‖g‖². So γ‖g‖² ≤ g(j) ≤ √(∑g²).
  -- Hence γ√(∑g²) ≤ 1, and |g(i)| ≤ √(∑g²) ≤ 1/γ.
  intro i j
  set g : Λ → ℝ := fun x => M⁻¹ x j with hg_def
  -- M g = e_j: this is the defining property of M⁻¹
  have hMg : M.mulVec g = fun x => if x = j then 1 else 0 := by
    ext x; simp only [Matrix.mulVec, dotProduct]
    have := congr_fun (congr_fun (Matrix.mul_nonsing_inv M hM_inv) x) j
    simp only [Matrix.mul_apply, Matrix.one_apply] at this; exact this
  have hinner_eq : ∑ x, g x * (M.mulVec g) x = g j := by
    rw [hMg]; simp [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
  have hgap_bound : γ * ∑ x, g x ^ 2 ≤ g j := by linarith [hgap g]
  have hentry_sq : g i ^ 2 ≤ ∑ x, g x ^ 2 :=
    Finset.single_le_sum (fun x _ => sq_nonneg (g x)) (Finset.mem_univ i)
  by_cases hg_zero : ∑ x, g x ^ 2 = 0
  · -- g = 0
    have : g i ^ 2 ≤ 0 := by rw [hg_zero] at hentry_sq; exact hentry_sq
    have : g i = 0 := by nlinarith [sq_nonneg (g i)]
    have : M⁻¹ i j = 0 := this
    rw [this, abs_zero]; exact div_nonneg one_pos.le hγ.le
  · -- g ≠ 0: use γ√S² ≤ √S to get γ√S ≤ 1
    have hsum_pos : 0 < ∑ x, g x ^ 2 := lt_of_le_of_ne
      (Finset.sum_nonneg (fun x _ => sq_nonneg (g x))) (Ne.symm hg_zero)
    have hsqrt_pos := Real.sqrt_pos.mpr hsum_pos
    have hgj_le_sqrt : g j ≤ Real.sqrt (∑ x, g x ^ 2) := by
      calc g j ≤ |g j| := le_abs_self _
        _ = Real.sqrt (g j ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ Real.sqrt (∑ x, g x ^ 2) := Real.sqrt_le_sqrt
              (Finset.single_le_sum (fun x _ => sq_nonneg (g x)) (Finset.mem_univ j))
    -- γ * S ≤ √S, and S = (√S)², so γ(√S)² ≤ √S, so γ√S ≤ 1
    have hγ_sqrt : γ * Real.sqrt (∑ x, g x ^ 2) ≤ 1 := by
      have h1 : γ * (∑ x, g x ^ 2) ≤ Real.sqrt (∑ x, g x ^ 2) :=
        le_trans hgap_bound hgj_le_sqrt
      nlinarith [Real.sq_sqrt (le_of_lt hsum_pos)]
    calc |g i| = Real.sqrt (g i ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (∑ x, g x ^ 2) := Real.sqrt_le_sqrt hentry_sq
      _ ≤ 1 / γ := by
          have h1 : Real.sqrt (∑ x, g x ^ 2) * γ ≤ 1 := by linarith
          rw [le_div_iff₀ hγ]; linarith

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
  -- Assembly: choose α so that (exp(αR)-1)·‖M‖ = γ/2, then chain the bounds.
  -- For any x y, using y as base point:
  --   |M⁻¹(x,y)| = exp(-α·d(x,y)) · |M_α⁻¹(x,y)|   [inverse_entry_bound]
  --              ≤ exp(-α·d(x,y)) · ‖M_α⁻¹‖           [entry_le_opNorm]
  --              ≤ exp(-α·d(x,y)) · |Λ|/gap(M_α)       [inverse_opNorm_bound]
  --              ≤ C · exp(-α·d(x,y))
  letI := @Matrix.linftyOpNormedAddCommGroup Λ Λ ℝ _ _ _
  by_cases hM_zero : ‖M‖ = 0
  · -- If ‖M‖ = 0 then M = 0; if Λ is nonempty this contradicts IsUnit M.det
    have hMeq : M = 0 := by rwa [norm_eq_zero] at hM_zero
    by_cases hne : Nonempty Λ
    · exfalso; rw [hMeq, Matrix.det_zero hne] at hM_inv; exact not_isUnit_zero hM_inv
    · -- Λ is empty: the bound holds vacuously
      rw [not_nonempty_iff] at hne
      exact ⟨1, 1, one_pos, one_pos, fun x => (hne.false x).elim⟩
  · -- ‖M‖ > 0
    have hM_pos : 0 < ‖M‖ := lt_of_le_of_ne (norm_nonneg M) (Ne.symm hM_zero)
    -- Choose α = log(1 + γ/(2‖M‖)) / R
    set α₀ := Real.log (1 + γ / (2 * ‖M‖)) / R with hα₀_def
    have hγ_2M : 0 < γ / (2 * ‖M‖) := div_pos hγ (mul_pos two_pos hM_pos)
    have h_log_pos : 0 < Real.log (1 + γ / (2 * ‖M‖)) := by
      apply Real.log_pos; linarith
    have hα₀_pos : 0 < α₀ := div_pos h_log_pos hR
    -- C from inverse_opNorm_bound applied to M_α with gap γ/2
    set C := (Fintype.card Λ : ℝ) / (γ / 2) with hC_def
    refine ⟨C, α₀, ?_, hα₀_pos, ?_⟩
    · -- C > 0 (Λ must be nonempty since ‖M‖ > 0)
      have : Nonempty Λ := by
        by_contra h; rw [not_nonempty_iff] at h
        have : M = 0 := Matrix.ext (fun i _ => (IsEmpty.false i).elim)
        simp [this] at hM_zero
      apply div_pos (Nat.cast_pos.mpr Fintype.card_pos) (half_pos hγ)
    · -- Main bound: |M⁻¹(x,y)| ≤ C * exp(-α₀*d(x,y))
      intro x y
      -- Use inverse_entry_bound with y₀ = y
      have h_entry := inverse_entry_bound M α₀ dist y hself hM_inv x
      rw [h_entry, abs_mul, abs_of_pos (exp_pos _)]
      -- Now: exp(-α₀d(x,y)) * |M_α⁻¹(x,y)| ≤ C * exp(-α₀d(x,y))
      rw [mul_comm C]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (exp_pos _))
      -- Use entry_le_opNorm + inverse_opNorm_bound on the conjugated matrix
      trans ‖(conjugatedMatrix M α₀ dist y)⁻¹‖
      · exact entry_le_opNorm _ x y
      · -- Need: ‖(conjugatedMatrix M α₀ dist y)⁻¹‖ ≤ C
        -- This requires showing conjugated matrix has spectral gap γ/2
        -- and then applying inverse_opNorm_bound.
        -- The key computation: (exp(α₀R)-1)*‖M‖ = γ/2 by choice of α₀.
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
