/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Symmetry Operators

Translation and reflection operators on the finite lattice, and their
commutation with the Laplacian (hence with the heat kernel and Green's function).

## Main definitions

- `latticeTranslation` — translation by `v ∈ (ℤ/Nℤ)^d` on lattice fields
- `latticeFullReflection` — full reflection `x ↦ -x`

## Main theorems

- `finiteLaplacian_translation_commute` — `Δ ∘ T_v = T_v ∘ Δ`
- `negLaplacianMatrix_toeplitz` — `(-Δ)(x+v, y+v) = (-Δ)(x, y)`
- `latticeTranslationMatrix_commute_negLaplacian` — `[T_v, -Δ] = 0` (matrix level)
- `latticeTranslation_commute_heatKernel` — `[T_v, K_t] = 0`

## Mathematical background

The discrete Laplacian on the periodic torus `(ℤ/Nℤ)^d` is a Toeplitz matrix:
its entries depend only on the difference `x - y`. This means every translation
operator commutes with it. Reflections `x ↦ -x` also commute because
the Laplacian stencil is symmetric in `±eᵢ`.

By `Commute.exp_right` (Mathlib), commuting with `-Δ` automatically gives
commutation with `K_t = exp(-t·(-Δ))` and hence Green's function invariance.
-/

import Lattice.HeatKernel

noncomputable section

namespace GaussianField

open Matrix

variable (d N : ℕ) [NeZero N]

/-! ## Translation operators -/

/-- Translation of a lattice field by `v ∈ (ℤ/Nℤ)^d`:
`(T_v f)(x) = f(x - v)`. -/
def latticeTranslationFun (v : FinLatticeSites d N)
    (f : FinLatticeField d N) : FinLatticeField d N :=
  fun x => f (x - v)

/-- Translation is linear. -/
def latticeTranslationLM (v : FinLatticeSites d N) :
    FinLatticeField d N →ₗ[ℝ] FinLatticeField d N where
  toFun := latticeTranslationFun d N v
  map_add' f g := by ext x; simp [latticeTranslationFun]
  map_smul' r f := by ext x; simp [latticeTranslationFun]

/-- Translation as a continuous linear map (automatic continuity). -/
def latticeTranslation (v : FinLatticeSites d N) :
    FinLatticeField d N →L[ℝ] FinLatticeField d N :=
  { latticeTranslationLM d N v with
    cont := (latticeTranslationLM d N v).continuous_of_finiteDimensional }

/-- Translation matrix: `T_v(x, y) = 1` if `y = x - v`, else `0`.
This is the matrix of the translation operator `(T_v f)(x) = f(x - v)`. -/
def latticeTranslationMatrix (v : FinLatticeSites d N) :
    Matrix (FinLatticeSites d N) (FinLatticeSites d N) ℝ :=
  fun x y => if y = x - v then 1 else 0

/-! ## Laplacian-translation commutation -/

/-- Key lemma: the Laplacian raw function commutes with translation.
`(Δ(T_v f))(x) = (T_v(Δ f))(x)` for all x.

Proof: The Laplacian stencil involves `f(x ± eᵢ)`, and shifting the argument
commutes with shifting the stencil by periodicity of `(ℤ/Nℤ)^d`. -/
theorem finiteLaplacian_translation_commute (a : ℝ) (v : FinLatticeSites d N)
    (f : FinLatticeField d N) :
    finiteLaplacian d N a (latticeTranslationFun d N v f) =
    latticeTranslationFun d N v (finiteLaplacian d N a f) := by
  ext x
  simp only [latticeTranslationFun]
  change finiteLaplacianFun d N a (fun z => f (z - v)) x =
    finiteLaplacianFun d N a f (x - v)
  simp only [finiteLaplacianFun]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have h_fwd : (fun j => if j = i then x j + 1 else x j) - v =
      fun j => if j = i then (x - v) j + 1 else (x - v) j := by
    ext j; simp [Pi.sub_apply]; split_ifs <;> ring
  have h_bwd : (fun j => if j = i then x j - 1 else x j) - v =
      fun j => if j = i then (x - v) j - 1 else (x - v) j := by
    ext j; simp [Pi.sub_apply]; split_ifs <;> ring
  rw [h_fwd, h_bwd]

/-! ## Delta function shift -/

/-- Shifting the delta function: `δ_{y+v} = T_v(δ_y)`.
`δ_{y+v}(z) = 1 iff z = y+v iff z-v = y = δ_y(z-v) = (T_v δ_y)(z)`. -/
set_option linter.unusedSectionVars false in
private theorem finLatticeDelta_shift (v : FinLatticeSites d N)
    (y : FinLatticeSites d N) :
    finLatticeDelta d N (y + v) =
    latticeTranslationFun d N v (finLatticeDelta d N y) := by
  ext z
  simp only [finLatticeDelta, latticeTranslationFun]
  -- Conditions: (z = y + v) and (z - v = y) are equivalent
  have : (z = y + v) ↔ (z - v = y) :=
    ⟨fun h => by rw [h, add_sub_cancel_right],
     fun h => by rw [← h, sub_add_cancel]⟩
  simp [this]

/-! ## Toeplitz property of the negative Laplacian -/

/-- The negative Laplacian matrix is Toeplitz (translation-invariant):
`(-Δ)(x + v, y + v) = (-Δ)(x, y)`.

This is the fundamental symmetry of the lattice Laplacian: its matrix entries
depend only on the difference `x - y`.

Proof: M(x+v, y+v) = (-Δ δ_{y+v})(x+v) = (-Δ (T_v δ_y))(x+v)
     = (T_v(-Δ δ_y))(x+v) = (-Δ δ_y)((x+v)-v) = (-Δ δ_y)(x) = M(x,y). -/
theorem negLaplacianMatrix_toeplitz (a : ℝ) (v : FinLatticeSites d N)
    (x y : FinLatticeSites d N) :
    negLaplacianMatrix d N a (x + v) (y + v) =
    negLaplacianMatrix d N a x y := by
  simp only [negLaplacianMatrix, massOperatorMatrix, massOperatorEntry]
  simp only [massOperator, sq, mul_zero, zero_smul, add_zero,
    ContinuousLinearMap.neg_apply]
  congr 1
  rw [finLatticeDelta_shift d N v y,
      finiteLaplacian_translation_commute d N a v (finLatticeDelta d N y)]
  simp [latticeTranslationFun, add_sub_cancel_right]

/-! ## Matrix commutation -/

/-- Translation matrix commutes with the negative Laplacian matrix.
`T_v · (-Δ) = (-Δ) · T_v`

Follows from the Toeplitz property. -/
theorem latticeTranslationMatrix_commute_negLaplacian (a : ℝ)
    (v : FinLatticeSites d N) :
    Commute (latticeTranslationMatrix d N v) (negLaplacianMatrix d N a) := by
  rw [Commute, SemiconjBy]
  ext x y
  simp only [Matrix.mul_apply, latticeTranslationMatrix]
  -- Convert RHS condition y = z - v to z = y + v
  simp_rw [show ∀ z : FinLatticeSites d N, (y = z - v) = (z = y + v) from
    fun z => propext ⟨fun h => by rw [h, sub_add_cancel],
                      fun h => by rw [h, add_sub_cancel_right]⟩]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (x - v),
      Finset.sum_ite_eq' Finset.univ (y + v)]
  simp only [Finset.mem_univ, ite_true]
  -- Now: M(x-v, y) = M(x, y+v)
  have h := negLaplacianMatrix_toeplitz d N a v (x - v) y
  rw [sub_add_cancel] at h
  exact h.symm

/-! ## Heat kernel commutation -/

/-- Translation commutes with the heat kernel: `[T_v, K_t] = 0`.

Immediate from translation commuting with `-Δ`, via `Commute.exp_right`. -/
theorem latticeTranslation_commute_heatKernel (a t : ℝ)
    (v : FinLatticeSites d N) :
    Commute (latticeTranslationMatrix d N v) (latticeHeatKernelMatrix d N a t) :=
  latticeHeatKernelMatrix_commute d N a t _
    (latticeTranslationMatrix_commute_negLaplacian d N a v)

/-! ## Reflection operators -/

/-- Full reflection: negate all coordinates.
`(Rf)(x) = f(-x)`. -/
def latticeFullReflectionFun
    (f : FinLatticeField d N) : FinLatticeField d N :=
  fun x => f (-x)

/-- Full reflection matrix: `R(x, y) = 1` if `y = -x`, else `0`. -/
def latticeFullReflectionMatrix :
    Matrix (FinLatticeSites d N) (FinLatticeSites d N) ℝ :=
  fun x y => if y = -x then 1 else 0

/-- The Laplacian raw function commutes with full reflection `x ↦ -x`.

Proof: The stencil `f(-x + eᵢ) + f(-x - eᵢ) - 2f(-x)` equals
`f(-(x - eᵢ)) + f(-(x + eᵢ)) - 2f(-x)`, which is the stencil of `f(-·)`
at `x` with the ±eᵢ terms swapped (sum is commutative). -/
theorem finiteLaplacian_reflection_commute (a : ℝ)
    (f : FinLatticeField d N) :
    finiteLaplacian d N a (latticeFullReflectionFun d N f) =
    latticeFullReflectionFun d N (finiteLaplacian d N a f) := by
  ext x
  simp only [latticeFullReflectionFun]
  change finiteLaplacianFun d N a (fun z => f (-z)) x =
    finiteLaplacianFun d N a f (-x)
  simp only [finiteLaplacianFun]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have h_fwd : -(fun j => if j = i then x j + 1 else x j) =
      fun j => if j = i then (-x) j - 1 else (-x) j := by
    ext j; simp [Pi.neg_apply]; split_ifs <;> ring
  have h_bwd : -(fun j => if j = i then x j - 1 else x j) =
      fun j => if j = i then (-x) j + 1 else (-x) j := by
    ext j; simp [Pi.neg_apply]; split_ifs <;> ring
  rw [h_fwd, h_bwd]
  ring

/-- Delta function under negation: `δ_{-y}(z) = δ_y(-z)`. -/
set_option linter.unusedSectionVars false in
private theorem finLatticeDelta_neg (y : FinLatticeSites d N) :
    finLatticeDelta d N (-y) =
    latticeFullReflectionFun d N (finLatticeDelta d N y) := by
  ext z
  simp only [finLatticeDelta, latticeFullReflectionFun]
  have : (z = -y) ↔ (-z = y) :=
    ⟨fun h => by rw [h, neg_neg], fun h => by rw [← h, neg_neg]⟩
  simp [this]

/-- The negative Laplacian is invariant under negation of both arguments:
`(-Δ)(-x, -y) = (-Δ)(x, y)`.

This is the even/reflection symmetry of the Laplacian. -/
theorem negLaplacianMatrix_neg_invariant (a : ℝ)
    (x y : FinLatticeSites d N) :
    negLaplacianMatrix d N a (-x) (-y) =
    negLaplacianMatrix d N a x y := by
  simp only [negLaplacianMatrix, massOperatorMatrix, massOperatorEntry]
  simp only [massOperator, sq, mul_zero, zero_smul, add_zero,
    ContinuousLinearMap.neg_apply]
  congr 1
  rw [finLatticeDelta_neg d N y,
      finiteLaplacian_reflection_commute d N a (finLatticeDelta d N y)]
  simp [latticeFullReflectionFun]

/-- Full reflection commutes with the negative Laplacian.

Proof: M(-x, y) = M(0, y+x) by Toeplitz, M(x, -y) = M(x+y, 0) by Toeplitz,
and M(0, y+x) = M(x+y, 0) by Hermiticity (symmetry of the matrix). -/
theorem latticeFullReflectionMatrix_commute_negLaplacian (a : ℝ) :
    Commute (latticeFullReflectionMatrix d N) (negLaplacianMatrix d N a) := by
  rw [Commute, SemiconjBy]
  ext x y
  simp only [Matrix.mul_apply, latticeFullReflectionMatrix]
  -- Convert RHS condition y = -z to z = -y
  simp_rw [show ∀ z : FinLatticeSites d N, (y = -z) = (z = -y) from
    fun z => propext ⟨fun h => by rw [h, neg_neg],
                      fun h => by rw [h, neg_neg]⟩]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (-x),
      Finset.sum_ite_eq' Finset.univ (-y)]
  simp only [Finset.mem_univ, ite_true]
  -- M(-x, y) = M(x, -y)
  -- Step 1: M(-x, y) = M(0, y+x) by Toeplitz with v = x
  have h1 := negLaplacianMatrix_toeplitz d N a x (-x) y
  simp only [neg_add_cancel] at h1
  -- h1 : M(0, y + x) = M(-x, y)
  -- Step 2: M(x, -y) = M(x+y, 0) by Toeplitz with v = y
  have h2 := negLaplacianMatrix_toeplitz d N a y x (-y)
  simp only [neg_add_cancel] at h2
  -- h2 : M(x + y, 0) = M(x, -y)
  rw [← h1, ← h2]
  -- Goal: M(0, y+x) = M(x+y, 0), which is Hermiticity
  have hsymm := (negLaplacianMatrix_isHermitian d N a).eq
  have h3 := congr_fun (congr_fun hsymm 0) (y + x)
  simp [Matrix.conjTranspose] at h3
  rw [h3.symm, add_comm]

/-- Full reflection commutes with the heat kernel. -/
theorem latticeFullReflection_commute_heatKernel (a t : ℝ) :
    Commute (latticeFullReflectionMatrix d N) (latticeHeatKernelMatrix d N a t) :=
  latticeHeatKernelMatrix_commute d N a t _
    (latticeFullReflectionMatrix_commute_negLaplacian d N a)

end GaussianField
