/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Asymmetric Discrete Laplacian

Defines the discrete Laplacian on the 2D finite torus with DIFFERENT
lattice spacings in each direction: `at` (time) and `as` (space).

This generalizes `finiteLaplacian d N a` which uses a single spacing `a`.

## Main definitions

- `asymFiniteLaplacian N at as` — 2D Laplacian with per-direction spacings
- `asymMassOperator N at as mass` — `-Δ_{at,as} + m²`

## Mathematical background

The asymmetric discrete Laplacian with spacings (at, as) is:

  `(Δ f)(i,j) = at⁻² [f(i+1,j) + f(i-1,j) - 2f(i,j)]
              + as⁻² [f(i,j+1) + f(i,j-1) - 2f(i,j)]`

Eigenvalues on (ℤ/Nℤ)²:
  `λ_{n₁,n₂} = (4/at²) sin²(πn₁/N) + (4/as²) sin²(πn₂/N)`

The mass operator eigenvalues `λ + m²` satisfy `λ + m² ≥ m² > 0`.
-/

import Lattice.Laplacian

noncomputable section

namespace GaussianField

open Real

variable (N : ℕ) [NeZero N]

/-! ## Asymmetric Laplacian on 2D lattice -/

/-- The asymmetric discrete Laplacian on (ℤ/Nℤ)² with spacings `at` (direction 0)
and `as` (direction 1).

  `(Δ f)(x) = at⁻² [f(x+e₀) + f(x-e₀) - 2f(x)] + as⁻² [f(x+e₁) + f(x-e₁) - 2f(x)]`
-/
def asymFiniteLaplacianFun (at' as' : ℝ) (f : FinLatticeField 2 N)
    (x : FinLatticeSites 2 N) : ℝ :=
  at'⁻¹ ^ 2 * (f (fun j => if j = (0 : Fin 2) then x j + 1 else x j) +
                f (fun j => if j = (0 : Fin 2) then x j - 1 else x j) -
                2 * f x) +
  as'⁻¹ ^ 2 * (f (fun j => if j = (1 : Fin 2) then x j + 1 else x j) +
                f (fun j => if j = (1 : Fin 2) then x j - 1 else x j) -
                2 * f x)

/-- The asymmetric Laplacian as a linear map. -/
def asymFiniteLaplacianLM (at' as' : ℝ) :
    FinLatticeField 2 N →ₗ[ℝ] FinLatticeField 2 N where
  toFun := asymFiniteLaplacianFun N at' as'
  map_add' := fun f g => by
    funext x; simp only [asymFiniteLaplacianFun, Pi.add_apply]
    ring
  map_smul' := fun r f => by
    funext x; simp only [asymFiniteLaplacianFun, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

/-- The asymmetric Laplacian as a CLM.
Continuity is automatic on finite-dimensional spaces. -/
noncomputable def asymFiniteLaplacian (at' as' : ℝ) :
    FinLatticeField 2 N →L[ℝ] FinLatticeField 2 N where
  toLinearMap := asymFiniteLaplacianLM N at' as'
  cont := by
    apply LinearMap.continuous_of_finiteDimensional

/-- The asymmetric Laplacian reduces to the symmetric one when at = as. -/
theorem asymFiniteLaplacian_eq_symmetric (a : ℝ) (f : FinLatticeField 2 N)
    (x : FinLatticeSites 2 N) :
    asymFiniteLaplacianFun N a a f x = finiteLaplacianFun 2 N a f x := by
  simp only [asymFiniteLaplacianFun, finiteLaplacianFun, Fin.sum_univ_two]
  ring

/-! ## Asymmetric mass operator -/

/-- The asymmetric mass operator: `-Δ_{at,as} + m²`.

This is the inverse covariance of the lattice GFF on the asymmetric torus. -/
noncomputable def asymMassOperator (at' as' mass : ℝ) :
    FinLatticeField 2 N →L[ℝ] FinLatticeField 2 N :=
  -asymFiniteLaplacian N at' as' + mass ^ 2 • ContinuousLinearMap.id ℝ _

/-- The asymmetric mass operator reduces to the symmetric one when at = as. -/
theorem asymMassOperator_eq_symmetric (a mass : ℝ) :
    asymMassOperator N a a mass = massOperator 2 N a mass := by
  ext f x
  simp only [asymMassOperator, massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply,
    smul_eq_mul]
  have h := asymFiniteLaplacian_eq_symmetric N a f x
  -- The CLM values agree pointwise; the CLMs are defined from their Fun functions
  show -(asymFiniteLaplacianFun N a a f x) + mass ^ 2 * f x =
       -(finiteLaplacianFun 2 N a f x) + mass ^ 2 * f x
  rw [h]

end GaussianField
