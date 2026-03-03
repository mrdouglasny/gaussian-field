/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Circle Restriction: Sampling Smooth Periodic Functions on Lattice Points

Defines `circleRestriction L N`, a continuous linear map that samples a smooth
periodic function at N equally spaced lattice points with the correct
normalization for Riemann sum convergence.

## Main definitions

- `circleRestriction L N` — CLM from `SmoothMap_Circle L ℝ` to `ZMod N → ℝ`

## Mathematical background

The circle restriction map is:

  `(r_N f)(k) = √(L/N) · f(kL/N)`    for k = 0, ..., N-1

The `√(L/N)` normalization ensures that the ℓ² norm of r_N f approximates
the L² norm of f: `Σ_k |r_N f(k)|² ≈ ∫₀ᴸ |f(x)|² dx` as N → ∞.

This is the 1D torus analogue of the lattice embedding from the continuum
limit construction, specialized to periodic functions on [0,L].

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1 (Lattice approximation)
-/

import SmoothCircle.Basic
import Mathlib.Data.ZMod.Basic

noncomputable section

namespace GaussianField

open SmoothMap_Circle

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Circle restriction map -/

/-- Lattice spacing on the circle: `a = L/N`. -/
def circleSpacing (N : ℕ) [NeZero N] : ℝ := L / N

theorem circleSpacing_pos (N : ℕ) [NeZero N] : 0 < circleSpacing L N :=
  div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos N))

/-- Position of the k-th lattice point on the circle: `kL/N`.

Uses `ZMod.val` to convert `ZMod N` to `ℕ`, matching the `FinLatticeSites`
convention where lattice sites are indexed by `ZMod N`. -/
def circlePoint (N : ℕ) [NeZero N] (k : ZMod N) : ℝ :=
  (ZMod.val k : ℝ) * L / N

/-- Evaluation at a single point is continuous on `SmoothMap_Circle L ℝ`.

  `ev_x(f) = f(x)` satisfies `|f(x)| ≤ p_0(f)` (the C⁰ seminorm). -/
theorem continuous_eval_at (x : ℝ) :
    Continuous (fun f : SmoothMap_Circle L ℝ => f x) := by
  -- Enough to show the linear functional f ↦ f(x) is bounded by a seminorm
  set lm : SmoothMap_Circle L ℝ →ₗ[ℝ] ℝ :=
    { toFun := fun f => f x
      map_add' := fun f g => add_apply f g x
      map_smul' := fun r f => smul_apply r f x }
  change Continuous lm
  apply Seminorm.continuous_from_bounded smoothCircle_withSeminorms (norm_withSeminorms ℝ ℝ)
  intro _
  refine ⟨{0}, ⟨1, by norm_num⟩, fun f => ?_⟩
  simp only [Seminorm.comp_apply, Finset.sup_singleton, NNReal.smul_def,
    Seminorm.smul_apply, NNReal.coe_mk]
  -- Goal: (normSeminorm ℝ ℝ) (lm f) ≤ 1 • sobolevSeminorm 0 f
  rw [one_smul, coe_normSeminorm, Real.norm_eq_abs]
  calc |f x| = ‖iteratedDeriv 0 (⇑f) x‖ := by
        rw [iteratedDeriv_zero]; exact (Real.norm_eq_abs _).symm
    _ ≤ sobolevSeminorm 0 f := norm_iteratedDeriv_le_sobolevSeminorm' f 0 x


/-- The circle restriction as a linear map (before proving continuity). -/
def circleRestrictionLM (N : ℕ) [NeZero N] :
    SmoothMap_Circle L ℝ →ₗ[ℝ] (ZMod N → ℝ) where
  toFun f k := Real.sqrt (circleSpacing L N) * f (circlePoint L N k)
  map_add' f g := by ext k; simp [add_apply, mul_add]
  map_smul' r f := by ext k; simp [smul_apply, mul_left_comm]

/-- The circle restriction map: sample a smooth periodic function at N lattice points.

  `(r_N f)(k) = √(L/N) · f(kL/N)`

The √(L/N) normalization makes the ℓ² inner product ⟨r_N f, r_N g⟩ approximate
the L²([0,L]) inner product ∫₀ᴸ f(x)g(x)dx as N → ∞. -/
def circleRestriction (N : ℕ) [NeZero N] :
    SmoothMap_Circle L ℝ →L[ℝ] (ZMod N → ℝ) where
  toLinearMap := circleRestrictionLM L N
  cont := by
    -- The map is continuous because it's a finite product of (scalar * eval_at_point),
    -- each of which is continuous since evaluation is continuous.
    apply continuous_pi
    intro k
    exact continuous_const.mul (continuous_eval_at L (circlePoint L N k))

@[simp] theorem circleRestriction_apply (N : ℕ) [NeZero N]
    (f : SmoothMap_Circle L ℝ) (k : ZMod N) :
    circleRestriction L N f k = Real.sqrt (circleSpacing L N) * f (circlePoint L N k) := rfl

/-- The circle restriction equals √(L/N) times evaluation at kL/N. -/
theorem circleRestriction_eq (N : ℕ) [NeZero N]
    (f : SmoothMap_Circle L ℝ) (k : ZMod N) :
    circleRestriction L N f k = Real.sqrt (L / N) * f ((ZMod.val k : ℝ) * L / N) := by
  simp [circleSpacing, circlePoint]

omit [Fact (0 < L)] in
@[simp] theorem circleSpacing_eq (N : ℕ) [NeZero N] :
    circleSpacing L N = L / N := rfl

/-! ## Duality with geometric embedding

The circle restriction is dual to the geometric torus embedding:
- `circlePoint L N k` gives the real coordinate `(ZMod.val k) * L / N`
- `ZMod.toScaledAddCircle L N hL k` gives the same value modulo L in `AddCircle L`

The torus embedding `torusEmbedCLM` (from `Torus/Evaluation.lean`) maps lattice
fields to configurations, while `circleRestriction` samples test functions at
lattice points. These are transposes: `⟨ι_N(φ), f⟩ = ⟨φ, r_N(f)⟩`. -/

/-! ## Riemann sum convergence -/

/-- The ℓ² norm squared of r_N f equals (L/N) times the Riemann sum of f². -/
theorem circleRestriction_sq_sum (N : ℕ) [NeZero N] (f : SmoothMap_Circle L ℝ) :
    ∑ k : ZMod N, (circleRestriction L N f k) ^ 2 =
    (L / ↑N) * ∑ k : ZMod N, (f (circlePoint L N k)) ^ 2 := by
  simp only [circleRestriction_apply, mul_pow, circleSpacing_eq]
  rw [← Finset.mul_sum]
  congr 1
  rw [Real.sq_sqrt (le_of_lt (div_pos hL.out (Nat.cast_pos.mpr (NeZero.pos N))))]

end GaussianField
