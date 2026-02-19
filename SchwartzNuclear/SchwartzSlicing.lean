/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Schwartz Function Slicing and Partial Hermite Coefficients

Defines the slicing of a multi-dimensional Schwartz function along one coordinate
and the partial Hermite coefficient map. These are the "A1" and "A2" analytical
constructions used in the multi-dimensional Hermite expansion proof.

## Main definitions

- `euclideanSnoc d y t` : embed `(y, t)` into `EuclideanSpace ℝ (Fin (d+1))`
- `euclideanInit d x` : project to the first `d` coordinates
- `schwartz_slice d f y` : fix first `d+1` coordinates of `f ∈ S(ℝ^{d+2})`, get `S(ℝ)`
- `schwartz_partial_hermiteCoeff d f n` : integrate out last coordinate against
  the `n`-th Hermite function, get `S(ℝ^{d+1})`

## Sorry inventory

- `schwartz_slice.smooth'` — smoothness of `t ↦ f(y, t)` as function of `t`
- `schwartz_slice.decay'` — Schwartz decay of the slice
- `schwartz_partial_hermiteCoeff.smooth'` — smoothness of `y ↦ ∫ f(y,t) ψ_n(t) dt`
- `schwartz_partial_hermiteCoeff.decay'` — Schwartz decay of the partial coefficient

These are standard analytical facts (restriction of Schwartz functions,
differentiation under the integral sign) not yet in Mathlib's multi-variable API.
-/

import SchwartzNuclear.SchwartzHermiteExpansion

open MeasureTheory Real SchwartzMap

noncomputable section

namespace GaussianField

/-- Embed `EuclideanSpace ℝ (Fin d) × ℝ` into `EuclideanSpace ℝ (Fin (d + 1))`
by appending the real value as the last coordinate. -/
def euclideanSnoc (d : ℕ) (y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    EuclideanSpace ℝ (Fin (d + 1)) :=
  (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y i) t)

/-- Project `EuclideanSpace ℝ (Fin (d + 1))` to its first `d` coordinates. -/
def euclideanInit (d : ℕ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    EuclideanSpace ℝ (Fin d) :=
  (WithLp.equiv 2 _).symm (fun i => x (Fin.castSucc i))

/-- Snoc of init and last coordinate recovers the original point. -/
lemma euclideanSnoc_init_last (d : ℕ) (x : EuclideanSpace ℝ (Fin (d + 1))) :
    euclideanSnoc d (euclideanInit d x) (x (Fin.last d)) = x := by
  simp only [euclideanSnoc, euclideanInit]
  apply (WithLp.equiv 2 _).injective
  simp only [Equiv.apply_symm_apply]
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro j; simp [Fin.snoc_castSucc]

/-- `euclideanSnoc d y` has temperate growth as a function of `t`. -/
private lemma euclideanSnoc_hasTemperateGrowth (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    Function.HasTemperateGrowth (euclideanSnoc (d + 1) y) := by
  have h_eq : euclideanSnoc (d+1) y =
    (EuclideanSpace.equiv (Fin (d+2)) ℝ).symm ∘ (fun t => Fin.snoc (fun i => y i) t) := by
    ext t; simp [euclideanSnoc, EuclideanSpace.equiv]
  rw [h_eq]
  exact (Function.HasTemperateGrowth.of_pi (fun i => Fin.lastCases
    (by simp [Fin.snoc_last]; exact Function.HasTemperateGrowth.id')
    (fun j => by simp [Fin.snoc_castSucc]; exact Function.HasTemperateGrowth.const _) i)).comp_clm
      (EuclideanSpace.equiv (Fin (d+2)) ℝ).symm

/-- `euclideanSnoc d y` is antilipschitz (in fact isometric) in `t`. -/
private lemma euclideanSnoc_antilipschitz (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    AntilipschitzWith 1 (euclideanSnoc (d + 1) y) := by
  refine AntilipschitzWith.of_dist_le_mul (fun s t => ?_)
  simp only [NNReal.coe_one, one_mul, dist_eq_norm]
  rw [EuclideanSpace.norm_eq]
  have hcoord : ∀ i : Fin (d+2),
    ‖(euclideanSnoc (d+1) y s - euclideanSnoc (d+1) y t) i‖ =
    if i = Fin.last (d+1) then ‖s - t‖ else 0 := by
    intro i
    simp only [euclideanSnoc, WithLp.equiv_symm_pi_lp_apply, Pi.sub_apply]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]
  have hsum : ∑ i, ‖(euclideanSnoc (d+1) y s - euclideanSnoc (d+1) y t) i‖ ^ 2
    = ‖s - t‖ ^ 2 := by
    conv_lhs => arg 2; ext i; rw [hcoord]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  rw [hsum, Real.sqrt_sq (norm_nonneg _)]

-- A1: Slicing a Schwartz function along the last coordinate
/-- Restrict `f ∈ S(ℝ^{d+2})` to the hyperplane `{x | x_rest = y}`,
giving a Schwartz function of the last coordinate. -/
noncomputable def schwartz_slice (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    SchwartzMap ℝ ℝ where
  toFun t := f (euclideanSnoc (d + 1) y t)
  smooth' :=
    (compCLMOfAntilipschitz ℝ (euclideanSnoc_hasTemperateGrowth d y)
      (euclideanSnoc_antilipschitz d y) f).smooth'
  decay' :=
    (compCLMOfAntilipschitz ℝ (euclideanSnoc_hasTemperateGrowth d y)
      (euclideanSnoc_antilipschitz d y) f).decay'

-- A2: Partial Hermite coefficient is Schwartz in remaining coordinates
/-- Integrate out the last coordinate of `f` against the `n`-th Hermite
function, giving a Schwartz function of the remaining `d + 1` coordinates.
The `sorry`s are smoothness and decay of `y ↦ ∫ f(y,t) ψ_n(t) dt`. -/
noncomputable def schwartz_partial_hermiteCoeff (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (n : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ where
  toFun y := hermiteCoeff1D n (schwartz_slice d f y)
  smooth' := sorry
  decay' := sorry

-- A3b: Partial coefficient relates to 1D slice (definitionally true)
lemma schwartz_partial_hermiteCoeff_eq_1D (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (n : ℕ) (y : EuclideanSpace ℝ (Fin (d + 1))) :
    schwartz_partial_hermiteCoeff d f n y =
      hermiteCoeff1D n (schwartz_slice d f y) := rfl

-- A3c: Slice evaluation (definitionally true)
lemma schwartz_slice_eq (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    schwartz_slice d f y t = f (euclideanSnoc (d + 1) y t) := rfl

end GaussianField
