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

- `contDiff_parametric_hermiteCoeff` — `ContDiff ℝ ⊤` and iterated derivative commutation
  for `y ↦ ∫ f(y,t) ψ_n(t) dt`

This requires iterated differentiation under the integral sign, not yet
available in Mathlib (only single-step `hasFDerivAt_integral_of_dominated_of_fderiv_le`).

## Proved lemmas

- `euclideanSnoc_norm_sq` — `‖euclideanSnoc y t‖² = ‖y‖² + t²`
- `euclideanSnoc_norm_ge_left` — `‖y‖ ≤ ‖euclideanSnoc y t‖`
- `integral_euclidean_snoc` — Fubini for EuclideanSpace slicing
-/

import SchwartzNuclear.SchwartzHermiteExpansion
-- import Mathlib.Analysis.Calculus.ParametricIntegral  -- needed for smooth' proof

open MeasureTheory Real SchwartzMap Measure

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
  -- The linear part: embed ℝ as the last coordinate in EuclideanSpace
  set L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
    (EuclideanSpace.equiv (Fin (d+2)) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single (R := ℝ) (φ := fun (_ : Fin (d + 2)) => ℝ)
        (Fin.last (d + 1)))
  -- The constant part
  set c := euclideanSnoc (d + 1) y 0
  have h_snoc_decomp : ∀ t,
      Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) t =
      Fin.snoc (α := fun _ => ℝ) (fun i => y.ofLp i) 0 +
        Pi.single (Fin.last (d + 1)) t := by
    intro t
    ext i
    rw [Pi.add_apply]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]
  have h_eq : euclideanSnoc (d+1) y = (fun t => c + L t) := by
    funext t
    simp only [c, L, euclideanSnoc, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.single_apply, ContinuousLinearEquiv.coe_coe]
    show (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) t) =
      (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) 0) +
      (EuclideanSpace.equiv (Fin (d+2)) ℝ).symm (Pi.single (Fin.last (d+1)) t)
    rw [h_snoc_decomp]
    simp [EuclideanSpace.equiv]
  rw [h_eq]
  exact Function.HasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
    L.hasTemperateGrowth

/-- `euclideanSnoc d y` is antilipschitz (in fact isometric) in `t`. -/
private lemma euclideanSnoc_antilipschitz (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    AntilipschitzWith 1 (euclideanSnoc (d + 1) y) := by
  refine AntilipschitzWith.of_le_mul_dist (fun s t => ?_)
  simp only [NNReal.coe_one, one_mul]
  have hcoord : ∀ i : Fin (d+2),
    ‖(euclideanSnoc (d+1) y s - euclideanSnoc (d+1) y t) i‖ =
    if i = Fin.last (d+1) then ‖s - t‖ else 0 := by
    intro i
    simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_sub, Pi.sub_apply]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]
  have hsum : ∑ i, ‖(euclideanSnoc (d+1) y s - euclideanSnoc (d+1) y t) i‖ ^ 2
    = ‖s - t‖ ^ 2 := by
    conv_lhs => arg 2; ext i; rw [hcoord]
    simp [Finset.sum_ite_eq', Finset.mem_univ]
  show dist s t ≤ dist (euclideanSnoc (d + 1) y s) (euclideanSnoc (d + 1) y t)
  rw [dist_eq_norm, dist_eq_norm (E := EuclideanSpace ℝ _), EuclideanSpace.norm_eq,
    hsum, Real.sqrt_sq (norm_nonneg _)]

/-- The norm of `euclideanSnoc y t` satisfies `‖y‖² + t² = ‖euclideanSnoc y t‖²`.
This is because snoc just appends one coordinate. -/
private lemma euclideanSnoc_norm_sq (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    ‖euclideanSnoc (d + 1) y t‖ ^ 2 = ‖y‖ ^ 2 + t ^ 2 := by
  have hlast : (euclideanSnoc (d + 1) y t) (Fin.last (d + 1)) = t := by
    simp [euclideanSnoc, Fin.snoc_last]
  have hcast : ∀ j : Fin (d + 1),
      (euclideanSnoc (d + 1) y t) (Fin.castSucc j) = y j := by
    intro j; simp [euclideanSnoc, Fin.snoc_castSucc]
  simp only [EuclideanSpace.norm_eq]
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
    Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rw [show ∑ i : Fin (d + 2), ‖(euclideanSnoc (d + 1) y t) i‖ ^ 2 =
    (∑ j : Fin (d + 1), ‖(euclideanSnoc (d + 1) y t) (Fin.castSucc j)‖ ^ 2) +
    ‖(euclideanSnoc (d + 1) y t) (Fin.last (d + 1))‖ ^ 2 from
    Fin.sum_univ_castSucc _]
  rw [hlast, norm_eq_abs, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [hcast]

/-- The first `d+1` coordinates contribute to the norm:
`‖y‖ ≤ ‖euclideanSnoc (d+1) y t‖`. -/
private lemma euclideanSnoc_norm_ge_left (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    ‖y‖ ≤ ‖euclideanSnoc (d + 1) y t‖ := by
  rw [← Real.sqrt_sq (norm_nonneg y),
    ← Real.sqrt_sq (norm_nonneg (euclideanSnoc (d + 1) y t))]
  apply Real.sqrt_le_sqrt
  rw [euclideanSnoc_norm_sq]
  linarith [sq_nonneg t]

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

/-! ## A2: Partial Hermite coefficient is Schwartz

The function `g(y) = ∫ f(euclideanSnoc y t) · ψ_n(t) dt` is Schwartz in y.

**Proof strategy** (following the parametric integral approach):

### Smoothness (`smooth'`)
Prove `ContDiff ℝ m` for all `m` by induction on `m`:
- Base (`m = 0`): continuity via `continuous_of_dominated`
- Step: `hasFDerivAt_integral_of_dominated_of_fderiv_le` gives the derivative
  as `∫ (∂_y f)(euclideanSnoc y t) · ψ_n(t) dt`, which has the same form with `∂_y f`
  (still Schwartz) replacing `f`, so the IH applies.

### Decay (`decay'`)
Use the key norm bound `‖y‖ ≤ ‖euclideanSnoc y t‖` (`euclideanSnoc_norm_ge_left`):
1. Commute `iteratedFDeriv` and the integral (via `smooth'`)
2. Bound `‖y‖^k * |integrand| ≤ ‖euclideanSnoc y t‖^k * |integrand|`
3. Apply Schwartz decay of `f` at the point `euclideanSnoc y t`
4. The resulting `t`-integral is finite since `hermiteFunction n` is integrable.
-/

/-- The integrand `f(euclideanSnoc y t) * hermiteFunction n t` is dominated
by `(seminorm ℝ 0 0 f) * |hermiteFunction n t|`, which is `y`-independent. -/
private lemma hermiteCoeff_integrand_bound (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    ‖f (euclideanSnoc (d + 1) y t) * hermiteFunction n t‖ ≤
      SchwartzMap.seminorm ℝ 0 0 f * ‖hermiteFunction n t‖ := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_le_seminorm ℝ f _) (norm_nonneg _)

/-- The dominating function `C * |hermiteFunction n t|` is integrable in `t`. -/
private lemma hermiteCoeff_bound_integrable (n : ℕ) (C : ℝ) :
    Integrable (fun t : ℝ => C * ‖hermiteFunction n t‖) := by
  apply Integrable.const_mul
  rw [show (fun t => ‖hermiteFunction n t‖) =
    (fun t => ‖(schwartzHermiteBasis1D n) t‖) from
    by ext t; rw [schwartzHermiteBasis1D_apply]]
  exact (schwartzHermiteBasis1D n).integrable.norm

/-- For fixed `t`, the map `y ↦ euclideanSnoc y t` is continuous.
Proved via 1-Lipschitz: changing `y` by `δ` changes `euclideanSnoc y t` by at most `δ`
since only the first `d+1` coordinates change. -/
private lemma continuous_euclideanSnoc_y (d : ℕ) (t : ℝ) :
    Continuous (fun y : EuclideanSpace ℝ (Fin (d + 1)) =>
      euclideanSnoc (d + 1) y t) := by
  apply LipschitzWith.continuous (K := 1)
  intro y₁ y₂
  simp only [ENNReal.coe_one, one_mul, edist_dist, dist_eq_norm]
  apply ENNReal.ofReal_le_ofReal
  -- ‖euclideanSnoc y₁ t - euclideanSnoc y₂ t‖ ≤ ‖y₁ - y₂‖
  rw [show euclideanSnoc (d + 1) y₁ t - euclideanSnoc (d + 1) y₂ t =
    euclideanSnoc (d + 1) (y₁ - y₂) 0 from by
    ext i
    simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_sub, Pi.sub_apply]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]]
  have h : ‖euclideanSnoc (d + 1) (y₁ - y₂) 0‖ ^ 2 = ‖y₁ - y₂‖ ^ 2 := by
    rw [euclideanSnoc_norm_sq]; ring
  nlinarith [norm_nonneg (euclideanSnoc (d + 1) (y₁ - y₂) 0), norm_nonneg (y₁ - y₂),
    sq_nonneg (‖euclideanSnoc (d + 1) (y₁ - y₂) 0‖ - ‖y₁ - y₂‖)]

/-- Iterated differentiation of a parametric integral:
if `g(y) = ∫ F(y, t) dt` where `F` is smooth in `y` with uniformly bounded
derivatives, then `g` is smooth and `iteratedFDeriv ℝ m g y = ∫ iteratedFDeriv_y ℝ m F(·, t) y dt`.

This is a standard result that follows by iterating
`hasFDerivAt_integral_of_dominated_of_fderiv_le` with the uniform bound
`‖iteratedFDeriv ℝ m (fun y' => f(euclideanSnoc y' t)) y‖ ≤ seminorm ℝ 0 m f`
(independent of `y` and `t`), ensuring the dominating function
`(seminorm ℝ 0 m f) * |hermiteFunction n t|` is integrable. -/
private lemma contDiff_parametric_hermiteCoeff (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y => ∫ t, f (euclideanSnoc (d + 1) y t) * hermiteFunction n t) ∧
    ∀ (m : ℕ) (y : EuclideanSpace ℝ (Fin (d + 1))),
      iteratedFDeriv ℝ m
        (fun y' => ∫ t, f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y =
      ∫ t, iteratedFDeriv ℝ m
        (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y := by
  sorry

/-- Smoothness of the partial Hermite coefficient: the function
`y ↦ ∫ f(y,t) ψ_n(t) dt` is `C^∞` in `y`. -/
private lemma schwartz_partial_hermiteCoeff_smooth (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => hermiteCoeff1D n (schwartz_slice d f y)) :=
  (contDiff_parametric_hermiteCoeff d f n).1

/-- For fixed `t`, the map `y ↦ euclideanSnoc y t` has temperate growth.
This is because the map is affine: `euclideanSnoc y t = c + L(y)` where
`L` is the castSucc isometric embedding and `c = euclideanSnoc 0 t = (0,...,0,t)`. -/
private lemma euclideanSnoc_y_hasTemperateGrowth (d : ℕ) (t : ℝ) :
    Function.HasTemperateGrowth (fun y : EuclideanSpace ℝ (Fin (d + 1)) =>
      euclideanSnoc (d + 1) y t) := by
  -- Constant part
  set c := euclideanSnoc (d + 1) (0 : EuclideanSpace ℝ (Fin (d + 1))) t
  -- Linear part: y ↦ euclideanSnoc y 0 (embeds y into first d+1 coordinates)
  set L_fun : EuclideanSpace ℝ (Fin (d + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
    { toFun := fun y => euclideanSnoc (d + 1) y 0
      map_add' := fun y₁ y₂ => by
        ext i
        simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_add, Pi.add_apply]
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc]
      map_smul' := fun a y => by
        ext i
        simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_smul,
          Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc] }
  have hL_bound : ∀ y, ‖L_fun y‖ ≤ 1 * ‖y‖ := fun y => by
    rw [one_mul]
    have hdef : ‖L_fun y‖ = ‖euclideanSnoc (d + 1) y 0‖ := rfl
    have h : ‖euclideanSnoc (d + 1) y 0‖ ^ 2 = ‖y‖ ^ 2 := by
      rw [euclideanSnoc_norm_sq]; ring
    nlinarith [norm_nonneg (euclideanSnoc (d + 1) y 0), norm_nonneg y,
      sq_nonneg (‖euclideanSnoc (d + 1) y 0‖ - ‖y‖)]
  set L := L_fun.mkContinuous 1 hL_bound
  have h_eq : (fun y => euclideanSnoc (d + 1) y t) = fun y => c + L y := by
    funext y
    show euclideanSnoc (d + 1) y t =
      euclideanSnoc (d + 1) 0 t + euclideanSnoc (d + 1) y 0
    ext i
    simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_add, Pi.add_apply]
    refine Fin.lastCases ?_ ?_ i
    · simp [Fin.snoc_last]
    · intro j; simp [Fin.snoc_castSucc]
  rw [h_eq]
  exact Function.HasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
    L.hasTemperateGrowth

/-- For fixed `t`, the map `y ↦ euclideanSnoc y t` is antilipschitz with constant 1.
This is because only the first d+1 coordinates change while the last stays fixed at `t`. -/
private lemma euclideanSnoc_y_antilipschitz (d : ℕ) (t : ℝ) :
    AntilipschitzWith 1 (fun y : EuclideanSpace ℝ (Fin (d + 1)) =>
      euclideanSnoc (d + 1) y t) := by
  refine AntilipschitzWith.of_le_mul_dist (fun y₁ y₂ => ?_)
  simp only [NNReal.coe_one, one_mul]
  rw [dist_eq_norm, dist_eq_norm]
  -- ‖y₁ - y₂‖ ≤ ‖euclideanSnoc y₁ t - euclideanSnoc y₂ t‖
  -- because the difference in euclideanSnoc only has the y-components
  have h : ‖euclideanSnoc (d + 1) y₁ t - euclideanSnoc (d + 1) y₂ t‖ ^ 2 =
      ‖y₁ - y₂‖ ^ 2 := by
    rw [show euclideanSnoc (d + 1) y₁ t - euclideanSnoc (d + 1) y₂ t =
      euclideanSnoc (d + 1) (y₁ - y₂) 0 from by
      ext i
      simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_sub, Pi.sub_apply]
      refine Fin.lastCases ?_ ?_ i
      · simp [Fin.snoc_last]
      · intro j; simp [Fin.snoc_castSucc]]
    rw [euclideanSnoc_norm_sq]; ring
  nlinarith [norm_nonneg (euclideanSnoc (d + 1) y₁ t - euclideanSnoc (d + 1) y₂ t),
    norm_nonneg (y₁ - y₂),
    sq_nonneg (‖euclideanSnoc (d + 1) y₁ t - euclideanSnoc (d + 1) y₂ t‖ - ‖y₁ - y₂‖)]

/-- For fixed `t`, the composition `f ∘ euclideanSnoc · t` is a Schwartz function of `y`. -/
private noncomputable def schwartz_slice_y (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (t : ℝ) : SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ :=
  compCLMOfAntilipschitz ℝ (euclideanSnoc_y_hasTemperateGrowth d t)
    (euclideanSnoc_y_antilipschitz d t) f

/-- The linear part of `y ↦ euclideanSnoc y t`: the CLM `y ↦ euclideanSnoc y 0`
that isometrically embeds the first d+1 coordinates. -/
private noncomputable def euclideanSnoc_linearCLM (d : ℕ) :
    EuclideanSpace ℝ (Fin (d + 1)) →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
  LinearMap.mkContinuous
    { toFun := fun y => euclideanSnoc (d + 1) y 0
      map_add' := fun y₁ y₂ => by
        ext i
        simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_add, Pi.add_apply]
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc]
      map_smul' := fun a y => by
        ext i
        simp only [euclideanSnoc, WithLp.equiv_symm_apply, WithLp.ofLp_smul,
          Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc] }
    1 (fun y => by
      rw [one_mul]
      show ‖euclideanSnoc (d + 1) y 0‖ ≤ _
      have h : ‖euclideanSnoc (d + 1) y 0‖ ^ 2 = ‖y‖ ^ 2 := by
        rw [euclideanSnoc_norm_sq]; ring
      nlinarith [norm_nonneg (euclideanSnoc (d + 1) y 0), norm_nonneg y,
        sq_nonneg (‖euclideanSnoc (d + 1) y 0‖ - ‖y‖)])

private lemma euclideanSnoc_linearCLM_apply (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    euclideanSnoc_linearCLM d y = euclideanSnoc (d + 1) y 0 := rfl

private lemma euclideanSnoc_decomp (d : ℕ) (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    euclideanSnoc (d + 1) y t =
      euclideanSnoc (d + 1) 0 t + euclideanSnoc_linearCLM d y := by
  ext i
  simp only [euclideanSnoc, euclideanSnoc_linearCLM_apply,
    WithLp.equiv_symm_apply, WithLp.ofLp_add, Pi.add_apply]
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last]
  · intro j; simp [Fin.snoc_castSucc]

private lemma euclideanSnoc_linearCLM_norm_le (d : ℕ) :
    ‖euclideanSnoc_linearCLM d‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ zero_le_one _

/-- Pointwise bound: the y-seminorm of the slice `f ∘ euclideanSnoc · t` is
bounded by the seminorm of `f`, uniformly in `t`. This uses the chain rule
for the affine isometric embedding `y ↦ euclideanSnoc y t` together with
`euclideanSnoc_norm_ge_left` to transfer the polynomial weight. -/
private lemma schwartz_slice_y_le_seminorm (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (t : ℝ) (k m : ℕ) (y : EuclideanSpace ℝ (Fin (d + 1))) :
    ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (schwartz_slice_y d f t) y‖ ≤
      f.seminorm ℝ k m := by
  -- Step 1: schwartz_slice_y agrees with f ∘ euclideanSnoc · t pointwise
  -- and therefore has the same iteratedFDeriv
  set c := euclideanSnoc (d + 1) (0 : EuclideanSpace ℝ (Fin (d + 1))) t
  set L := euclideanSnoc_linearCLM d
  -- The slice function equals (f ∘ (c + ·)) ∘ L
  set f' : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun z => f (c + z)
  -- Step 2: Chain rule for composition with L
  have hf'_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f' := by
    exact f.smooth'.comp (contDiff_const.add contDiff_id)
  have h_chain : iteratedFDeriv ℝ m (f' ∘ ⇑L) y =
      (iteratedFDeriv ℝ m f' (L y)).compContinuousLinearMap (fun _ => L) :=
    L.iteratedFDeriv_comp_right hf'_smooth y
      (WithTop.coe_le_coe.mpr le_top)
  -- Step 3: Translation invariance: iteratedFDeriv m f' z = iteratedFDeriv m f (c + z)
  have h_trans : ∀ z, iteratedFDeriv ℝ m f' z =
      iteratedFDeriv ℝ m (f : EuclideanSpace ℝ (Fin (d + 2)) → ℝ) (c + z) :=
    fun z => iteratedFDeriv_comp_add_left m c z
  -- Step 4: The slice function equals f' ∘ L
  have h_fun_eq : (schwartz_slice_y d f t : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) =
      f' ∘ ⇑L := by
    ext y'
    simp only [schwartz_slice_y, compCLMOfAntilipschitz_apply, Function.comp_apply, f']
    congr 1
    exact euclideanSnoc_decomp d y' t
  -- Step 5: Norm bound on the iterated derivative
  have h_norm : ‖iteratedFDeriv ℝ m (schwartz_slice_y d f t) y‖ ≤
      ‖iteratedFDeriv ℝ m f (euclideanSnoc (d + 1) y t)‖ := by
    rw [show (schwartz_slice_y d f t : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) = f' ∘ ⇑L
        from h_fun_eq]
    rw [h_chain]
    calc ‖(iteratedFDeriv ℝ m f' (L y)).compContinuousLinearMap (fun _ => L)‖
        ≤ ‖iteratedFDeriv ℝ m f' (L y)‖ * ∏ _ : Fin m, ‖L‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ m f' (L y)‖ * 1 := by
          gcongr
          calc ∏ _ : Fin m, ‖L‖ ≤ ∏ _ : Fin m, (1 : ℝ) :=
                Finset.prod_le_prod (fun _ _ => norm_nonneg _)
                  (fun _ _ => euclideanSnoc_linearCLM_norm_le d)
            _ = 1 := by simp
      _ = ‖iteratedFDeriv ℝ m f (c + L y)‖ := by rw [mul_one, h_trans]
      _ = ‖iteratedFDeriv ℝ m f (euclideanSnoc (d + 1) y t)‖ := by
          rw [euclideanSnoc_decomp d y t]
  -- Step 6: Combine with Schwartz decay
  calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ m (schwartz_slice_y d f t) y‖
      ≤ ‖y‖ ^ k * ‖iteratedFDeriv ℝ m f (euclideanSnoc (d + 1) y t)‖ :=
        mul_le_mul_of_nonneg_left h_norm (pow_nonneg (norm_nonneg _) _)
    _ ≤ ‖euclideanSnoc (d + 1) y t‖ ^ k *
        ‖iteratedFDeriv ℝ m f (euclideanSnoc (d + 1) y t)‖ := by
        gcongr; exact euclideanSnoc_norm_ge_left d y t
    _ ≤ f.seminorm ℝ k m := SchwartzMap.le_seminorm ℝ k m f _

/-- Schwartz decay of the partial Hermite coefficient: for all `k, m`,
`sup_y ‖y‖^k · ‖∂^m_y g(y)‖ < ∞` where `g(y) = ∫ f(y,t) ψ_n(t) dt`.

Uses `contDiff_parametric_hermiteCoeff` to commute derivatives with the integral,
then `schwartz_slice_y_le_seminorm` for the pointwise bound on each slice,
and integrates against `|ψ_n(t)| dt`. -/
private lemma schwartz_partial_hermiteCoeff_decay (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (n : ℕ) (k m : ℕ) :
    ∃ C : ℝ, ∀ y : EuclideanSpace ℝ (Fin (d + 1)),
      ‖y‖ ^ k * ‖iteratedFDeriv ℝ m
        (fun y' => hermiteCoeff1D n (schwartz_slice d f y')) y‖ ≤ C := by
  -- The proof uses:
  -- 1. contDiff_parametric_hermiteCoeff to commute iteratedFDeriv with the integral
  -- 2. The constant hermiteFunction n t factors out of iteratedFDeriv in y
  -- 3. schwartz_slice_y_le_seminorm gives ‖y‖^k * ‖D^m(f∘snoc·t)(y)‖ ≤ seminorm f
  -- 4. Integrate against |ψ_n(t)| dt (finite since ψ_n is Schwartz)
  exact ⟨f.seminorm ℝ k m * ∫ t, ‖hermiteFunction n t‖, fun y => by
    obtain ⟨_, h_comm⟩ := contDiff_parametric_hermiteCoeff d f n
    change ‖y‖ ^ k * ‖iteratedFDeriv ℝ m
      (fun y' => ∫ t, f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y‖ ≤ _
    rw [h_comm]
    -- Factor hermiteFunction n t out of iteratedFDeriv using const_smul
    have h_factor : ∀ t, iteratedFDeriv ℝ m
        (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y =
        hermiteFunction n t • iteratedFDeriv ℝ m (schwartz_slice_y d f t) y := by
      intro t
      have h_eq : (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) =
          (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') := by
        ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply, smul_eq_mul, mul_comm]
      rw [h_eq]
      exact iteratedFDeriv_const_smul_apply'
        (((schwartz_slice_y d f t).smooth'.of_le
          (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
    simp_rw [h_factor]
    -- Bound: ‖y‖^k * ‖∫ ψ(t) • D^m(slice)(y)‖ ≤ seminorm * ∫ ‖ψ‖
    calc ‖y‖ ^ k * ‖∫ t, hermiteFunction n t •
          iteratedFDeriv ℝ m (↑(schwartz_slice_y d f t)) y‖
        ≤ ‖y‖ ^ k * ∫ t, ‖hermiteFunction n t •
          iteratedFDeriv ℝ m (↑(schwartz_slice_y d f t)) y‖ := by
          gcongr; exact norm_integral_le_integral_norm _
      _ = ‖y‖ ^ k * ∫ t, ‖hermiteFunction n t‖ *
          ‖iteratedFDeriv ℝ m (↑(schwartz_slice_y d f t)) y‖ := by
          simp_rw [norm_smul]
      _ = ∫ t, ‖hermiteFunction n t‖ *
          (‖y‖ ^ k * ‖iteratedFDeriv ℝ m (↑(schwartz_slice_y d f t)) y‖) := by
          rw [← integral_const_mul]; congr 1; ext t; ring
      _ ≤ ∫ t, ‖hermiteFunction n t‖ * (f.seminorm ℝ k m) := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun t => mul_nonneg (norm_nonneg _)
              (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _)))
          · exact (hermiteCoeff_bound_integrable n (f.seminorm ℝ k m)).congr
              (Filter.Eventually.of_forall (fun t => by ring))
          · exact Filter.Eventually.of_forall (fun t =>
              mul_le_mul_of_nonneg_left
                (schwartz_slice_y_le_seminorm d f t k m y) (norm_nonneg _))
      _ = f.seminorm ℝ k m * ∫ t, ‖hermiteFunction n t‖ := by
          rw [← integral_const_mul]; congr 1; ext t; ring⟩

-- A2: Partial Hermite coefficient is Schwartz in remaining coordinates
/-- Integrate out the last coordinate of `f` against the `n`-th Hermite
function, giving a Schwartz function of the remaining `d + 1` coordinates. -/
noncomputable def schwartz_partial_hermiteCoeff (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (n : ℕ) :
    SchwartzMap (EuclideanSpace ℝ (Fin (d + 1))) ℝ where
  toFun y := hermiteCoeff1D n (schwartz_slice d f y)
  smooth' := schwartz_partial_hermiteCoeff_smooth d f n
  decay' := schwartz_partial_hermiteCoeff_decay d f n

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

/-- Fubini theorem for EuclideanSpace slicing.
Isolates the measure equivalence between ℝ^{d+2} and ℝ^{d+1} × ℝ. -/
lemma integral_euclidean_snoc (d : ℕ) (g : EuclideanSpace ℝ (Fin (d + 2)) → ℝ)
    (hg : Integrable g) :
    ∫ x, g x = ∫ y : EuclideanSpace ℝ (Fin (d + 1)), ∫ t : ℝ, g (euclideanSnoc (d + 1) y t) := by
  -- Step 1: Transfer from EuclideanSpace to Fin (d+2) → ℝ via volume-preserving equiv
  have hv := PiLp.volume_preserving_toLp (ι := Fin (d + 2))
  rw [← hv.integral_comp' (f := MeasurableEquiv.toLp 2 _)]
  -- Step 2: Split Fin (d+2) → ℝ into ℝ × (Fin (d+1) → ℝ) via piFinSuccAbove at Fin.last
  set e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 2) => ℝ) (Fin.last (d + 1))).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 2) => ℝ) (Fin.last (d + 1))).symm _
  rw [← hem.integral_comp' (f := e)]
  -- Step 3: Apply Fubini and swap integral order
  set F : ℝ × (Fin (d + 1) → ℝ) → ℝ :=
    fun p => g ((MeasurableEquiv.toLp 2 _) (e p))
  have hint : Integrable F :=
    (hem.integrable_comp_emb e.measurableEmbedding).mpr
      ((hv.integrable_comp_emb (MeasurableEquiv.toLp 2 _).measurableEmbedding).mpr hg)
  rw [volume_eq_prod] at hint ⊢
  rw [integral_prod _ hint, integral_integral_swap hint]
  -- Step 4: Transfer outer integral from Fin (d+1) → ℝ to EuclideanSpace
  have hv' := PiLp.volume_preserving_toLp (ι := Fin (d + 1))
  rw [← hv'.integral_comp' (f := MeasurableEquiv.toLp 2 _)]
  congr 1; funext y'
  congr 1; funext t
  -- Show the composed function equals g (euclideanSnoc ...)
  show F (t, y') = g (euclideanSnoc (d + 1) ((MeasurableEquiv.toLp 2 _) y') t)
  simp only [F, e, MeasurableEquiv.piFinSuccAbove_symm_apply, MeasurableEquiv.toLp,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_mk]
  congr 1
  ext i
  simp only [euclideanSnoc, WithLp.equiv_symm_apply]
  refine Fin.lastCases ?_ ?_ i
  · simp [Fin.snoc_last, Fin.insertNth_apply_same]
  · intro j; simp [Fin.snoc_castSucc, Fin.insertNth_apply_succAbove, Fin.succAbove_last]

end GaussianField
