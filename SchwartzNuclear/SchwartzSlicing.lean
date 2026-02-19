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
  (requires iterated differentiation under the integral sign, not yet in Mathlib)

- `schwartz_slice_partial.smooth'` / `decay'` — smoothness and Schwartz decay of the
  scalarized slice `t ↦ D^{l'}_y[f(·, t)](y)(v)` (follows from joint smoothness/decay of f)

- `schwartz_partial_hermiteCoeff_iteratedFDeriv` — the iterated derivative of
  `schwartz_partial_hermiteCoeff d f n` evaluated at `y` along `v` equals
  `hermiteCoeff1D n (schwartz_slice_partial d f l' y v)`

- `schwartz_slice_partial_seminorm_bound` — 1D Schwartz seminorm of the scalarized
  slice, weighted by `‖y‖^k'`, is bounded by `C * ∏‖vᵢ‖ * sup-seminorms(f)`

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

/-- The last coordinate contributes to the norm:
`|t| ≤ ‖euclideanSnoc (d+1) y t‖`. -/
private lemma euclideanSnoc_norm_ge_right (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    ‖t‖ ≤ ‖euclideanSnoc (d + 1) y t‖ := by
  rw [← Real.sqrt_sq (norm_nonneg t),
    ← Real.sqrt_sq (norm_nonneg (euclideanSnoc (d + 1) y t))]
  apply Real.sqrt_le_sqrt
  rw [euclideanSnoc_norm_sq, Real.norm_eq_abs, sq_abs]
  linarith [sq_nonneg ‖y‖]

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
/-- For fixed `y`, the function `t ↦ iteratedFDeriv ℝ m (y' ↦ f(snoc y' t) * ψ_n(t)) y`
is continuous. Uses the chain rule decomposition:
`iteratedFDeriv m (g t) y = ψ_n(t) • compCLML(iteratedFDeriv m f (snoc y t))`. -/
private lemma continuous_parametric_hermiteCoeff_iteratedFDeriv (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n m : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    Continuous (fun t => iteratedFDeriv ℝ m
      (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y) := by
  set L := euclideanSnoc_linearCLM d
  have h_eq : ∀ t, iteratedFDeriv ℝ m
      (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y = hermiteFunction n t •
      (ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin m => L))
        (iteratedFDeriv ℝ m (↑f) (euclideanSnoc (d + 1) y t)) := by
    intro t
    rw [show (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) =
        (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') from by
      ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply, smul_eq_mul, mul_comm],
      iteratedFDeriv_const_smul_apply'
        ((schwartz_slice_y d f t).smooth'.of_le
          (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
    congr 1
    set c := euclideanSnoc (d + 1) (0 : EuclideanSpace ℝ (Fin (d + 1))) t
    set f' : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun z => f (c + z)
    rw [show (schwartz_slice_y d f t : EuclideanSpace ℝ (Fin (d + 1)) → ℝ) = f' ∘ ⇑L from by
        ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply, f']
        congr 1; exact euclideanSnoc_decomp d y' t,
      L.iteratedFDeriv_comp_right (f.smooth'.comp (contDiff_const.add contDiff_id))
        y (WithTop.coe_le_coe.mpr le_top),
      iteratedFDeriv_comp_add_left m c (L y),
      show c + L y = euclideanSnoc (d + 1) y t from (euclideanSnoc_decomp d y t).symm]
    simp [ContinuousMultilinearMap.compContinuousLinearMapL_apply]
  exact (Continuous.smul
    ((schwartzHermiteBasis1D n).continuous.congr
      (fun t => (schwartzHermiteBasis1D_apply n t).symm))
    ((ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin m => L)).continuous.comp
      (f.smooth'.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top) |>.comp
        (euclideanSnoc_hasTemperateGrowth d y).smooth'.continuous))).congr
    (fun t => (h_eq t).symm)

private lemma contDiff_parametric_hermiteCoeff (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y => ∫ t, f (euclideanSnoc (d + 1) y t) * hermiteFunction n t) ∧
    ∀ (m : ℕ) (y : EuclideanSpace ℝ (Fin (d + 1))),
      iteratedFDeriv ℝ m
        (fun y' => ∫ t, f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y =
      ∫ t, iteratedFDeriv ℝ m
        (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y := by
  -- Abbreviation for the integrand parametrized by t
  set g : ℝ → EuclideanSpace ℝ (Fin (d + 1)) → ℝ :=
    fun t y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t with hg_def
  -- For each t, g t is smooth (it's ψ(t) • schwartz_slice_y)
  have h_smooth : ∀ t, ContDiff ℝ ⊤ (g t) := by
    intro t
    show ContDiff ℝ ⊤ (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t)
    have h_eq : (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) =
        (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') := by
      ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply, smul_eq_mul, mul_comm]
    rw [h_eq]; exact (schwartz_slice_y d f t).smooth'.const_smul _
  -- Uniform bound: ‖iteratedFDeriv m (g t) y‖ ≤ ‖ψ(t)‖ * seminorm 0 m f
  have h_bound : ∀ (m : ℕ) (t : ℝ) (y : EuclideanSpace ℝ (Fin (d + 1))),
      ‖iteratedFDeriv ℝ m (g t) y‖ ≤ ‖hermiteFunction n t‖ * f.seminorm ℝ 0 m := by
    intro m t y
    show ‖iteratedFDeriv ℝ m
      (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y‖ ≤ _
    rw [show (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) =
        (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') from by
      ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply, smul_eq_mul, mul_comm],
      iteratedFDeriv_const_smul_apply'
        ((schwartz_slice_y d f t).smooth'.of_le
          (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt),
      norm_smul]
    gcongr; simpa using schwartz_slice_y_le_seminorm d f t 0 m y
  -- Continuity of t ↦ iteratedFDeriv ℝ m (g t) y (for measurability)
  have h_cont_param : ∀ (m : ℕ) (y : EuclideanSpace ℝ (Fin (d + 1))),
      Continuous (fun t => iteratedFDeriv ℝ m (g t) y) :=
    fun m y => continuous_parametric_hermiteCoeff_iteratedFDeriv d f n m y
  -- Integrability at each level
  have h_int : ∀ (m : ℕ) (y : EuclideanSpace ℝ (Fin (d + 1))),
      Integrable (fun t => iteratedFDeriv ℝ m (g t) y) := by
    intro m y
    exact (hermiteCoeff_bound_integrable n (f.seminorm ℝ 0 m)).mono
      (h_cont_param m y).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => by
        calc ‖iteratedFDeriv ℝ m (g t) y‖
            ≤ ‖hermiteFunction n t‖ * f.seminorm ℝ 0 m := h_bound m t y
          _ = f.seminorm ℝ 0 m * ‖hermiteFunction n t‖ := mul_comm _ _
          _ ≤ ‖f.seminorm ℝ 0 m * ‖hermiteFunction n t‖‖ := le_abs_self _)
  -- Define the candidate FormalMultilinearSeries for HasFTaylorSeriesUpTo
  set p : EuclideanSpace ℝ (Fin (d + 1)) → FormalMultilinearSeries ℝ
      (EuclideanSpace ℝ (Fin (d + 1))) ℝ := fun x m =>
    ∫ t, iteratedFDeriv ℝ m (g t) x
  -- Show HasFTaylorSeriesUpTo
  have h_taylor : HasFTaylorSeriesUpTo (⊤ : ℕ∞)
      (fun y => ∫ t, g t y) p := by
    refine ⟨fun x => ?_, fun m _ x => ?_, fun m _ => ?_⟩
    · -- zero_eq: (p x 0).curry0 = ∫ t, g t x
      show (∫ t, iteratedFDeriv ℝ 0 (g t) x).curry0 = ∫ t, g t x
      rw [show ContinuousMultilinearMap.curry0
        (∫ t, iteratedFDeriv ℝ 0 (g t) x) =
        (∫ t, iteratedFDeriv ℝ 0 (g t) x) 0 from rfl,
        ContinuousMultilinearMap.integral_apply (h_int 0 x)]
      simp [iteratedFDeriv_zero_apply]
    · -- fderiv: HasFDerivAt (p · m) ((p x (m+1)).curryLeft) x
      show HasFDerivAt (fun y => ∫ t, iteratedFDeriv ℝ m (g t) y)
          ((∫ t, iteratedFDeriv ℝ (m + 1) (g t) x).curryLeft) x
      -- Step 1: Leibniz rule gives derivative = ∫ t, curryLeft(iteratedFDeriv (m+1) ...)
      -- since fderiv_iteratedFDeriv = rfl (definitional)
      set curry_iso := continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (m + 1) => EuclideanSpace ℝ (Fin (d + 1))) ℝ
      have h_leibniz : HasFDerivAt (fun y => ∫ t, iteratedFDeriv ℝ m (g t) y)
          (∫ t, (iteratedFDeriv ℝ (m + 1) (g t) x).curryLeft) x :=
        hasFDerivAt_integral_of_dominated_of_fderiv_le
          (F' := fun y t => (iteratedFDeriv ℝ (m + 1) (g t) y).curryLeft)
          (bound := fun t => f.seminorm ℝ 0 (m + 1) * ‖hermiteFunction n t‖)
          Filter.univ_mem
          (Filter.Eventually.of_forall fun y => (h_cont_param m y).aestronglyMeasurable)
          (h_int m x)
          ((curry_iso.continuous.comp (h_cont_param (m + 1) x)).aestronglyMeasurable)
          (Filter.Eventually.of_forall fun t y _ => by
            rw [ContinuousMultilinearMap.curryLeft_norm]
            calc ‖iteratedFDeriv ℝ (m + 1) (g t) y‖
                ≤ ‖hermiteFunction n t‖ * f.seminorm ℝ 0 (m + 1) := h_bound (m + 1) t y
              _ = f.seminorm ℝ 0 (m + 1) * ‖hermiteFunction n t‖ := mul_comm _ _)
          (hermiteCoeff_bound_integrable n (f.seminorm ℝ 0 (m + 1)))
          (Filter.Eventually.of_forall fun t y _ =>
            ((h_smooth t).iteratedFDeriv_right (show (↑m + ⊤ : ℕ∞) ≤ ⊤ from le_top)
            ).differentiable le_top |>.differentiableAt.hasFDerivAt)
      -- Step 2: Convert ∫ curryLeft(f) to curryLeft(∫ f) via linear equiv
      rwa [curry_iso.toContinuousLinearEquiv.integral_comp_comm
        (fun t => iteratedFDeriv ℝ (m + 1) (g t) x)] at h_leibniz
    · -- cont: Continuous (p · m)
      show Continuous (fun x => ∫ t, iteratedFDeriv ℝ m (g t) x)
      exact continuous_of_dominated
        (fun y => (h_int m y).aestronglyMeasurable)
        (fun y => Filter.Eventually.of_forall fun t => h_bound m t y)
        (hermiteCoeff_bound_integrable n (f.seminorm ℝ 0 m))
        (Filter.Eventually.of_forall fun t =>
          (h_smooth t).continuous_iteratedFDeriv
            (WithTop.coe_le_coe.mpr le_top))
  -- Conclude: ContDiff from HasFTaylorSeriesUpTo, formula from eq_iteratedFDeriv
  exact ⟨h_taylor.contDiff, fun m y => (h_taylor.eq_iteratedFDeriv le_top y).symm⟩

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

/-! ### Scalarization helpers for seminorm control

These helpers reduce the multi-dimensional seminorm control problem to 1D
by evaluating the multilinear map `D^{l'}_y[g_n]` along arbitrary vectors `v`,
reducing to a 1D problem solvable by `hermiteCoeff1D_decay`. -/

/-- Chain rule: the `l'`-th derivative in `y` of `f(euclideanSnoc y t)` evaluated at vectors
`v` equals the `l'`-th derivative of `f` at `euclideanSnoc y t` evaluated at `L(v_i)` where
`L = euclideanSnoc_linearCLM d`. -/
private lemma schwartz_slice_partial_chain_rule (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (l' : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1)))
    (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))) (t : ℝ) :
    iteratedFDeriv ℝ l' (fun y' => f (euclideanSnoc (d + 1) y' t)) y v =
      (iteratedFDeriv ℝ l' (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t))
        (fun i => euclideanSnoc_linearCLM d (v i)) := by
  set c := euclideanSnoc (d + 1) (0 : EuclideanSpace ℝ (Fin (d + 1))) t
  set L := euclideanSnoc_linearCLM d
  set f' : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun z => f (c + z)
  have hf'_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) f' :=
    f.smooth'.comp (contDiff_const.add contDiff_id)
  have h_fun_eq : (fun y' => f (euclideanSnoc (d + 1) y' t)) = f' ∘ ⇑L := by
    ext y'
    simp only [Function.comp_apply, f']
    congr 1
    exact euclideanSnoc_decomp d y' t
  rw [h_fun_eq]
  rw [L.iteratedFDeriv_comp_right hf'_smooth y (WithTop.coe_le_coe.mpr le_top)]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  ext u
  rw [iteratedFDeriv_comp_add_left]
  congr 1
  exact (euclideanSnoc_decomp d y t).symm

/-- The map `t ↦ euclideanSnoc y t` is smooth (affine in `t`). -/
private lemma euclideanSnoc_t_contDiff (d : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1))) :
    ContDiff ℝ ∞ (fun t : ℝ => euclideanSnoc (d + 1) y t) := by
  rw [show (fun t : ℝ => euclideanSnoc (d + 1) y t) =
    (WithLp.equiv 2 (Fin (d + 2) → ℝ)).symm ∘ (fun t => Fin.snoc (fun i => y i) t) from rfl]
  exact (WithLp.equiv 2 _).symm.toContinuousLinearEquiv.contDiff.comp
    (contDiff_pi.mpr (fun i => by
      refine Fin.lastCases ?_ ?_ i
      · simp [Fin.snoc_last]; exact contDiff_id
      · intro j; simp [Fin.snoc_castSucc]; exact contDiff_const))

/-- Norm equality: `‖iteratedFDeriv n (iteratedFDeriv l' f) z‖ = ‖iteratedFDeriv (n + l') f z‖`.
Uses the currying isometries that relate successive iterated derivatives. -/
private lemma norm_iteratedFDeriv_iteratedFDeriv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (n l' : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ n (iteratedFDeriv ℝ l' f) z‖ =
      ‖iteratedFDeriv ℝ (n + l') f z‖ := by
  induction l' generalizing f n with
  | zero =>
    simp [iteratedFDeriv_zero_eq_comp]
    rw [show n + 0 = n from (Nat.add_zero n)]
    -- iteratedFDeriv 0 f = continuousMultilinearCurryFin0.symm ∘ f
    -- The currying equiv is an isometry, so norm is preserved
    rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
  | succ l' ih =>
    rw [show n + (l' + 1) = (n + l') + 1 from by omega]
    rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ)]
    rw [show iteratedFDeriv ℝ (l' + 1) f =
      ((continuousMultilinearCurryRightEquiv' ℝ l'
          E F).symm ∘ iteratedFDeriv ℝ l' (fderiv ℝ f)) from by
      ext x; exact iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ)]
    rw [LinearIsometryEquiv.norm_iteratedFDeriv_comp_left]
    exact ih (fderiv ℝ f) n z

/-- The 1D Schwartz function obtained by evaluating the `l'`-th iterated Fréchet derivative
of a slice along vectors `v`. Used for the "scalarization" step: reduce the operator norm
of `D^{l'} g_n(y)` to pointwise evaluations that can be bounded via 1D Hermite decay. -/
private noncomputable def schwartz_slice_partial (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (l' : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1)))
    (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))) :
    SchwartzMap ℝ ℝ where
  toFun t := iteratedFDeriv ℝ l' (fun y' => f (euclideanSnoc (d + 1) y' t)) y v
  smooth' := by
    -- By chain rule, toFun t = (iteratedFDeriv l' f (euclideanSnoc y t)) w
    -- where w = fun i => L(v_i). This is a composition of smooth functions.
    set L := euclideanSnoc_linearCLM d
    set w : Fin l' → EuclideanSpace ℝ (Fin (d + 2)) := fun i => L (v i)
    suffices h : ContDiff ℝ ∞
        (fun t => (iteratedFDeriv ℝ l' (↑f : _ → ℝ)
          (euclideanSnoc (d + 1) y t)) w) by
      exact h.congr (fun t => (schwartz_slice_partial_chain_rule d f l' y v t).symm)
    -- Decompose: (apply w) ∘ (iteratedFDeriv l' f) ∘ (euclideanSnoc y ·)
    exact (ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ w).contDiff.comp
      ((f.smooth'.iteratedFDeriv_right le_top).comp (euclideanSnoc_t_contDiff d y))
  decay' := by
    -- By chain rule, toFun t = G(euclideanSnoc y t) where
    -- G z = (iteratedFDeriv l' f z) w. We bound the derivatives of G and
    -- use |t| ≤ ‖euclideanSnoc y t‖ to transfer the polynomial weight.
    intro k n
    set L := euclideanSnoc_linearCLM d
    set w : Fin l' → EuclideanSpace ℝ (Fin (d + 2)) := fun i => L (v i)
    set G : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun z =>
      (iteratedFDeriv ℝ l' (↑f : _ → ℝ) z) w
    -- The t-direction CLM: the linear part of euclideanSnoc y
    set L_t : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
      (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.single (R := ℝ) (φ := fun (_ : Fin (d + 2)) => ℝ)
          (Fin.last (d + 1)))
    -- Bound: ‖iteratedFDeriv n G z‖ ≤ ‖apply w‖ * ‖iteratedFDeriv (n+l') f z‖
    have h_G_bound : ∀ z, ‖iteratedFDeriv ℝ n G z‖ ≤
        ‖ContinuousMultilinearMap.apply ℝ
          (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ w‖ *
          ‖iteratedFDeriv ℝ (n + l') (↑f : _ → ℝ) z‖ := by
      intro z
      calc ‖iteratedFDeriv ℝ n G z‖
          ≤ ‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖ *
            ‖iteratedFDeriv ℝ n (iteratedFDeriv ℝ l' (↑f : _ → ℝ)) z‖ := by
            exact ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ _
              ((f.smooth'.iteratedFDeriv_right le_top).contDiffAt) le_top
        _ = ‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖ *
            ‖iteratedFDeriv ℝ (n + l') (↑f : _ → ℝ) z‖ := by
            rw [norm_iteratedFDeriv_iteratedFDeriv]
    -- The toFun equals G ∘ (euclideanSnoc y ·) by the chain rule
    have h_eq : (fun t => iteratedFDeriv ℝ l'
        (fun y' => f (euclideanSnoc (d + 1) y' t)) y v) =
        fun t => G (euclideanSnoc (d + 1) y t) := by
      ext t; exact schwartz_slice_partial_chain_rule d f l' y v t
    -- Bound the n-th derivative of toFun = G ∘ (c₀ + L_t ·)
    -- decomposing via iteratedFDeriv_comp_add_left and iteratedFDeriv_comp_right
    set c₀ := euclideanSnoc (d + 1) y 0
    have h_snoc_eq : (fun t => euclideanSnoc (d + 1) y t) = (fun t => c₀ + L_t t) := by
      ext t
      simp only [c₀, L_t, euclideanSnoc, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.single_apply, ContinuousLinearEquiv.coe_coe]
      show (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) t) =
        (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) 0) +
        (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm (Pi.single (Fin.last (d + 1)) t)
      have : ∀ s, Fin.snoc (fun i => y.ofLp i) s =
          Fin.snoc (fun i => y.ofLp i) 0 + Pi.single (Fin.last (d + 1)) s := by
        intro s; ext i; rw [Pi.add_apply]
        refine Fin.lastCases ?_ ?_ i
        · simp [Fin.snoc_last]
        · intro j; simp [Fin.snoc_castSucc]
      rw [this t]; simp [EuclideanSpace.equiv]
    -- L_t has norm ≤ 1 (isometric embedding of last coordinate)
    have h_Lt_norm : ‖L_t‖ ≤ 1 := by
      apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      intro t
      rw [one_mul]
      show ‖(EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm
        (Pi.single (Fin.last (d + 1)) t)‖ ≤ ‖t‖
      rw [EuclideanSpace.norm_eq]
      simp only [EuclideanSpace.equiv_symm_apply]
      rw [show ∑ i, ‖Pi.single (Fin.last (d + 1)) t i‖ ^ 2 = ‖t‖ ^ 2 from by
        conv_lhs => arg 2; ext i
        by_cases hi : i = Fin.last (d + 1) <;> simp [hi, Pi.single_apply]]
      exact le_of_eq (Real.sqrt_sq (norm_nonneg t))
    -- G is smooth
    have h_G_smooth : ContDiff ℝ ∞ G :=
      (ContinuousMultilinearMap.apply ℝ _ ℝ w).contDiff.comp
        (f.smooth'.iteratedFDeriv_right le_top)
    -- Bound iteratedFDeriv n of the composition using chain rule
    have h_deriv_bound : ∀ t,
        ‖iteratedFDeriv ℝ n (fun t => G (euclideanSnoc (d + 1) y t)) t‖ ≤
          ‖iteratedFDeriv ℝ n G (euclideanSnoc (d + 1) y t)‖ := by
      intro t
      -- Rewrite using the affine decomposition
      have h_comp_eq : (fun t => G (euclideanSnoc (d + 1) y t)) = (fun t => G (c₀ + L_t t)) := by
        rw [h_snoc_eq]
      rw [h_comp_eq]
      set G' := fun z => G (c₀ + z)
      have hG'_smooth : ContDiff ℝ ∞ G' :=
        h_G_smooth.comp (contDiff_const.add contDiff_id)
      have h_chain := L_t.iteratedFDeriv_comp_right hG'_smooth t
        (WithTop.coe_le_coe.mpr le_top : (n : ℕ∞) ≤ ⊤)
      have h_trans : iteratedFDeriv ℝ n G' (L_t t) = iteratedFDeriv ℝ n G (c₀ + L_t t) := by
        rw [show G' = fun z => G (c₀ + z) from rfl]
        rw [iteratedFDeriv_comp_add_left]
      rw [show (fun t => G (c₀ + L_t t)) = G' ∘ ⇑L_t from rfl, h_chain]
      calc ‖(iteratedFDeriv ℝ n G' (L_t t)).compContinuousLinearMap fun _ => L_t‖
          ≤ ‖iteratedFDeriv ℝ n G' (L_t t)‖ * ∏ _ : Fin n, ‖L_t‖ :=
            ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
        _ ≤ ‖iteratedFDeriv ℝ n G' (L_t t)‖ * 1 := by
            gcongr
            calc ∏ _ : Fin n, ‖L_t‖ ≤ ∏ _ : Fin n, (1 : ℝ) :=
                  Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => h_Lt_norm)
              _ = 1 := by simp
        _ = ‖iteratedFDeriv ℝ n G (c₀ + L_t t)‖ := by rw [mul_one, h_trans]
    -- Combine everything
    refine ⟨‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖ * f.seminorm ℝ k (n + l'), fun t => ?_⟩
    rw [h_eq]
    calc ‖t‖ ^ k * ‖iteratedFDeriv ℝ n (fun t => G (euclideanSnoc (d + 1) y t)) t‖
        ≤ ‖t‖ ^ k * ‖iteratedFDeriv ℝ n G (euclideanSnoc (d + 1) y t)‖ := by
          gcongr; exact h_deriv_bound t
      _ ≤ ‖t‖ ^ k * (‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖ *
            ‖iteratedFDeriv ℝ (n + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖) := by
          gcongr; exact h_G_bound _
      _ = ‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖ *
            (‖t‖ ^ k * ‖iteratedFDeriv ℝ (n + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖) :=
          by ring
      _ ≤ ‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖ *
            (‖euclideanSnoc (d + 1) y t‖ ^ k *
              ‖iteratedFDeriv ℝ (n + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖) := by
          gcongr
          · exact norm_nonneg _
          · exact pow_le_pow_left (norm_nonneg _) (euclideanSnoc_norm_ge_right d y t) k
      _ ≤ ‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖ * f.seminorm ℝ k (n + l') := by
          gcongr; exact SchwartzMap.le_seminorm ℝ k (n + l') f _

/-- The iterated Fréchet derivative of `schwartz_partial_hermiteCoeff d f n` evaluated
at `y` along vectors `v` equals the 1D Hermite coefficient of the corresponding
slice partial function. This is the key "commutation" lemma that connects the
multi-d seminorm to a 1D quantity. -/
private lemma schwartz_partial_hermiteCoeff_iteratedFDeriv (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (n l' : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1)))
    (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))) :
    iteratedFDeriv ℝ l' (schwartz_partial_hermiteCoeff d f n) y v =
      hermiteCoeff1D n (schwartz_slice_partial d f l' y v) := by
  -- Step 1: Commute iteratedFDeriv with the integral using contDiff_parametric_hermiteCoeff
  obtain ⟨_, h_comm⟩ := contDiff_parametric_hermiteCoeff d f n
  change (iteratedFDeriv ℝ l'
    (fun y' => ∫ t, f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y) v = _
  rw [h_comm]
  -- Step 2: Evaluate the ContinuousMultilinearMap integral at v
  have h_int : Integrable (fun t => iteratedFDeriv ℝ l'
      (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y) := by
    exact (hermiteCoeff_bound_integrable n (f.seminorm ℝ 0 l')).mono
      ((continuous_parametric_hermiteCoeff_iteratedFDeriv d f n l' y).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t => by
        rw [show (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) =
            (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') from by
          ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply, smul_eq_mul, mul_comm],
          iteratedFDeriv_const_smul_apply'
            ((schwartz_slice_y d f t).smooth'.of_le
              (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt), norm_smul]
        calc ‖hermiteFunction n t‖ * ‖iteratedFDeriv ℝ l' (↑(schwartz_slice_y d f t)) y‖
            ≤ ‖hermiteFunction n t‖ * f.seminorm ℝ 0 l' := by
              gcongr; simpa using schwartz_slice_y_le_seminorm d f t 0 l' y
          _ = f.seminorm ℝ 0 l' * ‖hermiteFunction n t‖ := mul_comm _ _
          _ ≤ ‖f.seminorm ℝ 0 l' * ‖hermiteFunction n t‖‖ := le_abs_self _)
  rw [ContinuousMultilinearMap.integral_apply h_int]
  -- Step 3: Factor hermiteFunction n t out of iteratedFDeriv (same as decay proof)
  have h_factor : ∀ t, (iteratedFDeriv ℝ l'
      (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) y) v =
      (iteratedFDeriv ℝ l' (↑(schwartz_slice_y d f t)) y) v * hermiteFunction n t := by
    intro t
    rw [show (fun y' => f (euclideanSnoc (d + 1) y' t) * hermiteFunction n t) =
        (fun y' => hermiteFunction n t • (schwartz_slice_y d f t) y') from by
      ext y'; simp [schwartz_slice_y, compCLMOfAntilipschitz_apply, smul_eq_mul, mul_comm],
      iteratedFDeriv_const_smul_apply'
        ((schwartz_slice_y d f t).smooth'.of_le
          (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
    simp [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  simp_rw [h_factor]
  -- Step 4: Recognize as hermiteCoeff1D
  -- hermiteCoeff1D n g = ∫ g(t) * hermiteFunction n t dt
  -- schwartz_slice_partial toFun t = iteratedFDeriv l' (fun y' => f(snoc y' t)) y v
  -- and schwartz_slice_y d f t y' = f(snoc y' t), so the integrands match
  show ∫ t, (iteratedFDeriv ℝ l' (↑(schwartz_slice_y d f t)) y) v * hermiteFunction n t =
    ∫ t, (schwartz_slice_partial d f l' y v) t * hermiteFunction n t
  congr 1; ext t; congr 1
  show (iteratedFDeriv ℝ l' (↑(schwartz_slice_y d f t)) y) v =
    iteratedFDeriv ℝ l' (fun y' => f (euclideanSnoc (d + 1) y' t)) y v
  congr 1; ext1 y'
  simp [schwartz_slice_y, compCLMOfAntilipschitz_apply]

/-- Pointwise bound for the scalarized slice: for each `t`,
`‖y‖^k * ‖t‖^a * ‖D^b_t[slice_partial](t)‖ ≤ ‖apply w‖ * f.seminorm (k+a) (b+l')`.
Combines the chain rule, CLM norm bounds, and Schwartz decay. -/
private lemma schwartz_slice_partial_pointwise_bound (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ) (l' : ℕ)
    (y : EuclideanSpace ℝ (Fin (d + 1)))
    (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))) (k a b : ℕ) (t : ℝ) :
    ‖y‖ ^ k * (‖t‖ ^ a * ‖iteratedFDeriv ℝ b
      (↑(schwartz_slice_partial d f l' y v)) t‖) ≤
      ‖ContinuousMultilinearMap.apply ℝ
        (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ
        (fun i => euclideanSnoc_linearCLM d (v i))‖ *
      f.seminorm ℝ (k + a) (b + l') := by
  set L := euclideanSnoc_linearCLM d
  set w : Fin l' → EuclideanSpace ℝ (Fin (d + 2)) := fun i => L (v i)
  set g := schwartz_slice_partial d f l' y v
  set G : EuclideanSpace ℝ (Fin (d + 2)) → ℝ := fun z =>
    (iteratedFDeriv ℝ l' (↑f : _ → ℝ) z) w
  -- Step 1: Chain rule bound on b-th t-derivative
  set L_t : ℝ →L[ℝ] EuclideanSpace ℝ (Fin (d + 2)) :=
    (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.single (R := ℝ) (φ := fun (_ : Fin (d + 2)) => ℝ)
        (Fin.last (d + 1)))
  set c₀ := euclideanSnoc (d + 1) y 0
  have h_snoc_eq : (fun t => euclideanSnoc (d + 1) y t) = (fun t => c₀ + L_t t) := by
    ext t
    simp only [c₀, L_t, euclideanSnoc, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.single_apply, ContinuousLinearEquiv.coe_coe]
    show (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) t) =
      (WithLp.equiv 2 _).symm (Fin.snoc (fun i => y.ofLp i) 0) +
      (EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm (Pi.single (Fin.last (d + 1)) t)
    have : ∀ s, Fin.snoc (fun i => y.ofLp i) s =
        Fin.snoc (fun i => y.ofLp i) 0 + Pi.single (Fin.last (d + 1)) s := by
      intro s; ext i; rw [Pi.add_apply]
      refine Fin.lastCases ?_ ?_ i
      · simp [Fin.snoc_last]
      · intro j; simp [Fin.snoc_castSucc]
    rw [this t]; simp [EuclideanSpace.equiv]
  have h_Lt_norm : ‖L_t‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro t; rw [one_mul]
    show ‖(EuclideanSpace.equiv (Fin (d + 2)) ℝ).symm
      (Pi.single (Fin.last (d + 1)) t)‖ ≤ ‖t‖
    rw [EuclideanSpace.norm_eq]; simp only [EuclideanSpace.equiv_symm_apply]
    rw [show ∑ i, ‖Pi.single (Fin.last (d + 1)) t i‖ ^ 2 = ‖t‖ ^ 2 from by
      conv_lhs => arg 2; ext i
      by_cases hi : i = Fin.last (d + 1) <;> simp [hi, Pi.single_apply]]
    exact le_of_eq (Real.sqrt_sq (norm_nonneg t))
  have h_G_smooth : ContDiff ℝ ∞ G :=
    (ContinuousMultilinearMap.apply ℝ _ ℝ w).contDiff.comp
      (f.smooth'.iteratedFDeriv_right le_top)
  -- Bound: ‖D^b_t[g](t)‖ ≤ ‖D^b G(euclideanSnoc y t)‖
  have h_deriv : ‖iteratedFDeriv ℝ b (↑g) t‖ ≤
      ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ := by
    have h_eq : (↑g : ℝ → ℝ) = (fun t => G (euclideanSnoc (d + 1) y t)) := by
      ext s; exact schwartz_slice_partial_chain_rule d f l' y v s
    rw [h_eq, h_snoc_eq]
    set G' := fun z => G (c₀ + z)
    have hG'_smooth : ContDiff ℝ ∞ G' := h_G_smooth.comp (contDiff_const.add contDiff_id)
    rw [show (fun t => G (c₀ + L_t t)) = G' ∘ ⇑L_t from rfl,
        L_t.iteratedFDeriv_comp_right hG'_smooth t (WithTop.coe_le_coe.mpr le_top)]
    calc ‖(iteratedFDeriv ℝ b G' (L_t t)).compContinuousLinearMap fun _ => L_t‖
        ≤ ‖iteratedFDeriv ℝ b G' (L_t t)‖ * ∏ _ : Fin b, ‖L_t‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ ≤ ‖iteratedFDeriv ℝ b G' (L_t t)‖ * 1 := by
          gcongr; calc ∏ _ : Fin b, ‖L_t‖ ≤ ∏ _ : Fin b, (1 : ℝ) :=
                Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => h_Lt_norm)
            _ = 1 := by simp
      _ = ‖iteratedFDeriv ℝ b G (c₀ + L_t t)‖ := by
          rw [mul_one]; congr 1; exact iteratedFDeriv_comp_add_left b c₀ (L_t t)
  -- Step 2: ‖D^b G z‖ ≤ ‖apply w‖ * ‖D^(b+l') f z‖
  have h_G_bound : ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖ ≤
      ‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖ *
        ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖ := by
    calc ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖
        ≤ ‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖ *
          ‖iteratedFDeriv ℝ b (iteratedFDeriv ℝ l' (↑f : _ → ℝ))
            (euclideanSnoc (d + 1) y t)‖ :=
          ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ _
            ((f.smooth'.iteratedFDeriv_right le_top).contDiffAt) le_top
      _ = _ := by rw [norm_iteratedFDeriv_iteratedFDeriv]
  -- Step 3: Combine with polynomial weights
  set C_w := ‖ContinuousMultilinearMap.apply ℝ
    (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ w‖
  calc ‖y‖ ^ k * (‖t‖ ^ a * ‖iteratedFDeriv ℝ b (↑g) t‖)
      ≤ ‖y‖ ^ k * (‖t‖ ^ a * ‖iteratedFDeriv ℝ b G (euclideanSnoc (d + 1) y t)‖) := by
        gcongr
    _ ≤ ‖y‖ ^ k * (‖t‖ ^ a * (C_w *
          ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖)) := by
        gcongr
    _ = C_w * (‖y‖ ^ k * ‖t‖ ^ a *
          ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖) := by ring
    _ ≤ C_w * (‖euclideanSnoc (d + 1) y t‖ ^ (k + a) *
          ‖iteratedFDeriv ℝ (b + l') (↑f : _ → ℝ) (euclideanSnoc (d + 1) y t)‖) := by
        gcongr
        calc ‖y‖ ^ k * ‖t‖ ^ a
            ≤ ‖euclideanSnoc (d + 1) y t‖ ^ k * ‖euclideanSnoc (d + 1) y t‖ ^ a := by
              gcongr
              · exact euclideanSnoc_norm_ge_left d y t
              · exact euclideanSnoc_norm_ge_right d y t
          _ = ‖euclideanSnoc (d + 1) y t‖ ^ (k + a) := (pow_add _ k a).symm
    _ ≤ C_w * f.seminorm ℝ (k + a) (b + l') := by
        gcongr; exact SchwartzMap.le_seminorm ℝ (k + a) (b + l') f _

/-- Seminorm bound for the slice partial function: the 1D Schwartz seminorm of
`schwartz_slice_partial d f l' y v`, weighted by `‖y‖^k'`, is bounded by a product
of `∏ ‖v_i‖` and finitely many higher-dimensional seminorms of `f`. -/
private lemma schwartz_slice_partial_seminorm_bound (d : ℕ) (k' l' a b : ℕ) :
    ∃ (C : ℝ) (q' : Finset (ℕ × ℕ)), 0 < C ∧
      ∀ (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
        (y : EuclideanSpace ℝ (Fin (d + 1)))
        (v : Fin l' → EuclideanSpace ℝ (Fin (d + 1))),
        ‖y‖ ^ k' * schwartzSeminormFamily ℝ ℝ ℝ (a, b)
          (schwartz_slice_partial d f l' y v) ≤
          C * (∏ i, ‖v i‖) *
            q'.sup (schwartzSeminormFamily ℝ (EuclideanSpace ℝ (Fin (d + 2))) ℝ) f
    := by
  refine ⟨1, {(k' + a, b + l')}, one_pos, fun f y v => ?_⟩
  simp only [Finset.sup_singleton, one_mul]
  set g := schwartz_slice_partial d f l' y v
  set L := euclideanSnoc_linearCLM d
  set w : Fin l' → EuclideanSpace ℝ (Fin (d + 2)) := fun i => L (v i)
  -- The apply norm is bounded by ∏ ‖w_i‖ ≤ ∏ ‖v_i‖
  have h_apply_le : ‖ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin l' => EuclideanSpace ℝ (Fin (d + 2))) ℝ w‖ ≤ ∏ i : Fin l', ‖v i‖ := by
    calc ‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖
        ≤ ∏ i, ‖w i‖ := by
          apply ContinuousLinearMap.opNorm_le_bound
          · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
          · intro A
            calc ‖A w‖ ≤ ‖A‖ * ∏ i, ‖w i‖ := A.le_opNorm w
              _ = (∏ i, ‖w i‖) * ‖A‖ := mul_comm _ _
      _ ≤ ∏ i, ‖v i‖ := by
          apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          intro i _
          calc ‖w i‖ = ‖L (v i)‖ := rfl
            _ ≤ ‖L‖ * ‖v i‖ := ContinuousLinearMap.le_opNorm L (v i)
            _ ≤ 1 * ‖v i‖ := by gcongr; exact euclideanSnoc_linearCLM_norm_le d
            _ = ‖v i‖ := one_mul _
  -- From pointwise bound to seminorm bound
  by_cases hy : ‖y‖ ^ k' = 0
  · simp [hy]
  · have hy_pos : 0 < ‖y‖ ^ k' := lt_of_le_of_ne (pow_nonneg (norm_nonneg _) _) (Ne.symm hy)
    have h_sem : SchwartzMap.seminorm ℝ a b g ≤
        ((∏ i : Fin l', ‖v i‖) * f.seminorm ℝ (k' + a) (b + l')) / ‖y‖ ^ k' := by
      apply SchwartzMap.seminorm_le_bound ℝ a b g (by positivity)
      intro t
      rw [le_div_iff hy_pos]
      calc ‖t‖ ^ a * ‖iteratedFDeriv ℝ b (↑g) t‖ * ‖y‖ ^ k'
          = ‖y‖ ^ k' * (‖t‖ ^ a * ‖iteratedFDeriv ℝ b (↑g) t‖) := by ring
        _ ≤ ‖ContinuousMultilinearMap.apply ℝ _ ℝ w‖ * f.seminorm ℝ (k' + a) (b + l') :=
            schwartz_slice_partial_pointwise_bound d f l' y v k' a b t
        _ ≤ (∏ i : Fin l', ‖v i‖) * f.seminorm ℝ (k' + a) (b + l') := by
            gcongr
    calc ‖y‖ ^ k' * SchwartzMap.seminorm ℝ a b g
        ≤ ‖y‖ ^ k' * (((∏ i, ‖v i‖) * f.seminorm ℝ (k' + a) (b + l')) / ‖y‖ ^ k') :=
          mul_le_mul_of_nonneg_left h_sem (le_of_lt hy_pos)
      _ = (∏ i, ‖v i‖) * f.seminorm ℝ (k' + a) (b + l') :=
          mul_div_cancel₀ _ (ne_of_gt hy_pos)

end GaussianField
