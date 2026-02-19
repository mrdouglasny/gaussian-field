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

- `schwartz_partial_hermiteCoeff_smooth` — `ContDiff ℝ ⊤` for `y ↦ ∫ f(y,t) ψ_n(t) dt`
- `schwartz_partial_hermiteCoeff_decay` — Schwartz decay of the partial coefficient

These require iterated differentiation under the integral sign, not yet
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

/-- Smoothness of the partial Hermite coefficient: the function
`y ↦ ∫ f(y,t) ψ_n(t) dt` is `C^∞` in `y`.

Proof by induction on the order of differentiability, using
`hasFDerivAt_integral_of_dominated_of_fderiv_le` at each step, with
domination from Schwartz decay. -/
private lemma schwartz_partial_hermiteCoeff_smooth (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => hermiteCoeff1D n (schwartz_slice d f y)) := by
  sorry

/-- Schwartz decay of the partial Hermite coefficient: for all `k, m`,
`sup_y ‖y‖^k · ‖∂^m_y g(y)‖ < ∞` where `g(y) = ∫ f(y,t) ψ_n(t) dt`.

Uses `euclideanSnoc_norm_ge_left` to push `‖y‖^k` inside the integral
and bound it by `‖(y,t)‖^k`, then applies Schwartz decay of `f`. -/
private lemma schwartz_partial_hermiteCoeff_decay (d : ℕ)
    (f : SchwartzMap (EuclideanSpace ℝ (Fin (d + 2))) ℝ)
    (n : ℕ) (k m : ℕ) :
    ∃ C : ℝ, ∀ y : EuclideanSpace ℝ (Fin (d + 1)),
      ‖y‖ ^ k * ‖iteratedFDeriv ℝ m
        (fun y' => hermiteCoeff1D n (schwartz_slice d f y')) y‖ ≤ C := by
  sorry

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
