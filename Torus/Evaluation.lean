/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Evaluation on Nuclear Tensor Products and Torus Test Functions

Specializes the `NuclearTensorProduct.evalCLM` to the torus test function
space `TorusTestFunction L`, providing point evaluation at lattice sites
and the lattice-to-torus embedding map.

## Main definitions

- `evalTorusAtSite` — evaluation of a torus test function at a lattice site
- `torusEmbedCLM` — embedding of lattice fields into Configuration(TorusTestFunction L)

## Mathematical background

For the torus, we evaluate `f ∈ TorusTestFunction L = C∞(S¹_L) ⊗̂ C∞(S¹_L)`
at a lattice site `x ∈ (ℤ/Nℤ)²` by applying `evalCLM` with the point
evaluation functionals from `circleRestriction`:

  `eval_x(f) = (r_N(·)(x 0) ⊗ r_N(·)(x 1))(f)`

where `r_N` is the circle restriction map (sampling with √(L/N) normalization).

## References

- Gel'fand-Vilenkin, *Generalized Functions* Vol. 4
- Treves, *Topological Vector Spaces, Distributions, and Kernels* §43
-/

import Torus.Restriction
import Torus.Symmetry
import Lattice.FiniteField
import Nuclear.TensorProductFunctorAxioms
import HeatKernel.GreenInvariance

noncomputable section

namespace GaussianField

open NuclearTensorProduct

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Torus test function evaluation -/

/-- Evaluation of a torus test function at a lattice site `x ∈ (ℤ/Nℤ)²`.

For `f ∈ TorusTestFunction L = C∞(S¹_L) ⊗̂ C∞(S¹_L)`, the evaluation at
site `x = (x₀, x₁)` is:

  `eval_x(f) = (r_N(·)(x₀) ⊗ r_N(·)(x₁))(f)`

where `r_N` is `circleRestriction L N`. For a pure tensor `f₁ ⊗ f₂`:
  `eval_x(f₁ ⊗ f₂) = r_N(f₁)(x₀) · r_N(f₂)(x₁)`
                     = `√(L/N) · f₁(x₀·L/N) · √(L/N) · f₂(x₁·L/N)`
                     = `(L/N) · f₁(x₀·L/N) · f₂(x₁·L/N)` -/
def evalTorusAtSite (N : ℕ) [NeZero N]
    (x : FinLatticeSites 2 N) : TorusTestFunction L →L[ℝ] ℝ :=
  let proj₀ : (ZMod N → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (x 0)
  let proj₁ : (ZMod N → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (x 1)
  NuclearTensorProduct.evalCLM
    (proj₀.comp (circleRestriction L N))
    (proj₁.comp (circleRestriction L N))

/-- The torus embedding: maps a lattice field `φ : (ℤ/Nℤ)² → ℝ` to a
continuous linear functional on `TorusTestFunction L`.

  `(ι_N φ)(f) = Σ_{x ∈ (ℤ/Nℤ)²} φ(x) · eval_x(f)` -/
def torusEmbedCLM (N : ℕ) [NeZero N]
    (φ : FinLatticeField 2 N) : Configuration (TorusTestFunction L) where
  toFun f := ∑ x : FinLatticeSites 2 N, φ x * evalTorusAtSite L N x f
  map_add' f g := by
    simp only [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [map_smul, smul_eq_mul, mul_left_comm, Finset.mul_sum, RingHom.id_apply]
  cont := by
    apply continuous_finset_sum
    intro x _
    exact continuous_const.mul (evalTorusAtSite L N x).cont

/-- The torus embedding agrees with evalTorusAtSite. -/
@[simp] theorem torusEmbedCLM_apply (N : ℕ) [NeZero N]
    (φ : FinLatticeField 2 N) (f : TorusTestFunction L) :
    torusEmbedCLM L N φ f =
    ∑ x : FinLatticeSites 2 N, φ x * evalTorusAtSite L N x f :=
  rfl

/-- Swap of lattice sites: (x₀, x₁) ↦ (x₁, x₀). -/
def swapSites (N : ℕ) (x : FinLatticeSites 2 N) : FinLatticeSites 2 N :=
  ![x 1, x 0]

/-- **Equivariance of evalTorusAtSite under coordinate swap.**

  `evalTorusAtSite x (swap f) = evalTorusAtSite (swap_sites x) f`

This is the key identity for proving D4 swap invariance of the
torus-embedded interacting measure. -/
theorem evalTorusAtSite_swap (N : ℕ) [NeZero N]
    (x : FinLatticeSites 2 N) (f : TorusTestFunction L) :
    evalTorusAtSite L N x (GaussianField.nuclearTensorProduct_swapCLM f) =
    evalTorusAtSite L N (swapSites N x) f := by
  simp only [evalTorusAtSite, swapSites]
  -- LHS: evalCLM (proj_{x 0} ∘ circRestr) (proj_{x 1} ∘ circRestr) (swapCLM f)
  -- RHS: evalCLM (proj_{![x 1, x 0] 0} ∘ circRestr) (proj_{![x 1, x 0] 1} ∘ circRestr) f
  -- Simplify ![x 1, x 0] indices
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  -- Now: evalCLM (proj_{x 0} ∘ circRestr) (proj_{x 1} ∘ circRestr) (swapCLM f) =
  --      evalCLM (proj_{x 1} ∘ circRestr) (proj_{x 0} ∘ circRestr) f
  exact GaussianField.evalCLM_comp_swapCLM _ _ f

/-- Time-reflection of lattice sites: (x₀, x₁) ↦ (-x₀, x₁). -/
def timeReflectSites (N : ℕ) (x : FinLatticeSites 2 N) : FinLatticeSites 2 N :=
  ![-x 0, x 1]

/-- **Equivariance of evalTorusAtSite under time reflection.**

  `evalTorusAtSite x (Θ f) = evalTorusAtSite (timeReflectSites x) f`

where `Θ = torusTimeReflection = mapCLM (circleReflection) id`.
Uses `evalCLM_comp_mapCLM`. -/
theorem evalTorusAtSite_timeReflection (N : ℕ) [NeZero N]
    (x : FinLatticeSites 2 N) (f : TorusTestFunction L) :
    evalTorusAtSite L N x (nuclearTensorProduct_mapCLM
      (circleReflection L) (ContinuousLinearMap.id ℝ _) f) =
    evalTorusAtSite L N (timeReflectSites N x) f := by
  simp only [evalTorusAtSite, timeReflectSites]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [evalCLM_comp_mapCLM (smoothCircle_coeff_basis L) (smoothCircle_coeff_basis L)]
  simp only [ContinuousLinearMap.comp_id]
  -- Need: proj_{x 0} ∘ circRestr ∘ circleReflection = proj_{-x 0} ∘ circRestr
  -- i.e., circleRestriction(circleReflection g)(x 0) = circleRestriction(g)(-x 0)
  -- Prove the key CLM equality and use it
  have key : ((ContinuousLinearMap.proj (x 0)).comp
      (circleRestriction L N)).comp (circleReflection L) =
    (ContinuousLinearMap.proj (-(x 0))).comp (circleRestriction L N) := by
    ext g
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      circleRestriction_apply, circleReflection, circlePoint]
    -- Goal: √(L/N) * g(-(val(x 0) * L / N)) = √(L/N) * g(val(-(x 0)) * L / N)
    congr 1
    -- Use ZMod.neg_val: val(-k) = if k = 0 then 0 else N - val k
    rw [ZMod.neg_val (x 0)]
    split
    · -- k = 0 case: g(-(val(0) * L/N)) = g(0)
      next hk => simp [hk]
    · -- k ≠ 0 case: g(-(val k * L/N)) = g((N - val k) * L/N)
      next hk =>
      have hval_le : ZMod.val (x 0) ≤ N := le_of_lt (ZMod.val_lt (x 0))
      have hN : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
      rw [show (↑(N - ZMod.val (x 0)) : ℝ) * L / ↑N =
          -(↑(ZMod.val (x 0)) * L / ↑N) + L from by
        rw [Nat.cast_sub hval_le]; field_simp; ring]
      exact (g.periodic' _).symm
  rw [key]

/-- Translation of lattice sites: x ↦ x - (j₁, j₂) in (ℤ/Nℤ)². -/
def translateSites (N : ℕ) (j₁ j₂ : ℤ) (x : FinLatticeSites 2 N) :
    FinLatticeSites 2 N :=
  ![x 0 - (j₁ : ZMod N), x 1 - (j₂ : ZMod N)]

/-- **Equivariance of evalTorusAtSite under lattice translation.**

  `evalTorusAtSite x (T_{(j₁a, j₂a)} f) = evalTorusAtSite (x - (j₁, j₂)) f`

where `a = L/N` is the lattice spacing and `j₁, j₂ ∈ ℤ`.
Uses `evalCLM_comp_mapCLM` + circle restriction translation property:
  `circleRestriction(T_{ja} g)(k) = circleRestriction(g)(k - j)` (by L-periodicity). -/
theorem evalTorusAtSite_latticeTranslation (N : ℕ) [NeZero N]
    (j₁ j₂ : ℤ) (x : FinLatticeSites 2 N) (f : TorusTestFunction L) :
    evalTorusAtSite L N x (nuclearTensorProduct_mapCLM
      (circleTranslation L (circleSpacing L N * j₁))
      (circleTranslation L (circleSpacing L N * j₂)) f) =
    evalTorusAtSite L N (translateSites N j₁ j₂ x) f := by
  simp only [evalTorusAtSite, translateSites]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [evalCLM_comp_mapCLM (smoothCircle_coeff_basis L) (smoothCircle_coeff_basis L)]
  -- Need: proj_{x i} ∘ circRestr ∘ T_{ja} = proj_{x i - j} ∘ circRestr
  -- Helper: (proj_k ∘ circRestr) ∘ T_{j*a} = (proj_{k-j}) ∘ circRestr
  -- i.e., circleRestriction(T_{ja} g)(k) = circleRestriction(g)(k - j)
  have transl_key : ∀ (k : ZMod N) (j : ℤ),
      ((ContinuousLinearMap.proj k).comp (circleRestriction L N)).comp
        (circleTranslation L (circleSpacing L N * j)) =
      (ContinuousLinearMap.proj (k - (j : ZMod N))).comp (circleRestriction L N) := by
    intro k j
    ext g
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      circleRestriction_apply, circlePoint, circleSpacing]
    -- Unfold circleTranslation application
    show Real.sqrt (L / ↑N) * g (↑(ZMod.val k) * L / ↑N - L / ↑N * ↑j) =
      Real.sqrt (L / ↑N) * g (↑(ZMod.val (k - (j : ZMod N))) * L / ↑N)
    congr 1
    -- val(k) - j ≡ val(k - j) (mod N), so they differ by m*N for some m : ℤ
    -- Hence (val(k) - j)*L/N = val(k-j)*L/N + m*L
    -- By L-periodicity of g, the two sides are equal.
    have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    -- Both val(k) - j and val(k-j) lift k - j : ZMod N to ℤ, so they're congruent mod N
    have hcong : (↑(ZMod.val k) - j : ℤ) ≡ ↑(ZMod.val (k - (j : ZMod N))) [ZMOD (N : ℤ)] := by
      rw [← ZMod.intCast_eq_intCast_iff]
      push_cast
      simp
    obtain ⟨m, hm⟩ := Int.modEq_iff_dvd.mp hcong
    -- hm : val(k-j) - (val(k) - j) = N * m
    -- Rewrite the LHS argument using periodicity
    have arith : ↑(ZMod.val k) * L / ↑N - L / ↑N * ↑j =
        ↑(ZMod.val (k - (j : ZMod N))) * L / ↑N + ↑(-m) * L := by
      have hm_real : (↑(ZMod.val (k - (j : ZMod N))) : ℝ) - (↑(ZMod.val k) - ↑j) =
          ↑N * ↑m := by exact_mod_cast hm
      -- val(k)*L/N - L/N*j = (val(k) - j) * L/N  (algebra)
      -- = (val(k-j) - N*m) * L/N                  (from hm_real)
      -- = val(k-j)*L/N - m*L                      (algebra)
      -- = val(k-j)*L/N + (-m)*L
      have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
      rw [show ↑(ZMod.val k) * L / ↑N - L / ↑N * ↑j =
        (↑(ZMod.val k) - ↑j) * L / ↑N from by ring]
      rw [show (↑(ZMod.val k) - ↑j : ℝ) =
        ↑(ZMod.val (k - (j : ZMod N))) - ↑N * ↑m from by linarith]
      rw [show (↑(ZMod.val (k - (j : ZMod N))) - ↑N * ↑m) * L / ↑N =
        ↑(ZMod.val (k - (j : ZMod N))) * L / ↑N - ↑m * (↑N * L / ↑N) from by ring]
      rw [show (↑N : ℝ) * L / ↑N = L from by rw [mul_comm]; exact mul_div_cancel_of_imp (fun h => absurd h hNr)]
      push_cast
      linarith
    rw [arith]
    exact (g.periodic.int_mul (-m)) _
  rw [transl_key (x 0) j₁, transl_key (x 1) j₂]

end GaussianField
