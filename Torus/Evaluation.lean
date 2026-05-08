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

/-! ## Circle point periodicity lemmas -/

private lemma zmod_val_neg_add_val_dvd (N : ℕ) [NeZero N] (k : ZMod N) :
    N ∣ ((-k).val + k.val) := by
  have h2 := ZMod.val_add (-k) k
  rw [show -k + k = (0 : ZMod N) from neg_add_cancel k, ZMod.val_zero] at h2
  exact Nat.dvd_of_mod_eq_zero h2.symm

private lemma zmod_val_sub_intCast_dvd (N : ℕ) [NeZero N] (k : ZMod N) (j : ℤ) :
    (N : ℤ) ∣ ((k.val : ℤ) - j - ((k - (j : ZMod N)).val : ℤ)) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; simp [ZMod.natCast_val]

private lemma periodic_add_int_mul {f : ℝ → ℝ} {c : ℝ} (hf : Function.Periodic f c)
    (x : ℝ) (n : ℤ) : f (x + n * c) = f x := by
  rw [show x + n * c = x - (-n) • c from by simp [zsmul_eq_mul]]
  exact hf.sub_zsmul_eq (-n)

/-- `g(-circlePoint(k)) = g(circlePoint(-k))` by L-periodicity of smooth circle functions. -/
private lemma smooth_neg_circlePoint (N : ℕ) [NeZero N]
    (g : SmoothMap_Circle L ℝ) (k : ZMod N) :
    g (-(circlePoint L N k)) = g (circlePoint L N (-k)) := by
  simp only [circlePoint]
  obtain ⟨m, hm⟩ := zmod_val_neg_add_val_dvd N k
  have hper : Function.Periodic (⇑g) L := g.periodic'
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h' : (↑((-k).val) : ℝ) - ↑N * ↑m = -↑(k.val) := by
    have : (↑((-k).val) : ℝ) + ↑(k.val) = ↑N * ↑m := by exact_mod_cast hm
    linarith
  rw [show -(↑(k.val) * L / ↑N) = ↑((-k).val) * L / ↑N - ↑m * L from by
    field_simp; rw [h']; ring]
  rw [show (↑m : ℝ) * L = (m : ℕ) • L from (nsmul_eq_mul m L).symm]
  exact hper.sub_nsmul_eq m

/-- `g(circlePoint(k) - j*spacing) = g(circlePoint(k - j))` by L-periodicity. -/
private lemma smooth_sub_circlePoint (N : ℕ) [NeZero N]
    (g : SmoothMap_Circle L ℝ) (k : ZMod N) (j : ℤ) :
    g (circlePoint L N k - circleSpacing L N * j) =
    g (circlePoint L N (k - (j : ZMod N))) := by
  simp only [circlePoint, circleSpacing]
  obtain ⟨m, hm⟩ := zmod_val_sub_intCast_dvd N k j
  have hper : Function.Periodic (⇑g) L := g.periodic'
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have arith : (↑(k.val) : ℝ) - (↑j : ℝ) =
      ↑((k - (↑j : ZMod N)).val) + (↑N : ℝ) * (↑m : ℝ) := by
    exact_mod_cast
      (show (↑(k.val) : ℤ) - j = ↑((k - (↑j : ZMod N)).val) + ↑N * m by linarith)
  rw [show ↑(k.val) * L / ↑N - L / ↑N * ↑j =
      ↑((k - (↑j : ZMod N)).val) * L / ↑N + ↑m * L from by field_simp; congr 1]
  exact periodic_add_int_mul hper _ m

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

/-! ## Glimm–Jaffe (Riemann-sum) torus evaluation

Parallel to `evalTorusAtSite` / `torusEmbedCLM`, but built from the
Riemann-sum-isometric `circleRestrictionGJ` instead of the
counting-isometric `circleRestriction`. For a pure tensor `f₁ ⊗ f₂`:

  `eval^{GJ}_x(f₁ ⊗ f₂) = (L/N) · f₁(x₀·L/N) · (L/N) · f₂(x₁·L/N)`
                           `= (L/N)² · f₁(x₀·L/N) · f₂(x₁·L/N)`
                           `= a^d · f₁(x₀·a) · f₂(x₁·a)`         (d = 2)

The squared sum `Σ_x (eval^{GJ}_x f)² ≈ a^d · ∫_{T²_L} f² dx` (`O(a^d)`),
which exactly cancels the `(a^d)⁻¹` factor in the GJ-aligned lattice
covariance, giving uniform-in-N control of the embedded two-point
function.

Relationship: `evalTorusAtSiteGJ = a^{d/2} • evalTorusAtSite`
(the extra `(L/N)^{1/2}` per coordinate compounds to `(L/N)^{d/2} = a^{d/2}`
across d coords; for d = 2 this is `(L/N) = a`). -/

/-- Glimm–Jaffe evaluation of a torus test function at a lattice site,
defined as `(L/N) = a` times the bare evaluation. Equivalently, this is
what one would get from `evalCLM` of `circleRestrictionGJ`-tensor-products
(see `evalTorusAtSiteGJ_pure` for the pure-tensor formula). -/
noncomputable def evalTorusAtSiteGJ (N : ℕ) [NeZero N]
    (x : FinLatticeSites 2 N) : TorusTestFunction L →L[ℝ] ℝ :=
  circleSpacing L N • evalTorusAtSite L N x

/-- The GJ torus embedding: maps a lattice field `φ : (ℤ/Nℤ)² → ℝ` to a
continuous linear functional on `TorusTestFunction L`, using the
Riemann-sum-isometric circle restriction.

  `(ι^{GJ}_N φ)(f) = Σ_{x ∈ (ℤ/Nℤ)²} φ(x) · eval^{GJ}_x(f)
                  = (L/N)² Σ_x φ_x · f(x · L/N)`

For pure tensors this is the Riemann-sum approximation of
`∫_{T²_L} φ_continuum · f dx` where `φ_continuum` is a step function
agreeing with `φ` on lattice cells. -/
def torusEmbedCLMGJ (N : ℕ) [NeZero N]
    (φ : FinLatticeField 2 N) : Configuration (TorusTestFunction L) where
  toFun f := ∑ x : FinLatticeSites 2 N, φ x * evalTorusAtSiteGJ L N x f
  map_add' f g := by
    simp only [map_add, mul_add, Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [map_smul, smul_eq_mul, mul_left_comm, Finset.mul_sum, RingHom.id_apply]
  cont := by
    apply continuous_finset_sum
    intro x _
    exact continuous_const.mul (evalTorusAtSiteGJ L N x).cont

/-- The GJ torus embedding agrees with evalTorusAtSiteGJ. -/
@[simp] theorem torusEmbedCLMGJ_apply (N : ℕ) [NeZero N]
    (φ : FinLatticeField 2 N) (f : TorusTestFunction L) :
    torusEmbedCLMGJ L N φ f =
    ∑ x : FinLatticeSites 2 N, φ x * evalTorusAtSiteGJ L N x f :=
  rfl

/-- The GJ evaluation equals `(L/N)` times the bare evaluation. -/
@[simp] theorem evalTorusAtSiteGJ_apply' (N : ℕ) [NeZero N]
    (x : FinLatticeSites 2 N) (f : TorusTestFunction L) :
    evalTorusAtSiteGJ L N x f = circleSpacing L N * evalTorusAtSite L N x f := by
  unfold evalTorusAtSiteGJ
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul]

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
  -- Reduce to: proj_{x 0} ∘ circRestr ∘ circleReflection = proj_{-x 0} ∘ circRestr
  suffices h : ((ContinuousLinearMap.proj (x 0)).comp (circleRestriction L N)).comp
      (circleReflection L) =
    (ContinuousLinearMap.proj (-x 0)).comp (circleRestriction L N) by rw [h]
  ext g
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    circleRestriction_apply]
  congr 1
  exact smooth_neg_circlePoint L N g (x 0)

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
  -- Reduce to: proj_{x i} ∘ circRestr ∘ T_{ja} = proj_{x i - j} ∘ circRestr
  suffices h₁ : ((ContinuousLinearMap.proj (x 0)).comp (circleRestriction L N)).comp
      (circleTranslation L (circleSpacing L N * j₁)) =
    (ContinuousLinearMap.proj (x 0 - (j₁ : ZMod N))).comp (circleRestriction L N) by
    suffices h₂ : ((ContinuousLinearMap.proj (x 1)).comp (circleRestriction L N)).comp
        (circleTranslation L (circleSpacing L N * j₂)) =
      (ContinuousLinearMap.proj (x 1 - (j₂ : ZMod N))).comp (circleRestriction L N) by
      rw [h₁, h₂]
    ext g; simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      circleRestriction_apply]; congr 1
    exact smooth_sub_circlePoint L N g (x 1) j₂
  ext g; simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    circleRestriction_apply]; congr 1
  exact smooth_sub_circlePoint L N g (x 0) j₁

end GaussianField
