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
import Lattice.FiniteField
import Nuclear.TensorProductFunctorAxioms

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

end GaussianField
