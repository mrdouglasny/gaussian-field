/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nuclear Tensor Product Functor Axioms

Axioms for the functorial structure of the nuclear tensor product:
CLMs on nuclear Fréchet spaces lift to CLMs on the completed projective
tensor product, preserving composition and identity.

## Main axioms

- `nuclearTensorProduct_mapCLM` — `T₁ ⊗ T₂` on `NuclearTensorProduct`
- `nuclearTensorProduct_swapCLM` — swap factors
- `nuclearTensorProduct_mapCLM_comp` — functoriality: `(T₁∘S₁) ⊗ (T₂∘S₂) = (T₁⊗T₂) ∘ (S₁⊗S₂)`
- `nuclearTensorProduct_mapCLM_id` — identity: `id ⊗ id = id`
- `nuclearTensorProduct_mapCLM_pure` — action on pure tensors
- `nuclearTensorProduct_swapCLM_pure` — swap on pure tensors

## Mathematical background

CLMs on nuclear Fréchet spaces lift to completed tensor products
(Trèves, Ch. 50). In our Dynin-Mityagin representation, CLMs have polynomial
growth on basis coefficients, which preserves rapid decay. The tensor
product functor is symmetric monoidal, preserving composition and identity.

## References

- Trèves, *Topological Vector Spaces, Distributions, and Kernels*, Ch. 43, 50
-/

import Nuclear.NuclearTensorProduct

noncomputable section

namespace GaussianField

open NuclearTensorProduct

/-! ## Tensor product of CLMs -/

/-- **Tensor product of CLMs on nuclear spaces.**

Given CLMs `T₁ : E₁ →L[ℝ] E₁` and `T₂ : E₂ →L[ℝ] E₂`, their tensor product
`T₁ ⊗ T₂` acts as a CLM on `NuclearTensorProduct E₁ E₂`.

On elementary tensors: `(T₁ ⊗ T₂)(f₁ ⊗ f₂) = T₁(f₁) ⊗ T₂(f₂)`.

Reference: Trèves, *Topological Vector Spaces*, Ch. 50, Theorem 50.1. -/
axiom nuclearTensorProduct_mapCLM
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (T₁ : E₁ →L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂) :
    NuclearTensorProduct E₁ E₂ →L[ℝ] NuclearTensorProduct E₁ E₂

/-- **Swap factors in a nuclear tensor product.**

The canonical isomorphism `E₁ ⊗̂ E₂ ≅ E₂ ⊗̂ E₁` as a CLM.

On elementary tensors: `swap(f₁ ⊗ f₂) = f₂ ⊗ f₁`.

Reference: Trèves, *Topological Vector Spaces*, Ch. 43, §43.5. -/
axiom nuclearTensorProduct_swapCLM
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂] :
    NuclearTensorProduct E₁ E₂ →L[ℝ] NuclearTensorProduct E₂ E₁

/-! ## Functoriality axioms -/

/-- **Functoriality of `mapCLM`: composition distributes.**

`(T₁ ∘ S₁) ⊗ (T₂ ∘ S₂) = (T₁ ⊗ T₂) ∘ (S₁ ⊗ S₂)`

On elementary tensors:
- LHS: `(T₁∘S₁)(f₁) ⊗ (T₂∘S₂)(f₂) = T₁(S₁(f₁)) ⊗ T₂(S₂(f₂))`
- RHS: `(T₁⊗T₂)(S₁(f₁) ⊗ S₂(f₂)) = T₁(S₁(f₁)) ⊗ T₂(S₂(f₂))` ✓

This is a basic property of the tensor product functor. -/
axiom nuclearTensorProduct_mapCLM_comp
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (T₁ S₁ : E₁ →L[ℝ] E₁) (T₂ S₂ : E₂ →L[ℝ] E₂) :
    nuclearTensorProduct_mapCLM (T₁.comp S₁) (T₂.comp S₂) =
    (nuclearTensorProduct_mapCLM T₁ T₂).comp (nuclearTensorProduct_mapCLM S₁ S₂)

/-- **`mapCLM` preserves identity: `id ⊗ id = id`.**

On elementary tensors: `(id ⊗ id)(f₁ ⊗ f₂) = id(f₁) ⊗ id(f₂) = f₁ ⊗ f₂` ✓

Together with `mapCLM_comp`, this makes `mapCLM` a functor from
`CLM(E₁) × CLM(E₂)` to `CLM(E₁ ⊗̂ E₂)`. -/
axiom nuclearTensorProduct_mapCLM_id
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂] :
    nuclearTensorProduct_mapCLM
      (ContinuousLinearMap.id ℝ E₁)
      (ContinuousLinearMap.id ℝ E₂) =
    ContinuousLinearMap.id ℝ (NuclearTensorProduct E₁ E₂)

/-! ## Pure tensor specifications -/

/-- **`mapCLM` acts on pure tensors by applying each factor.**

  `(T₁ ⊗ T₂)(pure e₁ e₂) = pure (T₁ e₁) (T₂ e₂)`

This is the defining property of the tensor product of linear maps
on elementary tensors.

Reference: Trèves, *Topological Vector Spaces*, Ch. 50, Theorem 50.1. -/
axiom nuclearTensorProduct_mapCLM_pure
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (T₁ : E₁ →L[ℝ] E₁) (T₂ : E₂ →L[ℝ] E₂) (e₁ : E₁) (e₂ : E₂) :
    nuclearTensorProduct_mapCLM T₁ T₂ (NuclearTensorProduct.pure e₁ e₂) =
    NuclearTensorProduct.pure (T₁ e₁) (T₂ e₂)

/-- **`swapCLM` swaps the factors of a pure tensor.**

  `swap(pure e₁ e₂) = pure e₂ e₁`

This is the defining property of the symmetric braiding on elementary tensors.

Reference: Trèves, *Topological Vector Spaces*, Ch. 43, §43.5. -/
axiom nuclearTensorProduct_swapCLM_pure
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (e₁ : E₁) (e₂ : E₂) :
    nuclearTensorProduct_swapCLM (NuclearTensorProduct.pure e₁ e₂) =
    NuclearTensorProduct.pure e₂ e₁

end GaussianField

end
