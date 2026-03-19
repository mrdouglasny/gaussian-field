/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Generalized Tensor Product Functor

Extends `nuclearTensorProduct_mapCLM` from endomorphisms to general CLMs
between different DyninMityagin spaces.

## Main definitions

- `nuclearTensorProduct_mapCLM_general` — `(T₁ ⊗ T₂)` for
  `T₁ : E₁ →L[ℝ] F₁` and `T₂ : E₂ →L[ℝ] F₂`, giving
  `NTP(E₁, E₂) →L[ℝ] NTP(F₁, F₂)`

## Mathematical background

The construction is the same as `nuclearTensorProduct_mapCLM`:
on the DM basis, `(T₁ ⊗ T₂)(basisVec m) = pure(T₁ ψ_a, T₂ ψ_b)`
where `m = pair(a, b)`. The coefficients of this pure tensor in the
output DM basis give a rapid-decay sequence, and the extension by
linearity/continuity gives the CLM.

The difference from `nuclearTensorProduct_mapCLM` is purely at the type
level: the input and output NTP spaces can be different.

## References

- Treves, *Topological Vector Spaces*, Ch. 50 (nuclear spaces)
-/

import Nuclear.NuclearTensorProduct
import Nuclear.TensorProductFunctorAxioms

noncomputable section

namespace GaussianField

open NuclearTensorProduct

/-! ## Generalized tensor product of CLMs -/

/-- **Generalized tensor product of CLMs** between different NTP spaces.

Given `T₁ : E₁ →L[ℝ] F₁` and `T₂ : E₂ →L[ℝ] F₂`, the tensor product
`T₁ ⊗ T₂ : NTP(E₁, E₂) →L[ℝ] NTP(F₁, F₂)` maps basis vectors by
`basisVec(a,b) ↦ pure(T₁ ψ_a, T₂ ψ_b)` and extends by continuity.

The proof follows the same structure as `nuclearTensorProduct_mapCLM`:
1. Define the action on basis vectors via `mapImage`
2. Show polynomial growth of seminorms (`mapImage_seminorm_bound`)
3. Show the induced map on rapid-decay sequences is continuous

Axiomatized for now as the full proof requires generalizing the entire
`mapImage`/`mapRapidDecay` machinery to different input/output types. -/
axiom nuclearTensorProduct_mapCLM_general
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    {F₁ : Type*} [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
    [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁] [DyninMityaginSpace F₁]
    {F₂ : Type*} [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
    [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] [DyninMityaginSpace F₂]
    (T₁ : E₁ →L[ℝ] F₁) (T₂ : E₂ →L[ℝ] F₂) :
    NuclearTensorProduct E₁ E₂ →L[ℝ] NuclearTensorProduct F₁ F₂

/-- Action on pure tensors: `(T₁ ⊗ T₂)(pure e₁ e₂) = pure (T₁ e₁) (T₂ e₂)`. -/
axiom nuclearTensorProduct_mapCLM_general_pure
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    {F₁ : Type*} [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁]
    [IsTopologicalAddGroup F₁] [ContinuousSMul ℝ F₁] [DyninMityaginSpace F₁]
    {F₂ : Type*} [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂]
    [IsTopologicalAddGroup F₂] [ContinuousSMul ℝ F₂] [DyninMityaginSpace F₂]
    (T₁ : E₁ →L[ℝ] F₁) (T₂ : E₂ →L[ℝ] F₂) (e₁ : E₁) (e₂ : E₂) :
    nuclearTensorProduct_mapCLM_general T₁ T₂ (NuclearTensorProduct.pure e₁ e₂) =
    NuclearTensorProduct.pure (T₁ e₁) (T₂ e₂)

end GaussianField
