/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nuclear Tensor Product Functor Axioms

Axioms (and theorems) for the functorial structure of the nuclear tensor product:
CLMs on nuclear Fréchet spaces lift to CLMs on the completed projective
tensor product, preserving composition and identity.

## Main axioms

- `nuclearTensorProduct_mapCLM` — `T₁ ⊗ T₂` on `NuclearTensorProduct`
- `nuclearTensorProduct_mapCLM_comp` — functoriality: `(T₁∘S₁) ⊗ (T₂∘S₂) = (T₁⊗T₂) ∘ (S₁⊗S₂)`
- `nuclearTensorProduct_mapCLM_id` — identity: `id ⊗ id = id`
- `nuclearTensorProduct_mapCLM_pure` — action on pure tensors

## Main theorems

- `nuclearTensorProduct_swapCLM` — swap factors (Cantor pair permutation)
- `nuclearTensorProduct_swapCLM_pure` — swap on pure tensors

## Mathematical background

CLMs on nuclear Fréchet spaces lift to completed tensor products
(Trèves, Ch. 50). In our Dynin-Mityagin representation, CLMs have polynomial
growth on basis coefficients, which preserves rapid decay. The tensor
product functor is symmetric monoidal, preserving composition and identity.

The swap map `E₁ ⊗̂ E₂ → E₂ ⊗̂ E₁` is realized as the Cantor pair permutation
`m ↦ pair(unpair(m).2, unpair(m).1)`. Rapid decay is preserved because
`1 + pair(a,b) ≤ 4·(1 + pair(b,a))²` via `nat_pair_bound`.

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

/-! ## Swap implementation -/

/-- Swap the components of a Cantor pair index: if `unpair(m) = (a,b)`,
then `pairSwap m = pair(b,a)`. -/
private def pairSwap (m : ℕ) : ℕ :=
  Nat.pair (Nat.unpair m).2 (Nat.unpair m).1

/-- `pairSwap` is an involution: `pairSwap (pairSwap m) = m`. -/
private theorem pairSwap_involutive : Function.Involutive pairSwap := fun m => by
  show Nat.pair (Nat.unpair (Nat.pair (Nat.unpair m).2 (Nat.unpair m).1)).2
    (Nat.unpair (Nat.pair (Nat.unpair m).2 (Nat.unpair m).1)).1 = m
  rw [Nat.unpair_pair]
  exact Nat.pair_unpair m

/-- `pairSwap` as an equivalence `ℕ ≃ ℕ` (from involutivity). -/
private def pairSwapEquiv : ℕ ≃ ℕ :=
  pairSwap_involutive.toPerm pairSwap

@[simp] private theorem pairSwapEquiv_apply (m : ℕ) :
    pairSwapEquiv m = pairSwap m :=
  congr_fun pairSwap_involutive.coe_toPerm m

/-- Weight bound: `1 + m ≤ 4 · (1 + pairSwap m) ^ 2`.

For `m = pair(a,b)`, `pairSwap m = pair(b,a)`. Since `a,b ≤ pair(b,a)`,
we get `a+b+2 ≤ 2·(1+pairSwap m)`, hence `1+m ≤ (a+b+2)² ≤ 4·(1+pairSwap m)²`. -/
private theorem one_add_le_sq_pairSwap (m : ℕ) :
    (1 + (m : ℝ)) ≤ 4 * (1 + (pairSwap m : ℝ)) ^ 2 := by
  set a := (Nat.unpair m).1
  set b := (Nat.unpair m).2
  have hm : m = Nat.pair a b := (Nat.pair_unpair m).symm
  have h_sw : pairSwap m = Nat.pair b a := rfl
  have ha : (a : ℝ) ≤ pairSwap m := by
    rw [h_sw]; exact_mod_cast Nat.right_le_pair b a
  have hb : (b : ℝ) ≤ pairSwap m := by
    rw [h_sw]; exact_mod_cast Nat.left_le_pair b a
  have h1 : (1 : ℝ) + m ≤ ((a : ℝ) + b + 2) ^ 2 := by
    rw [hm]
    have h_cast : (Nat.pair a b : ℝ) ≤ ((a : ℝ) + b + 1) ^ 2 := by
      exact_mod_cast nat_pair_bound a b
    nlinarith
  calc (1 : ℝ) + m ≤ ((a : ℝ) + b + 2) ^ 2 := h1
    _ ≤ (2 * (1 + (pairSwap m : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 2
    _ = 4 * (1 + (pairSwap m : ℝ)) ^ 2 := by ring

/-- The swapped sequence of a rapidly decaying sequence is rapidly decaying. -/
private def swapRapidDecay (f : RapidDecaySeq) : RapidDecaySeq where
  val m := f.val (pairSwap m)
  rapid_decay k := by
    apply Summable.of_nonneg_of_le
    · intro m; exact mul_nonneg (abs_nonneg _) (RapidDecaySeq.weight_nonneg m k)
    · intro m
      show |f.val (pairSwap m)| * (1 + (m : ℝ)) ^ k ≤
        (4 : ℝ) ^ k * (|f.val (pairSwap m)| * (1 + (pairSwap m : ℝ)) ^ (2 * k))
      have h_wt : (1 + (m : ℝ)) ^ k ≤ (4 : ℝ) ^ k * (1 + (pairSwap m : ℝ)) ^ (2 * k) :=
        calc (1 + (m : ℝ)) ^ k
            ≤ (4 * (1 + (pairSwap m : ℝ)) ^ 2) ^ k :=
              pow_le_pow_left₀ (by positivity) (one_add_le_sq_pairSwap m) k
          _ = (4 : ℝ) ^ k * (1 + (pairSwap m : ℝ)) ^ (2 * k) := by rw [mul_pow, ← pow_mul]
      calc |f.val (pairSwap m)| * (1 + (m : ℝ)) ^ k
          ≤ |f.val (pairSwap m)| * ((4 : ℝ) ^ k * (1 + (pairSwap m : ℝ)) ^ (2 * k)) :=
            mul_le_mul_of_nonneg_left h_wt (abs_nonneg _)
        _ = (4 : ℝ) ^ k * (|f.val (pairSwap m)| * (1 + (pairSwap m : ℝ)) ^ (2 * k)) := by ring
    · -- Summability via reindexing by pairSwapEquiv
      have h_eq : (fun m => (4 : ℝ) ^ k *
          (|f.val (pairSwap m)| * (1 + (pairSwap m : ℝ)) ^ (2 * k))) =
          fun m => (4 : ℝ) ^ k *
          ((fun n => |f.val n| * (1 + (n : ℝ)) ^ (2 * k)) (pairSwapEquiv m)) := by
        ext m; simp [pairSwapEquiv_apply]
      rw [h_eq]
      exact (pairSwapEquiv.summable_iff.mpr (f.rapid_decay (2 * k))).const_smul ((4 : ℝ) ^ k)

set_option maxHeartbeats 400000 in
/-- Seminorm bound: `rapidDecaySeminorm k (swap f) ≤ 4^k · rapidDecaySeminorm (2k) f`. -/
private theorem swap_seminorm_bound (k : ℕ) (f : RapidDecaySeq) :
    RapidDecaySeq.rapidDecaySeminorm k (swapRapidDecay f) ≤
    (4 : ℝ) ^ k * RapidDecaySeq.rapidDecaySeminorm (2 * k) f := by
  show ∑' m, |f.val (pairSwap m)| * (1 + (m : ℝ)) ^ k ≤
    (4 : ℝ) ^ k * ∑' m, |f.val m| * (1 + (m : ℝ)) ^ (2 * k)
  -- Reindex the RHS via pairSwapEquiv
  have h_reindex : ∑' m, |f.val m| * (1 + (m : ℝ)) ^ (2 * k) =
      ∑' m, |f.val (pairSwap m)| * (1 + (pairSwap m : ℝ)) ^ (2 * k) := by
    have := (pairSwapEquiv.tsum_eq
      (fun n => |f.val n| * (1 + (n : ℝ)) ^ (2 * k))).symm
    simp only [pairSwapEquiv_apply] at this
    exact this
  rw [h_reindex, ← tsum_mul_left]
  -- Pointwise bound
  have h_term : ∀ m, |f.val (pairSwap m)| * (1 + (m : ℝ)) ^ k ≤
      (4 : ℝ) ^ k * (|f.val (pairSwap m)| * (1 + (pairSwap m : ℝ)) ^ (2 * k)) := by
    intro m
    have h_wt : (1 + (m : ℝ)) ^ k ≤ (4 : ℝ) ^ k * (1 + (pairSwap m : ℝ)) ^ (2 * k) := by
      calc (1 + (m : ℝ)) ^ k
          ≤ (4 * (1 + (pairSwap m : ℝ)) ^ 2) ^ k :=
            pow_le_pow_left₀ (by positivity) (one_add_le_sq_pairSwap m) k
        _ = (4 : ℝ) ^ k * (1 + (pairSwap m : ℝ)) ^ (2 * k) := by rw [mul_pow, ← pow_mul]
    calc |f.val (pairSwap m)| * (1 + (m : ℝ)) ^ k
        ≤ |f.val (pairSwap m)| * ((4 : ℝ) ^ k * (1 + (pairSwap m : ℝ)) ^ (2 * k)) :=
          mul_le_mul_of_nonneg_left h_wt (abs_nonneg _)
      _ = (4 : ℝ) ^ k * (|f.val (pairSwap m)| * (1 + (pairSwap m : ℝ)) ^ (2 * k)) := by ring
  -- Summability of bounding series
  have h_sum : Summable (fun m => (4 : ℝ) ^ k *
      (|f.val (pairSwap m)| * (1 + (pairSwap m : ℝ)) ^ (2 * k))) := by
    have h_eq : (fun m => (4 : ℝ) ^ k *
        (|f.val (pairSwap m)| * (1 + (pairSwap m : ℝ)) ^ (2 * k))) =
        fun m => (4 : ℝ) ^ k *
        ((fun n => |f.val n| * (1 + (n : ℝ)) ^ (2 * k)) (pairSwapEquiv m)) := by
      ext m; simp [pairSwapEquiv_apply]
    rw [h_eq]
    exact (pairSwapEquiv.summable_iff.mpr (f.rapid_decay (2 * k))).const_smul ((4 : ℝ) ^ k)
  exact ((swapRapidDecay f).rapid_decay k).tsum_le_tsum h_term h_sum

/-- The swap linear map on `NuclearTensorProduct`. -/
private def swapLM
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂] :
    NuclearTensorProduct E₁ E₂ →ₗ[ℝ] NuclearTensorProduct E₂ E₁ where
  toFun := swapRapidDecay
  map_add' := fun f g => by ext m; rfl
  map_smul' := fun r f => by ext m; rfl

/-- **Swap factors in a nuclear tensor product.**

The canonical isomorphism `E₁ ⊗̂ E₂ ≅ E₂ ⊗̂ E₁` as a CLM, realized via
the Cantor pair permutation `m ↦ pair(unpair(m).2, unpair(m).1)`.

On elementary tensors: `swap(f₁ ⊗ f₂) = f₂ ⊗ f₁`.

Reference: Trèves, *Topological Vector Spaces*, Ch. 43, §43.5. -/
def nuclearTensorProduct_swapCLM
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂] :
    NuclearTensorProduct E₁ E₂ →L[ℝ] NuclearTensorProduct E₂ E₁ :=
  { swapLM with
    cont := by
      apply Seminorm.continuous_from_bounded
        (RapidDecaySeq.rapidDecay_withSeminorms :
          WithSeminorms (RapidDecaySeq.rapidDecaySeminorm :
            ℕ → Seminorm ℝ (NuclearTensorProduct E₁ E₂)))
        (RapidDecaySeq.rapidDecay_withSeminorms :
          WithSeminorms (RapidDecaySeq.rapidDecaySeminorm :
            ℕ → Seminorm ℝ (NuclearTensorProduct E₂ E₁)))
      intro k
      refine ⟨{2 * k}, ⟨(4 : ℝ) ^ k, by positivity⟩, fun f => ?_⟩
      simp only [Finset.sup_singleton, Seminorm.comp_apply]
      exact swap_seminorm_bound k f }

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

Proof: The swap permutes Cantor pair indices, giving
`coeff (unpair m).2 e₁ · coeff (unpair m).1 e₂ = coeff (unpair m).1 e₂ · coeff (unpair m).2 e₁`
by commutativity of multiplication. -/
theorem nuclearTensorProduct_swapCLM_pure
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    (e₁ : E₁) (e₂ : E₂) :
    nuclearTensorProduct_swapCLM (NuclearTensorProduct.pure e₁ e₂) =
    NuclearTensorProduct.pure e₂ e₁ := by
  ext m
  show (NuclearTensorProduct.pure e₁ e₂).val (pairSwap m) =
    (NuclearTensorProduct.pure e₂ e₁).val m
  simp only [pure_val, pairSwap, Nat.unpair_pair]
  ring

end GaussianField

end
