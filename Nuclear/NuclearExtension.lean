/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nuclear Extension Theorem

The nuclear extension theorem for DyninMityaginSpaces: a bilinear map
`B : E₁ →ₗ E₂ →ₗ G` that is bounded by continuous seminorms extends
uniquely to a continuous linear map on the nuclear tensor product.

## Main results

- `nuclear_bilinear_extension` — existence of the extension (from `lift`)
- `nuclear_bilinear_extension_unique` — uniqueness on pure tensors implies
  equality (from density of pure tensors, using `HasBiorthogonalBasis`)

## Mathematical content

The Schwartz nuclear theorem states: if E₁, ..., Eₙ are nuclear Fréchet
spaces and Φ : E₁ × ... × Eₙ → G is a separately continuous multilinear
map, then there exists a unique continuous linear map
W : E₁ ⊗̂ ... ⊗̂ Eₙ → G such that W(e₁ ⊗ ... ⊗ eₙ) = Φ(e₁,...,eₙ).

Here the tensor product E₁ ⊗̂ E₂ is `NuclearTensorProduct E₁ E₂`
(identified with `RapidDecaySeq` via Cantor pairing of basis indices).

The bilinear case (n=2) is `NuclearTensorProduct.lift` from
`Nuclear/NuclearTensorProduct.lean`. The n-linear case follows by
induction, extending one factor at a time:
  Φ : E₁ × E₂ × ... × Eₙ → G
  ↝ Φ₁ : E₁ × (E₂ ⊗̂ ... ⊗̂ Eₙ) → G   (by induction on n-1 factors)
  ↝ W : E₁ ⊗̂ (E₂ ⊗̂ ... ⊗̂ Eₙ) → G   (by bilinear lift)
Then use E₁ ⊗̂ (E₂ ⊗̂ ... ⊗̂ Eₙ) ≅ E₁ ⊗̂ E₂ ⊗̂ ... ⊗̂ Eₙ (associativity).

## References

- Gel'fand-Vilenkin, "Generalized Functions IV", Ch. I, §3
- Reed-Simon, "Methods of Modern Mathematical Physics I", Theorem V.13
- Treves, "Topological Vector Spaces", Ch. 51
-/

import Nuclear.NuclearTensorProduct

noncomputable section

namespace GaussianField

open NuclearTensorProduct

/-! ## Pure tensors span the tensor product

Under `HasBiorthogonalBasis`, each standard basis vector `basisVec m` of
`NuclearTensorProduct E₁ E₂` is the pure tensor of the corresponding
factor basis vectors. Since `hasSum_basisVec` shows that every element
is the limit of finite sums of `basisVec`, this means pure tensors are
dense. -/

section BasisVecPure

variable {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
  [DyninMityaginSpace.HasBiorthogonalBasis E₁]
variable {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
  [DyninMityaginSpace.HasBiorthogonalBasis E₂]

/-- Under biorthogonality, the standard basis vector at Cantor index `m`
equals the pure tensor of the factor basis vectors at `unpair m`.

At each coordinate `k`, both sides evaluate to `δ(unpair(k).1, i) * δ(unpair(k).2, j)`
where `(i, j) = unpair m`. -/
theorem basisVec_eq_pure (m : ℕ) :
    (RapidDecaySeq.basisVec m : NuclearTensorProduct E₁ E₂) =
    pure (DyninMityaginSpace.basis (E := E₁) (Nat.unpair m).1)
         (DyninMityaginSpace.basis (E := E₂) (Nat.unpair m).2) := by
  ext k
  simp only [pure_val,
    DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis,
    RapidDecaySeq.basisVec]
  -- Goal: (if k = m then 1 else 0) =
  --       (if unpair(k).1 = unpair(m).1 then 1 else 0) *
  --       (if unpair(k).2 = unpair(m).2 then 1 else 0)
  by_cases hk : k = m
  · subst hk; simp
  · -- k ≠ m, so unpair(k) ≠ unpair(m), hence at least one component differs
    simp only [hk, ite_false]
    by_cases h1 : (Nat.unpair k).1 = (Nat.unpair m).1
    · have h2 : (Nat.unpair k).2 ≠ (Nat.unpair m).2 := by
        intro h2; exact hk (by rw [← Nat.pair_unpair k, ← Nat.pair_unpair m, h1, h2])
      simp [h2]
    · simp [h1]

/-- Every element of the nuclear tensor product is the limit of finite sums
of pure tensors (under biorthogonality).

This follows from `hasSum_basisVec` and `basisVec_eq_pure`:
  `a = ∑' m, a.val m • basisVec m = ∑' m, a.val m • pure(ψ₁ᵢ, ψ₂ⱼ)`. -/
theorem hasSum_pure (a : NuclearTensorProduct E₁ E₂) :
    HasSum (fun m => a.val m •
      pure (DyninMityaginSpace.basis (E := E₁) (Nat.unpair m).1)
           (DyninMityaginSpace.basis (E := E₂) (Nat.unpair m).2)) a := by
  have h := RapidDecaySeq.hasSum_basisVec (a : RapidDecaySeq)
  simp_rw [basisVec_eq_pure (E₁ := E₁) (E₂ := E₂)] at h
  exact h

end BasisVecPure

/-! ## Bilinear nuclear extension -/

section Extension

variable {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
variable {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **Bilinear nuclear extension theorem (existence).**

A bilinear map `B : E₁ →ₗ E₂ →ₗ G` that is bounded by finitely many
continuous seminorms extends to a continuous linear map on the nuclear
tensor product, with `W(e₁ ⊗ e₂) = B(e₁, e₂)`.

This is a direct application of `NuclearTensorProduct.lift` and `lift_pure`.
The seminorm bound hypothesis is exactly what `lift` requires:
  `‖B e₁ e₂‖ ≤ C * (s₁.sup p) e₁ * (s₂.sup p) e₂`
where `s₁, s₂` are finsets of seminorm indices and `C > 0`.

**Note:** For a continuous bilinear map `B : E₁ →L[ℝ] E₂ →L[ℝ] G`,
extracting this bound requires knowing that the map into the space of
CLMs is bounded by seminorms. Use `nuclear_bilinear_extension_of_clm`
for the automated version when available. -/
theorem nuclear_bilinear_extension
    (B : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] G)
    {C : ℝ} {s₁ : Finset (@DyninMityaginSpace.ι E₁ _ _ _ _ _ _)}
    {s₂ : Finset (@DyninMityaginSpace.ι E₂ _ _ _ _ _ _)}
    (hC : 0 < C)
    (hB : ∀ e₁ e₂, ‖B e₁ e₂‖ ≤ C * (s₁.sup DyninMityaginSpace.p) e₁ *
        (s₂.sup DyninMityaginSpace.p) e₂) :
    ∃ (W : NuclearTensorProduct E₁ E₂ →L[ℝ] G),
      ∀ (e₁ : E₁) (e₂ : E₂), W (pure e₁ e₂) = B e₁ e₂ :=
  ⟨lift B hC hB, lift_pure B hC hB⟩

/-- **Bilinear nuclear extension (term-mode).**

Returns the CLM directly rather than an existence proof. Useful when
the extension needs to be composed with other maps. -/
def nuclearLift
    (B : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] G)
    {C : ℝ} {s₁ : Finset (@DyninMityaginSpace.ι E₁ _ _ _ _ _ _)}
    {s₂ : Finset (@DyninMityaginSpace.ι E₂ _ _ _ _ _ _)}
    (hC : 0 < C)
    (hB : ∀ e₁ e₂, ‖B e₁ e₂‖ ≤ C * (s₁.sup DyninMityaginSpace.p) e₁ *
        (s₂.sup DyninMityaginSpace.p) e₂) :
    NuclearTensorProduct E₁ E₂ →L[ℝ] G :=
  lift B hC hB

@[simp]
theorem nuclearLift_pure
    (B : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] G)
    {C : ℝ} {s₁ : Finset (@DyninMityaginSpace.ι E₁ _ _ _ _ _ _)}
    {s₂ : Finset (@DyninMityaginSpace.ι E₂ _ _ _ _ _ _)}
    (hC : 0 < C)
    (hB : ∀ e₁ e₂, ‖B e₁ e₂‖ ≤ C * (s₁.sup DyninMityaginSpace.p) e₁ *
        (s₂.sup DyninMityaginSpace.p) e₂)
    (e₁ : E₁) (e₂ : E₂) :
    nuclearLift B hC hB (pure e₁ e₂) = B e₁ e₂ :=
  lift_pure B hC hB e₁ e₂

end Extension

/-! ## Uniqueness of the nuclear extension -/

section Uniqueness

variable {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
  [DyninMityaginSpace.HasBiorthogonalBasis E₁]
variable {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
  [DyninMityaginSpace.HasBiorthogonalBasis E₂]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Uniqueness of the nuclear extension.**

If two continuous linear maps `W₁, W₂ : E₁ ⊗̂ E₂ →L[ℝ] G` agree on all
pure tensors, then they are equal.

**Proof:** Under `HasBiorthogonalBasis`, every standard basis vector
`basisVec m` equals `pure(ψ₁ᵢ, ψ₂ⱼ)` (see `basisVec_eq_pure`), and
every element is the limit `∑' m, aₘ • basisVec m` (see `hasSum_basisVec`).
By continuity and linearity, `W₁` and `W₂` agree on all elements. -/
theorem nuclear_bilinear_extension_unique
    (W₁ W₂ : NuclearTensorProduct E₁ E₂ →L[ℝ] G)
    (h_pure : ∀ (e₁ : E₁) (e₂ : E₂),
      W₁ (pure e₁ e₂) = W₂ (pure e₁ e₂)) :
    W₁ = W₂ := by
  ext a
  -- Every element is the limit of ∑ a.val m • pure(ψ₁ᵢ, ψ₂ⱼ)
  have h_sum := hasSum_pure (E₁ := E₁) (E₂ := E₂) a
  -- Apply W₁ and W₂ to the hasSum
  have h₁ := h_sum.mapL W₁
  have h₂ := h_sum.mapL W₂
  -- The summands agree
  have h_eq : ∀ m,
      W₁ (a.val m • pure (DyninMityaginSpace.basis (Nat.unpair m).1)
                          (DyninMityaginSpace.basis (Nat.unpair m).2)) =
      W₂ (a.val m • pure (DyninMityaginSpace.basis (Nat.unpair m).1)
                          (DyninMityaginSpace.basis (Nat.unpair m).2)) := by
    intro m
    simp only [map_smul]
    congr 1
    exact h_pure _ _
  rw [← h₂.tsum_eq, ← h₁.tsum_eq]
  congr 1
  ext m
  exact h_eq m

/-- **Existence and uniqueness combined.**

Under `HasBiorthogonalBasis`, there is a *unique* CLM extending `B`
to the nuclear tensor product. -/
theorem nuclear_bilinear_extension_existsUnique [CompleteSpace G]
    (B : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] G)
    {C : ℝ} {s₁ : Finset (@DyninMityaginSpace.ι E₁ _ _ _ _ _ _)}
    {s₂ : Finset (@DyninMityaginSpace.ι E₂ _ _ _ _ _ _)}
    (hC : 0 < C)
    (hB : ∀ e₁ e₂, ‖B e₁ e₂‖ ≤ C * (s₁.sup DyninMityaginSpace.p) e₁ *
        (s₂.sup DyninMityaginSpace.p) e₂) :
    ∃! (W : NuclearTensorProduct E₁ E₂ →L[ℝ] G),
      ∀ (e₁ : E₁) (e₂ : E₂), W (pure e₁ e₂) = B e₁ e₂ := by
  refine ⟨lift B hC hB, lift_pure B hC hB, ?_⟩
  intro W' hW'
  exact nuclear_bilinear_extension_unique W' (lift B hC hB)
    (fun e₁ e₂ => by rw [hW', lift_pure])

end Uniqueness

/-! ## The n-linear case (documentation)

The n-linear nuclear extension theorem (for `n ≥ 3`) follows from the
bilinear case by induction. Given a separately continuous multilinear map
`Φ : E₁ × E₂ × ... × Eₙ → G`:

1. By induction, the restriction `Φ_{e₁} : E₂ × ... × Eₙ → G` extends
   to `W_{e₁} : E₂ ⊗̂ ... ⊗̂ Eₙ →L[ℝ] G` for each `e₁`.

2. The map `e₁ ↦ W_{e₁}` is continuous and linear, giving a bilinear map
   `E₁ × (E₂ ⊗̂ ... ⊗̂ Eₙ) → G`.

3. Applying the bilinear case yields
   `W : E₁ ⊗̂ (E₂ ⊗̂ ... ⊗̂ Eₙ) →L[ℝ] G`.

4. Associativity of the nuclear tensor product
   `E₁ ⊗̂ (E₂ ⊗̂ ... ⊗̂ Eₙ) ≅ E₁ ⊗̂ E₂ ⊗̂ ... ⊗̂ Eₙ`
   (which holds because both sides are `RapidDecaySeq` via iterated
   Cantor pairing) gives the final map.

This is not formalized here since the bilinear case suffices for the
Gaussian field construction (where we need `n = 2` for the covariance
bilinear form). -/

end GaussianField

end
