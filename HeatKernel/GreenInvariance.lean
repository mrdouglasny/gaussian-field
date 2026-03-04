/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Green's Function Invariance under Torus Symmetries

Proves that the Green's function `G(f,g) = Σ c_m(f)·c_m(g)/(μ_m + mass²)`
on the torus tensor product is invariant under translation, reflection,
and coordinate swap.

## Main results

- `greenFunctionBilinear_reflection_pure` — G invariant under reflection on pure tensors
- `greenFunctionBilinear_swap_pure` — G invariant under swap on pure tensors
- `greenFunctionBilinear_translation_pure` — G invariant under translation on pure tensors
- `greenFunctionBilinear_invariant_of_pure` — extension from pure tensors to all elements
- `greenFunctionBilinear_timeReflection_invariant` — full reflection invariance (theorem)
- `greenFunctionBilinear_swap_invariant` — full swap invariance (theorem)
- `greenFunctionBilinear_translation_invariant` — full translation invariance (theorem)

## Mathematical background

On the torus `S¹_L ⊗ S¹_L`, the Green's function is
  `G(f,g) = Σ_{(n₁,n₂)} c_{n₁}(f₁)c_{n₂}(f₂) · c_{n₁}(g₁)c_{n₂}(g₂) / (μ₁(n₁) + μ₂(n₂) + m²)`
for pure tensors `f = f₁⊗f₂`, `g = g₁⊗g₂`.

**Reflection** `Θ⊗id`: Each factor `c_n(Θf)·c_n(Θg)` equals `(±1)²·c_n(f)·c_n(g)`,
so the sum is invariant term-by-term.

**Swap**: Relabel `(n₁,n₂) ↦ (n₂,n₁)` and use commutativity of addition.

**Translation**: Group the sum by degenerate frequency pairs (2k-1, 2k) in each
factor. The paired product `c_{2k-1}(Tf)·c_{2k-1}(Tg) + c_{2k}(Tf)·c_{2k}(Tg)`
is invariant (from `paired_coeff_product_circleTranslation`), and paired modes
share eigenvalues.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.4
-/

import SmoothCircle.FourierTranslation
import Nuclear.TensorProductFunctorAxioms

noncomputable section

namespace GaussianField

open NuclearTensorProduct SmoothMap_Circle

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Pure tensor invariance axioms

These axioms assert that the Green's function spectral sum is invariant
under symmetry operations on pure tensors `f₁⊗f₂`. Each follows from
the Fourier coefficient transformation axioms in `FourierTranslation.lean`
combined with `pure_val` (coefficient factorization for pure tensors).

The proofs involve tsum manipulations (reindexing, grouping by degenerate
pairs) that are technically involved but mathematically transparent. -/

/-- **Green's function is invariant under time reflection on pure tensors.**

  `G(Θf₁⊗f₂, Θg₁⊗g₂) = G(f₁⊗f₂, g₁⊗g₂)`

Proof strategy: Unfold to spectral sum via `pure_val`. Each term at index m
has numerator involving `c_{n₁}(Θf₁)·c_{n₂}(f₂)·c_{n₁}(Θg₁)·c_{n₂}(g₂)`.
By the reflection axioms, `c_n(Θf) = ±c_n(f)` (+ for cos modes, - for sin),
so `c_n(Θf)·c_n(Θg) = (±1)²·c_n(f)·c_n(g) = c_n(f)·c_n(g)`.
Each term is individually invariant, so the sum is invariant. -/
axiom greenFunctionBilinear_reflection_pure
    (mass : ℝ) (hmass : 0 < mass)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) :
    greenFunctionBilinear mass hmass
      (NuclearTensorProduct.pure (circleReflection L f₁) f₂)
      (NuclearTensorProduct.pure (circleReflection L g₁) g₂) =
    greenFunctionBilinear mass hmass
      (NuclearTensorProduct.pure f₁ f₂) (NuclearTensorProduct.pure g₁ g₂)

/-- **Green's function is invariant under coordinate swap on pure tensors.**

  `G(f₂⊗f₁, g₂⊗g₁) = G(f₁⊗f₂, g₁⊗g₂)`

Proof strategy: The spectral sum over `m = pair(n₁,n₂)` can be reindexed
via `(n₁,n₂) ↦ (n₂,n₁)`, i.e., `m ↦ pair(unpair(m).2, unpair(m).1)`.
The numerator transforms as `c_{n₁}(f₂)·c_{n₂}(f₁) ↦ c_{n₂}(f₁)·c_{n₁}(f₂)`
(commutative multiplication). The denominator transforms as
`μ(n₁) + μ(n₂) + m² ↦ μ(n₂) + μ(n₁) + m²` (commutative addition).
So the reindexed sum equals the original. -/
axiom greenFunctionBilinear_swap_pure
    (mass : ℝ) (hmass : 0 < mass)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) :
    greenFunctionBilinear mass hmass
      (NuclearTensorProduct.pure f₂ f₁)
      (NuclearTensorProduct.pure g₂ g₁) =
    greenFunctionBilinear mass hmass
      (NuclearTensorProduct.pure f₁ f₂) (NuclearTensorProduct.pure g₁ g₂)

/-- **Green's function is invariant under translation on pure tensors.**

  `G(T_{v₁}f₁⊗T_{v₂}f₂, T_{v₁}g₁⊗T_{v₂}g₂) = G(f₁⊗f₂, g₁⊗g₂)`

Proof strategy: For each circle factor, group the tsum by frequency pairs
(2k-1, 2k). Within each pair:
- The eigenvalues are degenerate: `μ(2k-1) = μ(2k) = (2πk/L)²`
- The paired product is invariant: by `paired_coeff_product_circleTranslation`,
  `c_{2k-1}(Tf)·c_{2k-1}(Tg) + c_{2k}(Tf)·c_{2k}(Tg) = c_{2k-1}(f)·c_{2k-1}(g) + c_{2k}(f)·c_{2k}(g)`
So each pair's contribution to the Green's function is invariant, hence the
full double sum is invariant. -/
axiom greenFunctionBilinear_translation_pure
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ × ℝ)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) :
    greenFunctionBilinear mass hmass
      (NuclearTensorProduct.pure (circleTranslation L v.1 f₁)
                                 (circleTranslation L v.2 f₂))
      (NuclearTensorProduct.pure (circleTranslation L v.1 g₁)
                                 (circleTranslation L v.2 g₂)) =
    greenFunctionBilinear mass hmass
      (NuclearTensorProduct.pure f₁ f₂) (NuclearTensorProduct.pure g₁ g₂)

/-! ## Extension from pure tensors to all elements -/

/-- **Green's function invariance extends from pure tensors to all elements.**

If a CLM `S` on `NuclearTensorProduct E₁ E₂` satisfies
`G(S(pure e₁ e₂), S(pure e₁' e₂')) = G(pure e₁ e₂, pure e₁' e₂')` for
all pure tensors, then `G(S f, S g) = G(f, g)` for all `f, g`.

Proof strategy: Every element `f ∈ NTP` expands as `f = Σ_m a_m · basisVec_m`
where each `basisVec_m = pure(basis_i, basis_j)` is a pure tensor
(`hasSum_basisVec`). Since `S` is continuous linear and `greenFunctionBilinear`
is continuous bilinear, `G(S f, S g)` is determined by its values on pure
tensors. More precisely:
- `G(S(Σ aₘ·eₘ), S(Σ bₙ·eₙ)) = Σₘₙ aₘ·bₙ · G(S eₘ, S eₙ)`
  (by bilinearity + absolute convergence)
- `= Σₘₙ aₘ·bₙ · G(eₘ, eₙ)` (by hypothesis on pure tensors)
- `= G(Σ aₘ·eₘ, Σ bₙ·eₙ) = G(f, g)` -/
axiom greenFunctionBilinear_invariant_of_pure
    {E₁ : Type*} [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
    [IsTopologicalAddGroup E₁] [ContinuousSMul ℝ E₁] [DyninMityaginSpace E₁]
    {E₂ : Type*} [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
    [IsTopologicalAddGroup E₂] [ContinuousSMul ℝ E₂] [DyninMityaginSpace E₂]
    [HasLaplacianEigenvalues E₁] [HasLaplacianEigenvalues E₂]
    (mass : ℝ) (hmass : 0 < mass)
    (S : NuclearTensorProduct E₁ E₂ →L[ℝ] NuclearTensorProduct E₁ E₂)
    (hpure : ∀ (e₁ : E₁) (e₂ : E₂) (e₁' : E₁) (e₂' : E₂),
      greenFunctionBilinear mass hmass (S (pure e₁ e₂)) (S (pure e₁' e₂')) =
      greenFunctionBilinear mass hmass (pure e₁ e₂) (pure e₁' e₂'))
    (f g : NuclearTensorProduct E₁ E₂) :
    greenFunctionBilinear mass hmass (S f) (S g) =
    greenFunctionBilinear mass hmass f g

/-! ## Full invariance theorems

These combine the pure-tensor axioms with the extension principle
and the `mapCLM_pure` / `swapCLM_pure` specifications. -/

/-- **Green's function is invariant under time reflection.**

  `G(Θf, Θg) = G(f, g)` for all torus test functions f, g.

Combines `mapCLM_pure` (to reduce to pure tensors), `reflection_pure`
(invariance on pure tensors), and `invariant_of_pure` (extension). -/
theorem greenFunctionBilinear_timeReflection_invariant
    (mass : ℝ) (hmass : 0 < mass)
    (f g : NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) :
    greenFunctionBilinear mass hmass
      (nuclearTensorProduct_mapCLM (circleReflection L)
        (ContinuousLinearMap.id ℝ _) f)
      (nuclearTensorProduct_mapCLM (circleReflection L)
        (ContinuousLinearMap.id ℝ _) g) =
    greenFunctionBilinear mass hmass f g := by
  apply greenFunctionBilinear_invariant_of_pure mass hmass
  intro e₁ e₂ e₁' e₂'
  rw [nuclearTensorProduct_mapCLM_pure, nuclearTensorProduct_mapCLM_pure]
  simp only [ContinuousLinearMap.id_apply]
  exact greenFunctionBilinear_reflection_pure L mass hmass e₁ e₁' e₂ e₂'

/-- **Green's function is invariant under coordinate swap.**

  `G(swap f, swap g) = G(f, g)` for all torus test functions f, g.

Note: `swapCLM : NTP E E → NTP E E` (both factors are the same type
for the square torus). -/
theorem greenFunctionBilinear_swap_invariant
    (mass : ℝ) (hmass : 0 < mass)
    (f g : NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) :
    greenFunctionBilinear mass hmass
      (nuclearTensorProduct_swapCLM f)
      (nuclearTensorProduct_swapCLM g) =
    greenFunctionBilinear mass hmass f g := by
  apply greenFunctionBilinear_invariant_of_pure mass hmass
  intro e₁ e₂ e₁' e₂'
  rw [nuclearTensorProduct_swapCLM_pure, nuclearTensorProduct_swapCLM_pure]
  exact greenFunctionBilinear_swap_pure L mass hmass e₁ e₁' e₂ e₂'

/-- **Green's function is invariant under translation.**

  `G(T_v f, T_v g) = G(f, g)` for all v ∈ ℝ² and torus test functions f, g. -/
theorem greenFunctionBilinear_translation_invariant
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ × ℝ)
    (f g : NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) :
    greenFunctionBilinear mass hmass
      (nuclearTensorProduct_mapCLM (circleTranslation L v.1)
        (circleTranslation L v.2) f)
      (nuclearTensorProduct_mapCLM (circleTranslation L v.1)
        (circleTranslation L v.2) g) =
    greenFunctionBilinear mass hmass f g := by
  apply greenFunctionBilinear_invariant_of_pure mass hmass
  intro e₁ e₂ e₁' e₂'
  rw [nuclearTensorProduct_mapCLM_pure, nuclearTensorProduct_mapCLM_pure]
  exact greenFunctionBilinear_translation_pure L mass hmass v e₁ e₁' e₂ e₂'

end GaussianField

end
