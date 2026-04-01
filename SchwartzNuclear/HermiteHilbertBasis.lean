/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hermite Functions as a Hilbert Basis of L²(ℝ)

Constructs the Hermite functions `ψₙ` as a `HilbertBasis ℕ ℝ (Lp ℝ 2 volume)`
and derives the Parseval identity for the DM basis of SchwartzMap ℝ ℝ.

## Main results

- `hermiteHilbertBasis` — the Hermite functions as a HilbertBasis of L²(ℝ)
- `dm_coeff_eq_l2_inner` — DM coefficients = L² inner products with Hermite functions
- `dm_l2InnerProduct_eq_l2_inner` — DM ℓ² inner product = L² inner product on Schwartz functions

## Proof strategy

1. Embed `hermiteFunction n : ℝ → ℝ` into `Lp ℝ 2 volume` (Schwartz → MemLp)
2. Show orthonormality in L² (from `hermiteFunction_orthonormal`)
3. Show completeness (orthogonal complement = ⊥, from `hermiteFunction_complete`)
4. Construct `HilbertBasis` via `HilbertBasis.mkOfOrthogonalEqBot`
5. Apply `HilbertBasis.hasSum_inner_mul_inner` for Parseval

## References

- Thangavelu, *Lectures on Hermite and Laguerre Expansions*, Ch. 1
-/

import SchwartzNuclear.HermiteNuclear
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section

open MeasureTheory GaussianField

/-! ## Hermite functions in L² -/

/-- Hermite function `ψ_n` as an element of `Lp ℝ 2 volume`. -/
def hermiteFunctionLp (n : ℕ) : Lp ℝ 2 (volume : Measure ℝ) := by
  sorry -- needs: MemLp (hermiteFunction n) 2 volume + Lp.mk

/-- Hermite functions are orthonormal in L²(ℝ). -/
theorem hermiteFunctionLp_orthonormal :
    Orthonormal ℝ hermiteFunctionLp := by
  sorry -- from hermiteFunction_orthonormal + L² inner product

/-- Hermite functions are complete in L²(ℝ): orthogonal complement = ⊥. -/
theorem hermiteFunctionLp_ortho_eq_bot :
    (Submodule.span ℝ (Set.range hermiteFunctionLp))ᗮ = ⊥ := by
  sorry -- from hermiteFunction_complete + orthogonal complement characterization

/-- **Hermite functions form a Hilbert basis of L²(ℝ).** -/
def hermiteHilbertBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume : Measure ℝ)) :=
  HilbertBasis.mkOfOrthogonalEqBot
    hermiteFunctionLp_orthonormal
    hermiteFunctionLp_ortho_eq_bot

/-! ## Parseval identity for DM coefficients

The DM basis coefficients of `SchwartzMap ℝ ℝ` are the L² inner products
with Hermite functions. Combined with the Hilbert basis Parseval identity,
this gives: `∑ coeff_n(f) * coeff_n(g) = ∫ f * g` for Schwartz functions. -/

/-- DM coefficient = L² inner product with Hermite function.

  `coeff_n(f) = ∫ f(x) · ψ_n(x) dx` -/
theorem dm_coeff_eq_l2_integral (n : ℕ) (f : SchwartzMap ℝ ℝ) :
    DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) n f = ∫ x, f x * hermiteFunction n x := by
  sorry -- from the DM basis construction in SchwartzNuclear

/-- **Parseval for DM coefficients**: the ℓ² inner product of DM coefficients
equals the L² inner product of the functions.

  `∑ coeff_n(f) * coeff_n(g) = ∫ f(x) · g(x) dx`

This follows from `HilbertBasis.hasSum_inner_mul_inner` applied to the
Hermite Hilbert basis. -/
theorem dm_l2InnerProduct_eq_integral (f g : SchwartzMap ℝ ℝ) :
    ∑' n, DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) n f * DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) n g =
    ∫ x, f x * g x := by
  sorry -- from dm_coeff_eq_l2_integral + hermiteHilbertBasis.hasSum_inner_mul_inner

end
