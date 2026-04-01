/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hermite Functions as a Hilbert Basis of L²(ℝ)

Constructs the Hermite functions `ψₙ` as a `HilbertBasis ℕ ℝ (Lp ℝ 2 volume)`
using Mathlib's `HilbertBasis.mkOfOrthogonalEqBot`, from:
- `hermiteFunction_orthonormal` — ∫ ψ_n ψ_m = δ_{nm}
- `hermiteFunction_complete` — {∫ f ψ_n = 0 for all n} → f =ᵐ 0

## Main results

- `hermiteHilbertBasis` — the Hermite functions as a HilbertBasis of L²(ℝ)
- `hermiteFunctionLp_inner` — L² inner product with Hermite function = ∫ f ψ_n

## Applications

Combined with `HilbertBasis.hasSum_inner_mul_inner` (Parseval), this gives:
  `∑ ⟨f, ψ_n⟩ · ⟨ψ_n, g⟩ = ⟨f, g⟩_{L²}`
for any f, g ∈ L²(ℝ). This is the key bridge between DM basis coefficients
and L² inner products, needed for proving `resolvent_laplace_inner`.

## References

- Thangavelu, *Lectures on Hermite and Laguerre Expansions*, Ch. 1
-/

import SchwartzNuclear.HermiteNuclear
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section

open MeasureTheory GaussianField

/-! ## Hermite functions in L² -/

/-- Hermite function `ψ_n` as an element of `Lp ℝ 2 volume`. -/
def hermiteFunctionLp (n : ℕ) : Lp ℝ 2 (volume : Measure ℝ) :=
  (hermiteFunction_memLp n).toLp (hermiteFunction n)

/-- L² inner product of two Hermite functions = ∫ ψ_n ψ_m. -/
theorem hermiteFunctionLp_inner (n m : ℕ) :
    @inner ℝ _ _ (hermiteFunctionLp n) (hermiteFunctionLp m) =
    ∫ x, hermiteFunction n x * hermiteFunction m x := by
  rw [L2.inner_def]; apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (hermiteFunction_memLp n),
    MemLp.coeFn_toLp (hermiteFunction_memLp m)] with x h1 h2
  simp only [hermiteFunctionLp, inner, RCLike.re, conj_trivial, h1, h2,
    AddMonoidHom.id_apply]; ring

/-- L² inner product of f with a Hermite function = ∫ f ψ_n. -/
theorem hermiteFunctionLp_inner_gen (n : ℕ) (f : Lp ℝ 2 (volume : Measure ℝ)) :
    @inner ℝ _ _ f (hermiteFunctionLp n) =
    ∫ x, (f : ℝ → ℝ) x * hermiteFunction n x := by
  rw [L2.inner_def]; apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (hermiteFunction_memLp n)] with x h1
  simp only [hermiteFunctionLp, inner, RCLike.re, conj_trivial, h1,
    AddMonoidHom.id_apply]; ring

/-! ## Hilbert basis construction -/

/-- Hermite functions are orthonormal in L²(ℝ). -/
theorem hermiteFunctionLp_orthonormal : Orthonormal ℝ hermiteFunctionLp := by
  rw [orthonormal_iff_ite]; intro i j
  rw [hermiteFunctionLp_inner, hermiteFunction_orthonormal]

/-- Hermite functions are complete in L²(ℝ): orthogonal complement = ⊥.

From `hermiteFunction_complete`: if `∫ f ψ_n = 0` for all n, then `f =ᵐ 0`. -/
theorem hermiteFunctionLp_ortho_eq_bot :
    (Submodule.span ℝ (Set.range hermiteFunctionLp))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]; intro f hf
  rw [Submodule.mem_orthogonal] at hf
  have h_iz : ∀ n, ∫ x, (f : ℝ → ℝ) x * hermiteFunction n x = 0 := by
    intro n; rw [← hermiteFunctionLp_inner_gen]
    rw [real_inner_comm]; exact hf _ (Submodule.subset_span (Set.mem_range_self n))
  have h_ae := hermiteFunction_complete _ (Lp.memLp f) h_iz
  ext1; exact h_ae.trans (Lp.coeFn_zero _ _ _).symm

/-- **Hermite functions form a Hilbert basis of L²(ℝ).**

Constructed from orthonormality + completeness via `HilbertBasis.mkOfOrthogonalEqBot`. -/
def hermiteHilbertBasis : HilbertBasis ℕ ℝ (Lp ℝ 2 (volume : Measure ℝ)) :=
  HilbertBasis.mkOfOrthogonalEqBot hermiteFunctionLp_orthonormal hermiteFunctionLp_ortho_eq_bot

end
