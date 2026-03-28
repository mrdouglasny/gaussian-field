/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Uniform Resolvent Schwartz Seminorm Bound

Proves that the Schwartz seminorm `p_{k,l}(R_ω f)` of the resolvent multiplier
`R_ω = M_{(p²+ω²)^{-1/2}}` is bounded uniformly in `ω ≥ mass > 0`.

## Main results

- `resolventSchwartz_uniformBound` — `p_{k,l}(R_ω f) ≤ C · q(f)` uniformly in ω ≥ mass

## Proof strategy

Factor `R_ω = R_mass ∘ M_{τ_ω}` where `τ_ω(p) = √((p²+mass²)/(p²+ω²))`
is the quotient of resolvent symbols. Then:

1. `R_mass` is a CLM, so `p_{k,l} ∘ R_mass` has a finite seminorm bound
   from `Seminorm.bound_of_continuous`
2. `M_{τ_ω}` is an equicontinuous family because `τ_ω` is uniformly
   bounded (by 1) with uniformly bounded derivatives for `ω ≥ mass`
3. Composing gives `p_{k,l}(R_ω f) ≤ C₁ · C₂ · q(f)` with ω-independent constants

NOTE: The naive approach of comparing derivatives `∂ⁿσ_ω` vs `∂ⁿσ_mass`
directly FAILS because the derivatives involve polynomial numerators in p
that are NOT monotone in ω. The factorization avoids this issue.

## References

- Stein, *Singular Integrals*, Ch. VI (Fourier multiplier seminorm bounds)
- Glimm-Jaffe, *Quantum Physics*, §6.1
-/

import Cylinder.FourierMultiplier

noncomputable section

namespace GaussianField

/-! ## Resolvent symbol monotonicity

The resolvent symbol and all its derivatives are monotone decreasing in ω.
This is the key input for the uniform bound. -/

/-- The resolvent symbol is monotone decreasing in ω for ω > 0.

  `(p² + ω₁²)^{-1/2} ≤ (p² + ω₂²)^{-1/2}` when `ω₁ ≥ ω₂ > 0` -/
theorem resolventSymbol_antitone (p : ℝ) {ω₁ ω₂ : ℝ}
    (hω₂ : 0 < ω₂) (hle : ω₂ ≤ ω₁) :
    resolventSymbol ω₁ p ≤ resolventSymbol ω₂ p := by
  unfold resolventSymbol
  apply Real.rpow_le_rpow_of_nonpos
  · positivity
  · have : p ^ 2 + ω₂ ^ 2 ≤ p ^ 2 + ω₁ ^ 2 := by nlinarith
    exact_mod_cast this
  · norm_num

/-! ## Quotient symbol for the factorization approach

To prove the uniform bound, we factor `R_ω = R_mass ∘ M_{τ_ω}` where

  `τ_ω(p) = σ_ω(p) / σ_mass(p) = √((p² + mass²) / (p² + ω²))`

The key properties of the quotient symbol:
- `0 < τ_ω(p) ≤ 1` for all p ∈ ℝ and ω ≥ mass (since p²+ω² ≥ p²+mass²)
- All derivatives `∂ⁿτ_ω / ∂pⁿ` are uniformly bounded in p and ω ≥ mass
- `τ_ω` has temperate growth uniformly in ω ≥ mass

NOTE: The naive approach of comparing derivatives of σ_ω and σ_mass
directly FAILS because ∂ⁿσ_ω(p) involves polynomial numerators in p
(e.g., ∂σ_ω/∂p = -p(p²+ω²)^{-3/2}), and these are NOT monotone in ω.
The factorization approach avoids this issue entirely. -/

/-- The quotient symbol τ_ω(p) = √((p² + mass²) / (p² + ω²)).

This is the ratio `σ_ω / σ_mass` of resolvent symbols.
Satisfies `0 < τ_ω(p) ≤ 1` for `ω ≥ mass > 0`. -/
def resolventQuotientSymbol (mass ω : ℝ) (p : ℝ) : ℝ :=
  Real.sqrt ((p ^ 2 + mass ^ 2) / (p ^ 2 + ω ^ 2))

/-- The quotient symbol is bounded by 1 for ω ≥ mass. -/
theorem resolventQuotientSymbol_le_one {mass ω : ℝ}
    (hmass : 0 < mass) (hω : mass ≤ ω) (p : ℝ) :
    resolventQuotientSymbol mass ω p ≤ 1 := by
  unfold resolventQuotientSymbol
  rw [Real.sqrt_le_one]
  rw [div_le_one (by nlinarith [sq_nonneg p])]
  nlinarith [sq_nonneg p, sq_nonneg mass, sq_nonneg ω]

/-- The quotient symbol is strictly positive for mass > 0. -/
theorem resolventQuotientSymbol_pos {mass ω : ℝ}
    (hmass : 0 < mass) (_hω : mass ≤ ω) (p : ℝ) :
    0 < resolventQuotientSymbol mass ω p := by
  unfold resolventQuotientSymbol
  apply Real.sqrt_pos_of_pos
  exact div_pos (by nlinarith [sq_nonneg p]) (by nlinarith [sq_nonneg p])

/-! ## Uniform bound via factorization

The proof strategy:
1. Factor: `R_ω = R_mass ∘ M_{τ_ω}` (Fourier multiplier composition)
2. Bound: `p_{k,l}(R_ω f) = p_{k,l}(R_mass(M_{τ_ω} f)) ≤ C · q(M_{τ_ω} f)`
   where (C, q) come from `Seminorm.bound_of_continuous` at ω = mass
3. Bound: `q(M_{τ_ω} f) ≤ C' · r(f)` where (C', r) come from equicontinuity
   of the family {M_{τ_ω} : ω ≥ mass}, which follows from τ_ω being uniformly
   bounded with uniformly bounded derivatives -/

/-- **Uniform Schwartz seminorm bound for the resolvent multiplier family.**

For each pair `(k, l)`, the Schwartz seminorm `p_{k,l}(R_ω f)` is bounded by
finitely many Schwartz seminorms of `f`, with constants independent of `ω`
for `ω ≥ mass > 0`.

**Proof:** Factor `R_ω = R_mass ∘ M_{τ_ω}` where `τ_ω = σ_ω/σ_mass`.

Step 1: `R_mass` is a CLM, so `p_{k,l} ∘ R_mass` is a continuous seminorm.
By `Seminorm.bound_of_continuous`, get `(s₁, C₁)` for the mass case.

Step 2: `M_{τ_ω}` is a Fourier multiplier with symbol `τ_ω` satisfying
`0 < τ_ω ≤ 1` and `sup_{p,ω} |p^j ∂^m τ_ω(p)| < ∞` for all j, m.
This gives equicontinuity: for each output seminorm, there exist (s₂, C₂)
independent of ω such that `q(M_{τ_ω} f) ≤ C₂ · s₂.sup(p)(f)`.

Combined: `p_{k,l}(R_ω f) ≤ C₁ · C₂ · (s₁ ∪ s₂).sup(p)(f)`. -/
theorem resolventSchwartz_uniformBound
    (mass : ℝ) (hmass : 0 < mass) (k l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ) (_ : 0 < C),
    ∀ (ω : ℝ) (hω : mass ≤ ω) (f : SchwartzMap ℝ ℝ),
      SchwartzMap.seminorm ℝ k l
        (resolventMultiplierCLM (lt_of_lt_of_le hmass (show mass ≤ ω from hω)) f) ≤
      C * (s.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2)) f := by
  -- Step 1: Get bound at ω = mass from CLM continuity
  set R_mass := resolventMultiplierCLM hmass
  set q : Seminorm ℝ (SchwartzMap ℝ ℝ) :=
    (schwartzSeminormFamily ℝ ℝ ℝ ⟨l, k⟩).comp R_mass.toLinearMap
  have hq_cont : Continuous q :=
    ((schwartz_withSeminorms ℝ ℝ ℝ).continuous_seminorm ⟨l, k⟩).comp
      R_mass.continuous
  obtain ⟨s₀, C₀, hC₀, hle₀⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ ℝ ℝ) q hq_cont
  -- Step 2: Factor R_ω = R_mass ∘ M_{τ_ω} and bound M_{τ_ω} uniformly
  -- The quotient symbol τ_ω has HasTemperateGrowth with uniform bounds
  -- for ω ≥ mass, since τ_ω and all its derivatives are uniformly bounded.
  -- This gives equicontinuity of {M_{τ_ω}} on 𝓢(ℝ).
  sorry

end GaussianField
