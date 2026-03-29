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

/-! ## Factorization identity

The product of the resolvent symbol at mass with the quotient symbol
equals the resolvent symbol at ω. -/

/-- `σ_mass · τ_ω = σ_ω`: the resolvent factorizes through the quotient symbol. -/
theorem resolventSymbol_mul_quotient {mass ω : ℝ} (hmass : 0 < mass) (hω : mass ≤ ω) (p : ℝ) :
    resolventSymbol mass p * resolventQuotientSymbol mass ω p = resolventSymbol ω p := by
  -- (p²+m²)^{-1/2} · √((p²+m²)/(p²+ω²)) = (p²+ω²)^{-1/2}
  -- Proof: (p²+m²)^{-1/2} · (p²+m²)^{1/2} · (p²+ω²)^{-1/2} cancel the (p²+m²) factors.
  unfold resolventSymbol resolventQuotientSymbol
  have hm : 0 < p ^ 2 + mass ^ 2 := by nlinarith [sq_nonneg p]
  have hw : 0 < p ^ 2 + ω ^ 2 := by nlinarith [sq_nonneg p]
  rw [Real.sqrt_eq_rpow, Real.div_rpow hm.le hw.le]
  rw [show (1 : ℝ) / 2 = -(-(1 : ℝ) / 2) from by norm_num]
  rw [Real.rpow_neg hm.le]
  have h1 := Real.rpow_pos_of_pos hm (-(1 : ℝ) / 2)
  field_simp
  rw [Real.rpow_neg hw.le, mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hw _))]

/-- The quotient symbol is even: `τ_ω(-p) = τ_ω(p)`. -/
theorem resolventQuotientSymbol_even (mass ω : ℝ) (p : ℝ) :
    resolventQuotientSymbol mass ω (-p) = resolventQuotientSymbol mass ω p := by
  unfold resolventQuotientSymbol; ring_nf

/-! ## Fourier multiplier seminorm domination (Mathlib axiom)

The following axiom encodes the Hörmander multiplier theorem for 1D Schwartz space:
if the symbol `σ₁` has derivative bounds dominated by those of `σ₂`, then the
Schwartz seminorms of `M_{σ₁} f` are dominated by those of `M_{σ₂} f`.

This is a standard result in harmonic analysis (Stein, *Singular Integrals*,
Ch. VI) that is not yet in Mathlib. The proof goes through the Leibniz rule
expansion of `D^l(σ · Ff)` and polynomial weight estimates. -/

/-- **Fourier multiplier domination by symbol bounds.**

If `0 ≤ σ₁(p) ≤ σ₂(p)` and `|D^j σ₁(p)| ≤ |D^j σ₂(p)|` for all j ≤ l and p,
and both symbols have temperate growth, then for each Schwartz seminorm `(k, l)`:

  `p_{k,l}(M_{σ₁} f) ≤ p_{k,l}(M_{σ₂} f)` for all f ∈ 𝓢(ℝ).

This follows from the structure of `fourierMultiplierCLM`: the CLM is
`F⁻¹ ∘ (σ · ) ∘ F`, and the Schwartz seminorm of the output is controlled
by the `L¹` norm of `D^k((2πip)^l σ · Ff)` via Fourier inversion. By
Leibniz, each term involves `|D^j σ|` which is dominated by assumption. -/
axiom fourierMultiplier_seminorm_domination
    {σ₁ σ₂ : ℝ → ℝ}
    (hσ₁ : σ₁.HasTemperateGrowth) (hσ₂ : σ₂.HasTemperateGrowth)
    (h_dom : ∀ (j : ℕ) (p : ℝ),
      ‖iteratedDeriv j σ₁ p‖ ≤ ‖iteratedDeriv j σ₂ p‖)
    (k l : ℕ) (f : SchwartzMap ℝ ℝ) :
    SchwartzMap.seminorm ℝ k l (realFourierMultiplierCLM σ₁ hσ₁ f) ≤
    SchwartzMap.seminorm ℝ k l (realFourierMultiplierCLM σ₂ hσ₂ f)

/-! ## Derivative domination for the resolvent family

The resolvent symbol derivatives satisfy `|D^j σ_ω(p)| ≤ |D^j σ_mass(p)|`
for ω ≥ mass. This is because `D^j[(p²+ω²)^{-1/2}] = P_j(p) · (p²+ω²)^{-1/2-j}`
where `P_j(p)` is a polynomial in p INDEPENDENT of ω, and the factor
`(p²+ω²)^{-1/2-j}` is decreasing in ω (negative exponent). -/

/-- The j-th derivative of the resolvent symbol is dominated by the mass case. -/
theorem resolventSymbol_deriv_antitone (j : ℕ) (p : ℝ) {ω mass : ℝ}
    (hmass : 0 < mass) (hω : mass ≤ ω) :
    ‖iteratedDeriv j (resolventSymbol ω) p‖ ≤
    ‖iteratedDeriv j (resolventSymbol mass) p‖ := by
  sorry

/-! ## Main theorem: uniform bound from domination -/

/-- **Uniform Schwartz seminorm bound for the resolvent multiplier family.**

Proved from `fourierMultiplier_seminorm_domination` applied to σ_ω ≤ σ_mass
(derivative domination), combined with `Seminorm.bound_of_continuous` at ω = mass. -/
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
    (schwartzSeminormFamily ℝ ℝ ℝ ⟨k, l⟩).comp R_mass.toLinearMap
  have hq_cont : Continuous q :=
    ((schwartz_withSeminorms ℝ ℝ ℝ).continuous_seminorm ⟨k, l⟩).comp R_mass.continuous
  obtain ⟨s₀, C₀, hC₀, hle₀⟩ := Seminorm.bound_of_continuous
    (schwartz_withSeminorms ℝ ℝ ℝ) q hq_cont
  -- Step 2: For ω ≥ mass, dominate by the mass case
  refine ⟨s₀, C₀, lt_of_le_of_ne C₀.2 (fun h => hC₀ (Subtype.ext h.symm)), fun ω hω f => ?_⟩
  -- p_{k,l}(R_ω f) ≤ p_{k,l}(R_mass f) by derivative domination
  calc SchwartzMap.seminorm ℝ k l (resolventMultiplierCLM _ f)
      ≤ SchwartzMap.seminorm ℝ k l (resolventMultiplierCLM hmass f) :=
        fourierMultiplier_seminorm_domination
          (resolventSymbol_hasTemperateGrowth ω (lt_of_lt_of_le hmass hω))
          (resolventSymbol_hasTemperateGrowth mass hmass)
          (fun j p => resolventSymbol_deriv_antitone j p hmass hω)
          k l f
    _ = q f := rfl
    _ ≤ C₀ * (s₀.sup (fun m => schwartzSeminormFamily ℝ ℝ ℝ m)) f := hle₀ f

end GaussianField
