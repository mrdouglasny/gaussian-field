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

/-! ## Hörmander multiplier theorem for S(ℝ)

The general Fourier multiplier Schwartz continuity theorem: a smooth symbol
with polynomially bounded derivatives gives a continuous operator on S(ℝ),
with seminorm bounds depending only on the derivative bound parameters.

The key property: the output constants `(s, C')` depend only on the input
parameters `(k, l, deriv_order, B, N)`, NOT on the specific symbol `σ`.
This gives uniform bounds for families of symbols with uniform derivative bounds.

Reference: Stein, *Singular Integrals*, Ch. VI. -/

/-- **Hörmander multiplier theorem for Schwartz space.**

For any smooth symbol σ : ℝ → ℝ with `|D^m σ(p)| ≤ B · (1 + |p|)^N` for m ≤ deriv_order,
the Fourier multiplier `M_σ` satisfies:

  `p_{k,l}(M_σ f) ≤ C' · q(f)`

where `C'` and `q` depend only on `(k, l, deriv_order, B, N)`, not on σ.

This enables uniform bounds for families: if `{σ_ω}` all satisfy the same derivative
bounds, the same `C'` and `q` work for all ω.

Note: for a useful bound on the `(k,l)`-seminorm, `deriv_order` should be at least `k`
(the Leibniz rule for `D^k(σ · Ff)` involves derivatives of σ up to order k). -/
axiom fourierMultiplier_schwartz_bound
    (k l deriv_order : ℕ) (B N : ℝ) :
    ∃ (s : Finset (ℕ × ℕ)) (C' : ℝ), 0 < C' ∧
    ∀ (σ : ℝ → ℝ) (hσ : σ.HasTemperateGrowth),
      (∀ (m : ℕ), m ≤ deriv_order →
        ∀ p : ℝ, ‖iteratedDeriv m σ p‖ ≤ B * (1 + |p|) ^ N) →
      ∀ f : SchwartzMap ℝ ℝ,
        SchwartzMap.seminorm ℝ k l (realFourierMultiplierCLM σ hσ f) ≤
        C' * (s.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2)) f

/-! ## Uniform resolvent bound from Hörmander theorem

The resolvent family `σ_ω(p) = (p² + ω²)^{-1/2}` for `ω ≥ mass > 0` has
uniform polynomial derivative bounds. The scaling identity
`σ_ω(p) = ω⁻¹ · σ₁(ω⁻¹ p)` reduces all derivative estimates to the fixed symbol
`σ₁`, and `σ₁` already has temperate growth by
`resolventSymbol_hasTemperateGrowth`. Applying
`fourierMultiplier_schwartz_bound` then yields the uniform seminorm bound. -/

/-- Scaling identity for the resolvent symbol. -/
private theorem resolventSymbol_scaling' {ω : ℝ} (hω : 0 < ω) :
    resolventSymbol ω = fun p => ω⁻¹ * resolventSymbol 1 (ω⁻¹ * p) := by
  funext p
  unfold resolventSymbol
  have hfact : p ^ 2 + ω ^ 2 = ω ^ 2 * ((ω⁻¹ * p) ^ 2 + 1 ^ 2) := by
    have hω0 : ω ≠ 0 := hω.ne'
    field_simp [hω0]
  rw [hfact, Real.mul_rpow (le_of_lt (sq_pos_of_pos hω)) (by positivity)]
  congr 1
  rw [show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
    Real.rpow_neg (sq_nonneg ω), ← Real.sqrt_eq_rpow, Real.sqrt_sq hω.le]

/-- Scaling of iterated derivatives of the resolvent symbol. -/
private theorem iteratedDeriv_resolventSymbol_scaling {ω : ℝ} (hω : 0 < ω) (m : ℕ) :
    iteratedDeriv m (resolventSymbol ω) =
      fun p => ω⁻¹ * (ω⁻¹) ^ m * iteratedDeriv m (resolventSymbol 1) (ω⁻¹ * p) := by
  have hcontTop := (resolventSymbol_hasTemperateGrowth 1 zero_lt_one).1
  have hcont : ContDiff ℝ m (resolventSymbol 1) := hcontTop.of_le
    (show (m : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) by
      exact_mod_cast (show (m : ℕ∞) ≤ (⊤ : ℕ∞) from le_top))
  funext p
  rw [resolventSymbol_scaling' hω]
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_comp_const_mul hcont ω⁻¹]
  ring

theorem resolventSymbol_uniform_deriv_bound (mass : ℝ) (hmass : 0 < mass) (deriv_order : ℕ) :
    ∃ (B : ℝ) (N : ℕ), 0 < B ∧ ∀ (ω : ℝ), mass ≤ ω →
      ∀ (m : ℕ), m ≤ deriv_order →
        ∀ p : ℝ, ‖iteratedDeriv m (resolventSymbol ω) p‖ ≤ B * (1 + |p|) ^ (N : ℝ) := by
  have hσ1 := resolventSymbol_hasTemperateGrowth 1 zero_lt_one
  obtain ⟨k, C, hC, hσ1_bound⟩ := hσ1.norm_iteratedFDeriv_le_uniform deriv_order
  let A : ℝ := max 1 (1 / mass)
  have hA : 1 ≤ A := le_max_left _ _
  have hA_nonneg : 0 ≤ A := le_trans zero_le_one hA
  have hAω : ∀ ω : ℝ, mass ≤ ω → 1 / ω ≤ A := by
    intro ω hω
    exact le_trans (div_le_div_of_nonneg_left one_pos.le hmass hω) (le_max_right _ _)
  refine ⟨(C + 1) * A ^ (deriv_order + 1 + k), k, ?_, ?_⟩
  · have hA_pos : 0 < A := lt_of_lt_of_le zero_lt_one hA
    positivity
  · intro ω hω m hm p
    have hω' : 0 < ω := lt_of_lt_of_le hmass hω
    have hσ1p : ‖iteratedDeriv m (resolventSymbol 1) (ω⁻¹ * p)‖ ≤
        C * (1 + |ω⁻¹ * p|) ^ k := by
      simpa [Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
        hσ1_bound m hm (ω⁻¹ * p)
    have hωinv_le : ω⁻¹ ≤ A := by
      simpa [one_div] using hAω ω hω
    have hp_scale : 1 + |ω⁻¹ * p| ≤ A * (1 + |p|) := by
      calc
        1 + |ω⁻¹ * p| = 1 + ω⁻¹ * |p| := by
          rw [abs_mul, abs_of_pos (inv_pos.mpr hω')]
        _ ≤ A + A * |p| := by
          gcongr
        _ = A * (1 + |p|) := by ring
    have hp_pow : (1 + |ω⁻¹ * p|) ^ k ≤ (A * (1 + |p|)) ^ k := by
      gcongr
    have hωpow : (ω⁻¹) ^ (m + 1) ≤ A ^ (deriv_order + 1) := by
      calc
        (ω⁻¹) ^ (m + 1) ≤ A ^ (m + 1) := by
          gcongr
        _ ≤ A ^ (deriv_order + 1) := by
          exact pow_le_pow_right₀ hA (Nat.succ_le_succ hm)
    have hAkpow : A ^ k ≤ A ^ (deriv_order + 1 + k) := by
      exact pow_le_pow_right₀ hA (Nat.le_add_left k (deriv_order + 1))
    have hAk : A ^ k * (1 + |p|) ^ (k : ℝ) ≤ A ^ (deriv_order + 1 + k) * (1 + |p|) ^ (k : ℝ) := by
      exact mul_le_mul_of_nonneg_right hAkpow (by positivity)
    calc
      ‖iteratedDeriv m (resolventSymbol ω) p‖
          = (ω⁻¹) ^ (m + 1) * ‖iteratedDeriv m (resolventSymbol 1) (ω⁻¹ * p)‖ := by
              rw [iteratedDeriv_resolventSymbol_scaling hω' m]
              rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
              have habsω : |ω| = ω := abs_of_pos hω'
              simp [habsω, abs_of_pos (inv_pos.mpr hω'), pow_succ, mul_assoc]
              ring
      _ ≤ (ω⁻¹) ^ (m + 1) * (C * (1 + |ω⁻¹ * p|) ^ k) := by
            gcongr
      _ ≤ A ^ (deriv_order + 1) * (C * (A * (1 + |p|)) ^ k) := by
            gcongr
      _ = C * A ^ (deriv_order + 1 + k) * (1 + |p|) ^ (k : ℝ) := by
            rw [mul_pow]
            rw [show (1 + |p|) ^ k = (1 + |p|) ^ (k : ℝ) by rw [Real.rpow_natCast]]
            ring
      _ ≤ (C + 1) * A ^ (deriv_order + 1 + k) * (1 + |p|) ^ (k : ℝ) := by
            gcongr
            linarith

theorem resolventSchwartz_uniformBound
    (mass : ℝ) (hmass : 0 < mass) (k l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ) (_ : 0 < C),
    ∀ (ω : ℝ) (hω : mass ≤ ω) (f : SchwartzMap ℝ ℝ),
      SchwartzMap.seminorm ℝ k l
        (resolventMultiplierCLM (lt_of_lt_of_le hmass (show mass ≤ ω from hω)) f) ≤
      C * (s.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2)) f := by
  -- Step 1: Get uniform derivative bounds for the resolvent family
  obtain ⟨B, N, hB, h_deriv⟩ := resolventSymbol_uniform_deriv_bound mass hmass (k + l)
  -- Step 2: Apply the Hörmander multiplier theorem with these bounds
  obtain ⟨s, C', hC', h_mult⟩ := fourierMultiplier_schwartz_bound k l (k + l) B N
  -- Step 3: Package
  refine ⟨s, C', hC', fun ω hω f => ?_⟩
  -- resolventMultiplierCLM hω' = realFourierMultiplierCLM (resolventSymbol ω) hσ
  have hω' := lt_of_lt_of_le hmass hω
  show SchwartzMap.seminorm ℝ k l (resolventMultiplierCLM hω' f) ≤ _
  rw [show resolventMultiplierCLM hω' =
    realFourierMultiplierCLM (resolventSymbol ω)
      (resolventSymbol_hasTemperateGrowth ω hω') from rfl]
  exact h_mult (resolventSymbol ω) (resolventSymbol_hasTemperateGrowth ω hω')
    (h_deriv ω hω) f

end GaussianField
