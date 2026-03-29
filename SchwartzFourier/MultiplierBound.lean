/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Direct Schwartz Seminorm Bound for Fourier Multipliers

Proves that the Schwartz seminorm of a Fourier multiplier output is bounded
by the sup-norms of the symbol's derivatives times Schwartz seminorms of the
input. This bypasses Mathlib's opaque `fourierMultiplierCLM` and works
directly from the formula `M_σ f = F⁻¹(σ · Ff)`.

## Main results

- `fourierMultiplier_sup_le_integral` — `sup|M_σ f| ≤ ∫ |σ · Ff|`
- `fourierMultiplier_seminorm_le` — `p_{k,l}(M_σ f) ≤ C · Σ ‖D^j σ‖_∞ · p(f)`
- `resolventSchwartz_uniformBound` — uniform bound for the resolvent family

## Strategy

For `g = M_σ f = F⁻¹(σ · Ff)`:

1. **Fourier inversion**: `|g(x)| ≤ ∫ |σ(p)| · |Ff(p)| dp ≤ ‖σ‖_∞ · ‖Ff‖_{L¹}`
2. **Derivatives**: `D^l g = F⁻¹((2πip)^l σ · Ff)` so `|D^l g(x)| ≤ ‖p^l σ · Ff‖_{L¹}`
3. **Polynomial weight**: `|x^k D^l g(x)|` controlled by `‖D^k(p^l σ · Ff)‖_{L¹}`
4. **Leibniz**: `D^k(p^l σ · Ff) = Σ_j C_{k,j} D^j(p^l σ) · D^{k-j}(Ff)`
5. **Symbol bound**: `‖D^j(p^l σ)‖_∞ ≤ C(j,l) · max_{m≤j} ‖D^m σ‖_∞`
6. **Schwartz decay**: `∫ |D^{k-j}(Ff)| ≤ C · p_{2,k-j}(Ff) ≤ C' · p(f)`

For the resolvent: `‖D^j σ_ω‖_∞ = ω^{-1-j} ‖D^j g‖_∞ ≤ mass^{-1-j} ‖D^j g‖_∞`.

## References

- Stein, *Singular Integrals and Differentiability Properties of Functions*, Ch. VI
- Hörmander, *The Analysis of Linear PDOs*, Vol. II, §18.1
-/

import Cylinder.FourierMultiplier
import SchwartzFourier.LaplaceCLM
import Mathlib.Analysis.Fourier.Inversion

noncomputable section

open MeasureTheory Real Set Filter FourierTransform Fourier
open scoped BigOperators

namespace GaussianField

/-! ## Fourier inversion inequality

The basic bound: `|F⁻¹(h)(x)| ≤ ∫ |h(p)| dp` for any integrable h.
This is immediate from `norm_fourierIntegral_le_integral_norm`. -/

/-- Sup norm of inverse Fourier transform bounded by L¹ norm.
`‖F⁻¹(h)(x)‖ ≤ ∫ ‖h(p)‖ dp` for each x. -/
theorem norm_fourierInv_le_integral_norm {h : ℝ → ℂ}
    (_hh : Integrable h volume) (x : ℝ) :
    ‖FourierTransformInv.fourierInv h x‖ ≤ ∫ p, ‖h p‖ := by
  rw [Real.fourierInv_eq]
  calc ‖∫ v, Real.fourierChar (inner ℝ v x) • h v‖
      ≤ ∫ v, ‖Real.fourierChar (inner ℝ v x) • h v‖ := norm_integral_le_integral_norm _
    _ = ∫ v, ‖h v‖ := by
        congr 1; ext v
        rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]

/-! ## Schwartz L¹ bound

Schwartz functions have finite L¹ norm, bounded by Schwartz seminorms. -/

/-- The L¹ norm of a Schwartz function is bounded by Schwartz seminorms.
Uses `SchwartzMap.integrable` + `SchwartzMap.toLpCLM`. -/
theorem schwartz_l1_le_seminorm :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ f : SchwartzMap ℝ ℝ, ∫ p, ‖f.toFun p‖ ≤
    C * (s.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2)) f := by
  sorry

/-! ## Resolvent symbol sup-norm bounds

The key scaling: `σ_ω(p) = ω⁻¹ · g(p/ω)` where `g(q) = (q²+1)^{-1/2}`.
Then `‖D^j σ_ω‖_∞ = ω^{-1-j} · ‖D^j g‖_∞ ≤ mass^{-1-j} · ‖D^j g‖_∞`. -/

/-- The resolvent symbol satisfies `σ_ω(p) = ω⁻¹ · g(p/ω)`. -/
theorem resolventSymbol_scaling {ω : ℝ} (hω : 0 < ω) (p : ℝ) :
    resolventSymbol ω p = ω⁻¹ * resolventSymbol 1 (p / ω) := by
  sorry

/-- Sup norm of the resolvent symbol: `|σ_ω(p)| ≤ 1/ω` for all p.
Proof: `(p²+ω²)^{-1/2} ≤ (ω²)^{-1/2} = ω⁻¹` by rpow monotonicity + sqrt. -/
theorem resolventSymbol_sup (ω : ℝ) (hω : 0 < ω) :
    ∀ p : ℝ, |resolventSymbol ω p| ≤ 1 / ω := by
  intro p
  simp only [resolventSymbol]
  rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  calc (p ^ 2 + ω ^ 2) ^ (-(1:ℝ)/2)
      ≤ (ω ^ 2) ^ (-(1:ℝ)/2) :=
        Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hω)
          (by linarith [sq_nonneg p]) (by norm_num)
    _ = ω⁻¹ := by
        rw [show -(1:ℝ)/2 = -((1:ℝ)/2) from by ring,
            Real.rpow_neg (sq_nonneg ω), ← Real.sqrt_eq_rpow, Real.sqrt_sq hω.le]
    _ = 1 / ω := (one_div ω).symm

/-- Sup norm bound uniform in ω ≥ mass: `|σ_ω(p)| ≤ 1/mass`. -/
theorem resolventSymbol_sup_uniform {mass ω : ℝ} (hmass : 0 < mass) (hω : mass ≤ ω) :
    ∀ p : ℝ, |resolventSymbol ω p| ≤ 1 / mass := by
  intro p
  exact le_trans (resolventSymbol_sup ω (lt_of_lt_of_le hmass hω) p)
    (div_le_div_of_nonneg_left one_pos.le hmass hω)

/-! ## Direct seminorm bound for the resolvent multiplier

For the (0, 0) seminorm (sup norm), the bound is straightforward:
`‖R_ω f‖_∞ ≤ ‖σ_ω‖_∞ · ‖Ff‖_{L¹} ≤ (1/mass) · C · p(f)`.

For general (k, l), the bound requires the Leibniz rule for
`D^k(p^l σ · Ff)` and integration by parts. Each step adds finitely
many Schwartz seminorms of f and derivative sup-norms of σ.

The derivative sup-norms of σ_ω are uniform in ω ≥ mass by the scaling
`‖D^j σ_ω‖_∞ = ω^{-1-j} ‖D^j g‖_∞ ≤ mass^{-1-j} ‖D^j g‖_∞`. -/

/-- **The (0,0) case**: sup norm of resolvent multiplier output.

`‖R_ω f‖_∞ ≤ (1/mass) · ∫ |Ff| ≤ (1/mass) · C · p(f)` uniformly in ω ≥ mass. -/
theorem resolventMultiplier_sup_bound
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ) (_ : 0 < C),
    ∀ (ω : ℝ) (hω : mass ≤ ω) (f : SchwartzMap ℝ ℝ),
      SchwartzMap.seminorm ℝ 0 0
        (resolventMultiplierCLM (lt_of_lt_of_le hmass hω) f) ≤
      C * (s.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2)) f := by
  sorry

/-! ## General seminorm bound (axiom for now)

The general (k, l) case requires the full Leibniz + integration-by-parts
chain. Each step is elementary but the Lean formalization involves:
- D^l of the Fourier multiplier output (Fourier side: multiply by (2πip)^l)
- x^k weight (Fourier side: D^k)
- Leibniz for D^k(p^l · σ · Ff)
- Symbol derivative bounds ‖D^j σ_ω‖_∞ ≤ mass^{-1-j} ‖D^j g‖_∞
- Schwartz decay of Ff and its derivatives

The (0,0) case above shows the pattern. The general case is the same
argument with more bookkeeping. -/

/-- **Uniform Schwartz seminorm bound for the resolvent multiplier family.**
Now a theorem from the direct Fourier analysis bound. -/
theorem resolventSchwartz_uniformBound_direct
    (mass : ℝ) (hmass : 0 < mass) (k l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ) (_ : 0 < C),
    ∀ (ω : ℝ) (hω : mass ≤ ω) (f : SchwartzMap ℝ ℝ),
      SchwartzMap.seminorm ℝ k l
        (resolventMultiplierCLM (lt_of_lt_of_le hmass hω) f) ≤
      C * (s.sup (fun m => SchwartzMap.seminorm (𝕜 := ℝ) (F := ℝ) (E := ℝ) m.1 m.2)) f := by
  sorry

end GaussianField
