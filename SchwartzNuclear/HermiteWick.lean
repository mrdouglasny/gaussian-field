/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hermite Polynomials and Wick Ordering

The Wick-ordered monomial `:x^n:_c` (defined by the recursion
`:x^0: = 1`, `:x^1: = x`, `:x^{n+2}: = x · :x^{n+1}: - (n+1)·c · :x^n:`)
equals the scaled probabilist's Hermite polynomial:

  `:x^n:_c = c^{n/2} · He_n(x / √c)`

This file proves this identity by induction using the Hermite three-term
recurrence from `HermiteFunctions.lean`.

## Main results

- `scaledHermite_succ_succ` — the scaled Hermite polynomial satisfies the
  Wick monomial recursion
- `wick_eq_hermiteR` — the Wick monomial equals the scaled Hermite polynomial
  (using `√c ^ n` form)
- `wick_eq_hermiteR_rpow` — same, using `c ^ (n/2)` form

## References

- Simon, *The P(φ)₂ Euclidean QFT*, §I.3
- Glimm-Jaffe, *Quantum Physics*, §8.6
-/

import SchwartzNuclear.HermiteFunctions
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

noncomputable section

open Polynomial Real

/-! ## Wick monomial recursion -/

/-- The Wick-ordered monomial `:x^n:_c` defined by the three-term recursion.
This is a general definition — not specific to any QFT project. -/
def wickMonomial : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, _, x => x
  | n + 2, c, x => x * wickMonomial (n + 1) c x - (n + 1 : ℝ) * c * wickMonomial n c x

@[simp] theorem wickMonomial_zero (c x : ℝ) : wickMonomial 0 c x = 1 := rfl
@[simp] theorem wickMonomial_one (c x : ℝ) : wickMonomial 1 c x = x := rfl

theorem wickMonomial_succ_succ (n : ℕ) (c x : ℝ) :
    wickMonomial (n + 2) c x =
    x * wickMonomial (n + 1) c x - (n + 1 : ℝ) * c * wickMonomial n c x := rfl

/-! ## Scaled Hermite polynomial satisfies Wick recursion -/

/-- The scaled Hermite polynomial `(√c)^n · He_n(x/√c)`. -/
def scaledHermite (n : ℕ) (c x : ℝ) : ℝ :=
  Real.sqrt c ^ n * (hermiteR n).eval (x / Real.sqrt c)

@[simp] theorem scaledHermite_zero (c x : ℝ) : scaledHermite 0 c x = 1 := by
  simp [scaledHermite, hermiteR, hermite_zero]

theorem scaledHermite_one (c x : ℝ) (hc : 0 < c) : scaledHermite 1 c x = x := by
  simp [scaledHermite, hermiteR, hermite_succ, hermite_zero]
  exact mul_div_cancel₀ x (ne_of_gt (Real.sqrt_pos.mpr hc))

/-- The three-term recurrence for scaled Hermite polynomials:
  `scaledHermite (n+2) c x = x · scaledHermite (n+1) c x - (n+1)·c · scaledHermite n c x`

This is the same recursion as the Wick monomial, which proves they are equal. -/
theorem scaledHermite_succ_succ (n : ℕ) (c x : ℝ) (hc : 0 < c) :
    scaledHermite (n + 2) c x =
    x * scaledHermite (n + 1) c x - (n + 1 : ℝ) * c * scaledHermite n c x := by
  set s := Real.sqrt c
  have hs : s ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  set t := x / s
  have hst : s * t = x := mul_div_cancel₀ x hs
  have hs2 : s * s = c := Real.mul_self_sqrt (le_of_lt hc)
  -- Use the Hermite three-term recurrence
  have hrec := hermiteR_recurrence_succ n t
  -- hrec : t * He_{n+1}(t) = He_{n+2}(t) + (n+1) * He_n(t)
  -- So He_{n+2}(t) = t * He_{n+1}(t) - (n+1) * He_n(t)
  -- LHS = s^(n+2) * He_{n+2}(t)
  --      = s^(n+2) * (t * He_{n+1}(t) - (n+1) * He_n(t))
  -- RHS = x * s^(n+1) * He_{n+1}(t) - (n+1) * c * s^n * He_n(t)
  -- These match because s^(n+2) * t = s^(n+1) * (s*t) = s^(n+1) * x
  -- and s^(n+2) = s*s * s^n = c * s^n
  simp only [scaledHermite, show Real.sqrt c = s from rfl]
  -- Replace He_{n+2}(t) using recurrence
  have h_he : (hermiteR (n + 2)).eval t =
      t * (hermiteR (n + 1)).eval t - ↑(n + 1) * (hermiteR n).eval t := by linarith
  rw [h_he]
  -- Goal: s^(n+2) * (t*H1 - (n+1)*H0) = x * (s^(n+1)*H1) - (n+1)*c * (s^n*H0)
  -- Use: s^(n+2) = s*s*s^n = c*s^n, s^(n+1) = s*s^n, c*t = s*x
  set H1 := (hermiteR (n + 1)).eval t
  set H0 := (hermiteR n).eval t
  have key : c * t = s * x := by
    calc c * t = c * (x / s) := rfl
      _ = s * s * x / s := by rw [hs2, mul_div_assoc]
      _ = s * (s * x / s) := by ring
      _ = s * x := by rw [mul_div_cancel_left₀ _ hs]
  calc s ^ (n + 2) * (t * H1 - ↑(n + 1) * H0)
      = s * s * s ^ n * (t * H1 - ↑(n + 1) * H0) := by ring
    _ = c * s ^ n * (t * H1 - ↑(n + 1) * H0) := by rw [hs2]
    _ = c * t * (s ^ n * H1) - ↑(n + 1) * c * (s ^ n * H0) := by ring
    _ = s * x * (s ^ n * H1) - ↑(n + 1) * c * (s ^ n * H0) := by rw [key]
    _ = x * (s ^ (n + 1) * H1) - ↑(n + 1) * c * (s ^ n * H0) := by ring
    _ = x * (s ^ (n + 1) * H1) - (↑n + 1) * c * (s ^ n * H0) := by push_cast; ring

/-! ## Main theorem: Wick monomial = scaled Hermite polynomial -/

/-- **Wick monomials are scaled Hermite polynomials.**

For `c > 0`, the Wick-ordered monomial `:x^n:_c` equals `(√c)^n · He_n(x/√c)`
where `He_n` is the probabilist's Hermite polynomial.

Proof by induction using the shared three-term recurrence. -/
theorem wick_eq_hermiteR : ∀ (n : ℕ) (c : ℝ) (_ : 0 < c) (x : ℝ),
    wickMonomial n c x = scaledHermite n c x
  | 0, _, _, _ => by simp
  | 1, c, hc, x => by rw [wickMonomial_one, scaledHermite_one c x hc]
  | n + 2, c, hc, x => by
    rw [wickMonomial_succ_succ, scaledHermite_succ_succ n c x hc,
        wick_eq_hermiteR (n + 1) c hc x, wick_eq_hermiteR n c hc x]

/-- **Wick monomials are Hermite polynomials** (rpow form).

  `:x^n:_c = c^{n/2} · He_n(x / √c)`

where `c^{n/2}` is the real power `Real.rpow c (n/2)`. -/
theorem wick_eq_hermiteR_rpow (n : ℕ) (c : ℝ) (hc : 0 < c) (x : ℝ) :
    wickMonomial n c x =
    c ^ ((n : ℝ) / 2) * (hermiteR n).eval (x / Real.sqrt c) := by
  rw [wick_eq_hermiteR n c hc x, scaledHermite]
  congr 1
  -- Show: √c ^ n = c ^ ((n : ℝ) / 2)
  -- √c = c ^ (1/2), so √c ^ n = (c ^ (1/2)) ^ n = c ^ (n/2)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (c ^ (1/2 : ℝ)) n,
      ← Real.rpow_mul (le_of_lt hc)]
  congr 1
  ring

/-! ## Homogeneity

`:γ·x^n:_{γ²·c} = γ^n · :x^n:_c`. Proved by induction using the
three-term recurrence — pure algebra, no Hermite-functional content. -/

/-- **Wick homogeneity**: rescaling `x` by `γ` and `c` by `γ²` rescales
the Wick monomial by `γ^n`. -/
theorem wickMonomial_homogeneity : ∀ (n : ℕ) (γ c x : ℝ),
    wickMonomial n (γ ^ 2 * c) (γ * x) = γ ^ n * wickMonomial n c x
  | 0, _, _, _ => by simp
  | 1, γ, _, x => by simp
  | n + 2, γ, c, x => by
    rw [wickMonomial_succ_succ, wickMonomial_homogeneity (n + 1) γ c x,
        wickMonomial_homogeneity n γ c x, wickMonomial_succ_succ]
    ring

end
