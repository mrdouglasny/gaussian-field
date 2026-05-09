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
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Fintype.Pi

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

/-! ## Multiplication-by-x identity (rearranged Wick recursion) -/

/-- **Multiplication-by-`x` identity.**

Multiplying a Wick monomial by its argument shifts the degree up and
introduces a contraction term:

  `x · :x^k:_c = :x^{k+1}:_c + k · c · :x^{k-1}:_c`.

For `k = 0` the contraction term vanishes (`(0 : ℝ) · c · _ = 0`).
For `k ≥ 1` this is the recursion `wickMonomial_succ_succ` rearranged. -/
theorem wickMonomial_x_mul : ∀ (k : ℕ) (c x : ℝ),
    x * wickMonomial k c x =
      wickMonomial (k + 1) c x + (k : ℝ) * c * wickMonomial (k - 1) c x
  | 0, c, x => by simp
  | k + 1, c, x => by
    -- `wickMonomial_succ_succ`: W_{k+2} = x · W_{k+1} - (k+1) c · W_k
    -- Rearrange: x · W_{k+1} = W_{k+2} + (k+1) c · W_k.
    have h := wickMonomial_succ_succ k c x
    -- (k + 1) - 1 = k
    have h0 : ((k + 1 : ℕ) - 1 : ℕ) = k := rfl
    rw [h0]
    push_cast
    linarith

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

/-! ## Bivariate Wick addition (binomial-type formula)

The Wick monomial in a sum `(c₁ + c₂, x + y)` expands as a binomial-type
sum. This is the polynomial identity equivalent to the generating-function
factorisation
  `exp(t(x+y) − (c₁+c₂)t²/2)
     = exp(tx − c₁ t²/2) · exp(ty − c₂ t²/2)`
expanded coefficient-wise in `t`. -/

/-- Auxiliary "double-indexed" sum used in the proof of bivariate Wick
addition.  Indexes a pair `(a, b) : ℕ × ℕ` with `a + b = n` (encoded
as `b = n - a` and the implicit constraint `a ≤ n` from the `range`). -/
private noncomputable def bivariateSum
    (n : ℕ) (c₁ c₂ x y : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (n.choose k : ℝ) * wickMonomial k c₁ x * wickMonomial (n - k) c₂ y

private lemma bivariateSum_zero (c₁ c₂ x y : ℝ) :
    bivariateSum 0 c₁ c₂ x y = 1 := by
  simp [bivariateSum]

private lemma bivariateSum_one (c₁ c₂ x y : ℝ) :
    bivariateSum 1 c₁ c₂ x y = x + y := by
  simp [bivariateSum, Finset.sum_range_succ]
  ring

/-! ### Choose-absorption identities (real-valued versions). -/

/-- `(k + 1) · C(n+1, k+1) = (n+1) · C(n, k)`, real-valued form.
This is `Nat.succ_mul_choose_eq` cast to `ℝ`. -/
private lemma choose_absorb_left_real (n k : ℕ) :
    (((k + 1 : ℕ)) : ℝ) * ((n + 1).choose (k + 1) : ℝ) =
      ((n + 1 : ℕ) : ℝ) * (n.choose k : ℝ) := by
  have h := Nat.add_one_mul_choose_eq n k
  -- h : (n + 1) * n.choose k = (n + 1).choose (k + 1) * (k + 1)
  have h' : (k + 1) * (n + 1).choose (k + 1) = (n + 1) * n.choose k := by linarith [h]
  exact_mod_cast h'

/-- `(n + 1 - k) · C(n+1, k) = (n+1) · C(n, k)` when `k ≤ n`, real-valued form.
Derived by direct factorial manipulation. -/
private lemma choose_absorb_right_real (n k : ℕ) (hk : k ≤ n) :
    (((n + 1 - k : ℕ)) : ℝ) * ((n + 1).choose k : ℝ) =
      ((n + 1 : ℕ) : ℝ) * (n.choose k : ℝ) := by
  have hk' : k ≤ n + 1 := Nat.le_succ_of_le hk
  have hkn : n + 1 - k = (n - k) + 1 := by omega
  have hfac : k.factorial > 0 := Nat.factorial_pos k
  have hfac' : (n - k).factorial > 0 := Nat.factorial_pos (n - k)
  have key : ((n + 1 - k) * (n + 1).choose k) * (k.factorial * (n - k).factorial) =
         ((n + 1) * n.choose k) * (k.factorial * (n - k).factorial) := by
    have lhs :
        ((n + 1 - k) * (n + 1).choose k) * (k.factorial * (n - k).factorial) =
          (n + 1).factorial := by
      rw [hkn]
      have rearr :
          ((n - k + 1) * (n + 1).choose k) * (k.factorial * (n - k).factorial) =
            (n + 1).choose k * k.factorial * ((n - k + 1) * (n - k).factorial) := by ring
      rw [rearr, ← Nat.factorial_succ]
      have hf : (n + 1).choose k * k.factorial * (n + 1 - k).factorial = (n + 1).factorial :=
        Nat.choose_mul_factorial_mul_factorial hk'
      rw [hkn] at hf
      exact hf
    have rhs :
        ((n + 1) * n.choose k) * (k.factorial * (n - k).factorial) = (n + 1).factorial := by
      have :
          ((n + 1) * n.choose k) * (k.factorial * (n - k).factorial) =
            (n + 1) * (n.choose k * k.factorial * (n - k).factorial) := by ring
      rw [this, Nat.choose_mul_factorial_mul_factorial hk, ← Nat.factorial_succ]
    rw [lhs, rhs]
  have hpos : k.factorial * (n - k).factorial > 0 := Nat.mul_pos hfac hfac'
  have hnat : (n + 1 - k) * (n + 1).choose k = (n + 1) * n.choose k :=
    Nat.eq_of_mul_eq_mul_right hpos key
  exact_mod_cast hnat

/-! ### Three-term recursion for `bivariateSum`. -/

/-- The bivariate sum satisfies the same three-term Wick recursion as
`wickMonomial n (c₁ + c₂) (x + y)`.  Combined with matching base cases
this yields the bivariate addition formula. -/
private lemma bivariateSum_recursion (n : ℕ) (c₁ c₂ x y : ℝ) :
    bivariateSum (n + 2) c₁ c₂ x y =
      (x + y) * bivariateSum (n + 1) c₁ c₂ x y -
        ((n : ℝ) + 1) * (c₁ + c₂) * bivariateSum n c₁ c₂ x y := by
  -- Abbreviations.
  set W₁ : ℕ → ℝ := fun k => wickMonomial k c₁ x with hW₁
  set W₂ : ℕ → ℝ := fun k => wickMonomial k c₂ y with hW₂
  -- The multiplication-by-argument identity.
  have hx : ∀ k, x * W₁ k = W₁ (k + 1) + (k : ℝ) * c₁ * W₁ (k - 1) := fun k => by
    simpa [hW₁] using wickMonomial_x_mul k c₁ x
  have hy : ∀ k, y * W₂ k = W₂ (k + 1) + (k : ℝ) * c₂ * W₂ (k - 1) := fun k => by
    simpa [hW₂] using wickMonomial_x_mul k c₂ y
  -- Unfold bivariateSum.
  simp only [bivariateSum]
  -- The "top" piece: combine the W₁-shifted (via x) and W₂-shifted (via y) sums.
  -- Define the "top-shift-x" sum:  A = ∑_{k=0}^{n+1} C(n+1, k) W₁(k+1) W₂(n+1-k).
  -- Re-indexed (k' = k+1): A = ∑_{k'=1}^{n+2} C(n+1, k'-1) W₁(k') W₂(n+2-k').
  -- And the "top-shift-y" sum: C = ∑_{k=0}^{n+1} C(n+1, k) W₁(k) W₂(n+2-k).
  -- A + C should give bivariateSum(n+2) by Pascal.
  -- The "low" pieces: B = ∑ k·c₁·C(n+1,k) W₁(k-1) W₂(n+1-k),
  --                   D = ∑ (n+1-k)·c₂·C(n+1,k) W₁(k) W₂(n-k),
  -- and these should equal (n+1)c₁·bivariateSum(n) and (n+1)c₂·bivariateSum(n)
  -- respectively, by the absorption identities.
  --
  -- We prove the recursion by computing
  --   (x+y)·bivariateSum(n+1) - bivariateSum(n+2)
  --     = (n+1)(c₁+c₂)·bivariateSum(n).
  -- Equivalently:  bivariateSum(n+2) + (n+1)(c₁+c₂)·bivariateSum(n)
  --             = (x+y)·bivariateSum(n+1).
  -- We organise the proof as: RHS - LHS = 0.
  -- Move everything to one side.
  have key :
      (x + y) * (∑ k ∈ Finset.range (n + 2),
          ((n + 1).choose k : ℝ) * W₁ k * W₂ (n + 1 - k)) =
      (∑ k ∈ Finset.range (n + 3),
          ((n + 2).choose k : ℝ) * W₁ k * W₂ (n + 2 - k)) +
      ((n : ℝ) + 1) * (c₁ + c₂) *
        (∑ k ∈ Finset.range (n + 1),
          (n.choose k : ℝ) * W₁ k * W₂ (n - k)) := by
    -- Expand (x+y) and apply hx, hy.
    have expand_xy :
        (x + y) * (∑ k ∈ Finset.range (n + 2),
            ((n + 1).choose k : ℝ) * W₁ k * W₂ (n + 1 - k)) =
        (∑ k ∈ Finset.range (n + 2),
          ((n + 1).choose k : ℝ) * (W₁ (k + 1) + (k : ℝ) * c₁ * W₁ (k - 1)) *
            W₂ (n + 1 - k)) +
        (∑ k ∈ Finset.range (n + 2),
          ((n + 1).choose k : ℝ) * W₁ k *
            (W₂ (n + 1 - k + 1) + ((n + 1 - k : ℕ) : ℝ) * c₂ * W₂ (n + 1 - k - 1))) := by
      rw [add_mul, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [show x * (((n + 1).choose k : ℝ) * W₁ k * W₂ (n + 1 - k)) =
              ((n + 1).choose k : ℝ) * (x * W₁ k) * W₂ (n + 1 - k) by ring,
            hx k]
      · refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [show y * (((n + 1).choose k : ℝ) * W₁ k * W₂ (n + 1 - k)) =
              ((n + 1).choose k : ℝ) * W₁ k * (y * W₂ (n + 1 - k)) by ring,
            hy (n + 1 - k)]
    rw [expand_xy]
    -- Split the four sums.
    rw [show
      (∑ k ∈ Finset.range (n + 2),
          ((n + 1).choose k : ℝ) *
            (W₁ (k + 1) + (k : ℝ) * c₁ * W₁ (k - 1)) * W₂ (n + 1 - k)) =
        (∑ k ∈ Finset.range (n + 2),
          ((n + 1).choose k : ℝ) * W₁ (k + 1) * W₂ (n + 1 - k)) +
        (∑ k ∈ Finset.range (n + 2),
          ((n + 1).choose k : ℝ) * ((k : ℝ) * c₁ * W₁ (k - 1)) * W₂ (n + 1 - k)) by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun k _ => ?_); ring]
    rw [show
      (∑ k ∈ Finset.range (n + 2),
          ((n + 1).choose k : ℝ) * W₁ k *
            (W₂ (n + 1 - k + 1) + ((n + 1 - k : ℕ) : ℝ) * c₂ * W₂ (n + 1 - k - 1))) =
        (∑ k ∈ Finset.range (n + 2),
          ((n + 1).choose k : ℝ) * W₁ k * W₂ (n + 1 - k + 1)) +
        (∑ k ∈ Finset.range (n + 2),
          ((n + 1).choose k : ℝ) * W₁ k *
            (((n + 1 - k : ℕ) : ℝ) * c₂ * W₂ (n + 1 - k - 1))) by
      rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl (fun k _ => ?_); ring]
    -- Now we have 4 sums on the LHS. Call them A_top, A_low, B_top, B_low.
    -- Claim:
    --   A_top + B_top = ∑_{j=0}^{n+2} C(n+2, j) W₁(j) W₂(n+2-j)   [by Pascal]
    --   A_low + B_low = (n+1)(c₁+c₂) · ∑_k C(n,k) W₁(k) W₂(n-k)   [by absorption]
    -- Add the two and rearrange.
    --
    -- A_top: reindex k → k+1.  Original: ∑_{k=0}^{n+1} C(n+1, k) W₁(k+1) W₂(n+1-k).
    -- After k → k-1 (i.e. j = k+1): ∑_{j=1}^{n+2} C(n+1, j-1) W₁(j) W₂(n+1-(j-1)) =
    -- ∑_{j=1}^{n+2} C(n+1, j-1) W₁(j) W₂(n+2-j).
    have h_A_top :
        (∑ k ∈ Finset.range (n + 2),
            ((n + 1).choose k : ℝ) * W₁ (k + 1) * W₂ (n + 1 - k)) =
          ∑ j ∈ Finset.range (n + 3),
            (if j = 0 then (0 : ℝ) else ((n + 1).choose (j - 1) : ℝ)) *
              W₁ j * W₂ (n + 2 - j) := by
      -- Use Finset.sum_range_succ' on the RHS only.
      conv_rhs => rw [show (n + 3) = (n + 2) + 1 from rfl, Finset.sum_range_succ']
      -- The j = 0 term on the RHS vanishes.
      have hj0 : (if (0 : ℕ) = 0 then (0 : ℝ) else ((n + 1).choose (0 - 1) : ℝ)) *
            W₁ 0 * W₂ (n + 2 - 0) = 0 := by simp
      rw [hj0, add_zero]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k < n + 2 := Finset.mem_range.mp hk
      have hkne : k + 1 ≠ 0 := Nat.succ_ne_zero _
      have hksub : (k + 1 : ℕ) - 1 = k := by omega
      have hk2 : n + 2 - (k + 1) = n + 1 - k := by omega
      rw [if_neg hkne, hksub, hk2]
    -- B_top is essentially ∑_{k=0}^{n+1} C(n+1, k) W₁(k) W₂(n+2-k), but the exponent
    -- on W₂ is `n + 1 - k + 1` which we need to simplify to `n + 2 - k` for k ≤ n+1.
    have h_B_top :
        (∑ k ∈ Finset.range (n + 2),
            ((n + 1).choose k : ℝ) * W₁ k * W₂ (n + 1 - k + 1)) =
          ∑ k ∈ Finset.range (n + 2),
            ((n + 1).choose k : ℝ) * W₁ k * W₂ (n + 2 - k) := by
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k ≤ n + 1 := by rw [Finset.mem_range] at hk; omega
      have : n + 1 - k + 1 = n + 2 - k := by omega
      rw [this]
    -- Reformulate B_top using the same "if j = 0 then 0 else …" form for compatibility,
    -- but extended over range(n+3) so that we can combine with A_top via Pascal.
    have h_B_top' :
        (∑ k ∈ Finset.range (n + 2),
            ((n + 1).choose k : ℝ) * W₁ k * W₂ (n + 2 - k)) =
          ∑ j ∈ Finset.range (n + 3),
            (if j = n + 2 then (0 : ℝ) else ((n + 1).choose j : ℝ)) *
              W₁ j * W₂ (n + 2 - j) := by
      -- Rewrite RHS via Finset.sum_range_succ.
      conv_rhs => rw [show (n + 3) = (n + 2) + 1 from rfl, Finset.sum_range_succ]
      -- The k = n+2 term on the RHS vanishes because (if n+2 = n+2 then 0 else …) = 0.
      have hzero : (if (n + 2 : ℕ) = n + 2 then (0 : ℝ) else ((n + 1).choose (n + 2) : ℝ)) *
            W₁ (n + 2) * W₂ (n + 2 - (n + 2)) = 0 := by simp
      rw [hzero, add_zero]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k < n + 2 := Finset.mem_range.mp hk
      have hne : k ≠ n + 2 := Nat.ne_of_lt hk'
      rw [if_neg hne]
    -- Combine: A_top + B_top = bivariateSum(n+2) by Pascal.
    have h_top :
        (∑ k ∈ Finset.range (n + 2),
            ((n + 1).choose k : ℝ) * W₁ (k + 1) * W₂ (n + 1 - k)) +
        (∑ k ∈ Finset.range (n + 2),
            ((n + 1).choose k : ℝ) * W₁ k * W₂ (n + 1 - k + 1)) =
          ∑ j ∈ Finset.range (n + 3),
            ((n + 2).choose j : ℝ) * W₁ j * W₂ (n + 2 - j) := by
      rw [h_A_top, h_B_top, h_B_top', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      -- Coefficient identity: (if j=0 then 0 else C(n+1, j-1)) + (if j=n+2 then 0 else C(n+1, j))
      -- = C(n+2, j).
      have hcoeff :
          (if j = 0 then (0 : ℝ) else ((n + 1).choose (j - 1) : ℝ)) +
              (if j = n + 2 then (0 : ℝ) else ((n + 1).choose j : ℝ)) =
            ((n + 2).choose j : ℝ) := by
        rcases Nat.eq_zero_or_pos j with hj0 | hj1
        · subst hj0
          simp [Nat.choose]
        · -- j ≥ 1
          rcases lt_or_ge j (n + 2) with hjlt | hjge
          · -- 1 ≤ j ≤ n + 1
            have hne0 : j ≠ 0 := Nat.ne_of_gt hj1
            have hne_n2 : j ≠ n + 2 := Nat.ne_of_lt hjlt
            simp [hne0, hne_n2]
            -- (n+1).choose (j-1) + (n+1).choose j = (n+2).choose j
            have hjsub : j - 1 + 1 = j := Nat.sub_add_cancel hj1
            -- Use: (n+1).choose ((j-1) + 1) = (n+1).choose (j-1) + (n+1).choose j ... wait.
            -- Pascal: (n+2).choose j = (n+1).choose (j-1) + (n+1).choose j when j ≥ 1.
            -- mathlib: Nat.choose_succ_succ : (n+1).choose (k+1) = n.choose k + n.choose (k+1).
            have hpas : (n + 1 + 1).choose (j - 1 + 1) =
                          (n + 1).choose (j - 1) + (n + 1).choose (j - 1 + 1) :=
              Nat.choose_succ_succ (n + 1) (j - 1)
            rw [hjsub] at hpas
            -- hpas : (n + 2).choose j = (n + 1).choose (j - 1) + (n + 1).choose j
            -- So coefficient sum = C(n+1, j-1) + C(n+1, j) = C(n+2, j).
            have : ((n + 2).choose j : ℝ) =
                ((n + 1).choose (j - 1) : ℝ) + ((n + 1).choose j : ℝ) := by
              exact_mod_cast hpas
            linarith
          · -- j ≥ n + 2.  We don't have an upper bound from the hypotheses
            -- here, but the equation should hold anyway for any such j ≥ n+2.
            -- For j = n+2: LHS = C(n+1, n+1) + 0 = 1 = C(n+2, n+2).
            -- For j > n+2: LHS = 0 + C(n+1, j) which equals 0 = C(n+2, j) since j > n+2.
            -- Easier: case on j = n+2 vs j ≥ n+3.
            rcases hjge.lt_or_eq with hj_gt | hj_eq
            · -- j > n + 2
              have hne0 : j ≠ 0 := by omega
              have hne_n2 : j ≠ n + 2 := by omega
              rw [if_neg hne0, if_neg hne_n2]
              have h1 : (n + 1).choose (j - 1) = 0 :=
                Nat.choose_eq_zero_of_lt (by omega)
              have h2 : (n + 1).choose j = 0 :=
                Nat.choose_eq_zero_of_lt (by omega)
              have h3 : (n + 2).choose j = 0 :=
                Nat.choose_eq_zero_of_lt (by omega)
              rw [h1, h2, h3]
              push_cast; ring
            · -- j = n + 2 (hj_eq : n + 2 = j)
              have hjeq : j = n + 2 := hj_eq.symm
              have hjsub : j - 1 = n + 1 := by omega
              have hne0 : j ≠ 0 := by omega
              rw [if_neg hne0, hjsub, if_pos hjeq]
              rw [hjeq, Nat.choose_self, Nat.choose_self]
              push_cast; ring
      -- Apply.
      have : (if j = 0 then (0 : ℝ) else ((n + 1).choose (j - 1) : ℝ)) * W₁ j * W₂ (n + 2 - j) +
              (if j = n + 2 then (0 : ℝ) else ((n + 1).choose j : ℝ)) * W₁ j * W₂ (n + 2 - j) =
            ((if j = 0 then (0 : ℝ) else ((n + 1).choose (j - 1) : ℝ)) +
              (if j = n + 2 then (0 : ℝ) else ((n + 1).choose j : ℝ))) *
              W₁ j * W₂ (n + 2 - j) := by ring
      rw [this, hcoeff]
    -- A_low: ∑_{k=0}^{n+1} C(n+1, k) (k:ℝ) c₁ W₁(k-1) W₂(n+1-k).
    -- The k=0 term vanishes.  Reindex k → k+1.
    have h_A_low :
        (∑ k ∈ Finset.range (n + 2),
            ((n + 1).choose k : ℝ) * ((k : ℝ) * c₁ * W₁ (k - 1)) * W₂ (n + 1 - k)) =
          ((n : ℝ) + 1) * c₁ *
            (∑ k ∈ Finset.range (n + 1),
              (n.choose k : ℝ) * W₁ k * W₂ (n - k)) := by
      rw [show (n + 2) = (n + 1) + 1 from rfl, Finset.sum_range_succ']
      simp
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      -- After the simp: each summand looks like C(n+1, k+1) * ((k+1:ℝ) * c₁ * W₁ k) * W₂ (n - k)
      -- and we want it equal to (n+1) * c₁ * (C(n, k) * W₁ k * W₂ (n - k)).
      have habs := choose_absorb_left_real n k
      -- habs : ((k + 1 : ℕ) : ℝ) * ((n + 1).choose (k + 1) : ℝ) = ((n + 1 : ℕ) : ℝ) * (n.choose k : ℝ)
      have habs' : ((k : ℝ) + 1) * ((n + 1).choose (k + 1) : ℝ) =
                    ((n : ℝ) + 1) * (n.choose k : ℝ) := by
        have := habs
        push_cast at this
        linarith
      have :
          ((n + 1).choose (k + 1) : ℝ) * (((k : ℝ) + 1) * c₁ * W₁ k) * W₂ (n - k) =
            (((k : ℝ) + 1) * ((n + 1).choose (k + 1) : ℝ)) * c₁ * W₁ k * W₂ (n - k) := by
        ring
      rw [this, habs']
      ring
    -- B_low: ∑_{k=0}^{n+1} C(n+1, k) W₁(k) (n+1-k) c₂ W₂(n+1-k-1).
    -- For k = n + 1, the factor (n+1-k) = 0 vanishes.  So restrict to k ∈ range (n+1).
    have h_B_low :
        (∑ k ∈ Finset.range (n + 2),
            ((n + 1).choose k : ℝ) * W₁ k *
              (((n + 1 - k : ℕ) : ℝ) * c₂ * W₂ (n + 1 - k - 1))) =
          ((n : ℝ) + 1) * c₂ *
            (∑ k ∈ Finset.range (n + 1),
              (n.choose k : ℝ) * W₁ k * W₂ (n - k)) := by
      -- Drop last (k = n+1) term: (n+1 - (n+1) : ℕ) = 0.
      rw [show (n + 2) = (n + 1) + 1 from rfl, Finset.sum_range_succ]
      have hzero :
          ((n + 1).choose (n + 1) : ℝ) * W₁ (n + 1) *
            (((n + 1 - (n + 1) : ℕ) : ℝ) * c₂ * W₂ (n + 1 - (n + 1) - 1)) = 0 := by
        have : (n + 1 - (n + 1) : ℕ) = 0 := Nat.sub_self _
        rw [this]
        simp
      rw [hzero, add_zero, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk' : k ≤ n := by rw [Finset.mem_range] at hk; omega
      have habs := choose_absorb_right_real n k hk'
      -- habs : ((n + 1 - k : ℕ) : ℝ) * ((n + 1).choose k : ℝ) = ((n + 1 : ℕ) : ℝ) * (n.choose k : ℝ)
      have hkn1 : n + 1 - k - 1 = n - k := by omega
      rw [hkn1]
      have :
          ((n + 1).choose k : ℝ) * W₁ k * (((n + 1 - k : ℕ) : ℝ) * c₂ * W₂ (n - k)) =
            (((n + 1 - k : ℕ) : ℝ) * ((n + 1).choose k : ℝ)) * c₂ * W₁ k * W₂ (n - k) := by
        ring
      rw [this, habs]
      push_cast
      ring
    -- Now combine everything.  We have four sums; group into (top + top) and (low + low).
    linarith [h_top, h_A_low, h_B_low]
  linarith [key]

/-- The Wick monomial vanishes for a zero argument and zero variance,
except at degree 0. -/
private lemma wickMonomial_zero_zero : ∀ k : ℕ, wickMonomial k (0 : ℝ) (0 : ℝ) =
    if k = 0 then 1 else 0
  | 0 => by simp
  | 1 => by simp
  | k + 2 => by
    rw [wickMonomial_succ_succ]
    simp [wickMonomial_zero_zero (k + 1), wickMonomial_zero_zero k]

/-- **Bivariate Wick addition.**

  `:_{(x+y)}^n:_{c₁+c₂} = ∑_k C(n, k) :x^k:_{c₁} · :y^{n-k}:_{c₂}`.

Proved by two-step induction on `n`: the LHS and the RHS (`bivariateSum`)
satisfy the same three-term recursion (`bivariateSum_recursion`) and the
same base cases. -/
theorem wickMonomial_add_add : ∀ (n : ℕ) (c₁ c₂ x y : ℝ),
    wickMonomial n (c₁ + c₂) (x + y) =
    ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℝ) * wickMonomial k c₁ x * wickMonomial (n - k) c₂ y := by
  -- It suffices to show wickMonomial n (c₁+c₂) (x+y) = bivariateSum n c₁ c₂ x y.
  suffices h : ∀ n c₁ c₂ x y, wickMonomial n (c₁ + c₂) (x + y) = bivariateSum n c₁ c₂ x y by
    intro n c₁ c₂ x y
    exact h n c₁ c₂ x y
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    intro c₁ c₂ x y; simp [bivariateSum]
  | one =>
    intro c₁ c₂ x y
    rw [bivariateSum_one]; simp
  | more n ih1 ih2 =>
    intro c₁ c₂ x y
    rw [wickMonomial_succ_succ, ih2 c₁ c₂ x y, ih1 c₁ c₂ x y,
        bivariateSum_recursion n c₁ c₂ x y]

/-! ## Multivariate Wick multinomial expansion

The multivariate generalisation of the bivariate addition formula.
For any finite index set `ι`, and any `γ ξ : ι → ℝ`,

  `wickMonomial k (∑_j γ_j²) (∑_j γ_j · ξ_j)
     = ∑_{|α|=k} (k! / ∏_j α_j!) · (∏_j γ_j^{α_j}) · ∏_j wickMonomial α_j 1 ξ_j`.

Proof by `Finset.induction_on s` on the support set `s : Finset ι`,
using `wickMonomial_add_add` to peel off one summand at a time and
`wickMonomial_homogeneity` to absorb the resulting `γ_j^k` factors.
-/

/-- Multi-indices supported in a Finset `s ⊆ ι` with total degree `k`. -/
private noncomputable def multiIndicesSupportedIn
    {ι : Type*} [Fintype ι] [DecidableEq ι] (s : Finset ι) (k : ℕ) :
    Finset (ι → ℕ) :=
  (Fintype.piFinset (fun _ : ι => Finset.range (k + 1))).filter
    (fun α => (∀ j ∉ s, α j = 0) ∧ ∑ j, α j = k)

/-- The full set `multiIndicesOfTotalDegree` corresponds to the support
being all of `ι`. -/
private lemma multiIndicesSupportedIn_univ
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    multiIndicesSupportedIn (Finset.univ : Finset ι) k =
    (Fintype.piFinset (fun _ : ι => Finset.range (k + 1))).filter
      (fun α => ∑ j, α j = k) := by
  unfold multiIndicesSupportedIn
  ext α
  simp [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]

/-- Empty case: only the zero multi-index is supported in ∅, and only
at total degree 0. -/
private lemma multiIndicesSupportedIn_empty
    {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) :
    multiIndicesSupportedIn (∅ : Finset ι) k =
      if k = 0 then {(fun _ => 0 : ι → ℕ)} else ∅ := by
  unfold multiIndicesSupportedIn
  ext α
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    Finset.notMem_empty]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [if_true, Finset.mem_singleton, funext_iff]
    constructor
    · rintro ⟨_, hα0, _⟩; intro j; exact hα0 j (by simp)
    · intro hα0
      refine ⟨fun i => ?_, fun j _ => hα0 j, ?_⟩
      · rw [hα0 i]; omega
      · simp_rw [hα0]; simp
  · have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
    simp only [hk_ne, if_false, Finset.notMem_empty, iff_false, not_and]
    intro hbound hα0
    -- α j = 0 for all j (since α has empty support), so ∑ α = 0 ≠ k.
    have hzero : ∀ j, α j = 0 := fun j => hα0 j (by simp)
    simp_rw [hzero]
    simp
    omega

/-- **Multivariate Wick multinomial expansion** (over a Finset).

For any Finset `s : Finset ι`, any `γ ξ : ι → ℝ`, and any `k : ℕ`:

  `wickMonomial k (∑_{j ∈ s} γ_j²) (∑_{j ∈ s} γ_j · ξ_j) =
     ∑_{α ∈ multiIndicesSupportedIn s k}
       (k! / ∏_j α_j!) · (∏_j γ_j^{α_j}) · ∏_j wickMonomial α_j 1 ξ_j`.

The products on the RHS are over all of `ι`, but factors with
`α j = 0` (which holds for `j ∉ s`) contribute 1.

Proved by `Finset.induction_on s`, peeling off one element at a time
via `wickMonomial_add_add` and `wickMonomial_homogeneity`. -/
private theorem wickMonomial_pow_sum_expansion_aux
    {ι : Type*} [Fintype ι] [DecidableEq ι] (γ ξ : ι → ℝ)
    (s : Finset ι) :
    ∀ (k : ℕ),
    wickMonomial k (∑ j ∈ s, (γ j) ^ 2) (∑ j ∈ s, γ j * ξ j) =
    ∑ α ∈ multiIndicesSupportedIn s k,
      ((k.factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) *
      (∏ j, γ j ^ (α j)) *
      (∏ j, wickMonomial (α j) 1 (ξ j)) := by
  induction s using Finset.induction_on with
  | empty =>
    intro k
    -- LHS: wickMonomial k 0 0 = if k = 0 then 1 else 0.
    -- RHS: sum over multiIndicesSupportedIn ∅ k = if k = 0 then {0_index} else ∅.
    simp only [Finset.sum_empty, wickMonomial_zero_zero, multiIndicesSupportedIn_empty]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
      simp [hk_ne]
  | insert j₀ s hj₀ ih =>
    intro k
    -- Split off j₀.
    have hsum_var :
        (∑ j ∈ insert j₀ s, (γ j) ^ 2) = (γ j₀) ^ 2 + ∑ j ∈ s, (γ j) ^ 2 :=
      Finset.sum_insert hj₀
    have hsum_pt :
        (∑ j ∈ insert j₀ s, γ j * ξ j) = γ j₀ * ξ j₀ + ∑ j ∈ s, γ j * ξ j :=
      Finset.sum_insert hj₀
    rw [hsum_var, hsum_pt]
    -- Apply bivariate addition.
    rw [wickMonomial_add_add]
    -- Each summand: C(k, m) · wickMonomial m (γ_{j₀}²) (γ_{j₀} ξ_{j₀})
    --              · wickMonomial (k - m) (∑_s γ²) (∑_s γ ξ).
    -- Apply homogeneity to the j₀ factor: wickMonomial m (γ_{j₀}²) (γ_{j₀} ξ_{j₀}) =
    --     γ_{j₀}^m · wickMonomial m 1 ξ_{j₀}.
    -- And IH to the s factor.
    have hhom : ∀ m, wickMonomial m ((γ j₀) ^ 2) (γ j₀ * ξ j₀) =
                  (γ j₀) ^ m * wickMonomial m 1 (ξ j₀) := fun m => by
      have := wickMonomial_homogeneity m (γ j₀) 1 (ξ j₀)
      simp at this
      exact this
    -- Substitute homogeneity for the j₀ factor and the IH for the s factor.
    have step1 :
        (∑ m ∈ Finset.range (k + 1),
            (k.choose m : ℝ) * wickMonomial m ((γ j₀) ^ 2) (γ j₀ * ξ j₀) *
              wickMonomial (k - m) (∑ j ∈ s, (γ j) ^ 2) (∑ j ∈ s, γ j * ξ j)) =
        (∑ m ∈ Finset.range (k + 1),
            (k.choose m : ℝ) * ((γ j₀) ^ m * wickMonomial m 1 (ξ j₀)) *
              ∑ α ∈ multiIndicesSupportedIn s (k - m),
                (((k - m).factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) *
                (∏ j, γ j ^ (α j)) *
                (∏ j, wickMonomial (α j) 1 (ξ j))) := by
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [hhom, ih (k - m)]
    rw [step1]
    -- Now we need to prove the LHS = RHS where the RHS is the sum over
    -- multiIndicesSupportedIn (insert j₀ s) k.
    -- Convert the double sum (m, α) into a single sum over α' = update α j₀ m.
    -- Use Finset.sum_bij.
    -- First, push the inner sum outside.
    rw [show ∑ m ∈ Finset.range (k + 1),
              ((k.choose m : ℝ) * ((γ j₀) ^ m * wickMonomial m 1 (ξ j₀))) *
                ∑ α ∈ multiIndicesSupportedIn s (k - m),
                  (((k - m).factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) *
                  (∏ j, γ j ^ (α j)) *
                  (∏ j, wickMonomial (α j) 1 (ξ j))
            = ∑ m ∈ Finset.range (k + 1),
                ∑ α ∈ multiIndicesSupportedIn s (k - m),
                  ((k.choose m : ℝ) * ((γ j₀) ^ m * wickMonomial m 1 (ξ j₀))) *
                  ((((k - m).factorial : ℝ) / ∏ j, ((α j).factorial : ℝ)) *
                  (∏ j, γ j ^ (α j)) *
                  (∏ j, wickMonomial (α j) 1 (ξ j))) from
      Finset.sum_congr rfl (fun m _ => Finset.mul_sum _ _ _)]
    -- Use Finset.sum_sigma' to convert nested sums to a Σ-sum.
    rw [Finset.sum_sigma' (Finset.range (k + 1))
        (fun m => multiIndicesSupportedIn s (k - m))]
    -- Now define the bijection (m, α) ↦ Function.update α j₀ m.
    refine Finset.sum_bij (fun (mα : Σ _ : ℕ, ι → ℕ) _ => Function.update mα.2 j₀ mα.1)
      ?hi ?h_inj ?h_surj ?h_eq
    · -- hi: image is in multiIndicesSupportedIn (insert j₀ s) k.
      rintro ⟨m, α⟩ hmα
      simp only [Finset.mem_sigma, Finset.mem_range] at hmα
      obtain ⟨hm_lt, hα⟩ := hmα
      simp only [multiIndicesSupportedIn, Finset.mem_filter, Fintype.mem_piFinset,
        Finset.mem_range] at hα ⊢
      obtain ⟨hα_bd, hα_supp, hα_sum⟩ := hα
      refine ⟨?_, ?_, ?_⟩
      · intro j
        rcases eq_or_ne j j₀ with hj | hj
        · subst hj
          rw [Function.update_self]
          omega
        · rw [Function.update_of_ne hj]
          have := hα_bd j
          omega
      · -- support: for j ∉ insert j₀ s, update α j₀ m at j = α j = 0.
        intro j hj
        rw [Finset.mem_insert, not_or] at hj
        obtain ⟨hj_ne, hj_ns⟩ := hj
        rw [Function.update_of_ne hj_ne]
        exact hα_supp j hj_ns
      · -- sum: ∑ (Function.update α j₀ m) = m + ∑ α (with α j₀ replaced) = m + (k - m) = k.
        -- Function.update α j₀ m: at j₀ value is m; elsewhere value is α j.
        -- So ∑_{j ∈ univ} (Function.update α j₀ m) j = m + ∑_{j ∈ univ \ {j₀}} α j
        --   = m + (∑_{j ∈ univ} α j - α j₀) = m + (k - m) - α j₀
        -- We have α j₀ = 0 because j₀ ∉ s (so by hα_supp).
        have hα_j₀ : α j₀ = 0 := hα_supp j₀ hj₀
        have hsum_eq : ∑ j, Function.update α j₀ m j = m + (k - m) := by
          rw [Finset.sum_update_of_mem (Finset.mem_univ j₀)]
          -- Goal: m + ∑ x ∈ univ \ {j₀}, α x = m + (k - m)
          have hsplit_sum :
              ∑ j, α j = α j₀ + ∑ x ∈ Finset.univ \ {j₀}, α x := by
            conv_lhs => rw [show (Finset.univ : Finset ι) = insert j₀ (Finset.univ \ {j₀}) by
              ext x
              simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ,
                Finset.mem_singleton, true_and]
              tauto]
            rw [Finset.sum_insert (by simp)]
          have : ∑ x ∈ Finset.univ \ {j₀}, α x = k - m := by
            omega
          rw [this]
        rw [hsum_eq]
        omega
    · -- h_inj: injective.
      rintro ⟨m, α⟩ hmα ⟨m', α'⟩ hmα' heq
      simp only at heq
      -- Function.update α j₀ m = Function.update α' j₀ m' implies m = m' (eval at j₀)
      -- and α j = α' j for j ≠ j₀.
      have hj₀_eq : (Function.update α j₀ m) j₀ = (Function.update α' j₀ m') j₀ := by
        rw [heq]
      simp at hj₀_eq
      have hα_eq : α = α' := by
        funext j
        rcases eq_or_ne j j₀ with hj | hj
        · -- j = j₀: both α j₀ and α' j₀ are 0 (since j₀ ∉ s).
          simp only [Finset.mem_sigma] at hmα hmα'
          have h1 : α j₀ = 0 := by
            have hmem := hmα.2
            simp only [multiIndicesSupportedIn, Finset.mem_filter] at hmem
            exact hmem.2.1 j₀ hj₀
          have h2 : α' j₀ = 0 := by
            have hmem := hmα'.2
            simp only [multiIndicesSupportedIn, Finset.mem_filter] at hmem
            exact hmem.2.1 j₀ hj₀
          rw [hj, h1, h2]
        · have hcongr := congr_fun heq j
          rw [Function.update_of_ne hj, Function.update_of_ne hj] at hcongr
          exact hcongr
      simp [hj₀_eq, hα_eq]
    · -- h_surj: every α' in multiIndicesSupportedIn (insert j₀ s) k arises.
      intro α' hα'
      simp only [multiIndicesSupportedIn, Finset.mem_filter, Fintype.mem_piFinset,
        Finset.mem_range] at hα'
      obtain ⟨hbd, hsupp, hsum⟩ := hα'
      -- Take m = α' j₀ and α = Function.update α' j₀ 0.
      refine ⟨⟨α' j₀, Function.update α' j₀ 0⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_range]
        refine ⟨?_, ?_⟩
        · -- α' j₀ < k + 1
          have := hbd j₀
          omega
        · simp only [multiIndicesSupportedIn, Finset.mem_filter, Fintype.mem_piFinset,
            Finset.mem_range]
          -- Helper: for j ≠ j₀, α' j ≤ ∑_{x ≠ j₀} α' x = k - α' j₀.
          have hsplit_sum :
              ∑ j, α' j = α' j₀ + ∑ x ∈ Finset.univ \ {j₀}, α' x := by
            conv_lhs => rw [show (Finset.univ : Finset ι) = insert j₀ (Finset.univ \ {j₀}) by
              ext x
              simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ,
                Finset.mem_singleton, true_and]
              tauto]
            rw [Finset.sum_insert (by simp)]
          have hsum_rest : ∑ x ∈ Finset.univ \ {j₀}, α' x = k - α' j₀ := by omega
          have hbd_rest : ∀ j ≠ j₀, α' j ≤ k - α' j₀ := by
            intro j hj
            have hmem : j ∈ Finset.univ \ {j₀} := by
              simp [hj]
            calc α' j ≤ ∑ x ∈ Finset.univ \ {j₀}, α' x :=
                    Finset.single_le_sum (f := α') (s := Finset.univ \ {j₀})
                      (fun _ _ => Nat.zero_le _) hmem
              _ = k - α' j₀ := hsum_rest
          refine ⟨?_, ?_, ?_⟩
          · intro j
            rcases eq_or_ne j j₀ with hj | hj
            · subst hj; rw [Function.update_self]; omega
            · rw [Function.update_of_ne hj]
              have := hbd_rest j hj
              omega
          · intro j hj
            rcases eq_or_ne j j₀ with hj' | hj'
            · subst hj'; rw [Function.update_self]
            · rw [Function.update_of_ne hj']
              apply hsupp
              rw [Finset.mem_insert, not_or]
              exact ⟨hj', hj⟩
          · -- ∑ (Function.update α' j₀ 0) = ∑ α' - α' j₀ = k - α' j₀.
            rw [Finset.sum_update_of_mem (Finset.mem_univ j₀)]
            rw [hsum_rest]
            ring
      · -- Function.update (Function.update α' j₀ 0) j₀ (α' j₀) = α'.
        dsimp only
        funext j
        rcases eq_or_ne j j₀ with hj | hj
        · subst hj; rw [Function.update_self]
        · rw [Function.update_of_ne hj, Function.update_of_ne hj]
    · -- h_eq: the values agree.
      rintro ⟨m, α⟩ hmα
      simp only at *
      simp only [Finset.mem_sigma, Finset.mem_range] at hmα
      obtain ⟨hm_lt, hα⟩ := hmα
      simp only [multiIndicesSupportedIn, Finset.mem_filter] at hα
      obtain ⟨_, hα_supp, hα_sum⟩ := hα
      have hα_j₀ : α j₀ = 0 := hα_supp j₀ hj₀
      -- Show: C(k, m) · γ_{j₀}^m · W_m 1 ξ_{j₀} · (k-m)!/∏α_j! · ∏ γ^α · ∏ W α 1 ξ
      --     = k!/∏ (update α j₀ m)_j! · ∏ γ^(update α j₀ m) · ∏ W (update α j₀ m) 1 ξ.
      -- Use:
      -- (1) (update α j₀ m) j₀ = m, (update α j₀ m) j = α j for j ≠ j₀.
      -- (2) ∏_j (update α j₀ m)_j! = m! · ∏_{j ≠ j₀} α j!
      --                              = m! · (∏ α_j!) / α_{j₀}! = m! · ∏ α_j!  (since α_{j₀} = 0, factorial = 1).
      -- (3) C(k, m) = k! / (m! · (k - m)!), so C(k, m) · (k-m)!/∏α_j! = k!/(m! ∏α_j!) = k!/∏(update)_j!.
      -- (4) Similarly for the γ and W products: split off j₀ and combine.
      -- Helper: split ∏ over `univ` into the j₀ term times ∏ over `univ \ {j₀}`.
      -- We use this for the three update-quantities below.  Specialised to ℝ
      -- to avoid universe-polymorphism issues.
      have hsplit : ∀ (f : ι → ℝ),
          ∏ j, f j = f j₀ * ∏ j ∈ Finset.univ \ {j₀}, f j := by
        intro f
        conv_lhs => rw [show (Finset.univ : Finset ι) = insert j₀ (Finset.univ \ {j₀}) by
          ext x
          simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ,
            Finset.mem_singleton, true_and]
          tauto]
        rw [Finset.prod_insert (by simp)]
      -- Now rewrite the three products.
      have hupdate_factorial_R :
          (∏ j, ((Function.update α j₀ m j).factorial : ℝ)) =
            (m.factorial : ℝ) * ∏ j, ((α j).factorial : ℝ) := by
        rw [hsplit (fun j => ((Function.update α j₀ m j).factorial : ℝ))]
        rw [hsplit (fun j => ((α j).factorial : ℝ))]
        rw [Function.update_self, hα_j₀, Nat.factorial_zero, Nat.cast_one]
        rw [show ∏ j ∈ Finset.univ \ {j₀},
              ((Function.update α j₀ m j).factorial : ℝ) =
            ∏ j ∈ Finset.univ \ {j₀}, ((α j).factorial : ℝ) by
          refine Finset.prod_congr rfl (fun j hj => ?_)
          rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
          rw [Function.update_of_ne hj.2]]
        ring
      have hupdate_gamma :
          (∏ j, γ j ^ (Function.update α j₀ m j)) = γ j₀ ^ m * ∏ j, γ j ^ α j := by
        rw [hsplit (fun j => γ j ^ (Function.update α j₀ m j))]
        rw [hsplit (fun j => γ j ^ α j)]
        rw [Function.update_self, hα_j₀, pow_zero]
        rw [show γ j₀ ^ m * ∏ j ∈ Finset.univ \ {j₀}, γ j ^ Function.update α j₀ m j =
              γ j₀ ^ m * ∏ j ∈ Finset.univ \ {j₀}, γ j ^ α j by
          congr 1
          refine Finset.prod_congr rfl (fun j hj => ?_)
          rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
          rw [Function.update_of_ne hj.2]]
        ring
      have hupdate_W :
          (∏ j, wickMonomial (Function.update α j₀ m j) 1 (ξ j)) =
            wickMonomial m 1 (ξ j₀) * ∏ j, wickMonomial (α j) 1 (ξ j) := by
        rw [hsplit (fun j => wickMonomial (Function.update α j₀ m j) 1 (ξ j))]
        rw [hsplit (fun j => wickMonomial (α j) 1 (ξ j))]
        rw [Function.update_self, hα_j₀, wickMonomial_zero, one_mul]
        rw [show wickMonomial m 1 (ξ j₀) *
              ∏ j ∈ Finset.univ \ {j₀}, wickMonomial (Function.update α j₀ m j) 1 (ξ j) =
            wickMonomial m 1 (ξ j₀) *
              ∏ j ∈ Finset.univ \ {j₀}, wickMonomial (α j) 1 (ξ j) by
          congr 1
          refine Finset.prod_congr rfl (fun j hj => ?_)
          rw [Finset.mem_sdiff, Finset.mem_singleton] at hj
          rw [Function.update_of_ne hj.2]]
      rw [hupdate_factorial_R, hupdate_gamma, hupdate_W]
      -- After substitutions, both sides factor through γ_{j₀}^m · W_m 1 ξ_{j₀} · ∏γ^α · ∏ W α 1 ξ.
      -- The only remaining task is the coefficient identity:
      --   C(k, m) · (k-m)!/∏α! = k! / (m! · ∏α!).
      have hm_le : m ≤ k := Nat.lt_succ_iff.mp hm_lt
      have hpos_m : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
      have hpos_prod : (0 : ℝ) < (∏ j, ((α j).factorial : ℝ)) := by
        apply Finset.prod_pos
        intro j _
        exact_mod_cast Nat.factorial_pos _
      have hpos_km : (0 : ℝ) < ((k - m).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
      have hpos_prod_ne : (∏ j, ((α j).factorial : ℝ)) ≠ 0 := ne_of_gt hpos_prod
      have hpos_m_ne : (m.factorial : ℝ) ≠ 0 := ne_of_gt hpos_m
      have hcoef' : (k.choose m : ℝ) * ((k - m).factorial : ℝ) * (m.factorial : ℝ) =
                    (k.factorial : ℝ) := by
        have hkm : k.choose m * (k - m).factorial * m.factorial = k.factorial := by
          have h := Nat.choose_mul_factorial_mul_factorial hm_le
          linarith
        exact_mod_cast hkm
      field_simp
      linear_combination (γ j₀ ^ m * wickMonomial m 1 (ξ j₀) * (∏ j, γ j ^ α j) *
        (∏ j, wickMonomial (α j) 1 (ξ j))) * hcoef'

end
