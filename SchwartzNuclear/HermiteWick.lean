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

end
