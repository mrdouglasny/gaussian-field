# Wick Bound Proof Strategy in Lean 4

## Overview

This document provides a detailed step-by-step strategy for proving `wick_bound` in Lean 4:

```lean
theorem wick_bound (n : ℕ) (f : Fin n → E) :
    ‖∫ ω : Configuration E, ∏ i, ω (f i) ∂(measure T)‖ ≤
      (n - 1).doubleFactorial * ∏ i, ‖T (f i)‖
```

The proof combines induction, the recursive Wick formula, Cauchy-Schwarz, and the key combinatorial identity `Fin.prod_univ_succAbove`.

---

## 1. Induction Strategy

### Why Strong Induction?

The tool `wick_recursive` reduces a moment of order n to a sum of moments of order n-2:
```
∫ ω, ω f₀ * ∏ᵢ ω (gᵢ) ∂μ = ∑ⱼ ⟨Tf₀, Tgⱼ⟩ * ∫ ω, ∏ᵢ ω (g (succAbove j i)) ∂μ
```

This **n → n-2** structure requires **strong induction** (`Nat.strong_induction_on`), not simple induction.

### Lean 4 Setup

```lean
theorem wick_bound (n : ℕ) (f : Fin n → E) : ... := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    -- ih : ∀ k < n, P k
    -- Goal: P n
    ...
```

---

## 2. Case Analysis by Parity

The proof naturally splits based on whether n is odd or even.

### Case 1: n is Odd

**Key Fact:** `odd_moment_vanish` states that the integral is zero.

```lean
have h_odd : Odd n := by {construct from hypothesis}
obtain ⟨k, hk⟩ := h_odd
rw [hk]
-- Now n = 2*k + 1
rw [odd_moment_vanish]
simp only [norm_zero]
-- Goal: 0 ≤ (n-1).doubleFactorial * ∏ i, ‖T (f i)‖
exact mul_nonneg (Nat.doubleFactorial_nonneg _)
  (Finset.prod_nonneg fun _ _ => norm_nonneg _)
```

### Case 2: n is Even (main induction)

The proof uses a `calc` block for the chain of inequalities. We handle base cases separately:
- **n = 0**: Trivial (empty product = 1, integral of 1 = 1, doubleFactorial 0 = 1)
- **n ≥ 2 and even**: Use strong induction with n = m + 2

```lean
match n with
| 0 => simp [Fin.prod_empty]
| 1 => contradiction with h_even
| m + 2 =>
  -- m + 2 is even, and m < m + 2
  -- Use ih m to bound the integral over Fin m
```

---

## 3. Main Induction Step: From n = m+2 to the Bound

### 3.1 Split the Product (using Fin.prod_univ_succ)

**Goal:** `‖∫ ω, ∏ i : Fin (m+2), ω (f i) ∂μ‖ ≤ ...`

Start by rewriting the product:
```lean
calc ‖∫ ω : Configuration E, ∏ i : Fin (m+2), ω (f i) ∂(measure T)‖
    = ‖∫ ω, ω (f 0) * ∏ i : Fin (m+1), ω (f i.succ) ∂μ‖ := by
      congr 1
      ext ω
      rw [Fin.prod_univ_succ]
```

This converts the product over Fin (m+2) into:
- One term: ω(f 0)
- A product over Fin (m+1): ∏ᵢ₊₁ ω(f(i+1))

### 3.2 Apply Wick's Recursive Formula (wick_recursive)

The integral now has the form: `∫ ω, ω(f₀) * (∏ᵢ ω(gᵢ)) ∂μ`

Apply `wick_recursive`:
```lean
    _ = ‖∑ j : Fin (m+1), @inner ℝ H _ (T (f 0)) (T (f j.succ)) *
        ∫ ω, ∏ i : Fin m, ω (f (j.succAbove i).succ) ∂μ‖ := by
      congr 1
      rw [wick_recursive T (m+1) (f 0) (fun i => f i.succ)]
```

Key details:
- After `wick_recursive`, we get: `∑ j, ⟨Tf₀, Tf_{j+1}⟩ * (integral over succAbove)`
- The product in the integral is now over `Fin m` (order reduced by 2)
- For each j, we apply the induction hypothesis to the integral over Fin m

### 3.3 Push Norm Through Sum (Triangle Inequality)

```lean
    _ ≤ ∑ j, ‖@inner ℝ H _ (T (f 0)) (T (f j.succ)) *
        ∫ ω, ∏ i : Fin m, ω (f (j.succAbove i).succ) ∂μ‖ := by
      exact norm_sum_le _ _
```

**Mathlib:** `norm_sum_le : ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖`

### 3.4 Split Product Norms and Apply Cauchy-Schwarz

```lean
    _ ≤ ∑ j, ‖@inner ℝ H _ (T (f 0)) (T (f j.succ))‖ *
        ‖∫ ω, ∏ i : Fin m, ω (f (j.succAbove i).succ) ∂μ‖ := by
      gcongr
      intro j
      rw [norm_mul]
```

Then apply Cauchy-Schwarz to the inner product:
```lean
    _ ≤ ∑ j, (‖T (f 0)‖ * ‖T (f j.succ)‖) *
        ‖∫ ω, ∏ i : Fin m, ω (f (j.succAbove i).succ) ∂μ‖ := by
      gcongr
      intro j
      exact norm_inner_le_norm (T (f 0)) (T (f j.succ))
```

**Mathlib:** `norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖`

### 3.5 Apply Induction Hypothesis

Each integral in the sum is over `Fin m`, which has strictly fewer elements than `m + 2 = n`. So we can apply `ih m`:

```lean
    _ ≤ ∑ j, (‖T (f 0)‖ * ‖T (f j.succ)‖) *
        ((m - 1).doubleFactorial * ∏ i : Fin m, ‖T (f (j.succAbove i).succ)‖) := by
      gcongr
      intro j
      have hm : m < m + 2 := by omega
      specialize ih m hm (fun i => f (j.succAbove i).succ)
      exact ih
```

**Key fact:** After applying `ih m`, the integral `‖∫ ω, ∏ i : Fin m, ω (f (j.succAbove i).succ) ∂μ‖` is bounded by `(m-1).doubleFactorial * ∏ᵢ ‖T(f((j.succAbove i).succ))‖`.

### 3.6 Algebraic Simplification and Product Rearrangement

Now we need to simplify:
```
∑ j, ‖T(f 0)‖ * ‖T(f j.succ)‖ * ((m-1)‼ * ∏ᵢ ‖T(f((succAbove j i).succ))‖)
```

#### 3.6a. Factor Out Constants

The terms `‖T(f 0)‖` and `(m-1).doubleFactorial` don't depend on j:

```lean
    _ = ‖T (f 0)‖ * (m - 1).doubleFactorial *
        ∑ j, ‖T (f j.succ)‖ * ∏ i : Fin m, ‖T (f (j.succAbove i).succ)‖ := by
      rw [Finset.sum_mul, Finset.mul_sum]
      ring_nf
```

#### 3.6b. Key Combinatorial Identity

**Lemma:** For any function `x : Fin (m+1) → ℝ` and `j : Fin (m+1)`:
```
x j * ∏ᵢ₌₀^{m-1} x (succAbove j i) = ∏ₖ₌₀^m x k
```

**Why?** The `succAbove j` function partitions `Fin (m+1) \ {j}` bijectively to `Fin m`. So the product over `succAbove j` covers all elements except j. Multiplying by `x j` gives the full product.

**Proof using Mathlib:**
```lean
lemma prod_with_succAbove (x : Fin (m + 1) → ℝ) (j : Fin (m + 1)) :
    x j * ∏ i : Fin m, x (j.succAbove i) = ∏ k : Fin (m + 1), x k := by
  rw [← Fin.prod_univ_succAbove x j]
  ring
```

**Mathlib lemma:** `Fin.prod_univ_succAbove (f : Fin (n+1) → M) (x : Fin (n+1)) : ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i)`

Apply this to our sum:
```lean
    _ = ‖T (f 0)‖ * (m - 1).doubleFactorial *
        ∑ j, ∏ i : Fin (m + 1), ‖T (f i.succ)‖ := by
      congr 1
      ext1
      -- Using prod_with_succAbove for the specific case
      ...
```

#### 3.6c. Sum of Constants

The inner product is constant (doesn't depend on j), so:
```lean
    _ = ‖T (f 0)‖ * (m - 1).doubleFactorial *
        (Fintype.card (Fin (m + 1))) * ∏ i : Fin (m + 1), ‖T (f i.succ)‖ := by
      rw [Finset.sum_const]
      simp [Fintype.card_fin]
```

**Mathlib:** `Fintype.card (Fin n) = n`

The card of `Fin (m+1)` is `m+1`, so:
```lean
    _ = ‖T (f 0)‖ * (m - 1).doubleFactorial * (m + 1) *
        ∏ i : Fin (m + 1), ‖T (f i.succ)‖ := by
      simp [Fintype.card_fin]
      ring
```

### 3.7 Combine Double Factorials

For even n = m+2, we have n-1 = m+1 (which is odd):
```
(m+1)‼ = (m+1) * (m-1)‼
```

So: `(m - 1).doubleFactorial * (m + 1) = (m + 1).doubleFactorial`

```lean
    _ = (m - 1).doubleFactorial * (m + 1) *
        (‖T (f 0)‖ * ∏ i : Fin (m + 1), ‖T (f i.succ)‖) := by
      ring
    _ = (m + 1).doubleFactorial *
        (‖T (f 0)‖ * ∏ i : Fin (m + 1), ‖T (f i.succ)‖) := by
      congr 1
      rw [Nat.doubleFactorial_add_two]
```

**Mathlib:** `Nat.doubleFactorial_add_two : (n+2)‼ = (n+2) * n‼`

### 3.8 Reconstruct the Final Product

The product `‖T(f 0)‖ * ∏ᵢ₌₀^{m+1} ‖T(f(i.succ))‖` is exactly the full product `∏ᵢ₌₀^{m+2} ‖T(f i)‖`:

```lean
    _ = (m + 1).doubleFactorial * ∏ i : Fin (m + 2), ‖T (f i)‖ := by
      congr 1
      rw [← Fin.prod_univ_succ]
```

**Mathlib:** `Fin.prod_univ_succ (f : Fin (n+1) → M) : ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ`

### 3.9 Relate Back to n

Since n = m + 2, we have n - 1 = m + 1:
```lean
    _ = (n - 1).doubleFactorial * ∏ i : Fin n, ‖T (f i)‖ := by
      congr 1
      omega
```

---

## 4. Key Mathlib Lemmas Required

| Lemma | Module | Purpose |
|-------|--------|---------|
| `Fin.prod_univ_succAbove` | `Algebra.BigOperators.Fin` | Partition products using `succAbove` |
| `Fin.prod_univ_succ` | `Algebra.BigOperators.Fin` | Split product at index 0 |
| `norm_sum_le` | `Analysis.Normed.Group.BigOperators` | Triangle inequality for sums |
| `norm_mul` | `Analysis.Normed.Group.Basic` | Multiplicativity of norm |
| `norm_inner_le_norm` | `Analysis.InnerProductSpace.Basic` | Cauchy-Schwarz inequality |
| `Nat.doubleFactorial_add_two` | `Data.Nat.Factorial.DoubleFactorial` | Recursion for double factorial |
| `Fintype.card_fin` | `Data.Fin.Basic` | Cardinality of Fin type |
| `Finset.sum_const` | `Data.Finset.Basic` | Sum of constant |

---

## 5. Proof Outline (Pseudocode)

```lean
theorem wick_bound (n : ℕ) (f : Fin n → E) : ... := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases h_odd : Odd n
    case pos =>  -- n is odd
      obtain ⟨k, rfl⟩ := h_odd
      rw [odd_moment_vanish]
      simp [norm_zero, mul_nonneg]
    case neg =>  -- n is even
      push_neg at h_odd  -- Now h_even : Even n
      match n with
      | 0 => simp [Fin.prod_empty, integral_one]
      | 1 => contradiction -- 1 is odd
      | n + 2 =>
        set m := n with hm_def
        calc ‖∫ ω, ∏ i : Fin (m+2), ω (f i) ∂(measure T)‖
            = ‖∫ ω, ω (f 0) * ∏ i : Fin (m+1), ω (f i.succ) ∂μ‖ := by
              rw [Fin.prod_univ_succ]
          _ = ‖∑ j, ⟨T(f 0), T(f j.succ)⟩ * ∫ ω, ∏ i, ω(f((succAbove j i).succ)) ∂μ‖ := by
              rw [wick_recursive]
          _ ≤ ∑ j, ‖⟨T(f 0), T(f j.succ)⟩ * ∫ ...‖ := norm_sum_le _ _
          _ ≤ ∑ j, ‖⟨T(f 0), T(f j.succ)⟩‖ * ‖∫ ...‖ := by gcongr; rw [norm_mul]
          _ ≤ ∑ j, (‖T(f 0)‖ * ‖T(f j.succ)‖) * ‖∫ ...‖ := by
              gcongr; exact norm_inner_le_norm _ _
          _ ≤ ∑ j, (‖T(f 0)‖ * ‖T(f j.succ)‖) *
              ((m-1)‼ * ∏ i, ‖T(f((succAbove j i).succ))‖) := by
              gcongr
              intro j
              exact ih m (by omega) _
          _ = ‖T(f 0)‖ * (m-1)‼ * ∑ j,
              (‖T(f j.succ)‖ * ∏ i, ‖T(f((succAbove j i).succ))‖) := by ring
          _ = ‖T(f 0)‖ * (m-1)‼ * ∑ j, ∏ i : Fin(m+1), ‖T(f i.succ)‖ := by
              -- Using prod_with_succAbove lemma
          _ = ‖T(f 0)‖ * (m-1)‼ * (m+1) * ∏ i : Fin(m+1), ‖T(f i.succ)‖ := by
              rw [Finset.sum_const, Fintype.card_fin]
          _ = (m+1)‼ * (‖T(f 0)‖ * ∏ i : Fin(m+1), ‖T(f i.succ)‖) := by
              rw [Nat.doubleFactorial_add_two]; ring
          _ = (m+1)‼ * ∏ i : Fin(m+2), ‖T(f i)‖ := by
              rw [← Fin.prod_univ_succ]
          _ = (n-1)‼ * ∏ i : Fin n, ‖T(f i)‖ := by omega
```

---

## 6. Tricky Points and Solutions

### 6.1 Handling the succAbove Indexing

**Problem:** After applying `wick_recursive`, the integral has `f((succAbove j i).succ)`, which is confusing.

**Solution:** Use the lemma:
```lean
lemma succAbove_composition (j : Fin (m+1)) (i : Fin m) :
    (j.succAbove i).succ = f ((Fin.succ j).succAbove i)  -- adjust as needed
```

Alternatively, think of `succAbove j` as a bijection from `Fin m` to `Fin (m+1) \ {j}`. The `.succ` shifts indices.

### 6.2 Double Factorial for Even vs. Odd n

- For **odd** n = 2k+1: (2k)‼ = 2k * (2k-2) * ... * 2 (even double factorial)
- For **even** n = 2k: (2k-1)‼ = (2k-1) * (2k-3) * ... * 1 (odd double factorial)

The recursion formula is: `(n+2)‼ = (n+2) * n‼`

### 6.3 Product Rearrangement

The key insight is:
```
∏ᵢ₌₀^n f(i) = f(j) * ∏ᵢ₌₀^{n-1} f(succAbove j i)
```

This is because `succAbove j` is a bijection from `Fin n` to `{0,...,n}\{j}`. So:
- `succAbove j 0, succAbove j 1, ..., succAbove j (n-1)` covers all indices except j
- Multiplying by `f(j)` gives the full product

Mathlib has: `Fin.prod_univ_succAbove` which exactly formalizes this.

### 6.4 Casting Between Norms and Real Numbers

Norms take values in `ℝ≥0` or `ℝ`. When working with products of norms:
```lean
∏ i, ‖T(f i)‖  : ℝ
```

Be careful with `Finset.prod` vs `∏` (product notation). Usually Lean infers the right type.

---

## 7. Summary of Tactics

| Tactic | Use Case |
|--------|----------|
| `norm_sum_le` | Push norm inside sum (triangle inequality) |
| `gcongr` | Goal congruence (useful for combining multiple ≤ steps) |
| `rw [norm_mul]` | Split `‖a * b‖` into `‖a‖ * ‖b‖` |
| `omega` | Arithmetic on natural numbers |
| `ring` | Polynomial ring identities |
| `simp [Fin.prod_...]` | Simplify product identities |
| `Finset.sum_const` | Sum of constant |
| `exact norm_inner_le_norm` | Cauchy-Schwarz |

---

## References

- **Wick's Theorem:** Janson, "Gaussian Hilbert Spaces", Theorem 1.28
- **Double Factorial:** OEIS A001147, A006882
- **Fin.prod_univ_succAbove:** Mathlib documentation, `Algebra.BigOperators.Fin`
