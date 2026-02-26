# Wick Bound: Mathlib Lemma Reference Guide

This document lists all Mathlib lemmas needed for the `wick_bound` proof with their exact names, signatures, and locations.

---

## 1. Fin Product Lemmas

### 1.1 Product Splitting at Index 0

```lean
@[to_additive]
theorem Fin.prod_univ_succ (f : Fin (n + 1) → M) :
    ∏ i, f i = f 0 * ∏ i : Fin n, f i.succ
```

**Location:** `Mathlib.Algebra.BigOperators.Fin`

**Use in wick_bound:**
- Split product ∏ᵢ₌₀^{n+2} ω(f i) into ω(f 0) and ∏ᵢ₌₀^{n+1} ω(f(i+1))
- Applied as: `rw [Fin.prod_univ_succ]`

**Related additive version:**
```lean
theorem Fin.sum_univ_succ (f : Fin (n + 1) → M) :
    ∑ i, f i = f 0 + ∑ i : Fin n, f i.succ
```

---

### 1.2 Product Partition Using succAbove

```lean
@[to_additive]
theorem Fin.prod_univ_succAbove (f : Fin (n + 1) → M) (x : Fin (n + 1)) :
    ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i)
```

**Location:** `Mathlib.Algebra.BigOperators.Fin`

**Signature breakdown:**
- `f : Fin (n + 1) → M` is the function to multiply
- `x : Fin (n + 1)` is the special index to extract
- `x.succAbove : Fin n → Fin (n + 1)` is the bijection from remaining indices
- The result: product = `f(x)` times product over the rest

**Use in wick_bound:**
- After Wick recursion, we have products with `succAbove j` partition
- Rearrange to get back the full product: `∏ᵢ ‖T(f(i.succ))‖`
- Applied in the key lemma `prod_with_succAbove`

**Example:**
```lean
-- For n=2, f : Fin 3 → M, j = 1:
-- ∏ i : Fin 3, f i = f 0 * f 1 * f 2
-- = f 1 * (f (1.succAbove 0) * f (1.succAbove 1))
-- = f 1 * (f 0 * f 2)  [since succAbove 1 maps 0→0, 1→2]
```

**Related:**
```lean
theorem Fin.prod_univ_castSucc (f : Fin (n + 1) → M) :
    ∏ i, f i = (∏ i : Fin n, f (Fin.castSucc i)) * f (Fin.last n)
```
This is the reverse partition (product at end instead of arbitrary position).

---

## 2. Norm Inequality Lemmas

### 2.1 Triangle Inequality for Sums

```lean
theorem norm_sum_le (f : ι → E) (s : Finset ι) :
    ‖∑ i in s, f i‖ ≤ ∑ i in s, ‖f i‖
```

**Location:** `Mathlib.Analysis.Normed.Group.BigOperators`

**Use in wick_bound:**
- After Wick recursion, we have `‖∑ j, (something)‖`
- Push norm inside: `≤ ∑ j, ‖...‖`
- Applied as: `exact norm_sum_le _ _` or `rw [norm_sum_le]`

**Type:** Works for normed groups / seminormed groups

---

### 2.2 Norm of Products

```lean
@[simp]
theorem norm_mul {G₀ : Type*} [SeminormedGroup G₀] (a b : G₀) :
    ‖a * b‖ = ‖a‖ * ‖b‖
```

**Location:** `Mathlib.Analysis.Normed.Group.Basic`

**Use in wick_bound:**
- Split `‖inner_product * integral‖` into norms
- Applied as: `rw [norm_mul]`

**Variant for commutative:**
```lean
theorem norm_mul_le {E : Type*} [SeminormedAddCommGroup E] [SMulCommClass ℝ ℝ E]
    (a b : E) : ‖a * b‖ ≤ ‖a‖ * ‖b‖
-- but equality version above is stronger
```

---

### 2.3 Cauchy-Schwarz Inequality (Norm Form)

```lean
theorem norm_inner_le_norm (x y : E) :
    ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖
```

**Location:** `Mathlib.Analysis.InnerProductSpace.Basic`

**Context:**
- Requires: `InnerProductSpace ℝ E` (or other field 𝕜)
- `⟪·,·⟫` is the inner product notation (angle brackets)
- `‖·‖` is the induced norm

**Use in wick_bound:**
- Bound the inner product term: `‖⟨Tf₀, Tfⱼ⟩‖ ≤ ‖Tf₀‖ * ‖Tfⱼ‖`
- Applied as: `exact norm_inner_le_norm (T (f 0)) (T (f j.succ))`

**Related lemmas:**
```lean
theorem re_inner_le_norm (x y : E) : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖

theorem nnnorm_inner_le_nnnorm (x y : E) : ‖⟪x, y⟫‖₊ ≤ ‖x‖₊ * ‖y‖₊
-- Nonnegative reals version
```

---

## 3. Finset and Sum Lemmas

### 3.1 Sum of Constants

```lean
@[simp]
theorem Finset.sum_const (s : Finset ι) (b : M) :
    (∑ x in s, b) = (s.card : ℕ) • b
```

**Location:** `Mathlib.Data.Finset.Basic` (or `Finset.Basic`)

**Use in wick_bound:**
- After showing the summand is constant w.r.t. index j
- `∑ⱼ C = card(Fin(m+1)) • C = (m+1) • C`
- Applied as: `rw [Finset.sum_const]`

**For Fin specifically:**
```lean
-- After rw [Finset.sum_const]:
goal: ... = (Fintype.card (Fin (m + 1)) : ℕ) • ...
-- Then use Fintype.card_fin (see below)
```

---

### 3.2 Cardinality of Fin Type

```lean
@[simp]
theorem Fintype.card_fin (n : ℕ) : Fintype.card (Fin n) = n
```

**Location:** `Mathlib.Data.Fin.Basic` or `Mathlib.Data.Fintype.Card`

**Use in wick_bound:**
- After `∑ⱼ₌₀^{m} C`, the sum equals `Fintype.card (Fin (m+1)) • C`
- Replace with `(m+1) • C`
- Applied as: `simp [Fintype.card_fin]` or `rw [Fintype.card_fin]`

---

### 3.3 Extracting Constants from Sums

```lean
theorem Finset.sum_mul (s : Finset ι) (a : M) (f : ι → M) :
    (∑ x in s, a * f x) = a * ∑ x in s, f x
```

**Location:** `Mathlib.Data.Finset.Basic`

**Use in wick_bound:**
- Factor out `‖T(f 0)‖` from the sum
- Applied as: `rw [← Finset.sum_mul]` (backwards)

**Variant:**
```lean
theorem Finset.mul_sum (s : Finset ι) (a : M) (f : ι → M) :
    (∑ x in s, f x * a) = (∑ x in s, f x) * a
```

---

## 4. Natural Number Lemmas

### 4.1 Double Factorial Recursion

```lean
theorem Nat.doubleFactorial_add_two (n : ℕ) :
    (n + 2).doubleFactorial = (n + 2) * n.doubleFactorial
```

**Location:** `Mathlib.Data.Nat.Factorial.DoubleFactorial`

**Signature breakdown:**
- Defines: `n‼ := n * (n-2)‼` for n ≥ 2
- Base cases: `0‼ = 1`, `1‼ = 1`
- Recursion: `(n+2)‼ = (n+2) * n‼`

**Use in wick_bound:**
- Convert `(m-1)‼ * (m+1)` to `(m+1)‼`
- Because: `(m+1)‼ = (m+1) * ((m+1)-2)‼ = (m+1) * (m-1)‼`
- Applied as: `rw [Nat.doubleFactorial_add_two]` (possibly backwards with `←`)

**Related lemmas:**
```lean
theorem Nat.doubleFactorial_zero : (0 : ℕ).doubleFactorial = 1
theorem Nat.doubleFactorial_one : (1 : ℕ).doubleFactorial = 1
theorem Nat.doubleFactorial_even (n : ℕ) : (2 * n).doubleFactorial = 2^n * n!
theorem Nat.doubleFactorial_odd (n : ℕ) : (2 * n + 1).doubleFactorial = ?
```

---

### 4.2 Double Factorial Nonnegative

```lean
theorem Nat.doubleFactorial_nonneg (n : ℕ) : 0 ≤ n.doubleFactorial
-- or in Nat, just use positivity tactic
```

**Location:** `Mathlib.Data.Nat.Factorial.DoubleFactorial`

**Use in wick_bound:**
- For odd case, show RHS is non-negative
- Used with `mul_nonneg` to combine factors

---

## 5. Tactic References

### 5.1 Goal Congruence (gcongr)

```lean
gcongr
-- Applies congruence closure to inequalities
-- Useful for: ∑ a_i ≤ ∑ b_i when a_i ≤ b_i
```

**Use:** After `calc` chain when ≤ propagates through operators

### 5.2 Arithmetic (omega)

```lean
omega
-- Solves linear arithmetic over ℕ, ℤ, etc.
```

**Use:** Proving `m < m + 2` or `m + 2 - 1 = m + 1`

### 5.3 Simplification (simp)

```lean
simp [lemma1, lemma2]
-- Applies rewriting rules
```

**Use:** After major steps to clean up remaining goals

---

## 6. Complete Imports Block

```lean
import Mathlib.Algebra.BigOperators.Fin          -- Fin.prod_univ_succ, etc.
import Mathlib.Analysis.InnerProductSpace.Basic  -- norm_inner_le_norm
import Mathlib.Analysis.Normed.Group.BigOperators -- norm_sum_le
import Mathlib.Data.Fin.Basic                    -- Fin operations
import Mathlib.Data.Nat.Factorial.DoubleFactorial -- doubleFactorial
import Mathlib.Data.Fintype.Card                 -- Fintype.card_fin
```

---

## 7. Quick Reference Table

| Name | Type | Signature | Module | Used for |
|------|------|-----------|--------|----------|
| `prod_univ_succ` | Lemma | `∏ i, f i = f 0 * ∏ i, f i.succ` | `BigOperators.Fin` | Splitting product |
| `prod_univ_succAbove` | Lemma | `∏ i, f i = f x * ∏ i, f (x.succAbove i)` | `BigOperators.Fin` | Rearranging products |
| `norm_sum_le` | Theorem | `‖∑ i, f i‖ ≤ ∑ i, ‖f i‖` | `Normed.Group.BigOperators` | Triangle inequality |
| `norm_mul` | Theorem | `‖a * b‖ = ‖a‖ * ‖b‖` | `Normed.Group.Basic` | Splitting norms |
| `norm_inner_le_norm` | Theorem | `‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖` | `InnerProductSpace.Basic` | Cauchy-Schwarz |
| `sum_const` | Theorem | `∑ x in s, c = s.card • c` | `Finset.Basic` | Constant sums |
| `card_fin` | Theorem | `card (Fin n) = n` | `Fintype.Card` | Cardinality |
| `sum_mul` | Theorem | `∑ x, a * f x = a * ∑ x, f x` | `Finset.Basic` | Factoring |
| `doubleFactorial_add_two` | Theorem | `(n+2)‼ = (n+2) * n‼` | `Nat.Factorial.DoubleFactorial` | DF recursion |

---

## 8. Common Patterns and Their Mathlib Counterparts

### Pattern: Push norm through a sum
```lean
calc ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
```

### Pattern: Split norm of product
```lean
have := norm_mul (a : E) (b : E)  -- ‖a * b‖ = ‖a‖ * ‖b‖
```

### Pattern: Cauchy-Schwarz on inner product
```lean
calc ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm x y
```

### Pattern: Factor constant from sum
```lean
calc ∑ i, a * f i = a * ∑ i, f i := by rw [← sum_mul]
```

### Pattern: Partition Fin product
```lean
calc ∏ i, f i = f j * ∏ i, f (j.succAbove i) :=
  (Fin.prod_univ_succAbove f j).symm
```

---

## 9. Type Class Dependencies

To use these lemmas, ensure the following instances are available:

```lean
variable {E : Type*} [AddCommGroup E]
variable {M : Type*} [Monoid M]
variable (x y : H) where H : Type* [NormedAddCommGroup H]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
```

For `wick_bound`, ensure:
```lean
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
```

---

## 10. Debugging: When Lemmas Don't Apply

### Issue: Type mismatch in `norm_inner_le_norm`

```lean
-- If you get an error, try:
@norm_inner_le_norm ℝ H inst1 inst2 inst3 (T (f 0)) (T (f j))
-- or check that T maps into an InnerProductSpace
```

### Issue: `prod_univ_succAbove` doesn't simplify

```lean
-- Try using with explicit arguments:
rw [Fin.prod_univ_succAbove (fun i => ‖T(f i)‖) j]
```

### Issue: Sum doesn't become constant

```lean
-- Verify the inner expression is truly independent of the summation index:
simp only [Finset.sum_congr rfl]
intro j _
-- Show the term is the same for all j
```

---

## References

- **Mathlib Docs:** https://mathlib4.github.io/
- **Fin operations:** Search "Fin.prod" in Mathlib
- **BigOperators:** `Mathlib.Algebra.BigOperators.Fin`
- **Norms:** `Mathlib.Analysis.Normed.Group.Basic`
- **Factorial:** `Mathlib.Data.Nat.Factorial.DoubleFactorial`
