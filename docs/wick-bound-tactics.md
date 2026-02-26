# Wick Bound: Lean 4 Tactical Implementation

This document provides concrete Lean 4 code snippets and helper lemmas for implementing `wick_bound`.

---

## Helper Lemmas to Define/Import

### 1. Product Rearrangement with succAbove

```lean
/-- Key identity for Wick bound: the product with succAbove covers all indices except j --/
private lemma prod_with_succAbove {M : Type*} [Monoid M]
    (x : Fin (m + 1) → M) (j : Fin (m + 1)) :
    x j * ∏ i : Fin m, x (j.succAbove i) = ∏ k : Fin (m + 1), x k := by
  rw [← Fin.prod_univ_succAbove x j]
  ring
```

This directly follows from `Fin.prod_univ_succAbove` in Mathlib:
```lean
theorem Fin.prod_univ_succAbove (f : Fin (n + 1) → M) (x : Fin (n + 1)) :
    ∏ i, f i = f x * ∏ i : Fin n, f (x.succAbove i)
```

### 2. Double Factorial Recursion

Mathlib provides:
```lean
theorem Nat.doubleFactorial_add_two (n : ℕ) :
    (n + 2).doubleFactorial = (n + 2) * n.doubleFactorial
```

For proofs, use:
```lean
rw [Nat.doubleFactorial_add_two]
```

### 3. Finite Sum of Constants

```lean
theorem Finset.sum_const (f : Finset ι) (a : M) :
    ∑ x in f, a = (f.card : ℕ) • a
```

For Fin type: `Fintype.card (Fin n) = n`

---

## The Calc Block Structure

### Overall Template

```lean
theorem wick_bound (n : ℕ) (f : Fin n → E) :
    ‖∫ ω : Configuration E, ∏ i, ω (f i) ∂(measure T)‖ ≤
      (n - 1).doubleFactorial * ∏ i, ‖T (f i)‖ := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    by_cases h_odd : Odd n
    · -- Case: n is odd
      sorry
    · -- Case: n is even
      push_neg at h_odd
      sorry
```

### Odd Case (Brief)

```lean
case pos =>
  -- n is odd, both sides are zero
  obtain ⟨k, rfl⟩ := h_odd
  rw [show (2 * k + 1 : ℕ) - 1 = 2 * k by omega]
  have := odd_moment_vanish T (2 * k) f
  rw [this]
  simp only [norm_zero]
  exact mul_nonneg (Nat.doubleFactorial_nonneg _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
```

### Even Case: Base Cases

```lean
case neg =>
  push_neg at h_odd
  -- For small even n, handle directly
  interval_cases n
  · -- n = 0: empty product
    simp [Fin.prod_empty, integral_const, norm_one]
  · -- n = 1: odd, skip by h_odd
    contradiction
  -- For n ≥ 2, proceed with induction
  -- Remaining case: n = m + 2 for some m
```

Or use `match`:
```lean
  match n with
  | 0 =>
    simp [Fin.prod_empty, integral_const, norm_one]
  | 1 =>
    simp only [Nat.odd_iff_not_even, decidable_not, Nat.even_one] at h_odd
    exact h_odd.elim trivial
  | m + 2 =>
    -- Main induction step
    sorry
```

### Even Case: Main Induction (m + 2)

```lean
  | m + 2 =>
    -- n = m + 2, which is even
    -- Goal: ‖∫ ω, ∏ i : Fin (m+2), ω(f i) ∂μ‖ ≤ (m+1)‼ * ∏ i, ‖T(f i)‖

    calc ‖∫ ω : Configuration E, ∏ i : Fin (m + 2), ω (f i) ∂(measure T)‖
        = ‖∫ ω, ω (f 0) * (∏ i : Fin (m + 1), ω (f (i.succ))) ∂(measure T)‖ := by
          congr 1
          ext ω
          simp only [Fin.prod_univ_succ]
      _ = ‖∑ j : Fin (m + 1), @inner ℝ H _ (T (f 0)) (T (f (j.succ))) *
          ∫ ω, (∏ i : Fin m, ω (f ((j.succAbove i).succ))) ∂(measure T)‖ := by
          congr 1
          exact (wick_recursive T (m + 1) (f 0) (fun i => f i.succ)).symm
      _ ≤ ∑ j : Fin (m + 1),
          ‖@inner ℝ H _ (T (f 0)) (T (f (j.succ))) *
          ∫ ω, (∏ i : Fin m, ω (f ((j.succAbove i).succ))) ∂(measure T)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ j : Fin (m + 1),
          (‖@inner ℝ H _ (T (f 0)) (T (f (j.succ)))‖ *
          ‖∫ ω, (∏ i : Fin m, ω (f ((j.succAbove i).succ))) ∂(measure T)‖) := by
          gcongr
          intro j
          exact norm_mul _ _
      _ ≤ ∑ j : Fin (m + 1),
          ((‖T (f 0)‖ * ‖T (f (j.succ))‖) *
          ‖∫ ω, (∏ i : Fin m, ω (f ((j.succAbove i).succ))) ∂(measure T)‖) := by
          gcongr
          intro j
          exact norm_inner_le_norm (T (f 0)) (T (f (j.succ)))
      _ ≤ ∑ j : Fin (m + 1),
          ((‖T (f 0)‖ * ‖T (f (j.succ))‖) *
          ((m - 1).doubleFactorial * ∏ i : Fin m, ‖T (f ((j.succAbove i).succ))‖)) := by
          gcongr
          intro j
          have hm : m < m + 2 := by omega
          have := ih m hm (fun i => f ((j.succAbove i).succ))
          exact this
      _ = ‖T (f 0)‖ * (m - 1).doubleFactorial *
          ∑ j : Fin (m + 1),
          (‖T (f (j.succ))‖ * ∏ i : Fin m, ‖T (f ((j.succAbove i).succ))‖) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
          ring_nf
      _ = ‖T (f 0)‖ * (m - 1).doubleFactorial *
          ∑ j : Fin (m + 1),
          ∏ i : Fin (m + 1), ‖T (f (i.succ))‖ := by
          congr 1
          ext1
          -- Apply prod_with_succAbove
          simp only [Finset.sum_congr rfl]
          intro j _
          exact (prod_with_succAbove (fun i : Fin (m + 1) => ‖T (f (i.succ))‖) j).symm
      _ = ‖T (f 0)‖ * (m - 1).doubleFactorial *
          ((m + 1 : ℕ) * ∏ i : Fin (m + 1), ‖T (f (i.succ))‖) := by
          rw [Finset.sum_const, Fintype.card_fin]
          simp [Nat.cast_add, Nat.cast_one]
      _ = ((m + 1) * (m - 1).doubleFactorial) *
          (‖T (f 0)‖ * ∏ i : Fin (m + 1), ‖T (f (i.succ))‖) := by
          ring
      _ = (m + 1).doubleFactorial * (‖T (f 0)‖ * ∏ i : Fin (m + 1), ‖T (f (i.succ))‖) := by
          congr 1
          exact (Nat.doubleFactorial_add_two m).symm
      _ = (m + 1).doubleFactorial * ∏ i : Fin (m + 2), ‖T (f i)‖ := by
          congr 1
          rw [← Fin.prod_univ_succ]
      _ = (m + 2 - 1).doubleFactorial * ∏ i : Fin (m + 2), ‖T (f i)‖ := by
          norm_num
```

---

## Key Tactic Patterns

### Pattern 1: Norm Inequality Chain

```lean
calc ‖something‖
    ≤ ∑ i, ‖individual_terms‖ := norm_sum_le _ _
    _ ≤ ∑ i, (‖factor1‖ * ‖factor2‖) := by gcongr; rw [norm_mul]
    _ ≤ ∑ i, (bound1 * bound2) := by gcongr; {apply specific_inequality}
```

### Pattern 2: Factoring Out Constants from Sum

```lean
calc ∑ i, (constant * f i)
    = constant * ∑ i, f i := by rw [← Finset.sum_mul]; ring
```

### Pattern 3: Applying Induction Hypothesis to Subterms

```lean
have hm : m < n := by omega
specialize ih m hm (fun i => reindexed_f i)
-- Now ih : ‖∫ ...‖ ≤ (m-1)‼ * ∏ i, ‖T (reindexed_f i)‖
```

### Pattern 4: Product Rearrangement

```lean
-- Before:
x j * ∏ i : Fin m, x (j.succAbove i)

-- After rearrangement using prod_with_succAbove:
∏ k : Fin (m + 1), x k
```

Tactic:
```lean
rw [prod_with_succAbove]
```

Or using `simp`:
```lean
simp only [← prod_with_succAbove]
```

### Pattern 5: Converting Between Different Equalities

When you have an equality that needs to be applied in a calc block:
```lean
have h : a = b := by ...
rw [← h]
-- or
calc ...
    = a := h.symm
    _ = b := ...
```

---

## Debugging Tips

### If the product rearrangement fails:

1. Check that `j.succAbove` is correctly typed as `Fin m → Fin (m+1)`
2. Verify that `succAbove j` partitions `Fin (m+1) \ {j}`
3. Use `#check Fin.prod_univ_succAbove` to see the exact statement in your context

### If norm inequalities don't compose:

1. Ensure each step introduces ≤ in the same direction
2. Use `gcongr` to handle congruence closure
3. If `gcongr` fails, manually apply lemmas with explicit arguments

### If induction hypothesis doesn't apply:

1. Verify `m < n` (use `omega`)
2. Check that the new function `fun i => f ...` has the right domain (`Fin m`)
3. Ensure you're applying `ih` before `rw` or other tactic modifications

### Handling type class issues:

If `norm_inner_le_norm` doesn't work:
```lean
-- Try explicit type class:
@norm_inner_le_norm ℝ H _ (T (f 0)) (T (f j))
-- or
have := @norm_inner_le_norm ℝ H inst1 inst2 inst3 (T (f 0)) (T (f j))
```

---

## Complete Template (Simplified)

```lean
theorem wick_bound (n : ℕ) (f : Fin n → E) :
    ‖∫ ω : Configuration E, ∏ i, ω (f i) ∂(measure T)‖ ≤
      (n - 1).doubleFactorial * ∏ i, ‖T (f i)‖ := by
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    match n with
    | 0 => simp [Fin.prod_empty, integral_const, norm_one]
    | 1 =>
      have h := measure_centered T (f 0)
      simp [h, norm_zero, Nat.doubleFactorial_zero]
    | n + 2 =>
      calc ‖∫ ω, ∏ i : Fin (n + 2), ω (f i) ∂(measure T)‖
          = ‖∫ ω, ω (f 0) * ∏ i : Fin (n + 1), ω (f i.succ) ∂(measure T)‖ := by
            congr 1; simp [Fin.prod_univ_succ]
        _ = ‖∑ j, ⟨T (f 0), T (f (j.succ))⟩ * ∫ ω, ∏ i : Fin n, ω (f ((j.succAbove i).succ)) ∂(measure T)‖ := by
            congr 1; exact (wick_recursive T (n + 1) (f 0) (fun i => f i.succ)).symm
        _ ≤ ∑ j, (‖T (f 0)‖ * ‖T (f (j.succ))‖) * ((n - 1).doubleFactorial *
            ∏ i : Fin n, ‖T (f ((j.succAbove i).succ))‖) := by
            rw [norm_sum_le]
            gcongr
            intro j
            rw [norm_mul, norm_mul]
            gcongr
            · exact norm_inner_le_norm (T (f 0)) (T (f (j.succ)))
            · exact ih n (by omega) _
        _ = (n + 1).doubleFactorial * ∏ i : Fin (n + 2), ‖T (f i)‖ := by
            -- Algebraic simplification
            sorry
```

---

## Imports Required

```lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.BigOperators
import Mathlib.Data.Nat.Factorial.DoubleFactorial
```

---

## References

- **Fin.prod_univ_succAbove:** Mathlib `Algebra.BigOperators.Fin`
- **norm_sum_le:** Mathlib `Analysis.Normed.Group.BigOperators`
- **norm_inner_le_norm:** Mathlib `Analysis.InnerProductSpace.Basic`
- **Nat.doubleFactorial_add_two:** Mathlib `Data.Nat.Factorial.DoubleFactorial`
