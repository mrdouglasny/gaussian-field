# Wick Bound Proof: Complete Summary

## Executive Summary

The `wick_bound` theorem states that n-point functions of a Gaussian measure are bounded by the double factorial of n-1 times the product of operator norms:

```
‖E[∏ᵢ ω(fᵢ)]‖ ≤ (n-1)‼ · ∏ᵢ ‖T(fᵢ)‖
```

The proof uses **strong induction** combined with the **recursive Wick formula**, **Cauchy-Schwarz inequality**, and the key combinatorial identity `Fin.prod_univ_succAbove` from Mathlib.

---

## High-Level Proof Strategy

### 1. Induction Choice: Strong Induction

Because `wick_recursive` reduces moments by 2 (n → n-2), we use:
```lean
induction n using Nat.strong_induction_on with | ind n ih =>
```

This allows us to assume the bound holds for all k < n and prove it for n.

### 2. Case Split: Odd vs. Even

- **Odd n:** Use `odd_moment_vanish` to show the integral is 0. The bound is trivial since 0 ≤ anything.
- **Even n:** Main induction. Decompose n = m + 2 and use the n-2 recursive structure.

### 3. Main Proof Structure for Even n = m + 2

1. **Split the product** using `Fin.prod_univ_succ`
   ```
   ∏ᵢ₌₀^{m+1} ω(f i) = ω(f 0) · ∏ᵢ₌₀^m ω(f(i+1))
   ```

2. **Apply Wick recursion** using `wick_recursive`
   ```
   ∫ ω(f₀)·∏ᵢ ω(gᵢ) dμ = ∑ⱼ ⟨Tf₀, Tgⱼ⟩ · ∫ ∏_{i≠j} ω(gᵢ) dμ
   ```

3. **Push norm through sum** using `norm_sum_le` (triangle inequality)
   ```
   ‖∑ aᵢ‖ ≤ ∑ ‖aᵢ‖
   ```

4. **Apply Cauchy-Schwarz** using `norm_inner_le_norm`
   ```
   ‖⟨x, y⟩‖ ≤ ‖x‖ · ‖y‖
   ```

5. **Apply induction hypothesis** to each integral
   ```
   ‖∫ ∏ᵢ₌₀^{m} ω(fᵢ) dμ‖ ≤ (m-1)‼ · ∏ᵢ ‖T(fᵢ)‖
   ```

6. **Rearrange products** using `Fin.prod_univ_succAbove`
   ```
   x(j) · ∏ᵢ x(succAbove j i) = ∏ₖ x(k)
   ```

7. **Sum of constants** using `Finset.sum_const`
   ```
   ∑ⱼ C = (m+1) · C
   ```

8. **Combine double factorials** using `Nat.doubleFactorial_add_two`
   ```
   (m+1)‼ = (m+1) · (m-1)‼
   ```

9. **Reconstruct the full product** using `Fin.prod_univ_succ` (backwards)
   ```
   ‖T(f 0)‖ · ∏ᵢ₌₀^{m} ‖T(f(i+1))‖ = ∏ᵢ₌₀^{m+1} ‖T(f i)‖
   ```

---

## Key Mathematical Insights

### 1. Why Strong Induction?

The recursive formula reduces the order by exactly 2:
- Start with n variables
- Apply `wick_recursive`: reduces to n-1 variables (in the index set of partners)
- Each integral has n-2 variables

For simple induction (n → n+1), we couldn't use the hypothesis at n-2. Strong induction is essential.

### 2. The succAbove Partition

For any index j in a finite set of size m+1:
- `succAbove j` is a bijection from Fin m to Fin(m+1) \ {j}
- It maps i ∈ {0,...,m-1} to the i-th element of {0,...,m} \ {j}

**Key identity:**
```
∏ₖ₌₀^{m+1} f(k) = f(j) · ∏ᵢ₌₀^{m-1} f(succAbove j i)
```

This is **exactly** `Fin.prod_univ_succAbove` in Mathlib.

### 3. Why the Double Factorial?

- The sum ∑ⱼ over m+1 terms gives factor (m+1)
- Combined with (m-1)‼ from IH: (m+1) · (m-1)‼ = (m+1)‼
- This is the (n-1)‼ for even n = m+2

### 4. Cauchy-Schwarz Boundary Case

The inner product ⟨Tf₀, Tfⱼ⟩ is bounded by:
```
|⟨Tf₀, Tfⱼ⟩| ≤ ‖Tf₀‖ · ‖Tfⱼ‖
```

This is the norm form of Cauchy-Schwarz: `norm_inner_le_norm` in Mathlib.

---

## Mathlib Lemmas Used

| Lemma | Signature | Purpose |
|-------|-----------|---------|
| `Fin.prod_univ_succAbove` | `∏ i, f i = f x · ∏ i, f (x.succAbove i)` | Partition products |
| `Fin.prod_univ_succ` | `∏ i, f i = f 0 · ∏ i, f i.succ` | Split at index 0 |
| `norm_sum_le` | `‖∑ i, f i‖ ≤ ∑ i, ‖f i‖` | Triangle inequality |
| `norm_mul` | `‖a · b‖ = ‖a‖ · ‖b‖` | Multiplicativity |
| `norm_inner_le_norm` | `‖⟪x, y⟫‖ ≤ ‖x‖ · ‖y‖` | Cauchy-Schwarz |
| `Nat.doubleFactorial_add_two` | `(n+2)‼ = (n+2) · n‼` | DF recursion |
| `Finset.sum_const` | `∑ C = card · C` | Constant sums |
| `Fintype.card_fin` | `card (Fin n) = n` | Cardinality |

---

## Proof Structure in Lean 4

```lean
theorem wick_bound (n : ℕ) (f : Fin n → E) : ... := by
  induction n using Nat.strong_induction_on with | ind n ih =>
    match n with
    | 0 => -- base case
    | 1 => -- odd case
    | n + 2 =>
      calc ‖∫ ω, ∏ i : Fin (n + 2), ω (f i) ∂μ‖
          = ... [Fin.prod_univ_succ]
        _ = ... [wick_recursive]
        _ ≤ ... [norm_sum_le]
        _ ≤ ... [norm_mul, Cauchy-Schwarz]
        _ ≤ ... [induction hypothesis ih]
        _ = ... [product rearrangement]
        _ = ... [constant sum]
        _ = ... [double factorial]
        _ = ... [product reconstruction]
```

---

## Common Pitfalls and Solutions

### 1. Type Confusion with Products

**Problem:** `∏ i : Fin n, ‖T(f i)‖` might have type issues.

**Solution:** Be explicit with type annotations when needed:
```lean
∏ i : Fin n, (‖T(f i)‖ : ℝ)
```

### 2. succAbove Application Order

**Problem:** After `wick_recursive`, you have `f((succAbove j i).succ)` which is confusing.

**Solution:** Trace through the indices carefully:
- `j : Fin (m+1)` (partner index)
- `i : Fin m` (remaining indices)
- `succAbove j i : Fin (m+1)` (the i-th element of Fin(m+1) \ {j})
- `.succ` shifts back from the original indexing

### 3. Double Factorial Edge Cases

**Problem:** `(n-1).doubleFactorial` when n is small.

**Solution:** Lean's `Nat` subtraction is truncated (n-1 = 0 if n = 0):
- `0 - 1 = 0` in Nat
- `0‼ = 1`
- `1‼ = 1`

Handle with `omega` tactic for arithmetic.

### 4. Applying wick_recursive Correctly

**Problem:** The direction of the equality.

**Solution:**
```lean
-- wick_recursive gives:
rw [wick_recursive T (m + 1) (f 0) (fun i => f i.succ)]

-- Or if you need the reverse:
rw [← wick_recursive ...]
```

---

## Verification Checklist

Before finalizing the proof, verify:

- [ ] Odd case uses `odd_moment_vanish` and shows 0 ≤ RHS
- [ ] Base case n=0 is handled (empty product = 1)
- [ ] Base case n=1 is handled or deferred to odd case
- [ ] Main step uses strong induction with `ih m` where `m < n`
- [ ] `wick_recursive` is applied correctly to the product split by `Fin.prod_univ_succ`
- [ ] All norm inequalities are in the same direction (≤)
- [ ] `prod_with_succAbove` rearranges products correctly
- [ ] Sum of constants reduces to multiplication by cardinality
- [ ] Double factorial recursion `(m+1)‼ = (m+1) · (m-1)‼` is applied
- [ ] Final product reconstruction matches the goal

---

## Proof Complexity Metrics

| Component | Complexity | Lines of Lean |
|-----------|-----------|---------------|
| Odd case | Trivial | ~5 |
| Base case (n=0) | Trivial | ~2 |
| Intro + split | Low | ~10 |
| Wick recursion | Medium | ~5 |
| Norm inequalities | Medium | ~15 |
| IH application | Medium | ~5 |
| Product rearrangement | High | ~20 |
| Algebraic simplification | High | ~30 |
| Final assembly | Medium | ~10 |
| **Total** | **~100 lines** | |

---

## Related Lemmas and Theorems

### Building on wick_bound:

1. **wick_bound_factorial** (already in file):
   ```
   ‖E[∏ ω(fᵢ)]‖ ≤ (n!)^{1/2} · ∏ ‖T(fᵢ)‖
   ```
   Uses `double_factorial_le_sqrt_factorial`.

2. **OS1' Schwinger growth** (future):
   ```
   S₁(p₁,...,pₙ) ≤ const · (n!)^{1/2}
   ```
   Follows from `wick_bound_factorial` and analyticity.

### Prerequisites:

1. **odd_moment_vanish**: Requires `wick_recursive`
2. **wick_recursive**: Requires `gaussian_ibp`
3. **gaussian_ibp**: Requires `charFun T` and Leibniz integral rule
4. **product_integrable**: Used to justify the integrals in Wick

---

## References

### Mathematical References

- **Janson, S.** "Gaussian Hilbert Spaces" (Cambridge). Theorem 1.28: Wick's theorem and recursive formula.
- **Simon, B.** "The P(φ)₂ Euclidean (Quantum) Field Theory" (Princeton). §I.3: Wick ordering and moments.
- **Glimm & Jaffe.** "Quantum Physics" (Springer). §6.1: Wick's theorem and quantization.

### Lean/Mathlib References

- **Fin.prod_univ_succAbove:** Mathlib `Algebra.BigOperators.Fin`
- **Nat.doubleFactorial_add_two:** Mathlib `Data.Nat.Factorial.DoubleFactorial`
- **norm_sum_le:** Mathlib `Analysis.Normed.Group.BigOperators`
- **norm_inner_le_norm:** Mathlib `Analysis.InnerProductSpace.Basic`

---

## Next Steps After Implementing wick_bound

1. Use `wick_bound` to prove `wick_bound_factorial` (factor growth)
2. Connect to OS1' condition via Schwinger functions
3. Use double factorial bound in growth estimates
4. Verify complete Gaussian field construction satisfies axioms
