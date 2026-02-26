# Wick Bound Proof Strategy: Complete Documentation Index

This index provides a roadmap to all documentation for proving `wick_bound` in Lean 4.

---

## Document Overview

### 1. **wick-bound-summary.md** (START HERE)
   - **Purpose:** High-level overview of the entire proof strategy
   - **Audience:** Anyone new to the proof, seeking quick understanding
   - **Contents:**
     - Executive summary of the statement and approach
     - High-level proof structure (9 steps)
     - Key mathematical insights (why strong induction, why succAbove works, etc.)
     - Proof complexity metrics
     - Verification checklist before finalizing

   **Read this first if:** You want to understand the big picture

---

### 2. **wick-bound-proof-strategy.md** (DETAILED THEORY)
   - **Purpose:** Complete mathematical explanation of the proof
   - **Audience:** Mathematicians and developers implementing the proof
   - **Contents:**
     - Section 1: Induction principle choice (strong induction rationale)
     - Section 2: Case analysis by parity (odd vs. even)
     - Section 3: Main induction step broken into 9 substeps:
       - 3.1: Split the product using `Fin.prod_univ_succ`
       - 3.2: Apply Wick's recursive formula
       - 3.3: Push norm through sum (triangle inequality)
       - 3.4: Split norms and apply Cauchy-Schwarz
       - 3.5: Apply induction hypothesis
       - 3.6: Product rearrangement using `Fin.prod_univ_succAbove`
       - 3.7: Combine double factorials
       - 3.8: Reconstruct the final product
       - 3.9: Relate back to n
     - Section 4: Key Mathlib lemmas table
     - Section 5: Full pseudocode proof outline
     - Section 6: Tricky points and solutions
     - Section 7: Tactic summary

   **Read this when:** You're implementing the proof and need to understand each mathematical step

---

### 3. **wick-bound-tactics.md** (IMPLEMENTATION GUIDE)
   - **Purpose:** Concrete Lean 4 code snippets and tactical patterns
   - **Audience:** Lean developers implementing the proof
   - **Contents:**
     - Helper lemmas to define (e.g., `prod_with_succAbove`)
     - Odd case implementation (brief)
     - Even case base cases (n=0, n=1)
     - Complete calc block for main induction (m+2 case) with all tactics
     - Key tactic patterns:
       - Norm inequality chains
       - Factoring constants from sums
       - Applying induction hypothesis
       - Product rearrangement
       - Converting equalities
     - Debugging tips and common errors
     - Complete template (simplified version)
     - Required imports

   **Read this when:** You're writing the actual Lean 4 code

---

### 4. **wick-bound-mathlib-reference.md** (LEMMA LOOKUP)
   - **Purpose:** Quick reference for all Mathlib lemmas needed
   - **Audience:** Anyone needing to look up a lemma's exact signature or location
   - **Contents:**
     - Section 1: Fin product lemmas (prod_univ_succ, prod_univ_succAbove)
     - Section 2: Norm inequality lemmas (norm_sum_le, norm_mul, norm_inner_le_norm)
     - Section 3: Finset and sum lemmas (sum_const, card_fin, sum_mul)
     - Section 4: Natural number lemmas (doubleFactorial_add_two, etc.)
     - Section 5: Tactic references (gcongr, omega, simp)
     - Section 6: Complete imports block
     - Section 7: Quick reference table
     - Section 8: Common patterns and their Mathlib counterparts
     - Section 9: Type class dependencies
     - Section 10: Debugging guide

   **Read this when:** You need to look up a lemma name, signature, or how to use it

---

## How to Use This Documentation

### Scenario 1: Understanding the Overall Proof Strategy
1. Read **wick-bound-summary.md** sections 1-3
2. Skim **wick-bound-proof-strategy.md** section 5 (pseudocode)
3. Check the **verification checklist** at the end of summary

### Scenario 2: Learning the Mathematical Details
1. Read **wick-bound-proof-strategy.md** completely
2. Reference **wick-bound-mathlib-reference.md** for lemma details
3. Use **wick-bound-summary.md** section on key insights

### Scenario 3: Implementing in Lean 4
1. Start with **wick-bound-tactics.md** template
2. Reference **wick-bound-proof-strategy.md** sections 3.1-3.9 for each step
3. Look up lemmas in **wick-bound-mathlib-reference.md**
4. Use debugging tips in **wick-bound-tactics.md** when things go wrong

### Scenario 4: Quick Lemma Lookup
1. Go directly to **wick-bound-mathlib-reference.md**
2. Use the quick reference table (section 7) to find what you need
3. Check the full lemma definition with context

---

## Key Concepts Mapped to Documents

| Concept | Document | Section |
|---------|----------|---------|
| Why strong induction? | proof-strategy | 1 |
| Odd vs. even cases | proof-strategy | 2 |
| Split product at index 0 | proof-strategy, tactics | 3.1 |
| Wick recursion application | proof-strategy, tactics | 3.2 |
| Triangle inequality | proof-strategy, tactics | 3.3 |
| Cauchy-Schwarz | proof-strategy, tactics | 3.4 |
| Induction hypothesis | proof-strategy, tactics | 3.5 |
| Product rearrangement | proof-strategy, tactics | 3.6, mathlib-ref 1.2 |
| Double factorial | proof-strategy, tactics | 3.7, mathlib-ref 4.1 |
| Full calc block | tactics | Main induction |
| Mathlib lemmas table | mathlib-reference | 7 |
| Debugging tips | tactics | Debugging section |

---

## Mathematical Background Needed

To understand this proof, you should be familiar with:

1. **Gaussian measures and moments**
   - Centered Gaussian measures
   - Covariance operator T
   - Odd and even moments

2. **Wick's theorem basics**
   - Recursive form of Wick's theorem
   - Partner/pairing structure
   - Why recursion is n → n-2

3. **Induction on natural numbers**
   - Simple induction (n → n+1)
   - Strong induction (assume all k < n)
   - Why strong induction is needed here

4. **Finite sets and combinatorics**
   - Fin type in Lean (Fin n = {0, 1, ..., n-1})
   - Partitions and bijections
   - Double factorial definition

5. **Functional analysis**
   - Inner product spaces and Cauchy-Schwarz
   - Norms and norm inequalities
   - Integration and triangle inequality for integrals

---

## Proof Roadmap: Step by Step

```
wick_bound (n : ℕ) (f : Fin n → E)
│
├─ Induction: Nat.strong_induction_on
│  │
│  └─ For n, assume P(k) holds for all k < n
│
├─ Case split: Odd n vs. Even n
│  │
│  ├─ Odd case (brief)
│  │  └─ Use odd_moment_vanish → integral = 0
│  │     Apply norm_zero, show RHS ≥ 0
│  │
│  └─ Even case (main work)
│     │
│     ├─ Match on n = m + 2
│     │
│     ├─ Step 1: Rewrite using Fin.prod_univ_succ
│     │  └─ ∏ᵢ₌₀^{m+1} ω(fᵢ) = ω(f 0) · ∏ᵢ₌₀^m ω(f(i+1))
│     │
│     ├─ Step 2: Apply wick_recursive
│     │  └─ ∫ ω(f₀) · ∏ᵢ ω(gᵢ) dμ = ∑ⱼ ⟨Tf₀, Tgⱼ⟩ · ∫ ∏_{i≠j} dμ
│     │
│     ├─ Step 3: Apply norm_sum_le (triangle inequality)
│     │  └─ ‖∑ aᵢ‖ ≤ ∑ ‖aᵢ‖
│     │
│     ├─ Step 4: Apply norm_mul and norm_inner_le_norm (Cauchy-Schwarz)
│     │  └─ ‖a·b‖ = ‖a‖·‖b‖ and ‖⟪x,y⟫‖ ≤ ‖x‖·‖y‖
│     │
│     ├─ Step 5: Apply ih m (induction hypothesis)
│     │  └─ ‖∫ ∏ᵢ dμ‖ ≤ (m-1)‼ · ∏ᵢ ‖T(...)‖
│     │
│     ├─ Step 6: Rearrange using Fin.prod_univ_succAbove
│     │  └─ x(j) · ∏ᵢ x(succAbove j i) = ∏ₖ x(k)
│     │
│     ├─ Step 7: Sum of constants using Finset.sum_const
│     │  └─ ∑ⱼ C = (m+1) · C
│     │
│     ├─ Step 8: Combine double factorials using Nat.doubleFactorial_add_two
│     │  └─ (m+1)‼ = (m+1) · (m-1)‼
│     │
│     ├─ Step 9: Reconstruct full product using Fin.prod_univ_succ
│     │  └─ ‖T(f 0)‖ · ∏ᵢ ‖T(f(i+1))‖ = ∏ᵢ₌₀^{m+1} ‖T(fᵢ)‖
│     │
│     └─ Final: Relate m+1 back to n-1 using omega
│        └─ (m+1)‼ = (n-1)‼ ✓
│
└─ QED
```

---

## Frequently Asked Questions

**Q: Why can't we use simple induction?**
A: The Wick recursion reduces from n to n-2, not n to n-1. Strong induction lets us assume the hypothesis for n-2. See proof-strategy section 1.

**Q: What's the role of succAbove?**
A: It's a bijection from Fin(m) to Fin(m+1) \ {j}. This allows us to rearrange products and recover the full product. See proof-strategy section 3.6b.

**Q: How does the double factorial appear?**
A: From the sum over m+1 terms: (m+1) · (m-1)‼ = (m+1)‼. See proof-strategy section 3.7.

**Q: What if n is odd?**
A: Use odd_moment_vanish to show the integral is 0. The bound is trivial. See proof-strategy section 2, case 1.

**Q: Which Mathlib lemmas are hardest to find?**
A: Fin.prod_univ_succAbove (in Algebra.BigOperators.Fin) and norm_inner_le_norm (in Analysis.InnerProductSpace.Basic). See mathlib-reference section 1.2 and 2.3.

---

## Proof Statistics

- **Total lines of Lean 4 code:** ~100 lines
- **Induction principle:** Strong induction (`Nat.strong_induction_on`)
- **Number of calc steps:** ~12 (main induction)
- **Key Mathlib lemmas used:** 8
- **Helper lemmas needed:** 1 (prod_with_succAbove)
- **Difficulty level:** Medium-Hard (requires understanding induction, partitions, and inequalities)

---

## Related Work

### In the same file:
- `odd_moment_vanish`: Requires `wick_recursive`
- `wick_bound_factorial`: Builds on `wick_bound`
- `double_factorial_le_sqrt_factorial`: Used in `wick_bound_factorial`

### Prerequisites:
- `wick_recursive`: Requires `gaussian_ibp`
- `product_integrable`: Justifies integrals in Wick

### Building on wick_bound:
- OS1' Schwinger growth bounds (future)
- Analytic continuation of correlators (future)

---

## Change Log

| Date | Document | Changes |
|------|----------|---------|
| 2026-02-22 | All | Initial creation |
| | summary | Added proof statistics |
| | proof-strategy | Added complete 9-step breakdown |
| | tactics | Added helper lemmas and debugging tips |
| | mathlib-reference | Added complete Mathlib lemma reference |

---

## Contact and Feedback

- **Questions about the mathematical content?** Check proof-strategy.md
- **Looking for Lean tactics?** Check tactics.md
- **Need a specific lemma?** Check mathlib-reference.md
- **Want to understand the high-level approach?** Check summary.md

---

## Quick Links to Key Sections

- **Induction choice**: proof-strategy.md section 1
- **Case analysis**: proof-strategy.md section 2
- **Main proof steps**: proof-strategy.md section 3
- **Full pseudocode**: proof-strategy.md section 5
- **Lean code template**: tactics.md main induction section
- **Mathlib lemmas**: mathlib-reference.md section 7 (table)
- **Debugging**: tactics.md debugging section
- **Verification**: summary.md final section
