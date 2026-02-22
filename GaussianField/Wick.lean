/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wick's Theorem (Isserlis' Theorem) for Gaussian Measures

Wick's theorem expresses the n-point functions of a centered Gaussian measure
in terms of the 2-point function (covariance). For the Gaussian measure
constructed in `GaussianField.Construction`:

- **Odd moments vanish**: E[ω(f₁)···ω(f₂ₖ₊₁)] = 0
- **Even moments factor into pairings**:
  E[ω(f₁)···ω(f₂ₖ)] = ∑_{pairings} ∏ C(fᵢ,fⱼ)

We state this in two forms:

1. **Recursive** (`wick_recursive`): Pick a partner for f₀ and recurse.
   This is the natural induction form and avoids enumerating pairings.

2. **Bound** (`wick_bound`): |E[∏ ω(fᵢ)]| ≤ (n-1)‼ · ∏ ‖T(fᵢ)‖.
   This is sufficient for verifying OS1' (Schwinger function growth).

## Proof strategy

The key tool is **Gaussian integration by parts**:
  E[ω(f₀) · F(ω)] = ∑ⱼ C(f₀, gⱼ) · E[∂F/∂(ω gⱼ)]
For F(ω) = ∏ᵢ ω(gᵢ), the derivative ∂F/∂(ω gⱼ) = ∏_{i≠j} ω(gᵢ).
This gives the recursive formula directly.

Gaussian IBP itself follows from differentiating the characteristic
functional `charFun T f` (proved in `GaussianField.Construction`):
  d/dt E[exp(it·ω(f))] |_{t=0} = i · E[ω(f)] = -⟨Tf, Tf⟩ · 0 = 0

## References

- Janson, "Gaussian Hilbert Spaces", Theorem 1.28
- Simon, "The P(φ)₂ Euclidean (Quantum) Field Theory", §I.3
- Glimm-Jaffe, "Quantum Physics", §6.1 (Wick ordering)
-/

import GaussianField.Properties
import Mathlib.Data.Nat.Factorial.DoubleFactorial

noncomputable section

namespace GaussianField

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped BigOperators NNReal ENNReal

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
variable (T : E →L[ℝ] H)

/-! ## Integrability of products

Products of n evaluation functionals are integrable, generalizing
`pairing_product_integrable` from n=2. This is needed for Wick's theorem
to be well-stated (the integrals must exist). -/

/-- HolderTriple (2p, 2p, p): `(2p)⁻¹ + (2p)⁻¹ = p⁻¹` in ℝ≥0∞.

This allows Hölder's inequality to be applied as: L^{2p} × L^{2p} → L^p. -/
private lemma holderTriple_double (p : ℝ≥0∞) :
    ENNReal.HolderTriple (2 * p) (2 * p) p where
  inv_add_inv_eq_inv := by
    have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := two_ne_zero
    have h2_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := ENNReal.ofNat_ne_top
    calc (2 * p)⁻¹ + (2 * p)⁻¹
        = 2 * (2 * p)⁻¹ := (two_mul _).symm
      _ = 2 * (2⁻¹ * p⁻¹) := by
          congr 1
          exact ENNReal.mul_inv (Or.inl h2_ne_zero) (Or.inl h2_ne_top)
      _ = (2 * 2⁻¹) * p⁻¹ := by rw [mul_assoc]
      _ = 1 * p⁻¹ := by rw [ENNReal.mul_inv_cancel h2_ne_zero h2_ne_top]
      _ = p⁻¹ := one_mul _

/-- Products of evaluation functionals are in L^p for all p.

By induction on n, splitting ∏ = head × tail. At each step, `pairing_memLp`
gives head ∈ L^{2p}, and the IH gives tail ∈ L^{2p}. Hölder's inequality
via `HolderTriple (2p) (2p) p` gives the product ∈ L^p. -/
private theorem product_memLp : ∀ (n : ℕ) (f : Fin n → E) (p : ℝ≥0),
    MemLp (fun ω : Configuration E => ∏ i, ω (f i)) (↑p) (measure T) := by
  intro n
  induction n with
  | zero => intro f p; simp; exact memLp_const 1
  | succ n ih =>
    intro f p
    simp_rw [Fin.prod_univ_succ]
    haveI : ENNReal.HolderTriple (↑(2 * p)) (↑(2 * p)) (↑p) := by
      rw [ENNReal.coe_mul]; exact holderTriple_double ↑p
    have hf0 : MemLp (fun ω : Configuration E => ω (f 0)) (↑(2 * p)) (measure T) :=
      pairing_memLp T (f 0) (2 * p)
    have htail : MemLp (fun ω : Configuration E => ∏ i : Fin n, ω (f (Fin.succ i)))
        (↑(2 * p)) (measure T) :=
      ih (fun i => f (Fin.succ i)) (2 * p)
    exact htail.mul' hf0

/-- Finite products of evaluation functionals are integrable.

Corollary of `product_memLp` with p = 1. -/
theorem product_integrable (n : ℕ) (f : Fin n → E) :
    Integrable (fun ω : Configuration E => ∏ i, ω (f i)) (measure T) := by
  rw [← memLp_one_iff_integrable]
  exact_mod_cast product_memLp T n f 1

/-! ## Odd moments vanish

For a centered Gaussian measure, all odd-order moments are zero.
This follows from the symmetry ω ↦ -ω of the measure. -/

/-- Odd moments of a centered Gaussian measure vanish.

Proof: The Gaussian measure with covariance C is symmetric under ω ↦ -ω
(since the characteristic functional exp(-½‖Tf‖²) is even). Under this
symmetry, ∏ᵢ ω(fᵢ) ↦ (-1)ⁿ ∏ᵢ ω(fᵢ). For odd n, this gives
E[∏ ω(fᵢ)] = -E[∏ ω(fᵢ)] = 0. -/
theorem odd_moment_vanish (k : ℕ) (f : Fin (2 * k + 1) → E) :
    ∫ ω : Configuration E, ∏ i, ω (f i) ∂(measure T) = 0 :=
  sorry

/-! ## Wick's theorem — recursive form

The recursive form avoids the combinatorial overhead of enumerating
perfect pairings. It says: pick any index (we use 0), then the
(n+2)-point function equals the sum over all partners j for index 0. -/

/-- **Wick's theorem (recursive form).**

For a centered Gaussian measure with covariance C(f,g) = ⟨Tf, Tg⟩_H:

  E[ω(f₀) · ∏ⱼ ω(gⱼ)] = ∑ⱼ C(f₀, gⱼ) · E[∏_{i≠j} ω(gᵢ)]

This is proved by induction using Gaussian integration by parts.
The base case n=0 is `measure_centered`, and n=1 is
`cross_moment_eq_covariance`. -/
theorem wick_recursive (n : ℕ) (f₀ : E) (g : Fin (n + 1) → E) :
    ∫ ω : Configuration E, ω f₀ * ∏ i, ω (g i) ∂(measure T) =
      ∑ j : Fin (n + 1), @inner ℝ H _ (T f₀) (T (g j)) *
        ∫ ω : Configuration E, ∏ i : Fin n,
          ω (g (Fin.succAbove j i)) ∂(measure T) :=
  sorry

/-! ## Wick bound

The bound on n-point functions follows from Wick's recursive formula
by induction, using Cauchy-Schwarz at each step. The (2k-1)!! factor
counts the number of perfect pairings of 2k elements. -/

/-- **Wick bound on n-point functions.**

  |E[∏ᵢ ω(fᵢ)]| ≤ (n-1)‼ · ∏ᵢ ‖T(fᵢ)‖

For odd n, both sides are zero (LHS by `odd_moment_vanish`, RHS by
convention (n-1)‼ for n=1 gives 0‼ = 1, but we use the general bound).

For even n = 2k, the (2k-1)‼ = (2k-1)(2k-3)···3·1 counts the number
of perfect pairings. Each pairing contributes ∏ |C(fᵢ,fⱼ)| ≤ ∏ ‖Tfᵢ‖·‖Tfⱼ‖
by Cauchy-Schwarz, so the total is ≤ (2k-1)‼ · ∏ ‖Tfᵢ‖.

This bound directly implies OS1' with γ = 1/2, since
(2k-1)‼ ≤ (2k)!^{1/2} and (2k)! ≤ (2k)^{2k}. More precisely,
(2k)! = (2k)‼ · (2k-1)‼ = 2^k · k! · (2k-1)‼, so
(2k-1)‼ = (2k)! / (2^k · k!) ≤ (2k)!^{1/2}. -/
theorem wick_bound (n : ℕ) (f : Fin n → E) :
    ‖∫ ω : Configuration E, ∏ i, ω (f i) ∂(measure T)‖ ≤
      (n - 1).doubleFactorial * ∏ i, ‖T (f i)‖ :=
  sorry

/-! ## Corollary: OS1' Schwinger growth for GFF

The Wick bound directly gives the factorial growth condition OS1'
with γ = 1/2, using the inequality (n-1)‼ ≤ n!^{1/2}. -/

end GaussianField

/-- Helper: m‼² ≤ (m+1)! for all m.

Proof by induction on m with step 2, using (m+2)‼ = (m+2)·m‼:
  ((m+2)‼)² = (m+2)²·(m‼)² ≤ (m+2)²·(m+1)! ≤ (m+3)·(m+2)·(m+1)! = (m+3)! -/
private lemma dfact_sq_le_succ_fact : ∀ m : ℕ, m.doubleFactorial ^ 2 ≤ (m + 1).factorial
  | 0 => by norm_num
  | 1 => by norm_num
  | m + 2 => by
    rw [Nat.doubleFactorial_add_two, mul_pow]
    calc (m + 2) ^ 2 * m.doubleFactorial ^ 2
        ≤ (m + 2) ^ 2 * (m + 1).factorial :=
          Nat.mul_le_mul_left _ (dfact_sq_le_succ_fact m)
      _ = (m + 2) * ((m + 2) * (m + 1).factorial) := by ring
      _ ≤ (m + 3) * ((m + 2) * (m + 1).factorial) :=
          Nat.mul_le_mul_right _ (by omega)
      _ = (m + 2 + 1).factorial := by
          simp only [Nat.factorial_succ, show m + 2 + 1 = m + 3 by omega]

/-- Double factorial bound: (n-1)‼ ≤ n!^{1/2} for all n.
This converts the Wick bound into the OS1' factorial form. -/
theorem double_factorial_le_sqrt_factorial (n : ℕ) :
    ((n - 1).doubleFactorial : ℝ) ≤ (n.factorial : ℝ) ^ ((1 : ℝ) / 2) := by
  rw [← Real.sqrt_eq_rpow]
  rw [Real.le_sqrt (Nat.cast_nonneg _)]
  · have h : (n - 1).doubleFactorial ^ 2 ≤ n.factorial := by
      cases n with
      | zero => norm_num
      | succ n => exact dfact_sq_le_succ_fact n
    exact_mod_cast h
  · exact Nat.cast_nonneg _

namespace GaussianField

open MeasureTheory ProbabilityTheory TopologicalSpace
open scoped BigOperators NNReal ENNReal

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
variable (T : E →L[ℝ] H)

/-- Wick bound in factorial form (suitable for OS1'):
  |E[∏ᵢ ω(fᵢ)]| ≤ n!^{1/2} · ∏ᵢ ‖T(fᵢ)‖ -/
theorem wick_bound_factorial (n : ℕ) (f : Fin n → E) :
    ‖∫ ω : Configuration E, ∏ i, ω (f i) ∂(measure T)‖ ≤
      (n.factorial : ℝ) ^ ((1 : ℝ) / 2) * ∏ i, ‖T (f i)‖ :=
  calc ‖∫ ω, ∏ i, ω (f i) ∂(measure T)‖
      ≤ (n - 1).doubleFactorial * ∏ i, ‖T (f i)‖ := wick_bound T n f
    _ ≤ (n.factorial : ℝ) ^ ((1 : ℝ) / 2) * ∏ i, ‖T (f i)‖ := by
        apply mul_le_mul_of_nonneg_right (double_factorial_le_sqrt_factorial n)
        exact Finset.prod_nonneg (fun i _ => norm_nonneg _)

end GaussianField
