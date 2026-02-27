/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Hypercontractive estimate for even integer p

This file proves `gaussian_moment_ratio_bound` for even integer p = 2m,
bypassing the Gamma function entirely via a combinatorial argument on
double factorials.

## Strategy

1. **Bridge**: `gaussian_abs_moment_std` expresses E[|Z|^k] using Gamma.
   For even integer k = 2n, Mathlib's `Real.Gamma_nat_add_half` gives
   Γ(n + 1/2) = (2n-1)!! · √π / 2^n, so E[Z^{2n}] = (2n-1)!!.

2. **Combinatorial inequality**: (2mn-1)!! ≤ (2m-1)^{mn} · ((2n-1)!!)^m
   Proved by partitioning the product ∏_{k=1}^{mn} (2k-1) into n blocks
   of m terms and bounding each block.

3. **Connection**: The above two facts prove `hypercontractive_1d` for p = 2m.

## References

- Simon, P(φ)₂, Theorem I.17
- Glimm-Jaffe, Quantum Physics, Ch. 8
-/

import GaussianField.Hypercontractive
import Mathlib.Data.Nat.Factorial.DoubleFactorial

noncomputable section

namespace GaussianField

open MeasureTheory ProbabilityTheory Real Finset Nat TopologicalSpace
open scoped BigOperators NNReal

/-! ## Part 1: Bridge from Gamma moments to double factorials -/

/-- E[Z^{2n}] for Z ~ N(0,1) equals (2n-1)!! (as a real number).

This bridges our `gaussian_abs_moment_std` (which uses Gamma functions) to the
double factorial. Uses `Real.Gamma_nat_add_half`:
  Γ(n + 1/2) = (2n-1)!! · √π / 2^n
-/
theorem gaussian_even_moment_eq_doubleFactorial (n : ℕ) :
    ∫ x : ℝ, |x| ^ ((2 : ℝ) * ↑n) ∂(gaussianReal 0 1) = ((2 * n - 1)‼ : ℝ) := by
  rw [gaussian_abs_moment_std ((2 : ℝ) * ↑n) (by positivity)]
  -- LHS = 2^(2n/2) * Γ((2n+1)/2) / √π = 2^n * Γ(n + 1/2) / √π
  -- Γ(n + 1/2) = (2n-1)!! * √π / 2^n  [Mathlib: Real.Gamma_nat_add_half]
  have h_exp : (2 : ℝ) * ↑n / 2 = ↑n := by ring
  rw [h_exp]
  have h_arg : ((2 : ℝ) * ↑n + 1) / 2 = ↑n + 1 / 2 := by ring
  rw [h_arg, Real.Gamma_nat_add_half n]
  have hsqrt_pos : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hsqrt_ne : √π ≠ 0 := ne_of_gt hsqrt_pos
  have h2n_pos : (0 : ℝ) < 2 ^ (n : ℕ) := pow_pos (by norm_num) n
  -- Convert rpow 2 ↑n to npow 2 n
  rw [rpow_natCast]
  -- 2^n * ((2n-1)!! * √π / 2^n) / √π = (2n-1)!!
  field_simp

/-- The even moment E[|Z|^{2n}] equals (2n-1)!! in the ℕ-power form
(used when the integrand has ℕ-exponent |x|^(2*n) rather than ℝ-rpow). -/
theorem gaussian_even_moment_pow_eq_doubleFactorial (n : ℕ) :
    ∫ x : ℝ, |x| ^ (2 * n) ∂(gaussianReal 0 1) = ((2 * n - 1)‼ : ℝ) := by
  -- Convert ℕ-power to rpow and use the rpow version
  have h_eq : ∀ x : ℝ, |x| ^ (2 * n) = (|x| : ℝ) ^ ((2 : ℝ) * (↑n : ℝ)) := by
    intro x
    rw [show (2 : ℝ) * (↑n : ℝ) = ((2 * n : ℕ) : ℝ) from by push_cast; ring]
    exact (Real.rpow_natCast (|x|) (2 * n)).symm
  simp_rw [h_eq]
  exact gaussian_even_moment_eq_doubleFactorial n

/-! ## Part 2: Combinatorial double-factorial inequality

We prove: (2*m*n - 1)‼ ≤ (2*m - 1)^(m*n) * ((2*n - 1)‼)^m

The LHS is ∏_{k=0}^{mn-1} (2k+1). We partition into n blocks of m terms
and bound each block.
-/

/-- The double factorial (2*k - 1)‼ expressed as a product of odd numbers.

We show (2*k - 1)‼ = ∏_{i ∈ range k} (2*i + 1). -/
private lemma doubleFactorial_as_prod (k : ℕ) :
    (2 * k - 1)‼ = ∏ i ∈ Finset.range k, (2 * i + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) - 1 = 2 * k + 1 from by omega,
        Nat.doubleFactorial_add_one (2 * k),
        Finset.prod_range_succ, ← ih]
    ring

/-- Repartition: the product over m*n indices can be written as a double
product over n blocks of m elements each. Uses `Finset.prod_range_add`. -/
private lemma prod_repartition {α : Type*} [CommMonoid α] (f : ℕ → α) (m n : ℕ) :
    ∏ k ∈ Finset.range (m * n), f k =
      ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range m, f (m * i + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show m * (n + 1) = m * n + m from by ring,
        Finset.prod_range_add, Finset.prod_range_succ, ih]

/-- Key element bound: for j < m and m ≥ 1,
2*(m*i + j) + 1 ≤ (2*m - 1) * (2*i + 1).

This bounds every element in the i-th block by the block's upper bound. -/
private lemma block_element_bound (m : ℕ) (hm : 1 ≤ m) (i j : ℕ) (hj : j < m) :
    2 * (m * i + j) + 1 ≤ (2 * m - 1) * (2 * i + 1) := by
  -- Uses: 2*(m*i+j)+1 ≤ 2*(m*i+m-1)+1 = 2*m*(i+1)-1 ≤ (2m-1)*(2i+1)
  -- The last step: (2m-1)*(2i+1) = 4mi+2m-2i-1 ≥ 2mi+2m-1 = 2m(i+1)-1
  -- because 4mi ≥ 2mi (since 2mi ≥ 0) and 2m-2i-1 + 2i = 2m-1.
  have h1 : 1 ≤ 2 * (m * i + j) + 1 := by omega
  have h2 : 1 ≤ 2 * m := by omega
  zify [h1, h2]
  nlinarith

/-- Each block of m consecutive odd numbers has product ≤ ((2m-1)*(2i+1))^m,
because each factor is ≤ (2m-1)*(2i+1). -/
private lemma block_prod_bound (m : ℕ) (hm : 1 ≤ m) (i : ℕ) :
    ∏ j ∈ Finset.range m, (2 * (m * i + j) + 1) ≤
      ((2 * m - 1) * (2 * i + 1)) ^ m := by
  calc ∏ j ∈ Finset.range m, (2 * (m * i + j) + 1)
      ≤ ∏ _j ∈ Finset.range m, ((2 * m - 1) * (2 * i + 1)) :=
        Finset.prod_le_prod' (fun j hj =>
          block_element_bound m hm i j (Finset.mem_range.mp hj))
    _ = ((2 * m - 1) * (2 * i + 1)) ^ m := by
        rw [Finset.prod_const, Finset.card_range]

/-- **Core combinatorial inequality**: (2mn - 1)‼ ≤ (2m - 1)^(mn) · ((2n - 1)‼)^m.

Proved by partitioning ∏_{k=0}^{mn-1}(2k+1) into n blocks of m terms,
bounding each block, and recombining. -/
theorem doubleFactorial_hypercontractive_bound (m n : ℕ) (hm : 1 ≤ m) :
    (2 * (m * n) - 1)‼ ≤ (2 * m - 1) ^ (m * n) * ((2 * n - 1)‼) ^ m := by
  rw [doubleFactorial_as_prod (m * n)]
  rw [prod_repartition (fun k => 2 * k + 1) m n]
  -- Each block: ∏_{j<m} (2*(m*i+j)+1) ≤ ((2m-1)*(2*i+1))^m
  calc ∏ i ∈ range n, ∏ j ∈ range m, (2 * (m * i + j) + 1)
      ≤ ∏ i ∈ range n, ((2 * m - 1) * (2 * i + 1)) ^ m :=
        Finset.prod_le_prod' (fun i _ => block_prod_bound m hm i)
    _ = ∏ i ∈ range n, ((2 * m - 1) ^ m * (2 * i + 1) ^ m) := by
        congr 1; ext i; exact Nat.mul_pow _ _ m
    _ = (2 * m - 1) ^ (m * n) * ∏ i ∈ range n, (2 * i + 1) ^ m := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul]
    _ = (2 * m - 1) ^ (m * n) * (∏ i ∈ range n, (2 * i + 1)) ^ m := by
        congr 1; exact Finset.prod_pow (range n) m (fun i => 2 * i + 1)
    _ = (2 * m - 1) ^ (m * n) * ((2 * n - 1)‼) ^ m := by
        congr 2; exact (doubleFactorial_as_prod n).symm

/-! ## Part 3: Hypercontractive inequality for even integer p -/

/-- **Hypercontractive inequality for even integer p**.

For Z ~ N(0,1), m ≥ 1, n ∈ ℕ, with p = 2m:
  E[|Z|^{2mn}] ≤ (2m - 1)^{mn} · (E[|Z|^{2n}])^m

This is `gaussian_moment_ratio_bound` restricted to p = 2m, proved
entirely via double factorial combinatorics. -/
theorem hypercontractive_1d_even (m n : ℕ) (hm : 1 ≤ m) :
    ∫ x : ℝ, |x| ^ (2 * (m * n)) ∂(gaussianReal 0 1) ≤
      (2 * m - 1) ^ (m * n) *
      (∫ x : ℝ, |x| ^ (2 * n) ∂(gaussianReal 0 1)) ^ m := by
  rw [gaussian_even_moment_pow_eq_doubleFactorial (m * n),
      gaussian_even_moment_pow_eq_doubleFactorial n]
  -- Now: ↑((2*m*n - 1)‼) ≤ (2m-1)^(mn) * (↑((2n-1)‼))^m
  have h := doubleFactorial_hypercontractive_bound m n hm
  have key : (2 * m - 1 : ℝ) = ((2 * m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2 * m)]
    push_cast; ring
  rw [key]
  exact_mod_cast h

/-- **Corollary**: hypercontractive for p=4 (m=2), the case used for log-Sobolev.

E[Z^{4n}] ≤ 3^{2n} · (E[Z^{2n}])^2 -/
theorem hypercontractive_1d_p4 (n : ℕ) :
    ∫ x : ℝ, |x| ^ (4 * n) ∂(gaussianReal 0 1) ≤
      3 ^ (2 * n) *
      (∫ x : ℝ, |x| ^ (2 * n) ∂(gaussianReal 0 1)) ^ 2 := by
  have h := hypercontractive_1d_even 2 n (by norm_num)
  convert h using 2
  · ring_nf
  · norm_num

/-! ## Full hypercontractive chain for even integer p

These lift `hypercontractive_1d_even` through the variance-scaling and
pushforward chain, giving the full hypercontractive estimate for even p = 2m.
The statements keep the original real-valued `p` parameter, with additional
hypotheses `(m : ℕ) (hm : 1 ≤ m) (hp_eq : p = 2 * ↑m)`.
-/

/-- **1D hypercontractive inequality** for the standard Gaussian (even p).

For Z ~ N(0,1), p = 2m ≥ 2, n ∈ ℕ:
  `E[|Z|^(p*n)] ≤ (p-1)^(p*n/2) · (E[|Z|^(2*n)])^(p/2)`

Proved via `hypercontractive_1d_even` (double-factorial combinatorics),
converting between rpow and npow. -/
lemma hypercontractive_1d (n : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (m : ℕ) (hm : 1 ≤ m) (hp_eq : p = 2 * ↑m) :
    ∫ x : ℝ, |x| ^ (p * ↑n) ∂(gaussianReal 0 1) ≤
      (p - 1) ^ (p * ↑n / 2) *
      (∫ x : ℝ, |x| ^ (2 * ↑n) ∂(gaussianReal 0 1)) ^ (p / 2) := by
  subst hp_eq
  -- Convert rpow LHS to npow
  have h_lhs : ∀ x : ℝ, |x| ^ ((2 : ℝ) * ↑m * ↑n) = |x| ^ (2 * (m * n)) := by
    intro x
    rw [show (2 : ℝ) * ↑m * ↑n = ↑(2 * (m * n) : ℕ) from by push_cast; ring]
    exact rpow_natCast |x| (2 * (m * n))
  simp_rw [h_lhs]
  -- Simplify rpow exponents to ℕ casts
  have he1 : (2 : ℝ) * ↑m * ↑n / 2 = ↑(m * n : ℕ) := by push_cast; ring
  have he2 : (2 : ℝ) * ↑m / 2 = ↑(m : ℕ) := by ring_nf
  rw [he1, he2, rpow_natCast, rpow_natCast]
  exact hypercontractive_1d_even m n hm

/-- **Hypercontractive inequality for N(0, v)** (even p): reduces to the
standard Gaussian case by scaling. -/
lemma hypercontractive_gaussianReal (v : ℝ≥0) (n : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (m : ℕ) (hm : 1 ≤ m) (hp_eq : p = 2 * ↑m) :
    ∫ x : ℝ, |x| ^ (p * ↑n) ∂(gaussianReal 0 v) ≤
      (p - 1) ^ (p * ↑n / 2) *
      (∫ x : ℝ, |x| ^ (2 * ↑n) ∂(gaussianReal 0 v)) ^ (p / 2) := by
  by_cases hv : v = 0
  · simp only [hv, gaussianReal_zero_var, integral_dirac, abs_zero]
    by_cases hn : n = 0
    · simp [hn]
    · have hp_pos : 0 < p := by linarith
      have h_pn_pos : 0 < p * ↑n := mul_pos hp_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
      rw [zero_rpow (ne_of_gt h_pn_pos)]
      apply mul_nonneg (rpow_nonneg (by linarith : 0 ≤ p - 1) _)
        (rpow_nonneg (by positivity) _)
  · set σ := Real.sqrt v with hσ_def
    have hv_pos : (0 : ℝ) < v := by positivity
    have hσ_pos : 0 < σ := Real.sqrt_pos_of_pos hv_pos
    have hσ_nn : (0 : ℝ) ≤ σ := le_of_lt hσ_pos
    have hp_pos : 0 < p := by linarith
    have hpn_nn : 0 ≤ p * ↑n := mul_nonneg (le_of_lt hp_pos) (Nat.cast_nonneg n)
    have h_scale : gaussianReal 0 v = (gaussianReal 0 1).map (σ * ·) := by
      rw [gaussianReal_map_const_mul]
      congr 1
      · simp
      · ext
        push_cast
        simp only [mul_one]
        exact (Real.sq_sqrt (NNReal.coe_nonneg v)).symm
    have h_asm_pn : AEStronglyMeasurable (fun x : ℝ => |x| ^ (p * ↑n))
        (Measure.map (σ * ·) (gaussianReal 0 1)) :=
      (continuous_abs.rpow_const (fun _ => Or.inr hpn_nn)).measurable.aestronglyMeasurable
    have h_asm_2n : AEStronglyMeasurable (fun x : ℝ => |x| ^ (2 * n))
        (Measure.map (σ * ·) (gaussianReal 0 1)) :=
      (continuous_abs.pow (2 * n)).measurable.aestronglyMeasurable
    rw [h_scale]
    rw [integral_map (by fun_prop : AEMeasurable (σ * ·) (gaussianReal 0 1)) h_asm_pn]
    rw [integral_map (by fun_prop : AEMeasurable (σ * ·) (gaussianReal 0 1)) h_asm_2n]
    have h_abs : ∀ z : ℝ, |σ * z| = σ * |z| := by
      intro z; rw [abs_mul, abs_of_pos hσ_pos]
    simp_rw [h_abs]
    have h_mul_rpow_pn : ∀ z : ℝ, (σ * |z|) ^ (p * ↑n) = σ ^ (p * ↑n) * |z| ^ (p * ↑n) := by
      intro z; exact Real.mul_rpow hσ_nn (abs_nonneg z)
    have h_mul_pow_2n : ∀ z : ℝ, (σ * |z|) ^ (2 * n) = σ ^ (2 * n) * |z| ^ (2 * n) := by
      intro z; exact mul_pow σ |z| (2 * n)
    simp_rw [h_mul_rpow_pn, h_mul_pow_2n]
    rw [integral_const_mul, integral_const_mul]
    have hσ_2n_nn : (0 : ℝ) ≤ σ ^ (2 * n) := pow_nonneg hσ_nn _
    have h_int_nn : 0 ≤ ∫ z : ℝ, |z| ^ (2 * n) ∂gaussianReal 0 1 := by
      apply integral_nonneg; intro z; exact pow_nonneg (abs_nonneg z) _
    rw [Real.mul_rpow hσ_2n_nn h_int_nn]
    have h_rpow_rpow : (σ ^ (2 * n) : ℝ) ^ (p / 2) = σ ^ (p * ↑n) := by
      rw [← Real.rpow_natCast σ (2 * n)]
      rw [← Real.rpow_mul hσ_nn]
      congr 1
      push_cast; ring
    rw [h_rpow_rpow]
    have hσ_pn_pos : 0 < σ ^ (p * ↑n) := Real.rpow_pos_of_pos hσ_pos _
    rw [show (p - 1) ^ (p * ↑n / 2) * (σ ^ (p * ↑n) * (∫ z, |z| ^ (2 * n) ∂gaussianReal 0 1) ^ (p / 2)) =
        σ ^ (p * ↑n) * ((p - 1) ^ (p * ↑n / 2) * (∫ z, |z| ^ (2 * n) ∂gaussianReal 0 1) ^ (p / 2)) from by ring]
    exact mul_le_mul_of_nonneg_left (hypercontractive_1d n p hp m hm hp_eq) (le_of_lt hσ_pn_pos)

set_option checkBinderAnnotations false in
/-- **Nelson's hypercontractive estimate** for the Gaussian measure (even p).

For the centered Gaussian measure `μ = GaussianField.measure T` on
`Configuration E = WeakDual ℝ E`, with p = 2m ≥ 2:

  `∫ |ω(f)|^{pn} dμ ≤ (p-1)^{pn/2} · (∫ |ω(f)|^{2n} dμ)^{p/2}`

**Proof**: Reduces to a 1D Gaussian integral via `pairing_is_gaussian`,
then delegates to `hypercontractive_gaussianReal`.

Reference: Gross (1975); Simon, P(φ)₂, Theorem I.17; Glimm-Jaffe Ch. 8.
-/
theorem gaussian_hypercontractive
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
    [inst_dm : DyninMityaginSpace E]
    {H : Type*} [inst_nacg : NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [SeparableSpace H]
    (T : E →L[ℝ] H)
    (f : E) (n : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (m : ℕ) (hm : 1 ≤ m) (hp_eq : p = 2 * ↑m) :
    ∫ ω : Configuration E, |ω f| ^ (p * ↑n) ∂(measure T) ≤
      (p - 1) ^ (p * ↑n / 2) *
      (∫ ω : Configuration E, |ω f| ^ (2 * ↑n) ∂(measure T)) ^ (p / 2) := by
  have h_gauss := pairing_is_gaussian T f
  have h_eval_meas := configuration_eval_measurable (E := E) f
  set v := (@inner ℝ H _ (T f) (T f) : ℝ).toNNReal with hv_def
  have h_reduce_lhs : ∫ ω : Configuration E, |ω f| ^ (p * ↑n) ∂(measure T) =
      ∫ x : ℝ, |x| ^ (p * ↑n) ∂(gaussianReal 0 v) := by
    rw [← h_gauss]
    symm
    apply integral_map h_eval_meas.aemeasurable
    exact (measurable_id.norm.pow_const _).aestronglyMeasurable
  have h_reduce_rhs : ∫ ω : Configuration E, |ω f| ^ (2 * ↑n) ∂(measure T) =
      ∫ x : ℝ, |x| ^ (2 * ↑n) ∂(gaussianReal 0 v) := by
    rw [← h_gauss]
    symm
    apply integral_map h_eval_meas.aemeasurable
    exact (measurable_id.norm.pow_const _).aestronglyMeasurable
  rw [h_reduce_lhs, h_reduce_rhs]
  exact hypercontractive_gaussianReal v n p hp m hm hp_eq

end GaussianField
