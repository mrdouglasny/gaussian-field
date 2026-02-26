/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nelson's Hypercontractive Estimate for Gaussian Measures

The fundamental estimate: for the Gaussian measure μ on E' = WeakDual ℝ E
with covariance C(f,g) = ⟨T(f), T(g)⟩_H, Wick-ordered polynomials satisfy

  ‖:ω(f)^n:‖_{L^p(μ)} ≤ (p-1)^{n/2} · ‖:ω(f)^n:‖_{L^2(μ)}

for all p ≥ 2. Equivalently, the Ornstein-Uhlenbeck semigroup P_t is a
contraction from L^2(μ) to L^p(μ) when e^{-2t} ≤ 1/(p-1).

## Proof strategy

The standard proof proceeds via the Gross log-Sobolev inequality:

1. **Log-Sobolev inequality** (Gross 1975): For the standard Gaussian measure γ
   on ℝ^n, ∫ f² log(f²/‖f‖²) dγ ≤ 2 ∫ |∇f|² dγ for all f ∈ H¹(γ).

2. **Hypercontractivity** follows from log-Sobolev by the Rothaus-Simon argument:
   d/dt ‖P_t f‖_{p(t)}^{p(t)} ≤ 0 when p'(t) = 2p(t)(p(t)-1)e^{2t}.

3. The infinite-dimensional case follows by approximation (cylindrical functions
   are dense in L^p).

## References

- L. Gross, "Logarithmic Sobolev inequalities," Amer. J. Math. 97 (1975), 1061-1083
- E. Nelson, "The free Markoff field," J. Funct. Anal. 12 (1973), 211-227
- B. Simon, The P(φ)₂ Euclidean (Quantum) Field Theory, Ch. I
- Glimm-Jaffe, Quantum Physics, Ch. 8
-/

import GaussianField.Properties
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

noncomputable section

namespace GaussianField

open MeasureTheory ProbabilityTheory TopologicalSpace Real Set
open scoped BigOperators NNReal

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [SeparableSpace H]
variable (T : E →L[ℝ] H)

/-! ## Nelson's hypercontractive estimate -/

/-- Absolute moment of the standard Gaussian in terms of the Gamma function.
For Z ~ N(0,1) and k ≥ 0:
  `E[|Z|^k] = 2^(k/2) · Γ((k+1)/2) / √π`

This is a standard identity obtained by substituting u = x²/2 in the Gaussian
integral and recognizing the Gamma function.

Reference: Any probability textbook, e.g. Feller, Vol. II, Ch. II. -/
private lemma gaussian_abs_moment_std_aux (k : ℝ) (hk : 0 ≤ k) :
    ∫ x : ℝ, |x| ^ k ∂(gaussianReal 0 1) =
      (√(2 * π))⁻¹ * (2 * ((1/2 : ℝ) ^ (-(k+1)/2) * (1/2) * Real.Gamma ((k+1)/2))) := by
  -- Step 1: Convert from gaussianReal measure to density form (Lebesgue integral)
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  -- Step 2: Expand gaussianPDFReal 0 1 x = (√(2π))⁻¹ * exp(-x²/2)
  simp only [gaussianPDFReal, NNReal.coe_one, sub_zero, mul_one, smul_eq_mul]
  -- Step 3: Factor out the constant (√(2π))⁻¹
  have h_factor : (fun x : ℝ => (√(2 * π))⁻¹ * rexp (-x ^ 2 / 2) * |x| ^ k) =
      fun x => (√(2 * π))⁻¹ * (rexp (-x ^ 2 / 2) * |x| ^ k) := by ext; ring
  rw [h_factor, integral_const_mul]
  congr 1
  -- Step 4: Use symmetry ∫ f(|x|) = 2 * ∫_{Ioi 0} f(x) for the even integrand
  have h_abs : (fun x : ℝ => rexp (-x ^ 2 / 2) * |x| ^ k) =
      fun x => (fun y => rexp (-y ^ 2 / 2) * y ^ k) |x| := by
    ext x; simp only; congr 1; congr 1; congr 1; rw [sq_abs]
  rw [h_abs]; simp only []  -- beta reduce
  rw [show (fun x : ℝ => rexp (-|x| ^ 2 / 2) * |x| ^ k) =
      (fun x : ℝ => (fun y : ℝ => rexp (-y ^ 2 / 2) * y ^ k) |x|) from rfl]
  rw [@integral_comp_abs (fun y => rexp (-y ^ 2 / 2) * y ^ k)]
  congr 1
  -- Step 5: Match integral_rpow_mul_exp_neg_mul_rpow form
  -- Target: ∫ x in Ioi 0, x^k * exp(-(1/2) * x^2) = (1/2)^(-(k+1)/2) * (1/2) * Γ((k+1)/2)
  convert integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := k) (b := 1/2)
    (by norm_num : (0:ℝ) < 2) (by linarith : -1 < k) (by norm_num : (0:ℝ) < 1/2) using 1
  · refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    have h1 : -x ^ 2 / 2 = -(1 / 2) * x ^ 2 := by ring
    rw [h1, mul_comm]; congr 2; norm_cast

lemma gaussian_abs_moment_std (k : ℝ) (hk : 0 ≤ k) :
    ∫ x : ℝ, |x| ^ k ∂(gaussianReal 0 1) =
      2 ^ (k / 2) * Real.Gamma ((k + 1) / 2) / Real.sqrt Real.pi := by
  rw [gaussian_abs_moment_std_aux k hk]
  -- Simplify: (√(2π))⁻¹ * (2 * ((1/2)^(-(k+1)/2) * (1/2) * Γ((k+1)/2))) = 2^(k/2) * Γ((k+1)/2) / √π
  -- (1/2)^(-(k+1)/2) = 2^((k+1)/2)
  have h1 : (1 / 2 : ℝ) ^ (-(k + 1) / 2) = 2 ^ ((k + 1) / 2) := by
    rw [one_div, inv_rpow (by norm_num : (0:ℝ) ≤ 2), ← rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    congr 1; ring
  rw [h1]
  -- √(2π) = √2 * √π
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) π]
  -- √2 = 2^(1/2)
  have hsqrt2_eq : Real.sqrt 2 = (2 : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.sqrt_eq_rpow 2
  rw [hsqrt2_eq]
  -- Now: ((2^(1/2) * √π))⁻¹ * (2 * (2^((k+1)/2) * (1/2) * Γ((k+1)/2)))
  -- = (2^(1/2))⁻¹ * (√π)⁻¹ * (2^((k+1)/2) * Γ((k+1)/2))
  -- = 2^(-(1/2)) * (√π)⁻¹ * 2^((k+1)/2) * Γ((k+1)/2)
  -- = 2^(-(1/2) + (k+1)/2) * Γ((k+1)/2) / √π
  -- = 2^(k/2) * Γ((k+1)/2) / √π
  rw [mul_inv, ← rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
  rw [div_eq_mul_inv]
  ring_nf
  -- Goal: 2^(-1/2) * (√π)⁻¹ * 2^(1/2 + k*(1/2)) * Γ(1/2 + k*(1/2))
  --     = (√π)⁻¹ * Γ(1/2 + k*(1/2)) * 2^(k*(1/2))
  -- Key: 2^(-1/2) * 2^(1/2 + k/2) = 2^(k/2)
  have h_combine : (2 : ℝ) ^ ((-1 : ℝ) / 2) * (2 : ℝ) ^ ((1 : ℝ) / 2 + k * (1 / 2)) =
      (2 : ℝ) ^ (k * (1 / 2)) := by
    rw [← rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1; ring
  -- Rearrange and substitute
  calc (2 : ℝ) ^ ((-1 : ℝ) / 2) * (√π)⁻¹ * (2 : ℝ) ^ ((1 : ℝ) / 2 + k * (1 / 2)) *
        Gamma (1 / 2 + k * (1 / 2))
      = ((2 : ℝ) ^ ((-1 : ℝ) / 2) * (2 : ℝ) ^ ((1 : ℝ) / 2 + k * (1 / 2))) *
        ((√π)⁻¹ * Gamma (1 / 2 + k * (1 / 2))) := by ring
    _ = (2 : ℝ) ^ (k * (1 / 2)) * ((√π)⁻¹ * Gamma (1 / 2 + k * (1 / 2))) := by
        rw [h_combine]
    _ = (√π)⁻¹ * Gamma (1 / 2 + k * (1 / 2)) * (2 : ℝ) ^ (k * (1 / 2)) := by ring

/-! ## Helper lemmas for the log-Sobolev inequality -/

/-- The fourth moment of the standard Gaussian: E[Z⁴] = 3 for Z ~ N(0,1).
    Proved via `iteratedDeriv 4 (mgf id (gaussianReal 0 1)) 0 = 3`. -/
private lemma deriv_exp_half_sq :
    deriv (fun t : ℝ => rexp (t ^ 2 / 2)) = fun t => t * rexp (t ^ 2 / 2) := by
  ext t
  have h : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
    have := (hasDerivAt_pow 2 t).div_const (2 : ℝ)
    simp at this; exact this
  rw [(h.exp).deriv]; ring

private lemma hasDerivAt_exp_half_sq (t : ℝ) :
    HasDerivAt (fun t : ℝ => rexp (t ^ 2 / 2)) (t * rexp (t ^ 2 / 2)) t := by
  have h : HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
    have := (hasDerivAt_pow 2 t).div_const (2 : ℝ)
    simp at this; exact this
  convert h.exp using 1; ring

private lemma hasDerivAt_t_mul_exp (t : ℝ) :
    HasDerivAt (fun t : ℝ => t * rexp (t ^ 2 / 2))
      ((1 + t ^ 2) * rexp (t ^ 2 / 2)) t := by
  have h1 : HasDerivAt (fun t : ℝ => t) 1 t := hasDerivAt_id t
  have := h1.mul (hasDerivAt_exp_half_sq t)
  convert this using 1; ring

private lemma hasDerivAt_quad_mul_exp (t : ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t ^ 2) * rexp (t ^ 2 / 2))
      ((3 * t + t ^ 3) * rexp (t ^ 2 / 2)) t := by
  have hp : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := by
    convert (hasDerivAt_pow 2 t).const_add 1 using 1; simp
  have := hp.mul (hasDerivAt_exp_half_sq t)
  convert this using 1; ring

private lemma hasDerivAt_cubic_mul_exp (t : ℝ) :
    HasDerivAt (fun t : ℝ => (3 * t + t ^ 3) * rexp (t ^ 2 / 2))
      ((3 + 6 * t ^ 2 + t ^ 4) * rexp (t ^ 2 / 2)) t := by
  have hp : HasDerivAt (fun t : ℝ => 3 * t + t ^ 3) (3 + 3 * t ^ 2) t := by
    have h1 := (hasDerivAt_id t).const_mul 3
    have h2 := hasDerivAt_pow 3 t
    convert h1.add h2 using 1; simp [mul_comm]
  have := hp.mul (hasDerivAt_exp_half_sq t)
  convert this using 1; ring

lemma fourth_moment_standard_gaussian :
    ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1) = 3 := by
  -- Use: iteratedDeriv n (mgf id μ) 0 = ∫ x^n dμ
  have h_int : 0 ∈ interior (ProbabilityTheory.integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) := by
    simp
  have h_mom := iteratedDeriv_mgf_zero h_int 4
  simp only [Pi.pow_apply] at h_mom
  rw [← h_mom]
  -- mgf of N(0,1) is exp(t²/2)
  rw [mgf_fun_id_gaussianReal]
  -- Simplify the mgf expression: μ=0, v=1 gives exp(0*t + 1*t²/2) = exp(t²/2)
  -- We need to compute the 4th derivative of this at 0
  -- Use the chain: exp(t²/2) →' t·exp(t²/2) →' (1+t²)·exp(t²/2)
  --   →' (3t+t³)·exp(t²/2) →' (3+6t²+t⁴)·exp(t²/2)
  -- At t=0: (3+0+0)·exp(0) = 3
  -- First, show the mgf simplifies to exp(t²/2)
  have hmgf : (fun t : ℝ => rexp (↑(0 : ℝ) * t + ↑(1 : ℝ≥0) * t ^ 2 / 2)) =
      fun t => rexp (t ^ 2 / 2) := by
    ext t; simp
  rw [hmgf]
  -- Now unfold iteratedDeriv 4 step by step using HasDerivAt
  have step1 : deriv (fun t => rexp (t ^ 2 / 2)) = fun t => t * rexp (t ^ 2 / 2) := by
    ext t; exact (hasDerivAt_exp_half_sq t).deriv
  have step2 : deriv (fun t => t * rexp (t ^ 2 / 2)) =
      fun t => (1 + t ^ 2) * rexp (t ^ 2 / 2) := by
    ext t; exact (hasDerivAt_t_mul_exp t).deriv
  have step3 : deriv (fun t => (1 + t ^ 2) * rexp (t ^ 2 / 2)) =
      fun t => (3 * t + t ^ 3) * rexp (t ^ 2 / 2) := by
    ext t; exact (hasDerivAt_quad_mul_exp t).deriv
  have step4 : deriv (fun t => (3 * t + t ^ 3) * rexp (t ^ 2 / 2)) =
      fun t => (3 + 6 * t ^ 2 + t ^ 4) * rexp (t ^ 2 / 2) := by
    ext t; exact (hasDerivAt_cubic_mul_exp t).deriv
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [step1, step2, step3, step4]
  simp

/-- Pointwise bound: for x ≠ 0 and σ² > 0, x² log(x²/σ²) ≤ x⁴/σ² - x².
    Follows from log(y) ≤ y - 1 applied to y = x²/σ². -/
lemma sq_log_div_le {x σsq : ℝ} (hσ : 0 < σsq) :
    x ^ 2 * Real.log (x ^ 2 / σsq) ≤ x ^ 4 / σsq - x ^ 2 := by
  by_cases hx : x = 0
  · simp [hx]
  · have hx2 : 0 < x ^ 2 := by positivity
    have hrat : 0 < x ^ 2 / σsq := div_pos hx2 hσ
    have hlog := Real.log_le_sub_one_of_pos hrat
    -- log(x²/σ²) ≤ x²/σ² - 1
    -- so x² * log(x²/σ²) ≤ x² * (x²/σ² - 1) = x⁴/σ² - x²
    calc x ^ 2 * Real.log (x ^ 2 / σsq)
        ≤ x ^ 2 * (x ^ 2 / σsq - 1) := by
          apply mul_le_mul_of_nonneg_left hlog (le_of_lt hx2)
      _ = x ^ 4 / σsq - x ^ 2 := by ring

/-- The second moment of N(0,v) equals v (as a real number). -/
lemma integral_sq_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 v) = (v : ℝ) := by
  have h_var : Var[fun x : ℝ => x; gaussianReal 0 v] = (v : ℝ) :=
    variance_fun_id_gaussianReal
  have h_zero : variance (fun x : ℝ => x) (gaussianReal 0 v) =
      ∫ x, x ^ 2 ∂(gaussianReal 0 v) :=
    variance_of_integral_eq_zero aemeasurable_id integral_id_gaussianReal
  linarith

/-- The fourth moment of N(0,v) equals 3v².
    Proof by scaling from the standard Gaussian: if X ~ N(0,1) then √v·X ~ N(0,v),
    so E[(√v·X)⁴] = v² · E[X⁴] = 3v². -/
lemma integral_pow4_gaussianReal (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  by_cases hv : v = 0
  · simp [hv, gaussianReal_zero_var, integral_dirac]
  · -- Scale from standard Gaussian via √v
    set σ := Real.sqrt v with hσ_def
    have hσ_pos : 0 < σ := Real.sqrt_pos_of_pos (by positivity : (0 : ℝ) < v)
    -- N(0,v) = N(0,1).map(σ*·)
    have h_scale : gaussianReal 0 v = (gaussianReal 0 1).map (σ * ·) := by
      rw [gaussianReal_map_const_mul]
      congr 1
      · simp
      · ext
        push_cast
        simp only [mul_one]
        exact (Real.sq_sqrt (NNReal.coe_nonneg v)).symm
    rw [h_scale]
    rw [integral_map (by fun_prop : AEMeasurable (σ * ·) (gaussianReal 0 1))
        (by fun_prop : AEStronglyMeasurable (fun x => x ^ 4) _)]
    simp only [mul_pow]
    rw [integral_const_mul]
    rw [fourth_moment_standard_gaussian]
    have : σ ^ 4 = (v : ℝ) ^ 2 := by
      rw [hσ_def]
      rw [show σ ^ 4 = (σ ^ 2) ^ 2 from by ring]
      rw [Real.sq_sqrt (NNReal.coe_nonneg v)]
    linarith

/-- The integral of x² log(x²/σ²) w.r.t. N(0,σ²) is at most 2σ².
    This is the 1D Gross log-Sobolev inequality for linear functions.

    Proof strategy: By the pointwise bound x² log(x²/σ²) ≤ x⁴/σ² - x²
    (from `sq_log_div_le`), the integral is bounded by E[X⁴]/σ² - E[X²].
    For N(0,σ²), E[X²] = σ² and E[X⁴] = 3σ⁴, giving 3σ² - σ² = 2σ².

    All components are fully proved: the pointwise bound, moment
    computations, integrability of the log-entropy integrand, and the
    main theorem `gross_log_sobolev`. -/
lemma log_sobolev_1d {σsq : ℝ} (hσ : 0 < σsq) :
    ∫ x : ℝ, x ^ 2 * Real.log (x ^ 2 / σsq)
      ∂(gaussianReal 0 σsq.toNNReal) ≤ 2 * σsq := by
  -- Integrability of x^2, x^4
  have h_int_sq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 σsq.toNNReal) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have h_int_norm4 : Integrable (fun x : ℝ => ‖x‖ ^ 4) (gaussianReal 0 σsq.toNNReal) :=
    (memLp_id_gaussianReal (4 : ℝ≥0)).integrable_norm_pow (by norm_num)
  have h_int_4 : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 σsq.toNNReal) := by
    refine h_int_norm4.mono ?_ ?_
    · exact (measurable_id.pow_const 4).aestronglyMeasurable
    · filter_upwards with x
      simp [Real.norm_eq_abs]
  have h_int_bound : Integrable (fun x : ℝ => x ^ 4 / σsq - x ^ 2)
      (gaussianReal 0 σsq.toNNReal) :=
    (h_int_4.div_const σsq).sub h_int_sq
  -- The LHS integrand is integrable (bounded in absolute value by the bound function + x^2)
  have h_int_lhs : Integrable (fun x : ℝ => x ^ 2 * Real.log (x ^ 2 / σsq))
      (gaussianReal 0 σsq.toNNReal) := by
    -- Bound: |x² * log(x²/σ²)| ≤ σ² + x⁴/σ² for all x
    -- When x²/σ² ≥ 1 (log ≥ 0): x² * log(x²/σ²) ≤ x⁴/σ² - x² ≤ x⁴/σ²  (by sq_log_div_le)
    -- When 0 < x²/σ² < 1 (log < 0): -x² * log(x²/σ²) = x² * log(σ²/x²)
    --   ≤ x² * (σ²/x² - 1) = σ² - x² ≤ σ²  (by log_le_sub_one)
    -- When x = 0: 0 * log(0/σ²) = 0 (since Real.log 0 = 0)
    -- So |x² * log(x²/σ²)| ≤ σ² + x⁴/σ² and the RHS is integrable.
    have h_bound_int : Integrable (fun x : ℝ => σsq + x ^ 4 / σsq)
        (gaussianReal 0 σsq.toNNReal) :=
      (integrable_const σsq).add (h_int_4.div_const σsq)
    apply Integrable.mono h_bound_int
    · exact (((measurable_id.pow_const 2).mul
        ((measurable_id.pow_const 2).div_const σsq |>.log)).aestronglyMeasurable)
    · filter_upwards with x
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ σsq + x ^ 4 / σsq)]
      rw [abs_mul, abs_pow]
      -- Need: |x|² * |log(x²/σ²)| ≤ σ² + x⁴/σ²
      -- i.e., x² * |log(x²/σ²)| ≤ σ² + x⁴/σ²
      have hx2_nn : 0 ≤ x ^ 2 := sq_nonneg x
      rw [sq_abs]
      by_cases hx : x = 0
      · simp [hx, Real.log_zero]
        positivity
      · have hx2_pos : 0 < x ^ 2 := by positivity
        have hrat : 0 < x ^ 2 / σsq := div_pos hx2_pos hσ
        by_cases hle : x ^ 2 / σsq ≥ 1
        · -- Case x²/σ² ≥ 1: log ≥ 0
          have hlog_nn : 0 ≤ Real.log (x ^ 2 / σsq) :=
            Real.log_nonneg hle
          rw [abs_of_nonneg hlog_nn]
          have := sq_log_div_le hσ (x := x)
          linarith
        · -- Case x²/σ² < 1: log < 0
          push_neg at hle
          have hlog_neg : Real.log (x ^ 2 / σsq) < 0 :=
            Real.log_neg hrat hle
          rw [abs_of_neg hlog_neg]
          -- -log(x²/σ²) = log(σ²/x²)
          rw [show -Real.log (x ^ 2 / σsq) = Real.log (σsq / x ^ 2) from by
            rw [Real.log_div (ne_of_gt hx2_pos) (ne_of_gt hσ)]
            rw [Real.log_div (ne_of_gt hσ) (ne_of_gt hx2_pos)]
            ring]
          have hrat2 : 0 < σsq / x ^ 2 := div_pos hσ hx2_pos
          have hlog2 := Real.log_le_sub_one_of_pos hrat2
          -- log(σ²/x²) ≤ σ²/x² - 1
          -- x² * log(σ²/x²) ≤ x² * (σ²/x² - 1) = σ² - x²
          calc x ^ 2 * Real.log (σsq / x ^ 2)
              ≤ x ^ 2 * (σsq / x ^ 2 - 1) := by
                apply mul_le_mul_of_nonneg_left hlog2 hx2_nn
            _ = σsq - x ^ 2 := by field_simp
            _ ≤ σsq + x ^ 4 / σsq := by
                have : 0 ≤ x ^ 4 / σsq := div_nonneg (by positivity) hσ.le
                linarith
  -- Apply integral_mono_ae with the pointwise bound
  calc ∫ x, x ^ 2 * Real.log (x ^ 2 / σsq) ∂(gaussianReal 0 σsq.toNNReal)
      ≤ ∫ x, (x ^ 4 / σsq - x ^ 2) ∂(gaussianReal 0 σsq.toNNReal) := by
        exact integral_mono_ae h_int_lhs h_int_bound
          (ae_of_all _ (fun x => sq_log_div_le hσ))
    _ = ∫ x, x ^ 4 / σsq ∂(gaussianReal 0 σsq.toNNReal) -
        ∫ x, x ^ 2 ∂(gaussianReal 0 σsq.toNNReal) :=
        integral_sub (h_int_4.div_const σsq) h_int_sq
    _ = (∫ x, x ^ 4 ∂(gaussianReal 0 σsq.toNNReal)) / σsq -
        ∫ x, x ^ 2 ∂(gaussianReal 0 σsq.toNNReal) := by
        congr 1; exact integral_div σsq _
    _ = 3 * σsq ^ 2 / σsq - σsq := by
        rw [integral_pow4_gaussianReal, integral_sq_gaussianReal]
        simp [Real.coe_toNNReal σsq hσ.le]
    _ = 2 * σsq := by field_simp; ring

/-- **Gross log-Sobolev inequality** for the Gaussian measure.

For the centered Gaussian measure μ = GaussianField.measure T, the
entropy of the squared linear observable ω(f)² relative to its expectation
is controlled by twice the variance:

  `∫ (ω f)² · log((ω f)² / E[(ω f)²]) dμ ≤ 2 ‖T f‖²`

**Proof method**: Since the integrand depends only on the single linear
functional ω(f), the infinite-dimensional integral reduces to a 1D Gaussian
integral via `pairing_is_gaussian`. The 1D bound follows from
`log(y) ≤ y - 1` applied pointwise, together with the Gaussian moment
identity E[Z⁴] = 3σ⁴.

Reference: Gross (1975), Thm 1; Simon, P(φ)₂, Prop. I.16. -/
theorem gross_log_sobolev
    (f : E) :
    ∫ ω : Configuration E,
        (ω f) ^ 2 * Real.log ((ω f) ^ 2 /
          ∫ ω' : Configuration E, (ω' f) ^ 2 ∂(measure T))
      ∂(measure T) ≤
    2 * ‖T f‖ ^ 2 := by
  -- Rewrite E[ω(f)²] = ⟨Tf, Tf⟩ = ‖Tf‖²
  rw [second_moment_eq_covariance T f, real_inner_self_eq_norm_sq]
  -- Case split on whether Tf = 0
  by_cases hTf : T f = 0
  case pos =>
    -- When Tf = 0, ‖Tf‖² = 0, so RHS = 0
    have hTf_norm : ‖T f‖ = 0 := by rw [hTf]; simp
    simp only [hTf_norm, sq, mul_zero]
    -- Since ‖Tf‖² = 0, second moment = 0, so ω(f) = 0 a.e.
    have h_inner_zero : @inner ℝ H _ (T f) (T f) = 0 := by simp [hTf]
    have h_second : ∫ ω : Configuration E, (ω f) ^ 2 ∂(measure T) = 0 := by
      rw [second_moment_eq_covariance, h_inner_zero]
    -- ω(f) = 0 a.e. since E[ω(f)²] = 0
    have h_ae_zero : ∀ᵐ ω ∂(measure T), ω f = 0 := by
      have h_nn : 0 ≤ᵐ[measure T] fun ω : Configuration E => (ω f) ^ 2 :=
        ae_of_all _ (fun ω => sq_nonneg _)
      have h_int : Integrable (fun ω : Configuration E => (ω f) ^ 2) (measure T) :=
        (pairing_memLp T f 2).integrable_sq
      have := (integral_eq_zero_iff_of_nonneg_ae h_nn h_int).mp h_second
      filter_upwards [this] with ω hω
      exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hω
    -- The integrand is 0 a.e., so the integral ≤ 0
    apply integral_nonpos_of_ae
    filter_upwards [h_ae_zero] with ω hω
    simp [hω]
  case neg =>
    -- Main case: Tf ≠ 0, so σ² = ‖Tf‖² > 0
    set σsq := ‖T f‖ ^ 2 with hσsq_def
    have hσ : 0 < σsq := by positivity
    -- Reduce to 1D via pushforward
    have h_gauss := pairing_is_gaussian T f
    -- The inner product equals σ²
    have h_inner_eq : @inner ℝ H _ (T f) (T f) = σsq := real_inner_self_eq_norm_sq (T f)
    -- Use integral_map to reduce to 1D Gaussian
    have h_eval_meas := configuration_eval_measurable (E := E) f
    -- Rewrite the LHS as an integral over the pushforward measure
    have h_reduce : ∫ ω : Configuration E,
        (ω f) ^ 2 * Real.log ((ω f) ^ 2 / σsq) ∂(measure T) =
        ∫ x : ℝ, x ^ 2 * Real.log (x ^ 2 / σsq)
          ∂((measure T).map (fun ω : Configuration E => ω f)) := by
      symm
      apply integral_map h_eval_meas.aemeasurable
      exact (((measurable_id.pow_const 2).mul
        ((measurable_id.pow_const 2).div_const σsq |>.log)).aestronglyMeasurable)
    rw [h_reduce, h_gauss, h_inner_eq]
    exact log_sobolev_1d hσ

end GaussianField

end
