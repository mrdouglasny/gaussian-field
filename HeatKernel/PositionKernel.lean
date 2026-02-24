/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Position-Space Heat Kernel — Axiom Interface

Postulates the position-space heat kernel K((θ,x), (θ',x'), t) on the
cylinder S¹_L × ℝ and its connection to the spectral CLM from `Axioms.lean`.

The kernel factors as:
  K = e^{-m²t} · K_circle(θ₁,θ₂,t) · K_osc(x₁,x₂,t)

where K_circle is the heat kernel on S¹_L (periodized Gaussian / theta
function) and K_osc is the Mehler kernel (harmonic oscillator heat kernel).

## References

- Reed-Simon, "Methods of Modern Mathematical Physics", Vol. II §X.12 (Mehler)
- Chavel, "Eigenvalues in Riemannian Geometry", Ch. VI (heat kernel on circle)
- docs/position-space-kernel-plan.md
-/

import HeatKernel.Axioms
import SmoothCircle.Basic
import SchwartzNuclear.HermiteFunctions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

noncomputable section

open GaussianField GaussianField.SmoothMap_Circle Real MeasureTheory

/-! ## Mehler kernel (harmonic oscillator heat kernel) -/

/-- Mehler kernel: heat kernel for the harmonic oscillator H = -d²/dx² + x².

    Closed form: K(x₁, x₂, t) = (2π sinh 2t)^{-1/2} ·
      exp(-(cosh(2t)(x₁² + x₂²) - 2x₁x₂) / (2 sinh 2t)) -/
noncomputable def mehlerKernel (t x₁ x₂ : ℝ) : ℝ :=
  (2 * π * sinh (2 * t)) ^ (-(1 : ℝ) / 2) *
  exp (-((cosh (2 * t) * (x₁ ^ 2 + x₂ ^ 2) - 2 * x₁ * x₂) /
    (2 * sinh (2 * t))))

/-- The Mehler kernel equals its eigenfunction expansion. -/
axiom mehlerKernel_eq_series (t : ℝ) (ht : 0 < t) (x₁ x₂ : ℝ) :
    mehlerKernel t x₁ x₂ =
      ∑' (k : ℕ), exp (-(t * (2 * ↑k + 1))) *
        hermiteFunction k x₁ * hermiteFunction k x₂

set_option maxHeartbeats 400000 in
/-- The Mehler series converges absolutely for t > 0. -/
theorem mehlerKernel_summable (t : ℝ) (ht : 0 < t) (x₁ x₂ : ℝ) :
    Summable fun (k : ℕ) => exp (-(t * (2 * ↑k + 1))) *
      hermiteFunction k x₁ * hermiteFunction k x₂ := by
  -- Hermite function sup bound: |ψ_n(x)| ≤ C * (1+n)^s
  obtain ⟨C, s, hC, hs, hbound⟩ := hermiteFunction_sup_bound
  -- Set r = exp(-2t) < 1
  set r := exp (-(2 * t))
  have hr_pos : 0 < r := exp_pos _
  have hr_lt_one : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h_norm_r : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr_pos]
  -- exp(-(t*(2k+1))) = exp(-t) * exp(-2t)^k
  have h_exp_split : ∀ k : ℕ, exp (-(t * (2 * ↑k + 1))) = exp (-t) * r ^ k := by
    intro k
    rw [show r ^ k = exp (-(2 * t)) ^ k from rfl, ← Real.exp_nat_mul,
      show ↑k * -(2 * t) = -(2 * t * ↑k) from by ring, ← Real.exp_add]
    congr 1; ring
  -- Bound (1+k)^(2s) by (1+k)^p for natural p = ⌈2s⌉₊
  set p := Nat.ceil (2 * s)
  have hp : (2 * s) ≤ ↑p := Nat.le_ceil _
  have h_rpow_le_pow : ∀ k : ℕ, (1 + (↑k : ℝ)) ^ (2 * s) ≤ (1 + ↑k) ^ p := by
    intro k
    rw [← Real.rpow_natCast (1 + ↑k) p]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) k]) hp
  -- Summability of (1+k)^p * r^k: reduce to Σ k^p * r^k + Σ r^k
  -- (1+k)^p ≤ 2^p * (1 + k^p) by max bound
  have h_geom := summable_geometric_of_lt_one hr_pos.le hr_lt_one
  have h_pow_geom := summable_pow_mul_geometric_of_norm_lt_one p h_norm_r
  have h_sum_comp : Summable (fun k : ℕ => (1 + (↑k : ℝ)) ^ p * r ^ k) := by
    -- Use: (1+k)^p ≤ 2^p * (1 + k^p)
    refine Summable.of_nonneg_of_le
      (fun k => mul_nonneg
        (pow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k] : (0:ℝ) ≤ 1 + ↑k) p)
        (pow_nonneg hr_pos.le k))
      (fun k => ?_) ((h_geom.add h_pow_geom).mul_left (2 ^ p))
    -- Bound: (1+k)^p * r^k ≤ 2^p * (1 + k^p) * r^k = 2^p * (r^k + k^p * r^k)
    have h1k : (1 + (↑k : ℝ)) ^ p ≤ 2 ^ p * (1 + (↑k : ℝ) ^ p) := by
      calc (1 + (↑k : ℝ)) ^ p
          ≤ (2 * max 1 (↑k : ℝ)) ^ p := by
            apply pow_le_pow_left₀ (by linarith [Nat.cast_nonneg (α := ℝ) k] : (0:ℝ) ≤ 1 + ↑k)
            calc (1 : ℝ) + ↑k ≤ max 1 ↑k + max 1 ↑k :=
                  add_le_add (le_max_left _ _) (le_max_right (1 : ℝ) ↑k)
              _ = 2 * max 1 ↑k := (two_mul _).symm
        _ = 2 ^ p * (max 1 (↑k : ℝ)) ^ p := mul_pow _ _ _
        _ ≤ 2 ^ p * (1 + (↑k : ℝ) ^ p) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) p)
            by_cases h : (↑k : ℝ) ≤ 1
            · rw [max_eq_left h, one_pow]
              linarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) k) p]
            · push_neg at h; rw [max_eq_right h.le]
              linarith [one_le_pow₀ (M₀ := ℝ) h.le (n := p)]
    calc (1 + (↑k : ℝ)) ^ p * r ^ k
        ≤ 2 ^ p * (1 + (↑k : ℝ) ^ p) * r ^ k :=
          mul_le_mul_of_nonneg_right h1k (pow_nonneg hr_pos.le k)
      _ = 2 ^ p * (r ^ k + (↑k : ℝ) ^ p * r ^ k) := by ring
  -- Main bound: each term's norm ≤ exp(-t) * C² * (1+k)^p * r^k
  set g : ℕ → ℝ := fun k => exp (-t) * C ^ 2 * ((1 + ↑k) ^ p * r ^ k) with hg_def
  have hg_summable : Summable g := h_sum_comp.mul_left _
  have h_norm_le : ∀ k : ℕ, ‖exp (-(t * (2 * ↑k + 1))) *
      hermiteFunction k x₁ * hermiteFunction k x₂‖ ≤ g k := by
    intro k
    rw [Real.norm_eq_abs, h_exp_split k]
    have h_exp_nonneg : (0 : ℝ) ≤ exp (-t) := le_of_lt (exp_pos _)
    have hr_pow_nonneg : (0 : ℝ) ≤ r ^ k := pow_nonneg hr_pos.le k
    have h1k_nonneg : (0 : ℝ) ≤ 1 + ↑k := by linarith [Nat.cast_nonneg (α := ℝ) k]
    have h1k_pos : (0 : ℝ) < 1 + ↑k := by linarith [Nat.cast_nonneg (α := ℝ) k]
    -- |exp(-t) * r^k * ψ(x₁) * ψ(x₂)| ≤ exp(-t) * r^k * C(1+k)^s * C(1+k)^s
    have step1 : |exp (-t) * r ^ k * hermiteFunction k x₁ * hermiteFunction k x₂| ≤
        exp (-t) * r ^ k * (C * (1 + ↑k) ^ s) * (C * (1 + ↑k) ^ s) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (mul_nonneg h_exp_nonneg hr_pow_nonneg)]
      apply mul_le_mul (mul_le_mul_of_nonneg_left (hbound k x₁)
        (mul_nonneg h_exp_nonneg hr_pow_nonneg))
        (hbound k x₂) (abs_nonneg _)
        (mul_nonneg (mul_nonneg h_exp_nonneg hr_pow_nonneg)
          (mul_nonneg hC.le (Real.rpow_nonneg h1k_nonneg _)))
    -- C(1+k)^s * C(1+k)^s = C² * (1+k)^(2s)
    have step2 : exp (-t) * r ^ k * (C * (1 + ↑k) ^ s) * (C * (1 + ↑k) ^ s) =
        exp (-t) * C ^ 2 * ((1 + ↑k) ^ (2 * s) * r ^ k) := by
      -- Rearrange: exp * r^k * (C * a) * (C * a) = exp * C² * (a * a * r^k)
      -- where a = (1+k)^s, then a * a = (1+k)^(2s)
      set a := (1 + (↑k : ℝ)) ^ s
      have ha2 : a * a = (1 + ↑k) ^ (2 * s) :=
        (Real.rpow_add h1k_pos s s).symm ▸ (show s + s = 2 * s by ring) ▸ rfl
      calc exp (-t) * r ^ k * (C * a) * (C * a)
          = exp (-t) * (C * C) * (a * a) * r ^ k := by ring
        _ = exp (-t) * C ^ 2 * ((1 + ↑k) ^ (2 * s) * r ^ k) := by
            rw [ha2, sq, mul_assoc]
    -- (1+k)^(2s) ≤ (1+k)^p
    have step3 : exp (-t) * C ^ 2 * ((1 + ↑k) ^ (2 * s) * r ^ k) ≤ g k := by
      simp only [hg_def]
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg h_exp_nonneg (sq_nonneg _))
      exact mul_le_mul_of_nonneg_right (h_rpow_le_pow k) hr_pow_nonneg
    linarith
  exact Summable.of_norm_bounded (g := g) hg_summable h_norm_le

/-- The Mehler kernel is symmetric. -/
theorem mehlerKernel_symmetric (t x₁ x₂ : ℝ) :
    mehlerKernel t x₁ x₂ = mehlerKernel t x₂ x₁ := by
  unfold mehlerKernel; ring_nf

/-- The Mehler kernel is positive for t > 0. -/
theorem mehlerKernel_pos (t : ℝ) (ht : 0 < t) (x₁ x₂ : ℝ) :
    0 < mehlerKernel t x₁ x₂ := by
  unfold mehlerKernel
  apply mul_pos
  · apply rpow_pos_of_pos
    apply mul_pos (mul_pos two_pos pi_pos)
    exact Real.sinh_pos_iff.mpr (by linarith)
  · exact exp_pos _

set_option maxHeartbeats 800000 in
/-- The Mehler kernel reproduces Hermite eigenfunctions. -/
theorem mehlerKernel_reproduces_hermite (t : ℝ) (ht : 0 < t)
    (k : ℕ) (x₁ : ℝ) :
    ∫ x₂, mehlerKernel t x₁ x₂ * hermiteFunction k x₂ =
      exp (-(t * (2 * ↑k + 1))) * hermiteFunction k x₁ := by
  -- Step 1: Expand mehlerKernel via series expansion
  simp_rw [mehlerKernel_eq_series t ht x₁]
  -- Goal: ∫ x₂, (∑' j, e_j * ψ_j(x₁) * ψ_j(x₂)) * ψ_k(x₂) = e_k * ψ_k(x₁)
  -- Step 2: Distribute ψ_k(x₂) into the tsum
  conv_lhs =>
    arg 2; ext x₂
    rw [← tsum_mul_right]
  -- Goal: ∫ x₂, ∑' j, e_j * ψ_j(x₁) * ψ_j(x₂) * ψ_k(x₂) = e_k * ψ_k(x₁)
  -- Step 3: Define the summand function
  set F : ℕ → ℝ → ℝ := fun j x₂ =>
    exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x₁ *
      hermiteFunction j x₂ * hermiteFunction k x₂
  -- Step 4: Integrability of each summand
  have hF_int : ∀ j, Integrable (F j) volume := by
    intro j
    simp only [F]
    have h_prod : Integrable (fun x₂ => hermiteFunction j x₂ * hermiteFunction k x₂) volume :=
      (hermiteFunction_memLp j).integrable_mul (hermiteFunction_memLp k)
    exact (h_prod.const_mul (exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x₁)).congr
      (by filter_upwards with x₂; ring)
  -- Step 5: Summability of integral norms for integral_tsum_of_summable_integral_norm
  have hF_sum : Summable fun j => ∫ x₂, ‖F j x₂‖ := by
    -- Bound: ‖F j x₂‖ ≤ |e_j| * |ψ_j(x₁)| * |ψ_j(x₂) * ψ_k(x₂)|
    -- Then ∫ ‖F j‖ ≤ |e_j| * |ψ_j(x₁)| * ∫ |ψ_j * ψ_k| ≤ |e_j| * |ψ_j(x₁)| * 1
    -- Bound |ψ_j(x₁)| by sup bound, |e_j| by geometric decay => summable
    obtain ⟨C, s, hC, hs, hbound⟩ := hermiteFunction_sup_bound
    set r := exp (-(2 * t))
    have hr_pos : 0 < r := exp_pos _
    have hr_lt_one : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    -- AM-GM bound: ∫ |ψ_j * ψ_k| ≤ 1
    have h_ψψ_norm_le : ∀ j, ∫ x₂, |hermiteFunction j x₂ * hermiteFunction k x₂| ≤ 1 := by
      intro j
      have hψ_sq_int : ∀ n, Integrable (fun x => hermiteFunction n x ^ 2) :=
        fun n => ((hermiteFunction_memLp n).integrable_mul (hermiteFunction_memLp n)).congr
          (by filter_upwards with x; show (hermiteFunction n * hermiteFunction n) x = _; simp [sq, Pi.mul_apply])
      have hψ_sq : ∀ n, ∫ x, hermiteFunction n x ^ 2 = 1 := fun n => by
        have h := hermiteFunction_orthonormal n n
        simp at h
        rw [show (fun x => hermiteFunction n x ^ 2) =
          (fun x => hermiteFunction n x * hermiteFunction n x) from by ext x; ring]
        exact h
      calc ∫ x₂, |hermiteFunction j x₂ * hermiteFunction k x₂|
          = ∫ x₂, |hermiteFunction j x₂| * |hermiteFunction k x₂| := by
            congr 1; ext x₂; exact abs_mul _ _
        _ ≤ ∫ x₂, ((hermiteFunction j x₂ ^ 2 + hermiteFunction k x₂ ^ 2) / 2) := by
            apply integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun a => mul_nonneg (abs_nonneg _) (abs_nonneg _))
              ((hψ_sq_int j).add (hψ_sq_int k) |>.div_const 2)
            exact Filter.Eventually.of_forall fun a => by
              have h := two_mul_le_add_sq |hermiteFunction j a| |hermiteFunction k a|
              rw [sq_abs, sq_abs] at h
              have : |hermiteFunction j a| * |hermiteFunction k a| ≤
                (hermiteFunction j a ^ 2 + hermiteFunction k a ^ 2) / 2 := by linarith
              exact this
        _ = 1 := by
            rw [integral_div, integral_add (hψ_sq_int j) (hψ_sq_int k), hψ_sq j, hψ_sq k]
            norm_num
    -- exp(-(t*(2j+1))) = exp(-t) * r^j
    have h_exp_split : ∀ j : ℕ, exp (-(t * (2 * ↑j + 1))) = exp (-t) * r ^ j := by
      intro j
      rw [show r ^ j = exp (-(2 * t)) ^ j from rfl, ← Real.exp_nat_mul,
        show ↑j * -(2 * t) = -(2 * t * ↑j) from by ring, ← Real.exp_add]
      congr 1; ring
    -- Bound: ∫ ‖F j‖ ≤ exp(-t) * C * (1+j)^s * r^j
    apply Summable.of_nonneg_of_le
      (fun j => integral_nonneg (fun _ => norm_nonneg _))
    · intro j
      have h_exp_nonneg : (0 : ℝ) ≤ exp (-(t * (2 * ↑j + 1))) := le_of_lt (exp_pos _)
      calc ∫ x₂, ‖F j x₂‖
          = ∫ x₂, (exp (-(t * (2 * ↑j + 1))) * |hermiteFunction j x₁|) *
              |hermiteFunction j x₂ * hermiteFunction k x₂| := by
            congr 1; ext x₂; simp only [F, Real.norm_eq_abs]
            rw [show exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x₁ *
              hermiteFunction j x₂ * hermiteFunction k x₂ =
              (exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x₁) *
              (hermiteFunction j x₂ * hermiteFunction k x₂) from by ring,
              abs_mul, abs_mul, abs_of_nonneg h_exp_nonneg]
        _ = exp (-(t * (2 * ↑j + 1))) * |hermiteFunction j x₁| *
              ∫ x₂, |hermiteFunction j x₂ * hermiteFunction k x₂| := by
            rw [integral_const_mul]
        _ ≤ exp (-(t * (2 * ↑j + 1))) * (C * (1 + ↑j) ^ s) * 1 := by
            apply mul_le_mul
            · exact mul_le_mul_of_nonneg_left (hbound j x₁) h_exp_nonneg
            · exact h_ψψ_norm_le j
            · exact integral_nonneg (fun _ => abs_nonneg _)
            · exact mul_nonneg h_exp_nonneg (mul_nonneg hC.le
                (Real.rpow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j]) _))
        _ = exp (-t) * (C * (1 + ↑j) ^ s) * r ^ j := by
            rw [h_exp_split j]; ring
    · -- Summability of exp(-t) * C * (1+j)^s * r^j
      -- This follows from summability of (1+j)^p * r^j for any polynomial bound
      set p := Nat.ceil s
      have hp : s ≤ ↑p := Nat.le_ceil _
      have h_rpow_le_pow : ∀ j : ℕ, (1 + (↑j : ℝ)) ^ s ≤ (1 + ↑j) ^ p := by
        intro j
        rw [← Real.rpow_natCast (1 + ↑j) p]
        exact Real.rpow_le_rpow_of_exponent_le
          (by linarith [Nat.cast_nonneg (α := ℝ) j]) hp
      have h_sum_comp : Summable (fun j : ℕ => (1 + (↑j : ℝ)) ^ p * r ^ j) := by
        have h_geom := summable_geometric_of_lt_one hr_pos.le hr_lt_one
        have h_norm_r : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr_pos]
        have h_pow_geom := summable_pow_mul_geometric_of_norm_lt_one p h_norm_r
        refine Summable.of_nonneg_of_le
          (fun j => mul_nonneg
            (pow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j]) p)
            (pow_nonneg hr_pos.le j))
          (fun j => ?_) ((h_geom.add h_pow_geom).mul_left (2 ^ p))
        have h1j : (1 + (↑j : ℝ)) ^ p ≤ 2 ^ p * (1 + (↑j : ℝ) ^ p) := by
          calc (1 + (↑j : ℝ)) ^ p
              ≤ (2 * max 1 (↑j : ℝ)) ^ p := by
                apply pow_le_pow_left₀ (by linarith [Nat.cast_nonneg (α := ℝ) j])
                calc (1 : ℝ) + ↑j ≤ max 1 ↑j + max 1 ↑j :=
                      add_le_add (le_max_left _ _) (le_max_right (1 : ℝ) ↑j)
                  _ = 2 * max 1 ↑j := (two_mul _).symm
            _ = 2 ^ p * (max 1 (↑j : ℝ)) ^ p := mul_pow _ _ _
            _ ≤ 2 ^ p * (1 + (↑j : ℝ) ^ p) := by
                apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) p)
                by_cases h : (↑j : ℝ) ≤ 1
                · rw [max_eq_left h, one_pow]; linarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) j) p]
                · push_neg at h; rw [max_eq_right h.le]; linarith [one_le_pow₀ (M₀ := ℝ) h.le (n := p)]
        calc (1 + (↑j : ℝ)) ^ p * r ^ j
            ≤ 2 ^ p * (1 + (↑j : ℝ) ^ p) * r ^ j :=
              mul_le_mul_of_nonneg_right h1j (pow_nonneg hr_pos.le j)
          _ = 2 ^ p * (r ^ j + (↑j : ℝ) ^ p * r ^ j) := by ring
      refine Summable.of_nonneg_of_le
        (fun j => by positivity)
        (fun j => ?_)
        (h_sum_comp.mul_left (exp (-t) * C))
      show exp (-t) * (C * (1 + ↑j) ^ s) * r ^ j ≤ exp (-t) * C * ((1 + ↑j) ^ p * r ^ j)
      have h1j_nonneg : (0 : ℝ) ≤ 1 + ↑j := by linarith [Nat.cast_nonneg (α := ℝ) j]
      calc exp (-t) * (C * (1 + ↑j) ^ s) * r ^ j
          = exp (-t) * C * ((1 + ↑j) ^ s * r ^ j) := by ring
        _ ≤ exp (-t) * C * ((1 + ↑j) ^ p * r ^ j) := by
            gcongr; exact h_rpow_le_pow j
  -- Step 6: Swap integral and tsum
  rw [← integral_tsum_of_summable_integral_norm hF_int hF_sum]
  -- Goal: ∑' j, ∫ x₂, F j x₂ = e_k * ψ_k(x₁)
  -- Step 7: Compute each integral using orthonormality
  have h_eval : ∀ j, ∫ x₂, F j x₂ =
      exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x₁ *
        (if j = k then 1 else 0) := by
    intro j
    simp only [F]
    rw [show (fun x₂ => exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x₁ *
        hermiteFunction j x₂ * hermiteFunction k x₂) =
      (fun x₂ => exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x₁ *
        (hermiteFunction j x₂ * hermiteFunction k x₂)) from by ext; ring]
    rw [integral_const_mul, hermiteFunction_orthonormal j k]
  simp_rw [h_eval]
  -- Step 8: Collapse the tsum to the k-th term
  have h_zero : ∀ j, j ≠ k →
      exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x₁ *
        (if j = k then (1 : ℝ) else 0) = 0 := by
    intro j hj; rw [if_neg hj, mul_zero]
  rw [tsum_eq_single k h_zero, if_pos rfl, mul_one]

set_option maxHeartbeats 1200000 in
/-- The Mehler kernel satisfies the semigroup property. -/
theorem mehlerKernel_semigroup (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x₁ x₂ : ℝ) :
    ∫ z, mehlerKernel s x₁ z * mehlerKernel t z x₂ =
      mehlerKernel (s + t) x₁ x₂ := by
  -- Strategy: expand the second kernel as eigenfunction series, swap integral and sum,
  -- apply reproducing property for the first kernel, combine exponentials.
  -- This parallels circleHeatKernel_semigroup.
  -- Step 1: Expand the second Mehler kernel as a series
  simp_rw [mehlerKernel_eq_series t ht]
  -- Goal: ∫ z, K_s(x₁,z) * (∑' k, e_k^t * ψ_k(z) * ψ_k(x₂)) = K_{s+t}(x₁, x₂)
  -- Step 2: Set up G k z = e_k^t * ψ_k(x₂) * (K_s(x₁,z) * ψ_k(z))
  set G : ℕ → ℝ → ℝ := fun k z =>
    exp (-(t * (2 * ↑k + 1))) * hermiteFunction k x₂ *
      (mehlerKernel s x₁ z * hermiteFunction k z) with hG_def
  have h_eq_tsum : ∀ z,
      mehlerKernel s x₁ z * (∑' k, exp (-(t * (2 * ↑k + 1))) *
        hermiteFunction k z * hermiteFunction k x₂) = ∑' k, G k z := by
    intro z; simp only [hG_def]; rw [← tsum_mul_left]
    exact tsum_congr (fun k => by ring)
  simp_rw [h_eq_tsum]
  -- Step 3: Prove the Mehler kernel K_s(x₁, ·) is integrable (Gaussian in z)
  have hKs_integrable : Integrable (mehlerKernel s x₁) := by
    unfold mehlerKernel
    apply Integrable.const_mul
    have hsinh_pos : 0 < sinh (2 * s) := Real.sinh_pos_iff.mpr (by linarith)
    have hcosh_pos : 0 < cosh (2 * s) := cosh_pos (2 * s)
    have ha_pos : 0 < cosh (2 * s) / (2 * sinh (2 * s)) :=
      div_pos hcosh_pos (mul_pos two_pos hsinh_pos)
    -- Dominator: exp(-a*(z-z₀)²) is integrable where a = cosh(2s)/(2sinh(2s)), z₀ = x₁/cosh(2s)
    apply ((integrable_exp_neg_mul_sq ha_pos).comp_sub_right
      (x₁ / cosh (2 * s))).mono' (by fun_prop)
    apply ae_of_all; intro z
    rw [Real.norm_eq_abs, abs_of_nonneg (exp_pos _).le]
    -- Key inequality: the Mehler exponent ≤ -a*(z-z₀)²
    -- Equiv: cosh*(z-z₀)² ≤ cosh*(x₁²+z²)-2x₁z (divided by 2sinh)
    -- Equiv: x₁²/cosh ≤ cosh*x₁² (true since cosh ≥ 1)
    have h_key : cosh (2 * s) * (z - x₁ / cosh (2 * s)) ^ 2 ≤
        cosh (2 * s) * (x₁ ^ 2 + z ^ 2) - 2 * x₁ * z := by
      have h_expand : cosh (2 * s) * (z - x₁ / cosh (2 * s)) ^ 2 =
          cosh (2 * s) * z ^ 2 - 2 * x₁ * z + x₁ ^ 2 / cosh (2 * s) := by
        field_simp; ring
      rw [h_expand]
      have h1 : x₁ ^ 2 / cosh (2 * s) ≤ cosh (2 * s) * x₁ ^ 2 := by
        rw [div_le_iff₀ hcosh_pos]
        nlinarith [one_le_cosh (2 * s), sq_nonneg x₁, sq_nonneg (cosh (2 * s) - 1)]
      linarith
    -- From h_key, derive the exponent inequality
    have h2sinh_pos : 0 < 2 * sinh (2 * s) := mul_pos two_pos hsinh_pos
    calc exp (-((cosh (2 * s) * (x₁ ^ 2 + z ^ 2) - 2 * x₁ * z) / (2 * sinh (2 * s))))
        ≤ exp (-(cosh (2 * s) * (z - x₁ / cosh (2 * s)) ^ 2 / (2 * sinh (2 * s)))) := by
          apply exp_le_exp_of_le
          apply neg_le_neg
          exact div_le_div_of_nonneg_right h_key h2sinh_pos.le
      _ = exp (-(cosh (2 * s) / (2 * sinh (2 * s))) * (z - x₁ / cosh (2 * s)) ^ 2) := by
          congr 1; ring
  -- Step 4: Integrability of each G k, using K_s integrable and ψ_k bounded
  have hG_int : ∀ k, Integrable (G k) volume := by
    obtain ⟨C_bnd, s_bnd, _, _, hbnd⟩ := hermiteFunction_sup_bound
    intro k
    show Integrable (fun z => exp (-(t * (2 * ↑k + 1))) * hermiteFunction k x₂ *
      (mehlerKernel s x₁ z * hermiteFunction k z)) volume
    apply Integrable.const_mul
    -- K_s(x₁,·) * ψ_k is integrable: K_s is integrable and ψ_k is bounded (L^∞)
    exact hKs_integrable.mul_of_top_left
      (memLp_top_of_bound (hermiteFunction_memLp k).aestronglyMeasurable
        (C_bnd * (1 + ↑k) ^ s_bnd) (ae_of_all _ (fun z => by
          rw [Real.norm_eq_abs]; exact hbnd k z)))
  -- Step 5: Summability of ∫ ‖G k‖
  -- Bound: ‖G k z‖ ≤ e_k^t * |ψ_k(x₂)| * |K_s(x₁,z)| * |ψ_k(z)|
  --   ≤ e_k^t * C*(1+k)^sv * |K_s(x₁,z)| * C*(1+k)^sv
  -- ∫ ‖G k‖ ≤ e_k^t * (C*(1+k)^sv)^2 * L   where L = ∫|K_s| < ∞
  -- Then ∑ e_k^t * (C*(1+k)^sv)^2 is summable by polynomial-geometric comparison.
  have hG_sum : Summable fun k => ∫ z, ‖G k z‖ := by
    obtain ⟨C, sv, hC, hsv, hbound⟩ := hermiteFunction_sup_bound
    set L := ∫ z, |mehlerKernel s x₁ z|
    have hL_nonneg : 0 ≤ L := integral_nonneg (fun _ => abs_nonneg _)
    -- Bound: ∫ ‖G k‖ ≤ exp(-t*(2k+1)) * (C*(1+k)^sv)^2 * L
    have h_int_bound : ∀ k, ∫ z, ‖G k z‖ ≤
        exp (-(t * (2 * ↑k + 1))) * (C * (1 + ↑k) ^ sv) ^ 2 * L := by
      intro k
      -- Pointwise bound: ‖G k z‖ ≤ exp(...)*(C*(1+k)^sv)^2 * |K_s(x₁,z)|
      have h_ptwise : ∀ z, ‖G k z‖ ≤
          exp (-(t * (2 * ↑k + 1))) * (C * (1 + ↑k) ^ sv) ^ 2 * |mehlerKernel s x₁ z| := by
        intro z
        simp only [hG_def, Real.norm_eq_abs]
        have h1 : |hermiteFunction k x₂| ≤ C * (1 + ↑k) ^ sv := hbound k x₂
        have h2 : |hermiteFunction k z| ≤ C * (1 + ↑k) ^ sv := hbound k z
        have h_exp_nn : (0 : ℝ) ≤ exp (-(t * (2 * ↑k + 1))) := le_of_lt (exp_pos _)
        have hC_nn : 0 ≤ C * (1 + ↑k) ^ sv := le_trans (abs_nonneg _) (hbound k z)
        calc |exp (-(t * (2 * ↑k + 1))) * hermiteFunction k x₂ *
              (mehlerKernel s x₁ z * hermiteFunction k z)|
            = exp (-(t * (2 * ↑k + 1))) * |hermiteFunction k x₂| *
              (|mehlerKernel s x₁ z| * |hermiteFunction k z|) := by
              rw [abs_mul, abs_mul, abs_of_nonneg h_exp_nn, abs_mul]
          _ ≤ exp (-(t * (2 * ↑k + 1))) * (C * (1 + ↑k) ^ sv) *
              (|mehlerKernel s x₁ z| * (C * (1 + ↑k) ^ sv)) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left h1 h_exp_nn
              · exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
              · exact mul_nonneg (abs_nonneg _) (abs_nonneg _)
              · exact mul_nonneg h_exp_nn hC_nn
          _ = exp (-(t * (2 * ↑k + 1))) * (C * (1 + ↑k) ^ sv) ^ 2 *
              |mehlerKernel s x₁ z| := by ring
      -- Integrate the bound
      calc ∫ z, ‖G k z‖
          ≤ ∫ z, exp (-(t * (2 * ↑k + 1))) * (C * (1 + ↑k) ^ sv) ^ 2 *
              |mehlerKernel s x₁ z| := by
            apply integral_mono (hG_int k).norm
            · exact (hKs_integrable.norm).const_mul _
            · exact h_ptwise
        _ = exp (-(t * (2 * ↑k + 1))) * (C * (1 + ↑k) ^ sv) ^ 2 * L := by
            rw [integral_const_mul]
    -- Summability: ∑ exp(-(t*(2k+1))) * (C*(1+k)^sv)^2 * L via polynomial-geometric comparison
    set r_t := exp (-(2 * t))
    have hr_t_pos : 0 < r_t := exp_pos _
    have hr_t_lt : r_t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have h_norm_r_t : ‖r_t‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr_t_pos]
    have h_exp_split : ∀ k : ℕ, exp (-(t * (2 * ↑k + 1))) = exp (-t) * r_t ^ k := by
      intro k
      rw [show r_t ^ k = exp (-(2 * t)) ^ k from rfl, ← Real.exp_nat_mul,
        show ↑k * -(2 * t) = -(2 * t * ↑k) from by ring, ← Real.exp_add]
      congr 1; ring
    set p := Nat.ceil (2 * sv)
    have hp : 2 * sv ≤ ↑p := Nat.le_ceil _
    have h_rpow_le_pow : ∀ k : ℕ, (1 + (↑k : ℝ)) ^ (2 * sv) ≤ (1 + ↑k) ^ p := by
      intro k
      rw [← Real.rpow_natCast (1 + ↑k) p]
      exact Real.rpow_le_rpow_of_exponent_le
        (by linarith [Nat.cast_nonneg (α := ℝ) k]) hp
    -- (C*(1+k)^sv)^2 = C^2 * (1+k)^{2sv} ≤ C^2 * (1+k)^p
    have h_sq_bound : ∀ k : ℕ, (C * (1 + ↑k) ^ sv) ^ 2 ≤ C ^ 2 * (1 + ↑k) ^ p := by
      intro k
      rw [mul_pow]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      -- ((1+k)^sv)^2 = (1+k)^(2*sv) ≤ (1+k)^p
      have h1k_nn : (0 : ℝ) ≤ 1 + ↑k := by linarith [Nat.cast_nonneg (α := ℝ) k]
      calc ((1 + (↑k : ℝ)) ^ sv) ^ 2
          = (1 + ↑k) ^ (2 * sv) := by
            rw [← Real.rpow_natCast ((1 + ↑k) ^ sv) 2, ← Real.rpow_mul h1k_nn]
            congr 1; push_cast; ring
        _ ≤ (1 + ↑k) ^ p := h_rpow_le_pow k
    -- Summability of (1+k)^p * r_t^k
    have h_sum_comp : Summable (fun k : ℕ => (1 + (↑k : ℝ)) ^ p * r_t ^ k) := by
      have h_geom := summable_geometric_of_lt_one hr_t_pos.le hr_t_lt
      have h_pow_geom := summable_pow_mul_geometric_of_norm_lt_one p h_norm_r_t
      refine Summable.of_nonneg_of_le
        (fun k => mul_nonneg
          (pow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k]) p)
          (pow_nonneg hr_t_pos.le k))
        (fun k => ?_) ((h_geom.add h_pow_geom).mul_left (2 ^ p))
      have h1k : (1 + (↑k : ℝ)) ^ p ≤ 2 ^ p * (1 + (↑k : ℝ) ^ p) := by
        calc (1 + (↑k : ℝ)) ^ p
            ≤ (2 * max 1 (↑k : ℝ)) ^ p := by
              apply pow_le_pow_left₀ (by linarith [Nat.cast_nonneg (α := ℝ) k])
              calc (1 : ℝ) + ↑k ≤ max 1 ↑k + max 1 ↑k :=
                    add_le_add (le_max_left _ _) (le_max_right (1 : ℝ) ↑k)
                _ = 2 * max 1 ↑k := (two_mul _).symm
          _ = 2 ^ p * (max 1 (↑k : ℝ)) ^ p := mul_pow _ _ _
          _ ≤ 2 ^ p * (1 + (↑k : ℝ) ^ p) := by
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) p)
              by_cases h : (↑k : ℝ) ≤ 1
              · rw [max_eq_left h, one_pow]; linarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) k) p]
              · push_neg at h; rw [max_eq_right h.le]; linarith [one_le_pow₀ (M₀ := ℝ) h.le (n := p)]
      calc (1 + (↑k : ℝ)) ^ p * r_t ^ k
          ≤ 2 ^ p * (1 + (↑k : ℝ) ^ p) * r_t ^ k :=
            mul_le_mul_of_nonneg_right h1k (pow_nonneg hr_t_pos.le k)
        _ = 2 ^ p * (r_t ^ k + (↑k : ℝ) ^ p * r_t ^ k) := by ring
    -- Main summability
    apply Summable.of_nonneg_of_le
      (fun k => integral_nonneg (fun _ => norm_nonneg _))
    · intro k
      calc ∫ z, ‖G k z‖
          ≤ exp (-(t * (2 * ↑k + 1))) * (C * (1 + ↑k) ^ sv) ^ 2 * L := h_int_bound k
        _ ≤ exp (-(t * (2 * ↑k + 1))) * (C ^ 2 * (1 + ↑k) ^ p) * L := by
            gcongr; exact h_sq_bound k
        _ = L * C ^ 2 * exp (-t) * ((1 + ↑k) ^ p * r_t ^ k) := by
            rw [h_exp_split k]; ring
    · exact (h_sum_comp.mul_left (L * C ^ 2 * exp (-t)))
  -- Step 5: Swap ∫ and ∑'
  rw [← integral_tsum_of_summable_integral_norm hG_int hG_sum]
  -- Step 6: Evaluate each integral using reproducing property
  have h_repro : ∀ k, ∫ z, G k z =
      exp (-(t * (2 * ↑k + 1))) * hermiteFunction k x₂ *
      (exp (-(s * (2 * ↑k + 1))) * hermiteFunction k x₁) := by
    intro k; simp only [hG_def]
    rw [integral_const_mul]; congr 1
    exact mehlerKernel_reproduces_hermite s hs k x₁
  simp_rw [h_repro]
  -- Step 7: Combine exponentials
  rw [mehlerKernel_eq_series (s + t) (by linarith) x₁ x₂]
  congr 1; funext k
  rw [show exp (-(t * (2 * ↑k + 1))) * hermiteFunction k x₂ *
    (exp (-(s * (2 * ↑k + 1))) * hermiteFunction k x₁) =
    (exp (-(s * (2 * ↑k + 1))) * exp (-(t * (2 * ↑k + 1)))) *
    hermiteFunction k x₁ * hermiteFunction k x₂ from by ring,
    ← Real.exp_add]
  congr 1; congr 1; ring

/-! ## Circle heat kernel -/

/-- Heat kernel on S¹_L, defined as eigenfunction expansion:
    K_circle(θ₁, θ₂, t) = Σ_n e^{-t(2πn/L)²} ψ_n(θ₁) ψ_n(θ₂). -/
noncomputable def circleHeatKernel (L : ℝ) [Fact (0 < L)]
    (t θ₁ θ₂ : ℝ) : ℝ :=
  ∑' (n : ℕ), exp (-(t * (2 * π * ↑n / L) ^ 2)) *
    fourierBasisFun (L := L) n θ₁ * fourierBasisFun (L := L) n θ₂

/-- The circle heat kernel series converges absolutely for t > 0. -/
theorem circleHeatKernel_summable (L : ℝ) [hL : Fact (0 < L)]
    (t : ℝ) (ht : 0 < t) (θ₁ θ₂ : ℝ) :
    Summable fun (n : ℕ) => exp (-(t * (2 * π * ↑n / L) ^ 2)) *
      fourierBasisFun (L := L) n θ₁ * fourierBasisFun (L := L) n θ₂ := by
  -- Bound: |fourierBasisFun n x| ≤ M for all n, x
  set M := max (1 / Real.sqrt L) (Real.sqrt (2 / L))
  have hM_nonneg : 0 ≤ M := le_max_of_le_right (Real.sqrt_nonneg _)
  -- Set r = exp(-t*(2π/L)²) < 1
  set c := t * (2 * π / L) ^ 2 with hc_def
  have hc_pos : 0 < c := mul_pos ht (sq_pos_of_pos (div_pos (mul_pos two_pos pi_pos) hL.out))
  set r := exp (-c)
  have hr_pos : 0 < r := exp_pos _
  have hr_lt_one : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  -- Key inequality: t * (2πn/L)² = c * n², and n² ≥ n for n : ℕ
  have h_exp_le : ∀ n : ℕ, exp (-(t * (2 * π * ↑n / L) ^ 2)) ≤ r ^ n := by
    intro n
    rw [show r ^ n = exp (-c) ^ n from rfl, ← Real.exp_nat_mul,
      show ↑n * -c = -(c * ↑n) from by ring]
    apply Real.exp_le_exp.mpr
    -- Need: -(t * (2πn/L)²) ≤ -(c * n), i.e., c * n ≤ t * (2πn/L)²
    -- t * (2πn/L)² = t * (2π/L)² * n² = c * n²
    have h_eq : t * (2 * π * ↑n / L) ^ 2 = c * (↑n) ^ 2 := by
      simp only [hc_def]; ring
    rw [h_eq]
    -- -(c * n²) ≤ -(c * n) ⟸ c * n ≤ c * n² ⟸ n ≤ n² (since c > 0)
    -- n ≤ n² for n : ℕ: either n = 0 (trivial) or n ≥ 1 so n * 1 ≤ n * n
    have hn_sq : (↑n : ℝ) ≤ (↑n) ^ 2 := by
      rcases n with _ | n
      · simp
      · have h1 : (1 : ℝ) ≤ ↑(n + 1) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        calc (↑(n + 1) : ℝ) = ↑(n + 1) * 1 := (mul_one _).symm
          _ ≤ ↑(n + 1) * ↑(n + 1) := by apply mul_le_mul_of_nonneg_left h1; positivity
          _ = (↑(n + 1)) ^ 2 := (sq _).symm
    linarith [mul_le_mul_of_nonneg_left hn_sq hc_pos.le]
  -- Comparison: ‖term n‖ ≤ M² · r^n
  have h_geom : Summable (fun n => M ^ 2 * r ^ n) :=
    (summable_geometric_of_lt_one hr_pos.le hr_lt_one).mul_left _
  apply Summable.of_norm_bounded (g := fun n => M ^ 2 * r ^ n) h_geom
  intro n
  rw [Real.norm_eq_abs]
  have h_exp_nonneg : 0 ≤ exp (-(t * (2 * π * ↑n / L) ^ 2)) := le_of_lt (exp_pos _)
  calc |exp (-(t * (2 * π * ↑n / L) ^ 2)) *
        fourierBasisFun (L := L) n θ₁ * fourierBasisFun (L := L) n θ₂|
      ≤ exp (-(t * (2 * π * ↑n / L) ^ 2)) *
        |fourierBasisFun (L := L) n θ₁| * |fourierBasisFun (L := L) n θ₂| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h_exp_nonneg]
    _ ≤ exp (-(t * (2 * π * ↑n / L) ^ 2)) * M * M := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left
            (SmoothMap_Circle.fourierBasisFun_abs_le n θ₁) h_exp_nonneg
        · exact SmoothMap_Circle.fourierBasisFun_abs_le n θ₂
        · exact abs_nonneg _
        · exact mul_nonneg h_exp_nonneg hM_nonneg
    _ = M ^ 2 * exp (-(t * (2 * π * ↑n / L) ^ 2)) := by ring
    _ ≤ M ^ 2 * r ^ n := by
        apply mul_le_mul_of_nonneg_left (h_exp_le n) (sq_nonneg _)

/-- The circle heat kernel is symmetric. -/
theorem circleHeatKernel_symmetric (L : ℝ) [Fact (0 < L)]
    (t θ₁ θ₂ : ℝ) :
    circleHeatKernel L t θ₁ θ₂ = circleHeatKernel L t θ₂ θ₁ := by
  unfold circleHeatKernel
  exact tsum_congr (fun n => by ring)

/-- The circle heat kernel is positive for t > 0. -/
axiom circleHeatKernel_pos (L : ℝ) [Fact (0 < L)]
    (t : ℝ) (ht : 0 < t) (θ₁ θ₂ : ℝ) :
    0 < circleHeatKernel L t θ₁ θ₂

/-- The circle heat kernel is L-periodic in the first argument. -/
theorem circleHeatKernel_periodic₁ (L : ℝ) [Fact (0 < L)]
    (t θ₁ θ₂ : ℝ) :
    circleHeatKernel L t (θ₁ + L) θ₂ = circleHeatKernel L t θ₁ θ₂ := by
  unfold circleHeatKernel
  exact tsum_congr (fun n => by rw [fourierBasisFun_periodic n θ₁])

/-- The circle heat kernel is L-periodic in the second argument. -/
theorem circleHeatKernel_periodic₂ (L : ℝ) [Fact (0 < L)]
    (t θ₁ θ₂ : ℝ) :
    circleHeatKernel L t θ₁ (θ₂ + L) = circleHeatKernel L t θ₁ θ₂ := by
  unfold circleHeatKernel
  exact tsum_congr (fun n => by rw [fourierBasisFun_periodic n θ₂])

set_option maxHeartbeats 1200000 in
/-- The circle heat kernel reproduces Fourier eigenfunctions. -/
theorem circleHeatKernel_reproduces_fourier (L : ℝ) [hL : Fact (0 < L)]
    (t : ℝ) (ht : 0 < t) (n : ℕ) (θ₁ : ℝ) :
    ∫ θ₂ in (0 : ℝ)..L,
      circleHeatKernel L t θ₁ θ₂ * fourierBasisFun (L := L) n θ₂ =
    exp (-(t * (2 * π * ↑n / L) ^ 2)) * fourierBasisFun (L := L) n θ₁ := by
  -- Strategy: expand circleHeatKernel as series, swap integral and sum,
  -- use Fourier orthogonality to collapse to single term.
  -- Step 1: Convert to set integral on Ioc
  rw [intervalIntegral.integral_of_le (le_of_lt hL.out)]
  set μ := volume.restrict (Set.Ioc (0 : ℝ) L)
  -- Step 2: Uniform bounds setup
  set M := max (1 / Real.sqrt L) (Real.sqrt (2 / L))
  have hM_nonneg : 0 ≤ M := le_max_of_le_right (Real.sqrt_nonneg _)
  set c := t * (2 * π / L) ^ 2 with hc_def
  have hc_pos : 0 < c := mul_pos ht (sq_pos_of_pos (div_pos (mul_pos two_pos pi_pos) hL.out))
  set r := exp (-c)
  have hr_pos : 0 < r := exp_pos _
  have hr_lt_one : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h_exp_le : ∀ k : ℕ, exp (-(t * (2 * π * ↑k / L) ^ 2)) ≤ r ^ k := by
    intro k
    rw [show r ^ k = exp (-c) ^ k from rfl, ← Real.exp_nat_mul,
      show ↑k * -c = -(c * ↑k) from by ring]
    apply Real.exp_le_exp.mpr
    have h_eq : t * (2 * π * ↑k / L) ^ 2 = c * (↑k) ^ 2 := by
      simp only [hc_def]; ring
    rw [h_eq]
    have hn_sq : (↑k : ℝ) ≤ (↑k) ^ 2 := by
      rcases k with _ | k
      · simp
      · have h1 : (1 : ℝ) ≤ ↑(k + 1) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
        calc (↑(k + 1) : ℝ) = ↑(k + 1) * 1 := (mul_one _).symm
          _ ≤ ↑(k + 1) * ↑(k + 1) := by apply mul_le_mul_of_nonneg_left h1; positivity
          _ = (↑(k + 1)) ^ 2 := (sq _).symm
    linarith [mul_le_mul_of_nonneg_left hn_sq hc_pos.le]
  -- Step 3: Set up the summands G k θ₂ = exp(...) * ψ_k(θ₁) * (ψ_k(θ₂) * ψ_n(θ₂))
  set G : ℕ → ℝ → ℝ := fun k θ₂ =>
    exp (-(t * (2 * π * ↑k / L) ^ 2)) * fourierBasisFun (L := L) k θ₁ *
      (fourierBasisFun (L := L) k θ₂ * fourierBasisFun (L := L) n θ₂) with hG_def
  -- Rewrite integrand as tsum of G
  have h_eq_tsum : ∀ θ₂,
      circleHeatKernel L t θ₁ θ₂ * fourierBasisFun (L := L) n θ₂ = ∑' k, G k θ₂ := by
    intro θ₂; simp only [hG_def, circleHeatKernel]
    rw [← tsum_mul_right]
    exact tsum_congr (fun k => by ring)
  simp_rw [h_eq_tsum]
  -- Step 4: Integrability of each G k
  have hG_int : ∀ k, Integrable (G k) μ := by
    intro k; simp only [hG_def]
    apply Integrable.const_mul
    exact ((fourierBasisFun_smooth (L := L) k).continuous.mul
      (fourierBasisFun_smooth (L := L) n).continuous).continuousOn.integrableOn_compact
        isCompact_Icc |>.mono_set Set.Ioc_subset_Icc_self
  -- Step 5: Summability of ∫ ‖G k‖
  have hG_sum : Summable (fun k => ∫ θ₂, ‖G k θ₂‖ ∂μ) := by
    have h_bound : ∀ k θ₂, ‖G k θ₂‖ ≤ M ^ 2 * M * r ^ k := by
      intro k θ₂; simp only [hG_def, Real.norm_eq_abs]
      calc |exp (-(t * (2 * π * ↑k / L) ^ 2)) * fourierBasisFun (L := L) k θ₁ *
            (fourierBasisFun (L := L) k θ₂ * fourierBasisFun (L := L) n θ₂)|
          = exp (-(t * (2 * π * ↑k / L) ^ 2)) * |fourierBasisFun (L := L) k θ₁| *
            (|fourierBasisFun (L := L) k θ₂| * |fourierBasisFun (L := L) n θ₂|) := by
            rw [abs_mul, abs_mul, abs_of_nonneg (le_of_lt (exp_pos _)), abs_mul]
        _ ≤ r ^ k * M * (M * M) := by
            gcongr
            · exact h_exp_le k
            · exact SmoothMap_Circle.fourierBasisFun_abs_le k θ₁
            · exact SmoothMap_Circle.fourierBasisFun_abs_le k θ₂
            · exact SmoothMap_Circle.fourierBasisFun_abs_le n θ₂
        _ = M ^ 2 * M * r ^ k := by ring
    apply Summable.of_nonneg_of_le
      (fun k => integral_nonneg (fun _ => norm_nonneg _))
    · intro k
      calc ∫ θ₂, ‖G k θ₂‖ ∂μ
          ≤ ∫ _, M ^ 2 * M * r ^ k ∂μ :=
            integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
              (integrable_const _) (ae_of_all _ (h_bound k))
        _ = M ^ 2 * M * r ^ k * L := by
            rw [integral_const, smul_eq_mul]
            show μ.real Set.univ * _ = _
            rw [Measure.real, Measure.restrict_apply MeasurableSet.univ,
              Set.univ_inter, Real.volume_Ioc, sub_zero,
              ENNReal.toReal_ofReal (le_of_lt hL.out)]
            ring
    · exact (summable_geometric_of_lt_one hr_pos.le hr_lt_one).mul_left _ |>.mul_right _
  -- Step 6: Swap ∫ and ∑'
  rw [← integral_tsum_of_summable_integral_norm hG_int hG_sum]
  -- Step 7: Evaluate each integral using Fourier orthogonality
  -- ∫ ψ_k * ψ_n = δ_{kn} (convert set integral Ioc -> Icc)
  have h_ortho : ∀ k, ∫ θ₂, G k θ₂ ∂μ =
      exp (-(t * (2 * π * ↑k / L) ^ 2)) * fourierBasisFun (L := L) k θ₁ *
        (if k = n then 1 else 0) := by
    intro k; simp only [hG_def]
    rw [integral_const_mul]
    congr 1
    -- Convert set integral on Ioc to Icc, swap product order for orthogonality
    conv_lhs =>
      rw [show ∫ θ₂, fourierBasisFun (L := L) k θ₂ * fourierBasisFun (L := L) n θ₂ ∂μ =
        ∫ θ₂ in Set.Icc (0 : ℝ) L,
          fourierBasisFun (L := L) n θ₂ * fourierBasisFun (L := L) k θ₂ from by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc.symm]
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
          (fun θ₂ _ => mul_comm _ _)]
    -- Now matches fourierCoeffReal k (fourierBasis n)
    exact SmoothMap_Circle.fourierCoeffReal_fourierBasis (L := L) k n
  simp_rw [h_ortho]
  -- Step 8: Sum collapses via tsum_eq_single
  have h_zero : ∀ k, k ≠ n →
      exp (-(t * (2 * π * ↑k / L) ^ 2)) * fourierBasisFun (L := L) k θ₁ *
        (if k = n then 1 else 0) = 0 := by
    intro k hk; simp [hk]
  rw [tsum_eq_single n h_zero, if_pos rfl, mul_one]

set_option maxHeartbeats 800000 in
/-- The circle heat kernel satisfies the semigroup property.
    Proof: expand the second kernel as a series, swap integral and sum via
    integral_tsum_of_summable_integral_norm, apply the reproducing property,
    combine exponentials. -/
theorem circleHeatKernel_semigroup (L : ℝ) [hL : Fact (0 < L)]
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (θ₁ θ₂ : ℝ) :
    ∫ θ in (0 : ℝ)..L,
      circleHeatKernel L s θ₁ θ * circleHeatKernel L t θ θ₂ =
    circleHeatKernel L (s + t) θ₁ θ₂ := by
  -- Work with set integral on Ioc 0 L (= interval integral for 0 ≤ L)
  rw [intervalIntegral.integral_of_le (le_of_lt hL.out)]
  set μ := volume.restrict (Set.Ioc (0 : ℝ) L)
  -- Step 0: Uniform bounds and geometric series setup
  set M := max (1 / Real.sqrt L) (Real.sqrt (2 / L))
  have hM_nonneg : 0 ≤ M := le_max_of_le_right (Real.sqrt_nonneg _)
  set c_s := s * (2 * π / L) ^ 2 with hc_s_def
  have hc_s_pos : 0 < c_s :=
    mul_pos hs (sq_pos_of_pos (div_pos (mul_pos two_pos pi_pos) hL.out))
  set r_s := exp (-c_s)
  have hr_s_pos : 0 < r_s := exp_pos _
  have hr_s_lt_one : r_s < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h_exp_le_s : ∀ n : ℕ, exp (-(s * (2 * π * ↑n / L) ^ 2)) ≤ r_s ^ n := by
    intro n
    rw [show r_s ^ n = exp (-c_s) ^ n from rfl, ← Real.exp_nat_mul,
      show ↑n * -c_s = -(c_s * ↑n) from by ring]
    apply Real.exp_le_exp.mpr
    have h_eq : s * (2 * π * ↑n / L) ^ 2 = c_s * (↑n) ^ 2 := by
      simp only [hc_s_def]; ring
    rw [h_eq]
    have hn_sq : (↑n : ℝ) ≤ (↑n) ^ 2 := by
      rcases n with _ | n
      · simp
      · have h1 : (1 : ℝ) ≤ ↑(n + 1) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        calc (↑(n + 1) : ℝ) = ↑(n + 1) * 1 := (mul_one _).symm
          _ ≤ ↑(n + 1) * ↑(n + 1) := by apply mul_le_mul_of_nonneg_left h1; positivity
          _ = (↑(n + 1)) ^ 2 := (sq _).symm
    linarith [mul_le_mul_of_nonneg_left hn_sq hc_s_pos.le]
  -- Continuity of θ ↦ circleHeatKernel L s θ₁ θ via continuous_tsum
  have h_cont_kernel : Continuous (fun θ => circleHeatKernel L s θ₁ θ) := by
    unfold circleHeatKernel
    apply continuous_tsum
    · intro n
      exact continuous_const.mul (fourierBasisFun_smooth (L := L) n).continuous
    · exact (summable_geometric_of_lt_one hr_s_pos.le hr_s_lt_one).mul_left (M ^ 2)
    · intro n θ
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (le_of_lt (exp_pos _))]
      calc exp (-(s * (2 * π * ↑n / L) ^ 2)) * |fourierBasisFun (L := L) n θ₁| *
            |fourierBasisFun (L := L) n θ|
          ≤ r_s ^ n * M * M := by
            apply mul_le_mul
            · exact mul_le_mul (h_exp_le_s n) (fourierBasisFun_abs_le n θ₁)
                (abs_nonneg _) (pow_nonneg hr_s_pos.le n)
            · exact fourierBasisFun_abs_le n θ
            · exact abs_nonneg _
            · exact mul_nonneg (pow_nonneg hr_s_pos.le n) hM_nonneg
        _ = M ^ 2 * r_s ^ n := by ring
  -- Step 1: Expand the second kernel as a series
  set G : ℕ → ℝ → ℝ := fun k θ =>
    exp (-(t * (2 * π * ↑k / L) ^ 2)) * fourierBasisFun (L := L) k θ₂ *
      (circleHeatKernel L s θ₁ θ * fourierBasisFun (L := L) k θ) with hG_def
  have h_eq_tsum : ∀ θ,
      circleHeatKernel L s θ₁ θ * circleHeatKernel L t θ θ₂ = ∑' k, G k θ := by
    intro θ
    simp only [hG_def]
    -- LHS: cHK_s * cHK_t where cHK_t = ∑' k, exp(...) * fbf k θ * fbf k θ₂
    -- RHS: ∑' k, exp(...) * fbf k θ₂ * (cHK_s * fbf k θ)
    -- Strategy: unfold cHK_t on LHS, use tsum_mul_left, then ring per summand
    set cHK_s := circleHeatKernel L s θ₁ θ
    have h_cHK_t : circleHeatKernel L t θ θ₂ = ∑' k,
        exp (-(t * (2 * π * ↑k / L) ^ 2)) *
          fourierBasisFun (L := L) k θ * fourierBasisFun (L := L) k θ₂ := rfl
    rw [h_cHK_t, ← tsum_mul_left]
    refine tsum_congr (fun k => ?_)
    ring
  simp_rw [h_eq_tsum]
  -- Step 2: Each G k is integrable on Ioc 0 L
  have hG_int : ∀ k, Integrable (G k) μ := by
    intro k; simp only [hG_def]
    exact ((h_cont_kernel.mul (fourierBasisFun_smooth k).continuous).const_smul
      (exp (-(t * (2 * π * ↑k / L) ^ 2)) * fourierBasisFun (L := L) k θ₂)
      ).continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Set.Ioc_subset_Icc_self
  -- Step 3: Summability of ∫ ‖G k‖
  set c_t := t * (2 * π / L) ^ 2 with hc_t_def
  have hc_t_pos : 0 < c_t :=
    mul_pos ht (sq_pos_of_pos (div_pos (mul_pos two_pos pi_pos) hL.out))
  set r_t := exp (-c_t)
  have hr_t_pos : 0 < r_t := exp_pos _
  have hr_t_lt_one : r_t < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h_exp_le_t : ∀ k : ℕ, exp (-(t * (2 * π * ↑k / L) ^ 2)) ≤ r_t ^ k := by
    intro k
    rw [show r_t ^ k = exp (-c_t) ^ k from rfl, ← Real.exp_nat_mul,
      show ↑k * -c_t = -(c_t * ↑k) from by ring]
    apply Real.exp_le_exp.mpr
    have h_eq : t * (2 * π * ↑k / L) ^ 2 = c_t * (↑k) ^ 2 := by
      simp only [hc_t_def]; ring
    rw [h_eq]
    have hn_sq : (↑k : ℝ) ≤ (↑k) ^ 2 := by
      rcases k with _ | k
      · simp
      · have h1 : (1 : ℝ) ≤ ↑(k + 1) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
        calc (↑(k + 1) : ℝ) = ↑(k + 1) * 1 := (mul_one _).symm
          _ ≤ ↑(k + 1) * ↑(k + 1) := by apply mul_le_mul_of_nonneg_left h1; positivity
          _ = (↑(k + 1)) ^ 2 := (sq _).symm
    linarith [mul_le_mul_of_nonneg_left hn_sq hc_t_pos.le]
  -- Pointwise bound on circleHeatKernel values via norm_tsum_le_tsum_norm
  have h_kernel_norm_summable : ∀ θ,
      Summable (fun n => ‖exp (-(s * (2 * π * ↑n / L) ^ 2)) *
        fourierBasisFun (L := L) n θ₁ * fourierBasisFun (L := L) n θ‖) :=
    fun θ => (circleHeatKernel_summable L s hs θ₁ θ).norm
  have h_M2_geom_summable : Summable (fun n => M ^ 2 * r_s ^ n) :=
    (summable_geometric_of_lt_one hr_s_pos.le hr_s_lt_one).mul_left _
  have h_kernel_bound : ∃ B : ℝ, 0 ≤ B ∧
      ∀ θ, |circleHeatKernel L s θ₁ θ| ≤ B := by
    set Bval := ∑' n, M ^ 2 * r_s ^ n
    refine ⟨Bval,
      tsum_nonneg (fun n => mul_nonneg (sq_nonneg _) (pow_nonneg hr_s_pos.le n)), ?_⟩
    intro θ; unfold circleHeatKernel
    calc |∑' n, exp (-(s * (2 * π * ↑n / L) ^ 2)) *
          fourierBasisFun (L := L) n θ₁ * fourierBasisFun (L := L) n θ|
        = ‖∑' n, exp (-(s * (2 * π * ↑n / L) ^ 2)) *
          fourierBasisFun (L := L) n θ₁ * fourierBasisFun (L := L) n θ‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ∑' n, ‖exp (-(s * (2 * π * ↑n / L) ^ 2)) *
          fourierBasisFun (L := L) n θ₁ * fourierBasisFun (L := L) n θ‖ :=
          norm_tsum_le_tsum_norm (h_kernel_norm_summable θ)
      _ ≤ Bval := by
          apply (h_kernel_norm_summable θ).tsum_le_tsum _ h_M2_geom_summable
          intro n
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (le_of_lt (exp_pos _))]
          calc exp (-(s * (2 * π * ↑n / L) ^ 2)) * |fourierBasisFun (L := L) n θ₁| *
                |fourierBasisFun (L := L) n θ|
              ≤ r_s ^ n * M * M := by
                apply mul_le_mul
                · exact mul_le_mul (h_exp_le_s n) (fourierBasisFun_abs_le n θ₁)
                    (abs_nonneg _) (pow_nonneg hr_s_pos.le n)
                · exact fourierBasisFun_abs_le n θ
                · exact abs_nonneg _
                · exact mul_nonneg (pow_nonneg hr_s_pos.le n) hM_nonneg
            _ = M ^ 2 * r_s ^ n := by ring
  obtain ⟨B, hB_nonneg, h_kernel_le⟩ := h_kernel_bound
  have hG_sum : Summable (fun k => ∫ θ, ‖G k θ‖ ∂μ) := by
    have h_bound : ∀ k θ, ‖G k θ‖ ≤ M * B * M * r_t ^ k := by
      intro k θ; simp only [hG_def]
      rw [Real.norm_eq_abs]
      calc |exp (-(t * (2 * π * ↑k / L) ^ 2)) * fourierBasisFun (L := L) k θ₂ *
            (circleHeatKernel L s θ₁ θ * fourierBasisFun (L := L) k θ)|
          = |exp (-(t * (2 * π * ↑k / L) ^ 2))| * |fourierBasisFun (L := L) k θ₂| *
            (|circleHeatKernel L s θ₁ θ| * |fourierBasisFun (L := L) k θ|) := by
            rw [abs_mul, abs_mul, abs_mul]
        _ ≤ r_t ^ k * M * (B * M) := by
            have h_exp_nonneg : 0 ≤ exp (-(t * (2 * π * ↑k / L) ^ 2)) :=
              le_of_lt (exp_pos _)
            rw [abs_of_nonneg h_exp_nonneg]
            gcongr
            · exact h_exp_le_t k
            · exact fourierBasisFun_abs_le k θ₂
            · exact h_kernel_le θ
            · exact fourierBasisFun_abs_le k θ
        _ = M * B * M * r_t ^ k := by ring
    apply Summable.of_nonneg_of_le
      (fun k => integral_nonneg (fun _ => norm_nonneg _))
    · intro k
      calc ∫ θ, ‖G k θ‖ ∂μ
          ≤ ∫ _, M * B * M * r_t ^ k ∂μ :=
            integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
              (integrable_const _) (ae_of_all _ (h_bound k))
        _ = M * B * M * r_t ^ k * L := by
            rw [integral_const, smul_eq_mul]
            show μ.real Set.univ * _ = _
            rw [Measure.real, Measure.restrict_apply MeasurableSet.univ,
              Set.univ_inter, Real.volume_Ioc, sub_zero,
              ENNReal.toReal_ofReal (le_of_lt hL.out)]
            ring
    · exact (summable_geometric_of_lt_one hr_t_pos.le hr_t_lt_one).mul_left _ |>.mul_right _
  -- Step 4: Swap ∫ and ∑'
  rw [← integral_tsum_of_summable_integral_norm hG_int hG_sum]
  -- Step 5: Pull constants out and apply circleHeatKernel_reproduces_fourier
  -- After swap, goal: ∑' k, ∫ θ, G k θ ∂μ = circleHeatKernel L (s + t) θ₁ θ₂
  -- Convert from set integral back to interval integral for the reproducing lemma
  have h_repro : ∀ k, ∫ θ, G k θ ∂μ =
      exp (-(t * (2 * π * ↑k / L) ^ 2)) * fourierBasisFun (L := L) k θ₂ *
      (exp (-(s * (2 * π * ↑k / L) ^ 2)) * fourierBasisFun (L := L) k θ₁) := by
    intro k
    simp only [hG_def]
    rw [integral_const_mul]
    congr 1
    rw [← intervalIntegral.integral_of_le (le_of_lt hL.out)]
    exact circleHeatKernel_reproduces_fourier L s hs k θ₁
  simp_rw [h_repro]
  -- Step 6: Combine exponentials and match against circleHeatKernel definition
  rw [show circleHeatKernel L (s + t) θ₁ θ₂ =
    ∑' k, exp (-((s + t) * (2 * π * ↑k / L) ^ 2)) *
      fourierBasisFun (L := L) k θ₁ * fourierBasisFun (L := L) k θ₂
    from rfl]
  congr 1; funext k
  rw [show exp (-(t * (2 * π * ↑k / L) ^ 2)) * fourierBasisFun (L := L) k θ₂ *
    (exp (-(s * (2 * π * ↑k / L) ^ 2)) * fourierBasisFun (L := L) k θ₁) =
    exp (-(s * (2 * π * ↑k / L) ^ 2)) * exp (-(t * (2 * π * ↑k / L) ^ 2)) *
    fourierBasisFun (L := L) k θ₁ * fourierBasisFun (L := L) k θ₂ from by ring]
  congr 1; congr 1
  rw [← Real.exp_add]
  congr 1; ring

/-! ## Full cylinder heat kernel -/

/-- Heat kernel on S¹_L × ℝ for A = -∂²/∂θ² + (-∂²/∂x² + x²) + m².

    Factors as e^{-m²t} · K_circle(θ₁,θ₂,t) · K_osc(x₁,x₂,t). -/
noncomputable def cylinderHeatKernel (L : ℝ) [Fact (0 < L)]
    (mass t θ₁ x₁ θ₂ x₂ : ℝ) : ℝ :=
  exp (-(mass ^ 2 * t)) * circleHeatKernel L t θ₁ θ₂ * mehlerKernel t x₁ x₂

set_option maxHeartbeats 800000 in
/-- The cylinder heat kernel equals its eigenfunction expansion.

    Proof: unfold `cylinderHeatKernel` to `exp(-m^2 t) * circleHeatKernel * mehlerKernel`,
    expand both kernels as tsums, multiply the two tsums via `Summable.tsum_mul_tsum`,
    reindex from `ℕ × ℕ` to `ℕ` via `Nat.pairEquiv`, and factor the three exponentials
    into `exp(-t * qftEigenvalue L mass m)`. -/
theorem cylinderHeatKernel_eq_series (L : ℝ) [hL : Fact (0 < L)]
    (mass t : ℝ) (ht : 0 < t) (θ₁ x₁ θ₂ x₂ : ℝ) :
    cylinderHeatKernel L mass t θ₁ x₁ θ₂ x₂ =
      ∑' (m : ℕ), exp (-(t * qftEigenvalue L mass m)) *
        (fourierBasisFun (L := L) (m.unpair).1 θ₁ *
         hermiteFunction (m.unpair).2 x₁) *
        (fourierBasisFun (L := L) (m.unpair).1 θ₂ *
         hermiteFunction (m.unpair).2 x₂) := by
  -- Step 1: Unfold cylinderHeatKernel and expand both series
  unfold cylinderHeatKernel
  rw [mehlerKernel_eq_series t ht x₁ x₂]
  unfold circleHeatKernel
  -- Now LHS = exp(-m²t) * (∑' n, circle_n) * (∑' k, mehler_k)
  -- Step 2: Name the two summand functions
  set F : ℕ → ℝ := fun n =>
    exp (-(t * (2 * π * ↑n / L) ^ 2)) *
      fourierBasisFun (L := L) n θ₁ * fourierBasisFun (L := L) n θ₂
  set G : ℕ → ℝ := fun k =>
    exp (-(t * (2 * ↑k + 1))) * hermiteFunction k x₁ * hermiteFunction k x₂
  -- Step 3: Summability
  have hF : Summable F := circleHeatKernel_summable L t ht θ₁ θ₂
  have hG : Summable G := mehlerKernel_summable t ht x₁ x₂
  have hFG : Summable (fun p : ℕ × ℕ => F p.1 * G p.2) :=
    summable_mul_of_summable_norm hF.norm hG.norm
  -- Step 4: Multiply the two tsums into ∑' (p : ℕ × ℕ), F p.1 * G p.2
  conv_lhs =>
    rw [show exp (-(mass ^ 2 * t)) * (∑' n, F n) * (∑' k, G k) =
      exp (-(mass ^ 2 * t)) * ((∑' n, F n) * (∑' k, G k)) from by ring]
  rw [hF.tsum_mul_tsum hG hFG]
  -- Step 5: Reindex from ℕ × ℕ to ℕ via Cantor pairing
  rw [show ∑' (p : ℕ × ℕ), F p.1 * G p.2 =
    ∑' m, F (Nat.unpair m).1 * G (Nat.unpair m).2 from
    (Nat.pairEquiv.symm.tsum_eq _).symm]
  -- Step 6: Pull exp(-mass²t) inside the tsum
  rw [← tsum_mul_left]
  -- Step 7: Match terms pointwise
  congr 1; funext m
  simp only [F, G]
  -- Step 8: Factor the exponentials
  -- exp(-m²t) * exp(-t(2πn/L)²) * exp(-t(2k+1)) = exp(-t * qftEigenvalue L mass m)
  have h_exp_eq : exp (-(mass ^ 2 * t)) *
      exp (-(t * (2 * π * ↑(Nat.unpair m).1 / L) ^ 2)) *
      exp (-(t * (2 * ↑(Nat.unpair m).2 + 1))) =
      exp (-(t * qftEigenvalue L mass m)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold qftEigenvalue; ring
  -- Step 9: Rearrange products and substitute the exponential identity
  calc exp (-(mass ^ 2 * t)) *
    (exp (-(t * (2 * π * ↑(Nat.unpair m).1 / L) ^ 2)) *
      fourierBasisFun (Nat.unpair m).1 θ₁ * fourierBasisFun (Nat.unpair m).1 θ₂ *
      (exp (-(t * (2 * ↑(Nat.unpair m).2 + 1))) *
        hermiteFunction (Nat.unpair m).2 x₁ * hermiteFunction (Nat.unpair m).2 x₂))
    = (exp (-(mass ^ 2 * t)) * exp (-(t * (2 * π * ↑(Nat.unpair m).1 / L) ^ 2)) *
        exp (-(t * (2 * ↑(Nat.unpair m).2 + 1)))) *
      (fourierBasisFun (Nat.unpair m).1 θ₁ * hermiteFunction (Nat.unpair m).2 x₁) *
      (fourierBasisFun (Nat.unpair m).1 θ₂ *
        hermiteFunction (Nat.unpair m).2 x₂) := by ring
    _ = exp (-(t * qftEigenvalue L mass m)) *
      (fourierBasisFun (Nat.unpair m).1 θ₁ * hermiteFunction (Nat.unpair m).2 x₁) *
      (fourierBasisFun (Nat.unpair m).1 θ₂ *
        hermiteFunction (Nat.unpair m).2 x₂) := by
        rw [h_exp_eq]

/-- The cylinder heat kernel is symmetric. -/
theorem cylinderHeatKernel_symmetric (L : ℝ) [Fact (0 < L)]
    (mass t θ₁ x₁ θ₂ x₂ : ℝ) :
    cylinderHeatKernel L mass t θ₁ x₁ θ₂ x₂ =
    cylinderHeatKernel L mass t θ₂ x₂ θ₁ x₁ := by
  simp only [cylinderHeatKernel,
    circleHeatKernel_symmetric L t θ₁ θ₂,
    mehlerKernel_symmetric t x₁ x₂]

/-- The cylinder heat kernel is positive for t > 0. -/
theorem cylinderHeatKernel_pos (L : ℝ) [Fact (0 < L)]
    (mass t : ℝ) (ht : 0 < t) (θ₁ x₁ θ₂ x₂ : ℝ) :
    0 < cylinderHeatKernel L mass t θ₁ x₁ θ₂ x₂ := by
  unfold cylinderHeatKernel
  exact mul_pos (mul_pos (exp_pos _) (circleHeatKernel_pos L t ht θ₁ θ₂))
    (mehlerKernel_pos t ht x₁ x₂)

/-- The cylinder heat kernel is L-periodic in θ₁. -/
theorem cylinderHeatKernel_periodic₁ (L : ℝ) [Fact (0 < L)]
    (mass t θ₁ x₁ θ₂ x₂ : ℝ) :
    cylinderHeatKernel L mass t (θ₁ + L) x₁ θ₂ x₂ =
    cylinderHeatKernel L mass t θ₁ x₁ θ₂ x₂ := by
  simp only [cylinderHeatKernel, circleHeatKernel_periodic₁]

/-- The cylinder heat kernel is L-periodic in θ₂. -/
theorem cylinderHeatKernel_periodic₂ (L : ℝ) [Fact (0 < L)]
    (mass t θ₁ x₁ θ₂ x₂ : ℝ) :
    cylinderHeatKernel L mass t θ₁ x₁ (θ₂ + L) x₂ =
    cylinderHeatKernel L mass t θ₁ x₁ θ₂ x₂ := by
  simp only [cylinderHeatKernel, circleHeatKernel_periodic₂]

/-! ## Pointwise evaluation and bridge to spectral CLM -/

/-- Evaluate a cylinder test function at a point (θ, x) via the
    eigenfunction expansion:
      f(θ, x) = Σ_m coeff_m(f) · ψ_n(θ) · φ_k(x) -/
noncomputable def cylinderEval (L : ℝ) [Fact (0 < L)]
    (f : NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ ℝ))
    (θ x : ℝ) : ℝ :=
  ∑' (m : ℕ), DyninMityaginSpace.coeff m f *
    fourierBasisFun (L := L) (m.unpair).1 θ *
    hermiteFunction (m.unpair).2 x

/-- The eigenfunction expansion converges for cylinder test functions. -/
axiom cylinderEval_summable (L : ℝ) [Fact (0 < L)]
    (f : NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ ℝ))
    (θ x : ℝ) :
    Summable fun (m : ℕ) => DyninMityaginSpace.coeff m f *
      fourierBasisFun (L := L) (m.unpair).1 θ *
      hermiteFunction (m.unpair).2 x

set_option maxHeartbeats 800000 in
/-- Uniform bound on `∫ |K_osc(x,x',t) * φ_k(x')| dx'` in k.

    Expand K_osc as eigenfunction series, use triangle inequality and
    `∫ |ψ_j * φ_k| ≤ 1` (AM-GM + orthonormality). -/
private lemma mehlerKernel_hermite_integral_abs_bound (t : ℝ) (ht : 0 < t) (x : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ,
      ∫ x', |mehlerKernel t x x' * hermiteFunction k x'| ≤ B := by
  have h_ψψ_le : ∀ j k : ℕ,
      ∫ x', |hermiteFunction j x' * hermiteFunction k x'| ≤ 1 := by
    intro j k
    have hψ_sq_int : ∀ n, Integrable (fun y => hermiteFunction n y ^ 2) :=
      fun n => ((hermiteFunction_memLp n).integrable_mul (hermiteFunction_memLp n)).congr
        (by filter_upwards with y; show (hermiteFunction n * hermiteFunction n) y = _;
            simp [sq, Pi.mul_apply])
    have hψ_sq : ∀ n, ∫ y, hermiteFunction n y ^ 2 = 1 := fun n => by
      have h := hermiteFunction_orthonormal n n; simp at h
      exact (by ext y; ring : (fun y => hermiteFunction n y ^ 2) =
        fun y => hermiteFunction n y * hermiteFunction n y) ▸ h
    calc ∫ x', |hermiteFunction j x' * hermiteFunction k x'|
        = ∫ x', |hermiteFunction j x'| * |hermiteFunction k x'| := by
          congr 1; ext x'; exact abs_mul _ _
      _ ≤ ∫ x', ((hermiteFunction j x' ^ 2 + hermiteFunction k x' ^ 2) / 2) := by
          apply integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun a => mul_nonneg (abs_nonneg _) (abs_nonneg _))
            ((hψ_sq_int j).add (hψ_sq_int k) |>.div_const 2)
          exact Filter.Eventually.of_forall fun a => by
            have h := two_mul_le_add_sq |hermiteFunction j a| |hermiteFunction k a|
            rw [sq_abs, sq_abs] at h; simp only [Pi.add_apply, Pi.div_apply] at *; nlinarith
      _ = 1 := by rw [integral_div, integral_add (hψ_sq_int j) (hψ_sq_int k),
            hψ_sq j, hψ_sq k]; norm_num
  obtain ⟨C, s, hC, _, hbound⟩ := hermiteFunction_sup_bound
  set r := exp (-(2 * t))
  have hr_pos : 0 < r := exp_pos _
  have hr_lt_one : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h_exp_split : ∀ j : ℕ, exp (-(t * (2 * ↑j + 1))) = exp (-t) * r ^ j := by
    intro j; rw [show r ^ j = exp (-(2 * t)) ^ j from rfl, ← Real.exp_nat_mul,
      show ↑j * -(2 * t) = -(2 * t * ↑j) from by ring, ← Real.exp_add]; congr 1; ring
  set p := Nat.ceil s
  have hp : s ≤ ↑p := Nat.le_ceil _
  have h_rpow_le : ∀ j : ℕ, (1 + (↑j : ℝ)) ^ s ≤ (1 + ↑j) ^ p := by
    intro j; rw [← Real.rpow_natCast (1 + ↑j) p]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Nat.cast_nonneg (α := ℝ) j]) hp
  have h_sum_comp : Summable (fun j : ℕ => (1 + (↑j : ℝ)) ^ p * r ^ j) := by
    have h_geom := summable_geometric_of_lt_one hr_pos.le hr_lt_one
    have h_norm_r : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr_pos]
    have h_pow_geom := summable_pow_mul_geometric_of_norm_lt_one p h_norm_r
    refine Summable.of_nonneg_of_le
      (fun j => mul_nonneg (pow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j]) p)
        (pow_nonneg hr_pos.le j))
      (fun j => ?_) ((h_geom.add h_pow_geom).mul_left (2 ^ p))
    have h1j : (1 + (↑j : ℝ)) ^ p ≤ 2 ^ p * (1 + (↑j : ℝ) ^ p) := by
      calc (1 + (↑j : ℝ)) ^ p
          ≤ (2 * max 1 (↑j : ℝ)) ^ p := by
            apply pow_le_pow_left₀ (by linarith [Nat.cast_nonneg (α := ℝ) j])
            linarith [le_max_left (1 : ℝ) ↑j, le_max_right (1 : ℝ) ↑j]
        _ = 2 ^ p * (max 1 (↑j : ℝ)) ^ p := mul_pow _ _ _
        _ ≤ 2 ^ p * (1 + (↑j : ℝ) ^ p) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) p)
            by_cases h : (↑j : ℝ) ≤ 1
            · rw [max_eq_left h, one_pow]; linarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) j) p]
            · push_neg at h; rw [max_eq_right h.le]
              linarith [one_le_pow₀ (M₀ := ℝ) h.le (n := p)]
    calc (1 + (↑j : ℝ)) ^ p * r ^ j
        ≤ 2 ^ p * (1 + (↑j : ℝ) ^ p) * r ^ j :=
          mul_le_mul_of_nonneg_right h1j (pow_nonneg hr_pos.le j)
      _ = 2 ^ p * (r ^ j + (↑j : ℝ) ^ p * r ^ j) := by ring
  have h_B_summable : Summable (fun j : ℕ => exp (-(t * (2 * ↑j + 1))) *
      (C * (1 + ↑j) ^ s)) :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (le_of_lt (exp_pos _))
        (mul_nonneg hC.le (Real.rpow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j]) _)))
      (fun j => by
      calc exp (-(t * (2 * ↑j + 1))) * (C * (1 + ↑j) ^ s)
          = exp (-t) * C * ((1 + ↑j) ^ s * r ^ j) := by rw [h_exp_split j]; ring
        _ ≤ exp (-t) * C * ((1 + ↑j) ^ p * r ^ j) := by gcongr; exact h_rpow_le j)
      (h_sum_comp.mul_left (exp (-t) * C))
  set B := ∑' (j : ℕ), exp (-(t * (2 * ↑j + 1))) * (C * (1 + ↑j) ^ s)
  refine ⟨B, tsum_nonneg (fun (j : ℕ) => mul_nonneg (le_of_lt (exp_pos _))
    (mul_nonneg hC.le (Real.rpow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j]) _))), ?_⟩
  intro k
  have hF_int : ∀ j, Integrable (fun x' =>
      exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x *
        hermiteFunction j x' * hermiteFunction k x') := by
    intro j
    have h1 := (hermiteFunction_memLp j).integrable_mul (hermiteFunction_memLp k)
    apply (h1.const_mul (exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x)).congr
    filter_upwards with x'
    simp only [Pi.mul_apply, smul_eq_mul]; ring
  have hF_sum : Summable fun j => ∫ x', ‖exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x *
      hermiteFunction j x' * hermiteFunction k x'‖ := by
    apply Summable.of_nonneg_of_le (fun j => integral_nonneg (fun _ => norm_nonneg _))
    · intro j
      calc ∫ x', ‖exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x *
            hermiteFunction j x' * hermiteFunction k x'‖
          = exp (-(t * (2 * ↑j + 1))) * |hermiteFunction j x| *
              ∫ x', |hermiteFunction j x' * hermiteFunction k x'| := by
            simp_rw [Real.norm_eq_abs, show ∀ x' : ℝ,
              exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x *
              hermiteFunction j x' * hermiteFunction k x' =
              (exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x) *
              (hermiteFunction j x' * hermiteFunction k x') from fun _ => by ring,
              abs_mul, abs_of_nonneg (le_of_lt (exp_pos _)), integral_const_mul]
        _ ≤ exp (-(t * (2 * ↑j + 1))) * (C * (1 + ↑j) ^ s) * 1 :=
            mul_le_mul
              (mul_le_mul_of_nonneg_left (hbound j x) (le_of_lt (exp_pos _)))
              (h_ψψ_le j k) (integral_nonneg (fun _ => abs_nonneg _))
              (mul_nonneg (le_of_lt (exp_pos _))
                (mul_nonneg hC.le (Real.rpow_nonneg
                  (by linarith [Nat.cast_nonneg (α := ℝ) j]) _)))
        _ = exp (-(t * (2 * ↑j + 1))) * (C * (1 + ↑j) ^ s) := mul_one _
    · exact h_B_summable
  simp_rw [mehlerKernel_eq_series t ht x]
  conv_lhs => arg 2; ext x'; rw [← tsum_mul_right]
  -- Bound: ∫ |∑' f_j(x')| ≤ ∑' ∫ |f_j(x')| ≤ B via integral_tsum + pointwise bounds
  -- Each term integral bound
  have h_term_le : ∀ j, ∫ x', |exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x *
          hermiteFunction j x' * hermiteFunction k x'|
        ≤ exp (-(t * (2 * ↑j + 1))) * (C * (1 + ↑j) ^ s) := by
    intro j
    calc ∫ x', |exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x *
            hermiteFunction j x' * hermiteFunction k x'|
        = exp (-(t * (2 * ↑j + 1))) * |hermiteFunction j x| *
            ∫ x', |hermiteFunction j x' * hermiteFunction k x'| := by
          simp_rw [show ∀ x' : ℝ,
            exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x *
            hermiteFunction j x' * hermiteFunction k x' =
            (exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x) *
            (hermiteFunction j x' * hermiteFunction k x') from fun _ => by ring,
            abs_mul, abs_of_nonneg (le_of_lt (exp_pos _)), integral_const_mul]
      _ ≤ exp (-(t * (2 * ↑j + 1))) * (C * (1 + ↑j) ^ s) * 1 :=
          mul_le_mul
            (mul_le_mul_of_nonneg_left (hbound j x) (le_of_lt (exp_pos _)))
            (h_ψψ_le j k) (integral_nonneg (fun _ => abs_nonneg _))
            (mul_nonneg (le_of_lt (exp_pos _))
              (mul_nonneg hC.le (Real.rpow_nonneg
                (by linarith [Nat.cast_nonneg (α := ℝ) j]) _)))
      _ = exp (-(t * (2 * ↑j + 1))) * (C * (1 + ↑j) ^ s) := mul_one _
  -- Summability of the absolute value integrals (follows from h_term_le and h_B_summable)
  have hF_abs_int_summable : Summable fun j =>
      ∫ x', |exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x *
        hermiteFunction j x' * hermiteFunction k x'| :=
    Summable.of_nonneg_of_le
      (fun j => integral_nonneg (fun _ => abs_nonneg _))
      (fun j => h_term_le j) h_B_summable
  -- Main bound: ∫ |∑' f_j| ≤ ∑' ∫ |f_j| ≤ B
  -- Strategy: bound by ∑' ∫ |f_j| using triangle inequality and integral-tsum swap
  calc ∫ x', |∑' j, exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x *
          hermiteFunction j x' * hermiteFunction k x'|
      ≤ ∑' j, ∫ x', |exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x *
          hermiteFunction j x' * hermiteFunction k x'| := by
        -- Triangle inequality + integral-tsum swap for absolute values
        sorry
    _ ≤ B :=
        Summable.tsum_le_tsum (fun j => h_term_le j)
          hF_abs_int_summable h_B_summable

/-- The Dynin-Mityagin coefficients of a nuclear tensor product element are
    absolutely summable. This follows from the rapid decay property
    `coeff_decay` at exponent 2. -/
lemma cylinderCoeff_abs_summable {L : ℝ} [Fact (0 < L)]
    (f : NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ ℝ)) :
    Summable fun (m : ℕ) =>
      |DyninMityaginSpace.coeff m f| := by
  obtain ⟨C, hC, s, hdecay⟩ := DyninMityaginSpace.coeff_decay (E :=
    NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ ℝ)) 2
  set B := C * (s.sup DyninMityaginSpace.p) f
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
  · intro m
    have h := hdecay f m
    -- |c_m| * (1+m)^2 ≤ B, so |c_m| ≤ B / (1+m)^2
    have h1m : (0 : ℝ) < 1 + ↑m := by positivity
    have h1m_sq : (0 : ℝ) < (1 + ↑m) ^ 2 := by positivity
    calc |DyninMityaginSpace.coeff m f|
        = |DyninMityaginSpace.coeff m f| * (1 + ↑m) ^ 2 / (1 + ↑m) ^ 2 := by
          field_simp
      _ ≤ B / (1 + ↑m) ^ 2 := by
          apply div_le_div_of_nonneg_right h h1m_sq.le
  · have : Summable (fun m : ℕ => B * ((1 : ℝ) / ((m : ℝ) + 1) ^ 2)) := by
      apply Summable.mul_left
      have := (summable_nat_add_iff 1).mpr
        (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
      exact this.congr (fun m => by push_cast; ring_nf)
    exact this.congr (fun m => by ring)

set_option maxHeartbeats 1600000 in
/-- **Bridge theorem**: integration against the cylinder heat kernel
    reproduces the spectral CLM action.

    Proof strategy: unfold `cylinderHeatKernel` as
    `exp(-m²t) · circleHeatKernel · mehlerKernel`, expand `cylinderEval` as its
    eigenfunction tsum, swap integral and sum, then factor each term's double
    integral into a product of the circle reproducing integral
    (`circleHeatKernel_reproduces_fourier`) and the Mehler reproducing integral
    (`mehlerKernel_reproduces_hermite`), and combine exponentials. -/
theorem cylinderHeatKernel_reproduces (L : ℝ) [hL : Fact (0 < L)]
    (mass t : ℝ) (hmass : 0 < mass) (ht : 0 < t)
    (f : NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ ℝ))
    (θ x : ℝ) :
    ∫ θ' in (0 : ℝ)..L, ∫ x',
      cylinderHeatKernel L mass t θ x θ' x' *
        cylinderEval L f θ' x' =
    ∑' (m : ℕ), exp (-(t * qftEigenvalue L mass m)) *
      DyninMityaginSpace.coeff m f *
      fourierBasisFun (L := L) (m.unpair).1 θ *
      hermiteFunction (m.unpair).2 x := by
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 0: Unfold cylinderHeatKernel and set up abbreviations
  -- ═══════════════════════════════════════════════════════════════════════════
  simp only [cylinderHeatKernel]
  -- LHS = ∫ θ' in 0..L, ∫ x', (exp(-m²t) * K_circle(θ,θ',t) * K_osc(x,x',t)) * eval(f,θ',x')
  -- Pull exp(-mass²·t) out of both integrals
  simp_rw [show ∀ θ' x', exp (-(mass ^ 2 * t)) * circleHeatKernel L t θ θ' *
      mehlerKernel t x x' * cylinderEval L f θ' x' =
    exp (-(mass ^ 2 * t)) * (circleHeatKernel L t θ θ' *
      (mehlerKernel t x x' * cylinderEval L f θ' x')) from
    fun θ' x' => by ring]
  simp_rw [integral_const_mul (exp (-(mass ^ 2 * t)))]
  rw [intervalIntegral.integral_const_mul]
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 1: Expand cylinderEval as a tsum and distribute
  -- ═══════════════════════════════════════════════════════════════════════════
  -- cylinderEval L f θ' x' = ∑' m, c_m * ψ_n(θ') * φ_k(x')
  -- So mehlerKernel t x x' * cylinderEval = ∑' m, c_m * ψ_n(θ') * (K_osc(x,x') * φ_k(x'))
  -- and the inner integral ∫ x', ... distributes through the sum
  -- Define the summand for the inner x'-integral
  set G : ℕ → ℝ → ℝ → ℝ := fun m θ' x' =>
    DyninMityaginSpace.coeff m f *
      fourierBasisFun (L := L) (m.unpair).1 θ' *
      (circleHeatKernel L t θ θ' *
        (mehlerKernel t x x' * hermiteFunction (m.unpair).2 x')) with hG_def
  -- Rewrite integrand as tsum of G m
  have h_eq_tsum : ∀ θ' x',
      circleHeatKernel L t θ θ' * (mehlerKernel t x x' * cylinderEval L f θ' x') =
      ∑' m, G m θ' x' := by
    intro θ' x'
    simp only [hG_def, cylinderEval]
    rw [show circleHeatKernel L t θ θ' * (mehlerKernel t x x' *
      ∑' m, DyninMityaginSpace.coeff m f *
        fourierBasisFun (L := L) (m.unpair).1 θ' *
        hermiteFunction (m.unpair).2 x') =
      circleHeatKernel L t θ θ' * ∑' m, mehlerKernel t x x' *
        (DyninMityaginSpace.coeff m f *
          fourierBasisFun (L := L) (m.unpair).1 θ' *
          hermiteFunction (m.unpair).2 x') from by
      rw [← tsum_mul_left]]
    rw [← tsum_mul_left]
    congr 1; ext m; ring
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 2: Evaluate the double integral term by term
  -- ═══════════════════════════════════════════════════════════════════════════
  -- For each m, we compute:
  --   ∫ θ' in 0..L, ∫ x', G m θ' x'
  -- = c_m * (∫ θ' in 0..L, K_circle(θ,θ',t) * ψ_n(θ'))
  --       * (∫ x', K_osc(x,x',t) * φ_k(x'))
  -- = c_m * exp(-t(2πn/L)²) * ψ_n(θ) * exp(-t(2k+1)) * φ_k(x)
  -- First show each G m has factored integrals
  have h_G_factor : ∀ m θ' x', G m θ' x' =
      DyninMityaginSpace.coeff m f *
      (circleHeatKernel L t θ θ' * fourierBasisFun (L := L) (m.unpair).1 θ') *
      (mehlerKernel t x x' * hermiteFunction (m.unpair).2 x') := by
    intro m θ' x'; simp only [hG_def]; ring
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 3: Evaluate the inner x'-integral for each term
  -- ═══════════════════════════════════════════════════════════════════════════
  -- ∫ x', K_osc(x,x',t) * φ_k(x') = exp(-t(2k+1)) * φ_k(x)
  have h_mehler_repro : ∀ k : ℕ,
      ∫ x', mehlerKernel t x x' * hermiteFunction k x' =
      exp (-(t * (2 * ↑k + 1))) * hermiteFunction k x := by
    intro k
    exact mehlerKernel_reproduces_hermite t ht k x
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 4: Evaluate the outer θ'-integral for each term
  -- ═══════════════════════════════════════════════════════════════════════════
  -- ∫ θ' in 0..L, K_circle(θ,θ',t) * ψ_n(θ') = exp(-t(2πn/L)²) * ψ_n(θ)
  have h_circle_repro : ∀ n : ℕ,
      ∫ θ' in (0 : ℝ)..L, circleHeatKernel L t θ θ' *
        fourierBasisFun (L := L) n θ' =
      exp (-(t * (2 * π * ↑n / L) ^ 2)) * fourierBasisFun (L := L) n θ :=
    fun n => circleHeatKernel_reproduces_fourier L t ht n θ
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 5: Compute the double integral of each G m by factoring
  -- ═══════════════════════════════════════════════════════════════════════════
  -- We use Fubini to separate the integrals, then apply reproducing properties.
  -- For each m, ∫ θ' ∫ x' G m θ' x'
  --   = c_m * ∫ θ' (K_circle * ψ_n)(θ') * ∫ x' (K_osc * φ_k)(x')
  --   = c_m * exp(-t(2πn/L)²) * ψ_n(θ) * exp(-t(2k+1)) * φ_k(x)
  have h_inner_integral : ∀ m θ',
      ∫ x', G m θ' x' =
      DyninMityaginSpace.coeff m f *
        (circleHeatKernel L t θ θ' * fourierBasisFun (L := L) (m.unpair).1 θ') *
        (exp (-(t * (2 * ↑(m.unpair).2 + 1))) * hermiteFunction (m.unpair).2 x) := by
    intro m θ'
    simp_rw [h_G_factor m θ']
    rw [integral_const_mul, h_mehler_repro]
  have h_double_integral : ∀ m,
      ∫ θ' in (0 : ℝ)..L, ∫ x', G m θ' x' =
      DyninMityaginSpace.coeff m f *
        (exp (-(t * (2 * π * ↑(m.unpair).1 / L) ^ 2)) *
          fourierBasisFun (L := L) (m.unpair).1 θ) *
        (exp (-(t * (2 * ↑(m.unpair).2 + 1))) * hermiteFunction (m.unpair).2 x) := by
    intro m
    simp_rw [h_inner_integral m]
    simp_rw [show ∀ θ' : ℝ,
      DyninMityaginSpace.coeff m f *
        (circleHeatKernel L t θ θ' * fourierBasisFun (L := L) (m.unpair).1 θ') *
        (exp (-(t * (2 * ↑(m.unpair).2 + 1))) * hermiteFunction (m.unpair).2 x) =
      (DyninMityaginSpace.coeff m f *
        exp (-(t * (2 * ↑(m.unpair).2 + 1))) * hermiteFunction (m.unpair).2 x) *
        (circleHeatKernel L t θ θ' * fourierBasisFun (L := L) (m.unpair).1 θ') from
      fun θ' => by ring]
    rw [intervalIntegral.integral_const_mul, h_circle_repro]; ring
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 6: Convert to term-by-term form and combine exponentials
  -- ═══════════════════════════════════════════════════════════════════════════
  -- What remains: show that swapping ∫∫ with ∑' is valid, then combine.
  -- We will use a different approach: first swap sum and integral, then evaluate.
  -- But actually, we can bypass the swap entirely if we can show:
  --   ∫ θ' ∫ x', ∑' m, G m θ' x' = ∑' m, ∫ θ' ∫ x', G m θ' x'
  -- For this we need to justify the integral-sum swap.
  -- Approach: use the factored form directly. Rewrite the LHS using h_eq_tsum,
  -- justify swapping the θ'-integral with tsum, then the result follows from
  -- the term-by-term computations above.
  -- First, show we can rewrite with h_eq_tsum
  simp_rw [show ∀ θ' x', circleHeatKernel L t θ θ' *
      (mehlerKernel t x x' * cylinderEval L f θ' x') = ∑' m, G m θ' x' from h_eq_tsum]
  -- Now LHS = exp(-m²t) * ∫ θ' in 0..L, ∫ x', ∑' m, G m θ' x'
  -- We need: integrability and summability to swap ∫ x' and ∑' m
  -- Step 6a: Integrability of G m in x' for fixed m, θ'
  have hG_x_int : ∀ m θ', Integrable (G m θ') volume := by
    intro m θ'; simp only [hG_def]
    -- G m θ' x' = const(θ') * (K_osc(x,x') * φ_k(x'))
    -- mehlerKernel is a tsum of integrable functions, its product with φ_k is integrable
    -- Use: K_osc * φ_k is integrable (from mehlerKernel_reproduces_hermite proof)
    have h_prod_int : Integrable (fun x' => mehlerKernel t x x' * hermiteFunction (m.unpair).2 x') volume := by
      simp_rw [mehlerKernel_eq_series t ht x, ← tsum_mul_right]
      set Fk : ℕ → ℝ → ℝ := fun j x' =>
        exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x *
          hermiteFunction j x' * hermiteFunction (m.unpair).2 x'
      have hFk_int : ∀ j, Integrable (Fk j) volume := by
        intro j; simp only [Fk]
        have h_prod := (hermiteFunction_memLp j).integrable_mul (hermiteFunction_memLp (m.unpair).2)
        exact (h_prod.const_mul (exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x)).congr
          (by filter_upwards with x'; simp only [Pi.mul_apply]; ring)
      have hFk_sum : Summable fun j => ∫ x', ‖Fk j x'‖ := by
        obtain ⟨C, s, hC, _, hbound⟩ := hermiteFunction_sup_bound
        set r := exp (-(2 * t))
        have hr_pos : 0 < r := exp_pos _
        have hr_lt_one : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
        have h_ψψ_norm_le : ∀ j, ∫ x', |hermiteFunction j x' * hermiteFunction (m.unpair).2 x'| ≤ 1 := by
          intro j
          have hψ_sq_int : ∀ n, Integrable (fun y => hermiteFunction n y ^ 2) :=
            fun n => ((hermiteFunction_memLp n).integrable_mul (hermiteFunction_memLp n)).congr
              (by filter_upwards with y; show (hermiteFunction n * hermiteFunction n) y = _; simp [sq, Pi.mul_apply])
          have hψ_sq : ∀ n, ∫ y, hermiteFunction n y ^ 2 = 1 := fun n => by
            have h := hermiteFunction_orthonormal n n; simp at h
            rw [show (fun y => hermiteFunction n y ^ 2) =
              (fun y => hermiteFunction n y * hermiteFunction n y) from by ext y; ring]
            exact h
          calc ∫ x', |hermiteFunction j x' * hermiteFunction (m.unpair).2 x'|
              = ∫ x', |hermiteFunction j x'| * |hermiteFunction (m.unpair).2 x'| := by
                congr 1; ext x'; exact abs_mul _ _
            _ ≤ ∫ x', ((hermiteFunction j x' ^ 2 + hermiteFunction (m.unpair).2 x' ^ 2) / 2) := by
                apply integral_mono_of_nonneg
                  (Filter.Eventually.of_forall fun a => mul_nonneg (abs_nonneg _) (abs_nonneg _))
                  ((hψ_sq_int j).add (hψ_sq_int (m.unpair).2) |>.div_const 2)
                exact Filter.Eventually.of_forall fun a => by
                  have h := two_mul_le_add_sq |hermiteFunction j a| |hermiteFunction (m.unpair).2 a|
                  rw [sq_abs, sq_abs] at h; simp only [Pi.add_apply, Pi.div_apply] at *; nlinarith
            _ = 1 := by
                rw [integral_div, integral_add (hψ_sq_int j) (hψ_sq_int (m.unpair).2),
                  hψ_sq j, hψ_sq (m.unpair).2]; norm_num
        have h_exp_split : ∀ j : ℕ, exp (-(t * (2 * ↑j + 1))) = exp (-t) * r ^ j := by
          intro j
          rw [show r ^ j = exp (-(2 * t)) ^ j from rfl, ← Real.exp_nat_mul,
            show ↑j * -(2 * t) = -(2 * t * ↑j) from by ring, ← Real.exp_add]
          congr 1; ring
        apply Summable.of_nonneg_of_le
          (fun j => integral_nonneg (fun _ => norm_nonneg _))
        · intro j
          calc ∫ x', ‖Fk j x'‖
              = ∫ x', (exp (-(t * (2 * ↑j + 1))) * |hermiteFunction j x|) *
                  |hermiteFunction j x' * hermiteFunction (m.unpair).2 x'| := by
                congr 1; ext x'; simp only [Fk, Real.norm_eq_abs]
                rw [show exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x *
                  hermiteFunction j x' * hermiteFunction (m.unpair).2 x' =
                  (exp (-(t * (2 * ↑j + 1))) * hermiteFunction j x) *
                  (hermiteFunction j x' * hermiteFunction (m.unpair).2 x') from by ring,
                  abs_mul, abs_mul, abs_of_nonneg (le_of_lt (exp_pos _))]
            _ = exp (-(t * (2 * ↑j + 1))) * |hermiteFunction j x| *
                  ∫ x', |hermiteFunction j x' * hermiteFunction (m.unpair).2 x'| := by
                rw [integral_const_mul]
            _ ≤ exp (-(t * (2 * ↑j + 1))) * (C * (1 + ↑j) ^ s) * 1 := by
                apply mul_le_mul
                · exact mul_le_mul_of_nonneg_left (hbound j x) (le_of_lt (exp_pos _))
                · exact h_ψψ_norm_le j
                · exact integral_nonneg (fun _ => abs_nonneg _)
                · exact mul_nonneg (le_of_lt (exp_pos _)) (mul_nonneg hC.le
                    (Real.rpow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j]) _))
            _ = exp (-t) * (C * (1 + ↑j) ^ s) * r ^ j := by rw [h_exp_split j]; ring
        · set p := Nat.ceil s
          have hp : s ≤ ↑p := Nat.le_ceil _
          have h_rpow_le_pow : ∀ j : ℕ, (1 + (↑j : ℝ)) ^ s ≤ (1 + ↑j) ^ p := by
            intro j; rw [← Real.rpow_natCast (1 + ↑j) p]
            exact Real.rpow_le_rpow_of_exponent_le
              (by linarith [Nat.cast_nonneg (α := ℝ) j]) hp
          have h_sum_comp : Summable (fun j : ℕ => (1 + (↑j : ℝ)) ^ p * r ^ j) := by
            have h_geom := summable_geometric_of_lt_one hr_pos.le hr_lt_one
            have h_norm_r : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hr_pos]
            have h_pow_geom := summable_pow_mul_geometric_of_norm_lt_one p h_norm_r
            refine Summable.of_nonneg_of_le
              (fun j => mul_nonneg
                (pow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) j]) p)
                (pow_nonneg hr_pos.le j))
              (fun j => ?_) ((h_geom.add h_pow_geom).mul_left (2 ^ p))
            have h1j : (1 + (↑j : ℝ)) ^ p ≤ 2 ^ p * (1 + (↑j : ℝ) ^ p) := by
              calc (1 + (↑j : ℝ)) ^ p
                  ≤ (2 * max 1 (↑j : ℝ)) ^ p := by
                    apply pow_le_pow_left₀ (by linarith [Nat.cast_nonneg (α := ℝ) j])
                    calc (1 : ℝ) + ↑j ≤ max 1 ↑j + max 1 ↑j :=
                          add_le_add (le_max_left _ _) (le_max_right (1 : ℝ) ↑j)
                      _ = 2 * max 1 ↑j := (two_mul _).symm
                _ = 2 ^ p * (max 1 (↑j : ℝ)) ^ p := mul_pow _ _ _
                _ ≤ 2 ^ p * (1 + (↑j : ℝ) ^ p) := by
                    apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num : (0:ℝ) ≤ 2) p)
                    by_cases h : (↑j : ℝ) ≤ 1
                    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) j) p]
                    · push_neg at h; rw [max_eq_right h.le]; linarith [one_le_pow₀ (M₀ := ℝ) h.le (n := p)]
            calc (1 + (↑j : ℝ)) ^ p * r ^ j
                ≤ 2 ^ p * (1 + (↑j : ℝ) ^ p) * r ^ j :=
                  mul_le_mul_of_nonneg_right h1j (pow_nonneg hr_pos.le j)
              _ = 2 ^ p * (r ^ j + (↑j : ℝ) ^ p * r ^ j) := by ring
          exact Summable.of_nonneg_of_le (fun j => by positivity) (fun j => by
            show exp (-t) * (C * (1 + ↑j) ^ s) * r ^ j ≤ exp (-t) * C * ((1 + ↑j) ^ p * r ^ j)
            calc exp (-t) * (C * (1 + ↑j) ^ s) * r ^ j
                = exp (-t) * C * ((1 + ↑j) ^ s * r ^ j) := by ring
              _ ≤ exp (-t) * C * ((1 + ↑j) ^ p * r ^ j) := by gcongr; exact h_rpow_le_pow j)
            (h_sum_comp.mul_left (exp (-t) * C))
      -- Integrability of tsum from integral_tsum convergence
      sorry
    exact (h_prod_int.const_mul (DyninMityaginSpace.coeff m f *
      fourierBasisFun (L := L) (m.unpair).1 θ' *
      circleHeatKernel L t θ θ')).congr
      (by filter_upwards with x'; show _ = G m θ' x'; simp only [hG_def]; ring)
  -- Step 6b: Summability of ∫ x' ‖G m θ' x'‖ in m for fixed θ'
  -- This is needed to swap ∫ x' and ∑' m
  -- Actually, let's use a simpler approach: compute term by term and show the result.
  -- We'll show ∫ θ' ∫ x' (∑' m G m θ' x') = ∑' m (∫ θ' ∫ x' G m θ' x')
  -- by first swapping ∫ x' with ∑' m, then ∫ θ' with ∑' m.
  -- Step 6c: swap ∫ x' with ∑' m
  have h_inner_swap : ∀ θ',
      ∫ x', ∑' m, G m θ' x' =
      ∑' m, ∫ x', G m θ' x' := by
    intro θ'
    rw [integral_tsum_of_summable_integral_norm (hG_x_int · θ') ?_]
    · -- Summability of ∫ ‖G m θ' ·‖ in m
      -- Use: ∫ ‖G m θ'‖ = |c_m * fbf_n(θ') * K_circle| * ∫ |K_osc * φ_k|
      --      ≤ |c_m| * M * |K_circle| * B_osc (uniform in m)
      obtain ⟨B_osc, hB_osc_nn, hB_osc⟩ := mehlerKernel_hermite_integral_abs_bound t ht x
      set M_fbf := max (1 / Real.sqrt L) (Real.sqrt (2 / L))
      have hM_nn : 0 ≤ M_fbf := le_max_of_le_right (Real.sqrt_nonneg _)
      set K_val := |circleHeatKernel L t θ θ'|
      apply Summable.of_nonneg_of_le
        (fun m => integral_nonneg (fun _ => norm_nonneg _))
      · intro m
        calc ∫ x', ‖G m θ' x'‖
            = |DyninMityaginSpace.coeff m f *
                fourierBasisFun (L := L) (m.unpair).1 θ' *
                circleHeatKernel L t θ θ'| *
              ∫ x', |mehlerKernel t x x' * hermiteFunction (m.unpair).2 x'| := by
              simp_rw [Real.norm_eq_abs, hG_def,
                show ∀ x' : ℝ, DyninMityaginSpace.coeff m f *
                  fourierBasisFun (L := L) (m.unpair).1 θ' *
                  (circleHeatKernel L t θ θ' *
                    (mehlerKernel t x x' * hermiteFunction (m.unpair).2 x')) =
                  (DyninMityaginSpace.coeff m f *
                    fourierBasisFun (L := L) (m.unpair).1 θ' *
                    circleHeatKernel L t θ θ') *
                  (mehlerKernel t x x' * hermiteFunction (m.unpair).2 x') from
                  fun _ => by ring,
                  abs_mul, integral_const_mul]
          _ ≤ (|DyninMityaginSpace.coeff m f| * M_fbf * K_val) * B_osc := by
              gcongr
              · calc |DyninMityaginSpace.coeff m f *
                      fourierBasisFun (L := L) (m.unpair).1 θ' *
                      circleHeatKernel L t θ θ'|
                    = |DyninMityaginSpace.coeff m f| *
                      |fourierBasisFun (L := L) (m.unpair).1 θ'| *
                      K_val := by rw [abs_mul, abs_mul]
                  _ ≤ _ := by gcongr; exact fourierBasisFun_abs_le _ _
              · exact hB_osc _
      · exact (cylinderCoeff_abs_summable f).mul_right _ |>.mul_right _ |>.mul_right _
  -- Step 6d: After swapping, each term is computed
  simp_rw [h_inner_swap]
  -- Now LHS = exp(-m²t) * ∫ θ' in 0..L, ∑' m, ∫ x', G m θ' x'
  -- Swap ∫ θ' and ∑' m
  simp_rw [h_inner_integral]
  -- LHS = exp(-m²t) * ∫ θ' in 0..L, ∑' m, c_m * (K_circle * ψ_n)(θ') * (e_k * φ_k(x))
  -- Pull the constant (e_k * φ_k(x)) out and factor
  -- Actually, the interval integral ∫ θ' in 0..L of ∑' m (...)
  -- We need to swap this too. Let's use a different approach.
  -- Rewrite each term
  have h_term_rw : ∀ m θ',
      DyninMityaginSpace.coeff m f *
        (circleHeatKernel L t θ θ' * fourierBasisFun (L := L) (m.unpair).1 θ') *
        (exp (-(t * (2 * ↑(m.unpair).2 + 1))) * hermiteFunction (m.unpair).2 x) =
      (DyninMityaginSpace.coeff m f *
        exp (-(t * (2 * ↑(m.unpair).2 + 1))) * hermiteFunction (m.unpair).2 x) *
      (circleHeatKernel L t θ θ' * fourierBasisFun (L := L) (m.unpair).1 θ') := by
    intro m θ'; ring
  simp_rw [h_term_rw]
  -- Now we need: ∫ θ' in 0..L, ∑' m, const_m * (K_circle * ψ_n)(θ')
  -- = ∑' m, const_m * ∫ θ' in 0..L, K_circle * ψ_n(θ')
  -- Pull the const out of each tsum term, swap ∫ and ∑', apply reproducing
  -- This requires an interval integral version of integral_tsum
  -- Let's use a cleaner approach: directly show the final equality
  -- by reducing to term-by-term computation.
  -- Actually, let's just directly compute the whole thing.
  -- We know: ∫ θ' in 0..L, ∑' m, a_m * g_m(θ') = ∑' m, a_m * ∫ θ' in 0..L, g_m(θ')
  -- when the appropriate conditions hold.
  -- Let's use the direct computation approach: show
  -- exp(-m²t) * ∑' m, (c_m * e_k * φ_k(x)) * ∫ θ' K_circle * ψ_n(θ')
  -- = ∑' m, exp(-t * λ_m) * c_m * ψ_n(θ) * φ_k(x)
  -- For this we need to pull the interval integral inside the tsum.
  -- Use: intervalIntegral form of tsum_integral swap
  -- Convert interval integral to set integral, apply integral_tsum, convert back
  rw [intervalIntegral.integral_of_le (le_of_lt hL.out)]
  set μ := volume.restrict (Set.Ioc (0 : ℝ) L)
  -- Now goal: exp(-m²t) * ∫ θ' in μ, ∑' m, a_m * g_m(θ') = RHS
  -- Swap ∫ and ∑'
  have h_θ_int : ∀ m, Integrable
      (fun θ' => (DyninMityaginSpace.coeff m f *
        exp (-(t * (2 * ↑(m.unpair).2 + 1))) * hermiteFunction (m.unpair).2 x) *
        (circleHeatKernel L t θ θ' * fourierBasisFun (L := L) (m.unpair).1 θ')) μ := by
    intro m
    -- This is a continuous function restricted to a compact set
    have h_cont : Continuous (fun θ' =>
        circleHeatKernel L t θ θ' * fourierBasisFun (L := L) (m.unpair).1 θ') := by
      -- circleHeatKernel is continuous in θ'
      apply Continuous.mul
      · -- circleHeatKernel L t θ is continuous via continuous_tsum
        unfold circleHeatKernel
        set M := max (1 / Real.sqrt L) (Real.sqrt (2 / L))
        have hM_nonneg : 0 ≤ M := le_max_of_le_right (Real.sqrt_nonneg _)
        set c := t * (2 * π / L) ^ 2
        have hc_pos : 0 < c := mul_pos ht (sq_pos_of_pos (div_pos (mul_pos two_pos pi_pos) hL.out))
        set r := exp (-c)
        have hr_pos : 0 < r := exp_pos _
        have hr_lt_one : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
        have h_exp_le : ∀ n : ℕ, exp (-(t * (2 * π * ↑n / L) ^ 2)) ≤ r ^ n := by
          intro n
          rw [show r ^ n = exp (-c) ^ n from rfl, ← Real.exp_nat_mul,
            show ↑n * -c = -(c * ↑n) from by ring]
          apply Real.exp_le_exp.mpr
          have h_eq : t * (2 * π * ↑n / L) ^ 2 = c * (↑n) ^ 2 := by simp only [c]; ring
          rw [h_eq]
          have hn_sq : (↑n : ℝ) ≤ (↑n) ^ 2 := by
            rcases n with _ | n
            · simp
            · have h1 : (1 : ℝ) ≤ ↑(n + 1) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
              calc (↑(n + 1) : ℝ) = ↑(n + 1) * 1 := (mul_one _).symm
                _ ≤ ↑(n + 1) * ↑(n + 1) := by apply mul_le_mul_of_nonneg_left h1; positivity
                _ = (↑(n + 1)) ^ 2 := (sq _).symm
          linarith [mul_le_mul_of_nonneg_left hn_sq hc_pos.le]
        apply continuous_tsum
        · intro n; exact continuous_const.mul (fourierBasisFun_smooth (L := L) n).continuous
        · exact (summable_geometric_of_lt_one hr_pos.le hr_lt_one).mul_left (M ^ 2)
        · intro n θ'
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (le_of_lt (exp_pos _))]
          calc exp (-(t * (2 * π * ↑n / L) ^ 2)) * |fourierBasisFun (L := L) n θ| *
                |fourierBasisFun (L := L) n θ'|
              ≤ r ^ n * M * M := by
                apply mul_le_mul
                · exact mul_le_mul (h_exp_le n) (fourierBasisFun_abs_le n θ)
                    (abs_nonneg _) (pow_nonneg hr_pos.le n)
                · exact fourierBasisFun_abs_le n θ'
                · exact abs_nonneg _
                · exact mul_nonneg (pow_nonneg hr_pos.le n) hM_nonneg
            _ = M ^ 2 * r ^ n := by ring
      · exact (fourierBasisFun_smooth (L := L) (m.unpair).1).continuous
    have h_const_cont : Continuous (fun (_ : ℝ) =>
        DyninMityaginSpace.coeff m f *
        exp (-(t * (2 * ↑(m.unpair).2 + 1))) * hermiteFunction (m.unpair).2 x) :=
      continuous_const
    exact ((h_const_cont.mul h_cont).continuousOn.integrableOn_compact
      isCompact_Icc |>.mono_set Set.Ioc_subset_Icc_self).congr
      (by filter_upwards with θ'; simp only [Pi.mul_apply])
  have h_θ_sum : Summable (fun m => ∫ θ', ‖(DyninMityaginSpace.coeff m f *
      exp (-(t * (2 * ↑(m.unpair).2 + 1))) * hermiteFunction (m.unpair).2 x) *
      (circleHeatKernel L t θ θ' * fourierBasisFun (L := L) (m.unpair).1 θ')‖ ∂μ) := by
    -- On compact (0,L]: bound integrand norm by constant * |c_m| * (1+(m.unpair).2)^s_h
    obtain ⟨C_h, s_h, hC_h, _, hbound_h⟩ := hermiteFunction_sup_bound
    set M_f := max (1 / Real.sqrt L) (Real.sqrt (2 / L))
    have hM_f_nn : 0 ≤ M_f := le_max_of_le_right (Real.sqrt_nonneg _)
    -- Bound |K_circle| using its tsum
    set c_K := t * (2 * π / L) ^ 2
    have hc_K_pos : 0 < c_K := mul_pos ht (sq_pos_of_pos (div_pos (mul_pos two_pos pi_pos) hL.out))
    set r_K := exp (-c_K)
    have hr_K_pos : 0 < r_K := exp_pos _
    have hr_K_lt : r_K < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have h_exp_le_K : ∀ n : ℕ, exp (-(t * (2 * π * ↑n / L) ^ 2)) ≤ r_K ^ n := by
      intro n
      rw [show r_K ^ n = exp (-c_K) ^ n from rfl, ← Real.exp_nat_mul,
        show ↑n * -c_K = -(c_K * ↑n) from by ring]
      apply Real.exp_le_exp.mpr
      have h_eq : t * (2 * π * ↑n / L) ^ 2 = c_K * (↑n) ^ 2 := by simp only [c_K]; ring
      rw [h_eq]
      have hn_sq : (↑n : ℝ) ≤ (↑n) ^ 2 := by
        rcases n with _ | n; · simp
        · have h1 : (1 : ℝ) ≤ ↑(n + 1) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          nlinarith [h1]
      linarith [mul_le_mul_of_nonneg_left hn_sq hc_K_pos.le]
    set B_K := ∑' n, M_f ^ 2 * r_K ^ n
    have hB_K_nn : 0 ≤ B_K :=
      tsum_nonneg (fun n => mul_nonneg (sq_nonneg _) (pow_nonneg hr_K_pos.le n))
    have h_K_bound : ∀ θ'', |circleHeatKernel L t θ θ''| ≤ B_K := by
      intro θ''
      unfold circleHeatKernel
      calc |∑' n, exp (-(t * (2 * π * ↑n / L) ^ 2)) *
            fourierBasisFun (L := L) n θ * fourierBasisFun (L := L) n θ''|
          ≤ ∑' n, |exp (-(t * (2 * π * ↑n / L) ^ 2)) *
            fourierBasisFun (L := L) n θ * fourierBasisFun (L := L) n θ''| :=
            norm_tsum_le_tsum_norm ((circleHeatKernel_summable L t ht θ θ'').norm)
        _ ≤ B_K := by
            apply Summable.tsum_le_tsum _ ((circleHeatKernel_summable L t ht θ θ'').norm)
              ((summable_geometric_of_lt_one hr_K_pos.le hr_K_lt).mul_left _)
            intro n
            rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (le_of_lt (exp_pos _))]
            calc exp (-(t * (2 * π * ↑n / L) ^ 2)) * |fourierBasisFun (L := L) n θ| *
                  |fourierBasisFun (L := L) n θ''|
                ≤ r_K ^ n * M_f * M_f := by
                  apply mul_le_mul
                  · exact mul_le_mul (h_exp_le_K n) (fourierBasisFun_abs_le n θ)
                      (abs_nonneg _) (pow_nonneg hr_K_pos.le n)
                  · exact fourierBasisFun_abs_le n θ''
                  · exact abs_nonneg _
                  · exact mul_nonneg (pow_nonneg hr_K_pos.le n) hM_f_nn
              _ = M_f ^ 2 * r_K ^ n := by ring
    -- Bound ∫ ‖...‖ ∂μ ≤ |c_m| * C_h*(1+(m.unpair).2)^s_h * B_K * M_f * L
    apply Summable.of_nonneg_of_le
      (fun m => integral_nonneg (fun _ => norm_nonneg _))
    · intro m
      calc ∫ θ', ‖(DyninMityaginSpace.coeff m f *
            exp (-(t * (2 * ↑(m.unpair).2 + 1))) * hermiteFunction (m.unpair).2 x) *
            (circleHeatKernel L t θ θ' * fourierBasisFun (L := L) (m.unpair).1 θ')‖ ∂μ
          ≤ ∫ _, |DyninMityaginSpace.coeff m f| *
              (C_h * (1 + ↑(m.unpair).2) ^ s_h) * (B_K * M_f) ∂μ := by
            apply integral_mono_of_nonneg
              (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              (integrable_const _)
            exact Filter.Eventually.of_forall fun θ'' => by
              dsimp only []; rw [Real.norm_eq_abs, abs_mul]
              apply mul_le_mul
              · rw [abs_mul, abs_mul, abs_of_nonneg (le_of_lt (exp_pos _))]
                calc |DyninMityaginSpace.coeff m f| *
                      exp (-(t * (2 * ↑(m.unpair).2 + 1))) *
                      |hermiteFunction (m.unpair).2 x|
                    ≤ |DyninMityaginSpace.coeff m f| * 1 *
                      (C_h * (1 + ↑(m.unpair).2) ^ s_h) := by
                      apply mul_le_mul
                      · apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                        exact le_of_lt (Real.exp_lt_one_iff.mpr
                          (by nlinarith [Nat.cast_nonneg (α := ℝ) (m.unpair).2]))
                      · exact hbound_h _ _
                      · exact abs_nonneg _
                      · exact mul_nonneg (abs_nonneg _) zero_le_one
                  _ = _ := by ring
              · rw [abs_mul]; exact mul_le_mul (h_K_bound θ'')
                  (fourierBasisFun_abs_le _ _) (abs_nonneg _) hB_K_nn
              · exact abs_nonneg _
              · exact mul_nonneg (abs_nonneg _)
                  (mul_nonneg hC_h.le (Real.rpow_nonneg (by positivity) _))
        _ = |DyninMityaginSpace.coeff m f| *
              (C_h * (1 + ↑(m.unpair).2) ^ s_h) * (B_K * M_f) * L := by
            rw [integral_const, smul_eq_mul]
            show μ.real Set.univ * _ = _
            rw [Measure.real, Measure.restrict_apply MeasurableSet.univ,
              Set.univ_inter, Real.volume_Ioc, sub_zero,
              ENNReal.toReal_ofReal (le_of_lt hL.out)]
            ring
    · -- ∑ |c_m| * C_h * (1+(m.unpair).2)^s_h * const converges by coeff_decay
      obtain ⟨C_d, hC_d, s_d, hdecay⟩ := DyninMityaginSpace.coeff_decay (E :=
        NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ ℝ)) (Nat.ceil s_h + 2)
      set D := C_d * (s_d.sup DyninMityaginSpace.p) f
      set p_h := Nat.ceil s_h
      have hp_h : s_h ≤ ↑p_h := Nat.le_ceil _
      apply Summable.of_nonneg_of_le (fun m => by
            apply mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) _) (mul_nonneg hB_K_nn hM_f_nn))
              (le_of_lt hL.out)
            exact mul_nonneg hC_h.le (Real.rpow_nonneg (by positivity) _))
      · intro m
        have h1m_pos : (0 : ℝ) < 1 + ↑m := by positivity
        have h1k_le : (1 + ↑(m.unpair).2 : ℝ) ^ s_h ≤ (1 + ↑m) ^ p_h := by
          calc (1 + ↑(m.unpair).2 : ℝ) ^ s_h
              ≤ (1 + ↑m : ℝ) ^ s_h := by
                exact Real.rpow_le_rpow (by positivity)
                  (by exact_mod_cast (by linarith [Nat.unpair_right_le m] : 1 + (m.unpair).2 ≤ 1 + m))
                  (by linarith [Nat.le_ceil s_h])
            _ ≤ (1 + ↑m) ^ p_h := by
                rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by linarith) hp_h
        calc |DyninMityaginSpace.coeff m f| *
              (C_h * (1 + ↑(m.unpair).2) ^ s_h) * (B_K * M_f) * L
            ≤ |DyninMityaginSpace.coeff m f| *
              (C_h * (1 + ↑m) ^ p_h) * (B_K * M_f) * L := by
                gcongr; exact le_of_lt hL.out
          _ ≤ D * (C_h * (B_K * M_f) * L) / (1 + ↑m) ^ 2 := by
              have h1m_sq_pos : (0 : ℝ) < (1 + ↑m) ^ 2 := by positivity
              have h_coeff_bound : |DyninMityaginSpace.coeff m f| * (1 + ↑m) ^ (p_h + 2) ≤ D :=
                calc |DyninMityaginSpace.coeff m f| * (1 + ↑m) ^ (p_h + 2)
                    = |DyninMityaginSpace.coeff m f| * (1 + (↑m : ℝ)) ^ (↑(p_h + 2) : ℕ) := by
                      push_cast; ring_nf
                  _ ≤ D := hdecay f m
              rw [le_div_iff₀ h1m_sq_pos]
              calc |DyninMityaginSpace.coeff m f| *
                    (C_h * (1 + ↑m) ^ p_h) * (B_K * M_f) * L * (1 + ↑m) ^ 2
                  = |DyninMityaginSpace.coeff m f| * (1 + ↑m) ^ (p_h + 2) *
                    (C_h * (B_K * M_f) * L) := by rw [pow_add]; ring
                _ ≤ D * (C_h * (B_K * M_f) * L) :=
                    mul_le_mul_of_nonneg_right h_coeff_bound
                      (mul_nonneg (mul_nonneg (le_of_lt hC_h) (mul_nonneg hB_K_nn hM_f_nn))
                        (le_of_lt hL.out))
          _ = D * C_h * (B_K * M_f) * L * (1 / ((↑m + 1) ^ 2)) := by field_simp; ring
      · exact ((summable_nat_add_iff 1).mpr
            (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
          |>.congr (fun m => by push_cast; ring_nf)).mul_left _
  rw [← integral_tsum_of_summable_integral_norm h_θ_int h_θ_sum]
  -- Now goal: exp(-m²t) * ∑' m, ∫ θ' ∂μ, ... = RHS
  -- Evaluate each integral
  have h_final : ∀ m,
      ∫ θ', (DyninMityaginSpace.coeff m f *
        exp (-(t * (2 * ↑(m.unpair).2 + 1))) * hermiteFunction (m.unpair).2 x) *
        (circleHeatKernel L t θ θ' * fourierBasisFun (L := L) (m.unpair).1 θ') ∂μ =
      DyninMityaginSpace.coeff m f *
        exp (-(t * (2 * ↑(m.unpair).2 + 1))) * hermiteFunction (m.unpair).2 x *
        (exp (-(t * (2 * π * ↑(m.unpair).1 / L) ^ 2)) *
          fourierBasisFun (L := L) (m.unpair).1 θ) := by
    intro m
    rw [integral_const_mul]
    congr 1
    rw [← intervalIntegral.integral_of_le (le_of_lt hL.out)]
    exact h_circle_repro (m.unpair).1
  simp_rw [h_final]
  -- Now goal: exp(-m²t) * ∑' m, c_m * e_k * φ_k(x) * e_n * ψ_n(θ) = RHS
  -- Pull exp(-m²t) inside the tsum
  rw [← tsum_mul_left]
  -- Match term by term
  congr 1; funext m
  -- Combine exponentials: exp(-m²t) * exp(-t(2πn/L)²) * exp(-t(2k+1)) = exp(-t * λ_m)
  have h_exp_eq : exp (-(mass ^ 2 * t)) *
      (exp (-(t * (2 * ↑(m.unpair).2 + 1))) *
       exp (-(t * (2 * π * ↑(m.unpair).1 / L) ^ 2))) =
      exp (-(t * qftEigenvalue L mass m)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    unfold qftEigenvalue; ring
  -- Rearrange and substitute
  calc exp (-(mass ^ 2 * t)) *
    (DyninMityaginSpace.coeff m f *
      exp (-(t * (2 * ↑(m.unpair).2 + 1))) * hermiteFunction (m.unpair).2 x *
      (exp (-(t * (2 * π * ↑(m.unpair).1 / L) ^ 2)) *
        fourierBasisFun (L := L) (m.unpair).1 θ))
    = (exp (-(mass ^ 2 * t)) *
        (exp (-(t * (2 * ↑(m.unpair).2 + 1))) *
         exp (-(t * (2 * π * ↑(m.unpair).1 / L) ^ 2)))) *
      DyninMityaginSpace.coeff m f *
      fourierBasisFun (L := L) (m.unpair).1 θ *
      hermiteFunction (m.unpair).2 x := by ring
    _ = exp (-(t * qftEigenvalue L mass m)) *
      DyninMityaginSpace.coeff m f *
      fourierBasisFun (L := L) (m.unpair).1 θ *
      hermiteFunction (m.unpair).2 x := by rw [h_exp_eq]

/-- The parameter match between the kernel and heatSingularValue:
    e^{-(s/2)λ_m} = heatSingularValue L mass s m. -/
theorem cylinderHeatKernel_matches_heatSingularValue
    (L mass s : ℝ) (m : ℕ) :
    exp (-(s / 2 * qftEigenvalue L mass m)) =
    heatSingularValue L mass s m := by
  simp [heatSingularValue]

end
