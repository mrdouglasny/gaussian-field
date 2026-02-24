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

/-- The Mehler kernel reproduces Hermite eigenfunctions. -/
axiom mehlerKernel_reproduces_hermite (t : ℝ) (ht : 0 < t)
    (k : ℕ) (x₁ : ℝ) :
    ∫ x₂, mehlerKernel t x₁ x₂ * hermiteFunction k x₂ =
      exp (-(t * (2 * ↑k + 1))) * hermiteFunction k x₁

/-- The Mehler kernel satisfies the semigroup property. -/
axiom mehlerKernel_semigroup (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (x₁ x₂ : ℝ) :
    ∫ z, mehlerKernel s x₁ z * mehlerKernel t z x₂ =
      mehlerKernel (s + t) x₁ x₂

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

/-- The circle heat kernel reproduces Fourier eigenfunctions. -/
axiom circleHeatKernel_reproduces_fourier (L : ℝ) [Fact (0 < L)]
    (t : ℝ) (ht : 0 < t) (n : ℕ) (θ₁ : ℝ) :
    ∫ θ₂ in (0 : ℝ)..L,
      circleHeatKernel L t θ₁ θ₂ * fourierBasisFun (L := L) n θ₂ =
    exp (-(t * (2 * π * ↑n / L) ^ 2)) * fourierBasisFun (L := L) n θ₁

/-- The circle heat kernel satisfies the semigroup property. -/
axiom circleHeatKernel_semigroup (L : ℝ) [Fact (0 < L)]
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (θ₁ θ₂ : ℝ) :
    ∫ θ in (0 : ℝ)..L,
      circleHeatKernel L s θ₁ θ * circleHeatKernel L t θ θ₂ =
    circleHeatKernel L (s + t) θ₁ θ₂

/-! ## Full cylinder heat kernel -/

/-- Heat kernel on S¹_L × ℝ for A = -∂²/∂θ² + (-∂²/∂x² + x²) + m².

    Factors as e^{-m²t} · K_circle(θ₁,θ₂,t) · K_osc(x₁,x₂,t). -/
noncomputable def cylinderHeatKernel (L : ℝ) [Fact (0 < L)]
    (mass t θ₁ x₁ θ₂ x₂ : ℝ) : ℝ :=
  exp (-(mass ^ 2 * t)) * circleHeatKernel L t θ₁ θ₂ * mehlerKernel t x₁ x₂

/-- The cylinder heat kernel equals its eigenfunction expansion. -/
axiom cylinderHeatKernel_eq_series (L : ℝ) [Fact (0 < L)]
    (mass t : ℝ) (ht : 0 < t) (θ₁ x₁ θ₂ x₂ : ℝ) :
    cylinderHeatKernel L mass t θ₁ x₁ θ₂ x₂ =
      ∑' (m : ℕ), exp (-(t * qftEigenvalue L mass m)) *
        (fourierBasisFun (L := L) (m.unpair).1 θ₁ *
         hermiteFunction (m.unpair).2 x₁) *
        (fourierBasisFun (L := L) (m.unpair).1 θ₂ *
         hermiteFunction (m.unpair).2 x₂)

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

/-- **Bridge theorem**: integration against the cylinder heat kernel
    reproduces the spectral CLM action. -/
axiom cylinderHeatKernel_reproduces (L : ℝ) [Fact (0 < L)]
    (mass t : ℝ) (hmass : 0 < mass) (ht : 0 < t)
    (f : NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ ℝ))
    (θ x : ℝ) :
    ∫ θ' in (0 : ℝ)..L, ∫ x',
      cylinderHeatKernel L mass t θ x θ' x' *
        cylinderEval L f θ' x' =
    ∑' (m : ℕ), exp (-(t * qftEigenvalue L mass m)) *
      DyninMityaginSpace.coeff m f *
      fourierBasisFun (L := L) (m.unpair).1 θ *
      hermiteFunction (m.unpair).2 x

/-- The parameter match between the kernel and heatSingularValue:
    e^{-(s/2)λ_m} = heatSingularValue L mass s m. -/
theorem cylinderHeatKernel_matches_heatSingularValue
    (L mass s : ℝ) (m : ℕ) :
    exp (-(s / 2 * qftEigenvalue L mass m)) =
    heatSingularValue L mass s m := by
  simp [heatSingularValue]

end
