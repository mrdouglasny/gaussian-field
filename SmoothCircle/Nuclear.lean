/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# DyninMityaginSpace Instance for C∞(S¹)

Proves that `SmoothCircle L` is a `DyninMityaginSpace` by constructing a
continuous linear equivalence with `RapidDecaySeq` via the real Fourier transform.

## Main results

- `smoothCircleRapidDecayEquiv` — CLE: `SmoothCircle L ≃L[ℝ] RapidDecaySeq`
- `smoothCircle_dyninMityaginSpace` — the `DyninMityaginSpace` instance

## Mathematical outline

1. **Coefficient decay** (integration by parts): `|c_n(f)| ≤ C · p_k(f) / n^k`
2. **Fourier series convergence**: `f = ∑ₙ c_n(f) · ψ_n` in the seminorm topology
3. **Forward map**: `f ↦ (c_n(f))_n` maps into `RapidDecaySeq`
4. **Backward map**: `(a_n) ↦ ∑ₙ a_n · ψ_n` maps into `SmoothCircle L`
5. **CLE**: forward ∘ backward = id (by orthogonality), backward ∘ forward = id (by uniqueness)
-/

import SmoothCircle.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Fourier.AddCircle

noncomputable section

namespace GaussianField

open SmoothCircle

variable {L : ℝ} [hL : Fact (0 < L)]

namespace SmoothCircle

/-! ## Integration by parts: Fourier coefficient decay -/

/-- Integration by parts gives rapid decay of Fourier coefficients:
`|c_n(f)| * (1+n)^k ≤ C · max(p_0(f), p_k(f))` for all k.

For n = 0: bounded by `C · p_0(f)` (integral bound).
For n ≥ 1: integrating by parts k times gives
`|c_n(f)| ≤ C · p_k(f) / n^k`, hence `|c_n(f)| · (1+n)^k ≤ C' · p_k(f)`.
Combined: bounded by `C · max(p_0, p_k)`. -/
-- The derivative of a SmoothCircle element is again a SmoothCircle element.
private def derivSC (f : SmoothCircle L) : SmoothCircle L where
  toFun := deriv f
  periodic' := by
    have h := f.periodic_iteratedDeriv 1
    simp only [iteratedDeriv_succ, iteratedDeriv_zero] at h; exact h
  smooth' := (contDiff_infty_iff_deriv.mp f.smooth).2

private theorem derivSC_apply (f : SmoothCircle L) (x : ℝ) :
    (derivSC f) x = deriv f x := rfl

private theorem sobolevSeminorm_derivSC (f : SmoothCircle L) (k : ℕ) :
    sobolevSeminorm k (derivSC f) ≤ sobolevSeminorm (k + 1) f := by
  apply csSup_le (Set.Nonempty.image _ Icc_nonempty)
  rintro _ ⟨x, hx, rfl⟩
  show ‖iteratedDeriv k (⇑(derivSC f)) x‖ ≤ _
  calc ‖iteratedDeriv k (⇑(derivSC f)) x‖
      = ‖iteratedDeriv (k + 1) (⇑f) x‖ := by
        congr 1; exact (congr_fun iteratedDeriv_succ' x).symm
    _ ≤ sobolevSeminorm (k + 1) f := norm_iteratedDeriv_le_sobolevSeminorm f (k + 1) hx

-- k rounds of IBP: |∫₀ᴸ f(x) trig(2πmx/L) dx| ≤ (L/(2πm))^k · L · p_k(f)
-- Proved by induction on k, with both cos and sin bounds simultaneously.
-- At each step, IBP transfers one derivative from the trig function to f,
-- with boundary terms vanishing (sin(0) = sin(2πm) = 0 for cos case;
-- periodicity of f for sin case).
private theorem ibp_trig_bound (k : ℕ) (m : ℕ) (hm : 0 < m) :
    ∀ f : SmoothCircle L,
      |∫ x in (0:ℝ)..L, f x * Real.cos (2 * Real.pi * m * x / L)| ≤
        (L / (2 * Real.pi * m)) ^ k * (L * sobolevSeminorm k f) ∧
      |∫ x in (0:ℝ)..L, f x * Real.sin (2 * Real.pi * m * x / L)| ≤
        (L / (2 * Real.pi * m)) ^ k * (L * sobolevSeminorm k f) := by
  induction k with
  | zero =>
    intro f; simp only [pow_zero, one_mul]
    have h_base : ∀ (trig : ℝ → ℝ), Continuous trig → (∀ x, |trig x| ≤ 1) →
        |∫ x in (0:ℝ)..L, f x * trig x| ≤ L * sobolevSeminorm 0 f := by
      intro trig htrig_cont htrig_bound
      have h1 : |∫ x in (0:ℝ)..L, f x * trig x| ≤
          ∫ x in (0:ℝ)..L, ‖f x * trig x‖ := by
        have := intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume)
          (f := fun x => f x * trig x) (le_of_lt hL.out)
        rwa [Real.norm_eq_abs] at this
      calc |∫ x in (0:ℝ)..L, f x * trig x|
          ≤ ∫ x in (0:ℝ)..L, ‖f x * trig x‖ := h1
        _ ≤ ∫ x in (0:ℝ)..L, sobolevSeminorm 0 f := by
            apply intervalIntegral.integral_mono_on (le_of_lt hL.out)
            · exact (f.continuous.mul htrig_cont).norm.intervalIntegrable _ _
            · exact continuous_const.intervalIntegrable _ _
            · intro x _; rw [norm_mul]
              calc ‖f x‖ * ‖trig x‖ ≤ sobolevSeminorm 0 f * 1 :=
                    mul_le_mul (norm_iteratedDeriv_le_sobolevSeminorm' f 0 x)
                      (by rw [Real.norm_eq_abs]; exact htrig_bound x)
                      (norm_nonneg _) (sobolevSeminorm_nonneg 0 f)
                _ = _ := mul_one _
        _ = L * sobolevSeminorm 0 f := by
            rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    exact ⟨h_base _ (Real.continuous_cos.comp (by fun_prop)) (fun x => Real.abs_cos_le_one _),
           h_base _ (Real.continuous_sin.comp (by fun_prop)) (fun x => Real.abs_sin_le_one _)⟩
  | succ k ih =>
    intro f
    have ⟨ih_cos, ih_sin⟩ := ih (derivSC f)
    -- IBP identities (boundary terms vanish by periodicity + sin(2πm)=0)
    have ibp_cos : ∫ x in (0:ℝ)..L, f x * Real.cos (2 * Real.pi * m * x / L) =
        -(L / (2 * Real.pi * m)) *
          ∫ x in (0:ℝ)..L, (derivSC f) x * Real.sin (2 * Real.pi * m * x / L) := by
      -- IBP: ∫ u·v' = u·v|₀ᴸ - ∫ u'·v, with u = f, v = L/(2πm) sin(2πmx/L)
      set c := 2 * Real.pi * (m : ℝ) / L with hc_def
      have hc_ne : c ≠ 0 := div_ne_zero
        (mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt Real.pi_pos))
          (Nat.cast_ne_zero.mpr (by omega)))
        (ne_of_gt hL.out)
      set v := fun x => L / (2 * Real.pi * m) * Real.sin (c * x)
      have hv_deriv : ∀ x, HasDerivAt v (Real.cos (c * x)) x := by
        intro x
        -- v(x) = L/(2πm) * sin(cx), v'(x) = L/(2πm) * c * cos(cx) = cos(cx) since L/(2πm)*c = 1
        have h1 : HasDerivAt (fun x => c * x) c x := by
          simpa using (hasDerivAt_id x).const_mul c
        have h2 : HasDerivAt (fun x => Real.sin (c * x)) (Real.cos (c * x) * c) x :=
          h1.sin
        have h3 : HasDerivAt v (L / (2 * Real.pi * ↑m) * (Real.cos (c * x) * c)) x :=
          h2.const_mul _
        have h4 : L / (2 * Real.pi * ↑m) * (Real.cos (c * x) * c) = Real.cos (c * x) := by
          rw [hc_def]; field_simp [ne_of_gt hL.out]
        rwa [h4] at h3
      -- v(0) = 0, v(L) = L/(2πm) sin(2πm) = 0
      have hv0 : v 0 = 0 := by simp [v, Real.sin_zero]
      have hvL : v L = 0 := by
        simp only [v, hc_def]
        rw [show c * L = 2 * Real.pi * m from by
          rw [hc_def]; field_simp [ne_of_gt hL.out]]
        have : Real.sin (2 * Real.pi * m) = 0 := by
          rw [show (2:ℝ) * Real.pi * m = ↑m * (2 * Real.pi) from by ring,
            ← sub_zero (↑m * (2 * Real.pi)), Real.sin_nat_mul_two_pi_sub, Real.sin_zero, neg_zero]
        simp [this]
      -- Apply IBP
      have h_ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (u := ⇑f) (v := v) (u' := deriv (⇑f)) (v' := fun x => Real.cos (c * x))
        (fun x _ => ((contDiff_infty_iff_deriv.mp f.smooth).1).differentiableAt.hasDerivAt)
        (fun x _ => hv_deriv x)
        ((contDiff_infty_iff_deriv.mp f.smooth).2.continuous.intervalIntegrable 0 L)
        (((Real.continuous_cos.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 L))
      -- Clean up: v' = cos(cx) = cos(2πmx/L)
      have h_rw : (fun x => Real.cos (c * x)) = fun x =>
          Real.cos (2 * Real.pi * ↑m * x / L) := by
        ext x; simp [hc_def]; ring_nf
      rw [h_rw] at h_ibp; clear h_rw
      simp only [h_ibp, hv0, hvL, mul_zero, sub_zero, zero_sub]
      -- The remaining integral: ∫ (deriv f) · v = (L/(2πm)) ∫ (deriv f) · sin
      rw [show (fun x => deriv (⇑f) x * v x) =
          fun x => L / (2 * Real.pi * m) * ((derivSC f) x * Real.sin (c * x)) from by
        ext x; simp [v, derivSC]; ring]
      rw [intervalIntegral.integral_const_mul]
      simp only [hc_def]; ring_nf
    have ibp_sin : ∫ x in (0:ℝ)..L, f x * Real.sin (2 * Real.pi * m * x / L) =
        (L / (2 * Real.pi * m)) *
          ∫ x in (0:ℝ)..L, (derivSC f) x * Real.cos (2 * Real.pi * m * x / L) := by
      set c := 2 * Real.pi * (m : ℝ) / L with hc_def'
      have hc_ne : c ≠ 0 := div_ne_zero
        (mul_ne_zero (mul_ne_zero two_ne_zero (ne_of_gt Real.pi_pos))
          (Nat.cast_ne_zero.mpr (by omega)))
        (ne_of_gt hL.out)
      set w := fun x => -(L / (2 * Real.pi * m)) * Real.cos (c * x)
      have hw_deriv : ∀ x, HasDerivAt w (Real.sin (c * x)) x := by
        intro x
        have h1 : HasDerivAt (fun x => c * x) c x := by
          simpa using (hasDerivAt_id x).const_mul c
        have h2 := h1.cos
        -- h2 : HasDerivAt (cos ∘ (c*·)) (-sin(c*x) * c) x
        have h3 := h2.const_mul (-(L / (2 * Real.pi * ↑m)))
        have h4 : -(L / (2 * Real.pi * ↑m)) * (-Real.sin (c * x) * c) =
            Real.sin (c * x) := by
          rw [hc_def']; field_simp [ne_of_gt hL.out]
        rwa [h4] at h3
      -- w(0) = w(L) since cos(2πm) = cos(0) = 1, and f(L) = f(0) by periodicity
      have hw_eq : f L * w L = f 0 * w 0 := by
        have hfL : (f : ℝ → ℝ) L = (f : ℝ → ℝ) 0 := by
          have h := f.periodic' 0; rwa [zero_add] at h
        have hwL : w L = w 0 := by
          simp only [w, mul_zero, Real.cos_zero]
          congr 1
          rw [show c * L = 2 * Real.pi * m from by
            rw [hc_def']; field_simp [ne_of_gt hL.out]]
          rw [show (2:ℝ) * Real.pi * m = ↑m * (2 * Real.pi) from by ring,
            ← sub_zero (↑m * (2 * Real.pi)), Real.cos_nat_mul_two_pi_sub, Real.cos_zero]
        rw [hfL, hwL]
      have h_ibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
        (u := ⇑f) (v := w) (u' := deriv (⇑f)) (v' := fun x => Real.sin (c * x))
        (fun x _ => ((contDiff_infty_iff_deriv.mp f.smooth).1).differentiableAt.hasDerivAt)
        (fun x _ => hw_deriv x)
        ((contDiff_infty_iff_deriv.mp f.smooth).2.continuous.intervalIntegrable 0 L)
        (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).intervalIntegrable 0 L))
      have h_rw : (fun x => Real.sin (c * x)) = fun x =>
          Real.sin (2 * Real.pi * ↑m * x / L) := by
        ext x; simp [hc_def']; ring_nf
      rw [h_rw] at h_ibp; clear h_rw
      rw [h_ibp, hw_eq, sub_self, zero_sub]
      rw [show (fun x => deriv (⇑f) x * w x) =
          fun x => -(L / (2 * Real.pi * m)) * ((derivSC f) x * Real.cos (c * x)) from by
        ext x; simp [w, derivSC]; ring]
      rw [intervalIntegral.integral_const_mul, neg_mul, neg_neg]
      simp only [hc_def']; ring_nf
    -- Sobolev seminorm bound: p_k(derivSC f) ≤ p_{k+1}(f)
    have h_sem := sobolevSeminorm_derivSC f k
    -- Combine: |∫ f cos| = (L/(2πm)) |∫ f' sin| ≤ (L/(2πm))^{k+1} · L · p_{k+1}(f)
    have hc : 0 ≤ L / (2 * Real.pi * ↑m) :=
      div_nonneg (le_of_lt hL.out) (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
        (Nat.cast_nonneg _))
    constructor
    · rw [ibp_cos]; rw [show -(L / (2 * Real.pi * ↑m)) * _ = -(L / (2 * Real.pi * ↑m) *
        ∫ x in (0:ℝ)..L, (derivSC f) x * Real.sin (2 * Real.pi * ↑m * x / L)) from by ring]
      rw [abs_neg, abs_mul, abs_of_nonneg hc, pow_succ]
      calc L / (2 * Real.pi * ↑m) *
            |∫ x in (0:ℝ)..L, (derivSC f) x * Real.sin (2 * Real.pi * ↑m * x / L)|
          ≤ L / (2 * Real.pi * ↑m) *
            ((L / (2 * Real.pi * ↑m)) ^ k * (L * sobolevSeminorm k (derivSC f))) :=
            mul_le_mul_of_nonneg_left ih_sin hc
        _ ≤ L / (2 * Real.pi * ↑m) *
            ((L / (2 * Real.pi * ↑m)) ^ k * (L * sobolevSeminorm (k + 1) f)) := by
            apply mul_le_mul_of_nonneg_left _ hc
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h_sem (le_of_lt hL.out)) (pow_nonneg hc k)
        _ = _ := by ring
    · rw [ibp_sin, abs_mul, abs_of_nonneg hc, pow_succ]
      calc L / (2 * Real.pi * ↑m) *
            |∫ x in (0:ℝ)..L, (derivSC f) x * Real.cos (2 * Real.pi * ↑m * x / L)|
          ≤ L / (2 * Real.pi * ↑m) *
            ((L / (2 * Real.pi * ↑m)) ^ k * (L * sobolevSeminorm k (derivSC f))) :=
            mul_le_mul_of_nonneg_left ih_cos hc
        _ ≤ L / (2 * Real.pi * ↑m) *
            ((L / (2 * Real.pi * ↑m)) ^ k * (L * sobolevSeminorm (k + 1) f)) := by
            apply mul_le_mul_of_nonneg_left _ hc
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left h_sem (le_of_lt hL.out)) (pow_nonneg hc k)
        _ = _ := by ring

-- IBP bound for Fourier coefficients of periodic functions.
private theorem fourierCoeff_ibp_bound (k : ℕ) :
    ∃ C > 0, ∀ (f : SmoothCircle L) (n : ℕ), n ≥ 1 →
      |fourierCoeffReal (L := L) n f| * ((n : ℝ) + 1) ^ k ≤ C * sobolevSeminorm k f := by
  set A := Real.sqrt (2 / L)
  have hA_pos : 0 < A := Real.sqrt_pos.mpr (div_pos two_pos hL.out)
  have hC_pos : 0 < A * L * (3 * L / (2 * Real.pi)) ^ k + 1 := by
    have : 0 ≤ A * L * (3 * L / (2 * Real.pi)) ^ k :=
      mul_nonneg (mul_nonneg hA_pos.le hL.out.le)
        (pow_nonneg (div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) hL.out.le)
          (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) Real.pi_pos.le)) k)
    linarith
  refine ⟨A * L * (3 * L / (2 * Real.pi)) ^ k + 1, hC_pos, ?_⟩
  intro f n hn
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  set m := n' / 2 + 1 with hm_def
  have hm_pos : 0 < m := by omega
  have hm_cast : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm_pos
  -- n'+2 ≤ 3*m
  have hm3 : (n' : ℝ) + 2 ≤ 3 * (m : ℝ) := by exact_mod_cast (show n' + 2 ≤ 3 * m by omega)
  -- Apply ibp_trig_bound for frequency m
  have ⟨ibp_c, ibp_s⟩ := ibp_trig_bound k m hm_pos f
  -- |c_{n'+1}(f)| ≤ A · (L/(2πm))^k · L · p_k(f)
  -- The integral in fourierCoeffReal = set integral over Icc = interval integral
  have h_coeff : |fourierCoeffReal (L := L) (n' + 1) f| ≤
      A * ((L / (2 * Real.pi * ↑m)) ^ k * (L * sobolevSeminorm k f)) := by
    unfold fourierCoeffReal fourierBasisFun
    simp only
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (le_of_lt hL.out)]
    split_ifs with h
    · -- cos case: factor out √(2/L)
      have : (fun x => f x * (A * Real.cos (2 * Real.pi * ↑(n' / 2 + 1) * x / L))) =
          fun x => A * (f x * Real.cos (2 * Real.pi * ↑(n' / 2 + 1) * x / L)) := by
        ext x; ring
      rw [this, intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg hA_pos.le]
      exact mul_le_mul_of_nonneg_left ibp_c hA_pos.le
    · -- sin case
      have : (fun x => f x * (A * Real.sin (2 * Real.pi * ↑(n' / 2 + 1) * x / L))) =
          fun x => A * (f x * Real.sin (2 * Real.pi * ↑(n' / 2 + 1) * x / L)) := by
        ext x; ring
      rw [this, intervalIntegral.integral_const_mul, abs_mul, abs_of_nonneg hA_pos.le]
      exact mul_le_mul_of_nonneg_left ibp_s hA_pos.le
  -- Key algebra: (L/(2πm))^k · (3m)^k = (3L/(2π))^k
  have h_pow_eq : (L / (2 * Real.pi * ↑m)) ^ k * (3 * ↑m) ^ k =
      (3 * L / (2 * Real.pi)) ^ k := by
    rw [← mul_pow]; congr 1
    field_simp [ne_of_gt hm_cast, ne_of_gt Real.pi_pos]
  -- (n'+2)^k ≤ (3m)^k
  have h_pow_le : ((n' : ℝ) + 2) ^ k ≤ (3 * (m : ℝ)) ^ k :=
    pow_le_pow_left₀ (by positivity) hm3 k
  -- Combine
  have h_sem_nn := sobolevSeminorm_nonneg k f
  have h_Aprod_nn : 0 ≤ A * ((L / (2 * Real.pi * ↑m)) ^ k * (L * sobolevSeminorm k f)) :=
    mul_nonneg hA_pos.le (mul_nonneg (pow_nonneg (div_nonneg hL.out.le
      (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) Real.pi_pos.le)
        (Nat.cast_nonneg _))) k) (mul_nonneg hL.out.le h_sem_nn))
  calc |fourierCoeffReal (n' + 1) f| * ((↑(n' + 1) : ℝ) + 1) ^ k
      = |fourierCoeffReal (n' + 1) f| * ((↑n' + 2) ^ k) := by push_cast; ring_nf
    _ ≤ A * ((L / (2 * Real.pi * ↑m)) ^ k * (L * sobolevSeminorm k f)) *
        ((↑n' + 2) ^ k) :=
        mul_le_mul_of_nonneg_right h_coeff (pow_nonneg (by positivity) k)
    _ ≤ A * ((L / (2 * Real.pi * ↑m)) ^ k * (L * sobolevSeminorm k f)) *
        ((3 * ↑m) ^ k) :=
        mul_le_mul_of_nonneg_left h_pow_le h_Aprod_nn
    _ = A * L * ((L / (2 * Real.pi * ↑m)) ^ k * (3 * ↑m) ^ k) *
        sobolevSeminorm k f := by ring
    _ = A * L * (3 * L / (2 * Real.pi)) ^ k * sobolevSeminorm k f := by rw [h_pow_eq]
    _ ≤ (A * L * (3 * L / (2 * Real.pi)) ^ k + 1) * sobolevSeminorm k f := by
        nlinarith

theorem fourierCoeffReal_decay (k : ℕ) :
    ∃ C > 0, ∀ (f : SmoothCircle L) (n : ℕ),
      ‖fourierCoeffReal n f‖ * (1 + (n : ℝ)) ^ k ≤
        C * (({0, k} : Finset ℕ).sup sobolevSeminorm) f := by
  -- Get bounds for both cases
  have h_bound := fourierCoeffReal_bound (L := L)
  obtain ⟨C₁, hC₁_pos, h_ibp⟩ := fourierCoeff_ibp_bound (L := L) k
  set M := max (1 / Real.sqrt L) (Real.sqrt (2 / L))
  have hM_pos : 0 < M := lt_max_of_lt_left (div_pos one_pos (Real.sqrt_pos.mpr hL.out))
  -- Constant: enough to bound both cases
  have hC_pos : 0 < M * L + C₁ + 1 := by linarith [mul_pos hM_pos hL.out]
  refine ⟨M * L + C₁ + 1, hC_pos, fun f n => ?_⟩
  -- Seminorm ordering: p_0 ≤ sup{p_0, p_k} and p_k ≤ sup{p_0, p_k}
  have h_le_0 : sobolevSeminorm (L := L) 0 ≤ ({0, k} : Finset ℕ).sup sobolevSeminorm :=
    Finset.le_sup (show (0 : ℕ) ∈ ({0, k} : Finset ℕ) from Finset.mem_insert_self _ _)
  have h_le_k : sobolevSeminorm (L := L) k ≤ ({0, k} : Finset ℕ).sup sobolevSeminorm :=
    Finset.le_sup (show k ∈ ({0, k} : Finset ℕ) from by simp)
  set S := (({0, k} : Finset ℕ).sup sobolevSeminorm) f
  have hS_nn : 0 ≤ S := by positivity
  rcases n with _ | n
  · -- n = 0: |c_0(f)| * 1^k = |c_0(f)| ≤ M*L*p_0(f) ≤ (M*L+C₁+1)*S
    simp only [Nat.cast_zero, add_zero, one_pow, mul_one]
    have h1 : ‖fourierCoeffReal 0 f‖ ≤ M * L * sobolevSeminorm 0 f := h_bound 0 f
    have h2 : sobolevSeminorm (L := L) 0 f ≤ S := h_le_0 f
    have h3 : M * L * sobolevSeminorm 0 f ≤ M * L * S :=
      mul_le_mul_of_nonneg_left h2 (mul_nonneg (le_of_lt hM_pos) (le_of_lt hL.out))
    have h4 : 0 ≤ C₁ * S := mul_nonneg (le_of_lt hC₁_pos) hS_nn
    linarith
  · -- n ≥ 1: IBP gives |c_n(f)| * (1+n)^k ≤ C₁ * p_k(f) ≤ (M*L+C₁+1)*S
    rw [show (1 + (↑(n + 1) : ℝ)) = (↑(n + 1) : ℝ) + 1 from by push_cast; ring,
      Real.norm_eq_abs]
    have h1 : |fourierCoeffReal (n + 1) f| * ((↑(n + 1) : ℝ) + 1) ^ k ≤
        C₁ * sobolevSeminorm k f := h_ibp f (n + 1) (by omega)
    have h2 : sobolevSeminorm (L := L) k f ≤ S := h_le_k f
    have h3 : C₁ * sobolevSeminorm k f ≤ C₁ * S :=
      mul_le_mul_of_nonneg_left h2 (le_of_lt hC₁_pos)
    linarith [mul_nonneg (mul_nonneg (le_of_lt hM_pos) (le_of_lt hL.out)) hS_nn, hS_nn]

/-! ## Forward map: SmoothCircle → RapidDecaySeq -/

/-- Helper: summability of shifted inverse square series `∑ 1/(1+n)^2`. -/
private theorem summable_shifted_inv_sq :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have h := (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
  refine (h.comp_injective (fun a b h => Nat.succ_injective h)).congr (fun n => ?_)
  simp only [Function.comp, Nat.cast_succ]
  ring

/-- The Fourier coefficients of a smooth periodic function form a rapidly
decreasing sequence. Uses `fourierCoeffReal_decay` at order k+2 and
comparison with the convergent p-series `∑ 1/(1+n)^2`. -/
theorem fourierCoeff_rapid_decay (f : SmoothCircle L) (k : ℕ) :
    Summable (fun m => |fourierCoeffReal (L := L) m f| * (1 + (m : ℝ)) ^ k) := by
  obtain ⟨C, hC, hbound⟩ := fourierCoeffReal_decay (L := L) (k + 2)
  set B := C * (({0, k + 2} : Finset ℕ).sup sobolevSeminorm) f
  have h_sum : Summable (fun m : ℕ => B * (1 / ((m : ℝ) + 1) ^ 2)) :=
    summable_shifted_inv_sq.mul_left B
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (abs_nonneg _) (pow_nonneg (by positivity) _))
    (fun m => ?_)
    h_sum
  -- Goal: |c_m f| * (1+m)^k ≤ B * (1 / (↑m + 1) ^ 2)
  have h1m : (0 : ℝ) < 1 + ↑m := by positivity
  have hm := hbound f m
  rw [Real.norm_eq_abs] at hm
  rw [mul_one_div]
  rw [show (↑m : ℝ) + 1 = 1 + ↑m from by ring]
  rw [le_div_iff₀ (pow_pos h1m 2)]
  calc |fourierCoeffReal m f| * (1 + ↑m) ^ k * (1 + ↑m) ^ 2
      = |fourierCoeffReal m f| * (1 + ↑m) ^ (k + 2) := by rw [pow_add, mul_assoc]
    _ ≤ B := hm

/-- The forward map: Fourier coefficients as a `RapidDecaySeq`. -/
def toRapidDecay (f : SmoothCircle L) : RapidDecaySeq where
  val m := fourierCoeffReal m f
  rapid_decay k := fourierCoeff_rapid_decay f k

/-- The forward map is linear. -/
def toRapidDecayLM : SmoothCircle L →ₗ[ℝ] RapidDecaySeq where
  toFun := toRapidDecay
  map_add' f g := by
    apply RapidDecaySeq.ext; intro m
    simp only [toRapidDecay, RapidDecaySeq.add_val]
    exact fourierCoeffReal_add m f g
  map_smul' r f := by
    apply RapidDecaySeq.ext; intro m
    simp only [toRapidDecay, RapidDecaySeq.smul_val]
    exact fourierCoeffReal_smul m r f

/-- The forward map is continuous. -/
theorem toRapidDecay_continuous : Continuous (toRapidDecayLM (L := L)) := by
  apply Seminorm.continuous_from_bounded smoothCircle_withSeminorms
    RapidDecaySeq.rapidDecay_withSeminorms
  intro k
  obtain ⟨C, hC, hbound⟩ := fourierCoeffReal_decay (L := L) (k + 2)
  set Z := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2
  refine ⟨{0, k + 2}, ⟨C * Z, by positivity⟩, fun f => ?_⟩
  simp only [Seminorm.comp_apply, NNReal.smul_def, Seminorm.smul_apply, NNReal.coe_mk]
  show ∑' m, |fourierCoeffReal m f| * (1 + (m : ℝ)) ^ k ≤
    C * Z * (({0, k + 2} : Finset ℕ).sup sobolevSeminorm) f
  set S := (({0, k + 2} : Finset ℕ).sup sobolevSeminorm) f
  have h_le : ∀ m : ℕ, |fourierCoeffReal m f| * (1 + (m : ℝ)) ^ k ≤
      C * S * (1 / ((↑m : ℝ) + 1) ^ 2) := by
    intro m
    have h1m : (0 : ℝ) < 1 + ↑m := by positivity
    have hm := hbound f m
    rw [Real.norm_eq_abs] at hm
    calc |fourierCoeffReal m f| * (1 + ↑m) ^ k
        = |fourierCoeffReal m f| * (1 + ↑m) ^ (k + 2) / (1 + ↑m) ^ 2 := by
          rw [pow_add]; field_simp
      _ ≤ C * S / (1 + ↑m) ^ 2 := div_le_div_of_nonneg_right hm (sq_nonneg _)
      _ = C * S * (1 / ((↑m : ℝ) + 1) ^ 2) := by ring
  calc ∑' m, |fourierCoeffReal m f| * (1 + ↑m) ^ k
      ≤ ∑' (m : ℕ), C * S * (1 / ((↑m : ℝ) + 1) ^ 2) :=
        (fourierCoeff_rapid_decay f k).tsum_le_tsum h_le
          ((summable_shifted_inv_sq.mul_left (C * S)).congr (fun n => by ring))
    _ = C * S * Z := by rw [tsum_mul_left]
    _ = C * Z * S := by ring

/-- The forward map as a CLM. -/
def toRapidDecayCLM : SmoothCircle L →L[ℝ] RapidDecaySeq where
  toLinearMap := toRapidDecayLM
  cont := toRapidDecay_continuous

/-! ## Backward map: RapidDecaySeq → SmoothCircle -/

theorem summable_fourierBasis_smul (a : RapidDecaySeq) :
    ∀ x, Summable (fun n => a.val n * fourierBasisFun (L := L) n x) := by
  intro x
  set C := max (1 / Real.sqrt L) (Real.sqrt (2 / L))
  apply Summable.of_norm_bounded (g := fun n => C * |a.val n|)
  · have h0 := a.rapid_decay 0
    simp only [pow_zero, mul_one] at h0
    exact (h0.mul_left C).congr (fun n => by simp)
  · intro n
    simp only [Real.norm_eq_abs, abs_mul]
    calc |a.val n| * |fourierBasisFun (L := L) n x|
        ≤ |a.val n| * C := mul_le_mul_of_nonneg_left (fourierBasisFun_abs_le n x) (abs_nonneg _)
      _ = C * |a.val n| := mul_comm _ _

/-- Bound on iteratedFDeriv of a single Fourier term `a_n * ψ_n(x)`. -/
private theorem norm_iteratedFDeriv_fourierTerm (a : RapidDecaySeq) (k n : ℕ) (x : ℝ)
    (_hk : (k : ℕ∞) ≤ ⊤) :
    ‖iteratedFDeriv ℝ k (fun y => a.val n * fourierBasisFun (L := L) n y) x‖ ≤
      |a.val n| * sobolevSeminorm (L := L) k (fourierBasis n) := by
  have hcoe : (fun y => a.val n * fourierBasisFun (L := L) n y) =
      (fun y => a.val n * (fourierBasis (L := L) n : ℝ → ℝ) y) := by ext; simp
  rw [hcoe, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_const_mul_field,
      norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_iteratedDeriv_le_sobolevSeminorm' _ k x) (abs_nonneg _)

/-- The Fourier series of rapidly decaying coefficients defines a smooth function. -/
theorem contDiff_fourierSeries (a : RapidDecaySeq) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑' n, a.val n * fourierBasisFun (L := L) n x) := by
  apply contDiff_tsum (v := fun k n => |a.val n| * sobolevSeminorm (L := L) k (fourierBasis n))
  · intro n; exact contDiff_const.mul (fourierBasisFun_smooth n)
  · intro k _
    obtain ⟨C, hC, hbound⟩ := sobolevSeminorm_fourierBasis_le (L := L) k
    exact Summable.of_nonneg_of_le
      (fun n => mul_nonneg (abs_nonneg _) (sobolevSeminorm_nonneg k _))
      (fun n => mul_le_mul_of_nonneg_left (hbound n) (abs_nonneg _))
      ((a.rapid_decay k).mul_right C |>.congr (fun n => by ring))
  · exact fun k n x hk => norm_iteratedFDeriv_fourierTerm a k n x hk

/-- The Fourier series of rapidly decaying coefficients defines a periodic function. -/
theorem periodic_fourierSeries (a : RapidDecaySeq) :
    Function.Periodic (fun x => ∑' n, a.val n * fourierBasisFun (L := L) n x) L := by
  intro x
  show ∑' n, a.val n * fourierBasisFun (L := L) n (x + L) =
    ∑' n, a.val n * fourierBasisFun (L := L) n x
  congr 1; ext n
  rw [fourierBasisFun_periodic (L := L) n x]

/-- The backward map: reconstruct a smooth periodic function from coefficients. -/
def fromRapidDecay (a : RapidDecaySeq) : SmoothCircle L :=
  ⟨fun x => ∑' n, a.val n * fourierBasisFun (L := L) n x,
   periodic_fourierSeries a,
   contDiff_fourierSeries a⟩

/-- The backward map is linear. -/
def fromRapidDecayLM : RapidDecaySeq →ₗ[ℝ] SmoothCircle L where
  toFun := fromRapidDecay
  map_add' a b := by
    apply SmoothCircle.ext; intro x
    show ∑' n, (a.val n + b.val n) * fourierBasisFun (L := L) n x =
      (∑' n, a.val n * fourierBasisFun (L := L) n x) +
      (∑' n, b.val n * fourierBasisFun (L := L) n x)
    simp_rw [add_mul]
    exact (summable_fourierBasis_smul a x).tsum_add (summable_fourierBasis_smul b x)
  map_smul' r a := by
    apply SmoothCircle.ext; intro x
    show ∑' n, (r * a.val n) * fourierBasisFun (L := L) n x =
      r * (∑' n, a.val n * fourierBasisFun (L := L) n x)
    simp_rw [mul_assoc]
    exact tsum_mul_left

/-- Summability of Fourier term bounds `|a_n| * p_j(ψ_n)` for any rapid decay seq. -/
private theorem summable_fourierTerm_bound (a : RapidDecaySeq) (j : ℕ) :
    Summable (fun n => |a.val n| * sobolevSeminorm (L := L) j (fourierBasis n)) := by
  obtain ⟨C, _, hbound⟩ := sobolevSeminorm_fourierBasis_le (L := L) j
  exact .of_nonneg_of_le
    (fun n => mul_nonneg (abs_nonneg _) (sobolevSeminorm_nonneg j _))
    (fun n => mul_le_mul_of_nonneg_left (hbound n) (abs_nonneg _))
    ((a.rapid_decay j).mul_right C |>.congr (fun n => by ring))

/-- The backward map is continuous. -/
theorem fromRapidDecay_continuous : Continuous (fromRapidDecayLM (L := L)) := by
  apply Seminorm.continuous_from_bounded RapidDecaySeq.rapidDecay_withSeminorms
    smoothCircle_withSeminorms
  intro k
  obtain ⟨C, hC, hbound⟩ := sobolevSeminorm_fourierBasis_le (L := L) k
  refine ⟨{k}, ⟨C, le_of_lt hC⟩, fun a => ?_⟩
  simp only [Finset.sup_singleton, Seminorm.comp_apply, NNReal.smul_def,
    Seminorm.smul_apply, NNReal.coe_mk]
  -- Goal: sobolevSeminorm k (fromRapidDecayLM a) ≤ C * rapidDecaySeminorm k a
  -- Bound the sSup pointwise
  apply csSup_le (Set.Nonempty.image _ (Set.nonempty_Icc.mpr (le_of_lt hL.out)))
  rintro _ ⟨x, _, rfl⟩
  -- ‖iteratedDeriv k (fromRapidDecay a) x‖ ≤ C * rapidDecaySeminorm k a
  -- Step 1: rewrite coercion and convert iteratedDeriv to iteratedFDeriv
  show ‖iteratedDeriv k (↑(fromRapidDecayLM (L := L) a) : ℝ → ℝ) x‖ ≤
    C * RapidDecaySeq.rapidDecaySeminorm k a
  rw [show (↑(fromRapidDecayLM (L := L) a) : ℝ → ℝ) =
    fun y => ∑' n, a.val n * fourierBasisFun (L := L) n y from rfl]
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv (𝕜 := ℝ)]
  -- Step 2: commute iteratedFDeriv with tsum
  rw [iteratedFDeriv_tsum_apply
    (fun n => contDiff_const.mul (fourierBasisFun_smooth (L := L) n))
    (fun j _ => summable_fourierTerm_bound a j)
    (fun j n y hj => norm_iteratedFDeriv_fourierTerm a j n y hj) le_top]
  -- Step 3: triangle inequality + pointwise bounds
  have h_norm : Summable (fun n =>
      ‖iteratedFDeriv ℝ k (fun y => a.val n * fourierBasisFun (L := L) n y) x‖) :=
    .of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun n => norm_iteratedFDeriv_fourierTerm a k n x le_top) (summable_fourierTerm_bound a k)
  calc ‖∑' n, iteratedFDeriv ℝ k (fun y => a.val n * fourierBasisFun n y) x‖
      ≤ ∑' n, ‖iteratedFDeriv ℝ k (fun y => a.val n * fourierBasisFun n y) x‖ :=
        norm_tsum_le_tsum_norm h_norm
    _ ≤ ∑' n, |a.val n| * sobolevSeminorm k (fourierBasis n) :=
        h_norm.tsum_le_tsum (fun n => norm_iteratedFDeriv_fourierTerm a k n x le_top)
          (summable_fourierTerm_bound a k)
    _ ≤ ∑' n, |a.val n| * (C * (1 + ↑n) ^ k) :=
        (summable_fourierTerm_bound a k).tsum_le_tsum
          (fun n => mul_le_mul_of_nonneg_left (hbound n) (abs_nonneg _))
          ((a.rapid_decay k).mul_right C |>.congr (fun n => by ring))
    _ = C * ∑' n, |a.val n| * (1 + ↑n) ^ k := by
        rw [show (fun n => |a.val n| * (C * (1 + ↑n) ^ k)) =
          fun n => C * (|a.val n| * (1 + ↑n) ^ k) from funext (fun n => by ring)]
        exact tsum_mul_left
    _ = C * RapidDecaySeq.rapidDecaySeminorm k a := rfl

/-- The backward map as a CLM. -/
def fromRapidDecayCLM : RapidDecaySeq →L[ℝ] SmoothCircle L where
  toLinearMap := fromRapidDecayLM
  cont := fromRapidDecay_continuous

/-- Backward then forward is the identity: if we construct a function from
rapidly decaying coefficients and take its Fourier coefficients, we get
back the original sequence. This follows from orthogonality. -/
theorem toRapidDecay_fromRapidDecay (a : RapidDecaySeq) :
    toRapidDecay (fromRapidDecay (L := L) a) = a := by
  apply RapidDecaySeq.ext; intro m
  show fourierCoeffReal m (fromRapidDecay a) = a.val m
  -- Key step: exchange sum and integral (justified by absolute convergence)
  -- fourierCoeffReal m (∑' n, a_n ψ_n) = ∑' n, a_n * fourierCoeffReal m (ψ_n)
  have key : fourierCoeffReal (L := L) m (fromRapidDecay a) =
      ∑' n, a.val n * fourierCoeffReal (L := L) m (fourierBasis n) := by
    open MeasureTheory in
    -- Unfold definitions
    simp only [fourierCoeffReal, fromRapidDecay, SmoothCircle.coe_mk, fourierBasis_apply]
    set μ := volume.restrict (Set.Icc (0 : ℝ) L)
    set M := max (1 / Real.sqrt L) (Real.sqrt (2 / L))
    -- Each a_n * (ψ_n · ψ_m) is integrable
    have h_int : ∀ n, Integrable (fun x => a.val n * (fourierBasisFun (L := L) n x *
        fourierBasisFun (L := L) m x)) μ :=
      fun n => (((fourierBasisFun_smooth (L := L) n).continuous.mul
        (fourierBasisFun_smooth m).continuous).const_smul (a.val n)).continuousOn.integrableOn_compact
        isCompact_Icc |>.integrable
    -- The sum ∑ ∫ ‖a_n * (ψ_n · ψ_m)‖ is finite
    have h_sum : Summable (fun n => ∫ x, ‖a.val n * (fourierBasisFun (L := L) n x *
        fourierBasisFun (L := L) m x)‖ ∂μ) := by
      apply Summable.of_nonneg_of_le
        (fun n => integral_nonneg (fun _ => norm_nonneg _))
      · intro n
        have h_bound : ∀ x, ‖a.val n * (fourierBasisFun (L := L) n x *
            fourierBasisFun (L := L) m x)‖ ≤ |a.val n| * (M * M) := by
          intro x
          simp only [norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul (fourierBasisFun_abs_le n x) (fourierBasisFun_abs_le m x)
              (abs_nonneg _) (le_max_of_le_right (Real.sqrt_nonneg _)))
            (abs_nonneg _)
        calc ∫ x, ‖a.val n * (fourierBasisFun (L := L) n x *
              fourierBasisFun (L := L) m x)‖ ∂μ
            ≤ ∫ _, |a.val n| * (M * M) ∂μ :=
              integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _))
                (integrable_const _) (ae_of_all _ h_bound)
          _ = |a.val n| * (M * M * L) := by
              rw [integral_const, smul_eq_mul]
              show μ.real Set.univ * _ = _
              rw [Measure.real, Measure.restrict_apply MeasurableSet.univ,
                Set.univ_inter, Real.volume_Icc, sub_zero,
                ENNReal.toReal_ofReal (le_of_lt hL.out)]
              ring
      · exact ((a.rapid_decay 0).congr (fun n => by
          show |a.val n| * (1 + (n : ℝ)) ^ 0 = |a.val n|; ring)).mul_right (M * M * L)
    -- Rewrite: (∑' n, a_n * ψ_n(x)) * ψ_m(x) = ∑' n, a_n * (ψ_n(x) * ψ_m(x))
    have h_rw : ∀ x, (∑' n, a.val n * fourierBasisFun (L := L) n x) *
        fourierBasisFun (L := L) m x =
        ∑' n, a.val n * (fourierBasisFun (L := L) n x * fourierBasisFun (L := L) m x) := by
      intro x; rw [← tsum_mul_right]; congr 1; funext n; ring
    simp_rw [h_rw]
    -- Exchange ∫ and ∑', then factor a_n out of each integral
    rw [← integral_tsum_of_summable_integral_norm h_int h_sum]
    congr 1; funext n
    exact integral_const_mul _ _
  rw [key]
  -- Use orthogonality: fourierCoeffReal m (ψ_n) = δ_{mn}
  simp_rw [fourierCoeffReal_fourierBasis]
  -- ∑' n, a_n * (if m = n then 1 else 0) = a_m
  have h_zero : ∀ n, n ≠ m → a.val n * (if m = n then (1 : ℝ) else 0) = 0 :=
    fun n hn => by rw [if_neg (Ne.symm hn), mul_zero]
  rw [tsum_eq_single m h_zero, if_pos rfl, mul_one]

/-! ## Fourier series convergence -/

/-- If all Fourier coefficients of a smooth periodic function are zero,
the function is zero. Follows from mapping to Mathlib's complex AddCircle L
and using the uniqueness of continuous functions with vanishing Fourier coefficients. -/
private theorem eq_zero_of_fourierCoeff_zero (g : SmoothCircle L)
    (h : ∀ n, fourierCoeffReal (L := L) n g = 0) : g = 0 := by
  -- Convert Set integrals to interval integrals
  have h_Icc_to_interval : ∀ f : ℝ → ℝ, ∫ x in Set.Icc (0:ℝ) L, f x = ∫ x in (0:ℝ)..L, f x := by
    intro f
    rw [intervalIntegral.integral_of_le (le_of_lt hL.out), MeasureTheory.integral_Icc_eq_integral_Ioc]
  -- Helper: extract vanishing of cos/sin integral from vanishing of a fourierCoeffReal
  -- using the factored form c · ∫ g·trig = 0 with c ≠ 0
  have h_extract_cos : ∀ m : ℕ, m > 0 →
      ∫ x in (0:ℝ)..L, g x * Real.cos (2 * Real.pi * m * x / L) = 0 := by
    intro m _
    have h' := h (2 * m - 1)
    unfold fourierCoeffReal fourierBasisFun at h'
    obtain ⟨n, hn⟩ : ∃ n, 2 * m - 1 = n + 1 := ⟨2 * m - 2, by omega⟩
    rw [hn] at h'; have hdiv : n / 2 + 1 = m := by omega
    have hmod : n % 2 = 0 := by omega
    simp only [hdiv, hmod, ite_true] at h'; rw [h_Icc_to_interval] at h'
    have h_rw : (fun x => g x * (Real.sqrt (2 / L) * Real.cos (2 * Real.pi * ↑m * x / L))) =
        fun x => Real.sqrt (2 / L) * (g x * Real.cos (2 * Real.pi * ↑m * x / L)) := by ext; ring
    rw [h_rw, intervalIntegral.integral_const_mul] at h'
    exact (mul_eq_zero.mp h').resolve_left (ne_of_gt (Real.sqrt_pos.mpr (div_pos two_pos hL.out)))
  have h_extract_sin : ∀ m : ℕ, m > 0 →
      ∫ x in (0:ℝ)..L, g x * Real.sin (2 * Real.pi * m * x / L) = 0 := by
    intro m _
    have h' := h (2 * m)
    unfold fourierCoeffReal fourierBasisFun at h'
    obtain ⟨n, hn⟩ : ∃ n, 2 * m = n + 1 := ⟨2 * m - 1, by omega⟩
    rw [hn] at h'
    have hdiv : n / 2 + 1 = m := by have := Nat.div_add_mod n 2; omega
    have h_odd : n % 2 = 1 := by omega
    have h_if : (n % 2 = 0) = False := by rw [h_odd]; decide
    simp only [hdiv, h_if, ite_false] at h'; rw [h_Icc_to_interval] at h'
    have h_rw : (fun x => g x * (Real.sqrt (2 / L) * Real.sin (2 * Real.pi * ↑m * x / L))) =
        fun x => Real.sqrt (2 / L) * (g x * Real.sin (2 * Real.pi * ↑m * x / L)) := by ext; ring
    rw [h_rw, intervalIntegral.integral_const_mul] at h'
    exact (mul_eq_zero.mp h').resolve_left (ne_of_gt (Real.sqrt_pos.mpr (div_pos two_pos hL.out)))
  -- Also the n=0 case
  have h_cos_zero : ∫ x in (0:ℝ)..L, g x * Real.cos (2 * Real.pi * 0 * x / L) = 0 := by
    have h' := h 0; unfold fourierCoeffReal fourierBasisFun at h'; rw [h_Icc_to_interval] at h'
    have h_rw : (fun x => g x * (1 / Real.sqrt L)) =
        fun x => (1 / Real.sqrt L) * (g x * Real.cos (2 * Real.pi * 0 * x / L)) := by
      ext x; rw [show (2 : ℝ) * Real.pi * 0 * x / L = 0 from by ring, Real.cos_zero, mul_one]; ring
    rw [h_rw, intervalIntegral.integral_const_mul] at h'
    exact (mul_eq_zero.mp h').resolve_left (ne_of_gt (div_pos one_pos (Real.sqrt_pos.mpr hL.out)))
  -- 1. Extend to all integers ℤ using cos even / sin odd
  have h_int_cos : ∀ m : ℤ, ∫ x in (0:ℝ)..L, g x * Real.cos (2 * Real.pi * (m : ℝ) * x / L) = 0 := by
    intro m; rcases m with k | k
    · rcases k with _ | k'
      · simpa using h_cos_zero
      · exact_mod_cast h_extract_cos (k' + 1) (by omega)
    · -- negSucc k: cos is even, so cos(2π(-k-1)x/L) = cos(2π(k+1)x/L)
      have : (fun x => g x * Real.cos (2 * Real.pi * (Int.negSucc k : ℝ) * x / L)) =
          fun x => g x * Real.cos (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * x / L) := by
        ext x; congr 1
        rw [show (Int.negSucc k : ℝ) = -((k + 1 : ℕ) : ℝ) from by push_cast; rfl,
          show 2 * Real.pi * -(↑(k + 1) : ℝ) * x / L = -(2 * Real.pi * (↑(k + 1) : ℝ) * x / L) from by ring,
          Real.cos_neg]
      rw [this]; exact_mod_cast h_extract_cos (k + 1) (by omega)
  have h_int_sin : ∀ m : ℤ, ∫ x in (0:ℝ)..L, g x * Real.sin (2 * Real.pi * (m : ℝ) * x / L) = 0 := by
    intro m; rcases m with k | k
    · rcases k with _ | k'
      · simp
      · exact_mod_cast h_extract_sin (k' + 1) (by omega)
    · -- negSucc k: sin is odd, so sin(2π(-k-1)x/L) = -sin(2π(k+1)x/L)
      have : (fun x => g x * Real.sin (2 * Real.pi * (Int.negSucc k : ℝ) * x / L)) =
          fun x => -(g x * Real.sin (2 * Real.pi * ((k + 1 : ℕ) : ℝ) * x / L)) := by
        ext x
        rw [show (Int.negSucc k : ℝ) = -((k + 1 : ℕ) : ℝ) from by push_cast; rfl,
          show 2 * Real.pi * -(↑(k + 1) : ℝ) * x / L = -(2 * Real.pi * (↑(k + 1) : ℝ) * x / L) from by ring,
          Real.sin_neg]; ring
      rw [this, intervalIntegral.integral_neg, h_extract_sin (k + 1) (by omega), neg_zero]
  -- 2. Lift to Mathlib's complex C(AddCircle L, ℂ) representation
  let g_val : ℝ → ℂ := fun x => (g x : ℂ)
  have hper : Function.Periodic g_val L := fun x => by simp [g_val, g.periodic x]
  let g_lift : C(AddCircle L, ℂ) :=
    ⟨hper.lift, continuous_coinduced_dom.2 (Complex.continuous_ofReal.comp g.continuous)⟩
  -- 3. Show Mathlib's complex Fourier coefficients are all zero
  have h_coeff : ∀ m : ℤ, fourierCoeff (⇑g_lift) m = 0 := by
    intro m
    rw [fourierCoeff_eq_intervalIntegral (⇑g_lift) m 0, zero_add]
    simp only [g_lift, ContinuousMap.coe_mk, Function.Periodic.lift_coe]
    -- Suffices: the integral is zero
    suffices h_z : ∫ x in (0:ℝ)..L, fourier (-m) (x : AddCircle L) • g_val x = 0 by
      rw [h_z, smul_zero]
    -- Expand via Euler's formula: e^{-2πimx/L} = cos - i·sin
    have h_eq : (fun x : ℝ => fourier (-m) (x : AddCircle L) • g_val x) =
        fun x => ↑(g x * Real.cos (2 * Real.pi * (m : ℝ) * x / L)) -
          Complex.I * ↑(g x * Real.sin (2 * Real.pi * (m : ℝ) * x / L)) := by
      ext x; show fourier (-m) (x : AddCircle L) • (g x : ℂ) = _
      rw [fourier_coe_apply, smul_eq_mul, mul_comm]
      have harg : 2 * ↑Real.pi * Complex.I * ((-m : ℤ) : ℂ) * ↑x / ↑L =
          ↑(-(2 * Real.pi * (m : ℝ) * x / L)) * Complex.I := by push_cast; ring
      rw [harg, Complex.exp_mul_I]
      simp only [Complex.ofReal_neg, Complex.cos_neg, Complex.sin_neg,
        Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_mul]
      ring
    rw [h_eq]
    have hC1 : Continuous (fun x => (↑(g x * Real.cos (2 * Real.pi * ↑m * x / L)) : ℂ)) :=
      Complex.continuous_ofReal.comp (g.continuous.mul (by fun_prop))
    have hC2 : Continuous (fun x => Complex.I * (↑(g x * Real.sin (2 * Real.pi * ↑m * x / L)) : ℂ)) :=
      continuous_const.mul (Complex.continuous_ofReal.comp (g.continuous.mul (by fun_prop)))
    rw [intervalIntegral.integral_sub (hC1.intervalIntegrable _ _) (hC2.intervalIntegrable _ _),
      show (fun x => Complex.I * (↑(g x * Real.sin (2 * Real.pi * ↑m * x / L)) : ℂ)) =
        fun x => Complex.I • (↑(g x * Real.sin (2 * Real.pi * ↑m * x / L)) : ℂ) from by ext; rfl,
      intervalIntegral.integral_smul,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal,
      h_int_cos m, h_int_sin m]
    simp
  -- 4. Apply Mathlib's uniformly convergent Fourier series to conclude g_lift = 0
  have h_summable : Summable (fourierCoeff (⇑g_lift)) := by
    have : fourierCoeff (⇑g_lift) = fun _ => 0 := funext h_coeff
    rw [this]; exact summable_zero
  have h_sum := hasSum_fourier_series_of_summable h_summable
  have h0 : ∀ i : ℤ, fourierCoeff (⇑g_lift) i • (fourier i : C(AddCircle L, ℂ)) =
      (0 : C(AddCircle L, ℂ)) := fun i => by rw [h_coeff, zero_smul]
  simp_rw [h0] at h_sum
  have g_lift_eq_zero : g_lift = 0 := h_sum.unique hasSum_zero
  -- 5. Since g_lift is globally zero, g is globally zero
  ext x
  have : g_lift (x : AddCircle L) = 0 := by rw [g_lift_eq_zero]; rfl
  exact Complex.ofReal_eq_zero.mp this

/-- **Fourier series expansion**: every smooth periodic function equals the
sum of its Fourier series `∑ₙ c_n(f) · ψ_n` in the seminorm topology. -/
theorem hasSum_fourierBasis (f : SmoothCircle L) :
    f = fromRapidDecay (toRapidDecay f) := by
  -- Suffices: g := f - fromRapidDecay(toRapidDecay f) = 0
  suffices h : f - fromRapidDecay (toRapidDecay f) = 0 from eq_of_sub_eq_zero h
  apply eq_zero_of_fourierCoeff_zero
  intro n
  -- fourierCoeffReal is a linear map, so fourierCoeffReal n (f - h) = c_n(f) - c_n(h)
  show (fourierCoeffLM (L := L) n) (f - fromRapidDecay (toRapidDecay f)) = 0
  rw [map_sub]
  -- c_n(fromRapidDecay(toRapidDecay f)) = (toRapidDecay(fromRapidDecay(toRapidDecay f))).val n
  --                                     = (toRapidDecay f).val n = c_n(f)
  have key : fourierCoeffReal (L := L) n (fromRapidDecay (toRapidDecay f)) =
      fourierCoeffReal n f := by
    show (toRapidDecay (fromRapidDecay (L := L) (toRapidDecay f))).val n = fourierCoeffReal n f
    rw [toRapidDecay_fromRapidDecay]; rfl
  simp [fourierCoeffLM, key]

/-! ## Continuous linear equivalence -/

/-- Forward then backward is the identity: if we take Fourier coefficients
and reconstruct, we get back the original function. -/
theorem fromRapidDecay_toRapidDecay (f : SmoothCircle L) :
    fromRapidDecay (toRapidDecay f) = f :=
  (hasSum_fourierBasis f).symm

/-- The continuous linear equivalence between `SmoothCircle L` and `RapidDecaySeq`
via the real Fourier transform. -/
def smoothCircleRapidDecayEquiv : SmoothCircle L ≃L[ℝ] RapidDecaySeq where
  toLinearMap := toRapidDecayLM
  invFun := fromRapidDecay
  left_inv f := fromRapidDecay_toRapidDecay f
  right_inv a := toRapidDecay_fromRapidDecay a
  continuous_toFun := toRapidDecay_continuous
  continuous_invFun := fromRapidDecay_continuous

/-! ## DyninMityaginSpace instance -/

end SmoothCircle

/-- **C∞(S¹) is a nuclear Fréchet space.**

The instance uses the Sobolev sup-seminorm family `k ↦ p_k` and a
basis/coefficient system derived from the topological isomorphism
`SmoothCircle L ≃L[ℝ] RapidDecaySeq` constructed from the real Fourier basis.

This enables Gaussian fields on the torus T¹ = ℝ/Lℤ and (via tensor products)
on cylinders S¹×ℝ and higher tori Tᵈ. -/
noncomputable instance smoothCircle_dyninMityaginSpace :
    DyninMityaginSpace (SmoothCircle L) :=
  DyninMityaginSpace.ofRapidDecayEquiv
    SmoothCircle.sobolevSeminorm
    SmoothCircle.smoothCircle_withSeminorms
    SmoothCircle.smoothCircleRapidDecayEquiv

end GaussianField
