/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# 1D Lattice Heat Kernel Convergence

Proves that the lattice heat kernel on ℤ/Nℤ converges to the continuum
heat kernel on S¹_L as N → ∞.

## Main results

- `latticeEigenvalue1d_tendsto` — eigenvalue convergence: (4N²/L²)sin²(πk/N) → (2πk/L)²
- `latticeDFTCoeff1d_tendsto` — DFT coefficient convergence via Riemann sums
- `latticeEigenvalue1d_ge_8m` — eigenvalue lower bound via Jordan's inequality

## Mathematical background

On the 1D lattice ℤ/Nℤ with spacing a = L/N, the Laplacian eigenvalues are:

  `λ_k = (4/a²) sin²(πk/N) = (2πk/L)² · sinc²(πk/N)`

As N → ∞, `sinc(πk/N) → 1`, so `λ_k → (2πk/L)²` = continuum eigenvalue.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Lattice.HeatKernel
import SmoothCircle.Restriction
import SmoothCircle.Eigenvalues
import SmoothCircle.Nuclear
import HeatKernel.Bilinear

noncomputable section

namespace GaussianField

open Filter Real Matrix

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## 1D lattice heat kernel bilinear form -/

/-- **1D lattice heat kernel bilinear form applied to circle test functions.**

  `K_t^N(f, g) = Σ_x (r_N f)(x) · (K_t · r_N g)(x)`

where `r_N` is the circle restriction map with √(L/N) normalization. -/
def latticeHeatKernelBilinear1d (N : ℕ) [NeZero N] (t : ℝ)
    (f g : SmoothMap_Circle L ℝ) : ℝ :=
  let a := circleSpacing L N
  let fN : FinLatticeField 1 N := fun x => circleRestriction L N f (x 0)
  let gN : FinLatticeField 1 N := fun x => circleRestriction L N g (x 0)
  let KgN := (latticeHeatKernelMatrix 1 N a t).mulVec gN
  ∑ x : FinLatticeSites 1 N, fN x * KgN x

/-! ## Eigenvalue convergence -/

/-- `1/(N+1) → 0` as `N → ∞`. -/
private theorem tendsto_inv_succ :
    Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) atTop (nhds 0) := by
  simp_rw [one_div]
  apply Filter.Tendsto.comp tendsto_inv_atTop_zero
  apply Filter.Tendsto.atTop_add
  · exact tendsto_natCast_atTop_atTop (R := ℝ)
  · exact tendsto_const_nhds

/-- `c/(N+1) → 0` as `N → ∞` for any constant c. -/
private theorem tendsto_const_div_succ (c : ℝ) :
    Tendsto (fun N : ℕ => c / ((N : ℝ) + 1)) atTop (nhds 0) := by
  have h := tendsto_inv_succ
  simp_rw [show ∀ N : ℕ, c / ((N : ℝ) + 1) = c * (1 / ((N : ℝ) + 1)) from
    fun N => by ring]
  rw [show (0 : ℝ) = c * 0 from by ring]
  exact h.const_mul c

/-- **Eigenvalue convergence: lattice → continuum as N → ∞.**

For each fixed frequency k ≥ 0, the 1D lattice Laplacian eigenvalue
converges to the continuum circle eigenvalue:

  `(4(N+1)²/L²) sin²(πk/(N+1)) → (2πk/L)²`

For k = 0: both sides are 0.
For k > 0: write `sin²(x) = x² · sinc²(x)` and use `sinc(0) = 1`. -/
theorem latticeEigenvalue1d_tendsto (k : ℕ) :
    Tendsto
      (fun N : ℕ => (4 * ((N : ℝ) + 1) ^ 2 / L ^ 2) *
        sin (π * k / ((N : ℝ) + 1)) ^ 2)
      atTop
      (nhds ((2 * π * k / L) ^ 2)) := by
  by_cases hk : k = 0
  · -- k = 0: both sides are 0
    subst hk; simp [sin_zero]
  · -- k > 0: use sinc
    -- Let x_N = π*k/(N+1). We have sin(x_N) = x_N * sinc(x_N), so
    -- sin(x_N)² = x_N² * sinc(x_N)² and
    -- (4(N+1)²/L²) * x_N² = (4(N+1)²/L²) * (πk/(N+1))² = (2πk/L)²
    -- Hence the sequence equals (2πk/L)² * sinc(x_N)² → (2πk/L)² * 1
    have hk' : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
    -- Rewrite using sinc: for x ≠ 0, sin(x) = x * sinc(x)
    have hxN : ∀ N : ℕ, π * (k : ℝ) / ((N : ℝ) + 1) ≠ 0 := by
      intro N; positivity
    -- Show the sequence equals (2πk/L)² * sinc(πk/(N+1))²
    suffices hsuff : Tendsto
        (fun N : ℕ => (2 * π * (k : ℝ) / L) ^ 2 *
          sinc (π * k / ((N : ℝ) + 1)) ^ 2)
        atTop (nhds ((2 * π * k / L) ^ 2)) by
      refine hsuff.congr (fun N => ?_)
      -- Need: (4(N+1)²/L²) * sin(πk/(N+1))² = (2πk/L)² * sinc(πk/(N+1))²
      rw [sinc_of_ne_zero (hxN N)]
      have hN1 : ((N : ℝ) + 1) ≠ 0 := by positivity
      have hL' : L ≠ 0 := ne_of_gt hL.out
      field_simp
      ring
    -- Now show (2πk/L)² * sinc(πk/(N+1))² → (2πk/L)²
    -- Since sinc(πk/(N+1)) → sinc(0) = 1 and sinc²(.) → 1² = 1
    conv => rhs; rw [show (2 * π * (k : ℝ) / L) ^ 2 =
        (2 * π * k / L) ^ 2 * sinc 0 ^ 2 from by rw [sinc_zero]; ring]
    apply Tendsto.const_mul
    apply Tendsto.pow
    -- sinc(πk/(N+1)) → sinc(0) as N → ∞
    exact (continuous_sinc.tendsto 0).comp (tendsto_const_div_succ (π * k))

/-! ## Lattice real Fourier basis and DFT coefficients -/

/-- The lattice real Fourier basis function on ℤ/Nℤ.

Mirrors the continuum `fourierBasisFun` but on the discrete lattice:
- Index 0: `1/√N` (constant)
- Index 2k-1 (k ≥ 1): `√(2/N) · cos(2πk·val/N)` (cosine)
- Index 2k (k ≥ 1): `√(2/N) · sin(2πk·val/N)` (sine) -/
def latticeFourierBasisFun (N : ℕ) : ℕ → ZMod N → ℝ
  | 0 => fun _ => 1 / Real.sqrt N
  | n + 1 =>
    let k := (n / 2 + 1 : ℕ)
    if n % 2 = 0 then
      fun z => Real.sqrt (2 / N) * Real.cos (2 * π * k * (ZMod.val z : ℝ) / N)
    else
      fun z => Real.sqrt (2 / N) * Real.sin (2 * π * k * (ZMod.val z : ℝ) / N)

/-- The lattice Fourier basis functions are uniformly bounded by `√(2/N)`. -/
private theorem latticeFourierBasisFun_abs_le (N : ℕ) [NeZero N] (m : ℕ) (z : ZMod N) :
    |latticeFourierBasisFun N m z| ≤ Real.sqrt (2 / N) := by
  cases m with
  | zero =>
    simp only [latticeFourierBasisFun]
    rw [abs_of_nonneg (by positivity)]
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    rw [div_le_iff₀ (Real.sqrt_pos_of_pos hN_pos)]
    calc 1 = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt 2 := Real.sqrt_le_sqrt (by norm_num)
      _ = Real.sqrt (2 / ↑N) * Real.sqrt ↑N := by
          rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 / ↑N),
            show (2 : ℝ) / ↑N * ↑N = 2 from by field_simp]
  | succ n =>
    simp only [latticeFourierBasisFun]; split
    · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc Real.sqrt (2 / ↑N) * |Real.cos _|
          ≤ Real.sqrt (2 / ↑N) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.sqrt_nonneg _)
        _ = Real.sqrt (2 / ↑N) := mul_one _
    · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc Real.sqrt (2 / ↑N) * |Real.sin _|
          ≤ Real.sqrt (2 / ↑N) * 1 :=
            mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (Real.sqrt_nonneg _)
        _ = Real.sqrt (2 / ↑N) := mul_one _

/-- **DFT coefficient of a restricted circle function at mode m.**

The inner product of the restricted function with the m-th lattice
Fourier basis function. For m ≥ N, this is 0 (no lattice mode).

The √(L/N) normalization in `circleRestriction` combined with the
1/√N normalization in `latticeFourierBasisFun` ensures these approximate
the continuum Fourier coefficients `DyninMityaginSpace.coeff m f`. -/
def latticeDFTCoeff1d (N : ℕ) [NeZero N]
    (f : SmoothMap_Circle L ℝ) (m : ℕ) : ℝ :=
  if m < N then
    ∑ z : ZMod N,
      circleRestriction L N f z * latticeFourierBasisFun N m z
  else 0

/-- DFT coefficients vanish beyond the lattice cutoff. -/
theorem latticeDFTCoeff1d_zero_of_ge (N : ℕ) [NeZero N]
    (f : SmoothMap_Circle L ℝ) (m : ℕ) (hm : N ≤ m) :
    latticeDFTCoeff1d L N f m = 0 := by
  unfold latticeDFTCoeff1d
  rw [if_neg (not_lt.mpr hm)]

/-- **Flat uniform bound on DFT coefficients.**

The lattice DFT coefficient is a sum of N terms, each bounded by
`√(L/N) · ‖f‖_C⁰ · √(2/N)`. Summing gives `N · √(L/N) · √(2/N) = √(2L)`.

This bound is uniform in both N and m, providing a dominating function
for dominated convergence when combined with eigenvalue decay. -/
theorem latticeDFTCoeff1d_flat_bound (f : SmoothMap_Circle L ℝ) :
    ∀ N m, |latticeDFTCoeff1d L (N + 1) f m| ≤
      Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 0 f := by
  intro N m
  by_cases hm : m < N + 1
  · simp only [latticeDFTCoeff1d, if_pos hm]
    set M := N + 1 with hM_def
    have hM_pos : (0 : ℝ) < M := by positivity
    have h_term : ∀ z : ZMod M,
        |circleRestriction L M f z * latticeFourierBasisFun M m z| ≤
        Real.sqrt (L / M) * SmoothMap_Circle.sobolevSeminorm 0 f *
          Real.sqrt (2 / M) := by
      intro z; rw [abs_mul]
      have h_cr : |circleRestriction L M f z| ≤
          Real.sqrt (L / M) * SmoothMap_Circle.sobolevSeminorm 0 f := by
        rw [circleRestriction_apply, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        have h := SmoothMap_Circle.norm_iteratedDeriv_le_sobolevSeminorm' f 0
          (circlePoint L M z)
        simp only [iteratedDeriv_zero] at h
        rwa [Real.norm_eq_abs] at h
      exact mul_le_mul h_cr (latticeFourierBasisFun_abs_le M m z) (abs_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg _)
          (SmoothMap_Circle.sobolevSeminorm_nonneg 0 f))
    calc |∑ z : ZMod M,
            circleRestriction L M f z * latticeFourierBasisFun M m z|
        ≤ ∑ z : ZMod M,
            |circleRestriction L M f z * latticeFourierBasisFun M m z| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : ZMod M,
            (Real.sqrt (L / M) * SmoothMap_Circle.sobolevSeminorm 0 f *
              Real.sqrt (2 / M)) :=
          Finset.sum_le_sum (fun z _ => h_term z)
      _ = ↑M * (Real.sqrt (L / ↑M) * SmoothMap_Circle.sobolevSeminorm 0 f *
            Real.sqrt (2 / ↑M)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          congr 1
          rw [show Finset.univ.card = (M : ℕ) from ZMod.card M]
      _ = ↑M * (Real.sqrt (L / ↑M) * Real.sqrt (2 / ↑M)) *
            SmoothMap_Circle.sobolevSeminorm 0 f := by ring
      _ = Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 0 f := by
          congr 1
          rw [← Real.sqrt_mul (div_nonneg hL.out.le hM_pos.le)]
          rw [show L / ↑M * (2 / ↑M) = 2 * L / ↑M ^ 2 from by
            field_simp]
          rw [Real.sqrt_div (by linarith [hL.out] : (0 : ℝ) ≤ 2 * L)]
          rw [Real.sqrt_sq hM_pos.le]; field_simp
  · rw [latticeDFTCoeff1d_zero_of_ge L (N + 1) f m (by omega), abs_zero]
    exact mul_nonneg (Real.sqrt_nonneg _)
      (SmoothMap_Circle.sobolevSeminorm_nonneg 0 f)

/-! ## Explicit 1D lattice eigenvalues -/

/-- The 1D lattice Laplacian eigenvalue at mode m, using `fourierFreq` indexing.

`λ_m = (4/a²) sin²(π · fourierFreq(m) / N)`

This matches the continuum ordering where modes are:
constant, cos(2πx/L), sin(2πx/L), cos(4πx/L), ... -/
def latticeEigenvalue1d (N : ℕ) (a : ℝ) (m : ℕ) : ℝ :=
  (4 / a ^ 2) * sin (π * (SmoothMap_Circle.fourierFreq m : ℝ) / N) ^ 2

/-- Eigenvalue at mode 0 is 0 (constant mode has zero Laplacian eigenvalue). -/
theorem latticeEigenvalue1d_zero (N : ℕ) (a : ℝ) :
    latticeEigenvalue1d N a 0 = 0 := by
  simp [latticeEigenvalue1d, SmoothMap_Circle.fourierFreq, sin_zero]

/-- 1D lattice eigenvalues are nonneg. -/
theorem latticeEigenvalue1d_nonneg (N : ℕ) (a : ℝ) (m : ℕ) :
    0 ≤ latticeEigenvalue1d N a m := by
  unfold latticeEigenvalue1d
  apply mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)

/-- **1D lattice eigenvalue converges to continuum eigenvalue.**

Proved from `latticeEigenvalue1d_tendsto` applied to `fourierFreq(m)`. -/
theorem latticeEigenvalue1d_tendsto_continuum (m : ℕ) :
    Tendsto (fun N : ℕ =>
      latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m)
      atTop (nhds (HasLaplacianEigenvalues.eigenvalue
        (E := SmoothMap_Circle L ℝ) m)) := by
  simp only [latticeEigenvalue1d, circleSpacing,
    circleHasLaplacianEigenvalues]
  -- (4 / (L/(N+1))²) * sin²(π·freq/((N+1))) → (2π·freq/L)²
  -- = (4(N+1)²/L²) * sin²(π·freq/(N+1)) → (2π·freq/L)²
  -- which is exactly latticeEigenvalue1d_tendsto applied to k = fourierFreq m
  have h := latticeEigenvalue1d_tendsto L (SmoothMap_Circle.fourierFreq m)
  convert h using 1
  ext N
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  have hL' : L ≠ 0 := ne_of_gt hL.out
  field_simp
  push_cast
  ring

/-! ## Eigenvalue lower bound via Jordan's inequality -/

/-- For `m ≥ 1`, the `fourierFreq` squared is at least `m/2`.

Since `fourierFreq m = (m-1)/2 + 1` for `m ≥ 1`, we have
`2 · fourierFreq m ≥ m` and `fourierFreq m ≥ 1`, giving
`fourierFreq(m)² ≥ fourierFreq(m) ≥ m/2`. -/
private theorem fourierFreq_sq_ge_half (m : ℕ) (hm : 1 ≤ m) :
    (m : ℝ) / 2 ≤ (SmoothMap_Circle.fourierFreq m : ℝ) ^ 2 := by
  have h_freq_ge_1 : (1 : ℝ) ≤ (SmoothMap_Circle.fourierFreq m : ℝ) := by
    have : 1 ≤ SmoothMap_Circle.fourierFreq m := by
      cases m with
      | zero => omega
      | succ n => simp only [SmoothMap_Circle.fourierFreq]; omega
    exact_mod_cast this
  have h2 : (m : ℝ) ≤ 2 * (SmoothMap_Circle.fourierFreq m : ℝ) := by
    have : m ≤ 2 * SmoothMap_Circle.fourierFreq m := by
      cases m with
      | zero => omega
      | succ n => simp only [SmoothMap_Circle.fourierFreq]; omega
    exact_mod_cast this
  calc (m : ℝ) / 2
      ≤ (SmoothMap_Circle.fourierFreq m : ℝ) := by linarith
    _ ≤ (SmoothMap_Circle.fourierFreq m : ℝ) ^ 2 := by
        rw [sq]; exact le_mul_of_one_le_left (by linarith) h_freq_ge_1

/-- **Eigenvalue lower bound via Jordan's inequality.**

For `m ≥ 1`, the lattice eigenvalue satisfies `λ_m ≥ 8m/L²`, uniformly in N.

Proof chain:
1. Jordan: `sin(πj/M) ≥ 2j/M` for `j ≤ M/2`
2. Square: `sin²(πj/M) ≥ 4j²/M²`
3. Multiply: `(4M²/L²) · sin²(πj/M) ≥ 16j²/L²`
4. Use `fourierFreq(m)² ≥ m/2`: `16j²/L² ≥ 8m/L²` -/
theorem latticeEigenvalue1d_ge_8m (N m : ℕ) (hm : 1 ≤ m)
    (hm_lt : m < N + 1) :
    8 * (m : ℝ) / L ^ 2 ≤
    latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m := by
  unfold latticeEigenvalue1d
  push_cast [circleSpacing]
  set M := (N : ℝ) + 1
  set j := (SmoothMap_Circle.fourierFreq m : ℝ)
  have hM_pos : 0 < M := by positivity
  have hL' : 0 < L := hL.out
  have h_coeff : 4 / (L / M) ^ 2 = 4 * M ^ 2 / L ^ 2 := by field_simp
  rw [h_coeff]
  have hj_pos : 0 < j := by
    show 0 < (SmoothMap_Circle.fourierFreq m : ℝ)
    have : 1 ≤ SmoothMap_Circle.fourierFreq m := by
      cases m with
      | zero => omega
      | succ n => simp only [SmoothMap_Circle.fourierFreq]; omega
    positivity
  have hj_le_half : j ≤ M / 2 := by
    show (SmoothMap_Circle.fourierFreq m : ℝ) ≤ ((N : ℝ) + 1) / 2
    have h_nat : SmoothMap_Circle.fourierFreq m ≤ (N + 1) / 2 := by
      cases m with
      | zero => omega
      | succ n => simp only [SmoothMap_Circle.fourierFreq]; omega
    calc (SmoothMap_Circle.fourierFreq m : ℝ)
        ≤ ((N + 1) / 2 : ℕ) := by exact_mod_cast h_nat
      _ ≤ ((N : ℝ) + 1) / 2 := by
          have h := Nat.div_mul_le_self (N + 1) 2
          have : (↑((N + 1) / 2) : ℝ) * 2 ≤ ↑(N + 1) := by exact_mod_cast h
          push_cast at this ⊢; linarith
  have harg : 0 ≤ π * j / M := by positivity
  have harg_le : π * j / M ≤ π / 2 := by
    rw [div_le_div_iff₀ hM_pos (by norm_num : (0:ℝ) < 2)]
    nlinarith [pi_pos]
  have hjordan : 2 / π * (π * j / M) ≤ sin (π * j / M) :=
    mul_le_sin harg harg_le
  have hsin_sq : (2 * j / M) ^ 2 ≤ sin (π * j / M) ^ 2 := by
    have : 2 / π * (π * j / M) = 2 * j / M := by field_simp
    rw [← this, sq, sq]
    exact mul_self_le_mul_self (by positivity) hjordan
  have h_freq_sq : (m : ℝ) / 2 ≤ j ^ 2 := by
    show (m : ℝ) / 2 ≤ (SmoothMap_Circle.fourierFreq m : ℝ) ^ 2
    exact fourierFreq_sq_ge_half m hm
  calc 8 * (m : ℝ) / L ^ 2
      = 16 * ((m : ℝ) / 2) / L ^ 2 := by ring
    _ ≤ 16 * j ^ 2 / L ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg L)
        linarith [h_freq_sq]
    _ = 4 * M ^ 2 / L ^ 2 * (2 * j / M) ^ 2 := by
        field_simp; ring
    _ ≤ 4 * M ^ 2 / L ^ 2 * sin (π * j / M) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hsin_sq; positivity

/-! ## Spectral expansion -/

/-- **Lattice heat kernel bilinear form equals the Mathlib spectral expansion.**

Uses `bilinear_exp_eq_spectral` applied to the negative Laplacian matrix.
The eigenvectors and eigenvalues are from Mathlib's abstract spectral theorem. -/
theorem latticeHeatKernelBilinear1d_eq_mathlib_spectral (N : ℕ) [NeZero N] (t : ℝ)
    (f g : SmoothMap_Circle L ℝ) :
    let a := circleSpacing L N
    let hM := negLaplacianMatrix_isHermitian 1 N a
    let fN : FinLatticeSites 1 N → ℝ := fun x => circleRestriction L N f (x 0)
    let gN : FinLatticeSites 1 N → ℝ := fun x => circleRestriction L N g (x 0)
    latticeHeatKernelBilinear1d L N t f g =
    ∑ k : FinLatticeSites 1 N,
      Real.exp (-t * hM.eigenvalues k) *
      (∑ x, (hM.eigenvectorBasis k : EuclideanSpace ℝ (FinLatticeSites 1 N)) x * fN x) *
      (∑ x, (hM.eigenvectorBasis k : EuclideanSpace ℝ (FinLatticeSites 1 N)) x * gN x) := by
  intro a hM fN gN
  unfold latticeHeatKernelBilinear1d latticeHeatKernelMatrix
  exact Matrix.IsHermitian.bilinear_exp_eq_spectral hM t fN gN

/-! ## Coefficient convergence (Riemann sum) -/

/-- **Normalization identity**: the product of circle restriction and lattice
Fourier basis equals (L/N) times the product of the original function with
the continuum Fourier basis, both evaluated at the lattice point. -/
private theorem restriction_times_latticeBasis
    (N : ℕ) [NeZero N] (f : SmoothMap_Circle L ℝ) (m : ℕ) (_hm : m < N)
    (z : ZMod N) :
    circleRestriction L N f z * latticeFourierBasisFun N m z =
    (L / N) * (f (circlePoint L N z) *
      SmoothMap_Circle.fourierBasisFun (L := L) m (circlePoint L N z)) := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hL' : L ≠ 0 := ne_of_gt hL.out
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have sqrt_factor (c : ℝ) (_hc : 0 ≤ c) :
      Real.sqrt (L / N) * Real.sqrt (c / N) = L / N * Real.sqrt (c / L) := by
    rw [← Real.sqrt_mul (div_nonneg hL.out.le hN_pos.le)]
    have : L / ↑N * (c / ↑N) = (L / ↑N) ^ 2 * (c / L) := by field_simp
    rw [this, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq (div_nonneg hL.out.le hN_pos.le)]
  -- Key: √(L/N) * (1/√N) = (L/N) * (1/√L)
  have sqrt_factor_one :
      Real.sqrt (L / ↑N) * (1 / Real.sqrt ↑N) = L / ↑N * (1 / Real.sqrt L) := by
    have h1 : (1 : ℝ) / Real.sqrt ↑N = Real.sqrt (1 / ↑N) := by
      rw [one_div, one_div, ← Real.sqrt_inv]
    have h2 : (1 : ℝ) / Real.sqrt L = Real.sqrt (1 / L) := by
      rw [one_div, one_div, ← Real.sqrt_inv]
    rw [h1, sqrt_factor 1 (by norm_num), h2]
  -- Key: arg rewrite for trig arguments
  have arg_eq (k : ℕ) : 2 * π * ↑k * (ZMod.val z : ℝ) / ↑N =
      2 * π * ↑k * circlePoint L N z / L := by
    simp only [circlePoint]; field_simp
  rcases m with _ | n
  · -- m = 0: √(L/N) * f(pt) * (1/√N) = (L/N) * (f(pt) * (1/√L))
    simp only [circleRestriction_apply, circleSpacing_eq,
      latticeFourierBasisFun, SmoothMap_Circle.fourierBasisFun]
    calc Real.sqrt (L / ↑N) * f (circlePoint L N z) * (1 / Real.sqrt ↑N)
        = (Real.sqrt (L / ↑N) * (1 / Real.sqrt ↑N)) * f (circlePoint L N z) := by ring
      _ = (L / ↑N * (1 / Real.sqrt L)) * f (circlePoint L N z) := by
            rw [sqrt_factor_one]
      _ = L / ↑N * (f (circlePoint L N z) * (1 / Real.sqrt L)) := by ring
  · -- m = n+1
    simp only [circleRestriction_apply, circleSpacing_eq,
      latticeFourierBasisFun, SmoothMap_Circle.fourierBasisFun]
    -- The goal has unapplied lambdas inside if-then-else; split_ifs to resolve
    split_ifs with h
    · -- cosine case: n % 2 = 0
      -- LHS: √(L/N) * f(pt) * (√(2/N) * cos(2πk·val/N))
      -- RHS: (L/N) * (f(pt) * (√(2/L) * cos(2πk·pt/L)))
      simp only [arg_eq]
      calc Real.sqrt (L / ↑N) * f (circlePoint L N z) *
            (Real.sqrt (2 / ↑N) * cos (2 * π * ↑(n / 2 + 1) * circlePoint L N z / L))
          = (Real.sqrt (L / ↑N) * Real.sqrt (2 / ↑N)) *
            (f (circlePoint L N z) * cos (2 * π * ↑(n / 2 + 1) * circlePoint L N z / L)) := by ring
        _ = (L / ↑N * Real.sqrt (2 / L)) *
            (f (circlePoint L N z) * cos (2 * π * ↑(n / 2 + 1) * circlePoint L N z / L)) := by
              rw [sqrt_factor 2 (by norm_num)]
        _ = L / ↑N * (f (circlePoint L N z) *
            (Real.sqrt (2 / L) * cos (2 * π * ↑(n / 2 + 1) * circlePoint L N z / L))) := by ring
    · -- sine case: n % 2 ≠ 0
      simp only [arg_eq]
      calc Real.sqrt (L / ↑N) * f (circlePoint L N z) *
            (Real.sqrt (2 / ↑N) * sin (2 * π * ↑(n / 2 + 1) * circlePoint L N z / L))
          = (Real.sqrt (L / ↑N) * Real.sqrt (2 / ↑N)) *
            (f (circlePoint L N z) * sin (2 * π * ↑(n / 2 + 1) * circlePoint L N z / L)) := by ring
        _ = (L / ↑N * Real.sqrt (2 / L)) *
            (f (circlePoint L N z) * sin (2 * π * ↑(n / 2 + 1) * circlePoint L N z / L)) := by
              rw [sqrt_factor 2 (by norm_num)]
        _ = L / ↑N * (f (circlePoint L N z) *
            (Real.sqrt (2 / L) * sin (2 * π * ↑(n / 2 + 1) * circlePoint L N z / L))) := by ring

/-- The lattice DFT coefficient equals a Riemann sum of f times fourierBasisFun. -/
private theorem latticeDFTCoeff1d_eq_riemann_sum
    (N : ℕ) [NeZero N] (f : SmoothMap_Circle L ℝ) (m : ℕ) (hm : m < N) :
    latticeDFTCoeff1d L N f m =
    ∑ z : ZMod N, (L / N) * (f (circlePoint L N z) *
      SmoothMap_Circle.fourierBasisFun (L := L) m (circlePoint L N z)) := by
  simp only [latticeDFTCoeff1d, if_pos hm]
  congr 1; ext z
  exact restriction_times_latticeBasis L N f m hm z

/-- **Riemann sum convergence for continuous periodic functions on [0, L].**

The left-endpoint Riemann sum with N+1 equally spaced points on [0, L]
converges to the integral as N → ∞. This follows from uniform continuity
of g on the compact interval [0, L]:

- Get δ from uniform continuity for tolerance ε/L
- For N large enough, spacing L/(N+1) < δ
- On each subinterval [ka, (ka+a)], |g(x) - g(ka)| < ε/L
- Total error = Σ_k |∫_{ka}^{(k+1)a} (g(x) - g(ka)) dx| ≤ (N+1) · a · (ε/L) = ε -/
theorem riemann_sum_periodic_tendsto
    (g : ℝ → ℝ) (hg : Continuous g) (_hper : Function.Periodic g L) :
    Tendsto (fun N : ℕ =>
      ∑ k ∈ Finset.range (N + 1),
        (L / (↑(N + 1) : ℝ)) * g (↑k * L / (↑(N + 1) : ℝ)))
      atTop (nhds (∫ x in Set.Icc 0 L, g x)) := by
  have hL_pos : (0 : ℝ) < L := hL.out
  have hL_ne : L ≠ 0 := ne_of_gt hL_pos
  -- Convert ∫ x in Set.Icc 0 L to interval integral ∫ x in (0:ℝ)..L
  have icc_eq : ∫ x in Set.Icc 0 L, g x = ∫ x in (0 : ℝ)..L, g x := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hL_pos.le]
  rw [icc_eq]
  -- Use Metric.tendsto_atTop: suffices to show for all ε > 0, eventually close
  rw [Metric.tendsto_atTop]
  intro ε hε
  -- Step 1: Uniform continuity of g on [0, L] (Heine-Cantor)
  have huc : UniformContinuousOn g (Set.Icc 0 L) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  -- Step 2: Get δ from uniform continuity for tolerance ε / L
  obtain ⟨δ, hδ_pos, hδ⟩ := huc (ε / (2 * L)) (div_pos hε (by positivity))
  -- Step 3: For N large enough, spacing L/(N+1) < δ
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, L / (↑N₀ + 1) < δ := by
    obtain ⟨n, hn⟩ := exists_nat_gt (L / δ)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < ↑n + 1)]
    have := (div_lt_iff₀ hδ_pos).mp hn
    linarith
  refine ⟨N₀, fun N hN => ?_⟩
  -- Abbreviation: a = L/(N+1) is the mesh width
  set M := N + 1 with hM_def
  have hM_pos : (0 : ℝ) < M := by positivity
  have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt hM_pos
  set a := L / (M : ℝ) with ha_def
  have ha_pos : 0 < a := div_pos hL_pos hM_pos
  -- The mesh is small enough: a < δ
  have ha_lt_δ : a < δ := by
    calc a = L / (↑N + 1) := by simp [ha_def, hM_def]
      _ ≤ L / (↑N₀ + 1) := by
          apply div_le_div_of_nonneg_left hL_pos.le
            (by positivity : (0 : ℝ) < ↑N₀ + 1)
          exact_mod_cast Nat.add_le_add_right hN 1
      _ < δ := hN₀
  -- Step 4: Rewrite the Riemann sum and integral using subintervals
  -- Node points: p(k) = k * a for k = 0, ..., M
  set p : ℕ → ℝ := fun k => (k : ℝ) * a with hp_def
  -- p is monotone
  have hp_mono : ∀ k l : ℕ, k ≤ l → p k ≤ p l := by
    intro k l hkl; simp [hp_def]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkl) ha_pos.le
  -- p(0) = 0 and p(M) = L
  have hp_zero : p 0 = 0 := by simp [hp_def]
  have hp_M : p M = L := by simp [hp_def, ha_def]; field_simp
  -- g is interval integrable on each subinterval
  have hint : ∀ k < M, IntervalIntegrable g MeasureTheory.volume (p k) (p (k + 1)) :=
    fun k _ => hg.intervalIntegrable _ _
  -- Split the integral: ∫₀ᴸ g = ∑_k ∫_{p(k)}^{p(k+1)} g
  have h_split : ∫ x in (0 : ℝ)..L, g x =
      ∑ k ∈ Finset.range M, ∫ x in p k..p (k + 1), g x := by
    rw [← hp_zero, ← hp_M]
    exact (intervalIntegral.sum_integral_adjacent_intervals hint).symm
  -- The Riemann sum: ∑_k a * g(p(k)) = ∑_k ∫_{p(k)}^{p(k+1)} g(p(k))
  have h_riemann : ∀ k ∈ Finset.range M,
      a * g (p k) = ∫ x in p k..p (k + 1), g (p k) := by
    intro k _
    rw [intervalIntegral.integral_const]
    -- (p (k+1) - p k) • g (p k) = a * g (p k), with smul = mul for ℝ
    simp only [hp_def, smul_eq_mul]; push_cast; ring
  -- Rewrite the Riemann sum as a Finset.range M sum
  have h_sum_eq : ∑ k ∈ Finset.range (N + 1),
      (L / (↑(N + 1) : ℝ)) * g (↑k * L / (↑(N + 1) : ℝ)) =
      ∑ k ∈ Finset.range M, (a * g (p k)) := by
    congr 1; ext k; simp only [ha_def, hp_def, hM_def]; ring
  -- Step 5: Bound the error
  rw [Real.dist_eq, h_sum_eq, h_split]
  -- |∑_k (∫ g(p(k)) - ∫ g)| = |∑_k ∫ (g(p(k)) - g)|
  -- Rewrite: sum - sum = sum of differences, then use h_riemann and integral_sub
  have h_rewrite : ∑ k ∈ Finset.range M, (a * g (p k)) -
      ∑ k ∈ Finset.range M, ∫ x in p k..p (k + 1), g x =
      ∑ k ∈ Finset.range M, ∫ x in p k..p (k + 1), (g (p k) - g x) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [h_riemann k hk, ← intervalIntegral.integral_sub
      (intervalIntegrable_const) (hg.intervalIntegrable _ _)]
  rw [h_rewrite]
  -- Bound: |∑_k ∫ (g(p(k)) - g(x)) dx| ≤ ∑_k |∫ (g(p(k)) - g(x)) dx|
  calc |∑ k ∈ Finset.range M, ∫ x in p k..p (k + 1), (g (p k) - g x)|
      ≤ ∑ k ∈ Finset.range M, |∫ x in p k..p (k + 1), (g (p k) - g x)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range M, (ε / (2 * L) * |p (k + 1) - p k|) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [← Real.norm_eq_abs]
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro x hx
        -- x ∈ Ι (p k) (p (k+1)) = Set.uIoc (p k) (p (k+1))
        -- Since p k ≤ p (k+1), this is (p k, p (k+1)]
        rw [Set.uIoc_of_le (hp_mono k (k + 1) (Nat.le_succ k))] at hx
        -- ‖g(p(k)) - g(x)‖ ≤ ε/(2L) by uniform continuity
        rw [Real.norm_eq_abs]
        have hk_lt : k < M := Finset.mem_range.mp hk
        -- p(k) ∈ [0, L]
        have hpk_mem : p k ∈ Set.Icc 0 L := by
          constructor
          · exact mul_nonneg (Nat.cast_nonneg k) ha_pos.le
          · calc p k = (k : ℝ) * a := rfl
              _ ≤ (M : ℝ) * a := by
                  apply mul_le_mul_of_nonneg_right _ ha_pos.le
                  exact_mod_cast hk_lt.le
              _ = L := by simp [ha_def]; field_simp
        -- x ∈ [0, L]
        have hx_mem : x ∈ Set.Icc 0 L := by
          constructor
          · linarith [hx.1, mul_nonneg (Nat.cast_nonneg k) ha_pos.le]
          · calc x ≤ p (k + 1) := hx.2
              _ ≤ p M := hp_mono _ _ hk_lt
              _ = L := hp_M
        -- dist (p k) x < δ since both are in the same subinterval of width a < δ
        have hdist : dist (p k) x < δ := by
          rw [Real.dist_eq]
          have h1 : p k ≤ x := le_of_lt hx.1
          have h2 : x - p k ≤ a := by
            have : x ≤ p (k + 1) := hx.2
            have : p (k + 1) - p k = a := by simp [hp_def]; ring
            linarith
          rw [abs_of_nonpos (by linarith)]
          linarith
        rw [← Real.dist_eq]
        exact le_of_lt (hδ _ hpk_mem _ hx_mem hdist)
    _ = ε / 2 := by
        -- Each |p(k+1) - p(k)| = a, sum of M terms of (ε/(2L)) * a = ε/2
        simp only [hp_def]
        have : ∀ k ∈ Finset.range M,
            ε / (2 * L) * |(↑(k + 1) : ℝ) * a - (↑k : ℝ) * a| = ε / (2 * L) * a := by
          intro k _
          congr 1
          push_cast
          have : ((k : ℝ) + 1) * a - (k : ℝ) * a = a := by ring
          rw [this, abs_of_pos ha_pos]
        rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        simp [ha_def, hM_def]
        field_simp
    _ < ε := by linarith

/-- **DFT coefficient converges to Fourier coefficient.**

For each fixed mode m, as N → ∞ the lattice DFT coefficient of the restricted
test function converges to the continuum DMS Fourier coefficient.
This is Riemann sum convergence for `∫ f(x) φ_m(x) dx`. -/
theorem latticeDFTCoeff1d_tendsto
    (f : SmoothMap_Circle L ℝ) (m : ℕ) :
    Tendsto (fun N : ℕ => latticeDFTCoeff1d L (N + 1) f m)
      atTop (nhds (DyninMityaginSpace.coeff m f)) := by
  -- DyninMityaginSpace.coeff m f = fourierCoeffReal m f = ∫ x in Icc 0 L, f x * φ_m x
  -- This follows by unfolding the chain:
  --   coeff m := (coeffCLM m).comp(equiv) → coeffCLM m (equiv f)
  --   → (equiv f).val m → (toRapidDecay f).val m → fourierCoeffReal m f
  have hcoeff : DyninMityaginSpace.coeff m f =
      ∫ x in Set.Icc 0 L, f x * SmoothMap_Circle.fourierBasisFun (L := L) m x := by
    show ((RapidDecaySeq.coeffCLM m).comp
      (SmoothMap_Circle.smoothCircleRapidDecayEquiv (L := L)).toContinuousLinearMap) f =
      ∫ x in Set.Icc 0 L, f x * SmoothMap_Circle.fourierBasisFun (L := L) m x
    simp [RapidDecaySeq.coeffCLM, RapidDecaySeq.coeffLM,
      SmoothMap_Circle.smoothCircleRapidDecayEquiv,
      SmoothMap_Circle.toRapidDecayLM, SmoothMap_Circle.toRapidDecay,
      SmoothMap_Circle.fourierCoeffReal]
  rw [hcoeff]
  set g := fun x => f x * SmoothMap_Circle.fourierBasisFun (L := L) m x
    with hg_def
  have hg_cont : Continuous g :=
    f.continuous.mul
      (SmoothMap_Circle.fourierBasisFun_smooth m).continuous
  have hg_per : Function.Periodic g L := fun x => by
    simp only [hg_def]
    rw [f.periodic x, SmoothMap_Circle.fourierBasisFun_periodic m x]
  apply (riemann_sum_periodic_tendsto L g hg_cont hg_per).congr'
  apply Filter.eventually_atTop.mpr
  refine ⟨m, fun N hN => ?_⟩
  have hm : m < N + 1 := by omega
  -- Beta-reduce the lambda applications
  show ∑ k ∈ Finset.range (N + 1), L / ↑(N + 1) * g (↑k * L / ↑(N + 1)) =
    latticeDFTCoeff1d L (N + 1) f m
  rw [latticeDFTCoeff1d_eq_riemann_sum L (N + 1) f m hm]
  -- Now: Finset.range sum of g = ZMod sum of f * fourierBasisFun at circlePoint
  -- Convert ZMod sum to Finset.range sum via Fin
  symm; rw [← Fin.sum_univ_eq_sum_range]
  congr 1


end GaussianField

end
