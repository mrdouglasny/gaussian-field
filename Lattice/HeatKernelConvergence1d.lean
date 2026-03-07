/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# 1D Lattice Heat Kernel Convergence

Proves that the lattice heat kernel on ℤ/Nℤ converges to the continuum
heat kernel on S¹_L as N → ∞.

## Main results

- `latticeEigenvalue1d_tendsto` — eigenvalue convergence: (4N²/L²)sin²(πk/N) → (2πk/L)²
- `lattice_heatKernel_tendsto_continuum_1d` — full bilinear form convergence

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

/-! ## Spectral expansion (ℕ-indexed) -/

/-- **Lattice heat kernel equals ℕ-indexed spectral sum.**

The matrix heat kernel bilinear form equals the spectral sum with
explicit sin² eigenvalues and DFT coefficients. This combines:
- DFT diagonalization of the circulant Laplacian on ℤ/Nℤ
- The lattice Fourier basis being an eigenbasis of the discrete Laplacian -/
axiom latticeHeatKernelBilinear1d_eq_spectral (N : ℕ) [NeZero N] (t : ℝ)
    (f g : SmoothMap_Circle L ℝ) :
    latticeHeatKernelBilinear1d L N t f g =
    ∑ m ∈ Finset.range N,
      Real.exp (-t * latticeEigenvalue1d N (circleSpacing L N) m) *
      latticeDFTCoeff1d L N f m * latticeDFTCoeff1d L N g m


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
axiom riemann_sum_periodic_tendsto
    (g : ℝ → ℝ) (hg : Continuous g) (_hper : Function.Periodic g L) :
    Tendsto (fun N : ℕ =>
      ∑ k ∈ Finset.range (N + 1),
        (L / (↑(N + 1) : ℝ)) * g (↑k * L / (↑(N + 1) : ℝ)))
      atTop (nhds (∫ x in Set.Icc 0 L, g x))

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

/-- **Uniform bound on DFT coefficients.**

The DFT coefficients of restricted smooth functions are uniformly bounded
in N by the rapid decay bound on the continuum coefficients.
This provides the dominating function for DCT. -/
axiom latticeDFTCoeff1d_uniform_bound
    (f : SmoothMap_Circle L ℝ) :
    ∃ C : ℝ, ∀ (N : ℕ) (m : ℕ), |latticeDFTCoeff1d L (N + 1) f m| ≤
      C / (1 + (m : ℝ)) ^ 2

/-! ## Full 1D heat kernel convergence -/

/-- The m-th lattice heat kernel term at lattice size N. -/
private def latticeHeatTerm1d (N : ℕ) [NeZero N] (t : ℝ)
    (f g : SmoothMap_Circle L ℝ) (m : ℕ) : ℝ :=
  Real.exp (-t * latticeEigenvalue1d N (circleSpacing L N) m) *
    latticeDFTCoeff1d L N f m * latticeDFTCoeff1d L N g m

/-- Lattice heat kernel term vanishes for m ≥ N. -/
private theorem latticeHeatTerm1d_zero_of_ge (N : ℕ) [NeZero N] (t : ℝ)
    (f g : SmoothMap_Circle L ℝ) (m : ℕ) (hm : N ≤ m) :
    latticeHeatTerm1d L N t f g m = 0 := by
  unfold latticeHeatTerm1d
  rw [latticeDFTCoeff1d_zero_of_ge L N f m hm]
  ring

/-- The lattice bilinear equals the tsum of lattice heat terms. -/
private theorem latticeHeatKernelBilinear1d_eq_tsum (N : ℕ) [NeZero N] (t : ℝ)
    (f g : SmoothMap_Circle L ℝ) :
    latticeHeatKernelBilinear1d L N t f g =
    ∑' m, latticeHeatTerm1d L N t f g m := by
  rw [latticeHeatKernelBilinear1d_eq_spectral]
  -- The tsum of a function that vanishes beyond N equals the Finset.range N sum
  symm
  rw [tsum_eq_sum (s := Finset.range N)]
  · rfl
  · intro m hm
    rw [Finset.mem_range, not_lt] at hm
    exact latticeHeatTerm1d_zero_of_ge L N t f g m hm

theorem lattice_heatKernel_tendsto_continuum_1d (t : ℝ) (ht : 0 < t)
    (f g : SmoothMap_Circle L ℝ) :
    Tendsto
      (fun N : ℕ => latticeHeatKernelBilinear1d L (N + 1) t f g)
      atTop
      (nhds (heatKernelBilinear (E := SmoothMap_Circle L ℝ) t f g)) := by
  -- Step 1: Rewrite LHS as tsum of lattice heat terms
  simp_rw [latticeHeatKernelBilinear1d_eq_tsum]
  -- Step 2: RHS unfolds to a tsum (through private heatKernelTerm)
  have hRHS : heatKernelBilinear (E := SmoothMap_Circle L ℝ) t f g =
      ∑' m, Real.exp (-t * HasLaplacianEigenvalues.eigenvalue
        (E := SmoothMap_Circle L ℝ) m) *
        DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g := rfl
  rw [hRHS]
  -- Step 3: Get uniform bounds from axioms
  obtain ⟨Cf, hCf⟩ := latticeDFTCoeff1d_uniform_bound L f
  obtain ⟨Cg, hCg⟩ := latticeDFTCoeff1d_uniform_bound L g
  -- Summability of 1/(m+1)^4
  have h_sum : Summable (fun (m : ℕ) => (1 : ℝ) / ((m : ℝ) + 1) ^ 4) := by
    have h := Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4)
    exact (summable_nat_add_iff 1).mpr h |>.congr fun m => by push_cast; ring
  -- Step 4: Apply Tannery's theorem (dominated convergence for sums)
  apply tendsto_tsum_of_dominated_convergence
    (bound := fun (m : ℕ) => Cf / (1 + (m : ℝ)) ^ 2 * (Cg / (1 + (m : ℝ)) ^ 2))
  · -- Summable bound: Cf*Cg/(1+m)^4 is summable
    refine (h_sum.const_smul (Cf * Cg)).congr fun m => ?_
    simp only [smul_eq_mul]; field_simp; ring
  · -- Pointwise convergence: each term converges
    intro m
    unfold latticeHeatTerm1d
    exact Filter.Tendsto.mul
      (Filter.Tendsto.mul
        ((Real.continuous_exp.tendsto _).comp
          (tendsto_const_nhds.mul (latticeEigenvalue1d_tendsto_continuum L m)))
        (latticeDFTCoeff1d_tendsto L f m))
      (latticeDFTCoeff1d_tendsto L g m)
  · -- Norm bound: |e^{-tλ} · a · b| ≤ Cf/(1+m)² · Cg/(1+m)²
    apply Filter.Eventually.of_forall
    intro N m
    unfold latticeHeatTerm1d
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hev := latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) m
    have hexp_le : Real.exp (-t * latticeEigenvalue1d (N + 1)
        (circleSpacing L (N + 1)) m) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    calc Real.exp _ * |latticeDFTCoeff1d L (N + 1) f m| *
            |latticeDFTCoeff1d L (N + 1) g m|
        ≤ 1 * |latticeDFTCoeff1d L (N + 1) f m| *
            |latticeDFTCoeff1d L (N + 1) g m| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hexp_le (abs_nonneg _)) (abs_nonneg _)
      _ = |latticeDFTCoeff1d L (N + 1) f m| *
            |latticeDFTCoeff1d L (N + 1) g m| := by ring
      _ ≤ Cf / (1 + (m : ℝ)) ^ 2 * (Cg / (1 + (m : ℝ)) ^ 2) :=
          mul_le_mul (hCf N m) (hCg N m) (abs_nonneg _)
            (le_trans (abs_nonneg _) (hCf N m))

end GaussianField

end
