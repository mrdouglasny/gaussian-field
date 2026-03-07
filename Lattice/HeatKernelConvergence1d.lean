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

/-! ## ℕ-indexed lattice DFT coefficients -/

/-- **DFT coefficient of a restricted circle function at mode m.**

The m-th DFT coefficient of the restriction of a smooth circle function
to the N-point lattice. For m < N, this is the projection of `r_N f`
onto the m-th DFT eigenvector. For m ≥ N, it is 0 (no lattice mode).

The √(L/N) normalization in `circleRestriction` ensures these
approximate the continuum Fourier coefficients `DyninMityaginSpace.coeff m f`. -/
axiom latticeDFTCoeff1d (N : ℕ) [NeZero N]
    (f : SmoothMap_Circle L ℝ) (m : ℕ) : ℝ

/-- DFT coefficients vanish beyond the lattice cutoff. -/
axiom latticeDFTCoeff1d_zero_of_ge (N : ℕ) [NeZero N]
    (f : SmoothMap_Circle L ℝ) (m : ℕ) (hm : N ≤ m) :
    latticeDFTCoeff1d L N f m = 0

/-! ## Spectral expansion (ℕ-indexed) -/

/-- **Lattice heat kernel equals ℕ-indexed spectral sum.**

The matrix heat kernel bilinear form equals the spectral sum with
explicit sin² eigenvalues and DFT coefficients. This combines:
- DFT diagonalization of the circulant Laplacian on ℤ/Nℤ
- Reindexing from ZMod N to ℕ via the mode map -/
axiom latticeHeatKernelBilinear1d_eq_spectral (N : ℕ) [NeZero N] (t : ℝ)
    (f g : SmoothMap_Circle L ℝ) :
    latticeHeatKernelBilinear1d L N t f g =
    ∑ m ∈ Finset.range N,
      Real.exp (-t * latticeLaplacianEigenvalue 1 N (circleSpacing L N) m) *
      latticeDFTCoeff1d L N f m * latticeDFTCoeff1d L N g m

/-! ## Coefficient convergence (Riemann sum) -/

/-- **DFT coefficient converges to Fourier coefficient.**

For each fixed mode m, as N → ∞ the lattice DFT coefficient of the restricted
test function converges to the continuum DMS Fourier coefficient.
This is Riemann sum convergence for `∫ f(x) φ_m(x) dx`. -/
axiom latticeDFTCoeff1d_tendsto
    (f : SmoothMap_Circle L ℝ) (m : ℕ) :
    Tendsto (fun N : ℕ => latticeDFTCoeff1d L (N + 1) f m)
      atTop (nhds (DyninMityaginSpace.coeff m f))

/-- **Uniform bound on DFT coefficients.**

The DFT coefficients of restricted smooth functions are uniformly bounded
in N by the rapid decay bound on the continuum coefficients.
This provides the dominating function for DCT. -/
axiom latticeDFTCoeff1d_uniform_bound
    (f : SmoothMap_Circle L ℝ) :
    ∃ C : ℝ, ∀ (N : ℕ) (m : ℕ), |latticeDFTCoeff1d L (N + 1) f m| ≤
      C / (1 + (m : ℝ)) ^ 2

/-- **Lattice eigenvalue converges to continuum eigenvalue.**

For each fixed mode m, as N → ∞ the 1D lattice Laplacian eigenvalue
converges to the continuum circle eigenvalue. This combines the
sin²→sinc² computation (`latticeEigenvalue1d_tendsto`) with the
mode-matching between ZMod N DFT modes and ℕ-indexed Fourier modes. -/
axiom latticeLaplacianEigenvalue1d_tendsto (m : ℕ) :
    Tendsto (fun N : ℕ =>
      latticeLaplacianEigenvalue 1 (N + 1) (circleSpacing L (N + 1)) m)
      atTop (nhds (HasLaplacianEigenvalues.eigenvalue
        (E := SmoothMap_Circle L ℝ) m))

/-! ## Full 1D heat kernel convergence -/

/-- The m-th lattice heat kernel term at lattice size N. -/
private def latticeHeatTerm1d (N : ℕ) [NeZero N] (t : ℝ)
    (f g : SmoothMap_Circle L ℝ) (m : ℕ) : ℝ :=
  Real.exp (-t * latticeLaplacianEigenvalue 1 N (circleSpacing L N) m) *
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
          (tendsto_const_nhds.mul (latticeLaplacianEigenvalue1d_tendsto L m)))
        (latticeDFTCoeff1d_tendsto L f m))
      (latticeDFTCoeff1d_tendsto L g m)
  · -- Norm bound: |e^{-tλ} · a · b| ≤ Cf/(1+m)² · Cg/(1+m)²
    apply Filter.Eventually.of_forall
    intro N m
    unfold latticeHeatTerm1d
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hev := latticeLaplacianEigenvalue_nonneg 1 (N + 1) (circleSpacing L (N + 1)) m
    have hexp_le : Real.exp (-t * latticeLaplacianEigenvalue 1 (N + 1)
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
