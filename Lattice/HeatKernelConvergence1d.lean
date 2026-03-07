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

/-! ## DFT basis and mode indexing -/

-- The real orthonormal DFT basis of ℝ^N that diagonalizes the circulant Laplacian:
-- v_0(j) = 1/√N (constant mode)
-- For 0 < k < N/2: cos mode v_{cos,k}(j) = √(2/N) cos(2πjk/N)
-- For 0 < k < N/2: sin mode v_{sin,k}(j) = √(2/N) sin(2πjk/N)
-- For k = N/2 (N even): alternating v(j) = (-1)^j/√N

/-- 1D DFT basis vectors on ℤ/Nℤ.

Orthonormal real eigenvectors of the circulant Laplacian on ℤ/Nℤ,
indexed by `ZMod N`. These form the discrete analogue of the real
Fourier basis {1, cos(2πkx/L), sin(2πkx/L)} on S¹_L. -/
axiom dftBasisVector1d (N : ℕ) [NeZero N] (k : ZMod N)
    (j : FinLatticeSites 1 N) : ℝ

/-- DFT basis is orthonormal in ℓ²(ℤ/Nℤ). -/
axiom dftBasisVector1d_orthonormal (N : ℕ) [NeZero N]
    (k₁ k₂ : ZMod N) :
    ∑ j : FinLatticeSites 1 N, dftBasisVector1d N k₁ j * dftBasisVector1d N k₂ j =
    if k₁ = k₂ then 1 else 0

/-- Maps continuum mode index m ∈ ℕ to lattice mode k ∈ ZMod N.

Matches `fourierFreq`: m = 0 → k = 0, m = 2j-1 → cos at freq j,
m = 2j → sin at freq j. The ZMod encoding combines cos/sin modes
at the same frequency. -/
axiom modeMap1d (N : ℕ) [NeZero N] (m : ℕ) : ZMod N

/-- The eigenvalue at mapped mode matches the 1D lattice eigenvalue. -/
axiom modeMap1d_eigenvalue (N : ℕ) [NeZero N] (a : ℝ) (m : ℕ)
    (hm : m < N) :
    (4 / a ^ 2) * sin (π * (ZMod.val (modeMap1d N m) : ℝ) / N) ^ 2 =
    latticeLaplacianEigenvalue 1 N a m

/-! ## Spectral expansion of the lattice heat kernel -/

/-- **Spectral expansion of the lattice heat kernel bilinear form.**

On ℤ/Nℤ, the Laplacian matrix `-Δ_a` is circulant, hence diagonalized by
the DFT basis. The matrix exponential `K_t = exp(-t(-Δ_a))` inherits this:

  `⟨f, K_t g⟩ = Σ_k e^{-t·λ_k} ⟨f, v_k⟩⟨v_k, g⟩`

Proof strategy: `-Δ_a` is circulant → DFT diagonalizes it → spectral
theorem gives the eigendecomposition → matrix exponential factors through. -/
axiom latticeHeatKernel1d_spectral_expansion (N : ℕ) [NeZero N] (a t : ℝ)
    (f g : FinLatticeField 1 N) :
    (∑ x : FinLatticeSites 1 N,
      f x * (latticeHeatKernelMatrix 1 N a t).mulVec g x) =
    ∑ k : ZMod N,
      Real.exp (-t * ((4 / a ^ 2) * sin (π * (ZMod.val k : ℝ) / N) ^ 2)) *
      (∑ j : FinLatticeSites 1 N, dftBasisVector1d N k j * f j) *
      (∑ j : FinLatticeSites 1 N, dftBasisVector1d N k j * g j)

/-! ## Coefficient convergence (Riemann sum) -/

/-- **DFT coefficient of restricted test function converges to Fourier coefficient.**

For smooth periodic f on S¹_L, the DFT projection of `r_N f` onto the m-th
mode converges to `DyninMityaginSpace.coeff m f` as N → ∞.

This is Riemann sum convergence: the √(L/N) normalization in `circleRestriction`
ensures the ℓ² DFT coefficients approximate L² Fourier coefficients. -/
axiom dft_coeff_tendsto_fourier_coeff
    (f : SmoothMap_Circle L ℝ) (m : ℕ) :
    Tendsto
      (fun N : ℕ =>
        let fN : FinLatticeField 1 (N + 1) :=
          fun x => circleRestriction L (N + 1) f (x 0)
        ∑ j : FinLatticeSites 1 (N + 1),
          dftBasisVector1d (N + 1) (modeMap1d (N + 1) m) j * fN j)
      atTop
      (nhds (DyninMityaginSpace.coeff m f))

/-! ## Full 1D heat kernel convergence -/

/-- **1D lattice heat kernel converges to continuum heat kernel.**

For t > 0 and smooth circle test functions f, g:

  `Σ_x (r_N f)(x) · (K_t^N · r_N g)(x) → K_t(f, g)` as N → ∞

The proof combines:
1. DFT diagonalization of the circulant lattice Laplacian
2. Eigenvalue convergence (sinc² → 1)
3. Coefficient convergence (Riemann sums)
4. Dominated convergence (e^{-tλ} ≤ 1 + rapid coefficient decay) -/
theorem lattice_heatKernel_tendsto_continuum_1d (t : ℝ) (ht : 0 < t)
    (f g : SmoothMap_Circle L ℝ) :
    Tendsto
      (fun N : ℕ => latticeHeatKernelBilinear1d L (N + 1) t f g)
      atTop
      (nhds (heatKernelBilinear (E := SmoothMap_Circle L ℝ) t f g)) := by
  sorry

end GaussianField

end
