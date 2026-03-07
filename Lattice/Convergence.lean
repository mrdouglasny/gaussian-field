/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice-to-Continuum Green's Function Convergence

Proves the convergence of the lattice covariance bilinear form (for restricted
torus test functions) to the continuum Green's function as the lattice spacing
goes to zero.

## Main results

- `lattice_green_tendsto_continuum_pure` — (theorem) convergence for pure tensors
- `lattice_green_tendsto_continuum` — (axiom) convergence for general elements

## Proof strategy (pure tensors)

The convergence for pure tensors `f₁⊗f₂` and `g₁⊗g₂` is proved via two
intermediate axioms and `tendsto_tsum_of_dominated_convergence` (Tannery):

1. **Circulant diagonalization** (`lattice_covariance_pure_eq_2d_spectral`):
   The abstract lattice covariance equals the explicit 2D DFT spectral sum.

2. **DFT coefficient decay** (`latticeDFTCoeff1d_quadratic_bound`):
   Lattice DFT coefficients decay as `C/(1+m)²`, uniformly in N.

3. **Mode-by-mode convergence**: From `latticeEigenvalue1d_tendsto_continuum`
   and `latticeDFTCoeff1d_tendsto`.

4. **Domination**: The bound `C/((1+m₁)⁴(1+m₂)⁴)` gives a summable
   dominating function over `ℕ × ℕ`.

## References

- Glimm-Jaffe, *Quantum Physics*, §6.1
- Simon, *The P(φ)₂ Euclidean QFT*, Ch. I
-/

import Lattice.Covariance
import Torus.Evaluation
import HeatKernel.Bilinear
import SmoothCircle.Eigenvalues
import Lattice.HeatKernelConvergence1d

noncomputable section

namespace GaussianField

open Filter MeasureTheory NuclearTensorProduct

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Fundamental axioms -/

/-- **Circulant diagonalization: lattice covariance = explicit 2D DFT spectral sum.**

For pure tensors `f₁ ⊗ f₂` and `g₁ ⊗ g₂`, the abstract lattice covariance
equals the explicit spectral sum with 1D DFT eigenvalues and coefficients.

The mass matrix on `(ℤ/Nℤ)²` is block-circulant-circulant-block (BCCB),
diagonalized by the 2D DFT. Eigenvalues are sums of 1D eigenvalues and
eigenvector inner products factor as products of 1D DFT coefficients.

Reference: Davis, *Circulant Matrices*, Ch. 5. -/
axiom lattice_covariance_pure_eq_2d_spectral
    (mass : ℝ) (hmass : 0 < mass) (N : ℕ)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) :
    covariance
      (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
        (circleSpacing_pos L (N + 1)) hmass)
      (fun x => evalTorusAtSite L (N + 1) x (pure f₁ f₂))
      (fun x => evalTorusAtSite L (N + 1) x (pure g₁ g₂))
    = ∑ m₁ ∈ Finset.range (N + 1), ∑ m₂ ∈ Finset.range (N + 1),
        latticeDFTCoeff1d L (N + 1) f₁ m₁ * latticeDFTCoeff1d L (N + 1) g₁ m₁ *
        latticeDFTCoeff1d L (N + 1) f₂ m₂ * latticeDFTCoeff1d L (N + 1) g₂ m₂ /
        (latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m₁ +
         latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m₂ + mass ^ 2)

/-- **Lattice DFT coefficients decay at least quadratically, uniformly in N.**

For smooth circle functions, `|c_m^{N+1}(f)| ≤ C / (1 + m)²` uniformly in N.
Follows from two rounds of discrete summation by parts on the periodic lattice.

Reference: Katznelson, *Harmonic Analysis*, §I.2. -/
axiom latticeDFTCoeff1d_quadratic_bound (f : SmoothMap_Circle L ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N m,
      |latticeDFTCoeff1d L (N + 1) f m| ≤ C / (1 + (m : ℝ)) ^ 2

/-! ## 2D spectral terms -/

/-- The `(m₁, m₂)`-th term of the 2D lattice Green's function spectral sum. -/
private def latticeGreenTerm2d (N : ℕ) (mass : ℝ)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) (p : ℕ × ℕ) : ℝ :=
  latticeDFTCoeff1d L (N + 1) f₁ p.1 * latticeDFTCoeff1d L (N + 1) g₁ p.1 *
  latticeDFTCoeff1d L (N + 1) f₂ p.2 * latticeDFTCoeff1d L (N + 1) g₂ p.2 /
  (latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
   latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2)

/-- The `(n₁, n₂)`-th term of the continuum 2D Green's function spectral sum. -/
private def continuumGreenTerm2d (mass : ℝ)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) (p : ℕ × ℕ) : ℝ :=
  DyninMityaginSpace.coeff p.1 f₁ * DyninMityaginSpace.coeff p.1 g₁ *
  DyninMityaginSpace.coeff p.2 f₂ * DyninMityaginSpace.coeff p.2 g₂ /
  (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) p.1 +
   HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) p.2 + mass ^ 2)

/-- Lattice Green's term vanishes when either index is out of range. -/
private theorem latticeGreenTerm2d_zero_of_ge (N : ℕ) (mass : ℝ)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) (p : ℕ × ℕ)
    (h : N + 1 ≤ p.1 ∨ N + 1 ≤ p.2) :
    latticeGreenTerm2d L N mass f₁ g₁ f₂ g₂ p = 0 := by
  unfold latticeGreenTerm2d
  rcases h with h1 | h2
  · rw [latticeDFTCoeff1d_zero_of_ge L (N + 1) f₁ p.1 h1]; ring
  · rw [latticeDFTCoeff1d_zero_of_ge L (N + 1) f₂ p.2 h2]; ring

/-! ## Connecting lattice covariance to ℕ × ℕ tsum -/

/-- The lattice covariance (via circulant axiom) equals `∑' p, latticeGreenTerm2d p`. -/
private theorem lattice_covariance_eq_tsum_pure
    (mass : ℝ) (hmass : 0 < mass) (N : ℕ)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) :
    covariance
      (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
        (circleSpacing_pos L (N + 1)) hmass)
      (fun x => evalTorusAtSite L (N + 1) x (pure f₁ f₂))
      (fun x => evalTorusAtSite L (N + 1) x (pure g₁ g₂))
    = ∑' p : ℕ × ℕ, latticeGreenTerm2d L N mass f₁ g₁ f₂ g₂ p := by
  rw [lattice_covariance_pure_eq_2d_spectral]
  symm
  rw [tsum_eq_sum (s := Finset.range (N + 1) ×ˢ Finset.range (N + 1))]
  · rw [Finset.sum_product]; rfl
  · intro p hp
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range,
        not_and_or, not_lt, not_lt] at hp
    exact latticeGreenTerm2d_zero_of_ge L N mass f₁ g₁ f₂ g₂ p hp

/-! ## Connecting continuum Green's function to ℕ × ℕ tsum -/

/-- The continuum Green's function for pure tensors equals `∑' p, continuumGreenTerm2d p`. -/
private theorem greenFunctionBilinear_pure_eq_tsum
    (mass : ℝ) (hmass : 0 < mass)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) :
    greenFunctionBilinear (E := TorusTestFunction L) mass hmass
      (pure f₁ f₂) (pure g₁ g₂) =
    ∑' p : ℕ × ℕ, continuumGreenTerm2d L mass f₁ g₁ f₂ g₂ p := by
  show ∑' m, DyninMityaginSpace.coeff m (pure f₁ f₂) *
        DyninMityaginSpace.coeff m (pure g₁ g₂) /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) m +
          mass ^ 2) =
      ∑' p : ℕ × ℕ, continuumGreenTerm2d L mass f₁ g₁ f₂ g₂ p
  -- Rewrite each term using pure_val and tensor eigenvalue
  have h_term : ∀ m : ℕ,
      DyninMityaginSpace.coeff m (pure f₁ f₂) *
        DyninMityaginSpace.coeff m (pure g₁ g₂) /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) m +
          mass ^ 2) =
      continuumGreenTerm2d L mass f₁ g₁ f₂ g₂ (Nat.unpair m) := by
    intro m
    -- coeff for NTP is (·).val, so rewrite using pure_val
    show (pure f₁ f₂).val m * (pure g₁ g₂).val m /
        (HasLaplacianEigenvalues.eigenvalue
          (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) m +
          mass ^ 2) =
      continuumGreenTerm2d L mass f₁ g₁ f₂ g₂ (Nat.unpair m)
    simp only [continuumGreenTerm2d, tensorProductHasLaplacianEigenvalues, pure_val]
    ring
  simp_rw [h_term, ← Nat.pairEquiv_symm_apply]
  exact Nat.pairEquiv.symm.tsum_eq _

/-! ## Pointwise convergence of each term -/

/-- Each lattice Green's term converges to the continuum term. -/
private theorem latticeGreenTerm2d_tendsto
    (mass : ℝ) (hmass : 0 < mass)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) (p : ℕ × ℕ) :
    Tendsto (fun N : ℕ => latticeGreenTerm2d L N mass f₁ g₁ f₂ g₂ p)
      atTop (nhds (continuumGreenTerm2d L mass f₁ g₁ f₂ g₂ p)) := by
  unfold latticeGreenTerm2d continuumGreenTerm2d
  apply Filter.Tendsto.div
  · exact Filter.Tendsto.mul
      (Filter.Tendsto.mul
        (Filter.Tendsto.mul
          (latticeDFTCoeff1d_tendsto L f₁ p.1)
          (latticeDFTCoeff1d_tendsto L g₁ p.1))
        (latticeDFTCoeff1d_tendsto L f₂ p.2))
      (latticeDFTCoeff1d_tendsto L g₂ p.2)
  · apply Filter.Tendsto.add
    · apply Filter.Tendsto.add
      · exact latticeEigenvalue1d_tendsto_continuum L p.1
      · exact latticeEigenvalue1d_tendsto_continuum L p.2
    · exact tendsto_const_nhds
  · -- Denominator is positive at the limit
    have : HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) p.1 +
           HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) p.2 +
           mass ^ 2 > 0 :=
      by linarith [HasLaplacianEigenvalues.eigenvalue_nonneg
                      (E := SmoothMap_Circle L ℝ) p.1,
                    HasLaplacianEigenvalues.eigenvalue_nonneg
                      (E := SmoothMap_Circle L ℝ) p.2,
                    sq_pos_of_pos hmass]
    linarith

/-! ## Domination -/

/-- Norm bound on each lattice Green's term using DFT quadratic decay.

Uses all four quadratic DFT bounds to get `C / ((1+m₁)⁴(1+m₂)⁴ mass²)`,
which is summable over `ℕ × ℕ`. -/
private theorem latticeGreenTerm2d_norm_le
    (mass : ℝ) (hmass : 0 < mass)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ)
    {Cf₁ Cg₁ Cf₂ Cg₂ : ℝ}
    (hCf₁ : 0 ≤ Cf₁) (hCg₁ : 0 ≤ Cg₁) (hCf₂ : 0 ≤ Cf₂) (hCg₂ : 0 ≤ Cg₂)
    (hf₁ : ∀ N m, |latticeDFTCoeff1d L (N + 1) f₁ m| ≤ Cf₁ / (1 + (m : ℝ)) ^ 2)
    (hg₁ : ∀ N m, |latticeDFTCoeff1d L (N + 1) g₁ m| ≤ Cg₁ / (1 + (m : ℝ)) ^ 2)
    (hf₂ : ∀ N m, |latticeDFTCoeff1d L (N + 1) f₂ m| ≤ Cf₂ / (1 + (m : ℝ)) ^ 2)
    (hg₂ : ∀ N m, |latticeDFTCoeff1d L (N + 1) g₂ m| ≤ Cg₂ / (1 + (m : ℝ)) ^ 2)
    (N : ℕ) (p : ℕ × ℕ) :
    ‖latticeGreenTerm2d L N mass f₁ g₁ f₂ g₂ p‖ ≤
      Cf₁ * Cg₁ * Cf₂ * Cg₂ /
      (mass ^ 2 * (1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4) := by
  unfold latticeGreenTerm2d
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_mul]
  have hden_pos : 0 < latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
      latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2 :=
    by linarith [latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.1,
                 latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.2,
                 sq_pos_of_pos hmass]
  rw [abs_of_pos hden_pos]
  -- Bound: |num| / den ≤ |num| / mass²
  have hden_ge : mass ^ 2 ≤ latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
      latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2 :=
    by linarith [latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.1,
                 latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.2]
  have hmass_sq := sq_pos_of_pos hmass
  have hp1 : (0 : ℝ) < (1 + (p.1 : ℝ)) ^ 2 := by positivity
  have hp2 : (0 : ℝ) < (1 + (p.2 : ℝ)) ^ 2 := by positivity
  -- |c_f₁| * |c_g₁| ≤ Cf₁*Cg₁ / (1+m₁)⁴
  have h1 : |latticeDFTCoeff1d L (N + 1) f₁ p.1| *
      |latticeDFTCoeff1d L (N + 1) g₁ p.1| ≤
      Cf₁ * Cg₁ / (1 + (p.1 : ℝ)) ^ 4 :=
    calc |latticeDFTCoeff1d L (N + 1) f₁ p.1| *
          |latticeDFTCoeff1d L (N + 1) g₁ p.1|
        ≤ (Cf₁ / (1 + (p.1 : ℝ)) ^ 2) * (Cg₁ / (1 + (p.1 : ℝ)) ^ 2) :=
          mul_le_mul (hf₁ N p.1) (hg₁ N p.1) (abs_nonneg _)
            (div_nonneg hCf₁ hp1.le)
      _ = Cf₁ * Cg₁ / (1 + (p.1 : ℝ)) ^ 4 := by
          rw [div_mul_div_comm]; congr 1; ring
  -- |c_f₂| * |c_g₂| ≤ Cf₂*Cg₂ / (1+m₂)⁴
  have h2 : |latticeDFTCoeff1d L (N + 1) f₂ p.2| *
      |latticeDFTCoeff1d L (N + 1) g₂ p.2| ≤
      Cf₂ * Cg₂ / (1 + (p.2 : ℝ)) ^ 4 :=
    calc |latticeDFTCoeff1d L (N + 1) f₂ p.2| *
          |latticeDFTCoeff1d L (N + 1) g₂ p.2|
        ≤ (Cf₂ / (1 + (p.2 : ℝ)) ^ 2) * (Cg₂ / (1 + (p.2 : ℝ)) ^ 2) :=
          mul_le_mul (hf₂ N p.2) (hg₂ N p.2) (abs_nonneg _)
            (div_nonneg hCf₂ hp2.le)
      _ = Cf₂ * Cg₂ / (1 + (p.2 : ℝ)) ^ 4 := by
          rw [div_mul_div_comm]; congr 1; ring
  -- Combined numerator bound
  have hnum : |latticeDFTCoeff1d L (N + 1) f₁ p.1| *
      |latticeDFTCoeff1d L (N + 1) g₁ p.1| *
      |latticeDFTCoeff1d L (N + 1) f₂ p.2| *
      |latticeDFTCoeff1d L (N + 1) g₂ p.2| ≤
      Cf₁ * Cg₁ * Cf₂ * Cg₂ / ((1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4) := by
    have hmul := mul_le_mul h1 h2 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      (div_nonneg (mul_nonneg hCf₁ hCg₁) (by positivity))
    calc |latticeDFTCoeff1d L (N + 1) f₁ p.1| *
          |latticeDFTCoeff1d L (N + 1) g₁ p.1| *
          |latticeDFTCoeff1d L (N + 1) f₂ p.2| *
          |latticeDFTCoeff1d L (N + 1) g₂ p.2|
        = (|latticeDFTCoeff1d L (N + 1) f₁ p.1| * |latticeDFTCoeff1d L (N + 1) g₁ p.1|) *
          (|latticeDFTCoeff1d L (N + 1) f₂ p.2| * |latticeDFTCoeff1d L (N + 1) g₂ p.2|) :=
          by ring
      _ ≤ (Cf₁ * Cg₁ / (1 + (p.1 : ℝ)) ^ 4) * (Cf₂ * Cg₂ / (1 + (p.2 : ℝ)) ^ 4) := hmul
      _ = Cf₁ * Cg₁ * Cf₂ * Cg₂ / ((1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4) := by
          rw [div_mul_div_comm]; congr 1; ring
  -- Main calc: bound denominator then combine
  set den := latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
      latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2
  calc |latticeDFTCoeff1d L (N + 1) f₁ p.1| *
        |latticeDFTCoeff1d L (N + 1) g₁ p.1| *
        |latticeDFTCoeff1d L (N + 1) f₂ p.2| *
        |latticeDFTCoeff1d L (N + 1) g₂ p.2| / den
      ≤ Cf₁ * Cg₁ * Cf₂ * Cg₂ / ((1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4) / den :=
        div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
    _ ≤ Cf₁ * Cg₁ * Cf₂ * Cg₂ / ((1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4) / mass ^ 2 :=
        div_le_div_of_nonneg_left (div_nonneg (by positivity) (by positivity)) hmass_sq hden_ge
    _ = Cf₁ * Cg₁ * Cf₂ * Cg₂ /
        (mass ^ 2 * (1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4) := by
        rw [div_div]; congr 1; ring

/-- Summability of `C / (mass² (1+m₁)⁴ (1+m₂)⁴)` over `ℕ × ℕ`. -/
private theorem summable_bound
    (mass : ℝ) (hmass : 0 < mass) (C : ℝ) :
    Summable (fun p : ℕ × ℕ =>
      C / (mass ^ 2 * (1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4)) := by
  -- 1D: ∑ 1/(1+n)⁴ converges (shifted p-series with p=4 > 1)
  have h1d : Summable (fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 4) := by
    have hps := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 4)).comp_injective
      Nat.succ_injective
    exact hps.congr fun n => by
      simp only [Function.comp, Nat.cast_succ, add_comm]
  -- 2D: product of summable nonneg sequences is summable over ℕ × ℕ
  have h2d := h1d.mul_of_nonneg h1d (fun _ => by positivity) (fun _ => by positivity)
  exact (h2d.mul_left (C / mass ^ 2)).congr fun p => by
    have : mass ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hmass)
    have : (1 + (p.1 : ℝ)) ^ 4 ≠ 0 := ne_of_gt (by positivity)
    have : (1 + (p.2 : ℝ)) ^ 4 ≠ 0 := ne_of_gt (by positivity)
    field_simp

/-! ## Main convergence for pure tensors -/

/-- **Lattice covariance converges to continuum Green's function (pure tensors).**

Proved from `lattice_covariance_pure_eq_2d_spectral` (circulant diagonalization),
`latticeDFTCoeff1d_quadratic_bound` (DFT decay), 1D eigenvalue/coefficient
convergence, and Tannery's theorem. -/
theorem lattice_green_tendsto_continuum_pure
    (mass : ℝ) (hmass : 0 < mass)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) :
    Tendsto
      (fun N : ℕ =>
        covariance
          (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
            (circleSpacing_pos L (N + 1)) hmass)
          (fun x => evalTorusAtSite L (N + 1) x (pure f₁ f₂))
          (fun x => evalTorusAtSite L (N + 1) x (pure g₁ g₂)))
      atTop
      (nhds (greenFunctionBilinear (E := TorusTestFunction L) mass hmass
        (pure f₁ f₂) (pure g₁ g₂))) := by
  -- Step 1: Rewrite both sides as tsums over ℕ × ℕ
  simp_rw [lattice_covariance_eq_tsum_pure]
  rw [greenFunctionBilinear_pure_eq_tsum]
  -- Step 2: Extract decay constants
  obtain ⟨Cf₁, hCf₁_nn, hCf₁⟩ := latticeDFTCoeff1d_quadratic_bound L f₁
  obtain ⟨Cg₁, hCg₁_nn, hCg₁⟩ := latticeDFTCoeff1d_quadratic_bound L g₁
  obtain ⟨Cf₂, hCf₂_nn, hCf₂⟩ := latticeDFTCoeff1d_quadratic_bound L f₂
  obtain ⟨Cg₂, hCg₂_nn, hCg₂⟩ := latticeDFTCoeff1d_quadratic_bound L g₂
  -- Step 3: Apply Tannery's theorem
  apply tendsto_tsum_of_dominated_convergence
    (bound := fun p : ℕ × ℕ => Cf₁ * Cg₁ * Cf₂ * Cg₂ /
      (mass ^ 2 * (1 + (p.1 : ℝ)) ^ 4 * (1 + (p.2 : ℝ)) ^ 4))
  · exact summable_bound mass hmass _
  · intro p; exact latticeGreenTerm2d_tendsto L mass hmass f₁ g₁ f₂ g₂ p
  · apply Filter.Eventually.of_forall
    intro N p
    exact latticeGreenTerm2d_norm_le L mass hmass f₁ g₁ f₂ g₂
      hCf₁_nn hCg₁_nn hCf₂_nn hCg₂_nn hCf₁ hCg₁ hCf₂ hCg₂ N p

/-! ## Extension to general elements -/

/-- **Lattice covariance converges to the continuum Green's function.**

For general `f, g : TorusTestFunction L`, the convergence follows from
the pure tensor case (`lattice_green_tendsto_continuum_pure`) by
bilinearity and continuity of both sides plus density of pure tensors.

Reference: Treves, *TVS, Distributions and Kernels*, §43. -/
axiom lattice_green_tendsto_continuum
    (mass : ℝ) (hmass : 0 < mass)
    (f g : TorusTestFunction L) :
    Tendsto
      (fun N : ℕ =>
        covariance
          (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
            (circleSpacing_pos L (N + 1)) hmass)
          (fun x => evalTorusAtSite L (N + 1) x f)
          (fun x => evalTorusAtSite L (N + 1) x g))
      atTop
      (nhds (greenFunctionBilinear mass hmass f g))

end GaussianField

end
