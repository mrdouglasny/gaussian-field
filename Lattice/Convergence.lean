/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice-to-Continuum Green's Function Convergence

Proves the convergence of the lattice covariance bilinear form (for restricted
torus test functions) to the continuum Green's function as the lattice spacing
goes to zero.

## Main results

- `lattice_green_tendsto_continuum_pure` — (theorem) convergence for pure tensors
- `lattice_green_tendsto_continuum` — (theorem) convergence for general elements

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
import Lattice.CirculantDFT

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
        ((latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m₁ +
         latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m₂ + mass ^ 2) *
         latticeFourierNormSq (N + 1) m₁ * latticeFourierNormSq (N + 1) m₂)

/-- **Lattice DFT coefficients decay at least quadratically, uniformly in N.**

For smooth circle functions, `|c_m^{N+1}(f)| ≤ C / (1 + m)²` uniformly in N.
Follows from two rounds of discrete summation by parts on the periodic lattice.

Reference: Katznelson, *Harmonic Analysis*, §I.2. -/
theorem latticeDFTCoeff1d_quadratic_bound (f : SmoothMap_Circle L ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N m,
      |latticeDFTCoeff1d L (N + 1) f m| ≤ C / (1 + (m : ℝ)) ^ 2 :=
  latticeDFTCoeff1d_quadratic_bound' L f

/-! ## 2D spectral terms -/

/-- The `(m₁, m₂)`-th term of the 2D lattice Green's function spectral sum. -/
private def latticeGreenTerm2d (N : ℕ) (mass : ℝ)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ) (p : ℕ × ℕ) : ℝ :=
  latticeDFTCoeff1d L (N + 1) f₁ p.1 * latticeDFTCoeff1d L (N + 1) g₁ p.1 *
  latticeDFTCoeff1d L (N + 1) f₂ p.2 * latticeDFTCoeff1d L (N + 1) g₂ p.2 /
  ((latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
   latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2) *
   latticeFourierNormSq (N + 1) p.1 * latticeFourierNormSq (N + 1) p.2)

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
  -- normSq → 1 for fixed mode as N → ∞
  have h_ns1 : Tendsto (fun N : ℕ => (latticeFourierNormSq (N + 1) p.1 : ℝ))
      atTop (nhds 1) := by
    rw [Filter.tendsto_def]; intro s hs
    apply (latticeFourierNormSq_eventually_one p.1).mono; intro N hN
    change latticeFourierNormSq (N + 1) p.1 ∈ s
    rw [hN]; exact mem_of_mem_nhds hs
  have h_ns2 : Tendsto (fun N : ℕ => (latticeFourierNormSq (N + 1) p.2 : ℝ))
      atTop (nhds 1) := by
    rw [Filter.tendsto_def]; intro s hs
    apply (latticeFourierNormSq_eventually_one p.2).mono; intro N hN
    change latticeFourierNormSq (N + 1) p.2 ∈ s
    rw [hN]; exact mem_of_mem_nhds hs
  -- Eigenvalue sum convergence
  have h_eig : Tendsto (fun N : ℕ =>
      latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
      latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2) atTop
      (nhds (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) p.1 +
             HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) p.2 +
             mass ^ 2)) :=
    ((latticeEigenvalue1d_tendsto_continuum L p.1).add
      (latticeEigenvalue1d_tendsto_continuum L p.2)).add tendsto_const_nhds
  -- Full denominator convergence: (eig_sum + m²) * normSq₁ * normSq₂ → (eig_sum + m²)
  have h_denom : Tendsto (fun N : ℕ =>
      (latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
       latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2) *
       latticeFourierNormSq (N + 1) p.1 * latticeFourierNormSq (N + 1) p.2) atTop
      (nhds (HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) p.1 +
             HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) p.2 +
             mass ^ 2)) := by
    have := (h_eig.mul h_ns1).mul h_ns2
    simp only [mul_one] at this; exact this
  apply Filter.Tendsto.div
  · exact Filter.Tendsto.mul
      (Filter.Tendsto.mul
        (Filter.Tendsto.mul
          (latticeDFTCoeff1d_tendsto L f₁ p.1)
          (latticeDFTCoeff1d_tendsto L g₁ p.1))
        (latticeDFTCoeff1d_tendsto L f₂ p.2))
      (latticeDFTCoeff1d_tendsto L g₂ p.2)
  · exact h_denom
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
  -- If either index is out of range, the term is 0
  by_cases h_range : p.1 < N + 1 ∧ p.2 < N + 1
  · obtain ⟨hp1_lt, hp2_lt⟩ := h_range
    unfold latticeGreenTerm2d
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, abs_mul]
    have hden_pos : 0 < (latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
        latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2) *
        latticeFourierNormSq (N + 1) p.1 * latticeFourierNormSq (N + 1) p.2 := by
      apply mul_pos (mul_pos _ _) _
      · linarith [latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.1,
                   latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.2,
                   sq_pos_of_pos hmass]
      · exact latticeFourierNormSq_pos (N + 1) p.1 hp1_lt
      · exact latticeFourierNormSq_pos (N + 1) p.2 hp2_lt
    rw [abs_of_pos hden_pos]
    -- Bound: |num| / den ≤ |num| / mass² (den ≥ mass² since normSq ≥ 1)
    have hden_ge : mass ^ 2 ≤ (latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
        latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2) *
        latticeFourierNormSq (N + 1) p.1 * latticeFourierNormSq (N + 1) p.2 := by
      have h_eig_sum_nn : 0 ≤ latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
          latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2 :=
        le_of_lt (by linarith [latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.1,
                               latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.2,
                               sq_pos_of_pos hmass])
      calc mass ^ 2
          ≤ latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
            latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2 :=
            by linarith [latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.1,
                         latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.2]
        _ ≤ _ * latticeFourierNormSq (N + 1) p.1 :=
            le_mul_of_one_le_right h_eig_sum_nn (latticeFourierNormSq_ge_one (N + 1) p.1 hp1_lt)
        _ ≤ _ * latticeFourierNormSq (N + 1) p.2 :=
            le_mul_of_one_le_right (mul_nonneg h_eig_sum_nn
              (le_of_lt (latticeFourierNormSq_pos (N + 1) p.1 hp1_lt)))
              (latticeFourierNormSq_ge_one (N + 1) p.2 hp2_lt)
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
    set den := (latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
        latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2) *
        latticeFourierNormSq (N + 1) p.1 * latticeFourierNormSq (N + 1) p.2
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
  · -- Out of range: term is 0
    rw [not_and_or, not_lt, not_lt] at h_range
    have h0 : latticeGreenTerm2d L N mass f₁ g₁ f₂ g₂ p = 0 :=
      latticeGreenTerm2d_zero_of_ge L N mass f₁ g₁ f₂ g₂ p h_range
    rw [h0, norm_zero]; positivity

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

/-! ### Helper lemmas (reproved from GreenInvariance.lean where private) -/

/-- Biorthogonality for `SmoothMap_Circle`: `coeff n (basis m) = δ_{nm}`. -/
private theorem smoothCircle_coeff_basis (n m : ℕ) :
    DyninMityaginSpace.coeff (E := SmoothMap_Circle L ℝ) n
      (DyninMityaginSpace.basis m) = if n = m then 1 else 0 := by
  show (RapidDecaySeq.coeffCLM n).comp
    (SmoothMap_Circle.smoothCircleRapidDecayEquiv (L := L)).toContinuousLinearMap
    ((SmoothMap_Circle.smoothCircleRapidDecayEquiv (L := L)).symm (RapidDecaySeq.basisVec m)) =
    if n = m then 1 else 0
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.apply_symm_apply,
    RapidDecaySeq.coeffCLM, RapidDecaySeq.coeffLM, RapidDecaySeq.basisVec]

/-- NTP basis elements are pure tensors (given biorthogonality in each factor). -/
private theorem ntp_basis_eq_pure (m : ℕ) :
    DyninMityaginSpace.basis
      (E := NuclearTensorProduct (SmoothMap_Circle L ℝ) (SmoothMap_Circle L ℝ)) m =
    pure (DyninMityaginSpace.basis (E := SmoothMap_Circle L ℝ) (Nat.unpair m).1)
         (DyninMityaginSpace.basis (E := SmoothMap_Circle L ℝ) (Nat.unpair m).2) := by
  ext k
  show (RapidDecaySeq.basisVec m).val k =
    (pure (DyninMityaginSpace.basis (E := SmoothMap_Circle L ℝ) (Nat.unpair m).1)
          (DyninMityaginSpace.basis (E := SmoothMap_Circle L ℝ) (Nat.unpair m).2)).val k
  rw [pure_val, smoothCircle_coeff_basis, smoothCircle_coeff_basis]
  simp only [RapidDecaySeq.basisVec]
  by_cases hk : k = m
  · subst hk; simp
  · simp only [hk, ite_false]
    by_cases h1 : (Nat.unpair k).1 = (Nat.unpair m).1
    · have h2 : (Nat.unpair k).2 ≠ (Nat.unpair m).2 := by
        intro h2; exact hk (by rw [← Nat.pair_unpair k, h1, h2, Nat.pair_unpair])
      simp [h2]
    · simp [h1]

/-- Continuity of `f ↦ G(f, h)` via polarization. -/
private theorem greenFunctionBilinear_continuous_left
    (mass : ℝ) (hmass : 0 < mass) (h : TorusTestFunction L) :
    Continuous (fun f => greenFunctionBilinear
      (E := TorusTestFunction L) mass hmass f h) := by
  have hcdiag := greenFunctionBilinear_continuous_diag mass hmass
    (E := TorusTestFunction L)
  have hpol : ∀ f, greenFunctionBilinear mass hmass f h =
      (greenFunctionBilinear mass hmass (f + h) (f + h) -
       greenFunctionBilinear mass hmass f f -
       greenFunctionBilinear mass hmass h h) / 2 := by
    intro f
    have : greenFunctionBilinear mass hmass (f + h) (f + h) =
        greenFunctionBilinear mass hmass f f +
        2 * greenFunctionBilinear mass hmass f h +
        greenFunctionBilinear mass hmass h h := by
      rw [greenFunctionBilinear_add_left, greenFunctionBilinear_add_right,
          greenFunctionBilinear_add_right, greenFunctionBilinear_symm mass hmass h f]
      ring
    linarith
  exact (((hcdiag.comp (continuous_id.add continuous_const)).sub hcdiag).sub
    continuous_const).div_const 2 |>.congr (fun f => (hpol f).symm)

/-- Green function as CLM in first argument. -/
private noncomputable def greenCLM_left
    (mass : ℝ) (hmass : 0 < mass) (h : TorusTestFunction L) :
    TorusTestFunction L →L[ℝ] ℝ :=
  ⟨{ toFun := fun f => greenFunctionBilinear (E := TorusTestFunction L) mass hmass f h
     map_add' := fun f₁ f₂ => greenFunctionBilinear_add_left mass hmass f₁ f₂ h
     map_smul' := fun c f => by
       rw [greenFunctionBilinear_smul_left, RingHom.id_apply, smul_eq_mul] },
   greenFunctionBilinear_continuous_left L mass hmass h⟩

@[simp] private theorem greenCLM_left_apply
    (mass : ℝ) (hmass : 0 < mass) (h f : TorusTestFunction L) :
    greenCLM_left L mass hmass h f =
    greenFunctionBilinear (E := TorusTestFunction L) mass hmass f h := rfl

/-! ### Lattice evaluation CLM -/

/-- The restriction map `f ↦ (x ↦ evalTorusAtSite x f)` as a CLM. -/
private def evalLatticeMap (N : ℕ) [NeZero N] :
    TorusTestFunction L →L[ℝ] FinLatticeField 2 N where
  toFun f := fun x => evalTorusAtSite L N x f
  map_add' f₁ f₂ := funext fun x => map_add (evalTorusAtSite L N x) f₁ f₂
  map_smul' c f := funext fun x => map_smul (evalTorusAtSite L N x) c f
  cont := continuous_pi fun x => (evalTorusAtSite L N x).continuous

@[simp] private theorem evalLatticeMap_apply (N : ℕ) [NeZero N]
    (f : TorusTestFunction L) (x : FinLatticeSites 2 N) :
    evalLatticeMap L N f x = evalTorusAtSite L N x f := rfl

/-- Lattice covariance CLM in the first argument (for fixed N and second argument). -/
private noncomputable def latticeCovCLM_left (N : ℕ) [NeZero N]
    (mass : ℝ) (hmass : 0 < mass) (ha : 0 < circleSpacing L N)
    (g : TorusTestFunction L) :
    TorusTestFunction L →L[ℝ] ℝ :=
  let T := (latticeCovariance 2 N (circleSpacing L N) mass ha hmass).comp
    (evalLatticeMap L N)
  (innerSL ℝ (T g)).comp T

private theorem latticeCovCLM_left_apply (N : ℕ) [NeZero N]
    (mass : ℝ) (hmass : 0 < mass) (ha : 0 < circleSpacing L N)
    (f g : TorusTestFunction L) :
    latticeCovCLM_left L N mass hmass ha g f =
    covariance (latticeCovariance 2 N (circleSpacing L N) mass ha hmass)
      (fun x => evalTorusAtSite L N x f)
      (fun x => evalTorusAtSite L N x g) := by
  simp only [latticeCovCLM_left, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    covariance, evalLatticeMap]
  exact real_inner_comm _ _

/-! ### DM expansion identities for lattice covariance -/

/-- B_N(f, g) = ∑' m, coeff(m, f) * B_N(basis m, g) via Dynin-Mityagin expansion. -/
private theorem covariance_dm_expansion_left (mass : ℝ) (hmass : 0 < mass) (N : ℕ)
    (f g : TorusTestFunction L) :
    covariance
      (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
        (circleSpacing_pos L (N + 1)) hmass)
      (fun x => evalTorusAtSite L (N + 1) x f)
      (fun x => evalTorusAtSite L (N + 1) x g) =
    ∑' m, DyninMityaginSpace.coeff m f *
      covariance
        (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
          (circleSpacing_pos L (N + 1)) hmass)
        (fun x => evalTorusAtSite L (N + 1) x (DyninMityaginSpace.basis m))
        (fun x => evalTorusAtSite L (N + 1) x g) := by
  haveI : NeZero (N + 1) := ⟨by omega⟩
  rw [← latticeCovCLM_left_apply]
  rw [DyninMityaginSpace.expansion (latticeCovCLM_left L (N + 1) mass hmass
    (circleSpacing_pos L (N + 1)) g) f]
  congr 1; ext m
  rw [latticeCovCLM_left_apply]

/-! ### Mixed norm bounds for domination -/

/-- Summability of `C / ((1+p₁)² · (1+p₂)²)` over `ℕ × ℕ`. -/
private theorem summable_inv_sq_sq :
    Summable (fun p : ℕ × ℕ =>
      1 / ((1 + (p.1 : ℝ)) ^ 2 * (1 + (p.2 : ℝ)) ^ 2)) := by
  have h1d : Summable (fun n : ℕ => 1 / (1 + (n : ℝ)) ^ 2) := by
    have hps := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)).comp_injective
      Nat.succ_injective
    exact hps.congr fun n => by
      simp only [Function.comp, Nat.cast_succ, add_comm]
  exact (h1d.mul_of_nonneg h1d (fun _ => by positivity) (fun _ => by positivity)).congr
    fun p => by simp [mul_comm]

/-- Uniform bound on `|B_N(pure(f₁,f₂), pure(g₁,g₂))|` using flat bounds for f and
quadratic bounds for g. -/
private theorem lattice_covariance_pure_abs_le
    (mass : ℝ) (hmass : 0 < mass)
    (f₁ g₁ f₂ g₂ : SmoothMap_Circle L ℝ)
    {Af₁ Af₂ Cg₁ Cg₂ : ℝ}
    (hAf₁ : 0 ≤ Af₁) (hAf₂ : 0 ≤ Af₂) (hCg₁ : 0 ≤ Cg₁) (hCg₂ : 0 ≤ Cg₂)
    (hf₁ : ∀ N m, |latticeDFTCoeff1d L (N + 1) f₁ m| ≤ Af₁)
    (hg₁ : ∀ N m, |latticeDFTCoeff1d L (N + 1) g₁ m| ≤ Cg₁ / (1 + (m : ℝ)) ^ 2)
    (hf₂ : ∀ N m, |latticeDFTCoeff1d L (N + 1) f₂ m| ≤ Af₂)
    (hg₂ : ∀ N m, |latticeDFTCoeff1d L (N + 1) g₂ m| ≤ Cg₂ / (1 + (m : ℝ)) ^ 2)
    (N : ℕ) :
    |covariance
      (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
        (circleSpacing_pos L (N + 1)) hmass)
      (fun x => evalTorusAtSite L (N + 1) x (pure f₁ f₂))
      (fun x => evalTorusAtSite L (N + 1) x (pure g₁ g₂))| ≤
    Af₁ * Cg₁ * Af₂ * Cg₂ / mass ^ 2 *
      ∑' p : ℕ × ℕ, 1 / ((1 + (p.1 : ℝ)) ^ 2 * (1 + (p.2 : ℝ)) ^ 2) := by
  rw [lattice_covariance_eq_tsum_pure]
  -- |∑' p, term p| ≤ ∑' p, |term p| ≤ ∑' p, bound p
  have hmass_sq := sq_pos_of_pos hmass
  -- Summability of the terms (bounded by a summable function)
  have h_summable : Summable (latticeGreenTerm2d L N mass f₁ g₁ f₂ g₂) := by
    obtain ⟨Cf₁, hCf₁_nn, hCf₁⟩ := latticeDFTCoeff1d_quadratic_bound L f₁
    obtain ⟨Cg₁', _, hCg₁'⟩ := latticeDFTCoeff1d_quadratic_bound L g₁
    obtain ⟨Cf₂, hCf₂_nn, hCf₂⟩ := latticeDFTCoeff1d_quadratic_bound L f₂
    obtain ⟨Cg₂', _, hCg₂'⟩ := latticeDFTCoeff1d_quadratic_bound L g₂
    exact Summable.of_norm_bounded (summable_bound mass hmass _)
      fun p => latticeGreenTerm2d_norm_le L mass hmass f₁ g₁ f₂ g₂
        hCf₁_nn (by positivity) hCf₂_nn (by positivity) hCf₁ hCg₁' hCf₂ hCg₂' N p
  calc |∑' p, latticeGreenTerm2d L N mass f₁ g₁ f₂ g₂ p|
      ≤ ∑' p, |latticeGreenTerm2d L N mass f₁ g₁ f₂ g₂ p| := by
        have h := norm_tsum_le_tsum_norm h_summable.norm
        simp only [Real.norm_eq_abs] at h; exact h
    _ ≤ ∑' p : ℕ × ℕ, Af₁ * Cg₁ * Af₂ * Cg₂ /
        (mass ^ 2 * (1 + (p.1 : ℝ)) ^ 2 * (1 + (p.2 : ℝ)) ^ 2) := by
        have hg_sum : Summable (fun p : ℕ × ℕ => Af₁ * Cg₁ * Af₂ * Cg₂ /
            (mass ^ 2 * (1 + (p.1 : ℝ)) ^ 2 * (1 + (p.2 : ℝ)) ^ 2)) :=
          (summable_inv_sq_sq.mul_left (Af₁ * Cg₁ * Af₂ * Cg₂ / mass ^ 2)).congr
            fun p => by field_simp
        apply h_summable.abs.tsum_le_tsum _ hg_sum
        intro p
        by_cases h_range : p.1 < N + 1 ∧ p.2 < N + 1
        · obtain ⟨hp1_lt, hp2_lt⟩ := h_range
          unfold latticeGreenTerm2d
          rw [abs_div, abs_mul, abs_mul, abs_mul]
          have hden_pos : 0 < (latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
              latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2) *
              latticeFourierNormSq (N + 1) p.1 * latticeFourierNormSq (N + 1) p.2 := by
            apply mul_pos (mul_pos _ _) _
            · linarith [latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.1,
                         latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.2]
            · exact latticeFourierNormSq_pos (N + 1) p.1 hp1_lt
            · exact latticeFourierNormSq_pos (N + 1) p.2 hp2_lt
          rw [abs_of_pos hden_pos]
          have hnum : |latticeDFTCoeff1d L (N + 1) f₁ p.1| *
              |latticeDFTCoeff1d L (N + 1) g₁ p.1| *
              |latticeDFTCoeff1d L (N + 1) f₂ p.2| *
              |latticeDFTCoeff1d L (N + 1) g₂ p.2| ≤
              Af₁ * (Cg₁ / (1 + (p.1 : ℝ)) ^ 2) *
              Af₂ * (Cg₂ / (1 + (p.2 : ℝ)) ^ 2) := by
            apply mul_le_mul
            · apply mul_le_mul
              · apply mul_le_mul (hf₁ N p.1) (hg₁ N p.1) (abs_nonneg _) hAf₁
              · exact hf₂ N p.2
              · exact abs_nonneg _
              · exact mul_nonneg hAf₁ (div_nonneg hCg₁ (by positivity))
            · exact hg₂ N p.2
            · exact abs_nonneg _
            · positivity
          set den := (latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
              latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2) *
              latticeFourierNormSq (N + 1) p.1 * latticeFourierNormSq (N + 1) p.2
          have hden_ge : mass ^ 2 ≤ den := by
            have h_ns1 := latticeFourierNormSq_ge_one (N + 1) p.1 hp1_lt
            have h_ns2 := latticeFourierNormSq_ge_one (N + 1) p.2 hp2_lt
            have h_eig_sum_pos : 0 < latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
                latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2 := by
              linarith [latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.1,
                         latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.2,
                         sq_pos_of_pos hmass]
            calc mass ^ 2
                ≤ latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
                  latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2 :=
                  by linarith [latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.1,
                               latticeEigenvalue1d_nonneg (N + 1) (circleSpacing L (N + 1)) p.2]
              _ ≤ (latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.1 +
                  latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) p.2 + mass ^ 2) *
                  latticeFourierNormSq (N + 1) p.1 :=
                  le_mul_of_one_le_right h_eig_sum_pos.le h_ns1
              _ ≤ den := le_mul_of_one_le_right
                  (mul_nonneg h_eig_sum_pos.le (le_of_lt (latticeFourierNormSq_pos (N + 1) p.1 hp1_lt))) h_ns2
          calc |latticeDFTCoeff1d L (N + 1) f₁ p.1| *
                |latticeDFTCoeff1d L (N + 1) g₁ p.1| *
                |latticeDFTCoeff1d L (N + 1) f₂ p.2| *
                |latticeDFTCoeff1d L (N + 1) g₂ p.2| / den
              ≤ Af₁ * (Cg₁ / (1 + ↑p.1) ^ 2) * Af₂ * (Cg₂ / (1 + ↑p.2) ^ 2) / den :=
                  div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
            _ ≤ Af₁ * (Cg₁ / (1 + ↑p.1) ^ 2) * Af₂ * (Cg₂ / (1 + ↑p.2) ^ 2) / mass ^ 2 := by
                  apply div_le_div_of_nonneg_left
                  · positivity
                  · exact hmass_sq
                  · exact hden_ge
            _ = Af₁ * Cg₁ * Af₂ * Cg₂ /
                (mass ^ 2 * (1 + ↑p.1) ^ 2 * (1 + ↑p.2) ^ 2) := by
                  field_simp
        · rw [not_and_or, not_lt, not_lt] at h_range
          rw [show |latticeGreenTerm2d L N mass f₁ g₁ f₂ g₂ p| = 0 from by
            rw [latticeGreenTerm2d_zero_of_ge L N mass f₁ g₁ f₂ g₂ p h_range, abs_zero]]
          positivity
    _ = Af₁ * Cg₁ * Af₂ * Cg₂ / mass ^ 2 *
        ∑' p : ℕ × ℕ, 1 / ((1 + (p.1 : ℝ)) ^ 2 * (1 + (p.2 : ℝ)) ^ 2) := by
        rw [← tsum_mul_left]; congr 1; ext p
        have : mass ^ 2 ≠ 0 := ne_of_gt hmass_sq
        have : (1 + (p.1 : ℝ)) ^ 2 ≠ 0 := ne_of_gt (by positivity)
        have : (1 + (p.2 : ℝ)) ^ 2 ≠ 0 := ne_of_gt (by positivity)
        field_simp

/-! ### Phase A: convergence for general f, pure g -/

/-- Convergence for general f, pure g: uses DM expansion in f, with Tannery's
theorem for dominated convergence. The domination uses the flat DFT bound
for basis elements and quadratic DFT bound for g₁, g₂. -/
private theorem lattice_green_tendsto_pure_right
    (mass : ℝ) (hmass : 0 < mass)
    (f : TorusTestFunction L) (g₁ g₂ : SmoothMap_Circle L ℝ) :
    Tendsto
      (fun N : ℕ =>
        covariance
          (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
            (circleSpacing_pos L (N + 1)) hmass)
          (fun x => evalTorusAtSite L (N + 1) x f)
          (fun x => evalTorusAtSite L (N + 1) x (pure g₁ g₂)))
      atTop
      (nhds (greenFunctionBilinear mass hmass f (pure g₁ g₂))) := by
  -- DM expansion: both sides equal ∑' m, coeff(m,f) * (CLM at basis m)
  have h_expand : ∀ N,
      covariance
        (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
          (circleSpacing_pos L (N + 1)) hmass)
        (fun x => evalTorusAtSite L (N + 1) x f)
        (fun x => evalTorusAtSite L (N + 1) x (pure g₁ g₂)) =
      ∑' m, DyninMityaginSpace.coeff m f *
        covariance
          (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
            (circleSpacing_pos L (N + 1)) hmass)
          (fun x => evalTorusAtSite L (N + 1) x (DyninMityaginSpace.basis m))
          (fun x => evalTorusAtSite L (N + 1) x (pure g₁ g₂)) :=
    fun N => covariance_dm_expansion_left L mass hmass N f (pure g₁ g₂)
  simp_rw [h_expand]
  have h_G_expand : greenFunctionBilinear mass hmass f (pure g₁ g₂) =
      ∑' m, DyninMityaginSpace.coeff m f *
        greenFunctionBilinear (E := TorusTestFunction L) mass hmass
          (DyninMityaginSpace.basis m) (pure g₁ g₂) := by
    have := DyninMityaginSpace.expansion (greenCLM_left L mass hmass (pure g₁ g₂)) f
    simp only [greenCLM_left_apply] at this
    exact this
  rw [h_G_expand]
  -- Extract quadratic DFT bounds for g₁, g₂
  obtain ⟨Cg₁, hCg₁_nn, hCg₁⟩ := latticeDFTCoeff1d_quadratic_bound L g₁
  obtain ⟨Cg₂, hCg₂_nn, hCg₂⟩ := latticeDFTCoeff1d_quadratic_bound L g₂
  -- Extract basis growth bound for sobolevSeminorm 0
  obtain ⟨A₀, hA₀_pos, r₀, hA₀⟩ :=
    DyninMityaginSpace.basis_growth (E := SmoothMap_Circle L ℝ) (0 : ℕ)
  set Sb := Real.sqrt (2 * L) * A₀ with hSb_def
  -- The flat DFT bound for basis(k): |c_m(basis k)| ≤ Sb * (1+k)^r₀
  have h_flat_basis : ∀ k N m,
      |latticeDFTCoeff1d L (N + 1) (DyninMityaginSpace.basis k) m| ≤
      Sb * (1 + (k : ℝ)) ^ r₀ := by
    intro k N m
    calc |latticeDFTCoeff1d L (N + 1) (DyninMityaginSpace.basis k) m|
        ≤ Real.sqrt (2 * L) *
          SmoothMap_Circle.sobolevSeminorm 0 (DyninMityaginSpace.basis k) :=
            latticeDFTCoeff1d_flat_bound L _ N m
      _ ≤ Real.sqrt (2 * L) * (A₀ * (1 + (k : ℝ)) ^ r₀) :=
            mul_le_mul_of_nonneg_left (hA₀ k) (Real.sqrt_nonneg _)
      _ = Sb * (1 + (k : ℝ)) ^ r₀ := by ring
  -- Set up the tsum convergence parameter
  set S₂ := ∑' p : ℕ × ℕ, 1 / ((1 + (p.1 : ℝ)) ^ 2 * (1 + (p.2 : ℝ)) ^ 2) with hS₂_def
  -- Bound on |B_N(basis m, pure g₁ g₂)| uniform in N, polynomial in m
  have h_BN_bound : ∀ m N,
      |covariance
        (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
          (circleSpacing_pos L (N + 1)) hmass)
        (fun x => evalTorusAtSite L (N + 1) x (DyninMityaginSpace.basis m))
        (fun x => evalTorusAtSite L (N + 1) x (pure g₁ g₂))| ≤
      Sb ^ 2 * Cg₁ * Cg₂ * S₂ / mass ^ 2 *
        (1 + ((Nat.unpair m).1 : ℝ)) ^ r₀ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₀ := by
    intro m N
    rw [ntp_basis_eq_pure L m]
    calc |covariance _ (fun x => evalTorusAtSite L (N + 1) x
            (pure (DyninMityaginSpace.basis (Nat.unpair m).1)
                  (DyninMityaginSpace.basis (Nat.unpair m).2)))
          (fun x => evalTorusAtSite L (N + 1) x (pure g₁ g₂))|
        ≤ (Sb * (1 + ((Nat.unpair m).1 : ℝ)) ^ r₀) * Cg₁ *
          (Sb * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₀) * Cg₂ / mass ^ 2 * S₂ :=
            lattice_covariance_pure_abs_le L mass hmass _ g₁ _ g₂
              (by positivity) (by positivity) hCg₁_nn hCg₂_nn
              (fun N' m' => h_flat_basis _ N' m') hCg₁
              (fun N' m' => h_flat_basis _ N' m') hCg₂ N
      _ = Sb ^ 2 * Cg₁ * Cg₂ * S₂ / mass ^ 2 *
          (1 + ((Nat.unpair m).1 : ℝ)) ^ r₀ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₀ := by
          ring
  -- Domination bound for Tannery
  set K := Sb ^ 2 * Cg₁ * Cg₂ * S₂ / mass ^ 2 with hK_def
  have hK_nn : 0 ≤ K := by positivity
  -- Summability of dominating function
  obtain ⟨D, hD_pos, sD, hD⟩ :=
    DyninMityaginSpace.coeff_decay (E := TorusTestFunction L) (2 * r₀ + 2)
  have h_dom_summable : Summable (fun m : ℕ =>
      |DyninMityaginSpace.coeff m f| * K *
      (1 + ((Nat.unpair m).1 : ℝ)) ^ r₀ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₀) := by
    have h_bound : ∀ m, |DyninMityaginSpace.coeff m f| * K *
        (1 + ((Nat.unpair m).1 : ℝ)) ^ r₀ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₀ ≤
        D * (sD.sup (DyninMityaginSpace.p (E := TorusTestFunction L))) f * K /
        (1 + (m : ℝ)) ^ 2 := by
      intro m
      have h1 : (Nat.unpair m).1 ≤ m := Nat.unpair_left_le m
      have h2 : (Nat.unpair m).2 ≤ m := Nat.unpair_right_le m
      have h_unpair_le : (1 + ((Nat.unpair m).1 : ℝ)) ^ r₀ *
          (1 + ((Nat.unpair m).2 : ℝ)) ^ r₀ ≤ (1 + (m : ℝ)) ^ (2 * r₀) := by
        calc (1 + ((Nat.unpair m).1 : ℝ)) ^ r₀ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₀
            ≤ (1 + (m : ℝ)) ^ r₀ * (1 + (m : ℝ)) ^ r₀ := by
              apply mul_le_mul
              · gcongr
              · gcongr
              · positivity
              · positivity
          _ = (1 + (m : ℝ)) ^ (2 * r₀) := by rw [← pow_add]; ring_nf
      have hm_pos : (0 : ℝ) < (1 + (m : ℝ)) ^ (2 * r₀ + 2) := by positivity
      have hD_bound := hD f m
      calc |DyninMityaginSpace.coeff m f| * K *
            (1 + ((Nat.unpair m).1 : ℝ)) ^ r₀ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₀
          = |DyninMityaginSpace.coeff m f| *
            ((1 + ((Nat.unpair m).1 : ℝ)) ^ r₀ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₀) * K := by
              ring
        _ ≤ |DyninMityaginSpace.coeff m f| * (1 + (m : ℝ)) ^ (2 * r₀) * K := by
              apply mul_le_mul_of_nonneg_right
              · exact mul_le_mul_of_nonneg_left h_unpair_le (abs_nonneg _)
              · exact hK_nn
        _ = (|DyninMityaginSpace.coeff m f| * (1 + (m : ℝ)) ^ (2 * r₀ + 2)) *
            (K / (1 + (m : ℝ)) ^ 2) := by
              have : (1 + (m : ℝ)) ^ 2 ≠ 0 := ne_of_gt (by positivity)
              field_simp; ring
        _ ≤ (D * (sD.sup (DyninMityaginSpace.p (E := TorusTestFunction L))) f) *
            (K / (1 + (m : ℝ)) ^ 2) := by
              exact mul_le_mul_of_nonneg_right hD_bound (div_nonneg hK_nn (by positivity))
        _ = D * (sD.sup (DyninMityaginSpace.p (E := TorusTestFunction L))) f * K /
            (1 + (m : ℝ)) ^ 2 := by ring
    apply Summable.of_nonneg_of_le
    · intro m; positivity
    · exact h_bound
    · have hps := (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2)).comp_injective
        Nat.succ_injective
      have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) :=
        hps.congr fun n => by simp only [Function.comp, Nat.cast_succ]
      exact (h1.mul_left
        (D * (sD.sup (DyninMityaginSpace.p (E := TorusTestFunction L))) f * K)).congr
        fun n => by ring
  -- Apply Tannery's theorem
  apply tendsto_tsum_of_dominated_convergence
    (bound := fun m => |DyninMityaginSpace.coeff m f| * K *
      (1 + ((Nat.unpair m).1 : ℝ)) ^ r₀ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₀)
  · exact h_dom_summable
  · -- Pointwise convergence: basis(m) is pure, so use lattice_green_tendsto_continuum_pure
    intro m
    apply Filter.Tendsto.const_mul
    rw [ntp_basis_eq_pure L m]
    exact lattice_green_tendsto_continuum_pure L mass hmass _ g₁ _ g₂
  · -- Domination
    apply Filter.Eventually.of_forall
    intro N m
    rw [Real.norm_eq_abs, abs_mul]
    have hrhs : |DyninMityaginSpace.coeff m f| * K *
        (1 + ((Nat.unpair m).1 : ℝ)) ^ r₀ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₀ =
        |DyninMityaginSpace.coeff m f| * (K *
        (1 + ((Nat.unpair m).1 : ℝ)) ^ r₀ * (1 + ((Nat.unpair m).2 : ℝ)) ^ r₀) := by ring
    rw [hrhs]
    apply mul_le_mul_of_nonneg_left
    · rw [abs_le]
      constructor
      · have := (abs_le.mp (h_BN_bound m N)).1; linarith
      · exact le_trans (le_abs_self _) (h_BN_bound m N)
    · exact abs_nonneg _

/-- The explicit quadratic DFT bound with seminorm-based constant.
Unlike `latticeDFTCoeff1d_quadratic_bound`, this gives the constant explicitly
in terms of Sobolev seminorms, allowing polynomial-in-k bounds for basis(k). -/
private theorem latticeDFTCoeff1d_seminorm_quadratic (f : SmoothMap_Circle L ℝ)
    (N m : ℕ) :
    |latticeDFTCoeff1d L (N + 1) f m| ≤
      (Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 0 f +
       Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 2 f * L ^ 2) /
      (1 + (m : ℝ)) ^ 2 := by
  set C₀ := Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 0 f
  set C₂ := Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 2 f
  set Cd := C₂ * L ^ 2
  set C := C₀ + Cd
  have hC₀_nn : 0 ≤ C₀ := by positivity
  have hC₂_nn : 0 ≤ C₂ := by positivity
  have hC_nn : 0 ≤ C := by positivity
  have h_pos : (0 : ℝ) < (1 + (m : ℝ)) ^ 2 := by positivity
  by_cases hm_lt : m < N + 1
  · by_cases hm0 : m = 0
    · subst hm0; simp only [Nat.cast_zero, add_zero, one_pow, div_one]
      exact (latticeDFTCoeff1d_flat_bound L f N 0).trans
        (le_add_of_nonneg_right (by positivity))
    · have hm_pos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      haveI hN1 : NeZero (N + 1) := ⟨by omega⟩
      have h_transfer := eigenvector_transfer L (N + 1) f m hm_lt
      have h_lap := laplacianDFT_flat_bound L (N + 1) f m
      have h_eig := latticeEigenvalue1d_ge_quadratic L (N + 1) m hm_pos hm_lt
      have h_eig_pos : 0 < latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m :=
        lt_of_lt_of_le (by have := hL.out; positivity) h_eig
      rw [← h_transfer] at h_lap
      have h_abs : |latticeDFTCoeff1d L (N + 1) f m| ≤
          C₂ / latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m := by
        rw [abs_mul, abs_of_pos h_eig_pos] at h_lap
        exact (le_div_iff₀ h_eig_pos).mpr (by linarith)
      have hL_pos := hL.out
      have h_denom_pos : (0 : ℝ) < (1 + ↑m) ^ 2 / L ^ 2 := by positivity
      calc |latticeDFTCoeff1d L (N + 1) f m|
          ≤ C₂ / latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m := h_abs
        _ ≤ C₂ / ((1 + ↑m) ^ 2 / L ^ 2) :=
            div_le_div_of_nonneg_left hC₂_nn h_denom_pos h_eig
        _ = Cd / (1 + ↑m) ^ 2 := by simp only [Cd]; field_simp
        _ ≤ C / (1 + ↑m) ^ 2 :=
            div_le_div_of_nonneg_right (by linarith) (by positivity)
  · rw [latticeDFTCoeff1d_zero_of_ge L (N + 1) f m (by omega), abs_zero]
    exact div_nonneg hC_nn (by positivity)

set_option maxHeartbeats 1600000 in
/-- Uniform-in-N polynomial bound on |B_N(f, basis m)| for general f.
Uses DM expansion of f, basis-basis bounds from `lattice_covariance_pure_abs_le`,
and `coeff_decay` summability. -/
private theorem lattice_covariance_general_basis_bound
    (mass : ℝ) (hmass : 0 < mass) (f : TorusTestFunction L) :
    ∃ C_B : ℝ, 0 < C_B ∧ ∃ s_B : ℕ, ∀ N m,
      |covariance
        (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
          (circleSpacing_pos L (N + 1)) hmass)
        (fun x => evalTorusAtSite L (N + 1) x f)
        (fun x => evalTorusAtSite L (N + 1) x (DyninMityaginSpace.basis m))| ≤
      C_B * (1 + (m : ℝ)) ^ s_B := by
  -- Step 1: Extract basis growth and coeff decay constants
  obtain ⟨A₀, hA₀_pos, r₀, hA₀⟩ :=
    DyninMityaginSpace.basis_growth (E := SmoothMap_Circle L ℝ) (0 : ℕ)
  obtain ⟨A₂, hA₂_pos, r₂, hA₂⟩ :=
    DyninMityaginSpace.basis_growth (E := SmoothMap_Circle L ℝ) (2 : ℕ)
  obtain ⟨D_f, hDf_pos, sD_f, hDf⟩ :=
    DyninMityaginSpace.coeff_decay (E := TorusTestFunction L) (2 * r₀ + 2)
  set Sb := Real.sqrt (2 * L) * A₀
  set Cq := Real.sqrt (2 * L) * A₀ + Real.sqrt (2 * L) * A₂ * L ^ 2
  set rq := r₀ + r₂
  set S₂ := ∑' p : ℕ × ℕ, 1 / ((1 + (p.1 : ℝ)) ^ 2 * (1 + (p.2 : ℝ)) ^ 2)
  set K_bb := Sb ^ 2 * Cq ^ 2 * S₂ / mass ^ 2
  -- Step 2: Flat DFT bound for basis elements
  have h_flat : ∀ k N j,
      |latticeDFTCoeff1d L (N + 1) (DyninMityaginSpace.basis k) j| ≤
      Sb * (1 + (k : ℝ)) ^ r₀ := by
    intro k N j
    calc _ ≤ Real.sqrt (2 * L) *
              SmoothMap_Circle.sobolevSeminorm 0 (DyninMityaginSpace.basis k) :=
            latticeDFTCoeff1d_flat_bound L _ N j
      _ ≤ Real.sqrt (2 * L) * (A₀ * (1 + (k : ℝ)) ^ r₀) :=
            mul_le_mul_of_nonneg_left (hA₀ k) (Real.sqrt_nonneg _)
      _ = Sb * (1 + (k : ℝ)) ^ r₀ := by ring
  -- Step 3: Quadratic DFT bound for basis elements (polynomial constant)
  have h_quad : ∀ k N j,
      |latticeDFTCoeff1d L (N + 1) (DyninMityaginSpace.basis k) j| ≤
      Cq * (1 + (k : ℝ)) ^ rq / (1 + (j : ℝ)) ^ 2 := by
    intro k N j
    have hk1 : (1 : ℝ) ≤ 1 + (k : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) k]
    calc _ ≤ (Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 0
                (DyninMityaginSpace.basis k) +
              Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 2
                (DyninMityaginSpace.basis k) * L ^ 2) /
            (1 + (j : ℝ)) ^ 2 :=
          latticeDFTCoeff1d_seminorm_quadratic L _ N j
      _ ≤ Cq * (1 + (k : ℝ)) ^ rq / (1 + (j : ℝ)) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          calc _ ≤ Real.sqrt (2 * L) * (A₀ * (1 + (k : ℝ)) ^ r₀) +
                    Real.sqrt (2 * L) * (A₂ * (1 + (k : ℝ)) ^ r₂) * L ^ 2 := by
                  apply add_le_add
                  · exact mul_le_mul_of_nonneg_left (hA₀ k) (Real.sqrt_nonneg _)
                  · exact mul_le_mul_of_nonneg_right
                      (mul_le_mul_of_nonneg_left (hA₂ k) (Real.sqrt_nonneg _)) (sq_nonneg L)
            _ ≤ Real.sqrt (2 * L) * (A₀ * (1 + (k : ℝ)) ^ rq) +
                  Real.sqrt (2 * L) * (A₂ * (1 + (k : ℝ)) ^ rq) * L ^ 2 := by
                  apply add_le_add
                  · apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
                    exact mul_le_mul_of_nonneg_left
                      (pow_le_pow_right₀ hk1 (Nat.le_add_right r₀ r₂)) hA₀_pos.le
                  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg L)
                    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
                    exact mul_le_mul_of_nonneg_left
                      (pow_le_pow_right₀ hk1 (Nat.le_add_left r₂ r₀)) hA₂_pos.le
            _ = Cq * (1 + (k : ℝ)) ^ rq := by ring
  -- Step 4: Basis-basis bound via lattice_covariance_pure_abs_le
  have h_bb : ∀ N n m,
      |covariance
        (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
          (circleSpacing_pos L (N + 1)) hmass)
        (fun x => evalTorusAtSite L (N + 1) x (DyninMityaginSpace.basis n))
        (fun x => evalTorusAtSite L (N + 1) x (DyninMityaginSpace.basis m))| ≤
      K_bb * (1 + (n : ℝ)) ^ (2 * r₀) * (1 + (m : ℝ)) ^ (2 * rq) := by
    intro N n m
    rw [ntp_basis_eq_pure L n, ntp_basis_eq_pure L m]
    calc _ ≤ (Sb * (1 + ((Nat.unpair n).1 : ℝ)) ^ r₀) *
              (Cq * (1 + ((Nat.unpair m).1 : ℝ)) ^ rq) *
              (Sb * (1 + ((Nat.unpair n).2 : ℝ)) ^ r₀) *
              (Cq * (1 + ((Nat.unpair m).2 : ℝ)) ^ rq) / mass ^ 2 * S₂ :=
            lattice_covariance_pure_abs_le L mass hmass _ _ _ _
              (by positivity) (by positivity) (by positivity) (by positivity)
              (fun N' j => h_flat _ N' j) (fun N' j => h_quad _ N' j)
              (fun N' j => h_flat _ N' j) (fun N' j => h_quad _ N' j) N
      _ = K_bb *
            ((1 + ((Nat.unpair n).1 : ℝ)) ^ r₀ * (1 + ((Nat.unpair n).2 : ℝ)) ^ r₀) *
            ((1 + ((Nat.unpair m).1 : ℝ)) ^ rq * (1 + ((Nat.unpair m).2 : ℝ)) ^ rq) := by
              ring
      _ ≤ K_bb * (1 + (n : ℝ)) ^ (2 * r₀) * (1 + (m : ℝ)) ^ (2 * rq) := by
          gcongr
          · calc (1 + ((Nat.unpair n).1 : ℝ)) ^ r₀ * (1 + ((Nat.unpair n).2 : ℝ)) ^ r₀
                ≤ (1 + (n : ℝ)) ^ r₀ * (1 + (n : ℝ)) ^ r₀ := by
                  apply mul_le_mul
                  · gcongr; exact_mod_cast Nat.unpair_left_le n
                  · gcongr; exact_mod_cast Nat.unpair_right_le n
                  · positivity
                  · positivity
              _ = (1 + (n : ℝ)) ^ (2 * r₀) := by rw [← pow_add]; ring_nf
          · calc (1 + ((Nat.unpair m).1 : ℝ)) ^ rq * (1 + ((Nat.unpair m).2 : ℝ)) ^ rq
                ≤ (1 + (m : ℝ)) ^ rq * (1 + (m : ℝ)) ^ rq := by
                  apply mul_le_mul
                  · gcongr; exact_mod_cast Nat.unpair_left_le m
                  · gcongr; exact_mod_cast Nat.unpair_right_le m
                  · positivity
                  · positivity
              _ = (1 + (m : ℝ)) ^ (2 * rq) := by rw [← pow_add]; ring_nf
  -- Step 5: Summability of |coeff(n,f)| * (1+n)^(2r₀)
  have h_coeff_poly_summable : Summable (fun n => |DyninMityaginSpace.coeff n f| *
      (1 + (n : ℝ)) ^ (2 * r₀)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity)
    · intro n
      calc _ = |DyninMityaginSpace.coeff n f| * (1 + (n : ℝ)) ^ (2 * r₀ + 2) /
              (1 + (n : ℝ)) ^ 2 := by
            have : (1 + (n : ℝ)) ^ 2 ≠ 0 := ne_of_gt (by positivity)
            field_simp; ring
        _ ≤ D_f * (sD_f.sup (DyninMityaginSpace.p (E := TorusTestFunction L))) f /
            (1 + (n : ℝ)) ^ 2 :=
            div_le_div_of_nonneg_right (hDf f n) (by positivity)
    · have hps := (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2)).comp_injective
          Nat.succ_injective
      have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) :=
        hps.congr fun n => by simp only [Function.comp, Nat.cast_succ]
      exact (h1.mul_left
        (D_f * (sD_f.sup (DyninMityaginSpace.p (E := TorusTestFunction L))) f)).congr
        fun n => by ring
  -- Step 6: Assemble the bound
  set sum_f := ∑' n, |DyninMityaginSpace.coeff n f| * (1 + (n : ℝ)) ^ (2 * r₀)
  refine ⟨K_bb * sum_f + 1, by positivity, 2 * rq, fun N m => ?_⟩
  -- DM expansion: B_N(f, basis m) = ∑' n, coeff(n,f) * B_N(basis n, basis m)
  rw [covariance_dm_expansion_left L mass hmass N f (DyninMityaginSpace.basis m)]
  -- Summability of the bound series
  have h_bound_sum : Summable (fun n => |DyninMityaginSpace.coeff n f| *
      (K_bb * (1 + (n : ℝ)) ^ (2 * r₀) * (1 + (m : ℝ)) ^ (2 * rq))) :=
    (h_coeff_poly_summable.mul_left (K_bb * (1 + (m : ℝ)) ^ (2 * rq))).congr
      fun n => by ring
  -- Summability of the original DM series (by norm comparison)
  have h_dm_sum : Summable (fun n => DyninMityaginSpace.coeff n f *
      covariance
        (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
          (circleSpacing_pos L (N + 1)) hmass)
        (fun x => evalTorusAtSite L (N + 1) x (DyninMityaginSpace.basis n))
        (fun x => evalTorusAtSite L (N + 1) x (DyninMityaginSpace.basis m))) :=
    .of_norm_bounded h_bound_sum fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (h_bb N n m) (abs_nonneg _)
  -- Triangle inequality + tsum comparison
  -- Abbreviate the sequence for type unification efficiency
  set a : ℕ → ℝ := fun n => DyninMityaginSpace.coeff n f *
      covariance (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
        (circleSpacing_pos L (N + 1)) hmass)
        (fun x => evalTorusAtSite L (N + 1) x (DyninMityaginSpace.basis n))
        (fun x => evalTorusAtSite L (N + 1) x (DyninMityaginSpace.basis m))
  set b : ℕ → ℝ := fun n => |DyninMityaginSpace.coeff n f| *
      (K_bb * (1 + (n : ℝ)) ^ (2 * r₀) * (1 + (m : ℝ)) ^ (2 * rq))
  have ha_sum : Summable a := h_dm_sum
  have hb_sum : Summable b := h_bound_sum
  have h_pw : ∀ n, |a n| ≤ b n := fun n => by
    simp only [a, b]; rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (h_bb N n m) (abs_nonneg _)
  -- |∑' a n| ≤ ∑' |a n| ≤ ∑' b n
  have h1 : |∑' n, a n| ≤ ∑' n, |a n| := by
    have := norm_tsum_le_tsum_norm ha_sum.norm
    simp only [Real.norm_eq_abs] at this; exact this
  have h2 : ∑' n, |a n| ≤ ∑' n, b n := by
    apply Summable.tsum_le_tsum h_pw (ha_sum.norm.congr fun n => Real.norm_eq_abs _) hb_sum
  -- ∑' b n = K_bb * (1+m)^(2*rq) * sum_f
  have h3 : ∑' n, b n = K_bb * (1 + (m : ℝ)) ^ (2 * rq) * sum_f := by
    show ∑' n, b n = _
    simp_rw [show ∀ n, b n = K_bb * (1 + (m : ℝ)) ^ (2 * rq) *
        (|DyninMityaginSpace.coeff n f| * (1 + (n : ℝ)) ^ (2 * r₀))
      from fun n => by simp only [b]; ring]
    exact tsum_mul_left
  linarith [h1.trans h2, h3.symm ▸ h2, (show (0 : ℝ) ≤ (1 + (m : ℝ)) ^ (2 * rq) from
    by positivity)]

/-! ### Phase B: main theorem -/

/-- **Lattice covariance converges to the continuum Green's function.**

For general `f, g : TorusTestFunction L`, the convergence follows from
the pure tensor case by two successive DM expansions:
- Phase A: fix g = pure(g₁,g₂), prove convergence for all f
- Phase B: fix f, use Phase A for basis(m) (which is pure), prove for all g

Each phase uses Tannery's theorem with a dominating function derived from
the flat DFT bound for basis elements, quadratic DFT bound for the fixed
pure factor, and polynomial basis growth.

Reference: Treves, *TVS, Distributions and Kernels*, §43. -/
theorem lattice_green_tendsto_continuum
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
      (nhds (greenFunctionBilinear mass hmass f g)) := by
  -- Phase B: DM expansion of g in both B_N and G
  -- B_N(f, g) = B_N(g, f) = ∑' m, coeff(m, g) * B_N(basis m, f)
  --           = ∑' m, coeff(m, g) * B_N(f, basis m)
  -- G(f, g) = ∑' m, coeff(m, g) * G(f, basis m)
  -- Use expansion in g via the symmetry B_N(f, g) = B_N(g, f)
  have h_symm : ∀ N,
      covariance
        (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
          (circleSpacing_pos L (N + 1)) hmass)
        (fun x => evalTorusAtSite L (N + 1) x f)
        (fun x => evalTorusAtSite L (N + 1) x g) =
      covariance
        (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
          (circleSpacing_pos L (N + 1)) hmass)
        (fun x => evalTorusAtSite L (N + 1) x g)
        (fun x => evalTorusAtSite L (N + 1) x f) := by
    intro N; simp [covariance, real_inner_comm]
  -- Expand B_N(g, f) using DM expansion in g, then swap back
  have h_expand_g : ∀ N,
      covariance
        (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
          (circleSpacing_pos L (N + 1)) hmass)
        (fun x => evalTorusAtSite L (N + 1) x f)
        (fun x => evalTorusAtSite L (N + 1) x g) =
      ∑' m, DyninMityaginSpace.coeff m g *
        covariance
          (latticeCovariance 2 (N + 1) (circleSpacing L (N + 1)) mass
            (circleSpacing_pos L (N + 1)) hmass)
          (fun x => evalTorusAtSite L (N + 1) x f)
          (fun x => evalTorusAtSite L (N + 1) x (DyninMityaginSpace.basis m)) := by
    intro N
    rw [h_symm N, covariance_dm_expansion_left L mass hmass N g f]
    congr 1; ext m; congr 1; simp [covariance, real_inner_comm]
  -- Expand G(f, g) = ∑' m, coeff(m, g) * G(f, basis m)
  have h_G_expand : greenFunctionBilinear mass hmass f g =
      ∑' m, DyninMityaginSpace.coeff m g *
        greenFunctionBilinear (E := TorusTestFunction L) mass hmass
          f (DyninMityaginSpace.basis m) := by
    have := DyninMityaginSpace.expansion (greenCLM_left L mass hmass f) g
    simp only [greenCLM_left_apply] at this
    rw [greenFunctionBilinear_symm mass hmass f g, this]
    congr 1; ext m; rw [greenFunctionBilinear_symm]
  simp_rw [h_expand_g]
  rw [h_G_expand]
  -- Get uniform-in-N polynomial bound on |B_N(f, basis m)|
  obtain ⟨C_B, hCB_pos, s_B, h_BN_bound⟩ :=
    lattice_covariance_general_basis_bound L mass hmass f
  -- Apply Tannery with the polynomial bound
  apply tendsto_tsum_of_dominated_convergence
    (bound := fun m => |DyninMityaginSpace.coeff m g| *
      (C_B * (1 + (m : ℝ)) ^ s_B))
  · -- Summability of the bound: |coeff(m,g)| * C_B * (1+m)^s_B
    obtain ⟨D, hD_pos, sD, hD⟩ :=
      DyninMityaginSpace.coeff_decay (E := TorusTestFunction L) (s_B + 2)
    set K := D * (sD.sup (DyninMityaginSpace.p (E := TorusTestFunction L))) g *
      C_B with hK_def
    have h_inv_sq_summable : Summable (fun n : ℕ => K / (1 + (n : ℝ)) ^ 2) := by
      have hps := (Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2)).comp_injective
          Nat.succ_injective
      have h1 : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) :=
        hps.congr fun n => by simp only [Function.comp, Nat.cast_succ]
      exact (h1.mul_left K).congr fun n => by ring
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) h_inv_sq_summable
    have h_pos2 : (0 : ℝ) < (1 + (m : ℝ)) ^ 2 := by positivity
    calc |DyninMityaginSpace.coeff m g| * (C_B * (1 + (m : ℝ)) ^ s_B)
        = |DyninMityaginSpace.coeff m g| * (1 + (m : ℝ)) ^ (s_B + 2) *
            (C_B / (1 + (m : ℝ)) ^ 2) := by
          have : (1 + (m : ℝ)) ^ 2 ≠ 0 := ne_of_gt h_pos2
          field_simp; ring
      _ ≤ D * (sD.sup (DyninMityaginSpace.p (E := TorusTestFunction L))) g *
            (C_B / (1 + (m : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_right (hD g m) (div_nonneg hCB_pos.le h_pos2.le)
      _ = K / (1 + (m : ℝ)) ^ 2 := by rw [hK_def]; ring
  · -- Pointwise convergence: basis(m) is pure, so use Phase A
    intro m
    apply Filter.Tendsto.const_mul
    rw [ntp_basis_eq_pure L m]
    exact lattice_green_tendsto_pure_right L mass hmass f _ _
  · -- Domination: trivial from the uniform polynomial bound
    apply Filter.Eventually.of_forall
    intro N m
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (h_BN_bound N m) (abs_nonneg _)

end GaussianField

end
