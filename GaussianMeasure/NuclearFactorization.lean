/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Source-Indexed Nuclear Representation of Schwartz CLMs

For any continuous linear map T : S(D,F) → H from a Schwartz space to
a Hilbert space, produces a nuclear representation:

  T(f) = ∑_m φ_m(f) · y_m,  ∑_m ‖y_m‖ < ∞

where φ_m are equicontinuous coefficient functionals (bounded by one
Schwartz seminorm) and y_m ∈ H.

## Proof technique

1. Hermite expansion: ⟨w, T(f)⟩ = ∑_m c_m(f) ⟨w, T(ψ_m)⟩
2. Polynomial growth of ‖T(ψ_m)‖ (from continuity of T)
3. Define y_m = (1+m)^{-s} T(ψ_m), φ_m = (1+m)^s c_m
4. Choose s = p+2 so ∑ ‖y_m‖ ≤ C ∑ (1+m)^{-2} < ∞

Uses axioms: `schwartz_hermite_expansion`, `schwartz_hermite_seminorm_growth`,
`schwartz_hermite_coefficient_decay`.

## References

- Gel'fand, Vilenkin, "Generalized Functions" Vol 4, Ch 3-4
-/

import GaussianMeasure.Axioms
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

open scoped BigOperators
open Finset

noncomputable section

namespace GaussianMeasure

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## P-series summability helper -/

/-- Sum of (1+m)^(-2) converges (p-series test). -/
lemma summable_one_add_rpow_neg_two :
    Summable (fun m : ℕ => (1 + (m : ℝ)) ^ ((-2) : ℝ)) := by
  have h := (summable_nat_add_iff (f := fun n => (↑n : ℝ) ^ ((-2) : ℝ)) 1).mpr
    (Real.summable_nat_rpow.mpr (by norm_num : ((-2) : ℝ) < -1))
  simp only [Nat.cast_add, Nat.cast_one] at h
  convert h using 1; ext m; simp [add_comm]

/-! ## Finset sup of polynomial bounds -/

/-- The sup of finitely many polynomially-bounded seminorms is polynomially bounded. -/
private lemma finset_sup_seminorm_poly_bound
    {D' : Type*} [NormedAddCommGroup D'] [NormedSpace ℝ D'] [FiniteDimensional ℝ D']
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
    (s : Finset (ℕ × ℕ))
    (ψ : ℕ → SchwartzMap D' F')
    (hψ : ∀ kl : ℕ × ℕ, ∃ (C : ℝ) (s : ℝ), 0 < C ∧
      ∀ m : ℕ, (schwartzSeminormFamily ℝ D' F' kl) (ψ m) ≤ C * (1 + (m : ℝ)) ^ s) :
    ∃ (C₁ : ℝ) (p₁ : ℝ), 0 < C₁ ∧
      ∀ m : ℕ, (s.sup (schwartzSeminormFamily ℝ D' F')) (ψ m) ≤
        C₁ * (1 + (m : ℝ)) ^ p₁ := by
  induction s using Finset.cons_induction with
  | empty =>
    refine ⟨1, 0, one_pos, fun m => ?_⟩
    simp only [Finset.sup_empty, Seminorm.bot_eq_zero, Seminorm.zero_apply]
    positivity
  | cons a s' ha ih =>
    obtain ⟨C_prev, p_prev, hC_prev, h_prev⟩ := ih
    obtain ⟨C_a, s_a, hC_a, h_a⟩ := hψ a
    refine ⟨C_prev + C_a, max p_prev s_a, add_pos hC_prev hC_a, fun m => ?_⟩
    rw [Finset.sup_cons]
    have hone_le : (1 : ℝ) ≤ 1 + (m : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg' m)
    calc (schwartzSeminormFamily ℝ D' F' a ⊔
            s'.sup (schwartzSeminormFamily ℝ D' F')) (ψ m)
        = schwartzSeminormFamily ℝ D' F' a (ψ m) ⊔
          (s'.sup (schwartzSeminormFamily ℝ D' F')) (ψ m) :=
          Seminorm.sup_apply _ _ _
      _ ≤ schwartzSeminormFamily ℝ D' F' a (ψ m) +
          (s'.sup (schwartzSeminormFamily ℝ D' F')) (ψ m) := by
          exact max_le (le_add_of_nonneg_right
            (apply_nonneg _ _)) (le_add_of_nonneg_left
            (apply_nonneg _ _))
      _ ≤ C_a * (1 + ↑m) ^ s_a + C_prev * (1 + ↑m) ^ p_prev :=
          add_le_add (h_a m) (h_prev m)
      _ ≤ C_a * (1 + ↑m) ^ max p_prev s_a +
          C_prev * (1 + ↑m) ^ max p_prev s_a := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hone_le (le_max_right _ _))
              (le_of_lt hC_a)
          · exact mul_le_mul_of_nonneg_left
              (Real.rpow_le_rpow_of_exponent_le hone_le (le_max_left _ _))
              (le_of_lt hC_prev)
      _ = (C_prev + C_a) * (1 + ↑m) ^ max p_prev s_a := by ring

/-! ## Polynomial growth of CLM images on Hermite basis -/

/-- CLM images of Schwartz functions with polynomially growing seminorms
    also grow polynomially. -/
theorem hermite_image_growth
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : (SchwartzMap D F) →L[ℝ] H)
    (ψ : ℕ → SchwartzMap D F)
    (hψ : ∀ (k l : ℕ), ∃ (C : ℝ) (s : ℝ), 0 < C ∧
      ∀ m : ℕ, SchwartzMap.seminorm ℝ k l (ψ m) ≤ C * (1 + (m : ℝ)) ^ s) :
    ∃ (C : ℝ) (p : ℝ), 0 < C ∧
      ∀ m : ℕ, ‖T (ψ m)‖ ≤ C * (1 + (m : ℝ)) ^ p := by
  have hcont : Continuous ((normSeminorm ℝ H).comp T.toLinearMap) := by
    convert T.continuous.norm using 1
  obtain ⟨s, C₀, hC₀_ne, hle⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℝ D F) _ hcont
  have hfinset_bound : ∃ (C₁ : ℝ) (p₁ : ℝ), 0 < C₁ ∧
      ∀ m : ℕ, (s.sup (schwartzSeminormFamily ℝ D F)) (ψ m) ≤ C₁ * (1 + (m : ℝ)) ^ p₁ :=
    finset_sup_seminorm_poly_bound s ψ (fun kl => hψ kl.1 kl.2)
  obtain ⟨C₁, p₁, hC₁_pos, hfinset⟩ := hfinset_bound
  have hC₀_pos : (0 : ℝ) < C₀ := by positivity
  exact ⟨C₀ * C₁, p₁, mul_pos hC₀_pos hC₁_pos, fun m =>
    calc ‖T (ψ m)‖
        ≤ C₀ * (s.sup (schwartzSeminormFamily ℝ D F)) (ψ m) := by
          have := hle (ψ m)
          simp only [Seminorm.comp_apply, coe_normSeminorm, Seminorm.smul_apply,
                     NNReal.smul_def, smul_eq_mul] at this
          exact this
      _ ≤ C₀ * (C₁ * (1 + (m : ℝ)) ^ p₁) :=
          mul_le_mul_of_nonneg_left (hfinset m) (le_of_lt hC₀_pos)
      _ = C₀ * C₁ * (1 + (m : ℝ)) ^ p₁ := by ring⟩

/-! ## Nuclear representation theorem -/

/-- **Source-indexed nuclear representation**: Any CLM from Schwartz space to
    a Hilbert space admits a ℓ¹-convergent series representation.

    This is the key bridge between the Hermite structure of Schwartz space
    and the nuclear factorization needed for the Gaussian construction. -/
theorem schwartz_clm_nuclear_representation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : SchwartzMap D F →L[ℝ] H) :
    ∃ (φ : ℕ → (SchwartzMap D F →L[ℝ] ℝ)) (y : ℕ → H),
      Summable (fun m => ‖y m‖) ∧
      (∃ (q : ℕ × ℕ) (B : ℝ), 0 < B ∧
        ∀ (m : ℕ) (f : SchwartzMap D F), |φ m f| ≤ B * SchwartzMap.seminorm ℝ q.1 q.2 f) ∧
      (∀ (f : SchwartzMap D F) (w : H),
        @inner ℝ H _ w (T f) = ∑' m, φ m f * @inner ℝ H _ w (y m)) := by
  set ψ := schwartzHermiteBasis D F with hψ_def
  set c := schwartzHermiteCoeff D F with hc_def
  have hexpand : ∀ (T' : (SchwartzMap D F) →L[ℝ] H) (f : SchwartzMap D F) (w : H),
      @inner ℝ H _ w (T' f) =
        ∑' m, c m f * @inner ℝ H _ w (T' (ψ m)) :=
    fun T' f w => schwartz_hermite_expansion T' w f
  have hdecay := fun (k : ℝ) => schwartz_hermite_coefficient_decay (D := D) (F := F) k
  -- Step 1: Get polynomial growth bound for ‖T(ψ_m)‖
  have hψ_bound : ∀ (k l : ℕ), ∃ (C : ℝ) (s : ℝ), 0 < C ∧
      ∀ m : ℕ, SchwartzMap.seminorm ℝ k l (ψ m) ≤ C * (1 + (m : ℝ)) ^ s :=
    fun k l => let ⟨C, s, hC, _, h⟩ := schwartz_hermite_seminorm_growth (D := D) (F := F) k l
               ⟨C, s, hC, h⟩
  obtain ⟨C_g, p, hCg_pos, hgrowth⟩ := hermite_image_growth T ψ hψ_bound
  -- Step 2: Choose s = p + 2 for convergence
  set s : ℝ := p + 2 with hs_def
  -- Step 3: Define y_m = (1+m)^(-s) · T(ψ_m)
  set y : ℕ → H := fun m => ((1 + (m : ℝ)) ^ (-s)) • T (ψ m) with hy_def
  -- Step 4: Define φ_m(f) = c_m(f) · (1+m)^s
  set φ : ℕ → (SchwartzMap D F) →L[ℝ] ℝ :=
    fun m => (1 + (m : ℝ)) ^ s • c m with hφ_def
  refine ⟨φ, y, ?_, ?_, ?_⟩
  · -- (i) ∑ ‖y_m‖ < ∞
    simp only [hy_def]
    refine Summable.of_norm_bounded (summable_one_add_rpow_neg_two.mul_left C_g) (fun m => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _), norm_smul,
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 1 + ↑m) _)]
    have hpos : (0 : ℝ) < 1 + ↑m := by positivity
    calc (1 + (↑m : ℝ)) ^ (-s) * ‖T (ψ m)‖
        ≤ (1 + (↑m : ℝ)) ^ (-s) * (C_g * (1 + (↑m : ℝ)) ^ p) :=
          mul_le_mul_of_nonneg_left (hgrowth m) (Real.rpow_nonneg (le_of_lt hpos) _)
      _ = C_g * ((1 + (↑m : ℝ)) ^ (-s) * (1 + (↑m : ℝ)) ^ p) := by ring
      _ = C_g * (1 + (↑m : ℝ)) ^ ((-2) : ℝ) := by
          congr 1; rw [← Real.rpow_add hpos]; congr 1; linarith
  · -- (ii) Equicontinuity of φ_m
    obtain ⟨C_s, q, hCs_pos, hdecay_s⟩ := hdecay s
    exact ⟨q, C_s, hCs_pos, fun m f => by
      simp only [hφ_def, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by positivity : (0:ℝ) < 1 + ↑m) s),
          mul_comm]
      exact hdecay_s f m⟩
  · -- (iii) ⟨w, T(f)⟩ = ∑ φ_m(f) · ⟨w, y_m⟩
    intro f w
    rw [hexpand T f w]
    congr 1
    ext m
    simp only [hφ_def, hy_def, ContinuousLinearMap.smul_apply, smul_eq_mul,
               inner_smul_right]
    have hpos : (0 : ℝ) < 1 + (↑m : ℝ) := by positivity
    rw [Real.rpow_neg (le_of_lt hpos)]
    have hne : (1 + (↑m : ℝ)) ^ s ≠ 0 := (Real.rpow_pos_of_pos hpos s).ne'
    field_simp

end GaussianMeasure
