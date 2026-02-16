/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Nuclear Representation of CLMs from Nuclear Spaces

For any continuous linear map T : E → H from a nuclear Fréchet space to
a Hilbert space, produces a nuclear representation:

  T(f) = ∑_m φ_m(f) · y_m,  ∑_m ‖y_m‖ < ∞

where φ_m are equicontinuous coefficient functionals (bounded by one
seminorm) and y_m ∈ H.

## Proof technique

1. Schauder expansion: ⟨w, T(f)⟩ = ∑_m c_m(f) ⟨w, T(ψ_m)⟩
2. Polynomial growth of ‖T(ψ_m)‖ (from continuity of T)
3. Define y_m = (1+m)^{-s} T(ψ_m), φ_m = (1+m)^s c_m
4. Choose s = p+2 so ∑ ‖y_m‖ ≤ C ∑ (1+m)^{-2} < ∞

## References

- Gel'fand, Vilenkin, "Generalized Functions" Vol 4, Ch 3-4
-/

import GaussianMeasure.NuclearSpace
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

open scoped BigOperators
open Finset

noncomputable section

namespace GaussianMeasure

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NuclearSpace E]

/-! ## P-series summability helper -/

/-- Sum of (1+m)^(-2) converges (p-series test). -/
lemma summable_one_add_rpow_neg_two :
    Summable (fun m : ℕ => (1 + (m : ℝ)) ^ ((-2) : ℝ)) := by
  have h := (summable_nat_add_iff (f := fun n => (↑n : ℝ) ^ ((-2) : ℝ)) 1).mpr
    (Real.summable_nat_rpow.mpr (by norm_num : ((-2) : ℝ) < -1))
  simp only [Nat.cast_add, Nat.cast_one] at h
  convert h using 1; ext m; simp [add_comm]

/-! ## Finset sup of polynomial bounds -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [NuclearSpace E] in
/-- The sup of finitely many polynomially-bounded seminorms is polynomially bounded. -/
private lemma finset_sup_seminorm_poly_bound
    {ι' : Type*} (p' : ι' → Seminorm ℝ E)
    (s : Finset ι')
    (x : ℕ → E)
    (hx : ∀ i : ι', ∃ C > 0, ∃ (t : ℕ),
      ∀ m : ℕ, p' i (x m) ≤ C * (1 + (m : ℝ)) ^ t) :
    ∃ (C₁ : ℝ) (p₁ : ℕ), 0 < C₁ ∧
      ∀ m : ℕ, (s.sup p') (x m) ≤ C₁ * (1 + (m : ℝ)) ^ p₁ := by
  induction s using Finset.cons_induction with
  | empty =>
    refine ⟨1, 0, one_pos, fun m => ?_⟩
    simp only [Finset.sup_empty, Seminorm.bot_eq_zero, Seminorm.zero_apply]
    positivity
  | cons a s' ha ih =>
    obtain ⟨C_prev, p_prev, hC_prev, h_prev⟩ := ih
    obtain ⟨C_a, hC_a, t_a, h_a⟩ := hx a
    refine ⟨C_prev + C_a, max p_prev t_a, add_pos hC_prev hC_a, fun m => ?_⟩
    rw [Finset.sup_cons]
    have hone_le : (1 : ℝ) ≤ 1 + (m : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg' m)
    calc (p' a ⊔ s'.sup p') (x m)
        = p' a (x m) ⊔ (s'.sup p') (x m) :=
          Seminorm.sup_apply _ _ _
      _ ≤ p' a (x m) + (s'.sup p') (x m) := by
          exact max_le (le_add_of_nonneg_right
            (apply_nonneg _ _)) (le_add_of_nonneg_left
            (apply_nonneg _ _))
      _ ≤ C_a * (1 + ↑m) ^ t_a + C_prev * (1 + ↑m) ^ p_prev :=
          add_le_add (h_a m) (h_prev m)
      _ ≤ C_a * (1 + ↑m) ^ max p_prev t_a +
          C_prev * (1 + ↑m) ^ max p_prev t_a := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hone_le (le_max_right _ _))
              (le_of_lt hC_a)
          · exact mul_le_mul_of_nonneg_left
              (pow_le_pow_right₀ hone_le (le_max_left _ _))
              (le_of_lt hC_prev)
      _ = (C_prev + C_a) * (1 + ↑m) ^ max p_prev t_a := by ring

/-! ## Polynomial growth of CLM images on basis -/

/-- CLM images of basis elements grow polynomially in the index. -/
theorem clm_image_growth
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : E →L[ℝ] H) :
    ∃ (C : ℝ) (p₁ : ℕ), 0 < C ∧
      ∀ m : ℕ, ‖T (NuclearSpace.basis m)‖ ≤ C * (1 + (m : ℝ)) ^ p₁ := by
  have hcont : Continuous ((normSeminorm ℝ H).comp T.toLinearMap) := by
    convert T.continuous.norm using 1
  obtain ⟨s, C₀, hC₀_ne, hle⟩ :=
    Seminorm.bound_of_continuous NuclearSpace.h_with _ hcont
  have hfinset_bound : ∃ (C₁ : ℝ) (p₁ : ℕ), 0 < C₁ ∧
      ∀ m : ℕ, (s.sup NuclearSpace.p) (NuclearSpace.basis m) ≤
        C₁ * (1 + (m : ℝ)) ^ p₁ :=
    finset_sup_seminorm_poly_bound NuclearSpace.p s NuclearSpace.basis
      NuclearSpace.basis_growth
  obtain ⟨C₁, p₁, hC₁_pos, hfinset⟩ := hfinset_bound
  have hC₀_pos : (0 : ℝ) < C₀ := by positivity
  exact ⟨C₀ * C₁, p₁, mul_pos hC₀_pos hC₁_pos, fun m =>
    calc ‖T (NuclearSpace.basis m)‖
        ≤ C₀ * (s.sup NuclearSpace.p) (NuclearSpace.basis m) := by
          have := hle (NuclearSpace.basis m)
          simp only [Seminorm.comp_apply, coe_normSeminorm, Seminorm.smul_apply,
                     NNReal.smul_def, smul_eq_mul] at this
          exact this
      _ ≤ C₀ * (C₁ * (1 + (m : ℝ)) ^ p₁) :=
          mul_le_mul_of_nonneg_left (hfinset m) (le_of_lt hC₀_pos)
      _ = C₀ * C₁ * (1 + (m : ℝ)) ^ p₁ := by ring⟩

/-! ## Nuclear representation theorem -/

/-- **Nuclear representation**: Any CLM from a nuclear space to
    a Hilbert space admits a ℓ¹-convergent series representation.

    This is the key bridge between the Schauder basis structure
    and the nuclear factorization needed for the Gaussian construction. -/
theorem nuclear_clm_representation
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (T : E →L[ℝ] H) :
    ∃ (φ : ℕ → (E →L[ℝ] ℝ)) (y : ℕ → H),
      Summable (fun m => ‖y m‖) ∧
      (∃ (q : NuclearSpace.ι (E := E)) (B : ℝ), 0 < B ∧
        ∀ (m : ℕ) (f : E), |φ m f| ≤ B * NuclearSpace.p q f) ∧
      (∀ (f : E) (w : H),
        @inner ℝ H _ w (T f) = ∑' m, φ m f * @inner ℝ H _ w (y m)) := by
  set ψ := NuclearSpace.basis (E := E) with hψ_def
  set c := NuclearSpace.coeff (E := E) with hc_def
  -- Step 1: Get polynomial growth bound for ‖T(ψ_m)‖
  obtain ⟨C_g, p₁, hCg_pos, hgrowth⟩ := clm_image_growth T
  -- Step 2: Choose exponent s = p₁ + 2 for convergence
  set s_exp : ℕ := p₁ + 2
  set s_real : ℝ := ↑s_exp with hs_def
  -- Step 3: Define y_m = (1+m)^(-s) · T(ψ_m)
  set y : ℕ → H := fun m => ((1 + (m : ℝ)) ^ (-s_real)) • T (ψ m) with hy_def
  -- Step 4: Define φ_m(f) = (1+m)^s · c_m(f)
  set φ : ℕ → (E →L[ℝ] ℝ) :=
    fun m => (1 + (m : ℝ)) ^ s_real • c m with hφ_def
  refine ⟨φ, y, ?_, ?_, ?_⟩
  · -- (i) ∑ ‖y_m‖ < ∞
    simp only [hy_def]
    refine Summable.of_norm_bounded (summable_one_add_rpow_neg_two.mul_left C_g) (fun m => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _), norm_smul,
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 1 + ↑m) _)]
    have hpos : (0 : ℝ) < 1 + ↑m := by positivity
    calc (1 + (↑m : ℝ)) ^ (-s_real) * ‖T (ψ m)‖
        ≤ (1 + (↑m : ℝ)) ^ (-s_real) * (C_g * (1 + (↑m : ℝ)) ^ p₁) :=
          mul_le_mul_of_nonneg_left (hgrowth m) (Real.rpow_nonneg (le_of_lt hpos) _)
      _ = C_g * ((1 + (↑m : ℝ)) ^ (-s_real) * (1 + (↑m : ℝ)) ^ p₁) := by ring
      _ = C_g * ((1 + (↑m : ℝ)) ^ (-s_real) * (1 + (↑m : ℝ)) ^ ((p₁ : ℝ))) := by
          congr 2; exact (Real.rpow_natCast _ _).symm
      _ = C_g * (1 + (↑m : ℝ)) ^ ((-2) : ℝ) := by
          congr 1; rw [← Real.rpow_add hpos]; congr 1
          rw [hs_def, show s_exp = p₁ + 2 from rfl]; push_cast; ring
  · -- (ii) Equicontinuity of φ_m
    obtain ⟨C_s, hCs_pos, q, hdecay_s⟩ := NuclearSpace.coeff_decay (E := E) s_exp
    exact ⟨q, C_s, hCs_pos, fun m f => by
      simp only [hφ_def, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by positivity : (0:ℝ) < 1 + ↑m) s_real)]
      rw [hs_def, Real.rpow_natCast, mul_comm]
      exact hdecay_s f m⟩
  · -- (iii) ⟨w, T(f)⟩ = ∑ φ_m(f) · ⟨w, y_m⟩
    intro f w
    rw [NuclearSpace.expansion_H T w f]
    congr 1
    ext m
    simp only [hφ_def, hy_def, ContinuousLinearMap.smul_apply, smul_eq_mul,
               inner_smul_right]
    have hpos : (0 : ℝ) < 1 + (↑m : ℝ) := by positivity
    rw [Real.rpow_neg (le_of_lt hpos)]
    have hne : (1 + (↑m : ℝ)) ^ s_real ≠ 0 := (Real.rpow_pos_of_pos hpos s_real).ne'
    field_simp; rfl

end GaussianMeasure
