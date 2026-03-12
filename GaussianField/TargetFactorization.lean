/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Target-Indexed Nuclear Factorization

Combines the source-indexed nuclear representation with the nuclear SVD
to produce a target-indexed factorization of any nuclear-to-Hilbert CLM.

## Main result

`nuclear_clm_target_factorization`: For any CLM T : E → H with E a nuclear
Fréchet space and H separable and infinite-dimensional, there exist:
- An adapted ONB {eₙ} of H
- An intermediate Hilbert space K (= ℓ²)
- A CLM j : E → K
- Vectors vₙ ∈ K with ∑ ‖vₙ‖ < ∞
- Such that ⟨eₙ, T(f)⟩ = ⟨vₙ, j(f)⟩_K

This is the factorization theorem that drives the Gaussian construction.
The key point is that the ONB is *output* (adapted to T's nuclear structure),
not input — the construction fails for arbitrary ONBs.
-/

import GaussianField.NuclearFactorization
import GaussianField.NuclearSVD

open scoped BigOperators
open Filter TopologicalSpace

noncomputable section

namespace GaussianField

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]

/-! ## ℓ² Construction Helpers -/

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E] in
/-- The ℓ² inner product equals the tsum of products. -/
theorem ell2_inner_eq_tsum (x y : ell2') :
    @inner ℝ ell2' _ x y = ∑' m, @inner ℝ _ _ ((x : ℕ → ℝ) m) ((y : ℕ → ℝ) m) :=
  lp.inner_eq_tsum x y

omit [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [DyninMityaginSpace E] in
/-- A summable scalar sequence multiplied by a fixed ℓ² element is summable. -/
theorem summable_smul_ell2 (σ_ : ℕ → ℝ) (u : ℕ → ell2')
    (hσ : Summable σ_) (hσ_nn : ∀ n, 0 ≤ σ_ n)
    (hu : ∀ n, σ_ n ≠ 0 → ‖u n‖ = 1) :
    Summable (fun n => ‖σ_ n • u n‖) := by
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ hσ
  intro n
  rw [norm_smul]
  by_cases hσn : σ_ n = 0
  · simp [hσn]
  · rw [hu n hσn, mul_one, Real.norm_of_nonneg (hσ_nn n)]

/-! ## ℓ² embedding from decay -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

set_option linter.unusedSectionVars false in
/-- Construct the ℓ² embedding `j : E →L[ℝ] ℓ²` from nuclear coefficients with
    m-dependent decay. Given CLMs `φ_m : E →L[ℝ] ℝ` satisfying
    `|φ_m(f)| ≤ C · p_q(f) · (1+m)^{-2}`, the map `j(f) = (φ_m(f))_m` defines a CLM. -/
theorem nuclear_ell2_embedding_from_decay
    (φ : ℕ → (E →L[ℝ] ℝ))
    (s : Finset (DyninMityaginSpace.ι (E := E))) (C : ℝ) (hC : 0 < C)
    (hφ_decay : ∀ (m : ℕ) (f : E),
      |φ m f| ≤ (C * (s.sup DyninMityaginSpace.p) f) * (1 + (m : ℝ)) ^ ((-2 : ℤ) : ℝ)) :
    ∃ (j : E →L[ℝ] ell2'),
      ∀ (f : E) (m : ℕ), (j f : ℕ → ℝ) m = φ m f := by
  -- Step 1: For each f, show (φ m f)_m ∈ ℓ²
  have hφ_memℓp : ∀ (f : E), Memℓp (fun m => φ m f) 2 := by
    intro f
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat]
    set Cf := C * (s.sup DyninMityaginSpace.p) f with hCf_def
    have hbd : ∀ m : ℕ, |φ m f| ≤ Cf * (1 + (m : ℝ)) ^ ((-2 : ℤ) : ℝ) := by
      intro m; exact hφ_decay m f
    have hsq_bound : ∀ m : ℕ, ‖φ m f‖ ^ (2 : ℝ) ≤
        Cf ^ 2 * (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ) := by
      intro m
      have hpos : (0 : ℝ) < 1 + (↑m : ℝ) := by positivity
      have hCf_nn : 0 ≤ Cf * (1 + ↑m) ^ ((-2 : ℤ) : ℝ) := by
        apply mul_nonneg (mul_nonneg (le_of_lt hC) (apply_nonneg _ _))
        exact Real.rpow_nonneg (le_of_lt hpos) _
      rw [Real.norm_eq_abs]
      have h1 : |φ m f| ^ (2 : ℝ) ≤ (Cf * (1 + ↑m) ^ ((-2 : ℤ) : ℝ)) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg _) (hbd m) (by norm_num)
      have h2 : (Cf * (1 + ↑m) ^ ((-2 : ℤ) : ℝ)) ^ (2 : ℝ) =
          Cf ^ 2 * (1 + ↑m) ^ ((-4 : ℤ) : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast, Real.rpow_natCast, mul_pow]
        congr 1
        rw [← Real.rpow_natCast ((1 + (↑m : ℝ)) ^ ((-2 : ℤ) : ℝ)) 2,
            show ((2 : ℕ) : ℝ) = (2 : ℝ) from by norm_cast,
            ← Real.rpow_mul (le_of_lt hpos)]
        norm_cast
      linarith
    have h4_summ : Summable (fun m : ℕ => (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ)) := by
      have h := (summable_nat_add_iff (f := fun n => (↑n : ℝ) ^ ((-4 : ℤ) : ℝ)) 1).mpr
        (Real.summable_nat_rpow.mpr (by norm_num : ((-4 : ℤ) : ℝ) < -1))
      simp only [Nat.cast_add, Nat.cast_one] at h
      convert h using 1; ext m; push_cast; ring_nf
    exact Summable.of_nonneg_of_le
      (fun m => by positivity)
      hsq_bound
      (h4_summ.mul_left _)
  -- Step 2: Construct the CLM j : E →L[ℝ] ℓ²
  set j_fun : E → ell2' :=
    fun f => ⟨fun m => φ m f, hφ_memℓp f⟩ with hj_fun_def
  have hadd : ∀ (f g : E), j_fun (f + g) = j_fun f + j_fun g := by
    intro f g; ext m
    simp only [hj_fun_def, map_add, lp.coeFn_add, Pi.add_apply]
  have hsmul : ∀ (a : ℝ) (f : E), j_fun (a • f) = a • j_fun f := by
    intro a f; ext m
    simp [hj_fun_def, lp.coeFn_smul, map_smul, smul_eq_mul, Pi.smul_apply]
  -- Construct the linear map
  set j_lin : E →ₗ[ℝ] ell2' :=
    { toFun := j_fun, map_add' := hadd, map_smul' := hsmul }
  -- Show norm bound: ‖j_fun f‖ ≤ B * (s.sup DyninMityaginSpace.p) f
  have h4_summ : Summable (fun m : ℕ => (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ)) := by
    have h := (summable_nat_add_iff (f := fun n => (↑n : ℝ) ^ ((-4 : ℤ) : ℝ)) 1).mpr
      (Real.summable_nat_rpow.mpr (by norm_num : ((-4 : ℤ) : ℝ) < -1))
    simp only [Nat.cast_add, Nat.cast_one] at h
    convert h using 1; ext m; push_cast; ring_nf
  set ζ4 := ∑' (m : ℕ), (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ) with hζ4_def
  have h_norm_sq : ∀ f : E, ‖j_fun f‖ ^ 2 ≤
      C ^ 2 * ζ4 * ((s.sup DyninMityaginSpace.p) f) ^ 2 := by
    intro f
    rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
    simp_rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hj_fun_def]
    have h_sq_summ : Summable (fun m : ℕ => (φ m f) ^ 2) := by
      have h := lp.summable_inner (𝕜 := ℝ) (⟨fun m => φ m f, hφ_memℓp f⟩ : ell2')
        (⟨fun m => φ m f, hφ_memℓp f⟩ : ell2')
      simp only at h
      exact h.congr (fun m => by
        rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]; ring)
    have h_ptwise : ∀ m : ℕ, (φ m f) ^ 2 ≤
        (C * (s.sup DyninMityaginSpace.p) f) ^ 2 *
          (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ) := by
      intro m
      have hpos : (0 : ℝ) < 1 + (↑m : ℝ) := by positivity
      have hCf_nn : 0 ≤ C * (s.sup DyninMityaginSpace.p) f *
          (1 + ↑m) ^ ((-2 : ℤ) : ℝ) := by
        apply mul_nonneg (mul_nonneg (le_of_lt hC) (apply_nonneg _ _))
        exact Real.rpow_nonneg (le_of_lt hpos) _
      rw [← sq_abs (φ m f)]
      calc |φ m f| ^ 2
          ≤ (C * (s.sup DyninMityaginSpace.p) f *
              (1 + ↑m) ^ ((-2 : ℤ) : ℝ)) ^ 2 :=
            sq_le_sq' (by linarith [abs_nonneg (φ m f)]) (hφ_decay m f)
        _ = (C * (s.sup DyninMityaginSpace.p) f) ^ 2 *
              (1 + ↑m) ^ ((-4 : ℤ) : ℝ) := by
            rw [mul_pow]; congr 1
            rw [← Real.rpow_natCast ((1 + (↑m : ℝ)) ^ ((-2 : ℤ) : ℝ)) 2,
                ← Real.rpow_mul (le_of_lt hpos)]
            norm_cast
    calc ∑' m, (φ m f) ^ 2
        ≤ ∑' (m : ℕ), ((C * (s.sup DyninMityaginSpace.p) f) ^ 2 *
            (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ)) :=
          Summable.tsum_le_tsum h_ptwise h_sq_summ (h4_summ.mul_left _)
      _ = (C * (s.sup DyninMityaginSpace.p) f) ^ 2 * ζ4 := tsum_mul_left
      _ = C ^ 2 * ζ4 * ((s.sup DyninMityaginSpace.p) f) ^ 2 := by ring
  have hζ4_nn : 0 ≤ ζ4 := tsum_nonneg (fun m => Real.rpow_nonneg (by positivity) _)
  -- Prove continuity via Seminorm.continuous_normedSpace_rng
  set B : ℝ := C * Real.sqrt ζ4
  have hB_nn : 0 ≤ B := by positivity
  have h_norm_bound : ∀ f : E, ‖j_fun f‖ ≤ B * (s.sup DyninMityaginSpace.p) f := by
    intro f
    have hB_sq : B ^ 2 = C ^ 2 * ζ4 := by
      show (C * Real.sqrt ζ4) ^ 2 = C ^ 2 * ζ4
      rw [mul_pow, Real.sq_sqrt hζ4_nn]
    have h2 := h_norm_sq f
    have h3 : ‖j_fun f‖ ^ 2 ≤ (B * (s.sup DyninMityaginSpace.p) f) ^ 2 := by
      rw [mul_pow, hB_sq]; exact h2
    exact le_of_sq_le_sq h3 (mul_nonneg hB_nn (apply_nonneg _ _))
  have j_cont : Continuous j_lin := by
    apply WithSeminorms.continuous_normedSpace_rng ell2' DyninMityaginSpace.h_with
    refine ⟨s, ⟨⟨B, hB_nn⟩, ?_⟩⟩
    rw [Seminorm.le_def]
    intro f
    simp only [Seminorm.comp_apply, coe_normSeminorm, Seminorm.smul_apply,
               NNReal.smul_def, smul_eq_mul]
    exact h_norm_bound f
  exact ⟨⟨j_lin, j_cont⟩, fun f m => rfl⟩

/-! ## Main Theorem -/

/-- **Target-indexed nuclear factorization for nuclear CLMs.**

    Any CLM T : E → H from a nuclear Fréchet space into a separable
    infinite-dimensional Hilbert space admits a factorization through an
    intermediate Hilbert space K with an adapted ONB. -/
theorem nuclear_clm_target_factorization
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (h_inf : ¬ FiniteDimensional ℝ H)
    (T : E →L[ℝ] H) :
    ∃ (e : ℕ → H)
      (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K)
      (j : E →L[ℝ] K) (v : ℕ → K),
      Orthonormal ℝ e ∧
      (⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) ∧
      Summable (fun n => ‖v n‖) ∧
      ∀ (f : E) (n : ℕ),
        @inner ℝ H _ (e n) (T f) = @inner ℝ K _ (v n) (j f) := by
  -- Step 1: Schauder basis with coefficients
  set c := DyninMityaginSpace.coeff (E := E) with hc_def
  set ψ := DyninMityaginSpace.basis (E := E) with hψ_def
  -- Step 2: Polynomial growth of ‖T(ψ_m)‖, define s, y_m, φ_m
  obtain ⟨C_g, p₁, hCg_pos, hT_growth⟩ := clm_image_growth T
  set s_exp : ℕ := p₁ + 2
  set s_real : ℝ := ↑s_exp with hs_def
  set y : ℕ → H := fun m => ((1 + (m : ℝ)) ^ (-s_real)) • T (ψ m) with hy_def
  set φ : ℕ → (E →L[ℝ] ℝ) :=
    fun m => ((1 + (m : ℝ)) ^ s_real) • c m with hφ_def
  -- Step 3: ∑ ‖y_m‖ < ∞
  have hy_sum : Summable (fun m => ‖y m‖) := by
    simp only [hy_def]
    refine Summable.of_norm_bounded (summable_one_add_rpow_neg_two.mul_left C_g) (fun m => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _), norm_smul,
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 1 + ↑m) _)]
    have hpos : (0 : ℝ) < 1 + ↑m := by positivity
    calc (1 + (↑m : ℝ)) ^ (-s_real) * ‖T (ψ m)‖
        ≤ (1 + (↑m : ℝ)) ^ (-s_real) * (C_g * (1 + (↑m : ℝ)) ^ p₁) :=
          mul_le_mul_of_nonneg_left (hT_growth m) (Real.rpow_nonneg (le_of_lt hpos) _)
      _ = C_g * ((1 + (↑m : ℝ)) ^ (-s_real) * (1 + (↑m : ℝ)) ^ p₁) := by ring
      _ = C_g * ((1 + (↑m : ℝ)) ^ (-s_real) * (1 + (↑m : ℝ)) ^ ((p₁ : ℝ))) := by
          congr 2; exact (Real.rpow_natCast _ _).symm
      _ = C_g * (1 + (↑m : ℝ)) ^ ((-2) : ℝ) := by
          congr 1; rw [← Real.rpow_add hpos]; congr 1
          rw [hs_def, show s_exp = p₁ + 2 from rfl]; push_cast; ring
  -- Step 4: Expansion identity
  have hexpand : ∀ (f : E) (w : H),
      @inner ℝ H _ w (T f) = ∑' m, φ m f * @inner ℝ H _ w (y m) := by
    intro f w
    rw [DyninMityaginSpace.expansion_H T w f]
    congr 1; ext m
    simp only [hφ_def, hy_def, ContinuousLinearMap.smul_apply, smul_eq_mul, inner_smul_right]
    have hpos : (0 : ℝ) < 1 + (↑m : ℝ) := by positivity
    rw [Real.rpow_neg (le_of_lt hpos)]
    have hne : (1 + (↑m : ℝ)) ^ s_real ≠ 0 := (Real.rpow_pos_of_pos hpos s_real).ne'
    field_simp; rfl
  -- Step 5: Nuclear SVD
  obtain ⟨e, σ_, W, he_on, he_span, hσ_nn, hσ_sum,
          hsvd_inner, hW_unit, hW_orth, hW_zero⟩ :=
    nuclear_sequence_svd h_inf y hy_sum
  -- Step 6: m-dependent decay → ℓ² embedding
  obtain ⟨C_d, hCd_pos, s_d, hdecay_strong⟩ := DyninMityaginSpace.coeff_decay (E := E) (s_exp + 2)
  have hφ_decay : ∀ (m : ℕ) (f : E),
      |φ m f| ≤ (C_d * (s_d.sup DyninMityaginSpace.p) f) *
        (1 + (m : ℝ)) ^ ((-2 : ℤ) : ℝ) := by
    intro m f
    simp only [hφ_def, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by positivity : (0:ℝ) < 1 + ↑m) s_real)]
    have hpos : (0 : ℝ) < 1 + (↑m : ℝ) := by positivity
    have hd := hdecay_strong f m
    rw [mul_comm ((1 + (↑m : ℝ)) ^ s_real) (|c m f|)]
    -- Convert rpow s_real to nat pow
    rw [hs_def, Real.rpow_natCast]
    -- Split (1+m)^s_exp = (1+m)^(s_exp+2) · (1+m)^(-2)
    have h_split : (1 + (↑m : ℝ)) ^ s_exp =
        (1 + ↑m) ^ (s_exp + 2) * (1 + ↑m) ^ ((-2 : ℤ) : ℝ) := by
      rw [show ((-2 : ℤ) : ℝ) = (-2 : ℝ) from by norm_cast,
          ← Real.rpow_natCast (1 + (↑m : ℝ)) (s_exp + 2),
          ← Real.rpow_add hpos, ← Real.rpow_natCast (1 + (↑m : ℝ)) s_exp]
      congr 1; push_cast; ring
    rw [h_split]
    simp only [hc_def]
    have hrpow_nn : (0 : ℝ) ≤ (1 + (↑m : ℝ)) ^ ((-2 : ℤ) : ℝ) :=
      Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 1 + ↑m) _
    rw [← mul_assoc]
    gcongr
  -- Construct j : E →L[ℝ] ℓ²
  obtain ⟨j, hj_spec⟩ := nuclear_ell2_embedding_from_decay φ s_d C_d hCd_pos hφ_decay
  -- Construct v : ℕ → ℓ²
  have hv_mem : ∀ n, Memℓp (fun m => σ_ n * W n m) 2 := by
    intro n
    by_cases hσn : σ_ n = 0
    · have : (fun m => σ_ n * W n m) = 0 := by ext; simp [hσn]
      rw [this]; exact zero_memℓp
    · have : Memℓp (fun m => W n m) 2 := by
        apply memℓp_gen
        simp only [ENNReal.toReal_ofNat]
        exact (hW_unit n hσn).summable.congr (fun m => by simp [Real.norm_eq_abs, sq_abs])
      exact this.const_smul (σ_ n)
  set v : ℕ → ell2' := fun n => ⟨fun m => σ_ n * W n m, hv_mem n⟩
  -- Exhibit the existential
  refine ⟨e, ell2', inferInstance, inferInstance, inferInstance, j, v,
          he_on, he_span, ?_, ?_⟩
  · -- ∑ ‖v n‖ < ∞
    suffices h : ∀ n, ‖v n‖ = σ_ n by
      rw [show (fun n => ‖v n‖) = σ_ from funext h]
      exact hσ_sum
    intro n
    by_cases hσn : σ_ n = 0
    · have : v n = 0 := by
        ext m; simp only [v, hσn, hW_zero n hσn m, mul_zero, lp.coeFn_zero, Pi.zero_apply]
      rw [this, norm_zero, hσn]
    · have h_sq : ‖v n‖ ^ 2 = σ_ n ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
        simp_rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, v]
        simp_rw [mul_pow]
        rw [tsum_mul_left, (hW_unit n hσn).tsum_eq, mul_one]
      have h1 : (‖v n‖ - σ_ n) * (‖v n‖ + σ_ n) = 0 := by nlinarith [h_sq]
      rcases mul_eq_zero.mp h1 with h | h
      · linarith
      · linarith [norm_nonneg (v n), hσ_nn n]
  · -- ⟨e n, T f⟩ = ⟨v n, j f⟩
    intro f n
    have lhs : @inner ℝ H _ (e n) (T f) = ∑' m, (φ m f) * (σ_ n * W n m) := by
      rw [hexpand f (e n)]
      congr 1; ext m; rw [hsvd_inner]
    have rhs : @inner ℝ ell2' _ (v n) (j f) = ∑' m, (σ_ n * W n m) * (φ m f) := by
      rw [lp.inner_eq_tsum]
      congr 1; ext m
      simp only [v]
      rw [real_inner_eq_re_inner ℝ, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
      rw [hj_spec f m]; ring
    rw [lhs, rhs]
    congr 1; ext m; ring

end GaussianField
