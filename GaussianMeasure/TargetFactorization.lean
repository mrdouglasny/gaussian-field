/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Target-Indexed Nuclear Factorization

Combines the source-indexed nuclear representation with the nuclear SVD
to produce a target-indexed factorization of any Schwartz-to-Hilbert CLM.

## Main result

`schwartz_clm_target_factorization`: For any CLM T : S(D,F) → H with H
separable and infinite-dimensional, there exist:
- An adapted ONB {eₙ} of H
- An intermediate Hilbert space K (= ℓ²)
- A CLM j : S(D,F) → K
- Vectors vₙ ∈ K with ∑ ‖vₙ‖ < ∞
- Such that ⟨eₙ, T(f)⟩ = ⟨vₙ, j(f)⟩_K

This is the factorization theorem that drives the Gaussian construction.
The key point is that the ONB is *output* (adapted to T's nuclear structure),
not input — the construction fails for arbitrary ONBs.
-/

import GaussianMeasure.NuclearFactorization
import GaussianMeasure.NuclearSVD

open scoped BigOperators
open Filter TopologicalSpace

noncomputable section

namespace GaussianMeasure

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## ℓ² Construction Helpers -/

/-- The ℓ² space used as intermediate Hilbert space K. -/
abbrev ell2 := lp (fun _ : ℕ => ℝ) 2

/-- A function f : ℕ → ℝ that is in ℓ² defines an element of ell2. -/
def ell2OfMemℓp (f : ℕ → ℝ) (hf : Memℓp f 2) : ell2 := ⟨f, hf⟩

/-- The ℓ² inner product equals the tsum of products. -/
theorem ell2_inner_eq_tsum (x y : ell2) :
    @inner ℝ ell2 _ x y = ∑' m, @inner ℝ _ _ ((x : ℕ → ℝ) m) ((y : ℕ → ℝ) m) :=
  lp.inner_eq_tsum x y

/-- A summable scalar sequence multiplied by a fixed ℓ² element is summable. -/
theorem summable_smul_ell2 (σ_ : ℕ → ℝ) (u : ℕ → ell2)
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
/-- Construct the ℓ² embedding `j : 𝓢 →L[ℝ] ℓ²` from nuclear coefficients with
    m-dependent decay. Given CLMs `φ_m : 𝓢 →L[ℝ] ℝ` satisfying
    `|φ_m(f)| ≤ C · p_q(f) · (1+m)^{-2}`, the map `j(f) = (φ_m(f))_m` defines a CLM. -/
theorem schwartz_ell2_embedding_from_decay
    (φ : ℕ → (SchwartzMap D F) →L[ℝ] ℝ)
    (q : ℕ × ℕ) (C : ℝ) (hC : 0 < C)
    (hφ_decay : ∀ (m : ℕ) (f : SchwartzMap D F),
      |φ m f| ≤ C * SchwartzMap.seminorm ℝ q.1 q.2 f * (1 + (m : ℝ)) ^ ((-2 : ℤ) : ℝ)) :
    ∃ (j : (SchwartzMap D F) →L[ℝ] ell2),
      ∀ (f : SchwartzMap D F) (m : ℕ), (j f : ℕ → ℝ) m = φ m f := by
  -- Step 1: For each f, show (φ m f)_m ∈ ℓ²
  have hφ_memℓp : ∀ (f : SchwartzMap D F), Memℓp (fun m => φ m f) 2 := by
    intro f
    apply memℓp_gen
    simp only [ENNReal.toReal_ofNat]
    set Cf := C * SchwartzMap.seminorm ℝ q.1 q.2 f with hCf_def
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
  -- Step 2: Construct the CLM j : 𝓢 →L[ℝ] ℓ²
  set j_fun : (SchwartzMap D F) → ell2 :=
    fun f => ⟨fun m => φ m f, hφ_memℓp f⟩ with hj_fun_def
  have hadd : ∀ (f g : SchwartzMap D F), j_fun (f + g) = j_fun f + j_fun g := by
    intro f g; ext m
    simp [hj_fun_def, map_add]
  have hsmul : ∀ (a : ℝ) (f : SchwartzMap D F), j_fun (a • f) = a • j_fun f := by
    intro a f; ext m
    simp [hj_fun_def, lp.coeFn_smul, map_smul, smul_eq_mul, Pi.smul_apply]
  have hbound : ∃ (s : Finset (ℕ × ℕ)) (B : ℝ), 0 ≤ B ∧
      ∀ (f : SchwartzMap D F), ‖j_fun f‖ ≤ B *
        s.sup (schwartzSeminormFamily ℝ D F) f := by
    have h4_summ : Summable (fun m : ℕ => (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ)) := by
      have h := (summable_nat_add_iff (f := fun n => (↑n : ℝ) ^ ((-4 : ℤ) : ℝ)) 1).mpr
        (Real.summable_nat_rpow.mpr (by norm_num : ((-4 : ℤ) : ℝ) < -1))
      simp only [Nat.cast_add, Nat.cast_one] at h
      convert h using 1; ext m; push_cast; ring_nf
    set ζ4 := ∑' (m : ℕ), (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ) with hζ4_def
    have h_norm_sq : ∀ f : SchwartzMap D F, ‖j_fun f‖ ^ 2 ≤
        C ^ 2 * ζ4 * (SchwartzMap.seminorm ℝ q.1 q.2 f) ^ 2 := by
      intro f
      rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
      simp_rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs, hj_fun_def]
      have h_sq_summ : Summable (fun m : ℕ => (φ m f) ^ 2) := by
        have h := lp.summable_inner (𝕜 := ℝ) (⟨fun m => φ m f, hφ_memℓp f⟩ : ell2)
          (⟨fun m => φ m f, hφ_memℓp f⟩ : ell2)
        simp only [RCLike.inner_apply', RCLike.conj_to_real] at h
        exact h.congr (fun m => by ring)
      have h_ptwise : ∀ m : ℕ, (φ m f) ^ 2 ≤
          (C * SchwartzMap.seminorm ℝ q.1 q.2 f) ^ 2 *
            (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ) := by
        intro m
        have hpos : (0 : ℝ) < 1 + (↑m : ℝ) := by positivity
        have hCf_nn : 0 ≤ C * SchwartzMap.seminorm ℝ q.1 q.2 f *
            (1 + ↑m) ^ ((-2 : ℤ) : ℝ) := by
          apply mul_nonneg (mul_nonneg (le_of_lt hC) (apply_nonneg _ _))
          exact Real.rpow_nonneg (le_of_lt hpos) _
        rw [← sq_abs (φ m f)]
        calc |φ m f| ^ 2
            ≤ (C * SchwartzMap.seminorm ℝ q.1 q.2 f *
                (1 + ↑m) ^ ((-2 : ℤ) : ℝ)) ^ 2 :=
              sq_le_sq' (by linarith [abs_nonneg (φ m f)]) (hφ_decay m f)
          _ = (C * SchwartzMap.seminorm ℝ q.1 q.2 f) ^ 2 *
                (1 + ↑m) ^ ((-4 : ℤ) : ℝ) := by
              rw [mul_pow]; congr 1
              rw [← Real.rpow_natCast ((1 + (↑m : ℝ)) ^ ((-2 : ℤ) : ℝ)) 2,
                  ← Real.rpow_mul (le_of_lt hpos)]
              norm_cast
      calc ∑' m, (φ m f) ^ 2
          ≤ ∑' (m : ℕ), ((C * SchwartzMap.seminorm ℝ q.1 q.2 f) ^ 2 *
              (1 + (m : ℝ)) ^ ((-4 : ℤ) : ℝ)) :=
            Summable.tsum_le_tsum h_ptwise h_sq_summ (h4_summ.mul_left _)
        _ = (C * SchwartzMap.seminorm ℝ q.1 q.2 f) ^ 2 * ζ4 := tsum_mul_left
        _ = C ^ 2 * ζ4 * (SchwartzMap.seminorm ℝ q.1 q.2 f) ^ 2 := by ring
    have hζ4_nn : 0 ≤ ζ4 := tsum_nonneg (fun m => Real.rpow_nonneg (by positivity) _)
    refine ⟨{q}, C * Real.sqrt ζ4, by positivity, fun f => ?_⟩
    rw [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply]
    apply le_of_sq_le_sq
    · calc ‖j_fun f‖ ^ 2
          ≤ C ^ 2 * ζ4 * (SchwartzMap.seminorm ℝ q.1 q.2 f) ^ 2 := h_norm_sq f
        _ = (C * Real.sqrt ζ4 * SchwartzMap.seminorm ℝ q.1 q.2 f) ^ 2 := by
            rw [mul_pow, mul_pow, Real.sq_sqrt hζ4_nn]
    · positivity
  set j := SchwartzMap.mkCLMtoNormedSpace (σ := RingHom.id ℝ) j_fun hadd hsmul hbound
  refine ⟨j, fun f m => ?_⟩
  show (j f : ℕ → ℝ) m = φ m f
  rfl

/-! ## Main Theorem -/

/-- **Target-indexed nuclear factorization for Schwartz CLMs.**

    Any CLM T : S(D,F) → H into a separable infinite-dimensional Hilbert space
    admits a factorization through an intermediate Hilbert space K with an
    adapted ONB. -/
theorem schwartz_clm_target_factorization
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (h_inf : ¬ FiniteDimensional ℝ H)
    (T : (SchwartzMap D F) →L[ℝ] H) :
    ∃ (e : ℕ → H)
      (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℝ K) (_ : CompleteSpace K)
      (j : (SchwartzMap D F) →L[ℝ] K) (v : ℕ → K),
      Orthonormal ℝ e ∧
      (⊤ ≤ (Submodule.span ℝ (Set.range e)).topologicalClosure) ∧
      Summable (fun n => ‖v n‖) ∧
      ∀ (f : SchwartzMap D F) (n : ℕ),
        @inner ℝ H _ (e n) (T f) = @inner ℝ K _ (v n) (j f) := by
  -- Step 1: Hermite basis with coefficients
  set c := schwartzHermiteCoeff D F with hc_def
  set ψ := schwartzHermiteBasis D F with hψ_def
  have hexpand_raw := @schwartz_hermite_expansion D _ _ _ F _ _
  have hdecay := fun (k : ℝ) => schwartz_hermite_coefficient_decay (D := D) (F := F) k
  have hgrowth : ∀ (k l : ℕ), ∃ (C : ℝ) (s : ℝ), 0 < C ∧
      ∀ m : ℕ, SchwartzMap.seminorm ℝ k l (ψ m) ≤ C * (1 + (m : ℝ)) ^ s :=
    fun k l => let ⟨C, s, hC, _, h⟩ := schwartz_hermite_seminorm_growth (D := D) (F := F) k l
               ⟨C, s, hC, h⟩
  -- Step 2: Polynomial growth of ‖T(ψ_m)‖, define s, y_m, φ_m
  obtain ⟨C_g, p_exp, hCg_pos, hT_growth⟩ :=
    hermite_image_growth T ψ hgrowth
  set s : ℝ := p_exp + 2 with hs_def
  set y : ℕ → H := fun m => ((1 + (m : ℝ)) ^ (-s)) • T (ψ m) with hy_def
  set φ : ℕ → (SchwartzMap D F) →L[ℝ] ℝ :=
    fun m => ((1 + (m : ℝ)) ^ s) • c m with hφ_def
  -- Step 3: ∑ ‖y_m‖ < ∞
  have hy_sum : Summable (fun m => ‖y m‖) := by
    simp only [hy_def]
    refine Summable.of_norm_bounded (summable_one_add_rpow_neg_two.mul_left C_g) (fun m => ?_)
    rw [Real.norm_of_nonneg (norm_nonneg _), norm_smul,
        Real.norm_of_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 1 + ↑m) _)]
    have hpos : (0 : ℝ) < 1 + ↑m := by positivity
    calc (1 + (↑m : ℝ)) ^ (-s) * ‖T (ψ m)‖
        ≤ (1 + (↑m : ℝ)) ^ (-s) * (C_g * (1 + (↑m : ℝ)) ^ p_exp) :=
          mul_le_mul_of_nonneg_left (hT_growth m) (Real.rpow_nonneg (le_of_lt hpos) _)
      _ = C_g * ((1 + (↑m : ℝ)) ^ (-s) * (1 + (↑m : ℝ)) ^ p_exp) := by ring
      _ = C_g * (1 + (↑m : ℝ)) ^ ((-2) : ℝ) := by
          congr 1; rw [← Real.rpow_add hpos]; congr 1; linarith
  -- Step 4: Expansion identity
  have hexpand : ∀ (f : SchwartzMap D F) (w : H),
      @inner ℝ H _ w (T f) = ∑' m, φ m f * @inner ℝ H _ w (y m) := by
    intro f w
    rw [hexpand_raw T w f]
    congr 1; ext m
    simp only [hφ_def, hy_def, hc_def, hψ_def,
               ContinuousLinearMap.smul_apply, smul_eq_mul, inner_smul_right]
    have hpos : (0 : ℝ) < 1 + (↑m : ℝ) := by positivity
    rw [Real.rpow_neg (le_of_lt hpos)]
    have hne : (1 + (↑m : ℝ)) ^ s ≠ 0 := (Real.rpow_pos_of_pos hpos s).ne'
    field_simp
  -- Step 5: Nuclear SVD
  obtain ⟨e, σ_, W, he_on, he_span, hσ_nn, hσ_sum,
          hsvd_inner, hW_unit, hW_orth, hW_zero⟩ :=
    nuclear_sequence_svd h_inf y hy_sum
  -- Step 6: m-dependent decay → ℓ² embedding
  obtain ⟨C_d, q_d, hCd_pos, hdecay_strong⟩ := hdecay (s + 2)
  have hφ_decay : ∀ (m : ℕ) (f : SchwartzMap D F),
      |φ m f| ≤ C_d * SchwartzMap.seminorm ℝ q_d.1 q_d.2 f *
        (1 + (m : ℝ)) ^ ((-2 : ℤ) : ℝ) := by
    intro m f
    simp only [hφ_def, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by positivity : (0:ℝ) < 1 + ↑m) s)]
    have hpos : (0 : ℝ) < 1 + (↑m : ℝ) := by positivity
    have hd := hdecay_strong f m
    rw [show ((-2 : ℤ) : ℝ) = (-2 : ℝ) from by norm_cast]
    rw [mul_comm ((1 + (↑m : ℝ)) ^ s) (|c m f|)]
    calc |c m f| * (1 + ↑m) ^ s
        = |c m f| * (1 + ↑m) ^ (s + 2 + (-2 : ℝ)) := by congr 1; congr 1; ring
      _ = |c m f| * ((1 + ↑m) ^ (s + 2) * (1 + ↑m) ^ ((-2) : ℝ)) := by
          rw [Real.rpow_add hpos]
      _ = |c m f| * (1 + ↑m) ^ (s + 2) * (1 + ↑m) ^ ((-2) : ℝ) := by ring
      _ ≤ C_d * SchwartzMap.seminorm ℝ q_d.1 q_d.2 f * (1 + ↑m) ^ ((-2) : ℝ) := by
          apply mul_le_mul_of_nonneg_right hd (Real.rpow_nonneg (le_of_lt hpos) _)
  -- Construct j : 𝓢 →L[ℝ] ℓ²
  obtain ⟨j, hj_spec⟩ := schwartz_ell2_embedding_from_decay φ q_d C_d hCd_pos hφ_decay
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
  set v : ℕ → ell2 := fun n => ⟨fun m => σ_ n * W n m, hv_mem n⟩
  -- Exhibit the existential
  refine ⟨e, ell2, inferInstance, inferInstance, inferInstance, j, v,
          he_on, he_span, ?_, ?_⟩
  · -- ∑ ‖v n‖ < ∞
    suffices h : ∀ n, ‖v n‖ = σ_ n by
      rw [show (fun n => ‖v n‖) = σ_ from funext h]
      exact hσ_sum
    intro n
    by_cases hσn : σ_ n = 0
    · have : v n = 0 := by
        ext m; simp [v, hW_zero n hσn m, hσn]
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
    have rhs : @inner ℝ ell2 _ (v n) (j f) = ∑' m, (σ_ n * W n m) * (φ m f) := by
      rw [lp.inner_eq_tsum]
      congr 1; ext m
      simp only [v]
      rw [RCLike.inner_apply', RCLike.conj_to_real]
      rw [hj_spec f m]
    rw [lhs, rhs]
    congr 1; ext m; ring

end GaussianMeasure
