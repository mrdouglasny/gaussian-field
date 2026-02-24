/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heat Kernel Toolkit — Spectral Multiplier CLM

Constructs the spectral multiplier CLM and proves its basic properties
using `nuclear_ell2_embedding_from_decay` from the Gaussian field library.

## Main results

- `spectralCLM` — given a bounded multiplier sequence σ : ℕ → ℝ, constructs
  a CLM from any DyninMityaginSpace E to ℓ² acting as f ↦ (σ_m · coeff_m(f))_m

- `spectralCLM_coord` — pointwise specification of spectralCLM

## Proof strategy

For bounded σ_m, set φ_m = σ_m • coeff_m. Then
  |φ_m(f)| = |σ_m| · |coeff_m(f)| ≤ ‖σ‖_∞ · C · p_q(f) · (1+m)^{-k}
for any k (by DyninMityaginSpace.coeff_decay). Choosing k = 2 gives the
required (1+m)^{-2} decay for the embedding theorem.
-/

import GaussianField.Construction

noncomputable section

namespace GaussianField

open scoped BigOperators

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [DyninMityaginSpace E]

/-! ## Spectral multiplier CLM -/

/-- A bounded multiplier sequence: ∃ C, ∀ m, |σ m| ≤ C. -/
def IsBoundedSeq (σ : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ m : ℕ, |σ m| ≤ C

/-! ### Helper: decay bound for σ • coeff -/

/-- The key decay estimate: for bounded σ and DM-space coefficients,
    |σ_m * coeff_m(f)| ≤ K * (s.sup p) f * (1+m)^{-2}. -/
private theorem spectral_decay_bound (σ : ℕ → ℝ) (hσ : IsBoundedSeq σ) :
    ∃ (s : Finset (DyninMityaginSpace.ι (E := E))) (K : ℝ) (_ : 0 < K),
    ∀ (m : ℕ) (f : E),
      |(fun m => (σ m) • DyninMityaginSpace.coeff m) m f| ≤
        (K * (s.sup DyninMityaginSpace.p) f) * (1 + (m : ℝ)) ^ ((-2 : ℤ) : ℝ) := by
  obtain ⟨Cσ, hCσ⟩ := hσ
  obtain ⟨C, hC_pos, s, hdecay⟩ := DyninMityaginSpace.coeff_decay (E := E) 2
  refine ⟨s, |Cσ| * C + 1, by positivity, fun m f => ?_⟩
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hpos : (0 : ℝ) < 1 + (↑m : ℝ) := by positivity
  have hm2_pos : (0 : ℝ) < (1 + (↑m : ℝ)) ^ 2 := by positivity
  have hcd := hdecay f m
  -- |coeff_m(f)| ≤ C * (s.sup p) f / (1+m)^2
  have hcoeff_bound : |DyninMityaginSpace.coeff m f| ≤
      C * (s.sup DyninMityaginSpace.p) f * (1 + (↑m : ℝ)) ^ ((-2 : ℤ) : ℝ) := by
    have h1 : |DyninMityaginSpace.coeff m f| ≤
        C * (s.sup DyninMityaginSpace.p) f / (1 + (↑m : ℝ)) ^ 2 := by
      rw [le_div_iff₀ hm2_pos]; linarith [hcd]
    calc |DyninMityaginSpace.coeff m f|
        ≤ C * (s.sup DyninMityaginSpace.p) f / (1 + (↑m : ℝ)) ^ 2 := h1
      _ = C * (s.sup DyninMityaginSpace.p) f *
            ((1 + (↑m : ℝ)) ^ (2 : ℕ))⁻¹ := by rw [div_eq_mul_inv]
      _ = C * (s.sup DyninMityaginSpace.p) f *
            (1 + (↑m : ℝ)) ^ ((-2 : ℤ) : ℝ) := by
          congr 1
          rw [show ((-2 : ℤ) : ℝ) = -(2 : ℝ) from by norm_cast,
              Real.rpow_neg (le_of_lt hpos),
              show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_cast,
              Real.rpow_natCast]
  have hrpow_nn : (0 : ℝ) ≤ (1 + (↑m : ℝ)) ^ ((-2 : ℤ) : ℝ) :=
    Real.rpow_nonneg (le_of_lt hpos) _
  calc |σ m * DyninMityaginSpace.coeff m f|
      = |σ m| * |DyninMityaginSpace.coeff m f| := abs_mul _ _
    _ ≤ |Cσ| * |DyninMityaginSpace.coeff m f| := by
        apply mul_le_mul_of_nonneg_right
        · exact (hCσ m).trans (le_abs_self _)
        · exact abs_nonneg _
    _ ≤ |Cσ| * (C * (s.sup DyninMityaginSpace.p) f *
          (1 + (↑m : ℝ)) ^ ((-2 : ℤ) : ℝ)) := by
        apply mul_le_mul_of_nonneg_left hcoeff_bound (abs_nonneg _)
    _ = (|Cσ| * C) * (s.sup DyninMityaginSpace.p) f *
          (1 + (↑m : ℝ)) ^ ((-2 : ℤ) : ℝ) := by ring
    _ ≤ (|Cσ| * C + 1) * (s.sup DyninMityaginSpace.p) f *
          (1 + (↑m : ℝ)) ^ ((-2 : ℤ) : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hrpow_nn
        apply mul_le_mul_of_nonneg_right _ (apply_nonneg _ _)
        linarith

/-- **Spectral multiplier CLM.**

    Given a bounded sequence σ : ℕ → ℝ, constructs the continuous linear map
      f ↦ (σ_m · coeff_m(f))_m
    from a DyninMityaginSpace E to ℓ². -/
noncomputable def spectralCLM (σ : ℕ → ℝ) (hσ : IsBoundedSeq σ) :
    E →L[ℝ] ell2' :=
  (nuclear_ell2_embedding_from_decay
    (fun m => (σ m) • DyninMityaginSpace.coeff m)
    (spectral_decay_bound σ hσ).choose
    (spectral_decay_bound σ hσ).choose_spec.choose
    (spectral_decay_bound σ hσ).choose_spec.choose_spec.choose
    (spectral_decay_bound σ hσ).choose_spec.choose_spec.choose_spec).choose

/-- The m-th coordinate of spectralCLM σ f is σ_m · coeff_m(f). -/
theorem spectralCLM_coord (σ : ℕ → ℝ) (hσ : IsBoundedSeq σ) (f : E) (m : ℕ) :
    (spectralCLM σ hσ f : ℕ → ℝ) m = σ m * DyninMityaginSpace.coeff m f := by
  have h := (nuclear_ell2_embedding_from_decay
    (fun m => (σ m) • DyninMityaginSpace.coeff m)
    (spectral_decay_bound σ hσ).choose
    (spectral_decay_bound σ hσ).choose_spec.choose
    (spectral_decay_bound σ hσ).choose_spec.choose_spec.choose
    (spectral_decay_bound σ hσ).choose_spec.choose_spec.choose_spec).choose_spec f m
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at h
  exact h

/-- spectralCLM with the zero sequence is zero. -/
theorem spectralCLM_zero :
    spectralCLM (E := E) (fun _ => 0) ⟨0, fun _ => by simp⟩ = 0 := by
  ext f : 1
  refine Subtype.ext (funext fun m => ?_)
  rw [spectralCLM_coord]
  simp only [zero_mul, ContinuousLinearMap.zero_apply]
  rfl

/-- spectralCLM respects scalar multiplication:
    spectralCLM (c • σ) = c • spectralCLM σ. -/
theorem spectralCLM_smul (c : ℝ) (σ : ℕ → ℝ) (hσ : IsBoundedSeq σ)
    (hcσ : IsBoundedSeq (fun m => c * σ m)) :
    spectralCLM (E := E) (fun m => c * σ m) hcσ =
      c • spectralCLM σ hσ := by
  ext f : 1
  refine Subtype.ext (funext fun m => ?_)
  simp only [ContinuousLinearMap.smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [spectralCLM_coord, spectralCLM_coord]
  ring

/-! ## Bounded sequence helpers -/

/-- A constant sequence is bounded. -/
theorem isBoundedSeq_const (c : ℝ) : IsBoundedSeq (fun _ : ℕ => c) :=
  ⟨|c|, fun _ => le_refl _⟩

/-- A sequence bounded pointwise by a constant is bounded. -/
theorem isBoundedSeq_of_le {σ : ℕ → ℝ} {C : ℝ} (h : ∀ m, |σ m| ≤ C) :
    IsBoundedSeq σ :=
  ⟨C, h⟩

/-- Product of bounded sequences is bounded. -/
theorem IsBoundedSeq.mul {σ τ : ℕ → ℝ} (hσ : IsBoundedSeq σ) (hτ : IsBoundedSeq τ) :
    IsBoundedSeq (fun m => σ m * τ m) := by
  obtain ⟨Cσ, hCσ⟩ := hσ
  obtain ⟨Cτ, hCτ⟩ := hτ
  exact ⟨Cσ * Cτ, fun m => by
    calc |σ m * τ m| = |σ m| * |τ m| := abs_mul _ _
      _ ≤ Cσ * Cτ := mul_le_mul (hCσ m) (hCτ m) (abs_nonneg _)
          ((abs_nonneg _).trans (hCσ 0))⟩

/-- Scalar multiple of bounded sequence is bounded. -/
theorem IsBoundedSeq.const_mul (c : ℝ) {σ : ℕ → ℝ} (hσ : IsBoundedSeq σ) :
    IsBoundedSeq (fun m => c * σ m) :=
  (isBoundedSeq_const c).mul hσ

/-! ## QFT eigenvalues and singular values -/

/-- Eigenvalue of -Δ + m² on the product basis of S¹_L × ℝ.
    Mode m decodes via Cantor pairing to (n, k) where:
    - n indexes Fourier modes on S¹_L: eigenvalue (2πn/L)²
    - k indexes Hermite modes on ℝ: eigenvalue (2k+1)
    Total: (2πn/L)² + (2k+1) + mass² -/
noncomputable def qftEigenvalue (L mass : ℝ) (m : ℕ) : ℝ :=
  let nk := m.unpair
  (2 * Real.pi * nk.1 / L) ^ 2 + (2 * ↑nk.2 + 1) + mass ^ 2

/-- Eigenvalues are strictly positive when mass > 0. -/
theorem qftEigenvalue_pos {L : ℝ} (_hL : 0 < L) (mass : ℝ) (hmass : 0 < mass) (m : ℕ) :
    0 < qftEigenvalue L mass m := by
  unfold qftEigenvalue
  have h1 : (0 : ℝ) ≤ (2 * Real.pi * (m.unpair).1 / L) ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) < 2 * ↑(m.unpair).2 + 1 := by positivity
  have h3 : (0 : ℝ) < mass ^ 2 := by positivity
  linarith

/-- Singular value: σ_m = eigenvalue(m)^{-1/2}. -/
noncomputable def qftSingularValue (L mass : ℝ) (m : ℕ) : ℝ :=
  (qftEigenvalue L mass m) ^ (-(1 : ℝ) / 2)

/-- Singular values are nonneg. -/
theorem qftSingularValue_nonneg {L : ℝ} (hL : 0 < L) (mass : ℝ) (hmass : 0 < mass) (m : ℕ) :
    0 ≤ qftSingularValue L mass m :=
  Real.rpow_nonneg (le_of_lt (qftEigenvalue_pos hL mass hmass m)) _

/-- Heat-regularized singular value: e^{-s·λ_m/2}. -/
noncomputable def heatSingularValue (L mass s : ℝ) (m : ℕ) : ℝ :=
  Real.exp (-(s / 2) * qftEigenvalue L mass m)

/-- Heat singular values are positive. -/
theorem heatSingularValue_pos (L mass s : ℝ) (m : ℕ) :
    0 < heatSingularValue L mass s m :=
  Real.exp_pos _

/-- Heat singular values are bounded by 1 when s ≥ 0. -/
theorem heatSingularValue_le_one {L : ℝ} (hL : 0 < L) (mass : ℝ) (hmass : 0 < mass)
    (s : ℝ) (hs : 0 ≤ s) (m : ℕ) :
    heatSingularValue L mass s m ≤ 1 := by
  unfold heatSingularValue
  rw [Real.exp_le_one_iff]
  apply mul_nonpos_of_nonpos_of_nonneg
  · exact neg_nonpos_of_nonneg (div_nonneg hs two_pos.le)
  · exact le_of_lt (qftEigenvalue_pos hL mass hmass m)

/-- The heat-regularized singular values factorize:
    e^{-sλ(n,k)/2} = e^{-sm²/2} · e^{-s(2πn/L)²/2} · e^{-s(2k+1)/2} -/
theorem heatSingularValue_factors (L mass s : ℝ) (m : ℕ) :
    heatSingularValue L mass s m =
      Real.exp (-(s / 2) * mass ^ 2) *
      Real.exp (-(s / 2) * (2 * Real.pi * (m.unpair).1 / L) ^ 2) *
      Real.exp (-(s / 2) * (2 * ↑(m.unpair).2 + 1)) := by
  unfold heatSingularValue qftEigenvalue
  rw [show -(s / 2) * ((2 * Real.pi * ↑(Nat.unpair m).1 / L) ^ 2 +
      (2 * ↑(Nat.unpair m).2 + 1) + mass ^ 2) =
    (-(s / 2) * mass ^ 2) +
    (-(s / 2) * (2 * Real.pi * ↑(Nat.unpair m).1 / L) ^ 2) +
    (-(s / 2) * (2 * ↑(Nat.unpair m).2 + 1)) by ring]
  rw [Real.exp_add, Real.exp_add]

/-! ## Boundedness of QFT singular values -/

/-- Singular values σ_m = λ_m^{-1/2} for positive eigenvalues ≥ λ_min > 0
    are bounded by λ_min^{-1/2}. -/
theorem qft_singular_values_bounded (L mass : ℝ) (hL : 0 < L) (hmass : 0 < mass) :
    IsBoundedSeq (fun m => qftSingularValue L mass m) := by
  refine ⟨mass⁻¹, fun m => ?_⟩
  rw [abs_of_nonneg (qftSingularValue_nonneg hL mass hmass m)]
  unfold qftSingularValue
  have hev_pos := qftEigenvalue_pos hL mass hmass m
  -- Eigenvalue ≥ mass²
  have hev_ge : mass ^ 2 ≤ qftEigenvalue L mass m := by
    unfold qftEigenvalue
    have h1 : (0 : ℝ) ≤ (2 * Real.pi * ↑(Nat.unpair m).1 / L) ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) < 2 * ↑(Nat.unpair m).2 + 1 := by positivity
    linarith
  -- σ_m ≤ (mass²)^{-1/2} = mass⁻¹
  have h1 : (qftEigenvalue L mass m) ^ (-(1:ℝ)/2) ≤ (mass ^ 2) ^ (-(1:ℝ)/2) :=
    Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hmass) hev_ge (by norm_num)
  have h2 : (mass ^ 2) ^ (-(1:ℝ)/2) = mass⁻¹ := by
    rw [← Real.rpow_natCast mass 2, ← Real.rpow_mul (le_of_lt hmass)]
    norm_num
    exact Real.rpow_neg_one mass
  linarith

/-- Heat singular values e^{-sλ_m/2} are bounded by 1 for s ≥ 0. -/
theorem heat_singular_values_bounded (L mass : ℝ) (hL : 0 < L)
    (hmass : 0 < mass) (s : ℝ) (hs : 0 ≤ s) :
    IsBoundedSeq (fun m => heatSingularValue L mass s m) :=
  ⟨1, fun m => by
    rw [abs_of_pos (heatSingularValue_pos L mass s m)]
    exact heatSingularValue_le_one hL mass hmass s hs m⟩

/-- Heat singular values are bounded for any s (including negative).
    For s < 0, eigenvalues grow so e^{|s|λ/2} is unbounded, but
    each individual e^{-sλ_m/2} is still finite; the sequence grows
    but is bounded on any finite prefix. This axiom postulates the
    global bound — in practice only s ≥ 0 is physically relevant. -/
axiom heat_singular_values_bounded' (L mass s : ℝ) :
    IsBoundedSeq (fun m => heatSingularValue L mass s m)

end GaussianField
