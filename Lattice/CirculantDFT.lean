/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Circulant DFT: Eigenvectors, Spectral Expansion, and Convergence

Proves that the lattice Fourier basis functions are eigenvectors of the
1D discrete Laplacian, constructs the DFT eigenbasis, proves the corrected
spectral expansion of the heat kernel bilinear form, and establishes the
full 1D lattice-to-continuum convergence.

## Main results

- `negLaplacian1d_cos_eigenvalue` / `sin_eigenvalue` — eigenvalue formulas
- `negLaplacian1d_dft_eigenvector` — normalized DFT basis eigenvector property
- `latticeFourierBasis` — DFT eigenbasis construction via linear independence + span
- `dft_expansion` — DFT expansion: f = Σ (⟨f,φ_m⟩/‖φ_m‖²) · φ_m
- `latticeHeatKernelBilinear1d_eq_spectral'` — corrected spectral expansion with /normSq
- `lattice_heatKernel_tendsto_continuum_1d` — full 1D heat kernel convergence
- `latticeDFTCoeff1d_quadratic_bound'` — |c_m(f)| ≤ C/(1+m)²

## References

- Davis, *Circulant Matrices*, Ch. 3
- Katznelson, *Harmonic Analysis*, §I.2
-/

import Lattice.HeatKernelConvergence1d

noncomputable section

namespace GaussianField

open Real Matrix Filter

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## ZMod.val shift lemmas

The key property: `cos(2πk·z/N)` and `sin(2πk·z/N)` are N-periodic in z,
so the ZMod wrapping of `.val` does not affect their values.

The proof uses ℤ-divisibility: `z.val + 1` and `(z+1).val` are congruent
mod N in ℤ, so their cos/sin values at `2πk·_/N` agree. -/

/-- `cos(2πk·(z+1).val/N) = cos(2πk·(z.val+1)/N)` for `z : ZMod N`. -/
theorem cos_zmod_succ (N : ℕ) [NeZero N] (k : ℕ) (z : ZMod N) :
    cos (2 * π * k * ((z + 1 : ZMod N).val : ℝ) / N) =
    cos (2 * π * k * ((z.val : ℝ) + 1) / N) := by
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- Both (z+1).val and z.val+1 represent z+1 in ZMod N, so they differ by N*q in ℤ
  have hdvd : (N : ℤ) ∣ ((z.val : ℤ) + 1 - ((z + 1 : ZMod N).val : ℤ)) := by
    rw [← Int.modEq_iff_dvd, ← ZMod.intCast_eq_intCast_iff]
    simp
  obtain ⟨q, hq⟩ := hdvd
  -- Cast the divisibility identity to ℝ
  have hqR : (z.val : ℝ) + 1 - ((z + 1 : ZMod N).val : ℝ) = ↑N * (q : ℝ) := by
    have := congr_arg (Int.cast (R := ℝ)) hq
    push_cast at this ⊢; linarith
  -- The cos arguments differ by 2πkq, and cos is 2π-periodic
  suffices h : 2 * π * ↑k * ((z.val : ℝ) + 1) / ↑N =
      2 * π * ↑k * ((z + 1 : ZMod N).val : ℝ) / ↑N + ↑(↑k * q) * (2 * π) by
    rw [h, cos_add_int_mul_two_pi]
  push_cast; field_simp; nlinarith [hqR]

/-- `sin(2πk·(z+1).val/N) = sin(2πk·(z.val+1)/N)` for `z : ZMod N`. -/
theorem sin_zmod_succ (N : ℕ) [NeZero N] (k : ℕ) (z : ZMod N) :
    sin (2 * π * k * ((z + 1 : ZMod N).val : ℝ) / N) =
    sin (2 * π * k * ((z.val : ℝ) + 1) / N) := by
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hdvd : (N : ℤ) ∣ ((z.val : ℤ) + 1 - ((z + 1 : ZMod N).val : ℤ)) := by
    rw [← Int.modEq_iff_dvd, ← ZMod.intCast_eq_intCast_iff]
    simp
  obtain ⟨q, hq⟩ := hdvd
  have hqR : (z.val : ℝ) + 1 - ((z + 1 : ZMod N).val : ℝ) = ↑N * (q : ℝ) := by
    have := congr_arg (Int.cast (R := ℝ)) hq
    push_cast at this ⊢; linarith
  suffices h : 2 * π * ↑k * ((z.val : ℝ) + 1) / ↑N =
      2 * π * ↑k * ((z + 1 : ZMod N).val : ℝ) / ↑N + ↑(↑k * q) * (2 * π) by
    rw [h, sin_add_int_mul_two_pi]
  push_cast; field_simp; nlinarith [hqR]

/-- `cos(2πk·(z-1).val/N) = cos(2πk·(z.val-1)/N)` for `z : ZMod N`. -/
theorem cos_zmod_pred (N : ℕ) [NeZero N] (k : ℕ) (z : ZMod N) :
    cos (2 * π * k * ((z - 1 : ZMod N).val : ℝ) / N) =
    cos (2 * π * k * ((z.val : ℝ) - 1) / N) := by
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hdvd : (N : ℤ) ∣ ((z.val : ℤ) - 1 - ((z - 1 : ZMod N).val : ℤ)) := by
    rw [← Int.modEq_iff_dvd, ← ZMod.intCast_eq_intCast_iff]
    simp
  obtain ⟨q, hq⟩ := hdvd
  have hqR : (z.val : ℝ) - 1 - ((z - 1 : ZMod N).val : ℝ) = ↑N * (q : ℝ) := by
    have := congr_arg (Int.cast (R := ℝ)) hq
    push_cast at this ⊢; linarith
  suffices h : 2 * π * ↑k * ((z.val : ℝ) - 1) / ↑N =
      2 * π * ↑k * ((z - 1 : ZMod N).val : ℝ) / ↑N + ↑(↑k * q) * (2 * π) by
    rw [h, cos_add_int_mul_two_pi]
  push_cast; field_simp; nlinarith [hqR]

/-- `sin(2πk·(z-1).val/N) = sin(2πk·(z.val-1)/N)` for `z : ZMod N`. -/
theorem sin_zmod_pred (N : ℕ) [NeZero N] (k : ℕ) (z : ZMod N) :
    sin (2 * π * k * ((z - 1 : ZMod N).val : ℝ) / N) =
    sin (2 * π * k * ((z.val : ℝ) - 1) / N) := by
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hdvd : (N : ℤ) ∣ ((z.val : ℤ) - 1 - ((z - 1 : ZMod N).val : ℤ)) := by
    rw [← Int.modEq_iff_dvd, ← ZMod.intCast_eq_intCast_iff]
    simp
  obtain ⟨q, hq⟩ := hdvd
  have hqR : (z.val : ℝ) - 1 - ((z - 1 : ZMod N).val : ℝ) = ↑N * (q : ℝ) := by
    have := congr_arg (Int.cast (R := ℝ)) hq
    push_cast at this ⊢; linarith
  suffices h : 2 * π * ↑k * ((z.val : ℝ) - 1) / ↑N =
      2 * π * ↑k * ((z - 1 : ZMod N).val : ℝ) / ↑N + ↑(↑k * q) * (2 * π) by
    rw [h, sin_add_int_mul_two_pi]
  push_cast; field_simp; nlinarith [hqR]

/-! ## Pure trig eigenvector identities -/

/-- `1 - cos(2x) = 2sin²(x)` -/
private lemma one_sub_cos_double (x : ℝ) : 1 - cos (2 * x) = 2 * sin x ^ 2 := by
  linarith [sin_sq_eq_half_sub x]

/-- **Cosine eigenvector identity (pure trig).**

`a⁻² [2cos(θ) - cos(θ+δ) - cos(θ-δ)] = a⁻² · 2(1-cos(δ)) · cos(θ)`

Proof: `cos(θ+δ) + cos(θ-δ) = 2cos(δ)cos(θ)`. -/
theorem negLaplacian1d_cos_eigenvector (a : ℝ) (θ δ : ℝ) :
    a⁻¹ ^ 2 * (2 * cos θ - cos (θ + δ) - cos (θ - δ)) =
    a⁻¹ ^ 2 * (2 * (1 - cos δ)) * cos θ := by
  have : cos (θ + δ) + cos (θ - δ) = 2 * cos δ * cos θ := by
    rw [cos_add, cos_sub]; ring
  nlinarith

/-- The eigenvalue identity: `a⁻² · 2(1 - cos(2πk/N)) = (4/a²)sin²(πk/N)`. -/
theorem eigenvalue_formula (a : ℝ) (N k : ℕ) :
    a⁻¹ ^ 2 * (2 * (1 - cos (2 * π * k / N))) =
    (4 / a ^ 2) * sin (π * k / N) ^ 2 := by
  have h1 : 1 - cos (2 * π * (k : ℝ) / N) = 2 * sin (π * k / N) ^ 2 := by
    rw [show 2 * π * (k : ℝ) / (N : ℝ) = 2 * (π * k / N) from by ring]
    exact one_sub_cos_double _
  rw [h1, show a⁻¹ ^ 2 = 1 / a ^ 2 from by rw [inv_pow, one_div]]
  ring

/-- **Sine eigenvector identity.** Same eigenvalue. -/
theorem negLaplacian1d_sin_eigenvector (a : ℝ) (θ δ : ℝ) :
    a⁻¹ ^ 2 * (2 * sin θ - sin (θ + δ) - sin (θ - δ)) =
    a⁻¹ ^ 2 * (2 * (1 - cos δ)) * sin θ := by
  have : sin (θ + δ) + sin (θ - δ) = 2 * cos δ * sin θ := by
    rw [sin_add, sin_sub]; ring
  nlinarith

/-! ## Bijection ZMod N ≃ FinLatticeSites 1 N -/

/-- Bijection between `ZMod N` and `FinLatticeSites 1 N`. -/
def zmodToFin1 (N : ℕ) : ZMod N ≃ FinLatticeSites 1 N where
  toFun z := fun _ => z
  invFun x := x 0
  left_inv _ := rfl
  right_inv x := by ext i; fin_cases i; rfl

/-- Sum over `FinLatticeSites 1 N` equals sum over `ZMod N`. -/
theorem sum_fin1_eq_sum_zmod {N : ℕ} [NeZero N]
    (f : FinLatticeSites 1 N → ℝ) :
    ∑ x : FinLatticeSites 1 N, f x = ∑ z : ZMod N, f (fun _ => z) :=
  Fintype.sum_equiv (zmodToFin1 N).symm _ _ (fun x => by
    show f x = f (fun _ => x 0)
    congr 1; ext i; fin_cases i; rfl)

/-! ## Eigenvector transfer identity -/

/-- **The eigenvector transfer identity.**

For the m-th Fourier mode with m < N:
`λ_m · c_m(f) = ∑_z (-Δ_a fN)(z) · φ_m(z)`

This transfers the Laplacian from the eigenvector to the test function
via self-adjointness. -/
theorem eigenvector_transfer (N : ℕ) [NeZero N]
    (f : SmoothMap_Circle L ℝ) (m : ℕ) (hm : m < N) :
    latticeEigenvalue1d N (circleSpacing L N) m *
      latticeDFTCoeff1d L N f m =
    ∑ z : ZMod N,
      ((circleSpacing L N)⁻¹ ^ 2 *
        (2 * circleRestriction L N f z -
         circleRestriction L N f (z + 1) -
         circleRestriction L N f (z - 1))) *
      latticeFourierBasisFun N m z := by
  -- Step 1: Unfold latticeDFTCoeff1d and pull eigenvalue into sum
  simp only [latticeDFTCoeff1d, if_pos hm]
  rw [Finset.mul_sum]
  -- Step 2: Eigenvector property (pointwise)
  have h_eigvec : ∀ z : ZMod N,
      latticeEigenvalue1d N (circleSpacing L N) m * latticeFourierBasisFun N m z =
      (circleSpacing L N)⁻¹ ^ 2 * (2 * latticeFourierBasisFun N m z -
        latticeFourierBasisFun N m (z + 1) -
        latticeFourierBasisFun N m (z - 1)) := by
    intro z
    cases m with
    | zero =>
      simp [latticeEigenvalue1d, latticeFourierBasisFun,
        SmoothMap_Circle.fourierFreq, sin_zero]
      right; ring
    | succ n =>
      simp only [latticeFourierBasisFun]
      set k := n / 2 + 1
      have hk : SmoothMap_Circle.fourierFreq (n + 1) = k := rfl
      split
      · -- cos mode
        dsimp only []
        rw [cos_zmod_succ N k z, cos_zmod_pred N k z]
        set θ := 2 * π * ↑k * (↑z.val : ℝ) / ↑N
        set δ := 2 * π * ↑k / ↑N
        rw [show 2 * π * ↑k * ((↑z.val : ℝ) + 1) / ↑N = θ + δ from by
              simp only [θ, δ]; ring,
            show 2 * π * ↑k * ((↑z.val : ℝ) - 1) / ↑N = θ - δ from by
              simp only [θ, δ]; ring]
        have h_cos_eig := negLaplacian1d_cos_eigenvector (circleSpacing L N) θ δ
        have h_ev : latticeEigenvalue1d N (circleSpacing L N) (n + 1) =
            (circleSpacing L N)⁻¹ ^ 2 * (2 * (1 - cos δ)) := by
          simp only [δ, latticeEigenvalue1d, hk]
          linarith [eigenvalue_formula (circleSpacing L N) N k]
        rw [h_ev]; linear_combination -√(2 / ↑N) * h_cos_eig
      · -- sin mode
        dsimp only []
        rw [sin_zmod_succ N k z, sin_zmod_pred N k z]
        set θ := 2 * π * ↑k * (↑z.val : ℝ) / ↑N
        set δ := 2 * π * ↑k / ↑N
        rw [show 2 * π * ↑k * ((↑z.val : ℝ) + 1) / ↑N = θ + δ from by
              simp only [θ, δ]; ring,
            show 2 * π * ↑k * ((↑z.val : ℝ) - 1) / ↑N = θ - δ from by
              simp only [θ, δ]; ring]
        have h_sin_eig := negLaplacian1d_sin_eigenvector (circleSpacing L N) θ δ
        have h_ev : latticeEigenvalue1d N (circleSpacing L N) (n + 1) =
            (circleSpacing L N)⁻¹ ^ 2 * (2 * (1 - cos δ)) := by
          simp only [δ, latticeEigenvalue1d, hk]
          linarith [eigenvalue_formula (circleSpacing L N) N k]
        rw [h_ev]; linear_combination -√(2 / ↑N) * h_sin_eig
  -- Step 3: Self-adjointness of discrete Laplacian
  have h_adj : ∀ (u v : ZMod N → ℝ),
      ∑ z : ZMod N, u z * (2 * v z - v (z + 1) - v (z - 1)) =
      ∑ z : ZMod N, (2 * u z - u (z + 1) - u (z - 1)) * v z := by
    intro u v
    have hs : ∑ z : ZMod N, u z * v (z + 1) = ∑ z : ZMod N, u (z - 1) * v z :=
      Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _ (fun z => by
        show u z * v (z + 1) = u ((z + 1) - 1) * v (z + 1)
        rw [add_sub_cancel_right])
    have hp : ∑ z : ZMod N, u z * v (z - 1) = ∑ z : ZMod N, u (z + 1) * v z :=
      Fintype.sum_equiv (Equiv.addRight ((-1 : ZMod N))) _ _ (fun z => by
        have h1 : (Equiv.addRight (-1 : ZMod N)) z = z - 1 := by
          simp [Equiv.addRight, sub_eq_add_neg]
        rw [h1, sub_add_cancel])
    calc ∑ z, u z * (2 * v z - v (z + 1) - v (z - 1))
        = ∑ z, (2 * (u z * v z) - u z * v (z + 1) - u z * v (z - 1)) := by
          congr 1; ext z; ring
      _ = 2 * ∑ z, u z * v z - ∑ z, u z * v (z + 1) - ∑ z, u z * v (z - 1) := by
          simp only [Finset.sum_sub_distrib, Finset.mul_sum]
      _ = 2 * ∑ z, u z * v z - ∑ z, u (z - 1) * v z - ∑ z, u (z + 1) * v z := by
          rw [hs, hp]
      _ = ∑ z, (2 * u z - u (z + 1) - u (z - 1)) * v z := by
          conv_rhs => arg 2; ext z; rw [show (2 * u z - u (z + 1) - u (z - 1)) * v z =
              2 * (u z * v z) - u (z + 1) * v z - u (z - 1) * v z from by ring]
          simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]; linarith
  -- Step 4: Combine using calc
  set fN := circleRestriction L N f
  set φ := latticeFourierBasisFun N m
  set c := (circleSpacing L N)⁻¹ ^ 2
  conv_lhs => arg 2; ext z
              rw [show latticeEigenvalue1d N (circleSpacing L N) m * (fN z * φ z) =
                  fN z * (latticeEigenvalue1d N (circleSpacing L N) m * φ z) from by ring,
                h_eigvec z]
  simp_rw [show ∀ z : ZMod N, fN z * (c * (2 * φ z - φ (z + 1) - φ (z - 1))) =
      c * (fN z * (2 * φ z - φ (z + 1) - φ (z - 1))) from fun z => by ring]
  rw [← Finset.mul_sum, h_adj fN φ, Finset.mul_sum]
  congr 1; ext z; ring

/-! ## Second difference bound -/

/-- **Symmetric second difference bound.**
`|f(x+h) + f(x-h) - 2f(x)| ≤ h² · ‖f''‖_∞` -/
theorem symmetric_second_diff_bound (f : SmoothMap_Circle L ℝ) (x h : ℝ) :
    |f (x + h) + f (x - h) - 2 * f x| ≤
    h ^ 2 * SmoothMap_Circle.sobolevSeminorm 2 f := by
  -- Reduce to h ≥ 0 by symmetry (h² = (-h)²)
  suffices key : ∀ t : ℝ, 0 ≤ t →
      |f (x + t) + f (x - t) - 2 * f x| ≤ t ^ 2 * SmoothMap_Circle.sobolevSeminorm 2 f by
    rcases le_or_gt 0 h with hh | hh
    · exact key h hh
    · have key_neg := key (-h) (by linarith)
      -- key_neg : |f(x+(-h)) + f(x-(-h)) - 2*f(x)| ≤ (-h)² * ...
      rw [sub_neg_eq_add] at key_neg
      -- Now: |f(x+(-h)) + f(x+h) - 2*f(x)| ≤ (-h)² * ...
      rw [show f (x + -h) + f (x + h) - 2 * f x =
          f (x + h) + f (x + -h) - 2 * f x from by ring,
          neg_sq] at key_neg
      -- key_neg : |f(x+h) + f(x-h) - 2*f(x)| ≤ h² * ... (x-h = x+(-h) def'ly)
      exact key_neg
  intro t ht
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · simp; linarith [SmoothMap_Circle.sobolevSeminorm_nonneg (L := L) 2 f]
  -- For t > 0, apply the Lagrange Taylor remainder with n = 1
  have hlt_fwd : x < x + t := by linarith
  have hf_cd2 : ContDiffOn ℝ (↑(1 + 1 : ℕ)) (⇑f) (Set.Icc x (x + t)) :=
    f.smooth.contDiffOn.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨c₁, hc₁, hc₁_eq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hlt_fwd hf_cd2
  -- Backward direction: expand g(s) = f(x-s) on [0, t]
  have hg_cd2 : ContDiffOn ℝ (↑(1 + 1 : ℕ))
      (fun s => (f : ℝ → ℝ) (x - s)) (Set.Icc 0 t) := by
    apply ContDiffOn.of_le _ (WithTop.coe_le_coe.mpr le_top)
    exact (f.smooth.comp ((contDiff_const.sub contDiff_id).of_le le_top)).contDiffOn
  obtain ⟨c₂, hc₂, hc₂_eq⟩ := taylor_mean_remainder_lagrange_iteratedDeriv ht_pos hg_cd2
  -- Simplify taylorWithinEval at n=1
  have hP₁ : taylorWithinEval (⇑f) 1 (Set.Icc x (x + t)) x (x + t) =
      f x + (x + t - x) * derivWithin (⇑f) (Set.Icc x (x + t)) x := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval]
    simp [iteratedDerivWithin_one, smul_eq_mul]
  have hQ₁ : taylorWithinEval (fun s => (f : ℝ → ℝ) (x - s)) 1 (Set.Icc 0 t) 0 t =
      (f : ℝ → ℝ) (x - 0) + (t - 0) *
        derivWithin (fun s => (f : ℝ → ℝ) (x - s)) (Set.Icc 0 t) 0 := by
    rw [taylorWithinEval_succ, taylor_within_zero_eval]
    simp [iteratedDerivWithin_one, smul_eq_mul]
  -- derivWithin on smooth functions = deriv
  have hDW_f : derivWithin (⇑f) (Set.Icc x (x + t)) x = deriv (⇑f) x :=
    (f.smooth.differentiable (by simp)).differentiableAt.derivWithin
      (uniqueDiffOn_Icc hlt_fwd x (Set.left_mem_Icc.mpr hlt_fwd.le))
  have hDW_g : derivWithin (fun s => (f : ℝ → ℝ) (x - s)) (Set.Icc 0 t) 0 =
      -deriv (⇑f) x := by
    have hud : UniqueDiffWithinAt ℝ (Set.Icc 0 t) 0 :=
      uniqueDiffOn_Icc ht_pos 0 (Set.left_mem_Icc.mpr ht_pos.le)
    have hg_diff : DifferentiableAt ℝ (fun s => (f : ℝ → ℝ) (x - s)) 0 :=
      ((f.smooth.comp ((contDiff_const.sub contDiff_id).of_le le_top)).differentiable
        (by simp)).differentiableAt
    rw [hg_diff.derivWithin hud]
    have hd : HasDerivAt (fun s => (f : ℝ → ℝ) (x - s)) (-deriv (⇑f) x) 0 := by
      have hf_da : DifferentiableAt ℝ (⇑f) x :=
        (f.smooth.differentiable (by simp)).differentiableAt
      have h1 : HasDerivAt (⇑f) (deriv (⇑f) x) ((fun s => x - s) 0) := by
        simp only [sub_zero]; exact hf_da.hasDerivAt
      have h2 : HasDerivAt (fun s : ℝ => x - s) (-1 : ℝ) (0 : ℝ) := by
        simpa using (hasDerivAt_const (0 : ℝ) x).sub (hasDerivAt_id (0 : ℝ))
      have h3 := h1.comp (0 : ℝ) h2
      simp at h3; convert h3 using 1
    exact hd.deriv
  rw [hP₁, hDW_f] at hc₁_eq; simp only [add_sub_cancel_left] at hc₁_eq
  rw [hQ₁, hDW_g] at hc₂_eq; simp only [sub_zero] at hc₂_eq
  have hsum : f (x + t) + f (x - t) - 2 * f x =
      (iteratedDeriv 2 (⇑f) c₁ + iteratedDeriv 2 (fun s => (f : ℝ → ℝ) (x - s)) c₂) *
        t ^ 2 / ↑(Nat.factorial 2) := by linarith [hc₁_eq, hc₂_eq]
  rw [hsum]
  have h2_fact : (Nat.factorial 2 : ℝ) = 2 := by norm_num
  rw [h2_fact, abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2),
    abs_mul, abs_of_nonneg (sq_nonneg t)]
  have hbd₁ : |iteratedDeriv 2 (⇑f) c₁| ≤ SmoothMap_Circle.sobolevSeminorm 2 f := by
    rw [← Real.norm_eq_abs]
    exact SmoothMap_Circle.norm_iteratedDeriv_le_sobolevSeminorm' f 2 c₁
  have hbd₂ : |iteratedDeriv 2 (fun s => (f : ℝ → ℝ) (x - s)) c₂| ≤
      SmoothMap_Circle.sobolevSeminorm 2 f := by
    have hchain : iteratedDeriv 2 (fun s => (f : ℝ → ℝ) (x - s)) c₂ =
        iteratedDeriv 2 (⇑f) (x - c₂) := by
      rw [show (fun s => (f : ℝ → ℝ) (x - s)) = (fun s => (f : ℝ → ℝ) ((-1) * s + x)) from by
        ext s; ring_nf]
      have hg_cd : ContDiff ℝ (↑(2 : ℕ)) (fun t => (f : ℝ → ℝ) (t + x)) := by
        apply ContDiff.of_le _ (WithTop.coe_le_coe.mpr le_top)
        exact f.smooth.comp ((contDiff_id.add contDiff_const).of_le le_top)
      rw [congr_fun (iteratedDeriv_comp_const_mul hg_cd (-1)) c₂,
        congr_fun (iteratedDeriv_comp_add_const 2 (⇑f) x) ((-1) * c₂)]
      simp; ring_nf
    rw [hchain, ← Real.norm_eq_abs]
    exact SmoothMap_Circle.norm_iteratedDeriv_le_sobolevSeminorm' f 2 (x - c₂)
  calc |iteratedDeriv 2 (⇑f) c₁ +
          iteratedDeriv 2 (fun s => (f : ℝ → ℝ) (x - s)) c₂| * t ^ 2 / 2
      ≤ (|iteratedDeriv 2 (⇑f) c₁| +
          |iteratedDeriv 2 (fun s => (f : ℝ → ℝ) (x - s)) c₂|) * t ^ 2 / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
        exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (sq_nonneg t)
    _ ≤ (SmoothMap_Circle.sobolevSeminorm 2 f + SmoothMap_Circle.sobolevSeminorm 2 f) *
          t ^ 2 / 2 := by
        apply div_le_div_of_nonneg_right _ (by norm_num : (0:ℝ) ≤ 2)
        exact mul_le_mul_of_nonneg_right (add_le_add hbd₁ hbd₂) (sq_nonneg t)
    _ = t ^ 2 * SmoothMap_Circle.sobolevSeminorm 2 f := by ring

/-! ## Laplacian restriction bounds -/

/-- The Laplacian of a restricted test function is bounded. -/
theorem negLaplacian_restriction_bound (N : ℕ) [NeZero N]
    (f : SmoothMap_Circle L ℝ) (z : ZMod N) :
    |(circleSpacing L N)⁻¹ ^ 2 *
      (2 * circleRestriction L N f z -
       circleRestriction L N f (z + 1) -
       circleRestriction L N f (z - 1))| ≤
    Real.sqrt (circleSpacing L N) * SmoothMap_Circle.sobolevSeminorm 2 f := by
  set a := circleSpacing L N with ha_def
  set x := circlePoint L N z with hx_def
  have ha_pos : 0 < a := circleSpacing_pos L N
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  simp only [circleRestriction_apply]
  -- Use L-periodicity to relate circlePoint at z±1 to x±a
  have hsucc : f (circlePoint L N (z + 1)) = f (x + a) := by
    simp only [x, a, circlePoint, circleSpacing]
    have hdvd : (N : ℤ) ∣ ((z.val : ℤ) + 1 - ((z + 1 : ZMod N).val : ℤ)) := by
      rw [← Int.modEq_iff_dvd, ← ZMod.intCast_eq_intCast_iff]; simp
    obtain ⟨q, hq⟩ := hdvd
    have hval : ((z + 1 : ZMod N).val : ℝ) = (z.val : ℝ) + 1 - (N : ℝ) * (q : ℝ) := by
      have := congr_arg (Int.cast (R := ℝ)) hq; push_cast at this ⊢; linarith
    conv_lhs => rw [show ((z + 1 : ZMod N).val : ℝ) * L / ↑N =
        (↑z.val * L / ↑N + L / ↑N) - ↑q * L from by rw [hval]; field_simp [hN_ne]]
    exact f.periodic.sub_int_mul_eq q
  have hpred : f (circlePoint L N (z - 1)) = f (x - a) := by
    simp only [x, a, circlePoint, circleSpacing]
    have hdvd : (N : ℤ) ∣ ((z.val : ℤ) - 1 - ((z - 1 : ZMod N).val : ℤ)) := by
      rw [← Int.modEq_iff_dvd, ← ZMod.intCast_eq_intCast_iff]; simp
    obtain ⟨q, hq⟩ := hdvd
    have hval : ((z - 1 : ZMod N).val : ℝ) = (z.val : ℝ) - 1 - (N : ℝ) * (q : ℝ) := by
      have := congr_arg (Int.cast (R := ℝ)) hq; push_cast at this ⊢; linarith
    conv_lhs => rw [show ((z - 1 : ZMod N).val : ℝ) * L / ↑N =
        (↑z.val * L / ↑N - L / ↑N) - ↑q * L from by rw [hval]; field_simp [hN_ne]]
    exact f.periodic.sub_int_mul_eq q
  rw [hsucc, hpred]
  -- Factor out √a, rearrange to isolate the second-difference
  rw [show 2 * (Real.sqrt a * f x) - Real.sqrt a * f (x + a) - Real.sqrt a * f (x - a) =
      Real.sqrt a * (-(f (x + a) + f (x - a) - 2 * f x)) from by ring,
    show a⁻¹ ^ 2 * (Real.sqrt a * -(f (x + a) + f (x - a) - 2 * f x)) =
      Real.sqrt a * (a⁻¹ ^ 2 * -(f (x + a) + f (x - a) - 2 * f x)) from by ring,
    abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ a⁻¹ ^ 2), abs_neg]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  -- a⁻² * |f(x+a) + f(x-a) - 2f(x)| ≤ a⁻² * a² * ‖f''‖ = ‖f''‖
  calc a⁻¹ ^ 2 * |f (x + a) + f (x - a) - 2 * f x|
      ≤ a⁻¹ ^ 2 * (a ^ 2 * SmoothMap_Circle.sobolevSeminorm 2 f) :=
        mul_le_mul_of_nonneg_left (symmetric_second_diff_bound L f x a) (by positivity)
    _ = SmoothMap_Circle.sobolevSeminorm 2 f := by
        rw [inv_pow, ← mul_assoc, inv_mul_cancel₀ (by positivity : a ^ 2 ≠ 0), one_mul]

/-- Flat bound on the "Laplacian DFT coefficient." -/
theorem laplacianDFT_flat_bound (N : ℕ) [NeZero N]
    (f : SmoothMap_Circle L ℝ) (m : ℕ) :
    |∑ z : ZMod N,
      ((circleSpacing L N)⁻¹ ^ 2 *
        (2 * circleRestriction L N f z -
         circleRestriction L N f (z + 1) -
         circleRestriction L N f (z - 1))) *
      latticeFourierBasisFun N m z| ≤
    Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 2 f := by
  set a := circleSpacing L N with ha_def
  have ha_pos : 0 < a := circleSpacing_pos L N
  have hN_pos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  -- Fourier basis bound (inline since the original is private)
  have hφ_bound : ∀ z : ZMod N, |latticeFourierBasisFun N m z| ≤ Real.sqrt (2 / N) := by
    intro z; cases m with
    | zero =>
      simp only [latticeFourierBasisFun]
      rw [abs_of_nonneg (by positivity)]
      calc 1 / Real.sqrt ↑N
          = Real.sqrt 1 / Real.sqrt ↑N := by rw [Real.sqrt_one]
        _ ≤ Real.sqrt 2 / Real.sqrt ↑N :=
            div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (by norm_num)) (Real.sqrt_nonneg _)
        _ = Real.sqrt (2 / ↑N) := by rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 2)]
    | succ n =>
      simp only [latticeFourierBasisFun]; split
      · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.abs_cos_le_one _)
      · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
        exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (Real.abs_sin_le_one _)
  -- Per-term bound
  have h_term : ∀ z : ZMod N,
      |((circleSpacing L N)⁻¹ ^ 2 *
        (2 * circleRestriction L N f z -
         circleRestriction L N f (z + 1) -
         circleRestriction L N f (z - 1))) *
      latticeFourierBasisFun N m z| ≤
      Real.sqrt a * SmoothMap_Circle.sobolevSeminorm 2 f * Real.sqrt (2 / N) := by
    intro z; rw [abs_mul]
    exact mul_le_mul (negLaplacian_restriction_bound L N f z) (hφ_bound z) (abs_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (SmoothMap_Circle.sobolevSeminorm_nonneg 2 f))
  calc |∑ z : ZMod N, _|
      ≤ ∑ z : ZMod N, |((circleSpacing L N)⁻¹ ^ 2 *
          (2 * circleRestriction L N f z -
           circleRestriction L N f (z + 1) -
           circleRestriction L N f (z - 1))) *
          latticeFourierBasisFun N m z| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : ZMod N,
          (Real.sqrt a * SmoothMap_Circle.sobolevSeminorm 2 f * Real.sqrt (2 / N)) :=
        Finset.sum_le_sum (fun z _ => h_term z)
    _ = ↑N * (Real.sqrt a * SmoothMap_Circle.sobolevSeminorm 2 f * Real.sqrt (2 / N)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1; rw [show Finset.univ.card = (N : ℕ) from ZMod.card N]
    _ = ↑N * (Real.sqrt a * Real.sqrt (2 / N)) *
          SmoothMap_Circle.sobolevSeminorm 2 f := by ring
    _ = Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 2 f := by
        congr 1
        rw [ha_def, circleSpacing_eq, ← Real.sqrt_mul (div_nonneg hL.out.le hN_pos.le)]
        rw [show L / ↑N * (2 / ↑N) = 2 * L / ↑N ^ 2 from by field_simp]
        rw [Real.sqrt_div (by linarith [hL.out] : (0 : ℝ) ≤ 2 * L)]
        rw [Real.sqrt_sq hN_pos.le]; field_simp

/-! ## Eigenvalue lower bound (quadratic in frequency) -/

/-- **Eigenvalue lower bound**: `λ_m ≥ (1+m)²/L²` for m ≥ 1 and m < N.

Uses: `λ_m = (4/a²)sin²(πk/N)` with `k = fourierFreq(m)` satisfying `2k ≥ m`,
Jordan's inequality `sin(πk/N) ≥ 2k/N` for `k ≤ N/2`,
and `a = L/N`. Combined: `λ_m ≥ 16k²/L² ≥ 4m²/L² ≥ (1+m)²/L²`. -/
theorem latticeEigenvalue1d_ge_quadratic (N m : ℕ) [NeZero N]
    (hm : 1 ≤ m) (hm_lt : m < N) :
    ((1 + (m : ℝ)) ^ 2) / L ^ 2 ≤
    latticeEigenvalue1d N (circleSpacing L N) m := by
  unfold latticeEigenvalue1d
  push_cast [circleSpacing]
  set M := (N : ℝ)
  set j := (SmoothMap_Circle.fourierFreq m : ℝ)
  have hM_pos : 0 < M := Nat.cast_pos.mpr (NeZero.pos N)
  have hL' : 0 < L := hL.out
  have h_coeff : 4 / (L / M) ^ 2 = 4 * M ^ 2 / L ^ 2 := by field_simp
  rw [h_coeff]
  -- Key facts about fourierFreq
  have hj_pos : 0 < j := by
    show 0 < (SmoothMap_Circle.fourierFreq m : ℝ)
    have : 1 ≤ SmoothMap_Circle.fourierFreq m := by
      cases m with
      | zero => omega
      | succ n => simp only [SmoothMap_Circle.fourierFreq]; omega
    positivity
  have h2j_ge_m : (m : ℝ) ≤ 2 * j := by
    show (m : ℝ) ≤ 2 * (SmoothMap_Circle.fourierFreq m : ℝ)
    have : m ≤ 2 * SmoothMap_Circle.fourierFreq m := by
      cases m with
      | zero => omega
      | succ n => simp only [SmoothMap_Circle.fourierFreq]; omega
    exact_mod_cast this
  have hj_le_half : j ≤ M / 2 := by
    show (SmoothMap_Circle.fourierFreq m : ℝ) ≤ (N : ℝ) / 2
    have h_nat : SmoothMap_Circle.fourierFreq m ≤ N / 2 := by
      cases m with
      | zero => omega
      | succ n => simp only [SmoothMap_Circle.fourierFreq]; omega
    calc (SmoothMap_Circle.fourierFreq m : ℝ)
        ≤ ((N / 2 : ℕ) : ℝ) := by exact_mod_cast h_nat
      _ ≤ (N : ℝ) / 2 := by
          have h := Nat.div_mul_le_self N 2
          have : (↑(N / 2) : ℝ) * 2 ≤ ↑N := by exact_mod_cast h
          push_cast at this ⊢; linarith
  -- Jordan's inequality: sin(πj/M) ≥ 2j/M
  have harg : 0 ≤ π * j / M := by positivity
  have harg_le : π * j / M ≤ π / 2 := by
    rw [div_le_div_iff₀ hM_pos (by norm_num : (0:ℝ) < 2)]
    nlinarith [pi_pos]
  have hjordan : 2 / π * (π * j / M) ≤ sin (π * j / M) :=
    mul_le_sin harg harg_le
  -- sin²(πj/M) ≥ (2j/M)²
  have hsin_sq : (2 * j / M) ^ 2 ≤ sin (π * j / M) ^ 2 := by
    have : 2 / π * (π * j / M) = 2 * j / M := by field_simp
    rw [← this, sq, sq]
    exact mul_self_le_mul_self (by positivity) hjordan
  -- Chain: (1+m)²/L² ≤ 4m²/L² ≤ 16j²/L² ≤ (4M²/L²)·sin²(πj/M)
  have h_4m_ge : (1 + (m : ℝ)) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by
    have hm_real : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    nlinarith
  calc (1 + (m : ℝ)) ^ 2 / L ^ 2
      ≤ 4 * (m : ℝ) ^ 2 / L ^ 2 := by
        apply div_le_div_of_nonneg_right h_4m_ge (sq_nonneg L)
    _ ≤ 16 * j ^ 2 / L ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg L)
        nlinarith
    _ = 4 * M ^ 2 / L ^ 2 * (2 * j / M) ^ 2 := by
        field_simp; ring
    _ ≤ 4 * M ^ 2 / L ^ 2 * sin (π * j / M) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hsin_sq; positivity

/-! ## Main theorem: Quadratic bound on DFT coefficients -/

/-- **Lattice DFT coefficients decay at least quadratically, uniformly in N.**

`∃ C, 0 ≤ C ∧ ∀ N m, |c_m^{N+1}(f)| ≤ C / (1 + m)²`

**Proof outline:**
- m = 0: `|c₀| ≤ √(2L)‖f‖ ≤ C`
- m ≥ 1, m < N+1: eigenvector transfer gives `λ_m · c_m = ⟨(-Δ)fN, φ_m⟩`,
  so `|c_m| ≤ √(2L)‖f''‖ / λ_m ≤ √(2L)‖f''‖L² / (1+m)²`
- m ≥ N+1: `c_m = 0` -/
theorem latticeDFTCoeff1d_quadratic_bound' (f : SmoothMap_Circle L ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N m,
      |latticeDFTCoeff1d L (N + 1) f m| ≤ C / (1 + (m : ℝ)) ^ 2 := by
  set C₀ := Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 0 f
  set C₂ := Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 2 f
  set Cd := C₂ * L ^ 2
  have hC₀_nn : 0 ≤ C₀ := mul_nonneg (Real.sqrt_nonneg _)
    (SmoothMap_Circle.sobolevSeminorm_nonneg 0 f)
  have hC₂_nn : 0 ≤ C₂ := mul_nonneg (Real.sqrt_nonneg _)
    (SmoothMap_Circle.sobolevSeminorm_nonneg 2 f)
  refine ⟨max C₀ Cd, le_max_of_le_left hC₀_nn, ?_⟩
  intro N m
  by_cases hm_lt : m < N + 1
  · by_cases hm0 : m = 0
    · -- m = 0: flat bound ≤ C₀ ≤ max C₀ Cd
      subst hm0; simp only [Nat.cast_zero, add_zero, one_pow, div_one]
      exact (latticeDFTCoeff1d_flat_bound L f N 0).trans (le_max_left _ _)
    · -- m ≥ 1: eigenvector transfer + eigenvalue lower bound
      have hm_pos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      haveI hN1 : NeZero (N + 1) := ⟨by omega⟩
      have h_transfer := eigenvector_transfer L (N + 1) f m hm_lt
      have h_lap := laplacianDFT_flat_bound L (N + 1) f m
      have h_eig := latticeEigenvalue1d_ge_quadratic L (N + 1) m hm_pos hm_lt
      have h_eig_pos : 0 < latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m :=
        lt_of_lt_of_le (by have := hL.out; positivity) h_eig
      -- |λ_m · c_m| = |laplacian coeff| ≤ C₂
      rw [← h_transfer] at h_lap
      -- |c_m| ≤ C₂ / λ_m
      have h_abs : |latticeDFTCoeff1d L (N + 1) f m| ≤
          C₂ / latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m := by
        rw [abs_mul, abs_of_pos h_eig_pos] at h_lap
        exact (le_div_iff₀ h_eig_pos).mpr (by linarith)
      -- C₂/λ_m ≤ Cd/(1+m)²
      have hL_pos := hL.out
      have h_denom_pos : (0 : ℝ) < (1 + ↑m) ^ 2 / L ^ 2 := by positivity
      calc |latticeDFTCoeff1d L (N + 1) f m|
          ≤ C₂ / latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m := h_abs
        _ ≤ C₂ / ((1 + ↑m) ^ 2 / L ^ 2) :=
            div_le_div_of_nonneg_left hC₂_nn h_denom_pos h_eig
        _ = Cd / (1 + ↑m) ^ 2 := by simp only [Cd]; field_simp
        _ ≤ max C₀ Cd / (1 + ↑m) ^ 2 :=
            div_le_div_of_nonneg_right (le_max_right _ _) (by positivity)
  · -- m ≥ N + 1: coefficient is 0
    rw [latticeDFTCoeff1d_zero_of_ge L (N + 1) f m (by omega), abs_zero]
    exact div_nonneg (le_trans hC₀_nn (le_max_left _ _)) (by positivity)

/-! ## Discrete trig sums

The key orthogonality ingredient: sums of cos and sin over ZMod N vanish
when the frequency is not a multiple of N. The proof uses shift-invariance
(bijection z ↦ z+1) to get a homogeneous 2×2 system with nonzero determinant. -/

/-- Sum of cos over ZMod N vanishes when cos(2πk/N) ≠ 1 (i.e., N ∤ k). -/
theorem sum_cos_zmod_eq_zero (N : ℕ) [NeZero N] (k : ℕ)
    (hk : cos (2 * π * k / N) ≠ 1) :
    ∑ z : ZMod N, cos (2 * π * k * (z.val : ℝ) / N) = 0 := by
  set δ := 2 * π * (k : ℝ) / (N : ℝ) with hδ_def
  set S_c := ∑ z : ZMod N, cos (2 * π * k * (z.val : ℝ) / N)
  set S_s := ∑ z : ZMod N, sin (2 * π * k * (z.val : ℝ) / N)
  -- Shift invariance: Σ_z f(z) = Σ_z f(z+1)
  have h_shift_c : S_c = cos δ * S_c - sin δ * S_s := by
    simp only [S_c, S_s]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply (Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _ _).symm
    intro z
    show cos δ * cos (2 * π * ↑k * (z.val : ℝ) / ↑N) -
        sin δ * sin (2 * π * ↑k * (z.val : ℝ) / ↑N) =
      cos (2 * π * ↑k * ((z + 1 : ZMod N).val : ℝ) / ↑N)
    rw [cos_zmod_succ N k,
      show 2 * π * ↑k * ((z.val : ℝ) + 1) / ↑N =
        2 * π * ↑k * (z.val : ℝ) / ↑N + δ from by simp only [δ]; ring,
      cos_add]; ring
  have h_shift_s : S_s = sin δ * S_c + cos δ * S_s := by
    simp only [S_c, S_s]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply (Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _ _).symm
    intro z
    show sin δ * cos (2 * π * ↑k * (z.val : ℝ) / ↑N) +
        cos δ * sin (2 * π * ↑k * (z.val : ℝ) / ↑N) =
      sin (2 * π * ↑k * ((z + 1 : ZMod N).val : ℝ) / ↑N)
    rw [sin_zmod_succ N k,
      show 2 * π * ↑k * ((z.val : ℝ) + 1) / ↑N =
        2 * π * ↑k * (z.val : ℝ) / ↑N + δ from by simp only [δ]; ring,
      sin_add]; ring
  -- From shifts: (1 - cos δ) S_c = -sin δ S_s  ... (*)
  --              (1 - cos δ) S_s = sin δ S_c    ... (**)
  have eq1 : (1 - cos δ) * S_c = -(sin δ * S_s) := by linarith [h_shift_c]
  -- Multiply (*) by (1 - cos δ): (1-cosδ)² S_c = -sinδ (1-cosδ) S_s
  -- Substitute (**): = -sinδ · sinδ · S_c = -sin²δ · S_c
  -- So [(1-cosδ)² + sin²δ] S_c = 0
  have eq2 : (1 - cos δ) * S_s = sin δ * S_c := by linarith [h_shift_s]
  have hdet : (1 - cos δ) ^ 2 * S_c + sin δ ^ 2 * S_c = 0 := by
    have h1 : (1 - cos δ) ^ 2 * S_c = (1 - cos δ) * ((1 - cos δ) * S_c) := by ring
    rw [h1, eq1]
    have h2 : sin δ ^ 2 * S_c = sin δ * (sin δ * S_c) := by ring
    rw [h2, ← eq2]; ring
  -- (1-cosδ)² + sin²δ = 2(1-cosδ)
  have hsimp : ((1 - cos δ) ^ 2 + sin δ ^ 2) * S_c = 0 := by linarith [hdet]
  have h2 : (1 - cos δ) ^ 2 + sin δ ^ 2 = 2 * (1 - cos δ) := by
    have := sin_sq_add_cos_sq δ; nlinarith
  rw [h2] at hsimp
  have hne : 1 - cos δ ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
  exact (mul_eq_zero.mp hsimp).resolve_left (mul_ne_zero two_ne_zero hne)

/-- Sum of sin over ZMod N vanishes for any integer frequency. -/
theorem sum_sin_zmod_eq_zero (N : ℕ) [NeZero N] (k : ℕ) :
    ∑ z : ZMod N, sin (2 * π * k * (z.val : ℝ) / N) = 0 := by
  by_cases hk : cos (2 * π * k / N) = 1
  · -- cos δ = 1 means δ ∈ 2πℤ, so sin δ = 0 and each sin(δ·z) = sin(2πnz) = 0
    -- More precisely: cos(δ) = 1 and sin²(δ) = 1 - cos²(δ) = 0
    have hsin_δ : sin (2 * π * k / N) = 0 := by nlinarith [sin_sq_add_cos_sq (2 * π * k / N)]
    -- Each term: sin(2πk·z.val/N) = sin(z.val · δ)
    -- Since cos δ = 1 and sin δ = 0, by induction sin(nδ) = 0 for all n
    -- Use: sin(nδ) = sin((n-1)δ + δ) = sin((n-1)δ)cosδ + cos((n-1)δ)sinδ
    --            = sin((n-1)δ) · 1 + cos((n-1)δ) · 0 = sin((n-1)δ)
    -- So sin(nδ) = sin(0) = 0 by induction
    have hzero : ∀ z : ZMod N,
        sin (2 * π * k * (z.val : ℝ) / N) = 0 := by
      intro z
      have : 2 * π * (k : ℝ) * (z.val : ℝ) / (N : ℝ) =
          (z.val : ℝ) * (2 * π * k / N) := by ring
      rw [this]
      induction z.val with
      | zero => simp
      | succ n ih =>
        rw [show ((n + 1 : ℕ) : ℝ) * (2 * π * ↑k / ↑N) =
            (n : ℝ) * (2 * π * ↑k / ↑N) + 2 * π * ↑k / ↑N from by push_cast; ring]
        rw [sin_add, hk, hsin_δ]; simp [ih]
    simp_rw [hzero, Finset.sum_const_zero]
  · -- cos δ ≠ 1: use the same 2×2 system as sum_cos_zmod_eq_zero
    set δ := 2 * π * (k : ℝ) / (N : ℝ) with hδ_def
    set S_c := ∑ z : ZMod N, cos (2 * π * k * (z.val : ℝ) / N)
    have hSc : S_c = 0 := sum_cos_zmod_eq_zero N k hk
    set S_s := ∑ z : ZMod N, sin (2 * π * k * (z.val : ℝ) / N)
    -- From the shift identity: (1-cosδ) S_s = sinδ · S_c = 0
    have h_shift_s : S_s = sin δ * S_c + cos δ * S_s := by
      simp only [S_c, S_s]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply (Fintype.sum_equiv (Equiv.addRight (1 : ZMod N)) _ _ _).symm
      intro z
      show sin δ * cos (2 * π * ↑k * (z.val : ℝ) / ↑N) +
          cos δ * sin (2 * π * ↑k * (z.val : ℝ) / ↑N) =
        sin (2 * π * ↑k * ((z + 1 : ZMod N).val : ℝ) / ↑N)
      rw [sin_zmod_succ N k,
        show 2 * π * ↑k * ((z.val : ℝ) + 1) / ↑N =
          2 * π * ↑k * (z.val : ℝ) / ↑N + δ from by simp only [δ]; ring,
        sin_add]; ring
    have eq2 : (1 - cos δ) * S_s = sin δ * S_c := by linarith [h_shift_s]
    rw [hSc, mul_zero] at eq2
    have hne : 1 - cos δ ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
    exact (mul_eq_zero.mp eq2).resolve_left hne

/-- Sum of cos over ZMod N when N divides k: equals N. -/
theorem sum_cos_zmod_eq_N (N : ℕ) [NeZero N] (k : ℕ) (hk : (N : ℤ) ∣ (k : ℤ)) :
    ∑ z : ZMod N, cos (2 * π * k * (z.val : ℝ) / N) = N := by
  obtain ⟨q, hq⟩ := hk
  have hN_ne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have : ∀ z : ZMod N,
      cos (2 * π * k * (z.val : ℝ) / N) = 1 := by
    intro z
    have hkR : (k : ℝ) = (N : ℝ) * (q : ℝ) := by exact_mod_cast hq
    rw [hkR, show 2 * π * ((N : ℝ) * (q : ℝ)) * (z.val : ℝ) / (N : ℝ) =
        ↑((z.val : ℤ) * q) * (2 * π) from by push_cast; field_simp]
    exact cos_int_mul_two_pi _
  simp_rw [this, Finset.sum_const, Finset.card_univ, ZMod.card N, nsmul_eq_mul, mul_one]

/-! ## Lattice Fourier basis norm squared -/

/-- The squared norm (sum of squares) of the m-th lattice Fourier basis function. -/
def latticeFourierNormSq (N m : ℕ) [NeZero N] : ℝ :=
  ∑ z : ZMod N, latticeFourierBasisFun N m z ^ 2

/-- The constant mode has norm squared 1. -/
theorem latticeFourierNormSq_zero (N : ℕ) [NeZero N] :
    latticeFourierNormSq N 0 = 1 := by
  simp only [latticeFourierNormSq, latticeFourierBasisFun]
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  simp_rw [div_pow, one_pow, sq_sqrt (Nat.cast_nonneg' N)]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card N, nsmul_eq_mul]
  field_simp

/-- For non-Nyquist modes m ≥ 1 with 2·fourierFreq(m) ≠ N, the norm squared is 1. -/
theorem latticeFourierNormSq_eq_one (N : ℕ) [NeZero N] (m : ℕ) (hm : 0 < m) (hm_lt : m < N)
    (hNotNyquist : 2 * SmoothMap_Circle.fourierFreq m ≠ N) :
    latticeFourierNormSq N m = 1 := by
  cases m with
  | zero => omega
  | succ n =>
    simp only [latticeFourierNormSq, latticeFourierBasisFun]
    set k := n / 2 + 1 with hk_def
    have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
    have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
    split
    · -- cosine mode: normSq = (2/N) Σ cos²(2πkz/N) = (2/N)(N/2) = 1
      simp_rw [mul_pow, sq_sqrt (by positivity : (0:ℝ) ≤ 2 / N)]
      -- Reduce cos² to double-angle form and pull constant out of sum
      simp_rw [show ∀ z : ZMod N, 2 / ↑N * cos (2 * π * ↑k * (↑z.val : ℝ) / ↑N) ^ 2 =
          (1 / ↑N) * (1 + cos (2 * (2 * π * ↑k * (↑z.val : ℝ) / ↑N))) from fun z => by
        rw [cos_sq]; ring]
      rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, ZMod.card N, nsmul_eq_mul]
      -- Σ cos(4πkz/N) = 0 since N ∤ 2k
      simp_rw [show ∀ z : ZMod N,
          cos (2 * (2 * π * ↑k * (↑z.val : ℝ) / ↑N)) =
          cos (2 * π * ↑(2 * k) * (↑z.val : ℝ) / ↑N) from fun z => by
        congr 1; push_cast; ring]
      have hcos_sum : ∑ z : ZMod N,
          cos (2 * π * ↑(2 * k) * (↑z.val : ℝ) / ↑N) = 0 := by
        apply sum_cos_zmod_eq_zero
        intro heq
        apply hNotNyquist
        -- From heq: cos(2π(2k)/N) = 1 with 0 < 2k ≤ N forces 2k = N
        have hk_pos : 0 < k := by omega
        have h2k_le_N : 2 * k ≤ N := by omega
        rcases Nat.eq_or_lt_of_le h2k_le_N with h2k_eq | h2k_lt
        · -- 2k = N: directly gives fourierFreq(n+1) = k = N/2
          simp only [SmoothMap_Circle.fourierFreq]; omega
        · -- 2k < N: cos = 1 is impossible since 0 < 2π(2k)/N < 2π
          exfalso
          have hx_pos : (0 : ℝ) < 2 * π * ↑(2 * k) / ↑N := by positivity
          have hx_lt : 2 * π * ↑(2 * k) / ↑N < 2 * π := by
            rw [div_lt_iff₀ hN_pos]
            nlinarith [show (↑(2 * k) : ℝ) < ↑N from Nat.cast_lt.mpr h2k_lt, pi_pos]
          have := (cos_eq_one_iff_of_lt_of_lt (by linarith) hx_lt).mp heq
          linarith
      rw [hcos_sum]; simp
    · -- sine mode: normSq = (2/N) Σ sin²(2πkz/N) = (2/N)(N/2) = 1
      simp_rw [mul_pow, sq_sqrt (by positivity : (0:ℝ) ≤ 2 / N)]
      simp_rw [show ∀ z : ZMod N, 2 / ↑N * sin (2 * π * ↑k * (↑z.val : ℝ) / ↑N) ^ 2 =
          (1 / ↑N) * (1 - cos (2 * (2 * π * ↑k * (↑z.val : ℝ) / ↑N))) from fun z => by
        rw [sin_sq, cos_sq]; ring]
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, ZMod.card N, nsmul_eq_mul]
      simp_rw [show ∀ z : ZMod N,
          cos (2 * (2 * π * ↑k * (↑z.val : ℝ) / ↑N)) =
          cos (2 * π * ↑(2 * k) * (↑z.val : ℝ) / ↑N) from fun z => by
        congr 1; push_cast; ring]
      have hcos_sum : ∑ z : ZMod N,
          cos (2 * π * ↑(2 * k) * (↑z.val : ℝ) / ↑N) = 0 := by
        apply sum_cos_zmod_eq_zero
        intro heq
        apply hNotNyquist
        have hk_pos : 0 < k := by omega
        have h2k_le_N : 2 * k ≤ N := by omega
        rcases Nat.eq_or_lt_of_le h2k_le_N with h2k_eq | h2k_lt
        · simp only [SmoothMap_Circle.fourierFreq]; omega
        · exfalso
          have hx_pos : (0 : ℝ) < 2 * π * ↑(2 * k) / ↑N := by positivity
          have hx_lt : 2 * π * ↑(2 * k) / ↑N < 2 * π := by
            rw [div_lt_iff₀ hN_pos]
            nlinarith [show (↑(2 * k) : ℝ) < ↑N from Nat.cast_lt.mpr h2k_lt, pi_pos]
          have := (cos_eq_one_iff_of_lt_of_lt (by linarith) hx_lt).mp heq
          linarith
      rw [hcos_sum]; simp

/-! ## Lattice Fourier basis orthogonality -/

/-- Product-to-sum: cos a * cos b = (cos(a-b) + cos(a+b))/2. -/
private theorem cos_mul_cos (a b : ℝ) :
    cos a * cos b = (cos (a - b) + cos (a + b)) / 2 := by
  linarith [cos_add a b, cos_sub a b]

/-- Product-to-sum: sin a * sin b = (cos(a-b) - cos(a+b))/2. -/
private theorem sin_mul_sin (a b : ℝ) :
    sin a * sin b = (cos (a - b) - cos (a + b)) / 2 := by
  linarith [cos_add a b, cos_sub a b]

/-- Product-to-sum: cos a * sin b = (sin(a+b) - sin(a-b))/2. -/
private theorem cos_mul_sin (a b : ℝ) :
    cos a * sin b = (sin (a + b) - sin (a - b)) / 2 := by
  linarith [sin_add a b, sin_sub a b]

/-- For 0 < m < N, cos(2πm/N) ≠ 1 (since 0 < 2πm/N < 2π). -/
theorem cos_ne_one_of_pos_lt (N : ℕ) [NeZero N] (m : ℕ)
    (hm_pos : 0 < m) (hm_lt : m < N) :
    cos (2 * π * ↑m / ↑N) ≠ 1 := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hx_pos : (0 : ℝ) < 2 * π * ↑m / ↑N := by positivity
  have hx_lt : 2 * π * ↑m / ↑N < 2 * π := by
    rw [div_lt_iff₀ hN_pos]
    nlinarith [show (↑m : ℝ) < ↑N from Nat.cast_lt.mpr hm_lt, pi_pos]
  intro heq
  exact absurd ((cos_eq_one_iff_of_lt_of_lt (by linarith) hx_lt).mp heq) (by linarith)

/-- Corollary: sum of cos vanishes for frequencies in (0, N). -/
theorem sum_cos_zmod_eq_zero_of_pos_lt (N : ℕ) [NeZero N] (m : ℕ)
    (hm_pos : 0 < m) (hm_lt : m < N) :
    ∑ z : ZMod N, cos (2 * π * ↑m * (z.val : ℝ) / ↑N) = 0 :=
  sum_cos_zmod_eq_zero N m (cos_ne_one_of_pos_lt N m hm_pos hm_lt)

/-- Sum of sin over ZMod N vanishes for any integer frequency. -/
theorem sum_sin_zmod_int_eq_zero (N : ℕ) [NeZero N] (m : ℤ) :
    ∑ z : ZMod N, sin (2 * π * ↑m * (z.val : ℝ) / ↑N) = 0 := by
  rcases le_or_gt 0 m with hm | hm
  · lift m to ℕ using hm
    exact_mod_cast sum_sin_zmod_eq_zero N m
  · -- m < 0: use sin(-x) = -sin(x) and reduce to (-m).toNat : ℕ
    set n := (-m).toNat
    have hmn : m = -(n : ℤ) := by simp [n, Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ -m)]
    simp_rw [show (m : ℝ) = -(n : ℝ) from by exact_mod_cast hmn,
      show ∀ z : ZMod N, 2 * π * (-(n : ℝ)) * (z.val : ℝ) / ↑N =
        -(2 * π * ↑n * (z.val : ℝ) / ↑N) from fun z => by ring,
      sin_neg, Finset.sum_neg_distrib, neg_eq_zero]
    exact sum_sin_zmod_eq_zero N n

/-- Product of cos and sin over ZMod N sums to zero (any frequencies). -/
theorem sum_cos_mul_sin_zmod_eq_zero (N : ℕ) [NeZero N] (k l : ℕ) :
    ∑ z : ZMod N, cos (2 * π * ↑k * (z.val : ℝ) / ↑N) *
      sin (2 * π * ↑l * (z.val : ℝ) / ↑N) = 0 := by
  simp_rw [cos_mul_sin]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp_rw [show ∀ z : ZMod N,
      2 * π * ↑k * (z.val : ℝ) / ↑N + 2 * π * ↑l * (z.val : ℝ) / ↑N =
      2 * π * ↑((k : ℤ) + ↑l) * (z.val : ℝ) / ↑N from fun z => by push_cast; ring]
  simp_rw [show ∀ z : ZMod N,
      2 * π * ↑k * (z.val : ℝ) / ↑N - 2 * π * ↑l * (z.val : ℝ) / ↑N =
      2 * π * ↑((k : ℤ) - ↑l) * (z.val : ℝ) / ↑N from fun z => by push_cast; ring]
  rw [sum_sin_zmod_int_eq_zero N ((k : ℤ) + l),
    sum_sin_zmod_int_eq_zero N ((k : ℤ) - l)]
  simp

/-- Product of cos functions over ZMod N sums to zero when frequencies
    are distinct and both in (0, N/2]. -/
theorem sum_cos_mul_cos_zmod_eq_zero (N : ℕ) [NeZero N] (k l : ℕ)
    (hk_pos : 0 < k) (hl_pos : 0 < l) (hkl : k ≠ l) (hkl_sum : k + l < N) :
    ∑ z : ZMod N, cos (2 * π * ↑k * (z.val : ℝ) / ↑N) *
      cos (2 * π * ↑l * (z.val : ℝ) / ↑N) = 0 := by
  simp_rw [cos_mul_cos]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  -- Sum frequency: k + l, with 0 < k+l < N
  simp_rw [show ∀ z : ZMod N,
      2 * π * ↑k * (z.val : ℝ) / ↑N + 2 * π * ↑l * (z.val : ℝ) / ↑N =
      2 * π * ↑(k + l) * (z.val : ℝ) / ↑N from fun z => by push_cast; ring]
  -- Difference frequency: |k - l|, with 0 < |k-l| < N
  rcases le_or_gt l k with hlk | hkl'
  · -- k ≥ l: difference = k - l
    simp_rw [show ∀ z : ZMod N,
        2 * π * ↑k * (z.val : ℝ) / ↑N - 2 * π * ↑l * (z.val : ℝ) / ↑N =
        2 * π * ↑(k - l) * (z.val : ℝ) / ↑N from fun z => by
          rw [Nat.cast_sub hlk]; ring]
    rw [sum_cos_zmod_eq_zero_of_pos_lt N (k - l) (Nat.sub_pos_of_lt
      (lt_of_le_of_ne hlk (Ne.symm hkl))) (by omega),
      sum_cos_zmod_eq_zero_of_pos_lt N (k + l) (by omega) hkl_sum]
    simp
  · -- k < l: difference is negative, use cos(-x) = cos(x)
    simp_rw [show ∀ z : ZMod N,
        2 * π * ↑k * (z.val : ℝ) / ↑N - 2 * π * ↑l * (z.val : ℝ) / ↑N =
        -(2 * π * ↑(l - k) * (z.val : ℝ) / ↑N) from fun z => by
          rw [Nat.cast_sub hkl'.le]; ring,
      cos_neg]
    rw [sum_cos_zmod_eq_zero_of_pos_lt N (l - k) (by omega) (by omega),
      sum_cos_zmod_eq_zero_of_pos_lt N (k + l) (by omega) hkl_sum]
    simp

/-- Product of sin functions over ZMod N sums to zero when frequencies
    are distinct and both in (0, N/2]. -/
theorem sum_sin_mul_sin_zmod_eq_zero (N : ℕ) [NeZero N] (k l : ℕ)
    (hk_pos : 0 < k) (hl_pos : 0 < l) (hkl : k ≠ l) (hkl_sum : k + l < N) :
    ∑ z : ZMod N, sin (2 * π * ↑k * (z.val : ℝ) / ↑N) *
      sin (2 * π * ↑l * (z.val : ℝ) / ↑N) = 0 := by
  simp_rw [sin_mul_sin]
  rw [← Finset.sum_div, Finset.sum_sub_distrib]
  simp_rw [show ∀ z : ZMod N,
      2 * π * ↑k * (z.val : ℝ) / ↑N + 2 * π * ↑l * (z.val : ℝ) / ↑N =
      2 * π * ↑(k + l) * (z.val : ℝ) / ↑N from fun z => by push_cast; ring]
  rcases le_or_gt l k with hlk | hkl'
  · simp_rw [show ∀ z : ZMod N,
        2 * π * ↑k * (z.val : ℝ) / ↑N - 2 * π * ↑l * (z.val : ℝ) / ↑N =
        2 * π * ↑(k - l) * (z.val : ℝ) / ↑N from fun z => by
          rw [Nat.cast_sub hlk]; ring]
    rw [sum_cos_zmod_eq_zero_of_pos_lt N (k - l) (Nat.sub_pos_of_lt
      (lt_of_le_of_ne hlk (Ne.symm hkl))) (by omega),
      sum_cos_zmod_eq_zero_of_pos_lt N (k + l) (by omega) hkl_sum]
    simp
  · simp_rw [show ∀ z : ZMod N,
        2 * π * ↑k * (z.val : ℝ) / ↑N - 2 * π * ↑l * (z.val : ℝ) / ↑N =
        -(2 * π * ↑(l - k) * (z.val : ℝ) / ↑N) from fun z => by
          rw [Nat.cast_sub hkl'.le]; ring,
      cos_neg]
    rw [sum_cos_zmod_eq_zero_of_pos_lt N (l - k) (by omega) (by omega),
      sum_cos_zmod_eq_zero_of_pos_lt N (k + l) (by omega) hkl_sum]
    simp

/-! ## Eigenvector property of 1D lattice Laplacian

The key structural result: cos(2πkz/N) and sin(2πkz/N) are eigenvectors
of the negative 1D lattice Laplacian `(-Δ)` with eigenvalue `(4/a²)sin²(πk/N)`.

This uses: cos(θ+δ) + cos(θ-δ) = 2cos(θ)cos(δ), so
(-Δ cos_k)(z) = a⁻²(2cos(θ) - cos(θ+δ) - cos(θ-δ))
             = 2a⁻²(1 - cos(δ))cos(θ) = (4/a²)sin²(πk/N)·cos(θ). -/

/-- Sum of cos at shifted argument: cos(k·(z+1)) + cos(k·(z-1)) = 2cos(kz)cos(k). -/
private theorem cos_shift_sum (N : ℕ) [NeZero N] (k : ℕ) (z : ZMod N) :
    cos (2 * π * ↑k * ((z + 1 : ZMod N).val : ℝ) / ↑N) +
    cos (2 * π * ↑k * ((z - 1 : ZMod N).val : ℝ) / ↑N) =
    2 * cos (2 * π * ↑k * (z.val : ℝ) / ↑N) *
      cos (2 * π * ↑k / ↑N) := by
  rw [cos_zmod_succ, cos_zmod_pred]
  set θ := 2 * π * ↑k * (z.val : ℝ) / ↑N
  set δ := 2 * π * ↑k / ↑N
  rw [show 2 * π * ↑k * ((z.val : ℝ) + 1) / ↑N = θ + δ from by simp only [θ, δ]; ring,
    show 2 * π * ↑k * ((z.val : ℝ) - 1) / ↑N = θ - δ from by simp only [θ, δ]; ring]
  linarith [cos_add θ δ, cos_sub θ δ]

/-- The negative 1D Laplacian acts on cos functions as eigenvalue multiplication.

For `v(x) = cos(2πk·(x 0).val/N)`, we have `(-Δ) v = λ_k · v`
where `λ_k = (2/a²)(1 - cos(2πk/N))`. -/
theorem negLaplacian1d_cos_eigenvalue (N : ℕ) [NeZero N] (a : ℝ) (ha : a ≠ 0) (k : ℕ) :
    let v : FinLatticeField 1 N :=
      fun x => cos (2 * π * ↑k * ((x 0).val : ℝ) / ↑N)
    ∀ x : FinLatticeSites 1 N,
      (negLaplacianMatrix 1 N a).mulVec v x =
      (2 * a⁻¹ ^ 2 * (1 - cos (2 * π * ↑k / ↑N))) * v x := by
  intro v x
  -- Bridge mulVec to operator action
  rw [show (negLaplacianMatrix 1 N a).mulVec v x =
      (massOperator 1 N a 0 v) x from by
    simp only [negLaplacianMatrix]
    rw [← massOperator_eq_matrix_mulVec]]
  -- Expand massOperator = -finiteLaplacian + 0²·id
  simp only [massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul]
  -- Unfold finiteLaplacian
  simp only [finiteLaplacian, ContinuousLinearMap.coe_mk',
    finiteLaplacianLM, LinearMap.coe_mk, AddHom.coe_mk,
    finiteLaplacianFun]
  -- For d=1, the sum over Fin 1 is a single term
  simp only [Fin.sum_univ_one]
  -- The shifted function arguments simplify via coordinate 0
  have hv_succ : v (fun j : Fin 1 => if j = 0 then x j + 1 else x j) =
      cos (2 * π * ↑k * ((x 0 + 1 : ZMod N).val : ℝ) / ↑N) := by
    show cos (2 * π * ↑k * (((fun j : Fin 1 => if j = 0 then x j + 1 else x j) 0).val : ℝ) / ↑N) = _
    simp
  have hv_pred : v (fun j : Fin 1 => if j = 0 then x j - 1 else x j) =
      cos (2 * π * ↑k * ((x 0 - 1 : ZMod N).val : ℝ) / ↑N) := by
    show cos (2 * π * ↑k * (((fun j : Fin 1 => if j = 0 then x j - 1 else x j) 0).val : ℝ) / ↑N) = _
    simp
  rw [hv_succ, hv_pred, cos_shift_sum]
  ring

/-- Sum of sin at shifted arguments: sin(k·(z+1)) + sin(k·(z-1)) = 2sin(kz)cos(k). -/
private theorem sin_shift_sum (N : ℕ) [NeZero N] (k : ℕ) (z : ZMod N) :
    sin (2 * π * ↑k * ((z + 1 : ZMod N).val : ℝ) / ↑N) +
    sin (2 * π * ↑k * ((z - 1 : ZMod N).val : ℝ) / ↑N) =
    2 * sin (2 * π * ↑k * (z.val : ℝ) / ↑N) *
      cos (2 * π * ↑k / ↑N) := by
  rw [sin_zmod_succ, sin_zmod_pred]
  set θ := 2 * π * ↑k * (z.val : ℝ) / ↑N
  set δ := 2 * π * ↑k / ↑N
  rw [show 2 * π * ↑k * ((z.val : ℝ) + 1) / ↑N = θ + δ from by simp only [θ, δ]; ring,
    show 2 * π * ↑k * ((z.val : ℝ) - 1) / ↑N = θ - δ from by simp only [θ, δ]; ring]
  linarith [sin_add θ δ, sin_sub θ δ]

/-- The negative 1D Laplacian acts on sin functions as eigenvalue multiplication. -/
theorem negLaplacian1d_sin_eigenvalue (N : ℕ) [NeZero N] (a : ℝ) (ha : a ≠ 0) (k : ℕ) :
    let v : FinLatticeField 1 N :=
      fun x => sin (2 * π * ↑k * ((x 0).val : ℝ) / ↑N)
    ∀ x : FinLatticeSites 1 N,
      (negLaplacianMatrix 1 N a).mulVec v x =
      (2 * a⁻¹ ^ 2 * (1 - cos (2 * π * ↑k / ↑N))) * v x := by
  intro v x
  rw [show (negLaplacianMatrix 1 N a).mulVec v x =
      (massOperator 1 N a 0 v) x from by
    simp only [negLaplacianMatrix]
    rw [← massOperator_eq_matrix_mulVec]]
  simp only [massOperator, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [finiteLaplacian, ContinuousLinearMap.coe_mk',
    finiteLaplacianLM, LinearMap.coe_mk, AddHom.coe_mk,
    finiteLaplacianFun]
  simp only [Fin.sum_univ_one]
  have hv_succ : v (fun j : Fin 1 => if j = 0 then x j + 1 else x j) =
      sin (2 * π * ↑k * ((x 0 + 1 : ZMod N).val : ℝ) / ↑N) := by
    show sin (2 * π * ↑k * (((fun j : Fin 1 => if j = 0 then x j + 1 else x j) 0).val : ℝ) / ↑N) = _
    simp
  have hv_pred : v (fun j : Fin 1 => if j = 0 then x j - 1 else x j) =
      sin (2 * π * ↑k * ((x 0 - 1 : ZMod N).val : ℝ) / ↑N) := by
    show sin (2 * π * ↑k * (((fun j : Fin 1 => if j = 0 then x j - 1 else x j) 0).val : ℝ) / ↑N) = _
    simp
  rw [hv_succ, hv_pred, sin_shift_sum]
  ring

/-! ## Full pairwise orthogonality of the DFT basis

The lattice Fourier basis functions `latticeFourierBasisFun N m` for `m < N`
are pairwise orthogonal over `ZMod N`. This uses the product-to-sum
identities and the trig sum vanishing theorems. -/

/-- **Pairwise orthogonality of the lattice Fourier basis.**

For distinct modes `m ≠ n` with `m, n < N`:
  `∑ z, φ_m(z) · φ_n(z) = 0` -/
theorem latticeFourierBasisFun_orthogonal (N : ℕ) [NeZero N] (m n : ℕ)
    (hm : m < N) (hn : n < N) (hmn : m ≠ n) :
    ∑ z : ZMod N, latticeFourierBasisFun N m z * latticeFourierBasisFun N n z = 0 := by
  cases m with
  | zero =>
    cases n with
    | zero => exact absurd rfl hmn
    | succ n =>
      simp only [latticeFourierBasisFun]
      set k := n / 2 + 1
      have hk_pos : 0 < k := by omega
      have hk_lt : k < N := by omega
      split
      · -- 0 vs cos(k)
        simp_rw [show ∀ z : ZMod N,
            (1 / Real.sqrt ↑N) * (Real.sqrt (2 / ↑N) * cos (2 * π * ↑k * ↑z.val / ↑N)) =
            (Real.sqrt (2 / ↑N) / Real.sqrt ↑N) * cos (2 * π * ↑k * ↑z.val / ↑N) from
          fun z => by ring]
        rw [← Finset.mul_sum, sum_cos_zmod_eq_zero_of_pos_lt N k hk_pos hk_lt, mul_zero]
      · -- 0 vs sin(k)
        simp_rw [show ∀ z : ZMod N,
            (1 / Real.sqrt ↑N) * (Real.sqrt (2 / ↑N) * sin (2 * π * ↑k * ↑z.val / ↑N)) =
            (Real.sqrt (2 / ↑N) / Real.sqrt ↑N) * sin (2 * π * ↑k * ↑z.val / ↑N) from
          fun z => by ring]
        rw [← Finset.mul_sum, sum_sin_zmod_eq_zero N k, mul_zero]
  | succ m =>
    cases n with
    | zero =>
      -- m+1 vs 0: factor out constants, use trig sum vanishing
      simp only [latticeFourierBasisFun]
      set k := m / 2 + 1
      have hk_pos : 0 < k := by omega
      have hk_lt : k < N := by omega
      split
      · -- cos(k) vs constant
        simp_rw [show ∀ z : ZMod N,
            (Real.sqrt (2 / ↑N) * cos (2 * π * ↑k * ↑z.val / ↑N)) * (1 / Real.sqrt ↑N) =
            (Real.sqrt (2 / ↑N) / Real.sqrt ↑N) * cos (2 * π * ↑k * ↑z.val / ↑N) from
          fun z => by ring]
        rw [← Finset.mul_sum, sum_cos_zmod_eq_zero_of_pos_lt N k hk_pos hk_lt, mul_zero]
      · -- sin(k) vs constant
        simp_rw [show ∀ z : ZMod N,
            (Real.sqrt (2 / ↑N) * sin (2 * π * ↑k * ↑z.val / ↑N)) * (1 / Real.sqrt ↑N) =
            (Real.sqrt (2 / ↑N) / Real.sqrt ↑N) * sin (2 * π * ↑k * ↑z.val / ↑N) from
          fun z => by ring]
        rw [← Finset.mul_sum, sum_sin_zmod_eq_zero N k, mul_zero]
    | succ n =>
      -- Both ≥ 1: case split on mode types
      simp only [latticeFourierBasisFun]
      set km := m / 2 + 1 with hkm_def
      set kn := n / 2 + 1 with hkn_def
      have hkm_pos : 0 < km := by omega
      have hkn_pos : 0 < kn := by omega
      have hkm_lt : km ≤ N / 2 := by omega
      have hkn_lt : kn ≤ N / 2 := by omega
      -- Factor √(2/N) · a · (√(2/N) · b) = (2/N) · (a · b)
      have hsq : ∀ (a b : ℝ),
          Real.sqrt (2 / ↑N) * a * (Real.sqrt (2 / ↑N) * b) = (2 / ↑N) * (a * b) := by
        intro a b
        rw [mul_mul_mul_comm, Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2 / ↑N)]
      split <;> split
      · -- cos(km) vs cos(kn)
        have hkm_ne_kn : km ≠ kn := by intro h; apply hmn; omega
        have hkm_kn_lt : km + kn < N := by omega
        simp_rw [hsq]
        rw [← Finset.mul_sum,
          sum_cos_mul_cos_zmod_eq_zero N km kn hkm_pos hkn_pos hkm_ne_kn hkm_kn_lt,
          mul_zero]
      · -- cos(km) vs sin(kn)
        simp_rw [hsq]
        rw [← Finset.mul_sum,
          sum_cos_mul_sin_zmod_eq_zero N km kn, mul_zero]
      · -- sin(km) vs cos(kn)
        simp_rw [hsq, show ∀ z : ZMod N,
            sin (2 * π * ↑km * ↑z.val / ↑N) * cos (2 * π * ↑kn * ↑z.val / ↑N) =
            cos (2 * π * ↑kn * ↑z.val / ↑N) * sin (2 * π * ↑km * ↑z.val / ↑N) from
          fun z => mul_comm _ _]
        rw [← Finset.mul_sum,
          sum_cos_mul_sin_zmod_eq_zero N kn km, mul_zero]
      · -- sin(km) vs sin(kn)
        have hkm_ne_kn : km ≠ kn := by intro h; apply hmn; omega
        have hkm_kn_lt : km + kn < N := by omega
        simp_rw [hsq]
        rw [← Finset.mul_sum,
          sum_sin_mul_sin_zmod_eq_zero N km kn hkm_pos hkn_pos hkm_ne_kn hkm_kn_lt,
          mul_zero]

/-- The lattice Fourier norm squared is positive for all modes m < N. -/
theorem latticeFourierNormSq_pos (N : ℕ) [NeZero N] (m : ℕ) (hm : m < N) :
    0 < latticeFourierNormSq N m := by
  cases m with
  | zero => rw [latticeFourierNormSq_zero]; exact one_pos
  | succ n =>
    by_cases hNyq : 2 * SmoothMap_Circle.fourierFreq (n + 1) = N
    · -- Nyquist: n must be even (n odd → fourierFreq = (n+1)/2, so N = n+1, contradicting hm)
      have hn_even : n % 2 = 0 := by
        by_contra h; push_neg at h
        simp [SmoothMap_Circle.fourierFreq] at hNyq; omega
      -- φ(0) = √(2/N) * cos(0) = √(2/N) > 0, so φ(0)² > 0
      have h0 : 0 < latticeFourierBasisFun N (n + 1) (0 : ZMod N) ^ 2 := by
        simp only [latticeFourierBasisFun, hn_even, ↓reduceIte]
        simp [ZMod.val_zero, mul_zero, zero_div, cos_zero, mul_one]
        exact pow_pos (div_pos (Real.sqrt_pos_of_pos (by norm_num : (0:ℝ) < 2))
          (Real.sqrt_pos_of_pos (Nat.cast_pos.mpr (NeZero.pos N)))) 2
      exact lt_of_lt_of_le h0
        (Finset.single_le_sum (fun z _ => sq_nonneg _) (Finset.mem_univ (0 : ZMod N)))
    · rw [latticeFourierNormSq_eq_one N (n + 1) (by omega) hm hNyq]; exact one_pos

/-- At the Nyquist mode, the norm squared is 2. -/
private theorem latticeFourierNormSq_nyquist (N : ℕ) [NeZero N] (n : ℕ)
    (hn_lt : n + 1 < N) (hn_even : n % 2 = 0)
    (hNyq : 2 * SmoothMap_Circle.fourierFreq (n + 1) = N) :
    latticeFourierNormSq N (n + 1) = 2 := by
  have hN_pos : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have h2k : (2 : ℝ) * ↑(n / 2 + 1) = ↑N := by exact_mod_cast hNyq
  simp only [latticeFourierNormSq, latticeFourierBasisFun, hn_even, ↓reduceIte]
  simp_rw [mul_pow, sq_sqrt (by positivity : (0:ℝ) ≤ 2 / N)]
  -- cos(2π(n/2+1)·z/N)² = cos(π·z)² = 1 for all z (since 2(n/2+1) = N)
  have hcos_sq_one : ∀ z : ZMod N,
      cos (2 * π * ↑(n / 2 + 1) * ↑z.val / ↑N) ^ 2 = 1 := by
    intro z
    have harg : 2 * π * ↑(n / 2 + 1) * ↑z.val / ↑N = ↑z.val * π := by
      rw [show 2 * π * ↑(n / 2 + 1) * ↑z.val / ↑N =
        ↑z.val * π * (2 * ↑(n / 2 + 1) / ↑N) from by ring,
        h2k, div_self (ne_of_gt hN_pos), mul_one]
    rw [harg]
    nlinarith [Real.sin_nat_mul_pi z.val, Real.sin_sq_add_cos_sq (↑z.val * π)]
  simp_rw [hcos_sq_one, mul_one, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  rw [mul_div_cancel₀ _ (ne_of_gt hN_pos)]

/-- The lattice Fourier norm squared is at least 1 for all modes m < N. -/
theorem latticeFourierNormSq_ge_one (N : ℕ) [NeZero N] (m : ℕ) (hm : m < N) :
    1 ≤ latticeFourierNormSq N m := by
  cases m with
  | zero => rw [latticeFourierNormSq_zero]
  | succ n =>
    by_cases hNyq : 2 * SmoothMap_Circle.fourierFreq (n + 1) = N
    · have hn_even : n % 2 = 0 := by
        by_contra h; push_neg at h
        simp [SmoothMap_Circle.fourierFreq] at hNyq; omega
      rw [latticeFourierNormSq_nyquist N n hm hn_even hNyq]; norm_num
    · rw [latticeFourierNormSq_eq_one N (n + 1) (by omega) hm hNyq]

/-- For fixed m, latticeFourierNormSq (N+1) m = 1 for all sufficiently large N. -/
theorem latticeFourierNormSq_eventually_one (m : ℕ) :
    ∀ᶠ N in Filter.atTop, latticeFourierNormSq (N + 1) m = 1 := by
  cases m with
  | zero =>
    apply Filter.Eventually.of_forall; intro N
    exact latticeFourierNormSq_zero (N + 1)
  | succ n =>
    -- For fixed n+1, the Nyquist condition 2*fourierFreq(n+1) = N+1 holds for at most one N.
    -- For N ≥ max(n, 2*fourierFreq(n+1)), both n+1 < N+1 and ¬Nyquist hold.
    set k := SmoothMap_Circle.fourierFreq (n + 1)
    apply Filter.eventually_atTop.mpr
    refine ⟨n + 1 + 2 * k, fun N hN => ?_⟩
    have hm_lt : n + 1 < N + 1 := by omega
    have hNotNyq : 2 * k ≠ N + 1 := by omega
    exact latticeFourierNormSq_eq_one (N + 1) (n + 1) (by omega) hm_lt hNotNyq

/-- The DFT basis functions are linearly independent over ℝ. -/
theorem latticeFourierBasisFun_linearIndependent (N : ℕ) [NeZero N] :
    LinearIndependent ℝ (fun m : Fin N => latticeFourierBasisFun N m.val) := by
  rw [linearIndependent_iff']
  intro s c hsum m hms
  -- hsum : ∑ i ∈ s, c i • φ_i = 0 (as function ZMod N → ℝ)
  -- Take "dot product" with φ_m to isolate c_m
  have hpw : ∀ z : ZMod N,
      ∑ i ∈ s, c i * latticeFourierBasisFun N i.val z = 0 := by
    intro z; have := congr_fun hsum z; simpa [Finset.sum_apply, smul_eq_mul]
  -- Multiply each equation by φ_m(z) and sum over z
  have h_dot : ∑ z : ZMod N, ∑ i ∈ s,
      c i * (latticeFourierBasisFun N m.val z * latticeFourierBasisFun N i.val z) = 0 := by
    simp_rw [show ∀ (i : Fin N) (z : ZMod N),
        c i * (latticeFourierBasisFun N m.val z * latticeFourierBasisFun N i.val z) =
        latticeFourierBasisFun N m.val z * (c i * latticeFourierBasisFun N i.val z) from
      fun i z => by ring, ← Finset.mul_sum]
    simp [hpw]
  -- Swap sums: ∑_i c_i * (∑_z φ_m(z) * φ_i(z))
  rw [Finset.sum_comm] at h_dot
  simp_rw [← Finset.mul_sum] at h_dot
  -- By orthogonality, ∑_z φ_m(z) * φ_i(z) = 0 for i ≠ m, so only i = m survives
  have h_ortho : ∀ i ∈ s, i ≠ m →
      ∑ z : ZMod N, latticeFourierBasisFun N m.val z *
        latticeFourierBasisFun N i.val z = 0 := by
    intro ⟨i, hi⟩ _ hne
    exact latticeFourierBasisFun_orthogonal N m.val i m.2 hi
      (fun h => hne (Fin.ext h.symm))
  rw [Finset.sum_eq_single m (fun i hi hne => by rw [h_ortho i hi hne, mul_zero])
    (fun hm_not => absurd hms hm_not)] at h_dot
  -- h_dot : c m * normSq(m) = 0
  have h_normSq_pos := latticeFourierNormSq_pos N m.val m.2
  rw [latticeFourierNormSq] at h_normSq_pos
  simp_rw [sq] at h_normSq_pos
  exact (mul_eq_zero.mp h_dot).resolve_right (ne_of_gt h_normSq_pos)

/-- The DFT basis functions span all of `ZMod N → ℝ`. -/
theorem latticeFourierBasisFun_span_eq_top (N : ℕ) [NeZero N] :
    Submodule.span ℝ (Set.range (fun m : Fin N =>
      (fun z : ZMod N => latticeFourierBasisFun N m.val z))) = ⊤ :=
  (latticeFourierBasisFun_linearIndependent N).span_eq_top_of_card_eq_finrank'
    (by rw [Fintype.card_fin, Module.finrank_pi, ZMod.card])

/-- The DFT basis as a `Module.Basis`. -/
noncomputable def latticeFourierBasis (N : ℕ) [NeZero N] :
    Module.Basis (Fin N) ℝ (ZMod N → ℝ) :=
  Module.Basis.mk (latticeFourierBasisFun_linearIndependent N)
    (latticeFourierBasisFun_span_eq_top N).ge

/-- The DFT expansion formula: any `f : ZMod N → ℝ` equals its
Fourier series with coefficients `(f · φ_m) / normSq(m)`. -/
theorem dft_expansion (N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    f = ∑ m : Fin N,
      ((∑ z : ZMod N, f z * latticeFourierBasisFun N m.val z) /
        latticeFourierNormSq N m.val) •
      (fun z => latticeFourierBasisFun N m.val z) := by
  -- Abbreviate the DFT basis functions
  set φ : Fin N → (ZMod N → ℝ) :=
    fun m => latticeFourierBasisFun N m.val with hφ_def
  -- Construct a basis from linear independence + span = ⊤
  set B : Module.Basis (Fin N) ℝ (ZMod N → ℝ) :=
    Module.Basis.mk (latticeFourierBasisFun_linearIndependent N)
      (latticeFourierBasisFun_span_eq_top N).ge
  have hBφ : ∀ m : Fin N, B m = φ m :=
    fun m => Module.Basis.mk_apply _ _ m
  -- Define the "error" g = f - expansion
  set g := f - ∑ m : Fin N,
    ((∑ z, f z * φ m z) / latticeFourierNormSq N m.val) • φ m
  -- Step 1: g · φ_j = 0 for every j (by orthogonality)
  have h_ortho : ∀ j : Fin N,
      ∑ z : ZMod N, g z * φ j z = 0 := by
    intro j
    simp only [g, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [show ∀ (m : Fin N) (z : ZMod N),
        (∑ w, f w * φ m w) / latticeFourierNormSq N m.val *
          φ m z * φ j z =
        ((∑ w, f w * φ m w) / latticeFourierNormSq N m.val) *
          (φ m z * φ j z) from fun m z => by ring]
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_eq_single j]
    · rw [show ∑ z : ZMod N, φ j z * φ j z = latticeFourierNormSq N j.val from by
        simp only [latticeFourierNormSq, sq, φ], div_mul_cancel₀]
      exact ne_of_gt (latticeFourierNormSq_pos N j.val j.2)
    · intro m _ hmj
      rw [latticeFourierBasisFun_orthogonal N m.val j.val m.2 j.2
          (fun h => hmj (Fin.ext h)), mul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  -- Step 2: B.repr g j = 0 for every j
  have hcoeff : ∀ j : Fin N, B.repr g j = 0 := by
    intro j
    -- Pointwise: g z = ∑ m, (B.repr g m) * φ m z
    have h_pw : ∀ z : ZMod N,
        g z = ∑ m : Fin N, B.repr g m * φ m z := by
      intro z
      have h := congr_fun (B.sum_repr g) z
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      rw [← h]; congr 1; ext m _; congr 1; exact congr_fun (hBφ m) _
    -- c_j * normSq(j) = g · φ_j = 0
    have h_dot : B.repr g j * latticeFourierNormSq N j.val = 0 := by
      -- Unfold normSq: ∑ φ² = ∑ φ*φ
      have h_normSq : latticeFourierNormSq N j.val =
          ∑ z : ZMod N, φ j z * φ j z := by
        simp only [latticeFourierNormSq, sq, φ]
      rw [h_normSq, show B.repr g j * ∑ z, φ j z * φ j z =
          ∑ z : ZMod N, g z * φ j z from ?_, h_ortho j]
      -- Expand g, swap sums, use orthogonality
      simp_rw [h_pw, Finset.sum_mul]
      rw [Finset.sum_comm]
      simp_rw [show ∀ (m : Fin N) (z : ZMod N),
          B.repr g m * φ m z * φ j z =
          B.repr g m * (φ m z * φ j z) from fun m z => by ring]
      simp_rw [← Finset.mul_sum]
      rw [Finset.sum_eq_single j
        (fun m _ hmj => by rw [latticeFourierBasisFun_orthogonal N m.val j.val
            m.2 j.2 (fun h => hmj (Fin.ext h)), mul_zero])
        (fun hj => absurd (Finset.mem_univ j) hj)]
    exact (mul_eq_zero.mp h_dot).resolve_right
      (ne_of_gt (latticeFourierNormSq_pos N j.val j.2))
  -- Step 3: g = 0
  have hg : g = 0 :=
    B.ext_elem (fun j => by rw [hcoeff j, map_zero, Finsupp.zero_apply])
  exact sub_eq_zero.mp hg

/-- The normalized DFT basis functions are eigenvectors of the
1D negative Laplacian on `FinLatticeSites 1 N`. -/
theorem negLaplacian1d_dft_eigenvector (N : ℕ) [NeZero N] (a : ℝ) (ha : a ≠ 0)
    (m : ℕ) (_hm : m < N) :
    (negLaplacianMatrix 1 N a).mulVec
      (fun x : FinLatticeSites 1 N => latticeFourierBasisFun N m (x 0)) =
    latticeEigenvalue1d N a m •
      (fun x : FinLatticeSites 1 N => latticeFourierBasisFun N m (x 0)) := by
  -- Helper: eigenvalue formula connecting the cos form to latticeEigenvalue1d
  have hev : ∀ k : ℕ, ∀ n : ℕ, SmoothMap_Circle.fourierFreq (n + 1) = k →
      latticeEigenvalue1d N a (n + 1) =
      2 * a⁻¹ ^ 2 * (1 - cos (2 * π * ↑k / ↑N)) := by
    intro k n hfk
    unfold latticeEigenvalue1d; rw [hfk]
    linarith [eigenvalue_formula a N k]
  funext x; simp only [Pi.smul_apply, smul_eq_mul]
  cases m with
  | zero =>
    -- φ₀ = const 1/√N, λ₀ = 0
    simp only [latticeFourierBasisFun, latticeEigenvalue1d_zero, zero_mul]
    -- M.mulVec (const c) = 0 because Laplacian of constant is 0
    have h := negLaplacian1d_cos_eigenvalue N a ha 0 x
    simp only [Nat.cast_zero, zero_mul, zero_div, cos_zero, sub_self,
      mul_zero] at h
    -- h : M.mulVec (fun _ => 1) x = 0
    conv_lhs =>
      rw [show (fun (_ : FinLatticeSites 1 N) => (1 : ℝ) / Real.sqrt ↑N) =
          (1 / Real.sqrt ↑N) • (fun (_ : FinLatticeSites 1 N) => (1 : ℝ)) from by
        ext; simp]
    rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, h, mul_zero]
  | succ n =>
    simp only [latticeFourierBasisFun]
    set k := n / 2 + 1
    have hfk : SmoothMap_Circle.fourierFreq (n + 1) = k := rfl
    split
    · -- Cos mode
      rw [show (fun x : FinLatticeSites 1 N =>
          Real.sqrt (2 / ↑N) * cos (2 * π * ↑k * ↑(x 0).val / ↑N)) =
        Real.sqrt (2 / ↑N) • (fun x : FinLatticeSites 1 N =>
          cos (2 * π * ↑k * ↑(x 0).val / ↑N)) from rfl,
        Matrix.mulVec_smul]; simp only [Pi.smul_apply, smul_eq_mul]
      rw [negLaplacian1d_cos_eigenvalue N a ha k x, hev k n hfk]; ring
    · -- Sin mode
      rw [show (fun x : FinLatticeSites 1 N =>
          Real.sqrt (2 / ↑N) * sin (2 * π * ↑k * ↑(x 0).val / ↑N)) =
        Real.sqrt (2 / ↑N) • (fun x : FinLatticeSites 1 N =>
          sin (2 * π * ↑k * ↑(x 0).val / ↑N)) from rfl,
        Matrix.mulVec_smul]; simp only [Pi.smul_apply, smul_eq_mul]
      rw [negLaplacian1d_sin_eigenvalue N a ha k x, hev k n hfk]; ring

/-- **Corrected spectral expansion of the 1D lattice heat kernel.**

The bilinear form equals the sum over DFT modes of
`exp(-t λ_m) * c_m(f) * c_m(g) / normSq(m)`.
The `/normSq(m)` factor corrects the normalization at the Nyquist mode
for even N. -/
theorem latticeHeatKernelBilinear1d_eq_spectral' (N : ℕ) [NeZero N] (t : ℝ)
    (f g : SmoothMap_Circle L ℝ) :
    latticeHeatKernelBilinear1d L N t f g =
    ∑ m ∈ Finset.range N,
      Real.exp (-t * latticeEigenvalue1d N (circleSpacing L N) m) *
      latticeDFTCoeff1d L N f m * latticeDFTCoeff1d L N g m /
      latticeFourierNormSq N m := by
  set a := circleSpacing L N
  set M := negLaplacianMatrix 1 N a
  set fN : FinLatticeSites 1 N → ℝ := fun x => circleRestriction L N f (x 0)
  set gN : FinLatticeSites 1 N → ℝ := fun x => circleRestriction L N g (x 0)
  set φ := latticeFourierBasisFun N
  set φL : ℕ → FinLatticeSites 1 N → ℝ := fun m x => φ m (x 0)
  have ha : a ≠ 0 := ne_of_gt (circleSpacing_pos L N)
  -- Step 1: Expand gN via DFT expansion, lifted to FinLatticeSites
  have h_gN_expand : gN = ∑ m : Fin N,
      ((∑ z, circleRestriction L N g z * φ m.val z) /
        latticeFourierNormSq N m.val) • φL m.val := by
    ext x
    have := congr_fun (dft_expansion N (fun z => circleRestriction L N g z)) (x 0)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    exact this
  -- Step 2: Apply exp(-tM) to the expansion
  have h_exp_gN : (latticeHeatKernelMatrix 1 N a t).mulVec gN =
      ∑ m : Fin N,
        (((∑ z, circleRestriction L N g z * φ m.val z) /
          latticeFourierNormSq N m.val) *
        Real.exp (-t * latticeEigenvalue1d N a m.val)) • φL m.val := by
    conv_lhs => rw [h_gN_expand]
    unfold latticeHeatKernelMatrix
    rw [Matrix.mulVec_sum]
    congr 1; ext m
    rw [Matrix.mulVec_smul]
    -- exp(-tM) φL_m = exp(-tλ_m) • φL_m
    have h_eig : (NormedSpace.exp ((-t) • M)).mulVec (φL m.val) =
        Real.exp (-t * latticeEigenvalue1d N a m.val) • φL m.val :=
      Matrix.IsHermitian.mulVec_exp_of_eigenvector
        (negLaplacianMatrix_isHermitian 1 N a) t
        (negLaplacian1d_dft_eigenvector N a ha m.val m.2)
    rw [h_eig, smul_smul]
  -- Step 3: Rewrite bilinear form as a sum and apply h_exp_gN
  show (∑ x, fN x * ((latticeHeatKernelMatrix 1 N a t).mulVec gN) x) =
    ∑ m ∈ Finset.range N,
      Real.exp (-t * latticeEigenvalue1d N a m) *
      latticeDFTCoeff1d L N f m * latticeDFTCoeff1d L N g m /
      latticeFourierNormSq N m
  rw [h_exp_gN]
  simp_rw [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm, ← Fin.sum_univ_eq_sum_range]
  congr 1; ext m
  -- Factor out the scalar coefficient
  have h_rearrange : ∀ (x : FinLatticeSites 1 N),
      fN x * ((∑ z, (circleRestriction L N) g z * φ (↑m) z) /
        latticeFourierNormSq N ↑m *
        rexp (-t * latticeEigenvalue1d N a ↑m) * φL (↑m) x) =
      ((∑ z, (circleRestriction L N) g z * φ (↑m) z) /
        latticeFourierNormSq N ↑m *
        rexp (-t * latticeEigenvalue1d N a ↑m)) *
      (fN x * φL (↑m) x) := fun x => by ring
  simp_rw [h_rearrange, ← Finset.mul_sum]
  -- Identify ∑ x, fN x * φL m x = latticeDFTCoeff1d L N f m
  have h_dot_f : ∑ x : FinLatticeSites 1 N, fN x * φL (↑m) x =
      latticeDFTCoeff1d L N f m.val := by
    rw [sum_fin1_eq_sum_zmod]
    simp only [latticeDFTCoeff1d, fN, φL, φ, m.2, ↓reduceIte]
  rw [h_dot_f]
  -- Identify the coefficient sum with latticeDFTCoeff1d
  have h_coeff_g : ∑ z, (circleRestriction L N) g z * φ (↑m) z =
      latticeDFTCoeff1d L N g m.val := by
    simp only [latticeDFTCoeff1d, φ, m.2, ↓reduceIte]
  rw [h_coeff_g]; ring

/-! ## Full 1D heat kernel convergence -/

/-- The m-th corrected lattice heat kernel term at lattice size N.
Includes the `/ latticeFourierNormSq` factor that corrects the Nyquist mode. -/
private def latticeHeatTerm1d (N : ℕ) [NeZero N] (t : ℝ)
    (f g : SmoothMap_Circle L ℝ) (m : ℕ) : ℝ :=
  Real.exp (-t * latticeEigenvalue1d N (circleSpacing L N) m) *
    latticeDFTCoeff1d L N f m * latticeDFTCoeff1d L N g m /
    latticeFourierNormSq N m

/-- Lattice heat kernel term vanishes for m ≥ N. -/
private theorem latticeHeatTerm1d_zero_of_ge (N : ℕ) [NeZero N] (t : ℝ)
    (f g : SmoothMap_Circle L ℝ) (m : ℕ) (hm : N ≤ m) :
    latticeHeatTerm1d L N t f g m = 0 := by
  unfold latticeHeatTerm1d
  rw [latticeDFTCoeff1d_zero_of_ge L N f m hm]
  ring

/-- The lattice bilinear equals the tsum of corrected lattice heat terms. -/
private theorem latticeHeatKernelBilinear1d_eq_tsum (N : ℕ) [NeZero N] (t : ℝ)
    (f g : SmoothMap_Circle L ℝ) :
    latticeHeatKernelBilinear1d L N t f g =
    ∑' m, latticeHeatTerm1d L N t f g m := by
  rw [latticeHeatKernelBilinear1d_eq_spectral']
  symm
  rw [tsum_eq_sum (s := Finset.range N)]
  · rfl
  · intro m hm
    rw [Finset.mem_range, not_lt] at hm
    exact latticeHeatTerm1d_zero_of_ge L N t f g m hm

/-- **Full 1D heat kernel convergence: lattice → continuum.**

Uses the flat DFT bound `|c_m| ≤ √(2L) · ‖f‖_C⁰` combined with the
eigenvalue lower bound `λ_m ≥ 8m/L²` (from Jordan's inequality) to construct
a summable dominating function `C · exp(-8tm/L²)` for Tannery's theorem.
The `/normSq` correction vanishes for large N (normSq → 1 for fixed m). -/
theorem lattice_heatKernel_tendsto_continuum_1d (t : ℝ) (ht : 0 < t)
    (f g : SmoothMap_Circle L ℝ) :
    Tendsto
      (fun N : ℕ => latticeHeatKernelBilinear1d L (N + 1) t f g)
      atTop
      (nhds (heatKernelBilinear (E := SmoothMap_Circle L ℝ) t f g)) := by
  -- Step 1: Rewrite LHS as tsum of lattice heat terms
  simp_rw [latticeHeatKernelBilinear1d_eq_tsum]
  -- Step 2: RHS unfolds to a tsum
  have hRHS : heatKernelBilinear (E := SmoothMap_Circle L ℝ) t f g =
      ∑' m, Real.exp (-t * HasLaplacianEigenvalues.eigenvalue
        (E := SmoothMap_Circle L ℝ) m) *
        DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g := rfl
  rw [hRHS]
  -- Step 3: Set up flat bounds and eigenvalue decay
  set Cf := Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 0 f
  set Cg := Real.sqrt (2 * L) * SmoothMap_Circle.sobolevSeminorm 0 g
  have hCf_nn : 0 ≤ Cf := mul_nonneg (Real.sqrt_nonneg _)
    (SmoothMap_Circle.sobolevSeminorm_nonneg 0 f)
  have hCg_nn : 0 ≤ Cg := mul_nonneg (Real.sqrt_nonneg _)
    (SmoothMap_Circle.sobolevSeminorm_nonneg 0 g)
  set α := 8 * t / L ^ 2 with hα_def
  have hα_pos : 0 < α := div_pos (mul_pos (by norm_num : (0:ℝ) < 8) ht) (sq_pos_of_pos hL.out)
  -- Summable dominating function: Cf * Cg * exp(-α * m)
  have h_sum : Summable (fun m : ℕ => Cf * Cg * Real.exp (-α * (m : ℝ))) := by
    have h_exp_sum : Summable (fun m : ℕ => Real.exp (-α * (m : ℝ))) := by
      have : ∀ m : ℕ, Real.exp (-α * (m : ℝ)) = Real.exp ((m : ℝ) * (-α)) := by
        intro m; ring_nf
      simp_rw [this]
      exact Real.summable_exp_nat_mul_iff.mpr (by linarith)
    exact h_exp_sum.const_smul (Cf * Cg) |>.congr fun m => by simp [smul_eq_mul]
  -- Step 4: Apply Tannery's theorem
  apply tendsto_tsum_of_dominated_convergence
    (bound := fun m : ℕ => Cf * Cg * Real.exp (-α * (m : ℝ)))
  · exact h_sum
  · -- Pointwise convergence: each term converges
    intro m
    -- normSq(N+1, m) = 1 eventually, so latticeHeatTerm1d = exp * c_f * c_g eventually
    have h_ev : ∀ᶠ N in atTop,
        latticeHeatTerm1d L (N + 1) t f g m =
        Real.exp (-t * latticeEigenvalue1d (N + 1) (circleSpacing L (N + 1)) m) *
          latticeDFTCoeff1d L (N + 1) f m *
          latticeDFTCoeff1d L (N + 1) g m :=
      (latticeFourierNormSq_eventually_one m).mono fun N hN => by
        unfold latticeHeatTerm1d; rw [hN, div_one]
    exact (Filter.Tendsto.mul
        (Filter.Tendsto.mul
          ((Real.continuous_exp.tendsto _).comp
            (tendsto_const_nhds.mul (latticeEigenvalue1d_tendsto_continuum L m)))
          (latticeDFTCoeff1d_tendsto L f m))
        (latticeDFTCoeff1d_tendsto L g m)).congr'
          (Filter.EventuallyEq.symm h_ev)
  · -- Norm bound: |latticeHeatTerm(N,m)| ≤ Cf * Cg * exp(-α*m)
    apply Filter.Eventually.of_forall
    intro N m
    unfold latticeHeatTerm1d
    -- |exp * c_f * c_g / normSq| ≤ |exp * c_f * c_g| since normSq ≥ 1
    rw [Real.norm_eq_abs]
    by_cases hm : m = 0
    · subst hm
      simp only [latticeEigenvalue1d_zero, mul_zero, Real.exp_zero, one_mul,
        latticeFourierNormSq_zero, div_one, Nat.cast_zero, mul_one]
      rw [abs_mul]
      exact mul_le_mul (latticeDFTCoeff1d_flat_bound L f N 0)
        (latticeDFTCoeff1d_flat_bound L g N 0) (abs_nonneg _) hCf_nn
    · have hm' : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      by_cases hm_lt : m < N + 1
      · have h_eig_lb := latticeEigenvalue1d_ge_8m L N m hm' hm_lt
        have h_exp : Real.exp (-t * latticeEigenvalue1d (N + 1)
            (circleSpacing L (N + 1)) m) ≤ Real.exp (-α * (m : ℝ)) := by
          apply Real.exp_le_exp_of_le
          rw [hα_def, neg_mul, neg_mul, neg_le_neg_iff]
          calc 8 * t / L ^ 2 * (m : ℝ)
              = t * (8 * (m : ℝ) / L ^ 2) := by ring
            _ ≤ t * latticeEigenvalue1d (N + 1)
                  (circleSpacing L (N + 1)) m :=
                mul_le_mul_of_nonneg_left h_eig_lb ht.le
        -- |a / b| ≤ |a| when b ≥ 1
        have h_normSq_ge : 1 ≤ latticeFourierNormSq (N + 1) m :=
          latticeFourierNormSq_ge_one (N + 1) m hm_lt
        have h_abs_div : |Real.exp (-t * latticeEigenvalue1d (N + 1)
            (circleSpacing L (N + 1)) m) *
            latticeDFTCoeff1d L (N + 1) f m * latticeDFTCoeff1d L (N + 1) g m /
            latticeFourierNormSq (N + 1) m| ≤
            |Real.exp (-t * latticeEigenvalue1d (N + 1)
              (circleSpacing L (N + 1)) m) *
              latticeDFTCoeff1d L (N + 1) f m * latticeDFTCoeff1d L (N + 1) g m| := by
          rw [abs_div]
          exact div_le_self (abs_nonneg _)
            (by rw [abs_of_nonneg (le_of_lt (latticeFourierNormSq_pos (N + 1) m hm_lt))]
                exact h_normSq_ge)
        calc |Real.exp _ * latticeDFTCoeff1d L (N + 1) f m *
                latticeDFTCoeff1d L (N + 1) g m /
                latticeFourierNormSq (N + 1) m|
            ≤ |Real.exp _ * latticeDFTCoeff1d L (N + 1) f m *
                latticeDFTCoeff1d L (N + 1) g m| := h_abs_div
          _ = Real.exp _ * |latticeDFTCoeff1d L (N + 1) f m| *
                |latticeDFTCoeff1d L (N + 1) g m| := by
              rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
          _ ≤ Real.exp (-α * (m : ℝ)) * Cf * Cg := by
              apply mul_le_mul
              · exact mul_le_mul h_exp
                  (latticeDFTCoeff1d_flat_bound L f N m)
                  (abs_nonneg _) (Real.exp_nonneg _)
              · exact latticeDFTCoeff1d_flat_bound L g N m
              · exact abs_nonneg _
              · exact mul_nonneg (Real.exp_nonneg _) hCf_nn
          _ = Cf * Cg * Real.exp (-α * (m : ℝ)) := by ring
      · rw [latticeDFTCoeff1d_zero_of_ge L (N + 1) f m (by omega),
            latticeDFTCoeff1d_zero_of_ge L (N + 1) g m (by omega)]
        simp only [mul_zero, zero_div, abs_zero]
        exact mul_nonneg (mul_nonneg hCf_nn hCg_nn) (Real.exp_nonneg _)

end GaussianField
