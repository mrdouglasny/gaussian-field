/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Circulant DFT: Eigenvectors and Quadratic Decay

Proves that the lattice Fourier basis functions are eigenvectors of the
1D discrete Laplacian, and uses this to establish quadratic decay of
lattice DFT coefficients (replacing the axiom `latticeDFTCoeff1d_quadratic_bound`).

## Main results

- `negLaplacian1d_cos_eigenvector` — cos modes are eigenvectors of -Δ_a
- `negLaplacian1d_sin_eigenvector` — sin modes are eigenvectors of -Δ_a
- `eigenvector_transfer` — λ_m · c_m(f) = ⟨(-Δ)fN, φ_m⟩
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

end GaussianField
