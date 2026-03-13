/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Heat Semigroup on the Circle S¹_L

Defines the heat semigroup `e^{-tΔ}` as a one-parameter family of continuous
linear endomorphisms of `SmoothMap_Circle L ℝ`, where `Δ = -d²/dx²` is the
circle Laplacian.

## Main definitions

- `circleHeatSemigroup L t` — CLM: `SmoothMap_Circle L ℝ →L[ℝ] SmoothMap_Circle L ℝ`

## Main results

- `circleHeatSemigroup_fourierBasis` — spectral action:
  `e^{-tΔ}(ψ_n) = e^{-tλ_n} · ψ_n`
- `circleHeatSemigroup_comp` — semigroup property:
  `e^{-sΔ} ∘ e^{-tΔ} = e^{-(s+t)Δ}`
- `circleHeatSemigroup_zero` — identity:
  `e^{0·Δ} = id`

## Mathematical background

The heat semigroup is defined spectrally: in the Fourier basis, `e^{-tΔ}`
multiplies the n-th coefficient by `e^{-tλ_n}` where `λ_n = (2πk/L)²`.
Since `e^{-tλ_n} ≤ 1` for t ≥ 0, this preserves rapid decay.

## References

- Reed-Simon, *Methods of Modern Mathematical Physics* Vol. II, §X.12
- Evans, *Partial Differential Equations*, §2.3
-/

import SmoothCircle.Laplacian

noncomputable section

namespace GaussianField

open SmoothMap_Circle

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Heat weight function -/

/-- The heat weight for mode n at time t: `e^{-t·λ_n}`. -/
def heatWeight (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-t * HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) n)

theorem heatWeight_nonneg (t : ℝ) (n : ℕ) : 0 ≤ heatWeight L t n :=
  Real.exp_nonneg _

theorem heatWeight_le_one {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : heatWeight L t n ≤ 1 := by
  unfold heatWeight
  rw [Real.exp_le_one_iff]
  nlinarith [HasLaplacianEigenvalues.eigenvalue_nonneg (E := SmoothMap_Circle L ℝ) n]

theorem heatWeight_abs_le_one {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    |heatWeight L t n| ≤ 1 := by
  rw [abs_le]
  exact ⟨by linarith [heatWeight_nonneg L t n], heatWeight_le_one L ht n⟩

@[simp] theorem heatWeight_zero (n : ℕ) : heatWeight L 0 n = 1 := by
  simp [heatWeight]

theorem heatWeight_add (s t : ℝ) (n : ℕ) :
    heatWeight L (s + t) n = heatWeight L s n * heatWeight L t n := by
  simp only [heatWeight, neg_add_rev, ← Real.exp_add]
  ring_nf

/-! ## Diagonal multiplication on RapidDecaySeq

A bounded weight sequence `w : ℕ → ℝ` with `|w_n| ≤ 1` defines a CLM
on `RapidDecaySeq` by pointwise multiplication. -/

/-- Pointwise multiplication by a bounded sequence preserves rapid decay. -/
private def diagMulFun (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1)
    (a : RapidDecaySeq) : RapidDecaySeq where
  val n := w n * a.val n
  rapid_decay k := by
    apply Summable.of_nonneg_of_le
    · intro n; exact mul_nonneg (abs_nonneg _) (RapidDecaySeq.weight_nonneg n k)
    · intro n
      show |w n * a.val n| * (1 + (n : ℝ)) ^ k ≤ |a.val n| * (1 + (n : ℝ)) ^ k
      calc |w n * a.val n| * (1 + (n : ℝ)) ^ k
          = |w n| * |a.val n| * (1 + (n : ℝ)) ^ k := by rw [abs_mul]
        _ ≤ 1 * |a.val n| * (1 + (n : ℝ)) ^ k := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_right (hw n) (abs_nonneg _)
            · exact pow_nonneg (by positivity) k
        _ = |a.val n| * (1 + (n : ℝ)) ^ k := by ring
    · exact a.rapid_decay k

private def diagMulLM (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) :
    RapidDecaySeq →ₗ[ℝ] RapidDecaySeq where
  toFun := diagMulFun w hw
  map_add' a b := by
    ext n; show w n * (a + b).val n = (diagMulFun w hw a + diagMulFun w hw b).val n
    simp [diagMulFun, RapidDecaySeq.add_val, mul_add]
  map_smul' r a := by
    ext n; show w n * (r • a).val n = (r • diagMulFun w hw a).val n
    simp [diagMulFun, RapidDecaySeq.smul_val, mul_left_comm]

private theorem diagMul_isBounded (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) :
    Seminorm.IsBounded RapidDecaySeq.rapidDecaySeminorm
      RapidDecaySeq.rapidDecaySeminorm (diagMulLM w hw) := by
  intro k
  refine ⟨{k}, 1, fun a => ?_⟩
  simp only [Seminorm.comp_apply, Finset.sup_singleton, one_smul]
  show ∑' n, |w n * a.val n| * (1 + (n : ℝ)) ^ k ≤
    ∑' n, |a.val n| * (1 + (n : ℝ)) ^ k
  exact ((diagMulFun w hw a).rapid_decay k).tsum_le_tsum
    (fun n => by
      calc |w n * a.val n| * (1 + (n : ℝ)) ^ k
          = |w n| * |a.val n| * (1 + (n : ℝ)) ^ k := by rw [abs_mul]
        _ ≤ 1 * |a.val n| * (1 + (n : ℝ)) ^ k := by
            apply mul_le_mul_of_nonneg_right
            · exact mul_le_mul_of_nonneg_right (hw n) (abs_nonneg _)
            · exact pow_nonneg (by positivity) k
        _ = |a.val n| * (1 + (n : ℝ)) ^ k := by ring)
    (a.rapid_decay k)

/-- Diagonal multiplication by a bounded (|w_n| ≤ 1) sequence as a CLM. -/
private def diagMulCLM (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1) :
    RapidDecaySeq →L[ℝ] RapidDecaySeq where
  toLinearMap := diagMulLM w hw
  cont := WithSeminorms.continuous_of_isBounded
    RapidDecaySeq.rapidDecay_withSeminorms
    RapidDecaySeq.rapidDecay_withSeminorms
    (diagMulLM w hw) (diagMul_isBounded w hw)

@[simp] private theorem diagMulCLM_val (w : ℕ → ℝ) (hw : ∀ n, |w n| ≤ 1)
    (a : RapidDecaySeq) (n : ℕ) :
    (diagMulCLM w hw a).val n = w n * a.val n := rfl

/-! ## Heat semigroup -/

/-- **The heat semigroup on S¹_L.**

  `(e^{-tΔ} f)` has Fourier coefficients `e^{-tλ_n} · c_n(f)`.

Defined as conjugation of the diagonal operator through the Fourier
equivalence `SmoothMap_Circle L ℝ ≃L[ℝ] RapidDecaySeq`. -/
def circleHeatSemigroup {t : ℝ} (ht : 0 ≤ t) :
    SmoothMap_Circle L ℝ →L[ℝ] SmoothMap_Circle L ℝ :=
  smoothCircleRapidDecayEquiv.symm.toContinuousLinearMap.comp
    ((diagMulCLM (heatWeight L t) (heatWeight_abs_le_one L ht)).comp
      smoothCircleRapidDecayEquiv.toContinuousLinearMap)

/-- The heat semigroup acts on the Fourier basis by eigenvalue exponential.

  `e^{-tΔ}(ψ_n) = e^{-tλ_n} · ψ_n` -/
theorem circleHeatSemigroup_fourierBasis {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    circleHeatSemigroup L ht (SmoothMap_Circle.fourierBasis n) =
    heatWeight L t n • SmoothMap_Circle.fourierBasis n := by
  unfold circleHeatSemigroup
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  set e := smoothCircleRapidDecayEquiv (L := L) with he_def
  -- The Fourier equiv maps fourierBasis n to a basis vector
  have h_coeff : ∀ i, (e (SmoothMap_Circle.fourierBasis n)).val i =
      if i = n then 1 else 0 := by
    intro i
    show (toRapidDecayLM (L := L) (SmoothMap_Circle.fourierBasis n)).val i = _
    simp only [toRapidDecayLM]
    exact fourierCoeffReal_fourierBasis i n
  -- Diagonal multiplication by heatWeight scales by heatWeight n
  have h_diag : diagMulCLM (heatWeight L t) (heatWeight_abs_le_one L ht)
      (e (SmoothMap_Circle.fourierBasis n)) =
      heatWeight L t n • e (SmoothMap_Circle.fourierBasis n) := by
    apply RapidDecaySeq.ext; intro i
    simp only [diagMulCLM_val, RapidDecaySeq.smul_val, h_coeff]
    split
    · subst_vars; ring
    · ring
  rw [h_diag, map_smul, ContinuousLinearEquiv.symm_apply_apply]

/-- The heat semigroup at time 0 is the identity.

  `e^{0·Δ} = id` -/
theorem circleHeatSemigroup_zero :
    circleHeatSemigroup L le_rfl = ContinuousLinearMap.id ℝ _ := by
  ext f
  unfold circleHeatSemigroup
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe]
  have h : diagMulCLM (heatWeight L 0) (heatWeight_abs_le_one L le_rfl)
      (smoothCircleRapidDecayEquiv (L := L) f) =
      smoothCircleRapidDecayEquiv (L := L) f := by
    apply RapidDecaySeq.ext; intro n
    simp [heatWeight]
  rw [h, ContinuousLinearEquiv.symm_apply_apply]

end GaussianField
