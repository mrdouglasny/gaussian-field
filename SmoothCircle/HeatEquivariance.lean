/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Circle Heat Semigroup Equivariance

Proves that the heat semigroup on S¹_L commutes with spatial translation
and reflection. These are the spatial components of the cylinder heat
kernel equivariance needed for Green's function invariance.

## Main results

- `circleHeatSemigroup_translation_comm` — `e^{-tΔ} ∘ T_v = T_v ∘ e^{-tΔ}`
- `circleHeatSemigroup_reflection_comm` — `e^{-tΔ} ∘ Θ = Θ ∘ e^{-tΔ}`

## Proof strategy

Both proofs work by comparing Fourier coefficients. The heat semigroup
multiplies the n-th coefficient by `heatWeight L t n = e^{-tλ_n}`, while
translation rotates cos/sin pairs by angle `θ = 2πkv/L`.

The key fact: paired modes `(2k-1, 2k)` share the same eigenvalue
`λ_{2k-1} = λ_{2k} = (2πk/L)²`, so the diagonal heat weight commutes
with the 2×2 rotation matrix on each pair.

## References

- Reed-Simon, *Methods of Modern Mathematical Physics* Vol. II, §X.12
-/

import SmoothCircle.HeatSemigroup
import SmoothCircle.FourierTranslation

noncomputable section

namespace GaussianField

open SmoothMap_Circle

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Paired mode eigenvalue equality

Fourier modes `2k-1` (cosine) and `2k` (sine) for the same frequency k
share the same Laplacian eigenvalue `(2πk/L)²`, hence the same heat weight. -/

omit hL in
/-- Paired cosine/sine modes have the same Fourier frequency. -/
theorem fourierFreq_paired (k : ℕ) (hk : 0 < k) :
    fourierFreq (2 * k - 1) = fourierFreq (2 * k) := by
  have h1 : 2 * k - 1 = 2 * (k - 1) + 1 := by omega
  have h2 : 2 * k = (2 * k - 1) + 1 := by omega
  rw [h1, h2]; simp only [fourierFreq]; omega

/-- Paired cosine/sine modes have the same Laplacian eigenvalue. -/
theorem eigenvalue_paired (k : ℕ) (hk : 0 < k) :
    HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) (2 * k - 1) =
    HasLaplacianEigenvalues.eigenvalue (E := SmoothMap_Circle L ℝ) (2 * k) := by
  show (2 * Real.pi * ↑(fourierFreq (2 * k - 1)) / L) ^ 2 =
    (2 * Real.pi * ↑(fourierFreq (2 * k)) / L) ^ 2
  rw [fourierFreq_paired k hk]

/-- Paired cosine/sine modes have the same heat weight. -/
theorem heatWeight_paired (t : ℝ) (k : ℕ) (hk : 0 < k) :
    heatWeight L t (2 * k - 1) = heatWeight L t (2 * k) := by
  unfold heatWeight
  rw [eigenvalue_paired L k hk]

/-! ## Heat semigroup commutes with translation -/

/-- `smoothCircleRapidDecayEquiv` extracts Fourier coefficients. -/
private lemma equiv_val (f : SmoothMap_Circle L ℝ) (n : ℕ) :
    (smoothCircleRapidDecayEquiv (L := L) f).val n = fourierCoeffReal n f := rfl

/-- The circle heat semigroup commutes with spatial translation.

  `e^{-tΔ}(T_v f) = T_v(e^{-tΔ} f)` for all v, t ≥ 0, f.

Proof: both sides have the same Fourier coefficients. The heat semigroup
scales each coefficient by `e^{-tλ_n}`, and translation rotates each
(cos, sin) pair. These commute because paired modes share the same
eigenvalue. -/
theorem circleHeatSemigroup_translation_comm {t : ℝ} (ht : 0 ≤ t) (v : ℝ)
    (f : SmoothMap_Circle L ℝ) :
    circleHeatSemigroup L ht (circleTranslation L v f) =
    circleTranslation L v (circleHeatSemigroup L ht f) := by
  -- Reduce to equality of Fourier coefficients
  apply smoothCircleRapidDecayEquiv.injective
  apply RapidDecaySeq.ext; intro n
  -- Rewrite LHS using heat semigroup coefficient formula
  rw [circleHeatSemigroup_fourierCoeff, equiv_val, equiv_val]
  -- Goal: heatWeight L t n * fourierCoeffReal n (T_v f) =
  --        fourierCoeffReal n (T_v (heat f))
  -- Abbreviate the heated function
  set g := circleHeatSemigroup L ht f
  -- Key: Fourier coefficients of g = heat f
  have hg : ∀ m, fourierCoeffReal m g =
      heatWeight L t m * fourierCoeffReal m f := fun m => by
    have := circleHeatSemigroup_fourierCoeff L ht f m
    rwa [equiv_val, equiv_val] at this
  -- Case split on n
  cases n with
  | zero =>
    -- Constant mode: translation-invariant
    rw [fourierCoeffReal_circleTranslation_zero,
        fourierCoeffReal_circleTranslation_zero, hg]
  | succ m =>
    -- For m+1: determine if cos mode (m even) or sin mode (m odd)
    rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- m = 2j, so n = 2j+1 = 2(j+1)-1 is a cos mode with k = j+1
      have hn : m + 1 = 2 * (j + 1) - 1 := by omega
      have hk : 0 < j + 1 := by omega
      rw [hn,
          fourierCoeffReal_circleTranslation_cos L (j + 1) hk v f,
          fourierCoeffReal_circleTranslation_cos L (j + 1) hk v g,
          hg (2 * (j + 1) - 1), hg (2 * (j + 1)),
          heatWeight_paired L t (j + 1) hk]
      ring
    · -- m = 2j+1, so n = 2j+2 = 2(j+1) is a sin mode with k = j+1
      have hn : m + 1 = 2 * (j + 1) := by omega
      have hk : 0 < j + 1 := by omega
      rw [hn,
          fourierCoeffReal_circleTranslation_sin L (j + 1) hk v f,
          fourierCoeffReal_circleTranslation_sin L (j + 1) hk v g,
          hg (2 * (j + 1) - 1), hg (2 * (j + 1)),
          heatWeight_paired L t (j + 1) hk]
      ring

/-! ## Heat semigroup commutes with reflection -/

/-- The circle heat semigroup commutes with spatial reflection.

  `e^{-tΔ}(Θ f) = Θ(e^{-tΔ} f)` for all t ≥ 0, f.

Proof: reflection preserves cos modes and negates sin modes. Since
the heat weight depends only on the frequency (shared by paired modes),
it commutes with this action. -/
theorem circleHeatSemigroup_reflection_comm {t : ℝ} (ht : 0 ≤ t)
    (f : SmoothMap_Circle L ℝ) :
    circleHeatSemigroup L ht (circleReflection L f) =
    circleReflection L (circleHeatSemigroup L ht f) := by
  apply smoothCircleRapidDecayEquiv.injective
  apply RapidDecaySeq.ext; intro n
  rw [circleHeatSemigroup_fourierCoeff, equiv_val, equiv_val]
  set g := circleHeatSemigroup L ht f
  have hg : ∀ m, fourierCoeffReal m g =
      heatWeight L t m * fourierCoeffReal m f := fun m => by
    have := circleHeatSemigroup_fourierCoeff L ht f m
    rwa [equiv_val, equiv_val] at this
  cases n with
  | zero =>
    rw [fourierCoeffReal_circleReflection_zero,
        fourierCoeffReal_circleReflection_zero, hg]
  | succ m =>
    rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
    · -- cos mode 2(j+1)-1: reflection preserves
      have hn : m + 1 = 2 * (j + 1) - 1 := by omega
      have hk : 0 < j + 1 := by omega
      rw [hn,
          fourierCoeffReal_circleReflection_cos L (j + 1) hk f,
          fourierCoeffReal_circleReflection_cos L (j + 1) hk g, hg]
    · -- sin mode 2(j+1): reflection negates
      have hn : m + 1 = 2 * (j + 1) := by omega
      have hk : 0 < j + 1 := by omega
      rw [hn,
          fourierCoeffReal_circleReflection_sin L (j + 1) hk f,
          fourierCoeffReal_circleReflection_sin L (j + 1) hk g, hg]
      ring

end GaussianField
