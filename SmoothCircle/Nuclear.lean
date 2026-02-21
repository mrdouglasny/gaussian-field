/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# DyninMityaginSpace Instance for C∞(S¹)

Proves that `SmoothCircle L` is a `DyninMityaginSpace` by constructing a
continuous linear equivalence with `RapidDecaySeq` via the real Fourier transform.

## Main results

- `smoothCircleRapidDecayEquiv` — CLE: `SmoothCircle L ≃L[ℝ] RapidDecaySeq`
- `smoothCircle_dyninMityaginSpace` — the `DyninMityaginSpace` instance

## Mathematical outline

1. **Coefficient decay** (integration by parts): `|c_n(f)| ≤ C · p_k(f) / n^k`
2. **Fourier series convergence**: `f = ∑ₙ c_n(f) · ψ_n` in the seminorm topology
3. **Forward map**: `f ↦ (c_n(f))_n` maps into `RapidDecaySeq`
4. **Backward map**: `(a_n) ↦ ∑ₙ a_n · ψ_n` maps into `SmoothCircle L`
5. **CLE**: forward ∘ backward = id (by orthogonality), backward ∘ forward = id (by uniqueness)
-/

import SmoothCircle.Basic

noncomputable section

namespace GaussianField

open SmoothCircle

variable {L : ℝ} [hL : Fact (0 < L)]

namespace SmoothCircle

/-! ## Integration by parts: Fourier coefficient decay -/

/-- Integration by parts gives rapid decay of Fourier coefficients:
`|c_n(f)| * (1+n)^k ≤ C · max(p_0(f), p_k(f))` for all k.

For n = 0: bounded by `C · p_0(f)` (integral bound).
For n ≥ 1: integrating by parts k times gives
`|c_n(f)| ≤ C · p_k(f) / n^k`, hence `|c_n(f)| · (1+n)^k ≤ C' · p_k(f)`.
Combined: bounded by `C · max(p_0, p_k)`. -/
theorem fourierCoeffReal_decay (k : ℕ) :
    ∃ C > 0, ∀ (f : SmoothCircle L) (n : ℕ),
      ‖fourierCoeffReal n f‖ * (1 + (n : ℝ)) ^ k ≤
        C * (({0, k} : Finset ℕ).sup sobolevSeminorm) f := by
  sorry

/-! ## Forward map: SmoothCircle → RapidDecaySeq -/

/-- Helper: summability of shifted inverse square series `∑ 1/(1+n)^2`. -/
private theorem summable_shifted_inv_sq :
    Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
  have h := (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
  refine (h.comp_injective (fun a b h => Nat.succ_injective h)).congr (fun n => ?_)
  simp only [Function.comp, Nat.cast_succ]
  ring

/-- The Fourier coefficients of a smooth periodic function form a rapidly
decreasing sequence. Uses `fourierCoeffReal_decay` at order k+2 and
comparison with the convergent p-series `∑ 1/(1+n)^2`. -/
theorem fourierCoeff_rapid_decay (f : SmoothCircle L) (k : ℕ) :
    Summable (fun m => |fourierCoeffReal (L := L) m f| * (1 + (m : ℝ)) ^ k) := by
  obtain ⟨C, hC, hbound⟩ := fourierCoeffReal_decay (L := L) (k + 2)
  set B := C * (({0, k + 2} : Finset ℕ).sup sobolevSeminorm) f
  have h_sum : Summable (fun m : ℕ => B * (1 / ((m : ℝ) + 1) ^ 2)) :=
    summable_shifted_inv_sq.mul_left B
  refine Summable.of_nonneg_of_le
    (fun m => mul_nonneg (abs_nonneg _) (pow_nonneg (by positivity) _))
    (fun m => ?_)
    h_sum
  -- Goal: |c_m f| * (1+m)^k ≤ B * (1 / (↑m + 1) ^ 2)
  have h1m : (0 : ℝ) < 1 + ↑m := by positivity
  have hm := hbound f m
  rw [Real.norm_eq_abs] at hm
  rw [mul_one_div]
  rw [show (↑m : ℝ) + 1 = 1 + ↑m from by ring]
  rw [le_div_iff₀ (pow_pos h1m 2)]
  calc |fourierCoeffReal m f| * (1 + ↑m) ^ k * (1 + ↑m) ^ 2
      = |fourierCoeffReal m f| * (1 + ↑m) ^ (k + 2) := by rw [pow_add, mul_assoc]
    _ ≤ B := hm

/-- The forward map: Fourier coefficients as a `RapidDecaySeq`. -/
def toRapidDecay (f : SmoothCircle L) : RapidDecaySeq where
  val m := fourierCoeffReal m f
  rapid_decay k := fourierCoeff_rapid_decay f k

/-- The forward map is linear. -/
def toRapidDecayLM : SmoothCircle L →ₗ[ℝ] RapidDecaySeq where
  toFun := toRapidDecay
  map_add' f g := by
    apply RapidDecaySeq.ext; intro m
    simp only [toRapidDecay, RapidDecaySeq.add_val]
    exact fourierCoeffReal_add m f g
  map_smul' r f := by
    apply RapidDecaySeq.ext; intro m
    simp only [toRapidDecay, RapidDecaySeq.smul_val, smul_eq_mul]
    exact fourierCoeffReal_smul m r f

/-- The forward map is continuous. -/
theorem toRapidDecay_continuous : Continuous (toRapidDecayLM (L := L)) := by
  apply Seminorm.continuous_from_bounded smoothCircle_withSeminorms
    RapidDecaySeq.rapidDecay_withSeminorms
  intro k
  obtain ⟨C, hC, hbound⟩ := fourierCoeffReal_decay (L := L) (k + 2)
  set Z := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2
  refine ⟨{0, k + 2}, ⟨C * Z, by positivity⟩, fun f => ?_⟩
  simp only [Seminorm.comp_apply, NNReal.smul_def, Seminorm.smul_apply, NNReal.coe_mk]
  show ∑' m, |fourierCoeffReal m f| * (1 + (m : ℝ)) ^ k ≤
    C * Z * (({0, k + 2} : Finset ℕ).sup sobolevSeminorm) f
  set S := (({0, k + 2} : Finset ℕ).sup sobolevSeminorm) f
  have h_le : ∀ m : ℕ, |fourierCoeffReal m f| * (1 + (m : ℝ)) ^ k ≤
      C * S * (1 / ((↑m : ℝ) + 1) ^ 2) := by
    intro m
    have h1m : (0 : ℝ) < 1 + ↑m := by positivity
    have hm := hbound f m
    rw [Real.norm_eq_abs] at hm
    calc |fourierCoeffReal m f| * (1 + ↑m) ^ k
        = |fourierCoeffReal m f| * (1 + ↑m) ^ (k + 2) / (1 + ↑m) ^ 2 := by
          rw [pow_add]; field_simp
      _ ≤ C * S / (1 + ↑m) ^ 2 := div_le_div_of_nonneg_right hm (sq_nonneg _)
      _ = C * S * (1 / ((↑m : ℝ) + 1) ^ 2) := by ring
  calc ∑' m, |fourierCoeffReal m f| * (1 + ↑m) ^ k
      ≤ ∑' (m : ℕ), C * S * (1 / ((↑m : ℝ) + 1) ^ 2) :=
        (fourierCoeff_rapid_decay f k).tsum_le_tsum h_le
          ((summable_shifted_inv_sq.mul_left (C * S)).congr (fun n => by ring))
    _ = C * S * Z := by rw [tsum_mul_left]
    _ = C * Z * S := by ring

/-- The forward map as a CLM. -/
def toRapidDecayCLM : SmoothCircle L →L[ℝ] RapidDecaySeq where
  toLinearMap := toRapidDecayLM
  cont := toRapidDecay_continuous

/-! ## Backward map: RapidDecaySeq → SmoothCircle -/

theorem summable_fourierBasis_smul (a : RapidDecaySeq) :
    ∀ x, Summable (fun n => a.val n * fourierBasisFun (L := L) n x) := by
  intro x
  set C := max (1 / Real.sqrt L) (Real.sqrt (2 / L))
  apply Summable.of_norm_bounded (g := fun n => C * |a.val n|)
  · have h0 := a.rapid_decay 0
    simp only [pow_zero, mul_one] at h0
    exact (h0.mul_left C).congr (fun n => by simp)
  · intro n
    simp only [Real.norm_eq_abs, abs_mul]
    calc |a.val n| * |fourierBasisFun (L := L) n x|
        ≤ |a.val n| * C := mul_le_mul_of_nonneg_left (fourierBasisFun_abs_le n x) (abs_nonneg _)
      _ = C * |a.val n| := mul_comm _ _

/-- The Fourier series of rapidly decaying coefficients defines a smooth function. -/
theorem contDiff_fourierSeries (a : RapidDecaySeq) :
    ContDiff ℝ ⊤ (fun x => ∑' n, a.val n * fourierBasisFun (L := L) n x) := by
  sorry

/-- The Fourier series of rapidly decaying coefficients defines a periodic function. -/
theorem periodic_fourierSeries (a : RapidDecaySeq) :
    Function.Periodic (fun x => ∑' n, a.val n * fourierBasisFun (L := L) n x) L := by
  intro x
  show ∑' n, a.val n * fourierBasisFun (L := L) n (x + L) =
    ∑' n, a.val n * fourierBasisFun (L := L) n x
  congr 1; ext n
  rw [fourierBasisFun_periodic (L := L) n x]

/-- The backward map: reconstruct a smooth periodic function from coefficients. -/
def fromRapidDecay (a : RapidDecaySeq) : SmoothCircle L :=
  ⟨fun x => ∑' n, a.val n * fourierBasisFun (L := L) n x,
   periodic_fourierSeries a,
   contDiff_fourierSeries a⟩

/-- The backward map is linear. -/
def fromRapidDecayLM : RapidDecaySeq →ₗ[ℝ] SmoothCircle L where
  toFun := fromRapidDecay
  map_add' a b := by
    apply SmoothCircle.ext; intro x
    show ∑' n, (a.val n + b.val n) * fourierBasisFun (L := L) n x =
      (∑' n, a.val n * fourierBasisFun (L := L) n x) +
      (∑' n, b.val n * fourierBasisFun (L := L) n x)
    simp_rw [add_mul]
    exact (summable_fourierBasis_smul a x).tsum_add (summable_fourierBasis_smul b x)
  map_smul' r a := by
    apply SmoothCircle.ext; intro x
    show ∑' n, (r * a.val n) * fourierBasisFun (L := L) n x =
      r * (∑' n, a.val n * fourierBasisFun (L := L) n x)
    simp_rw [mul_assoc]
    exact tsum_mul_left

/-- The backward map is continuous. -/
theorem fromRapidDecay_continuous : Continuous (fromRapidDecayLM (L := L)) := by
  apply Seminorm.continuous_from_bounded RapidDecaySeq.rapidDecay_withSeminorms
    smoothCircle_withSeminorms
  -- For each Sobolev seminorm p_k, bound by rapid decay seminorm k+2
  sorry

/-- The backward map as a CLM. -/
def fromRapidDecayCLM : RapidDecaySeq →L[ℝ] SmoothCircle L where
  toLinearMap := fromRapidDecayLM
  cont := fromRapidDecay_continuous

/-! ## Fourier series convergence -/

/-- **Fourier series expansion**: every smooth periodic function equals the
sum of its Fourier series `∑ₙ c_n(f) · ψ_n` in the seminorm topology. -/
theorem hasSum_fourierBasis (f : SmoothCircle L) :
    f = fromRapidDecay (toRapidDecay f) := by
  sorry

/-! ## Continuous linear equivalence -/

/-- Forward then backward is the identity: if we take Fourier coefficients
and reconstruct, we get back the original function. -/
theorem fromRapidDecay_toRapidDecay (f : SmoothCircle L) :
    fromRapidDecay (toRapidDecay f) = f :=
  (hasSum_fourierBasis f).symm

/-- Backward then forward is the identity: if we construct a function from
rapidly decaying coefficients and take its Fourier coefficients, we get
back the original sequence. This follows from orthogonality. -/
theorem toRapidDecay_fromRapidDecay (a : RapidDecaySeq) :
    toRapidDecay (fromRapidDecay (L := L) a) = a := by
  apply RapidDecaySeq.ext; intro m
  show fourierCoeffReal m (fromRapidDecay a) = a.val m
  -- This reduces to: (1/L) ∫₀ᴸ (∑ₙ aₙ ψₙ(x)) ψₘ(x) dx = aₘ
  -- by exchanging sum and integral (justified by absolute convergence)
  -- and using orthogonality: (1/L) ∫₀ᴸ ψₙ(x) ψₘ(x) dx = δ_{nm}
  sorry

/-- The continuous linear equivalence between `SmoothCircle L` and `RapidDecaySeq`
via the real Fourier transform. -/
def smoothCircleRapidDecayEquiv : SmoothCircle L ≃L[ℝ] RapidDecaySeq where
  toLinearMap := toRapidDecayLM
  invFun := fromRapidDecay
  left_inv f := fromRapidDecay_toRapidDecay f
  right_inv a := toRapidDecay_fromRapidDecay a
  continuous_toFun := toRapidDecay_continuous
  continuous_invFun := fromRapidDecay_continuous

/-! ## DyninMityaginSpace instance -/

end SmoothCircle

/-- **C∞(S¹) is a nuclear Fréchet space.**

The instance uses the Sobolev sup-seminorm family `k ↦ p_k` and a
basis/coefficient system derived from the topological isomorphism
`SmoothCircle L ≃L[ℝ] RapidDecaySeq` constructed from the real Fourier basis.

This enables Gaussian fields on the torus T¹ = ℝ/Lℤ and (via tensor products)
on cylinders S¹×ℝ and higher tori Tᵈ. -/
noncomputable instance smoothCircle_dyninMityaginSpace :
    DyninMityaginSpace (SmoothCircle L) :=
  DyninMityaginSpace.ofRapidDecayEquiv
    SmoothCircle.sobolevSeminorm
    SmoothCircle.smoothCircle_withSeminorms
    SmoothCircle.smoothCircleRapidDecayEquiv

end GaussianField
