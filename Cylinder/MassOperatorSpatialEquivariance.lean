/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas

# Mass-operator spatial equivariance

Discharges the remaining spatial-translation `_norm_eq` axiom by proving
invariance of the bilinear form `⟪Tf, Tg⟫` on pure tensors and extending
from pure tensors to all cylinder test functions by the DM basis expansion.
-/

import Cylinder.MassOperatorConstruction
import Cylinder.Symmetry
import HeatKernel.GreenInvariance
import SmoothCircle.HeatEquivariance
import Nuclear.NuclearExtension

noncomputable section

namespace GaussianField

variable (L : ℝ) [hL : Fact (0 < L)]

private def massInnerBilinear (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) : ℝ :=
  @inner ℝ ell2' _ (cylinderMassOperator L mass hmass f)
    (cylinderMassOperator L mass hmass g)

private theorem massInnerBilinear_add_left
    (mass : ℝ) (hmass : 0 < mass)
    (f₁ f₂ g : CylinderTestFunction L) :
    massInnerBilinear L mass hmass (f₁ + f₂) g =
      massInnerBilinear L mass hmass f₁ g +
        massInnerBilinear L mass hmass f₂ g := by
  simp [massInnerBilinear, inner_add_left]

private theorem massInnerBilinear_smul_left
    (mass : ℝ) (hmass : 0 < mass)
    (c : ℝ) (f g : CylinderTestFunction L) :
    massInnerBilinear L mass hmass (c • f) g =
      c * massInnerBilinear L mass hmass f g := by
  simp [massInnerBilinear, real_inner_smul_left]

private theorem massInnerBilinear_symm
    (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    massInnerBilinear L mass hmass f g =
      massInnerBilinear L mass hmass g f := by
  simp [massInnerBilinear, real_inner_comm]

private def massInnerCLM_left
    (mass : ℝ) (hmass : 0 < mass) (g : CylinderTestFunction L) :
    CylinderTestFunction L →L[ℝ] ℝ :=
  { toLinearMap :=
      { toFun := fun f => massInnerBilinear L mass hmass f g
        map_add' := fun f₁ f₂ => massInnerBilinear_add_left L mass hmass f₁ f₂ g
        map_smul' := fun c f => by
          rw [massInnerBilinear_smul_left, RingHom.id_apply, smul_eq_mul] }
    cont := by
      let hpair : Continuous fun f : CylinderTestFunction L =>
          ((cylinderMassOperator L mass hmass f), cylinderMassOperator L mass hmass g) :=
        ((cylinderMassOperator L mass hmass).continuous).prodMk continuous_const
      simpa [massInnerBilinear] using continuous_inner.comp hpair }

@[simp] private theorem massInnerCLM_left_apply
    (mass : ℝ) (hmass : 0 < mass)
    (f g : CylinderTestFunction L) :
    massInnerCLM_left L mass hmass g f =
      massInnerBilinear L mass hmass f g := rfl

private theorem massInner_invariant_of_pure
    (mass : ℝ) (hmass : 0 < mass)
    (S : CylinderTestFunction L →L[ℝ] CylinderTestFunction L)
    (hpure : ∀ (e₁ e₁' : SmoothMap_Circle L ℝ) (e₂ e₂' : SchwartzMap ℝ ℝ),
      massInnerBilinear L mass hmass
          (S (NuclearTensorProduct.pure e₁ e₂))
          (S (NuclearTensorProduct.pure e₁' e₂')) =
        massInnerBilinear L mass hmass
          (NuclearTensorProduct.pure e₁ e₂)
          (NuclearTensorProduct.pure e₁' e₂'))
    (f g : CylinderTestFunction L) :
    massInnerBilinear L mass hmass (S f) (S g) =
      massInnerBilinear L mass hmass f g := by
  suffices phaseA :
      ∀ (e₁' : SmoothMap_Circle L ℝ) (e₂' : SchwartzMap ℝ ℝ)
        (f' : CylinderTestFunction L),
        massInnerBilinear L mass hmass (S f')
            (S (NuclearTensorProduct.pure e₁' e₂')) =
          massInnerBilinear L mass hmass f'
            (NuclearTensorProduct.pure e₁' e₂') by
    set ψB : CylinderTestFunction L →L[ℝ] ℝ :=
      (massInnerCLM_left L mass hmass (S f)).comp S -
        massInnerCLM_left L mass hmass f
    have hψB : ∀ n, ψB (DyninMityaginSpace.basis n) = 0 := by
      intro n
      simp only [ψB, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
        massInnerCLM_left_apply, sub_eq_zero]
      rw [show (DyninMityaginSpace.basis (E := CylinderTestFunction L) n :
          CylinderTestFunction L) =
          NuclearTensorProduct.pure
            (DyninMityaginSpace.basis (E := SmoothMap_Circle L ℝ) (Nat.unpair n).1)
            (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) (Nat.unpair n).2) from
        NuclearTensorProduct.basisVec_eq_pure (smoothCircle_coeff_basis L)
          DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis n,
        massInnerBilinear_symm L mass hmass
          (S (NuclearTensorProduct.pure
            (DyninMityaginSpace.basis (E := SmoothMap_Circle L ℝ) (Nat.unpair n).1)
            (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) (Nat.unpair n).2))) (S f),
        massInnerBilinear_symm L mass hmass
          (NuclearTensorProduct.pure
            (DyninMityaginSpace.basis (E := SmoothMap_Circle L ℝ) (Nat.unpair n).1)
            (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) (Nat.unpair n).2)) f]
      exact phaseA _ _ f
    have hexp := DyninMityaginSpace.expansion ψB g
    have hzero : ψB g = 0 := by
      rw [hexp]
      convert tsum_zero with n
      rw [hψB, mul_zero]
    simp only [ψB, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      massInnerCLM_left_apply, sub_eq_zero] at hzero
    rwa [massInnerBilinear_symm L mass hmass (S g) (S f),
      massInnerBilinear_symm L mass hmass g f] at hzero
  intro e₁' e₂' f'
  set ψA : CylinderTestFunction L →L[ℝ] ℝ :=
    (massInnerCLM_left L mass hmass (S (NuclearTensorProduct.pure e₁' e₂'))).comp S -
      massInnerCLM_left L mass hmass (NuclearTensorProduct.pure e₁' e₂')
  have hψA : ∀ n, ψA (DyninMityaginSpace.basis n) = 0 := by
    intro n
    simp only [ψA, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      massInnerCLM_left_apply, sub_eq_zero]
    rw [show (DyninMityaginSpace.basis (E := CylinderTestFunction L) n :
        CylinderTestFunction L) =
        NuclearTensorProduct.pure
          (DyninMityaginSpace.basis (E := SmoothMap_Circle L ℝ) (Nat.unpair n).1)
          (DyninMityaginSpace.basis (E := SchwartzMap ℝ ℝ) (Nat.unpair n).2) from
      NuclearTensorProduct.basisVec_eq_pure (smoothCircle_coeff_basis L)
        DyninMityaginSpace.HasBiorthogonalBasis.coeff_basis n]
    exact hpure _ _ _ _
  have hexp := DyninMityaginSpace.expansion ψA f'
  have hzero : ψA f' = 0 := by
    rw [hexp]
    convert tsum_zero with n
    rw [hψA, mul_zero]
  simpa only [ψA, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    massInnerCLM_left_apply, sub_eq_zero] using hzero

omit hL in
private theorem resolventFreq_modePartner (mass : ℝ) (n : ℕ) :
    resolventFreq L mass n = resolventFreq L mass (modePartner n) := by
  unfold resolventFreq
  congr 2
  cases n with
  | zero =>
      simp [modePartner]
  | succ n =>
      rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
      · have hn : n + 1 = 2 * (j + 1) - 1 := by omega
        have hp : modePartner (n + 1) = 2 * (j + 1) := by
          rw [hn]
          exact modePartner_cos (j + 1) (by omega)
        rw [hp, hn]
        exact congrArg (fun t : ℕ => (2 * Real.pi * (t : ℝ) / L) ^ 2)
          (fourierFreq_paired (j + 1) (by omega))
      · have hn : n + 1 = 2 * (j + 1) := by omega
        have hp : modePartner (n + 1) = 2 * (j + 1) - 1 := by
          rw [hn]
          exact modePartner_sin (j + 1) (by omega)
        rw [hp, hn]
        exact congrArg (fun t : ℕ => (2 * Real.pi * (t : ℝ) / L) ^ 2)
          ((fourierFreq_paired (j + 1) (by omega)).symm)

set_option maxHeartbeats 3000000 in
private theorem massInner_spatialTranslation_pure
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ)
    (f₁ g₁ : SmoothMap_Circle L ℝ) (f₂ g₂ : SchwartzMap ℝ ℝ) :
    massInnerBilinear L mass hmass
      (NuclearTensorProduct.pure (circleTranslation L v f₁) f₂)
      (NuclearTensorProduct.pure (circleTranslation L v g₁) g₂) =
    massInnerBilinear L mass hmass
      (NuclearTensorProduct.pure f₁ f₂)
      (NuclearTensorProduct.pure g₁ g₂) := by
  unfold massInnerBilinear
  rw [lp.inner_eq_tsum]
  let Fv := cylinderMassOperator L mass hmass
    (NuclearTensorProduct.pure (circleTranslation L v f₁) f₂)
  let Gv := cylinderMassOperator L mass hmass
    (NuclearTensorProduct.pure (circleTranslation L v g₁) g₂)
  let F₀ := cylinderMassOperator L mass hmass (NuclearTensorProduct.pure f₁ f₂)
  let G₀ := cylinderMassOperator L mass hmass (NuclearTensorProduct.pure g₁ g₂)
  set σ : ℕ ≃ ℕ := Nat.pairEquiv.symm.trans
    ((Equiv.prodCongrLeft fun _ => modePartnerEquiv).trans Nat.pairEquiv)
  have hsumv : Summable (fun n : ℕ => @inner ℝ ℝ _ (Fv n) (Gv n)) := lp.summable_inner Fv Gv
  have hsum0 : Summable (fun n : ℕ => @inner ℝ ℝ _ (F₀ n) (G₀ n)) := lp.summable_inner F₀ G₀
  apply tsum_eq_of_paired_involution (σ := σ)
  · exact hsumv
  · exact hsum0
  · intro m
    have hσ : σ m = Nat.pair (modePartner (Nat.unpair m).1) (Nat.unpair m).2 := by
      simp [σ, Nat.pairEquiv, modePartnerEquiv, Function.Involutive.toPerm,
        Equiv.prodCongrLeft, Function.uncurry]
    set a := (Nat.unpair m).1
    set b := (Nat.unpair m).2
    have hωf :
        DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) b
          (resolventMultiplierCLM (resolventFreq_pos L mass hmass (modePartner a)) f₂) =
        DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) b
          (resolventMultiplierCLM (resolventFreq_pos L mass hmass a) f₂) := by
      simp [a, resolventFreq_modePartner L mass a]
    have hωg :
        DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) b
          (resolventMultiplierCLM (resolventFreq_pos L mass hmass (modePartner a)) g₂) =
        DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) b
          (resolventMultiplierCLM (resolventFreq_pos L mass hmass a) g₂) := by
      simp [a, resolventFreq_modePartner L mass a]
    simp only [cylinderMassOperator_formula, hσ, a, b, ntpSliceSchwartz_pure, map_smul,
      Nat.unpair_pair]
    rw [hωf, hωg]
    have hcT1 := coeff_eq_fourierCoeffReal L a (circleTranslation L v f₁)
    have hcT2 := coeff_eq_fourierCoeffReal L a (circleTranslation L v g₁)
    have hcP1 := coeff_eq_fourierCoeffReal L (modePartner a) (circleTranslation L v f₁)
    have hcP2 := coeff_eq_fourierCoeffReal L (modePartner a) (circleTranslation L v g₁)
    have hc1 := coeff_eq_fourierCoeffReal L a f₁
    have hc2 := coeff_eq_fourierCoeffReal L a g₁
    have hcQ1 := coeff_eq_fourierCoeffReal L (modePartner a) f₁
    have hcQ2 := coeff_eq_fourierCoeffReal L (modePartner a) g₁
    rw [hcT1, hcT2, hcP1, hcP2, hc1, hc2, hcQ1, hcQ2]
    set c₂f := DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) b
      (resolventMultiplierCLM (resolventFreq_pos L mass hmass a) f₂)
    set c₂g := DyninMityaginSpace.coeff (E := SchwartzMap ℝ ℝ) b
      (resolventMultiplierCLM (resolventFreq_pos L mass hmass a) g₂)
    have hpaired := coeff_product_paired_translation L v f₁ g₁ a
    have hTI1 :
        @inner ℝ ℝ _ (SmoothMap_Circle.fourierCoeffReal a ((circleTranslation L v) f₁) • c₂f)
            (SmoothMap_Circle.fourierCoeffReal a ((circleTranslation L v) g₁) • c₂g) =
          (SmoothMap_Circle.fourierCoeffReal a ((circleTranslation L v) f₁) • c₂f) *
            (SmoothMap_Circle.fourierCoeffReal a ((circleTranslation L v) g₁) • c₂g) := by
      simpa [smul_eq_mul] using
        (RCLike.inner_apply'
          (SmoothMap_Circle.fourierCoeffReal a ((circleTranslation L v) f₁) • c₂f)
          (SmoothMap_Circle.fourierCoeffReal a ((circleTranslation L v) g₁) • c₂g))
    have hTI2 :
        @inner ℝ ℝ _
            (SmoothMap_Circle.fourierCoeffReal (modePartner a) ((circleTranslation L v) f₁) • c₂f)
            (SmoothMap_Circle.fourierCoeffReal (modePartner a) ((circleTranslation L v) g₁) • c₂g) =
          (SmoothMap_Circle.fourierCoeffReal (modePartner a) ((circleTranslation L v) f₁) • c₂f) *
            (SmoothMap_Circle.fourierCoeffReal (modePartner a) ((circleTranslation L v) g₁) • c₂g) := by
      simpa [smul_eq_mul] using
        (RCLike.inner_apply'
          (SmoothMap_Circle.fourierCoeffReal (modePartner a) ((circleTranslation L v) f₁) • c₂f)
          (SmoothMap_Circle.fourierCoeffReal (modePartner a) ((circleTranslation L v) g₁) • c₂g))
    have hI1 :
        @inner ℝ ℝ _ (SmoothMap_Circle.fourierCoeffReal a f₁ • c₂f)
            (SmoothMap_Circle.fourierCoeffReal a g₁ • c₂g) =
          (SmoothMap_Circle.fourierCoeffReal a f₁ • c₂f) *
            (SmoothMap_Circle.fourierCoeffReal a g₁ • c₂g) := by
      simpa [smul_eq_mul] using
        (RCLike.inner_apply'
          (SmoothMap_Circle.fourierCoeffReal a f₁ • c₂f)
          (SmoothMap_Circle.fourierCoeffReal a g₁ • c₂g))
    have hI2 :
        @inner ℝ ℝ _ (SmoothMap_Circle.fourierCoeffReal (modePartner a) f₁ • c₂f)
            (SmoothMap_Circle.fourierCoeffReal (modePartner a) g₁ • c₂g) =
          (SmoothMap_Circle.fourierCoeffReal (modePartner a) f₁ • c₂f) *
            (SmoothMap_Circle.fourierCoeffReal (modePartner a) g₁ • c₂g) := by
      simpa [smul_eq_mul] using
        (RCLike.inner_apply'
          (SmoothMap_Circle.fourierCoeffReal (modePartner a) f₁ • c₂f)
          (SmoothMap_Circle.fourierCoeffReal (modePartner a) g₁ • c₂g))
    rw [hTI1, hTI2, hI1, hI2]
    simp [smul_eq_mul] at *
    linear_combination c₂f * c₂g * hpaired

private theorem massInner_spatialTranslation_invariant
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ)
    (f g : CylinderTestFunction L) :
    massInnerBilinear L mass hmass
      (cylinderSpatialTranslation L v f)
      (cylinderSpatialTranslation L v g) =
    massInnerBilinear L mass hmass f g := by
  apply massInner_invariant_of_pure L mass hmass (cylinderSpatialTranslation L v)
  intro e₁ e₁' e₂ e₂'
  rw [cylinderSpatialTranslation, nuclearTensorProduct_mapCLM_pure,
    nuclearTensorProduct_mapCLM_pure]
  exact massInner_spatialTranslation_pure L mass hmass v e₁ e₁' e₂ e₂'

theorem cylinderMassOperator_spatialTranslation_normSq_eq_proved
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ) (f : CylinderTestFunction L) :
    ‖cylinderMassOperator L mass hmass (cylinderSpatialTranslation L v f)‖ ^ 2 =
      ‖cylinderMassOperator L mass hmass f‖ ^ 2 := by
  have h := massInner_spatialTranslation_invariant L mass hmass v f f
  simpa [massInnerBilinear, real_inner_self_eq_norm_sq] using h

theorem cylinderMassOperator_spatialTranslation_norm_eq_proved
    (mass : ℝ) (hmass : 0 < mass) (v : ℝ) (f : CylinderTestFunction L) :
    ‖cylinderMassOperator L mass hmass (cylinderSpatialTranslation L v f)‖ =
      ‖cylinderMassOperator L mass hmass f‖ := by
  have h_sq := cylinderMassOperator_spatialTranslation_normSq_eq_proved L mass hmass v f
  have hx : 0 ≤ ‖cylinderMassOperator L mass hmass (cylinderSpatialTranslation L v f)‖ :=
    norm_nonneg _
  have hy : 0 ≤ ‖cylinderMassOperator L mass hmass f‖ := norm_nonneg _
  nlinarith [sq_nonneg
    (‖cylinderMassOperator L mass hmass (cylinderSpatialTranslation L v f)‖ -
      ‖cylinderMassOperator L mass hmass f‖), h_sq]

end GaussianField

end
