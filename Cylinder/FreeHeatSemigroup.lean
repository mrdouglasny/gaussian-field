/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder Heat Semigroup and Equivariance

Defines the cylinder heat semigroup `e^{-t(-Δ_{S¹} - d²/dt² + m²)}` on
`CylinderTestFunction L = C∞(S¹_L) ⊗̂ 𝓢(ℝ)` and proves it commutes with
spatial translation, time translation, and time reflection.

## Main definitions

- `cylinderHeatSemigroup` — `e^{-t(-Δ_{S¹} - d²/dt² + m²)}` on `C∞(S¹_L) ⊗̂ 𝓢(ℝ)`

## Main results

- `cylinderHeatSemigroup_spatialTranslation_comm` — commutes with spatial translation
- `cylinderHeatSemigroup_timeTranslation_comm` — commutes with time translation
- `cylinderHeatSemigroup_timeReflection_comm` — commutes with time reflection

## Mathematical background

The cylinder heat semigroup factors as a tensor product:

  `e^{-t(-Δ_{S¹} + Δ_ℝ + m²)} = e^{-m²t} · e^{-tΔ_{S¹}} ⊗ e^{-tΔ_ℝ}`

The circle factor `e^{-tΔ_{S¹}}` uses the proved `circleHeatSemigroup` from
`SmoothCircle.HeatSemigroup`. The temporal factor `e^{-tΔ_ℝ}` is the
Fourier multiplier `freeHeatSemigroup` from `Cylinder.FourierMultiplier`.

Equivariance of each factor is combined via functoriality of the nuclear
tensor product (`nuclearTensorProduct_mapCLM_comp`).

## References

- Reed-Simon, *Methods of Modern Mathematical Physics* Vol. II, §X.12
- Evans, *Partial Differential Equations*, §2.3
-/

import Cylinder.FourierMultiplier
import SmoothCircle.HeatEquivariance

noncomputable section

namespace GaussianField

open NuclearTensorProduct SmoothMap_Circle

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Cylinder heat semigroup

The cylinder operator `-Δ_{S¹} - d²/dt² + m²` decomposes as a sum of
commuting operators on the two factors plus a scalar. The heat semigroup
therefore factors:

  `e^{-t(-Δ_{S¹} - d²/dt² + m²)} = e^{-m²t} · e^{-tΔ_{S¹}} ⊗ e^{-tΔ_ℝ}` -/

/-- **The cylinder heat semigroup** on `CylinderTestFunction L = C∞(S¹_L) ⊗̂ 𝓢(ℝ)`.

  `e^{-t(-Δ_{S¹} - d²/dt² + m²)} = e^{-m²t} · (e^{-tΔ_{S¹}} ⊗ e^{-tΔ_ℝ})`

Defined as the tensor product of the circle and free heat semigroups,
scaled by the mass exponential factor. -/
def cylinderHeatSemigroup {t : ℝ} (ht : 0 ≤ t) (mass : ℝ) :
    CylinderTestFunction L →L[ℝ] CylinderTestFunction L :=
  Real.exp (-mass ^ 2 * t) •
    nuclearTensorProduct_mapCLM (circleHeatSemigroup L ht) (freeHeatSemigroup ht)

/-! ### Equivariance of the cylinder heat semigroup

Each equivariance proof follows the same pattern:

1. Unfold the cylinder heat semigroup as `exp(-m²t) • mapCLM(circleHeat, freeHeat)`
2. Unfold the symmetry as `mapCLM(circleSymm, schwartzSymm)`
3. Use `mapCLM_comp` to compose: `mapCLM(A,B) ∘ mapCLM(C,D) = mapCLM(A∘C, B∘D)`
4. Use the component equivariance to swap: `A∘C = C∘A`
5. Factor back with `mapCLM_comp` -/

/-- The cylinder heat semigroup commutes with spatial translation.

  `e^{-tA}(T_v ⊗ id)(f) = (T_v ⊗ id)(e^{-tA} f)`

Proof: Spatial translation acts only on the circle factor, where
`circleHeatSemigroup_translation_comm` provides the commutation.
The free heat semigroup composes with `id` trivially. -/
theorem cylinderHeatSemigroup_spatialTranslation_comm {t : ℝ} (ht : 0 ≤ t)
    (mass : ℝ) (v : ℝ) (f : CylinderTestFunction L) :
    cylinderHeatSemigroup L ht mass (cylinderSpatialTranslation L v f) =
    cylinderSpatialTranslation L v (cylinderHeatSemigroup L ht mass f) := by
  simp only [cylinderHeatSemigroup, cylinderSpatialTranslation,
    ContinuousLinearMap.smul_apply, map_smul]
  congr 1
  have h_comp1 : (nuclearTensorProduct_mapCLM (circleHeatSemigroup L ht)
      (freeHeatSemigroup ht)).comp
      (nuclearTensorProduct_mapCLM (circleTranslation L v)
        (ContinuousLinearMap.id ℝ (SchwartzMap ℝ ℝ))) =
    nuclearTensorProduct_mapCLM
      ((circleHeatSemigroup L ht).comp (circleTranslation L v))
      ((freeHeatSemigroup ht).comp (ContinuousLinearMap.id ℝ _)) :=
    (nuclearTensorProduct_mapCLM_comp _ _ _ _).symm
  have h_comp2 : (nuclearTensorProduct_mapCLM (circleTranslation L v)
      (ContinuousLinearMap.id ℝ (SchwartzMap ℝ ℝ))).comp
      (nuclearTensorProduct_mapCLM (circleHeatSemigroup L ht)
        (freeHeatSemigroup ht)) =
    nuclearTensorProduct_mapCLM
      ((circleTranslation L v).comp (circleHeatSemigroup L ht))
      ((ContinuousLinearMap.id ℝ _).comp (freeHeatSemigroup ht)) :=
    (nuclearTensorProduct_mapCLM_comp _ _ _ _).symm
  have h_circle : (circleHeatSemigroup L ht).comp (circleTranslation L v) =
      (circleTranslation L v).comp (circleHeatSemigroup L ht) :=
    ContinuousLinearMap.ext (circleHeatSemigroup_translation_comm L ht v)
  have h_free : (freeHeatSemigroup ht).comp (ContinuousLinearMap.id ℝ _) =
      (ContinuousLinearMap.id ℝ _).comp (freeHeatSemigroup ht) := by
    simp [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
  rw [show nuclearTensorProduct_mapCLM (circleHeatSemigroup L ht)
        (freeHeatSemigroup ht)
      (nuclearTensorProduct_mapCLM (circleTranslation L v)
        (ContinuousLinearMap.id ℝ _) f) =
    ((nuclearTensorProduct_mapCLM (circleHeatSemigroup L ht)
        (freeHeatSemigroup ht)).comp
      (nuclearTensorProduct_mapCLM (circleTranslation L v)
        (ContinuousLinearMap.id ℝ _))) f from rfl]
  rw [h_comp1, h_circle, h_free, ← h_comp2]
  rfl

/-- The cylinder heat semigroup commutes with time translation.

  `e^{-tA}(id ⊗ T_τ)(f) = (id ⊗ T_τ)(e^{-tA} f)`

Proof: Time translation acts only on the Schwartz factor, where
`freeHeatSemigroup_translation_comm` provides the commutation.
The circle heat semigroup composes with `id` trivially. -/
theorem cylinderHeatSemigroup_timeTranslation_comm {t : ℝ} (ht : 0 ≤ t)
    (mass : ℝ) (τ : ℝ) (f : CylinderTestFunction L) :
    cylinderHeatSemigroup L ht mass (cylinderTimeTranslation L τ f) =
    cylinderTimeTranslation L τ (cylinderHeatSemigroup L ht mass f) := by
  simp only [cylinderHeatSemigroup, cylinderTimeTranslation,
    ContinuousLinearMap.smul_apply, map_smul]
  congr 1
  have h_comp1 : (nuclearTensorProduct_mapCLM (circleHeatSemigroup L ht)
      (freeHeatSemigroup ht)).comp
      (nuclearTensorProduct_mapCLM (ContinuousLinearMap.id ℝ (SmoothMap_Circle L ℝ))
        (schwartzTranslation τ)) =
    nuclearTensorProduct_mapCLM
      ((circleHeatSemigroup L ht).comp (ContinuousLinearMap.id ℝ _))
      ((freeHeatSemigroup ht).comp (schwartzTranslation τ)) :=
    (nuclearTensorProduct_mapCLM_comp _ _ _ _).symm
  have h_comp2 : (nuclearTensorProduct_mapCLM (ContinuousLinearMap.id ℝ (SmoothMap_Circle L ℝ))
      (schwartzTranslation τ)).comp
      (nuclearTensorProduct_mapCLM (circleHeatSemigroup L ht)
        (freeHeatSemigroup ht)) =
    nuclearTensorProduct_mapCLM
      ((ContinuousLinearMap.id ℝ _).comp (circleHeatSemigroup L ht))
      ((schwartzTranslation τ).comp (freeHeatSemigroup ht)) :=
    (nuclearTensorProduct_mapCLM_comp _ _ _ _).symm
  have h_circle : (circleHeatSemigroup L ht).comp (ContinuousLinearMap.id ℝ _) =
      (ContinuousLinearMap.id ℝ _).comp (circleHeatSemigroup L ht) := by
    simp [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
  have h_free : (freeHeatSemigroup ht).comp (schwartzTranslation τ) =
      (schwartzTranslation τ).comp (freeHeatSemigroup ht) :=
    ContinuousLinearMap.ext (freeHeatSemigroup_translation_comm ht τ)
  rw [show nuclearTensorProduct_mapCLM (circleHeatSemigroup L ht)
        (freeHeatSemigroup ht)
      (nuclearTensorProduct_mapCLM (ContinuousLinearMap.id ℝ _)
        (schwartzTranslation τ) f) =
    ((nuclearTensorProduct_mapCLM (circleHeatSemigroup L ht)
        (freeHeatSemigroup ht)).comp
      (nuclearTensorProduct_mapCLM (ContinuousLinearMap.id ℝ _)
        (schwartzTranslation τ))) f from rfl]
  rw [h_comp1, h_circle, h_free, ← h_comp2]
  rfl

/-- The cylinder heat semigroup commutes with time reflection.

  `e^{-tA}(id ⊗ Θ)(f) = (id ⊗ Θ)(e^{-tA} f)`

Proof: Time reflection acts only on the Schwartz factor, where
`freeHeatSemigroup_reflection_comm` provides the commutation. -/
theorem cylinderHeatSemigroup_timeReflection_comm {t : ℝ} (ht : 0 ≤ t)
    (mass : ℝ) (f : CylinderTestFunction L) :
    cylinderHeatSemigroup L ht mass (cylinderTimeReflection L f) =
    cylinderTimeReflection L (cylinderHeatSemigroup L ht mass f) := by
  simp only [cylinderHeatSemigroup, cylinderTimeReflection,
    ContinuousLinearMap.smul_apply, map_smul]
  congr 1
  have h_comp1 : (nuclearTensorProduct_mapCLM (circleHeatSemigroup L ht)
      (freeHeatSemigroup ht)).comp
      (nuclearTensorProduct_mapCLM (ContinuousLinearMap.id ℝ (SmoothMap_Circle L ℝ))
        schwartzReflection) =
    nuclearTensorProduct_mapCLM
      ((circleHeatSemigroup L ht).comp (ContinuousLinearMap.id ℝ _))
      ((freeHeatSemigroup ht).comp schwartzReflection) :=
    (nuclearTensorProduct_mapCLM_comp _ _ _ _).symm
  have h_comp2 : (nuclearTensorProduct_mapCLM (ContinuousLinearMap.id ℝ (SmoothMap_Circle L ℝ))
      schwartzReflection).comp
      (nuclearTensorProduct_mapCLM (circleHeatSemigroup L ht)
        (freeHeatSemigroup ht)) =
    nuclearTensorProduct_mapCLM
      ((ContinuousLinearMap.id ℝ _).comp (circleHeatSemigroup L ht))
      (schwartzReflection.comp (freeHeatSemigroup ht)) :=
    (nuclearTensorProduct_mapCLM_comp _ _ _ _).symm
  have h_circle : (circleHeatSemigroup L ht).comp (ContinuousLinearMap.id ℝ _) =
      (ContinuousLinearMap.id ℝ _).comp (circleHeatSemigroup L ht) := by
    simp [ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
  have h_free : (freeHeatSemigroup ht).comp schwartzReflection =
      schwartzReflection.comp (freeHeatSemigroup ht) :=
    ContinuousLinearMap.ext (freeHeatSemigroup_reflection_comm ht)
  rw [show nuclearTensorProduct_mapCLM (circleHeatSemigroup L ht)
        (freeHeatSemigroup ht)
      (nuclearTensorProduct_mapCLM (ContinuousLinearMap.id ℝ _)
        schwartzReflection f) =
    ((nuclearTensorProduct_mapCLM (circleHeatSemigroup L ht)
        (freeHeatSemigroup ht)).comp
      (nuclearTensorProduct_mapCLM (ContinuousLinearMap.id ℝ _)
        schwartzReflection)) f from rfl]
  rw [h_comp1, h_circle, h_free, ← h_comp2]
  rfl

end GaussianField
