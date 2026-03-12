/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cylinder Symmetry Actions: Reflection and Translation

Defines symmetry transformations on the cylinder test function space
`CylinderTestFunction L = C∞(S¹_L) ⊗̂ 𝓢(ℝ)` and their lifts to
configuration space.

## Main definitions

### Schwartz-level (temporal direction)
- `schwartzReflection` — `f ↦ f(-·)` on `𝓢(ℝ)`
- `schwartzTranslation τ` — `f ↦ f(· - τ)` on `𝓢(ℝ)`

### Cylinder-level (from nuclearTensorProduct_mapCLM)
- `cylinderTimeReflection` — `id ⊗ Θ` (time reflection t ↦ -t)
- `cylinderSpatialTranslation v` — `T_v ⊗ id` (spatial translation)
- `cylinderTimeTranslation τ` — `id ⊗ T_τ` (time translation)
- `cylinderTranslation v τ` — `T_v ⊗ T_τ` (full translation)

### Configuration-level
- `cylinderConfigReflection` — precomposition with `cylinderTimeReflection`
- `cylinderConfigTranslation` — precomposition with `cylinderTranslation`

## Mathematical background

The cylinder S¹_L × ℝ has:
- Spatial translation S¹_L acting by shift on the first factor
- Time translation ℝ acting by shift on the second factor
- Time reflection t ↦ -t for OS axiom OS3

The key advantage over the torus: time reflection maps (0,∞) to (-∞,0),
giving a clean decomposition into future and past. No wraparound issues.

## References

- Trèves, *Topological Vector Spaces, Distributions, and Kernels*, Ch. 50
- Glimm-Jaffe, *Quantum Physics*, §6.4
- Osterwalder-Schrader (1973), Axiom (A3)
-/

import Cylinder.Basic
import Torus.Symmetry
import Nuclear.TensorProductFunctorAxioms

noncomputable section

namespace GaussianField

open NuclearTensorProduct SmoothMap_Circle

variable (L : ℝ) [hL : Fact (0 < L)]

/-! ## Schwartz-level symmetry actions

Reflection and translation on Schwartz space 𝓢(ℝ). These use Mathlib's
`SchwartzMap.compCLMOfContinuousLinearEquiv` (for reflection via
`LinearIsometryEquiv.neg`) and `SchwartzMap.compSubConstCLM` (for
translation by a constant). -/

/-- Reflection on Schwartz space: `(Θf)(t) = f(-t)`.

Defined via `compCLMOfContinuousLinearEquiv` applied to the negation
linear isometry equivalence. Preserves all Schwartz seminorms since
negation is a linear isometry. -/
def schwartzReflection : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv

/-- Pointwise evaluation of Schwartz reflection. -/
@[simp]
theorem schwartzReflection_apply (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    schwartzReflection f x = f (-x) := rfl

/-- Schwartz reflection is an involution: Θ² = id. -/
theorem schwartzReflection_involution :
    schwartzReflection.comp schwartzReflection =
    ContinuousLinearMap.id ℝ (SchwartzMap ℝ ℝ) := by
  ext f x
  simp [schwartzReflection]

/-- Time translation on Schwartz space: `(T_τ f)(t) = f(t - τ)`.

Defined via `SchwartzMap.compSubConstCLM`, which handles the decay
bounds automatically using the antilipschitz property of translation. -/
def schwartzTranslation (τ : ℝ) : SchwartzMap ℝ ℝ →L[ℝ] SchwartzMap ℝ ℝ :=
  SchwartzMap.compSubConstCLM ℝ τ

/-- Pointwise evaluation of Schwartz translation. -/
@[simp]
theorem schwartzTranslation_apply (τ : ℝ) (f : SchwartzMap ℝ ℝ) (x : ℝ) :
    schwartzTranslation τ f x = f (x - τ) := rfl

/-- Translation by zero is the identity. -/
theorem schwartzTranslation_zero :
    schwartzTranslation 0 = ContinuousLinearMap.id ℝ (SchwartzMap ℝ ℝ) :=
  SchwartzMap.compSubConstCLM_zero

/-- Translation is additive: T_{σ+τ} = T_τ ∘ T_σ. -/
theorem schwartzTranslation_add (σ τ : ℝ) :
    (schwartzTranslation τ).comp (schwartzTranslation σ) =
    schwartzTranslation (σ + τ) := by
  ext f x
  simp [schwartzTranslation, add_comm σ τ]

/-! ## Cylinder-level symmetry actions -/

/-- Time reflection on the cylinder: `(id ⊗ Θ)(f₁ ⊗ f₂)(x,t) = f₁(x) ⊗ f₂(-t)`.

This is the Osterwalder-Schrader time reflection, acting on the second
(temporal) factor of `CylinderTestFunction L = C∞(S¹_L) ⊗̂ 𝓢(ℝ)`.

Note: Unlike the torus where time reflection acts on the first factor,
here we use the convention that the first factor is spatial (S¹) and
the second is temporal (ℝ). Time reflection acts on the temporal factor. -/
def cylinderTimeReflection :
    CylinderTestFunction L →L[ℝ] CylinderTestFunction L :=
  nuclearTensorProduct_mapCLM
    (ContinuousLinearMap.id ℝ (SmoothMap_Circle L ℝ))
    schwartzReflection

/-- Spatial translation on the cylinder: `(T_v ⊗ id)(f)(x,t) = f(x - v, t)`.

Translates in the periodic spatial direction S¹_L. -/
def cylinderSpatialTranslation (v : ℝ) :
    CylinderTestFunction L →L[ℝ] CylinderTestFunction L :=
  nuclearTensorProduct_mapCLM
    (circleTranslation L v)
    (ContinuousLinearMap.id ℝ (SchwartzMap ℝ ℝ))

/-- Time translation on the cylinder: `(id ⊗ T_τ)(f)(x,t) = f(x, t - τ)`.

Translates in the non-compact temporal direction ℝ. -/
def cylinderTimeTranslation (τ : ℝ) :
    CylinderTestFunction L →L[ℝ] CylinderTestFunction L :=
  nuclearTensorProduct_mapCLM
    (ContinuousLinearMap.id ℝ (SmoothMap_Circle L ℝ))
    (schwartzTranslation τ)

/-- Full translation on the cylinder: `(T_v ⊗ T_τ)(f)(x,t) = f(x - v, t - τ)`.

The cylinder S¹_L × ℝ has translation group S¹_L × ℝ. -/
def cylinderTranslation (v : ℝ) (τ : ℝ) :
    CylinderTestFunction L →L[ℝ] CylinderTestFunction L :=
  nuclearTensorProduct_mapCLM
    (circleTranslation L v)
    (schwartzTranslation τ)

/-- Time reflection is an involution: Θ² = id on the cylinder. -/
theorem cylinderTimeReflection_involution :
    (cylinderTimeReflection L).comp (cylinderTimeReflection L) =
    ContinuousLinearMap.id ℝ _ := by
  unfold cylinderTimeReflection
  rw [← nuclearTensorProduct_mapCLM_comp, ContinuousLinearMap.id_comp,
      schwartzReflection_involution]
  exact nuclearTensorProduct_mapCLM_id

/-! ## Configuration-level actions

Configuration = WeakDual ℝ (CylinderTestFunction L) = E →L[ℝ] ℝ with weak-* topology.
Symmetry actions on test functions induce dual actions on configurations
by precomposition: `(T_* ω)(f) = ω(T f)`. -/

/-- Time reflection on configurations: `(Θ_* ω)(f) = ω(Θ f)`. -/
def cylinderConfigReflection :
    Configuration (CylinderTestFunction L) → Configuration (CylinderTestFunction L) :=
  fun ω => (ω : CylinderTestFunction L →L[ℝ] ℝ).comp (cylinderTimeReflection L)

/-- Spatial translation on configurations: `(T_{v,*} ω)(f) = ω(T_v f)`. -/
def cylinderConfigSpatialTranslation (v : ℝ) :
    Configuration (CylinderTestFunction L) → Configuration (CylinderTestFunction L) :=
  fun ω => (ω : CylinderTestFunction L →L[ℝ] ℝ).comp (cylinderSpatialTranslation L v)

/-- Time translation on configurations: `(T_{τ,*} ω)(f) = ω(T_τ f)`. -/
def cylinderConfigTimeTranslation (τ : ℝ) :
    Configuration (CylinderTestFunction L) → Configuration (CylinderTestFunction L) :=
  fun ω => (ω : CylinderTestFunction L →L[ℝ] ℝ).comp (cylinderTimeTranslation L τ)

/-- Full translation on configurations. -/
def cylinderConfigTranslation (v : ℝ) (τ : ℝ) :
    Configuration (CylinderTestFunction L) → Configuration (CylinderTestFunction L) :=
  fun ω => (ω : CylinderTestFunction L →L[ℝ] ℝ).comp (cylinderTranslation L v τ)

/-- Time reflection on configurations is continuous. -/
theorem cylinderConfigReflection_continuous :
    Continuous (cylinderConfigReflection L) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  exact WeakDual.eval_continuous (cylinderTimeReflection L f)

/-- Spatial translation on configurations is continuous. -/
theorem cylinderConfigSpatialTranslation_continuous (v : ℝ) :
    Continuous (cylinderConfigSpatialTranslation L v) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  exact WeakDual.eval_continuous (cylinderSpatialTranslation L v f)

/-- Time translation on configurations is continuous. -/
theorem cylinderConfigTimeTranslation_continuous (τ : ℝ) :
    Continuous (cylinderConfigTimeTranslation L τ) := by
  apply WeakDual.continuous_of_continuous_eval
  intro f
  exact WeakDual.eval_continuous (cylinderTimeTranslation L τ f)

/-- Time reflection on configurations is an involution. -/
theorem cylinderConfigReflection_involution (ω : Configuration (CylinderTestFunction L)) :
    cylinderConfigReflection L (cylinderConfigReflection L ω) = ω := by
  apply ContinuousLinearMap.ext
  intro f
  simp only [cylinderConfigReflection, ContinuousLinearMap.comp_apply]
  congr 1
  exact ContinuousLinearMap.ext_iff.mp (cylinderTimeReflection_involution L) f

end GaussianField
