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

/-! ## Positive-time Schwartz submodule (1D)

The submodule of Schwartz functions on ℝ that vanish on (-∞, 0].
This is the temporal component of the Osterwalder-Schrader positive-time
condition: test functions supported in the future half-line (0, ∞). -/

/-- Submodule of Schwartz functions vanishing on (-∞, 0].

Mathematically, these are the Schwartz functions with support in (0, ∞).
The condition `∀ x ≤ 0, f x = 0` is equivalent to
`Function.support f ⊆ Set.Ioi 0`. -/
def schwartzPositiveTimeSubmodule : Submodule ℝ (SchwartzMap ℝ ℝ) where
  carrier := {f | ∀ x ≤ 0, f x = 0}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun {f g} hf hg x hx => by simp [hf x hx, hg x hx]
  smul_mem' := fun r f hf x hx => by simp [hf x hx]

/-- If f vanishes on (-∞, 0], then Θf vanishes on [0, ∞). -/
theorem schwartzReflection_positive_to_negative
    {f : SchwartzMap ℝ ℝ} (hf : f ∈ schwartzPositiveTimeSubmodule) :
    ∀ x, 0 ≤ x → schwartzReflection f x = 0 := by
  intro x hx
  simp [hf (-x) (by linarith)]

/-- Positive-time and reflected positive-time are disjoint (except 0).

If f vanishes on (-∞, 0] and Θf also vanishes on (-∞, 0], then
f must vanish everywhere: the first condition kills f on (-∞, 0]
and the second kills f on [0, ∞) (since (Θf)(x) = f(-x) = 0 for x ≤ 0
means f(y) = 0 for y ≥ 0). -/
theorem schwartzPositiveTime_disjoint_reflected
    {f : SchwartzMap ℝ ℝ} (hf : f ∈ schwartzPositiveTimeSubmodule)
    (hne : f ≠ 0) :
    schwartzReflection f ∉ schwartzPositiveTimeSubmodule := by
  intro hΘf
  apply hne
  ext x
  simp only [SchwartzMap.zero_apply]
  by_cases hx : x ≤ 0
  · exact hf x hx
  · push Not at hx
    have h : schwartzReflection f (-x) = 0 := hΘf (-x) (by linarith)
    simpa using h

/-- Time translation by τ > 0 preserves positive-time support.

If f vanishes on (-∞, 0] and τ > 0, then (T_τ f)(x) = f(x - τ).
For x ≤ 0: x - τ < 0, so f(x - τ) = 0. -/
theorem schwartzTranslation_preserves_positiveTime
    {f : SchwartzMap ℝ ℝ} (hf : f ∈ schwartzPositiveTimeSubmodule)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    schwartzTranslation τ f ∈ schwartzPositiveTimeSubmodule := by
  intro x hx
  simp [hf (x - τ) (by linarith)]

/-! ## Schwartz evaluation CLM -/

/-- Point evaluation at t is a CLM on Schwartz space.
Bounded by the (0,0)-seminorm: |f(t)| ≤ seminorm 0 0 f. -/
noncomputable def schwartzEvalCLM (t : ℝ) : SchwartzMap ℝ ℝ →L[ℝ] ℝ :=
  SchwartzMap.mkCLMtoNormedSpace (fun f => f t)
    (fun f g => by simp [SchwartzMap.add_apply])
    (fun a f => by simp [SchwartzMap.smul_apply])
    ⟨{(0, 0)}, 1, zero_le_one, fun f => by
      simp only [one_mul, Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply]
      exact SchwartzMap.norm_le_seminorm ℝ f t⟩

@[simp]
theorem schwartzEvalCLM_apply (t : ℝ) (f : SchwartzMap ℝ ℝ) :
    schwartzEvalCLM t f = f t := by
  simp [schwartzEvalCLM, SchwartzMap.mkCLMtoNormedSpace]

/-- Submodule of Schwartz functions vanishing on [0, ∞).
Mirror of `schwartzPositiveTimeSubmodule`: these have support in (-∞, 0). -/
def schwartzNegativeTimeSubmodule : Submodule ℝ (SchwartzMap ℝ ℝ) where
  carrier := {f | ∀ x, 0 ≤ x → f x = 0}
  zero_mem' := fun _ _ => by simp
  add_mem' := fun {f g} hf hg x hx => by simp [hf x hx, hg x hx]
  smul_mem' := fun r f hf x hx => by simp [hf x hx]

/-- The positive-time Schwartz submodule is topologically closed.
Follows from pointwise evaluation being continuous: if f_n → f in the
Schwartz topology and each f_n(x) = 0 for x ≤ 0, then f(x) = 0. -/
theorem schwartzPositiveTimeSubmodule_isClosed :
    IsClosed (schwartzPositiveTimeSubmodule : Set (SchwartzMap ℝ ℝ)) := by
  have : (schwartzPositiveTimeSubmodule : Set (SchwartzMap ℝ ℝ)) =
      ⋂ (x : ℝ) (_ : x ≤ 0), {f | f x = 0} := by
    ext f; simp [schwartzPositiveTimeSubmodule, Set.mem_iInter]
  rw [this]
  apply isClosed_iInter; intro x
  apply isClosed_iInter; intro _
  exact isClosed_eq (schwartzEvalCLM x).continuous continuous_const

/-- The negative-time Schwartz submodule is topologically closed. -/
theorem schwartzNegativeTimeSubmodule_isClosed :
    IsClosed (schwartzNegativeTimeSubmodule : Set (SchwartzMap ℝ ℝ)) := by
  have : (schwartzNegativeTimeSubmodule : Set (SchwartzMap ℝ ℝ)) =
      ⋂ (x : ℝ) (_ : 0 ≤ x), {f | f x = 0} := by
    ext f; simp [schwartzNegativeTimeSubmodule, Set.mem_iInter]
  rw [this]
  apply isClosed_iInter; intro x
  apply isClosed_iInter; intro _
  exact isClosed_eq (schwartzEvalCLM x).continuous continuous_const

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
