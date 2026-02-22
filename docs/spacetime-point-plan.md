# Spacetime Point Types and Manifold Connection

## Context

The heat kernel on the cylinder currently takes separated coordinates
`θ₁ x₁ θ₂ x₂ : ℝ`, making signatures long and error-prone. We want to:

1. Bundle coordinates into a single point type
2. Connect to Mathlib's manifold infrastructure where possible
3. Set up the right architecture for tensor products on manifolds

## Key constraint: why we can't use Mathlib manifolds for test functions

Mathlib's `ContMDiffMap` (smooth maps on manifolds) has algebraic structure
(module, ring) but **no Fréchet space topology**. Our `DyninMityaginSpace`
typeclass requires Fréchet seminorms. So we cannot build `DyninMityaginSpace`
on Mathlib's smooth map spaces.

Also: `AddCircle L` has no manifold instance in current Mathlib (only the
complex `Circle` does). And `SmoothMap_Circle` uses `ContDiff ℝ ⊤` on ℝ,
not `ContMDiff` on `AddCircle`.

**Conclusion**: connecting to Mathlib manifolds is the right long-term goal,
but premature for the test function space. We CAN introduce a point type
for the domain (where test functions are evaluated).

## Design: thin `CylinderPoint` wrapper

### New file: `HeatKernel/CylinderPoint.lean`

```lean
/-- A point on the cylinder S¹_L × ℝ.
    The angular coordinate θ is real-valued (understood modulo L). -/
structure CylinderPoint (L : ℝ) where
  θ : ℝ
  x : ℝ

namespace CylinderPoint
def shiftTheta (p : CylinderPoint L) (d : ℝ) : CylinderPoint L :=
  ⟨p.θ + d, p.x⟩

noncomputable def toAddCircleProd (p : CylinderPoint L) : AddCircle L × ℝ :=
  (QuotientAddGroup.mk p.θ, p.x)
end CylinderPoint
```

### Refactor `HeatKernel/PositionKernel.lean`

| Before | After |
|--------|-------|
| `cylinderHeatKernel L mass t θ₁ x₁ θ₂ x₂` | `cylinderHeatKernel L mass t p₁ p₂` |
| `cylinderEval L f θ x` | `cylinderEval L f p` |
| `cylinderHeatKernel_symmetric ... θ₁ x₁ θ₂ x₂` | `cylinderHeatKernel_symmetric ... p₁ p₂` |
| `cylinderHeatKernel_periodic₁` + `_periodic₂` | `cylinderHeatKernel_periodic₁ ... (p₁.shiftTheta L) p₂` |

Bodies access `p.θ` and `p.x`. No proof logic changes.

### Update `Test.lean`

Position kernel tests use `CylinderPoint.mk` or anonymous constructors.

## What NOT to do

- **Don't** make `SmoothMap_Circle` use `AddCircle L` as domain (all calculus is on ℝ)
- **Don't** add `ChartedSpace`/`IsManifold` to `CylinderPoint` (it's a coordinate bundle, not a manifold)
- **Don't** add a `TestFunctionSpace M E` typeclass yet (only 3 instances, premature)
- **Don't** try to build `DyninMityaginSpace` on `ContMDiffMap` (Mathlib gap)

## Future extensibility

- **Torus**: `CylinderPoint L₁ × CylinderPoint L₂` or dedicated `TorusPoint`
- **ℝⁿ**: Point type is `EuclideanSpace ℝ (Fin n)` (already in Mathlib)
- **Manifold connection**: When Mathlib adds Fréchet topology to `C^∞⟮I, M; 𝕜⟩`,
  replace `CylinderPoint L` with `AddCircle L × ℝ` with manifold structure
- **`TestFunctionSpace` typeclass**: Add when we have ≥4 concrete instances and
  see the common API pattern

## Files to modify

| File | Change |
|------|--------|
| `HeatKernel/CylinderPoint.lean` | **New**: point type + helpers |
| `HeatKernel/PositionKernel.lean` | Refactor signatures to use `CylinderPoint` |
| `HeatKernel.lean` | Add `import HeatKernel.CylinderPoint` |
| `Test.lean` | Update position kernel tests |

## Verification

`lake build Test` — all files compile, zero errors.
