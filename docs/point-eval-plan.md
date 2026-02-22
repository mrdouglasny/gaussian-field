# Test Function Spaces with Point Evaluation

## Context

Every test function space in our project has an underlying domain where functions
are evaluated. Currently this is implicit — `SchwartzMap` and `SmoothMap_Circle`
have `FunLike` instances, but `NuclearTensorProduct` (used for Cylinder, Torus,
etc.) has no evaluation at all. The heat kernel takes separated coordinates
`θ₁ x₁ θ₂ x₂ : ℝ` instead of points.

We want a unified framework that:
1. Associates a **point type M** with each test function space E
2. Provides **pointwise evaluation** `E → M → ℝ` for all spaces
3. Handles **tensor products**: if E₁ has points M₁ and E₂ has points M₂,
   then E₁ ⊗̂ E₂ has points M₁ × M₂
4. Covers all our examples: Schwartz on ℝᵈ, S¹_L, Cylinder, Torus, lattices

## Inventory of test function spaces

| Space E | Domain M | Basis | Eval exists? |
|---------|----------|-------|-------------|
| `SchwartzMap ℝ ℝ` | `ℝ` | Hermite functions | Yes (FunLike) |
| `SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ` | `EuclideanSpace ℝ (Fin d)` | Tensor Hermite | Yes (FunLike) |
| `SmoothMap_Circle L ℝ` | `ℝ` | Fourier basis | Yes (FunLike) |
| `NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ ℝ)` (Cylinder) | `ℝ × ℝ` | Fourier ⊗ Hermite | **No** (only ad-hoc `cylinderEval` axiom) |
| `NuclearTensorProduct (SmoothMap_Circle L₁ ℝ) (SmoothMap_Circle L₂ ℝ)` (Torus) | `ℝ × ℝ` | Fourier ⊗ Fourier | **No** |
| `NuclearTensorProduct (SchwartzMap ℝ ℝ) (SchwartzMap ℝ ℝ)` | `ℝ × ℝ` | Hermite ⊗ Hermite | **No** |
| OSforGFF `TestFunction` = `SchwartzMap SpaceTime ℝ` | `SpaceTime` (= ℝ⁴) | Hermite (4D) | Yes (FunLike) |
| `Fin N → ℝ` (lattice) | `Fin N` | Standard basis | Yes |

## Mathlib status

- `ContMDiffMap` (`C^∞⟮I, M; 𝕜⟩`): has module/algebra structure but **no Fréchet
  topology** — cannot build `DyninMityaginSpace` on it
- `AddCircle L`: no manifold instance (only complex `Circle` has one)
- `SchwartzMap`: Fréchet space with seminorms, but domain must be a normed space

**Conclusion**: we define our own lightweight typeclass rather than depending
on Mathlib's manifold infrastructure.

## Design: `HasPointEval` typeclass

### New file: `Nuclear/PointEval.lean`

```lean
/-- Associates a point type M with a test function space E,
    together with pointwise evaluation. -/
class HasPointEval (E : Type*) (M : outParam Type*) where
  pointEval : E → M → ℝ
```

The `outParam` on M means Lean infers M from E automatically.

### Instances for base spaces

Evaluation is just function application via existing `FunLike`:

```lean
instance : HasPointEval (SchwartzMap D ℝ) D where
  pointEval f p := f p

instance : HasPointEval (SmoothMap_Circle L ℝ) ℝ where
  pointEval f p := f p
```

### Instance for tensor products

The tensor product evaluation uses the **factor space bases**:

```
f(p₁, p₂) = Σ_m coeff_m(f) · eval₁(basis₁(m.unpair.1), p₁) · eval₂(basis₂(m.unpair.2), p₂)
```

where `basis₁`, `basis₂` come from `DyninMityaginSpace` instances on the
factors, and `eval₁`, `eval₂` come from `HasPointEval` instances.

```lean
instance [DyninMityaginSpace E₁] [DyninMityaginSpace E₂]
    [HasPointEval E₁ M₁] [HasPointEval E₂ M₂] :
    HasPointEval (NuclearTensorProduct E₁ E₂) (M₁ × M₂) where
  pointEval f p :=
    ∑' (m : ℕ), DyninMityaginSpace.coeff m f *
      HasPointEval.pointEval (DyninMityaginSpace.basis (m.unpair).1 : E₁) p.1 *
      HasPointEval.pointEval (DyninMityaginSpace.basis (m.unpair).2 : E₂) p.2
```

Note: `DyninMityaginSpace.coeff` here is the coefficient functional of the
tensor product (which is `RapidDecaySeq`), while `DyninMityaginSpace.basis`
of E₁ and E₂ are the factor space bases. The Cantor pairing `m.unpair`
decodes the single index to a pair of factor indices.

### Convergence

The tsum in the tensor product instance needs convergence. Options:
- Axiomatize it (consistent with our axiom-first approach)
- Prove it from coefficient decay × basis growth (the math works)

### What this gives us

1. **Unified evaluation**: `HasPointEval.pointEval f p` works for ALL spaces
2. **Automatic tensor products**: Cylinder, Torus, SchwartzProduct get eval for free
3. **Heat kernel signatures**: `cylinderHeatKernel L mass t p₁ p₂` with `p : ℝ × ℝ`
4. **OSforGFF compatibility**: `SchwartzMap SpaceTime ℝ` gets `HasPointEval _ SpaceTime`
5. **Lattices**: `Fin N → ℝ` gets `HasPointEval _ (Fin N)` trivially

### Refactor existing code

The ad-hoc `cylinderEval` becomes a special case:
```lean
theorem cylinderEval_eq_pointEval :
    cylinderEval L f θ x = HasPointEval.pointEval f (θ, x)
```

The heat kernel uses the point type directly:
```lean
noncomputable def cylinderHeatKernel (L : ℝ) [Fact (0 < L)]
    (mass t : ℝ) (p₁ p₂ : ℝ × ℝ) : ℝ :=
  exp (-(mass ^ 2 * t)) *
    circleHeatKernel L t p₁.1 p₂.1 * mehlerKernel t p₁.2 p₂.2
```

## Files to create/modify

| File | Change |
|------|--------|
| `Nuclear/PointEval.lean` | **New**: `HasPointEval` typeclass + base instances |
| `HeatKernel/PositionKernel.lean` | Refactor to use point pairs, connect `cylinderEval` to `pointEval` |
| `HeatKernel.lean` | Import update |
| `Test.lean` | Update tests, add `#check HasPointEval.pointEval` for all concrete spaces |

## What NOT to do

- **Don't** use Mathlib's `ContMDiffMap` — it lacks Fréchet topology
- **Don't** add manifold structure to point types (premature)
- **Don't** make `SmoothMap_Circle` use `AddCircle` domain (breaks all calculus)

## Verification

1. `lake build Test` — zero errors
2. `#check HasPointEval.pointEval` elaborates for all concrete spaces
3. `cylinderEval` becomes a definitional special case of `pointEval`
