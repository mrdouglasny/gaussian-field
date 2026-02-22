# Two Deliverables: API File + GFF Repo

## Deliverable 1: `QFTFramework.lean` in gaussian-field

A single file stating the axiomatic API that gaussian-field provides to
downstream projects. Contains only the general functional analysis machinery —
no physics (no Schwinger functions, no OS axioms).

### File: `QFTFramework.lean`

```lean
import Nuclear.DyninMityagin
import Nuclear.NuclearTensorProduct
import HeatKernel.Axioms
import Mathlib.Topology.Algebra.Module.WeakDual
```

**Section 1: Point Evaluation**
```lean
class HasPointEval (E : Type*) (M : outParam Type*) where
  pointEval : E → M → ℝ

-- Instances for SchwartzMap, SmoothMap_Circle, NuclearTensorProduct, Fin N → ℝ
```

**Section 2: Configuration Space**
```lean
abbrev Configuration (E) := WeakDual ℝ E
-- Pairing: ω f = ω.toFun f (already from WeakDual)
-- Evaluation CLM: continuous by WeakDual.eval_continuous
```

**Section 3: Gaussian Measure** (restating what Construction/Properties prove)
```lean
axiom GaussianField.measure (T : E →L[ℝ] H) : Measure (Configuration E)
axiom GaussianField.measure_isProbability ...
axiom GaussianField.charFun (T) (f) :
    ∫ ω, exp(i · ω f) ∂(measure T) = exp(-½ ‖T f‖²)
axiom GaussianField.measure_centered (T) (f) : ∫ ω, ω f ∂(measure T) = 0
axiom GaussianField.cross_moment (T) (f g) :
    ∫ ω, ω f * ω g ∂(measure T) = ⟨T f, T g⟩
```

**Section 4: Spectral CLM** (from HeatKernel/Axioms.lean)
```lean
-- Already axiomatized there, just re-exported here for reference:
-- spectralCLM, qftEigenvalue, heatSingularValue
```

### What stays OUT of this file

- Schwinger functions → GFF repo
- OS axioms → GFF repo
- QFTSymmetry typeclass → GFF repo
- Generating functionals → GFF repo
- Concrete space abbreviations (Cylinder, Torus) → GFF repo

---

## Deliverable 2: New repo `GFF`

Depends on gaussian-field. Contains the physics: Schwinger functions,
OS axioms, concrete spaces, GFF construction, and the problem statement
(OS verification with sorrys).

### Structure

```
GFF/
  lakefile.lean
  lean-toolchain
  GFF.lean                       -- root import
  GFF/
    SchwingerFunctions.lean      -- general Schwinger functions & generating functional
    OSAxioms.lean                -- OS axiom definitions (parametrised over E)
    TestFunctionSpaces.lean      -- concrete E instances (Cylinder, Torus, Schwartz ℝ^d)
    GFFConstruction.lean         -- covariance operators T for each space
    OSVerification.lean          -- OS axioms for cylinder GFF (sorry proofs)
```

### `lakefile.lean`
```lean
package «GFF» where
  leanOptions := #[⟨`pp.unicode.fun, true⟩]

require «GaussianField» from git
  "https://github.com/mdouglas/gaussian-field.git"

lean_lib «GFF»
```

### `GFF/SchwingerFunctions.lean`

Generalised from OSforGFF, parametric over E:

```lean
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

def SchwingerFunction (dμ : ProbabilityMeasure (Configuration E))
    (n : ℕ) (f : Fin n → E) : ℝ :=
  ∫ ω, ∏ i, ω (f i) ∂dμ.toMeasure

def GJGeneratingFunctional (dμ : ProbabilityMeasure (Configuration E))
    (J : E) : ℂ :=
  ∫ ω, exp(I * ↑(ω J)) ∂dμ.toMeasure

-- Basic properties (proved or sorry'd):
-- schwinger_eq_mean, schwinger_eq_covariance, etc.
```

### `GFF/OSAxioms.lean`

OS axioms parametrised over E with symmetry data:

```lean
class QFTSymmetry (E : Type*) where
  timeReflection : E →L[ℝ] E
  timeTranslation : ℝ → Configuration E → Configuration E
  positiveTimeSubspace : Submodule ℝ E

-- OS axioms use QFTSymmetry + DyninMityaginSpace
def OS0_Analyticity [QFTSymmetry E] (dμ) : Prop := ...
def OS1_Regularity [QFTSymmetry E] (dμ) : Prop := ...
def OS2_Invariance [QFTSymmetry E] (dμ) : Prop := ...
def OS3_ReflectionPositivity [QFTSymmetry E] (dμ) : Prop := ...
def OS4_Clustering [QFTSymmetry E] (dμ) : Prop := ...

structure SatisfiesAllOS [QFTSymmetry E] (dμ) : Prop where
  os0 : OS0_Analyticity dμ
  os1 : OS1_Regularity dμ
  os2 : OS2_Invariance dμ
  os3 : OS3_ReflectionPositivity dμ
  os4 : OS4_Clustering dμ
```

### `GFF/TestFunctionSpaces.lean`

Concrete spaces with HasPointEval and DyninMityaginSpace:

```lean
-- Cylinder: S¹_L × ℝ
abbrev CylinderTestFun (L : ℝ) [Fact (0 < L)] :=
  NuclearTensorProduct (SmoothMap_Circle L ℝ) (SchwartzMap ℝ ℝ)
-- gets DyninMityaginSpace and HasPointEval (ℝ × ℝ) from instances

-- Schwartz on ℝ^d
abbrev SchwartzTestFun (d : ℕ) :=
  SchwartzMap (EuclideanSpace ℝ (Fin d)) ℝ

-- Torus: S¹_{L₁} × S¹_{L₂}
abbrev TorusTestFun (L₁ L₂ : ℝ) [Fact (0 < L₁)] [Fact (0 < L₂)] :=
  NuclearTensorProduct (SmoothMap_Circle L₁ ℝ) (SmoothMap_Circle L₂ ℝ)
```

### `GFF/GFFConstruction.lean`

Covariance operators and measures for each space:

```lean
-- Cylinder GFF
noncomputable def cylinderGFF_T (L mass : ℝ) ... :
    CylinderTestFun L →L[ℝ] ell2' :=
  spectralCLM (qftSingularValue L mass) ...

noncomputable def cylinderGFF_measure (L mass : ℝ) ... :=
  GaussianField.measure (cylinderGFF_T L mass ...)

-- QFTSymmetry instance for the cylinder
instance cylinderQFTSymmetry (L : ℝ) [Fact (0 < L)] :
    QFTSymmetry (CylinderTestFun L) where
  timeReflection := sorry
  timeTranslation := sorry
  positiveTimeSubspace := sorry
```

### `GFF/OSVerification.lean`

The problem statement — prove OS axioms for the cylinder GFF:

```lean
theorem cylinderGFF_OS0 ... : OS0_Analyticity (cylinderGFF_measure L mass ...) := sorry
theorem cylinderGFF_OS1 ... : OS1_Regularity (cylinderGFF_measure L mass ...) := sorry
theorem cylinderGFF_OS2 ... : OS2_Invariance (cylinderGFF_measure L mass ...) := sorry
theorem cylinderGFF_OS3 ... : OS3_ReflectionPositivity (cylinderGFF_measure L mass ...) := sorry
theorem cylinderGFF_OS4 ... : OS4_Clustering (cylinderGFF_measure L mass ...) := sorry

theorem cylinderGFF_satisfies_all_OS (L mass : ℝ) [Fact (0 < L)] (hmass : 0 < mass) :
    SatisfiesAllOS (cylinderGFF_measure L mass ...) := sorry
```

---

## Files to create/modify

### In gaussian-field:
| File | Change |
|------|--------|
| `Nuclear/PointEval.lean` | **New**: `HasPointEval` typeclass + instances |
| `QFTFramework.lean` | **New**: API file (Configuration, Gaussian measure axioms, point eval) |

### New repo GFF:
| File | Content |
|------|---------|
| `lakefile.lean` | Package config, depends on gaussian-field |
| `lean-toolchain` | Same as gaussian-field (v4.28.0) |
| `GFF.lean` | Root import |
| `GFF/SchwingerFunctions.lean` | Schwinger functions, generating functional |
| `GFF/OSAxioms.lean` | QFTSymmetry class, OS0-OS4 definitions, SatisfiesAllOS |
| `GFF/TestFunctionSpaces.lean` | Cylinder, Torus, Schwartz ℝ^d abbreviations |
| `GFF/GFFConstruction.lean` | Covariance operators, measures, QFTSymmetry instances |
| `GFF/OSVerification.lean` | OS axiom theorems with sorry proofs |

## Implementation order

1. Create `Nuclear/PointEval.lean` in gaussian-field
2. Create `QFTFramework.lean` in gaussian-field
3. Build gaussian-field to verify
4. Create GFF repo with lakefile + lean-toolchain
5. Write GFF files (SchwingerFunctions, OSAxioms, TestFunctionSpaces, GFFConstruction, OSVerification)
6. Build GFF to verify typechecking (sorrys ok, no type errors)

## Verification

1. `lake build` in gaussian-field — zero errors
2. `lake build` in GFF — compiles with sorrys only in OSVerification and GFFConstruction
