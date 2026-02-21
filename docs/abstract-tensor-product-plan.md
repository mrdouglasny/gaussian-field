# Path A: Abstract tensor product via Mathlib's `TensorProduct`

## Status

**Path B is complete.** The concrete universal property on `RapidDecaySeq` is fully
proved (`lift`, `lift_pure`) in `Nuclear/NuclearTensorProduct.lean`. Path A is a
future direction for building the mathematically complete abstract foundation.

## Goal

Build a completed projective tensor product for locally convex spaces on top of
Mathlib's algebraic `TensorProduct R M N`, prove it coincides with our concrete
`RapidDecaySeq` model for `DyninMityaginSpace` spaces, and transfer the universal
property. This would establish that `NuclearTensorProduct E₁ E₂` IS the completed
projective tensor product.

## What Mathlib already has

### Algebraic tensor product (`Mathlib.LinearAlgebra.TensorProduct`)

- `TensorProduct.mk : M →ₗ[R] N →ₗ[R] M ⊗[R] N` — canonical bilinear map
- `TensorProduct.lift : (M →ₛₗ[σ] N →ₛₗ[σ] P) → (M ⊗[R] N →ₛₗ[σ] P)` — universal property
- `TensorProduct.lift.equiv : (M →ₛₗ[σ] N →ₛₗ[σ] P) ≃ₗ[R₂] (M ⊗[R] N →ₛₗ[σ] P)` — isomorphism
- `lift.tmul : lift f (m ⊗ₜ n) = f m n` — factoring identity
- Associativity, commutativity, functoriality (`map`)

### Seminorms on `PiTensorProduct` (finite normed families)

In `Mathlib.Analysis.Normed.Module.PiTensorProduct`:

- **Projective seminorm** (`ProjectiveSeminorm.lean`):
  `PiTensorProduct.projectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i)` —
  infimum over representations `∑ⱼ ∏ᵢ ‖mⱼ i‖`

- **Injective seminorm** (`InjectiveSeminorm.lean`):
  `PiTensorProduct.injectiveSeminorm : Seminorm 𝕜 (⨂[𝕜] i, E i)` —
  supremum over evaluation maps. Satisfies `injectiveSeminorm ≤ projectiveSeminorm`.

- **Norm structure**: `PiTensorProduct` gets `SeminormedAddCommGroup` and `NormedSpace`
  from the injective seminorm.

- **Isometric universal property** (`InjectiveSeminorm.lean`):
  ```
  PiTensorProduct.liftIsometry :
      ContinuousMultilinearMap 𝕜 E F ≃ₗᵢ[𝕜] (⨂[𝕜] i, E i) →L[𝕜] F
  ```
  This is an isometric linear equivalence between continuous multilinear maps
  and CLMs from the tensor product. The key bound is:
  ```
  norm_eval_le_injectiveSeminorm f x : ‖lift f.toMultilinearMap x‖ ≤ ‖f‖ * injectiveSeminorm x
  ```

- **Functoriality**: `mapL` sends `⨂ₜ mᵢ ↦ ⨂ₜ (fᵢ mᵢ)` with `‖mapL f‖ ≤ ∏ᵢ ‖fᵢ‖`.

- **Continuous tensor map**: `tprodL : ContinuousMultilinearMap 𝕜 E (⨂[𝕜] i, E i)`.

### What Mathlib does NOT have

- Projective/injective tensor topology for `WithSeminorms` spaces (only for normed)
- Completed tensor product type (only the algebraic tensor product)
- Nuclear coincidence theorem (π = ε for nuclear spaces)
- Any nuclear space definition

### Other relevant Mathlib infrastructure

- `UniformSpace.Completion` — completion of any uniform space
- `Completion.instAddCommGroup`, `Completion.instModule` — algebraic structure on completions
- `WithSeminorms` — locally convex topology from seminorm families
- `Seminorm.continuous_from_bounded` — continuity of linear maps between seminormed spaces
- `Hahn-Banach` (`Analysis.Convex.Cone.Extension`) — for cross-seminorm equality

## Implementation plan

### Step 1: Projective seminorm family on `E₁ ⊗[ℝ] E₂` (~200–300 lines)

For locally convex spaces `E₁`, `E₂` with seminorm families `p₁ : ι₁ → Seminorm ℝ E₁`
and `p₂ : ι₂ → Seminorm ℝ E₂`, define the projective seminorm family on the algebraic
tensor product:

```lean
def projectiveTensorSeminorm (i : ι₁) (j : ι₂) :
    Seminorm ℝ (E₁ ⊗[ℝ] E₂) where
  toFun u := sInf { ∑ k in s, p₁ i (x k) * p₂ j (y k) |
                     (s, x, y), u = ∑ k in s, x k ⊗ₜ y k }
```

This is the standard projective cross-seminorm: the infimum over all representations
of u as a finite sum of elementary tensors.

**Key properties to prove:**
- Triangle inequality (from the infimum definition)
- Homogeneity `p(r • u) = |r| * p(u)`
- `p_{i,j}(x ⊗ₜ y) ≤ p₁_i(x) * p₂_j(y)` (take the 1-term representation)
- `p_{i,j}(x ⊗ₜ y) = p₁_i(x) * p₂_j(y)` (equality, harder, uses Hahn-Banach)

**Note:** Mathlib's `PiTensorProduct.projectiveSeminorm` does this for a single norm.
We generalize to a *family* of seminorms indexed by `ι₁ × ι₂`. The infimum
construction is similar but must be done for each pair `(i, j)`.

### Step 2: `WithSeminorms` instance on `E₁ ⊗[ℝ] E₂` (~100–150 lines)

```lean
instance : WithSeminorms (fun (i, j) => projectiveTensorSeminorm p₁ p₂ i j)
```

The topology on `E₁ ⊗[ℝ] E₂` is the initial topology making all
`projectiveTensorSeminorm i j` continuous. This is the projective tensor topology.

**Key properties:**
- `IsTopologicalAddGroup` and `ContinuousSMul ℝ` instances
- `mk` (the canonical bilinear map) is continuous: from the cross-seminorm bound

### Step 3: Completion (~200–300 lines)

Define the completed projective tensor product:

```lean
def CompletedTensorProduct (E₁ E₂ : Type*) [TVS instances...] :=
  UniformSpace.Completion (E₁ ⊗[ℝ] E₂)
```

Mathlib's `UniformSpace.Completion` provides the completion of any uniform space.
For a locally convex TVS, the uniform structure comes from the seminorm family.

**Key properties to prove:**
- The completion inherits `AddCommGroup`, `Module ℝ`, topological instances
- `WithSeminorms` for the completed seminorms (extend by uniform continuity)
- The canonical map `E₁ ⊗[ℝ] E₂ → CompletedTensorProduct E₁ E₂` is a dense embedding
- The algebraic `lift` extends by density to a CLM on the completion

### Step 4: Isomorphism with `RapidDecaySeq` for DM spaces (~300–500 lines)

For `DyninMityaginSpace E₁` and `DyninMityaginSpace E₂`:

```lean
def dmTensorEquiv :
    CompletedTensorProduct E₁ E₂ ≃L[ℝ] RapidDecaySeq
```

The map sends `ψ₁_i ⊗ₜ ψ₂_j ↦ basisVec (Nat.pair i j)` and extends by
linearity and continuity.

**Prerequisites — biorthogonality:**

This step requires adding biorthogonality to `DyninMityaginSpace`:
```lean
class DyninMityaginSpace (E : Type*) ... where
  ...
  biorthogonal : ∀ m n, coeff m (basis n) = if m = n then 1 else 0
```

Biorthogonality is needed to:
- Show the map is well-defined (independent of representation)
- Prove injectivity (an element mapping to 0 must be 0)
- Construct the inverse map

**Proof outline:**
- *Surjectivity*: every `a ∈ RapidDecaySeq` is the limit of
  `∑_{m∈s} a_m · basisVec m = ∑_{m∈s} a_m · (ψ₁_{i_m} ⊗ₜ ψ₂_{j_m})`
- *Continuity*: from the seminorm bounds (rapid decay seminorms match
  projective cross-seminorms via coefficient decay + basis growth)

### Step 5: Nuclear coincidence theorem (~200–400 lines)

For nuclear spaces (Pietsch sense), the projective and injective tensor topologies
coincide:

```lean
theorem nuclear_tensor_unique [NuclearSpace E₁] :
    ∀ i j, projectiveTensorSeminorm p₁ p₂ i j = injectiveTensorSeminorm p₁ p₂ i j
```

This is Grothendieck's theorem and a key characterization of nuclear spaces.
The proof uses the nuclear factorization from `NuclearSpace.nuclear_dominance`.

This is a deep result but only needed for the full mathematical picture, not for
the Gaussian field application.

### Step 6: Transfer universal property

With the isomorphism from Step 4:

```lean
theorem NuclearTensorProduct.universal_property :
    ∀ (B : E₁ →L[ℝ] E₂ →L[ℝ] G),
    ∃! T : NuclearTensorProduct E₁ E₂ →L[ℝ] G,
      ∀ e₁ e₂, T (pure e₁ e₂) = B e₁ e₂
```

This also requires `lift_unique`, which needs biorthogonality (Step 4 prerequisite).

## Dependencies and ordering

```
Step 1 (projective seminorms)
    ↓
Step 2 (WithSeminorms on ⊗)
    ↓
Step 3 (completion)
    ↓
Step 4 (isomorphism with RapidDecaySeq)  ←── requires biorthogonality
    ↓
Step 5 (nuclear coincidence)  ←── requires NuclearSpace
    ↓
Step 6 (transfer)
```

Steps 1–3 are independent of nuclear spaces — they build general locally convex
tensor product infrastructure that could eventually be contributed to Mathlib.
Steps 4–6 connect to the nuclear space theory.

## Estimated total effort

~1000–2000 lines of new Lean code across several new files:

| File (proposed) | Lines | Contents |
|------|------:|----------|
| `Nuclear/ProjectiveTensor.lean` | ~400 | Steps 1–2: projective seminorms + topology |
| `Nuclear/CompletedTensor.lean` | ~300 | Step 3: completion + universal property extension |
| `Nuclear/TensorIsomorphism.lean` | ~500 | Step 4: DM isomorphism with RapidDecaySeq |
| `Nuclear/NuclearCoincidence.lean` | ~300 | Step 5: π = ε for nuclear spaces |

## Key Mathlib dependencies

- `Mathlib.LinearAlgebra.TensorProduct.Basic` — algebraic tensor product + lift
- `Mathlib.Analysis.Normed.Module.PiTensorProduct.InjectiveSeminorm` — existing norm structure
- `Mathlib.Topology.UniformSpace.Completion` — uniform completion
- `Mathlib.Analysis.LocallyConvex.WithSeminorms` — seminorm families
- `Mathlib.Analysis.Convex.Cone.Extension` — Hahn-Banach (for cross-seminorm equality)

## Relation to Path B (current implementation)

Path B gives the universal property directly on `RapidDecaySeq` without abstract
tensor product theory:
- `NuclearTensorProduct.pure` — continuous bilinear map into `RapidDecaySeq`
- `NuclearTensorProduct.lift` — factors any continuous bilinear map through `pure`
- `NuclearTensorProduct.lift_pure` — the factoring identity `lift B (pure e₁ e₂) = B e₁ e₂`

Path B is sufficient for the Gaussian field construction. Path A would establish
that this concrete model IS the completed projective tensor product, providing
the mathematically complete foundation. Path A would be valuable for:
- Contributing general locally convex tensor product infrastructure to Mathlib
- Applications needing the abstract tensor product structure (e.g., operator algebras)
- Proving uniqueness (`lift_unique`) via the abstract universal property
